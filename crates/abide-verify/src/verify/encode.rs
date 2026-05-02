//! Pure expression encoding — maps IR expressions to Z3 AST in a local variable environment.

use std::collections::{HashMap, HashSet};

use super::smt::{AbideSolver, Bool, Dynamic, FuncDecl, Int, SatResult, Sort};

use crate::ir::types::{IRExpr, IRType};

use super::context::VerifyContext;
use super::defenv;
use super::smt::{self, SmtValue};
use super::walkers::dynamic_to_smt_value;

/// Counter for generating unique lambda function names.
static LAMBDA_COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

// ── Z3 variable creation ────────────────────────────────────────────

pub(super) fn make_z3_var_from_smt(name: &str, template: &SmtValue) -> SmtValue {
    match template {
        SmtValue::Int(_) => smt::int_var(name),
        SmtValue::Bool(_) => smt::bool_var(name),
        SmtValue::Real(_) => smt::real_var(name),
        SmtValue::Array(_) => {
            // For arrays/dynamic/func, fall back to int (best effort)
            smt::int_var(name)
        }
        SmtValue::Dynamic(d) => SmtValue::Dynamic(smt::dynamic_const(name, &smt::dynamic_sort(d))),
        SmtValue::Func(_) => {
            // For arrays/dynamic/func, fall back to int (best effort)
            smt::int_var(name)
        }
    }
}

/// Create a Z3 variable for a given IR type.
/// Check that a function call's arguments satisfy the callee's preconditions.
pub(super) fn make_z3_var(name: &str, ty: &crate::ir::types::IRType) -> Result<SmtValue, String> {
    make_z3_var_ctx(name, ty, None)
}

pub(super) fn make_z3_var_ctx(
    name: &str,
    ty: &crate::ir::types::IRType,
    vctx: Option<&VerifyContext>,
) -> Result<SmtValue, String> {
    use crate::ir::types::IRType;
    match ty {
        IRType::Int | IRType::Identity | IRType::String => Ok(smt::int_var(name)),
        IRType::Bool => Ok(smt::bool_var(name)),
        IRType::Real | IRType::Float => Ok(smt::real_var(name)),
        IRType::Enum {
            name: enum_name, ..
        } => {
            // Use ADT sort if the enum has constructor fields
            if let Some(ctx) = vctx {
                if let Some(dt) = ctx.adt_sorts.get(enum_name) {
                    let dt_sort = dt.sort();
                    let var = smt::dynamic_const(name, &dt_sort);
                    return Ok(SmtValue::Dynamic(var));
                }
            }
            Ok(smt::int_var(name))
        }
        IRType::Refinement { base, .. } => make_z3_var_ctx(name, base, vctx),
        IRType::Set { .. } | IRType::Map { .. } => smt::array_var(name, ty),
        IRType::Seq { element } => Ok(SmtValue::Dynamic(smt::dynamic_const(
            name,
            &smt::seq_sort(element).sort(),
        ))),
        _ => Err(format!(
            "unsupported parameter type for fn contract verification: {ty:?}"
        )),
    }
}

fn expr_type(expr: &IRExpr) -> Option<&IRType> {
    match expr {
        IRExpr::Lit { ty, .. }
        | IRExpr::Var { ty, .. }
        | IRExpr::BinOp { ty, .. }
        | IRExpr::UnOp { ty, .. }
        | IRExpr::App { ty, .. }
        | IRExpr::Field { ty, .. }
        | IRExpr::Choose { ty, .. }
        | IRExpr::MapUpdate { ty, .. }
        | IRExpr::Index { ty, .. }
        | IRExpr::SetLit { ty, .. }
        | IRExpr::SeqLit { ty, .. }
        | IRExpr::MapLit { ty, .. }
        | IRExpr::SetComp { ty, .. } => Some(ty),
        IRExpr::Prime { expr, .. } => expr_type(expr),
        IRExpr::Let { body, .. } => expr_type(body),
        IRExpr::Ctor { .. } => None,
        _ => None,
    }
}

// ── Precondition context ────────────────────────────────────────────

/// Context for call-site precondition checking inside `encode_pure_expr`.
///
/// When present, every `App` expansion checks that the callee's `requires`
/// hold in the current context (`fn_requires` + `extra_assumptions`).
pub(super) struct PrecheckCtx<'a> {
    pub(super) fn_requires: &'a [IRExpr],
    pub(super) extra_assumptions: &'a [Bool],
    /// The function being verified — recursive self-calls are not expanded
    /// but instead return a fresh variable constrained by the function's ensures.
    pub(super) self_fn: Option<&'a crate::ir::types::IRFunction>,
}

// ── Pure expression entry points ────────────────────────────────────

pub(super) fn encode_pure_expr(
    expr: &IRExpr,
    env: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
) -> Result<SmtValue, String> {
    encode_pure_expr_inner(expr, env, vctx, defs, None)
}

pub(super) fn encode_pure_expr_checked(
    expr: &IRExpr,
    env: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    precheck: &PrecheckCtx<'_>,
) -> Result<SmtValue, String> {
    encode_pure_expr_inner(expr, env, vctx, defs, Some(precheck))
}

// ── Core expression encoder ─────────────────────────────────────────

#[allow(clippy::too_many_lines)]
pub(super) fn encode_pure_expr_inner(
    expr: &IRExpr,
    env: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    precheck: Option<&PrecheckCtx<'_>>,
) -> Result<SmtValue, String> {
    match expr {
        IRExpr::Lit { value, ty, .. } => encode_pure_lit(value, ty),

        IRExpr::Var { name, .. } => {
            if let Some(val) = env.get(name) {
                return Ok(val.clone());
            }
            if let Some(expanded) = defs.expand_var(name) {
                return encode_pure_expr_inner(&expanded, env, vctx, defs, precheck);
            }
            Err(format!("unbound variable in fn contract: '{name}'"))
        }
        IRExpr::Choose { .. } => Err(
            "choose expression is not yet supported in verifier encoding".to_owned(),
        ),
        IRExpr::RelComp { .. } => {
            Err("relation comprehension is not supported in fn contract encoding".to_owned())
        }

        IRExpr::Ctor {
            enum_name, ctor, args, ..
        } => {
 // ADT-encoded enum: use constructor function with field arguments
            if let Some(dt) = vctx.adt_sorts.get(enum_name) {
                for variant in &dt.variants {
                    if smt::func_decl_name(&variant.constructor) == *ctor {
                        let arity = variant.accessors.len();
                        if arity > 0 && args.is_empty() {
                            return Err(format!(
                                "constructor '{ctor}' of '{enum_name}' requires {arity} \
                                 field argument(s) — use @{enum_name}::{ctor} {{ ... }}"
                            ));
                        }
                        if args.is_empty() {
 // Nullary constructor (no fields)
                            let result = smt::func_decl_apply(&variant.constructor, &[]);
                            return Ok(dynamic_to_smt_value(result));
                        }

 // Validate and reorder field arguments by declared order.
 // Accessor names define the canonical field order.
                        let declared_names: Vec<std::string::String> = variant
                            .accessors
                            .iter()
                            .map(smt::func_decl_name)
                            .collect();

 // Check for unknown fields
                        for (field_name, _) in args {
                            if !declared_names.iter().any(|d| d == field_name) {
                                return Err(format!(
                                    "unknown field '{field_name}' in constructor '{ctor}' \
                                     of '{enum_name}' — declared fields: {}",
                                    declared_names.join(", ")
                                ));
                            }
                        }

 // Check for duplicates
                        let mut seen = std::collections::HashSet::new();
                        for (field_name, _) in args {
                            if !seen.insert(field_name.as_str()) {
                                return Err(format!(
                                    "duplicate field '{field_name}' in constructor '{ctor}'"
                                ));
                            }
                        }

 // Check arity
                        if args.len() != arity {
                            let missing: Vec<&str> = declared_names
                                .iter()
                                .filter(|d| !args.iter().any(|(n, _)| n == d.as_str()))
                                .map(std::string::String::as_str)
                                .collect();
                            return Err(format!(
                                "constructor '{ctor}' of '{enum_name}' requires {arity} \
                                 field(s) but got {} — missing: {}",
                                args.len(),
                                missing.join(", ")
                            ));
                        }

 // Build args in declared field order (not source order)
                        let args_map: HashMap<&str, &IRExpr> = args
                            .iter()
                            .map(|(n, e)| (n.as_str(), e))
                            .collect();
                        let mut z3_args: Vec<Dynamic> = Vec::new();
                        for decl_name in &declared_names {
                            let field_expr = args_map[decl_name.as_str()];
                            let val = encode_pure_expr_inner(
                                field_expr, env, vctx, defs, precheck,
                            )?;
                            z3_args.push(val.to_dynamic());
                        }

                        let arg_refs: Vec<&Dynamic> = z3_args.iter().collect();
                        let result = smt::func_decl_apply(&variant.constructor, &arg_refs);
                        return Ok(dynamic_to_smt_value(result));
                    }
                }
            }
 // Flat Int encoding for fieldless enums
            let id = vctx.variants.try_id_of(enum_name, ctor)?;
            Ok(smt::int_val(id))
        }

        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpSeqConcat" => {
            let lhs = encode_pure_expr_inner(left, env, vctx, defs, precheck)?;
            let rhs = encode_pure_expr_inner(right, env, vctx, defs, precheck)?;
            let Some(IRType::Seq { element }) = expr_type(left) else {
                return Err("Seq::concat requires sequence operands".to_owned());
            };
            smt::seq_concat(&lhs, &rhs, element)
        }
        IRExpr::BinOp { op, left, right, .. } if op == "OpMapHas" => {
            let map_val = encode_pure_expr_inner(left, env, vctx, defs, precheck)?;
            let key_val = encode_pure_expr_inner(right, env, vctx, defs, precheck)?;
            let Some(IRType::Map { value, .. }) = expr_type(left) else {
                return Err("Map::has requires a map-typed left operand".to_owned());
            };
            smt::map_has(&map_val, &key_val, value)
        }
        IRExpr::BinOp { op, left, right, .. } if op == "OpMapMerge" => {
            let left_val = encode_pure_expr_inner(left, env, vctx, defs, precheck)?;
            let right_val = encode_pure_expr_inner(right, env, vctx, defs, precheck)?;
            let Some(IRType::Map { key, value }) = expr_type(left) else {
                return Err("Map::merge requires map operands".to_owned());
            };
            smt::map_merge(&left_val, &right_val, key, value)
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let lhs = encode_pure_expr_inner(left, env, vctx, defs, precheck)?;
            let rhs = encode_pure_expr_inner(right, env, vctx, defs, precheck)?;
            smt::binop(op, &lhs, &rhs)
        }

        IRExpr::UnOp { op, operand, .. } if op == "OpSeqHead" => {
            let val = encode_pure_expr_inner(operand, env, vctx, defs, precheck)?;
            let Some(IRType::Seq { element }) = expr_type(operand) else {
                return smt::unop(op, &val);
            };
            smt::seq_head(&val, element)
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpSeqTail" => {
            if let IRExpr::SeqLit { elements, ty, .. } = operand.as_ref() {
                let tail = IRExpr::SeqLit {
                    elements: elements.iter().skip(1).cloned().collect(),
                    ty: ty.clone(),
                    span: None,
                };
                return encode_pure_expr_inner(&tail, env, vctx, defs, precheck);
            }
            let val = encode_pure_expr_inner(operand, env, vctx, defs, precheck)?;
            let Some(IRType::Seq { element }) = expr_type(operand) else {
                return smt::unop(op, &val);
            };
            smt::seq_tail(&val, element)
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpSeqLength" => {
            let val = encode_pure_expr_inner(operand, env, vctx, defs, precheck)?;
            let Some(IRType::Seq { element }) = expr_type(operand) else {
                let card = IRExpr::Card {
                    expr: operand.clone(),
                    span: None,
                };
                return encode_pure_expr_inner(&card, env, vctx, defs, precheck);
            };
            smt::seq_length(&val, element)
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpSeqEmpty" => {
            let len = if let Some(IRType::Seq { element }) = expr_type(operand) {
                let val = encode_pure_expr_inner(operand, env, vctx, defs, precheck)?;
                smt::seq_length(&val, element)?
            } else {
                let card = IRExpr::Card {
                    expr: operand.clone(),
                    span: None,
                };
                encode_pure_expr_inner(&card, env, vctx, defs, precheck)?
            };
            Ok(SmtValue::Bool(smt::smt_eq(&len, &smt::int_val(0))?))
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpMapDomain" => {
            if let IRExpr::MapLit { entries, .. } = operand.as_ref() {
                let set_lit = IRExpr::SetLit {
                    elements: entries.iter().map(|(k, _)| k.clone()).collect(),
                    ty: IRType::Set {
                        element: Box::new(match expr_type(operand) {
                            Some(IRType::Map { key, .. }) => key.as_ref().clone(),
                            _ => IRType::Int,
                        }),
                    },
                    span: None,
                };
                return encode_pure_expr_inner(&set_lit, env, vctx, defs, precheck);
            }
            let map_val = encode_pure_expr_inner(operand, env, vctx, defs, precheck)?;
            let Some(IRType::Map { key, value }) = expr_type(operand) else {
                return Err("Map::domain requires a map operand".to_owned());
            };
            smt::map_domain(&map_val, key, value)
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpMapRange" => {
            if let IRExpr::MapLit { entries, .. } = operand.as_ref() {
                let set_lit = IRExpr::SetLit {
                    elements: entries.iter().map(|(_, v)| v.clone()).collect(),
                    ty: IRType::Set {
                        element: Box::new(match expr_type(operand) {
                            Some(IRType::Map { value, .. }) => value.as_ref().clone(),
                            _ => IRType::Int,
                        }),
                    },
                    span: None,
                };
                return encode_pure_expr_inner(&set_lit, env, vctx, defs, precheck);
            }
            let map_val = encode_pure_expr_inner(operand, env, vctx, defs, precheck)?;
            let Some(IRType::Map { key, value }) = expr_type(operand) else {
                return Err("Map::range requires a map operand".to_owned());
            };
            smt::map_range(&map_val, key, value)
        }
        IRExpr::UnOp { op, operand, .. } => {
            let val = encode_pure_expr_inner(operand, env, vctx, defs, precheck)?;
            smt::unop(op, &val)
        }

        IRExpr::App { .. } => {
 // Determine if this is a recursive self-call
            let is_self_call = precheck
                .and_then(|ctx| ctx.self_fn)
                .and_then(|sf| {
                    defenv::decompose_app_chain_name(expr)
                        .filter(|name| name == &sf.name)
                })
                .is_some();

 // Check preconditions for NON-self calls.
 // Self-call preconditions are checked by (termination VC)
 // with proper path conditions from the enclosing branch structure.
            if !is_self_call {
                if let Some(ctx) = precheck {
                    if let Some(preconditions) = defs.call_preconditions(expr) {
                        if !preconditions.is_empty() {
                            let mut context_bools: Vec<Bool> = Vec::new();
                            for req in ctx.fn_requires {
                                let req_val = encode_pure_expr(req, env, vctx, defs)?;
                                context_bools.push(req_val.to_bool()?);
                            }
                            for assumption in ctx.extra_assumptions {
                                context_bools.push(assumption.clone());
                            }
                            for pre in &preconditions {
                                let pre_val = encode_pure_expr(pre, env, vctx, defs)?;
                                let pre_bool = pre_val.to_bool()?;
                                let vc_solver = AbideSolver::new();
                                super::assert_lambda_axioms_on(&vc_solver);
                                for ctx_bool in &context_bools {
                                    vc_solver.assert(ctx_bool);
                                }
                                vc_solver.assert(smt::bool_not(&pre_bool));
                                if vc_solver.check() != SatResult::Unsat {
                                    return Err(
                                        crate::messages::FN_CALL_PRECONDITION_FAILED.to_owned(),
                                    );
                                }
                            }
                        }
                    }
                }
            }
 // Handle recursive self-calls: don't expand, return fresh
 // variable constrained by the function's ensures (modular reasoning).
            if let Some(ctx) = precheck {
                if let Some(self_f) = ctx.self_fn {
                    if let Some((call_name, call_args)) =
                        defenv::decompose_app_chain_public(expr)
                    {
                        if call_name == self_f.name {
                            return super::encode_recursive_self_call(
                                self_f, &call_args, env, vctx, defs,
                            );
                        }
                    }
                }
            }
 // Collect the full curried application chain: App(App(f, a), b) → (f, [a, b])
 // Then check if the base function is a lambda (Func-valued).
            {
                let mut base = expr;
                let mut arg_exprs: Vec<&IRExpr> = Vec::new();
                while let IRExpr::App { func, arg, .. } = base {
                    arg_exprs.push(arg);
                    base = func;
                }
                arg_exprs.reverse(); // collected in reverse order

 // Try encoding the base function
                let func_result = encode_pure_expr_inner(base, env, vctx, defs, precheck);
                if let Ok(SmtValue::Func(ref ft)) = func_result {
                    let (ref func_decl, ref param_sorts, ref range_sort) = **ft;
                    let arity = param_sorts.len();
                    let mut z3_args: Vec<Dynamic> = Vec::new();
                    for arg_expr in &arg_exprs {
                        let val = encode_pure_expr_inner(arg_expr, env, vctx, defs, precheck)?;
                        z3_args.push(val.to_dynamic());
                    }

                    if arg_exprs.len() == arity {
 // Full application
                        let arg_refs: Vec<&Dynamic> = z3_args.iter().collect();
                        let result = smt::func_decl_apply(func_decl, &arg_refs);
                        return Ok(dynamic_to_smt_value(result));
                    } else if arg_exprs.len() < arity {
 // Partial application
                        return encode_partial_application(
                            func_decl, param_sorts, range_sort, &z3_args,
                        );
                    }
                    return Err(format!(
                        "too many arguments — function expects {arity} but got {}",
                        arg_exprs.len()
                    ));
                }
 // If base is not Func-valued, fall through to DefEnv / self-call
            }

 // Expand via DefEnv
            if let Some(expanded) = defs.expand_app(expr) {
                return encode_pure_expr_inner(&expanded, env, vctx, defs, precheck);
            }
            Err("could not expand function application in fn contract".to_string())
        }

        IRExpr::Let { bindings, body, .. } => {
            let mut extended_env = env.clone();
            for b in bindings {
                let val = encode_pure_expr_inner(&b.expr, &extended_env, vctx, defs, precheck)?;
                extended_env.insert(b.name.clone(), val);
            }
            encode_pure_expr_inner(body, &extended_env, vctx, defs, precheck)
        }

        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond_val = encode_pure_expr_inner(cond, env, vctx, defs, precheck)?;
            let cond_bool = cond_val.to_bool()?;
            let then_val = encode_pure_expr_inner(then_body, env, vctx, defs, precheck)?;
            if let Some(eb) = else_body {
                let else_val = encode_pure_expr_inner(eb, env, vctx, defs, precheck)?;
                encode_ite(&cond_bool, &then_val, &else_val)
            } else {
                let then_bool = then_val.to_bool()?;
                Ok(SmtValue::Bool(smt::bool_implies(&cond_bool, &then_bool)))
            }
        }

        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            let scrut_val = encode_pure_expr_inner(scrutinee, env, vctx, defs, precheck)?;
            encode_pure_match(&scrut_val, arms, env, vctx, defs, precheck)
        }

        IRExpr::Forall {
            var, domain, body, ..
        } => encode_z3_quantifier(true, var, domain, body, env, vctx, defs, precheck),

        IRExpr::Exists {
            var, domain, body, ..
        } => encode_z3_quantifier(false, var, domain, body, env, vctx, defs, precheck),

        IRExpr::One {
            var, domain, body, ..
        } => encode_z3_one(var, domain, body, env, vctx, defs, precheck),

        IRExpr::Lone {
            var, domain, body, ..
        } => encode_z3_lone(var, domain, body, env, vctx, defs, precheck),

        IRExpr::Index { map, key, ty, .. } => {
            let map_val = encode_pure_expr_inner(map, env, vctx, defs, precheck)?;
            let key_val = encode_pure_expr_inner(key, env, vctx, defs, precheck)?;
            if let Some(IRType::Map { value, .. }) = expr_type(map) {
                return smt::map_lookup(&map_val, &key_val, value);
            }
            if let Some(IRType::Seq { element }) = expr_type(map) {
                return smt::seq_index(&map_val, &key_val, element);
            }
            let arr = map_val.as_array()?;
            let result = arr.select(&key_val.to_dynamic());
            Ok(smt::dynamic_to_typed_value(result, ty))
        }

        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            let map_val = encode_pure_expr_inner(map, env, vctx, defs, precheck)?;
            let key_val = encode_pure_expr_inner(key, env, vctx, defs, precheck)?;
            let val = encode_pure_expr_inner(value, env, vctx, defs, precheck)?;
            if let Some(IRType::Map { value: value_ty, .. }) = expr_type(map) {
                return smt::map_store(&map_val, &key_val, &val, value_ty);
            }
            let arr = map_val.as_array()?;
            Ok(SmtValue::Array(
                arr.store(&key_val.to_dynamic(), &val.to_dynamic()),
            ))
        }

        IRExpr::SetLit { elements, ty, .. } => {
            let elem_ty = match ty {
                crate::ir::types::IRType::Set { element } => element.as_ref(),
 // Unresolved type: infer element type from first element (Int default)
                _ => &crate::ir::types::IRType::Int,
            };
            let elem_sort = smt::ir_type_to_sort(elem_ty);
            let false_dyn = smt::default_dynamic(&crate::ir::types::IRType::Bool);
            let mut arr = smt::const_array(&elem_sort, &false_dyn);
            let true_dyn = smt::bool_to_dynamic(&smt::bool_const(true));
            for e in elements {
                let elem = encode_pure_expr_inner(e, env, vctx, defs, precheck)?;
                arr = arr.store(&elem.to_dynamic(), &true_dyn);
            }
            Ok(SmtValue::Array(arr))
        }

        IRExpr::SeqLit { elements, ty, .. } => {
            let elem_ty = match ty {
                crate::ir::types::IRType::Seq { element } => element.as_ref(),
                _ => &crate::ir::types::IRType::Int,
            };
            let elems = elements
                .iter()
                .map(|e| encode_pure_expr_inner(e, env, vctx, defs, precheck))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(smt::seq_literal(elem_ty, &elems))
        }

        IRExpr::MapLit { entries, ty, .. } => {
            let (key_ty, val_ty) = match ty {
                crate::ir::types::IRType::Map { key, value } => (key.as_ref(), value.as_ref()),
 // Unresolved type: infer from entries (Int keys, Bool values as default)
                _ => (
                    &crate::ir::types::IRType::Int,
                    &crate::ir::types::IRType::Bool,
                ),
            };
            let key_sort = smt::ir_type_to_sort(key_ty);
            let default = smt::map_none_dynamic(val_ty);
            let mut arr = smt::const_array(&key_sort, &default);
            for (k, v) in entries {
                let key_val = encode_pure_expr_inner(k, env, vctx, defs, precheck)?;
                let val_val = encode_pure_expr_inner(v, env, vctx, defs, precheck)?;
                arr = arr.store(&key_val.to_dynamic(), &smt::map_some_dynamic(val_ty, &val_val));
            }
            Ok(SmtValue::Array(arr))
        }

        IRExpr::Card { expr: inner, .. } => match inner.as_ref() {
 // Set cardinality: count semantically distinct elements.
 // Encode each element to Z3, then use the "first occurrence"
 // pattern: element i is counted iff it differs from all prior
 // elements. This correctly handles `#Set(1, 1 + 0)` = 1.
            IRExpr::SetLit { elements, .. } => {
                if elements.is_empty() {
                    return Ok(smt::int_val(0));
                }
                let z3_elems: Vec<SmtValue> = elements
                    .iter()
                    .map(|e| encode_pure_expr_inner(e, env, vctx, defs, precheck))
                    .collect::<Result<_, _>>()?;

                let one = smt::int_lit(1);
                let zero = smt::int_lit(0);
                let mut terms: Vec<Int> = Vec::new();

                for (i, vi) in z3_elems.iter().enumerate() {
                    if i == 0 {
 // First element always counts
                        terms.push(one.clone());
                    } else {
 // Count iff different from all prior elements
                        let mut diff_from_prior: Vec<Bool> = Vec::new();
                        for vj in &z3_elems[..i] {
                            let neq = smt::smt_neq(vi, vj)?;
                            diff_from_prior.push(neq);
                        }
                        let refs: Vec<&Bool> = diff_from_prior.iter().collect();
                        let is_first = smt::bool_and(&refs);
                        terms.push(smt::int_ite(&is_first, &one, &zero));
                    }
                }

                let refs: Vec<&Int> = terms.iter().collect();
                Ok(SmtValue::Int(smt::int_add(&refs)))
            }
            IRExpr::SeqLit { elements, .. } => Ok(smt::int_val(i64::try_from(elements.len()).unwrap_or(0))),
            IRExpr::MapLit { entries, .. } => {
                if entries.is_empty() {
                    return Ok(smt::int_val(0));
                }
 // Same first-occurrence pattern for map keys
                let z3_keys: Vec<SmtValue> = entries
                    .iter()
                    .map(|(k, _)| encode_pure_expr_inner(k, env, vctx, defs, precheck))
                    .collect::<Result<_, _>>()?;

                let one = smt::int_lit(1);
                let zero = smt::int_lit(0);
                let mut terms: Vec<Int> = Vec::new();

                for (i, ki) in z3_keys.iter().enumerate() {
                    if i == 0 {
                        terms.push(one.clone());
                    } else {
                        let mut diff: Vec<Bool> = Vec::new();
                        for kj in &z3_keys[..i] {
                            diff.push(smt::smt_neq(ki, kj)?);
                        }
                        let refs: Vec<&Bool> = diff.iter().collect();
                        let is_first = smt::bool_and(&refs);
                        terms.push(smt::int_ite(&is_first, &one, &zero));
                    }
                }

                let refs: Vec<&Int> = terms.iter().collect();
                Ok(SmtValue::Int(smt::int_add(&refs)))
            }
 // Cardinality of non-literal: encode the inner expression and
 // reject if it's not a form we can reason about.
            _ => {
                if let Some(IRType::Seq { element }) = expr_type(inner) {
                    let seq = encode_pure_expr_inner(inner, env, vctx, defs, precheck)?;
                    smt::seq_length(&seq, element)
                } else {
                    Err(
                        "cardinality (#) of non-literal collections not supported in fn contracts — \
                         use #Set(...), #Seq(...), or #Map(...)"
                            .to_owned(),
                    )
                }
            }
        },
 // Set comprehension: { x: T where P(x) }
 // Encode as Z3 lambda array with domain restriction:
 // simple: λx. domain_pred(x) ∧ P(x)
 // projection: λy. ∃x. domain_pred(x) ∧ P(x) ∧ f(x) == y
        IRExpr::SetComp {
            var,
            domain,
            filter,
            projection,
            ..
        } => {
 // Create a fresh Z3 constant for the comprehension variable
            let bound_var = make_z3_var(var, domain)?;
            let mut inner_env = env.clone();
            inner_env.insert(var.to_owned(), bound_var.clone());

 // Encode the filter predicate with the bound variable in scope
            let filter_val =
                encode_pure_expr_inner(filter, &inner_env, vctx, defs, precheck)?;
            let filter_bool = filter_val.to_bool()?;

 // Build domain predicate for restricted types (enum, refinement)
            let domain_pred = build_domain_predicate(
                domain, &bound_var, &inner_env, vctx, defs, precheck,
            )?;

 // Combine filter with domain predicate: domain_pred ∧ filter
            let restricted_filter = match domain_pred {
                Some(dp) => smt::bool_and(&[&dp, &filter_bool]),
                None => filter_bool,
            };

            if let Some(proj) = projection {
 // Projection comprehension: { f(x) | x: T where P(x) }
 // Encode as: λy. ∃x. domain_pred(x) ∧ P(x) ∧ f(x) == y
                let proj_val =
                    encode_pure_expr_inner(proj, &inner_env, vctx, defs, precheck)?;

                let proj_var_name = format!("{var}__proj");
                let proj_bound = make_z3_var_from_smt(&proj_var_name, &proj_val);

                let eq = smt::smt_eq(&proj_val, &proj_bound)?;
                let body = smt::bool_and(&[&restricted_filter, &eq]);

                let bound_dyn = bound_var.to_dynamic();
                let exists_body = smt::exists(&[&bound_dyn], &body);

                let body_dyn = smt::bool_to_dynamic(&exists_body);
                let proj_dyn = proj_bound.to_dynamic();
                let arr = smt::lambda(&[&proj_dyn], &body_dyn);
                Ok(SmtValue::Array(arr))
            } else {
 // Simple comprehension: { x: T where P(x) }
 // Encode as: λx. domain_pred(x) ∧ P(x)
                let body_dyn = smt::bool_to_dynamic(&restricted_filter);
                let var_dyn = bound_var.to_dynamic();
                let arr = smt::lambda(&[&var_dyn], &body_dyn);
                Ok(SmtValue::Array(arr))
            }
        }
        IRExpr::Always { .. }
        | IRExpr::Eventually { .. }
        | IRExpr::Until { .. }
        | IRExpr::Historically { .. }
        | IRExpr::Once { .. }
        | IRExpr::Previously { .. }
        | IRExpr::Since { .. } => {
            Err("temporal operators not allowed in fn contracts".to_owned())
        }
        IRExpr::Saw { .. } => Err(crate::messages::SAW_NOT_ALLOWED_IN_FN_BODY.to_owned()),
        IRExpr::Prime { .. } => Err("prime (next-state) not allowed in fn contracts".to_owned()),
        IRExpr::Field { .. } => {
            Err("entity field access not allowed in fn contracts".to_owned())
        }
        IRExpr::Lam { .. } => {
            encode_lambda(expr, env, vctx, defs, precheck)
        }

        IRExpr::Block { exprs, .. } => {
            if exprs.is_empty() {
                return Ok(smt::bool_val(true));
            }
            let mut last = smt::bool_val(true);
            for e in exprs {
                last = encode_pure_expr_inner(e, env, vctx, defs, precheck)?;
            }
            Ok(last)
        }

        IRExpr::VarDecl {
            name, init, rest, ..
        } => {
            let val = encode_pure_expr_inner(init, env, vctx, defs, precheck)?;
            let mut extended_env = env.clone();
            extended_env.insert(name.clone(), val);
            encode_pure_expr_inner(rest, &extended_env, vctx, defs, precheck)
        }

        IRExpr::While { .. } => {
            Err(crate::messages::FN_LOOP_NO_INVARIANT.to_owned())
        }

        IRExpr::Assert { .. } => {
            Err("assert in pure expression context — assert is an imperative statement and must appear in a function body block".to_owned())
        }
        IRExpr::Assume { .. } => {
            Err("assume in pure expression context — assume is an imperative statement and must appear in a function body block".to_owned())
        }

        IRExpr::Aggregate {
            kind,
            var,
            domain,
            body,
            in_filter,
            ..
        } => encode_pure_aggregate(*kind, var, domain, body, in_filter.as_deref(), env, vctx, defs, precheck),
        IRExpr::Sorry { .. } => Ok(smt::bool_val(true)),
        IRExpr::Todo { .. } => Err("todo expression in fn contract body".to_owned()),
    }
}

// ── Domain predicates ───────────────────────────────────────────────

/// Build a domain predicate for restricted types (enum, refinement).
/// Returns `None` for unrestricted types (Int, Bool, Real, etc.).
///
/// Used by both quantifier encoding and set comprehension encoding to
/// constrain bound variables to their declared domain.
#[allow(clippy::too_many_arguments)]
pub(super) fn build_domain_predicate(
    domain: &crate::ir::types::IRType,
    bound_var: &SmtValue,
    inner_env: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    precheck: Option<&PrecheckCtx<'_>>,
) -> Result<Option<Bool>, String> {
    use crate::ir::types::IRType;
    match domain {
        IRType::Enum { name, variants: vs } => {
            // ADT-encoded enums (Dynamic): Z3's ADT sort already constrains
            // the variable to valid constructors — no domain predicate needed.
            if matches!(bound_var, SmtValue::Dynamic(_)) {
                return Ok(None);
            }
            // Flat Int-encoded enums: restrict to valid variant ID range.
            let var_int = bound_var.as_int()?;
            let ids: Vec<i64> = vs
                .iter()
                .map(|v| vctx.variants.try_id_of(name, &v.name))
                .collect::<Result<_, _>>()?;
            let min_id = *ids.iter().min().unwrap();
            let max_id = *ids.iter().max().unwrap();
            let lo = smt::int_val(min_id);
            let hi = smt::int_val(max_id);
            Ok(Some(smt::bool_and(&[
                &smt::int_ge(var_int, lo.as_int().unwrap()),
                &smt::int_le(var_int, hi.as_int().unwrap()),
            ])))
        }
        IRType::Refinement { predicate, .. } => {
            let mut pred_env = inner_env.clone();
            pred_env.insert("$".to_owned(), bound_var.clone());
            let pred_val = encode_pure_expr_inner(predicate, &pred_env, vctx, defs, precheck)?;
            Ok(Some(pred_val.to_bool()?))
        }
        _ => Ok(None),
    }
}

// ── Aggregation ─────────────────────────────────────────────────────

/// encode an aggregate in the pure-expression
/// context (fn contracts). Supports fieldless enums and Bool domains
/// via finite unfolding. Other domains are rejected with an error.
#[allow(clippy::too_many_arguments)]
pub(super) fn encode_pure_aggregate(
    kind: crate::ir::types::IRAggKind,
    var: &str,
    domain: &crate::ir::types::IRType,
    body: &IRExpr,
    in_filter: Option<&IRExpr>,
    env: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    precheck: Option<&PrecheckCtx<'_>>,
) -> Result<SmtValue, String> {
    use crate::ir::types::IRAggKind;

    // Collect the domain values to iterate over.
    let values: Vec<SmtValue> = match domain {
        crate::ir::types::IRType::Bool => {
            vec![smt::bool_val(false), smt::bool_val(true)]
        }
        crate::ir::types::IRType::Enum { .. } if !domain.has_variant_fields() => {
            let n = enum_variant_count(domain);
            (0..n).map(|i| smt::int_val(i as i64)).collect()
        }
        _ => {
            return Err(format!(
                "{kind:?} aggregator over `{domain:?}` domain is not supported in \
                 fn contracts — use a fieldless enum or Bool domain"
            ));
        }
    };

    if values.is_empty() {
        return match kind {
            IRAggKind::Sum | IRAggKind::Count => Ok(smt::int_val(0)),
            IRAggKind::Product => Ok(smt::int_val(1)),
            IRAggKind::Min | IRAggKind::Max => Err(format!("{kind:?} over empty domain")),
        };
    }

    // Collect (filter_flag, body_value) for each domain element.
    let mut slot_data: Vec<(Bool, SmtValue)> = Vec::new();
    let mut inner_env = env.clone();
    for v in &values {
        inner_env.insert(var.to_owned(), v.clone());
        let mut flag = smt::bool_const(true);
        if let Some(filter_expr) = in_filter {
            let membership = encode_pure_expr_inner(filter_expr, &inner_env, vctx, defs, precheck)?;
            flag = membership.to_bool()?;
        }
        if kind == IRAggKind::Count {
            let pred = encode_pure_expr_inner(body, &inner_env, vctx, defs, precheck)?;
            let pred_bool = pred.to_bool()?;
            slot_data.push((smt::bool_and(&[&flag, &pred_bool]), smt::int_val(1)));
        } else {
            let val = encode_pure_expr_inner(body, &inner_env, vctx, defs, precheck)?;
            slot_data.push((flag, val));
        }
    }

    match kind {
        IRAggKind::Sum | IRAggKind::Count => {
            let zero = slot_data.first().map_or_else(
                || super::agg_zero_from_ir(body),
                |(_, v)| super::agg_zero(v),
            );
            let mut acc = zero;
            for (cond, val) in &slot_data {
                let z = super::agg_zero(val);
                acc = smt::binop("OpAdd", &acc, &super::ite_value(cond, val, &z))?;
            }
            Ok(acc)
        }
        IRAggKind::Product => {
            let one = slot_data
                .first()
                .map_or_else(|| super::agg_one_from_ir(body), |(_, v)| super::agg_one(v));
            let mut acc = one;
            for (cond, val) in &slot_data {
                let o = super::agg_one(val);
                acc = smt::binop("OpMul", &acc, &super::ite_value(cond, val, &o))?;
            }
            Ok(acc)
        }
        IRAggKind::Min | IRAggKind::Max => {
            if slot_data.is_empty() {
                return Err(format!("{kind:?} over empty domain"));
            }
            let is_min = kind == IRAggKind::Min;
            let op = if is_min { "OpLt" } else { "OpGt" };
            let mut acc = slot_data[0].1.clone();
            let mut any_active = slot_data[0].0.clone();
            for (cond, val) in slot_data.iter().skip(1) {
                let better = smt::binop(op, val, &acc)?.to_bool()?;
                let take = smt::bool_and(&[cond, &better]);
                acc = super::ite_value(&take, val, &acc);
                let first_active = smt::bool_and(&[cond, &smt::bool_not(&any_active)]);
                acc = super::ite_value(&first_active, val, &acc);
                any_active = smt::bool_or(&[&any_active, cond]);
            }
            let undef_name = format!(
                "__agg_{}_pure_{var}_undef",
                if is_min { "min" } else { "max" }
            );
            let undef = if super::ir_expr_is_real(body) {
                smt::real_var(&undef_name)
            } else {
                smt::int_var(&undef_name)
            };
            acc = super::ite_value(&any_active, &acc, &undef);
            Ok(acc)
        }
    }
}

// ── Quantifiers ─────────────────────────────────────────────────────

/// Encode a Z3 native quantifier (forall / exists) for non-entity domains.
///
/// Creates a fresh Z3 constant for the bound variable, encodes the body with
/// that variable in scope, then wraps with `smt::forall` or
/// `smt::exists`. No patterns/triggers — Z3 uses MBQI automatically.
///
/// For restricted domains (enums, refinement types), the body is guarded by
/// a domain predicate:
/// - forall y: E | P(y) → forall y: Int | (y ∈ E) implies P(y)
/// - exists y: E | P(y) → exists y: Int | (y ∈ E) and P(y)
#[allow(clippy::too_many_arguments)]
pub(super) fn encode_z3_quantifier(
    is_forall: bool,
    var: &str,
    domain: &crate::ir::types::IRType,
    body: &IRExpr,
    env: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    precheck: Option<&PrecheckCtx<'_>>,
) -> Result<SmtValue, String> {
    // Create a fresh Z3 constant for the bound variable (ADT-aware via vctx)
    let bound_var = make_z3_var_ctx(var, domain, Some(vctx))?;

    // Extend environment with the bound variable
    let mut inner_env = env.clone();
    inner_env.insert(var.to_owned(), bound_var.clone());

    // Encode the body with the bound variable in scope
    let body_val = encode_pure_expr_inner(body, &inner_env, vctx, defs, precheck)?;
    let body_bool = body_val.to_bool()?;

    let domain_pred = build_domain_predicate(domain, &bound_var, &inner_env, vctx, defs, precheck)?;

    // Combine body with domain predicate:
    // forall: domain_pred implies body
    // exists: domain_pred and body
    let quantified_body = match domain_pred {
        Some(dp) => {
            if is_forall {
                smt::bool_implies(&dp, &body_bool)
            } else {
                smt::bool_and(&[&dp, &body_bool])
            }
        }
        None => body_bool,
    };

    let result = build_z3_quantifier(is_forall, &bound_var, &quantified_body, var, domain)?;
    Ok(SmtValue::Bool(result))
}

/// Return the number of variants in an enum IR type.
pub(super) fn enum_variant_count(ty: &crate::ir::types::IRType) -> usize {
    match ty {
        crate::ir::types::IRType::Enum { variants, .. } => variants.len(),
        _ => 0,
    }
}

/// Build a Z3 quantifier (`exists_const` or `forall_const`) from a bound variable
/// and body. Dispatches on the `SmtValue` variant to extract the Z3 AST node.
pub(super) fn build_z3_quantifier(
    is_forall: bool,
    bound_var: &SmtValue,
    body: &Bool,
    _var: &str,
    _domain: &crate::ir::types::IRType,
) -> Result<Bool, String> {
    let dyn_bound = bound_var.to_dynamic();
    let bounds: &[&Dynamic] = &[&dyn_bound];
    if is_forall {
        Ok(smt::forall(bounds, body))
    } else {
        Ok(smt::exists(bounds, body))
    }
}

// ── Cardinality quantifiers ─────────────────────────────────────────

/// Encode `one x: T | P(x)` — exactly one x satisfies P.
///
/// Semantics: ∃x. D(x) ∧ P(x) ∧ ∀y. D(y) ∧ P(y) → y = x
///
/// where D is the domain predicate (enum range, refinement guard, etc.)
#[allow(clippy::too_many_arguments)]
pub(super) fn encode_z3_one(
    var: &str,
    domain: &crate::ir::types::IRType,
    body: &IRExpr,
    env: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    precheck: Option<&PrecheckCtx<'_>>,
) -> Result<SmtValue, String> {
    // Create bound variable x (ADT-aware via vctx)
    let x_var = make_z3_var_ctx(var, domain, Some(vctx))?;
    let mut x_env = env.clone();
    x_env.insert(var.to_owned(), x_var.clone());

    // Encode P(x)
    let p_x = encode_pure_expr_inner(body, &x_env, vctx, defs, precheck)?.to_bool()?;

    // Domain predicate for x
    let d_x = build_domain_predicate(domain, &x_var, &x_env, vctx, defs, precheck)?;

    // D(x) ∧ P(x)
    let x_satisfies = match &d_x {
        Some(dp) => smt::bool_and(&[dp, &p_x]),
        None => p_x.clone(),
    };

    // Create a fresh bound variable y (different Z3 name, ADT-aware)
    let y_name = format!("{var}__unique");
    let y_var = make_z3_var_ctx(&y_name, domain, Some(vctx))?;
    let mut y_env = env.clone();
    y_env.insert(var.to_owned(), y_var.clone());

    // Encode P(y) — same body, but with y bound to the quantifier variable
    let p_y = encode_pure_expr_inner(body, &y_env, vctx, defs, precheck)?.to_bool()?;

    // Domain predicate for y
    let d_y = build_domain_predicate(domain, &y_var, &y_env, vctx, defs, precheck)?;

    // D(y) ∧ P(y) → y = x
    let y_satisfies = match &d_y {
        Some(dp) => smt::bool_and(&[dp, &p_y]),
        None => p_y,
    };
    let y_eq_x = smt::smt_eq(&y_var, &x_var)?;
    let uniqueness_body = smt::bool_implies(&y_satisfies, &y_eq_x);

    // ∀y. D(y) ∧ P(y) → y = x
    let forall_unique = build_z3_quantifier(true, &y_var, &uniqueness_body, &y_name, domain)?;

    // ∃x. D(x) ∧ P(x) ∧ (∀y. D(y) ∧ P(y) → y = x)
    let exists_body = smt::bool_and(&[&x_satisfies, &forall_unique]);
    let result = build_z3_quantifier(false, &x_var, &exists_body, var, domain)?;

    Ok(SmtValue::Bool(result))
}

/// Encode `lone x: T | P(x)` — at most one x satisfies P.
///
/// Semantics: ∀x, y. D(x) ∧ D(y) ∧ P(x) ∧ P(y) → x = y
///
/// where D is the domain predicate (enum range, refinement guard, etc.)
#[allow(clippy::too_many_arguments)]
pub(super) fn encode_z3_lone(
    var: &str,
    domain: &crate::ir::types::IRType,
    body: &IRExpr,
    env: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    precheck: Option<&PrecheckCtx<'_>>,
) -> Result<SmtValue, String> {
    // Create bound variable x (ADT-aware via vctx)
    let x_var = make_z3_var_ctx(var, domain, Some(vctx))?;
    let mut x_env = env.clone();
    x_env.insert(var.to_owned(), x_var.clone());

    // Create bound variable y (different Z3 name, ADT-aware)
    let y_name = format!("{var}__unique");
    let y_var = make_z3_var_ctx(&y_name, domain, Some(vctx))?;
    let mut y_env = env.clone();
    y_env.insert(var.to_owned(), y_var.clone());

    // Encode P(x) and P(y)
    let p_x = encode_pure_expr_inner(body, &x_env, vctx, defs, precheck)?.to_bool()?;
    let p_y = encode_pure_expr_inner(body, &y_env, vctx, defs, precheck)?.to_bool()?;

    // Domain predicates
    let d_x = build_domain_predicate(domain, &x_var, &x_env, vctx, defs, precheck)?;
    let d_y = build_domain_predicate(domain, &y_var, &y_env, vctx, defs, precheck)?;

    // D(x) ∧ D(y) ∧ P(x) ∧ P(y)
    let mut antecedents = Vec::new();
    if let Some(dp) = &d_x {
        antecedents.push(dp.clone());
    }
    if let Some(dp) = &d_y {
        antecedents.push(dp.clone());
    }
    antecedents.push(p_x);
    antecedents.push(p_y);
    let antecedent_refs: Vec<&Bool> = antecedents.iter().collect();
    let lhs = smt::bool_and(&antecedent_refs);

    // x = y
    let x_eq_y = smt::smt_eq(&x_var, &y_var)?;

    // D(x) ∧ D(y) ∧ P(x) ∧ P(y) → x = y
    let forall_body = smt::bool_implies(&lhs, &x_eq_y);

    // ∀y. [body]
    let inner = build_z3_quantifier(true, &y_var, &forall_body, &y_name, domain)?;
    // ∀x. ∀y. [body]
    let result = build_z3_quantifier(true, &x_var, &inner, var, domain)?;

    Ok(SmtValue::Bool(result))
}

// ── Lambda encoding ─────────────────────────────────────────────────

/// Encode a lambda expression as a Z3 uninterpreted function with a
/// definitional axiom.
///
/// For `fn(x: T): R => body`:
/// 1. Uncurry nested Lams to get all parameters
/// 2. Create `smt::func_decl("__lambda_N", domain_sorts, range_sort)`
/// 3. Create Z3 bound variables for each parameter
/// 4. Encode the body with parameters in scope
/// 5. Assert definitional axiom: `forall params. f(params) == body`
/// 6. Return `SmtValue::Func(func_decl)`
///
/// Handles curried lambdas: `Lam(x, Lam(y, body))` → `f(x, y) == body`.
fn encode_lambda(
    expr: &IRExpr,
    env: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    precheck: Option<&PrecheckCtx<'_>>,
) -> Result<SmtValue, String> {
    // Uncurry: collect all nested Lam parameters
    let mut params: Vec<(&str, &crate::ir::types::IRType)> = Vec::new();
    let mut current = expr;
    while let IRExpr::Lam {
        param,
        param_type,
        body,
        ..
    } = current
    {
        params.push((param.as_str(), param_type));
        current = body;
    }
    let body_expr = current;

    if params.is_empty() {
        return Err("empty lambda (no parameters)".to_owned());
    }

    // Create Z3 variables for parameters (ADT-aware via vctx)
    let mut inner_env = env.clone();
    let mut bound_vars: Vec<SmtValue> = Vec::new();
    let mut domain_sorts: Vec<Sort> = Vec::new();
    for (pname, pty) in &params {
        let var = make_z3_var_ctx(pname, pty, Some(vctx))?;
        // Extract the sort from the created variable
        let sort = smt::dynamic_sort(&var.to_dynamic());
        domain_sorts.push(sort);
        inner_env.insert((*pname).to_owned(), var.clone());
        bound_vars.push(var);
    }
    let domain_refs: Vec<&Sort> = domain_sorts.iter().collect();

    // Encode the body with all params in scope
    let body_val = encode_pure_expr_inner(body_expr, &inner_env, vctx, defs, precheck)?;

    // Determine range sort from the encoded body value
    let range_sort = smt::dynamic_sort(&body_val.to_dynamic());

    // Create the uninterpreted function
    let lambda_id = LAMBDA_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let func_name = format!("__lambda_{lambda_id}");
    let func_decl = smt::func_decl(func_name.as_str(), &domain_refs, &range_sort);

    // Build the definitional axiom: forall params. f(params) == body
    // Use Dynamic for all parameter types (works for scalars and ADTs)
    let bound_dyns: Vec<Dynamic> = bound_vars.iter().map(SmtValue::to_dynamic).collect();
    let app_args: Vec<&Dynamic> = bound_dyns.iter().collect();
    let app_result = smt::func_decl_apply(&func_decl, &app_args);
    let app_smt = dynamic_to_smt_value(app_result);
    let eq = smt::smt_eq(&app_smt, &body_val)?;

    // Quantify over all parameters using Dynamic binders
    let bounds: Vec<&Dynamic> = bound_dyns.iter().collect();
    let axiom = smt::forall(&bounds, &eq);

    super::push_lambda_axiom(axiom);

    Ok(SmtValue::Func(std::rc::Rc::new((
        func_decl,
        domain_sorts,
        range_sort,
    ))))
}

/// Encode a partial application as a new uninterpreted function.
///
/// Given `f(a1,..., ak)` where `f` has arity `n > k`, creates a fresh
/// function `g(x_{k+1},..., x_n)` with axiom:
/// `forall x_{k+1},..., x_n. g(x_{k+1},..., x_n) = f(a1,..., ak, x_{k+1},..., x_n)`
///
/// This models currying: `add(1)` creates `inc(y) = add(1, y)`.
fn encode_partial_application(
    orig_func: &FuncDecl,
    param_sorts: &[Sort],
    range_sort: &Sort,
    bound_args: &[Dynamic],
) -> Result<SmtValue, String> {
    let remaining_param_sorts: Vec<Sort> = param_sorts[bound_args.len()..].to_vec();
    let remaining_sort_refs: Vec<&Sort> = remaining_param_sorts.iter().collect();

    // Create fresh function symbol for the partial application
    let partial_id = LAMBDA_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let partial_name = format!("__partial_{partial_id}");
    let partial_func = smt::func_decl(partial_name.as_str(), &remaining_sort_refs, range_sort);

    // Create bound variables for the remaining parameters
    let mut remaining_vars: Vec<Dynamic> = Vec::new();
    for (i, sort) in remaining_param_sorts.iter().enumerate() {
        let var_name = format!("__parg_{partial_id}_{i}");
        remaining_vars.push(smt::dynamic_const(var_name.as_str(), sort));
    }

    // Build: g(x_{k+1},..., x_n)
    let partial_arg_refs: Vec<&Dynamic> = remaining_vars.iter().collect();
    let partial_app = smt::func_decl_apply(&partial_func, &partial_arg_refs);

    // Build: f(a1,..., ak, x_{k+1},..., x_n)
    let mut full_args: Vec<Dynamic> = bound_args.to_vec();
    full_args.extend(remaining_vars.iter().cloned());
    let full_arg_refs: Vec<&Dynamic> = full_args.iter().collect();
    let full_app = smt::func_decl_apply(orig_func, &full_arg_refs);

    // Definitional axiom: g(remaining) == f(bound, remaining)
    let eq = smt::dynamic_eq(&partial_app, &full_app);

    // Quantify over remaining parameters
    let bounds: Vec<&Dynamic> = remaining_vars.iter().collect();
    let axiom = if bounds.is_empty() {
        eq
    } else {
        smt::forall(&bounds, &eq)
    };

    super::push_lambda_axiom(axiom);

    Ok(SmtValue::Func(std::rc::Rc::new((
        partial_func,
        remaining_param_sorts,
        range_sort.clone(),
    ))))
}

// ── Literal, ITE, match ─────────────────────────────────────────────

/// Encode a literal value to Z3.
pub(super) fn encode_pure_lit(
    value: &crate::ir::types::LitVal,
    _ty: &crate::ir::types::IRType,
) -> Result<SmtValue, String> {
    use crate::ir::types::LitVal;
    match value {
        LitVal::Int { value } => Ok(smt::int_val(*value)),
        LitVal::Bool { value } => Ok(smt::bool_val(*value)),
        LitVal::Real { value } => {
            // Approximate: convert f64 to rational
            #[allow(clippy::cast_possible_truncation)]
            let scaled = (*value * 1_000_000.0) as i64;
            Ok(smt::real_val(scaled, 1_000_000))
        }
        LitVal::Float { value } => {
            #[allow(clippy::cast_possible_truncation)]
            let scaled = (*value * 1_000_000.0) as i64;
            Ok(smt::real_val(scaled, 1_000_000))
        }
        LitVal::Str { value } => {
            // Strings are encoded as Int (see smt::ir_type_to_sort).
            // Each distinct string literal must produce a distinct Int constant.
            // We use a deterministic hash so "a" != "b" but "a" == "a".
            use std::hash::{Hash, Hasher};
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            value.hash(&mut hasher);
            // Use the lower 62 bits to stay safely in i64 range
            let hash = (hasher.finish() & 0x3FFF_FFFF_FFFF_FFFF) as i64;
            Ok(smt::int_val(hash))
        }
    }
}

/// Encode an if-then-else at the `SmtValue` level.
pub(super) fn encode_ite(
    cond: &Bool,
    then_val: &SmtValue,
    else_val: &SmtValue,
) -> Result<SmtValue, String> {
    match (then_val, else_val) {
        (SmtValue::Int(t), SmtValue::Int(e)) => Ok(SmtValue::Int(smt::int_ite(cond, t, e))),
        (SmtValue::Bool(t), SmtValue::Bool(e)) => Ok(SmtValue::Bool(smt::bool_ite(cond, t, e))),
        (SmtValue::Real(t), SmtValue::Real(e)) => Ok(SmtValue::Real(smt::real_ite(cond, t, e))),
        (SmtValue::Array(t), SmtValue::Array(e)) => Ok(SmtValue::Array(smt::array_ite(cond, t, e))),
        (SmtValue::Dynamic(t), SmtValue::Dynamic(e)) => {
            Ok(SmtValue::Dynamic(smt::dynamic_ite(cond, t, e)))
        }
        // Cross-variant: coerce to Dynamic
        _ => {
            let t_dyn = then_val.to_dynamic();
            let e_dyn = else_val.to_dynamic();
            Ok(SmtValue::Dynamic(smt::dynamic_ite(cond, &t_dyn, &e_dyn)))
        }
    }
}

/// Encode a match expression in the pure context.
///
/// Each arm is encoded as an ITE chain:
/// match e { P1 => b1, P2 => b2, _ => b3 }
/// → ite(P1(e), b1, ite(P2(e), b2, b3))
pub(super) fn encode_pure_match(
    scrut: &SmtValue,
    arms: &[crate::ir::types::IRMatchArm],
    env: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    precheck: Option<&PrecheckCtx<'_>>,
) -> Result<SmtValue, String> {
    if arms.is_empty() {
        return Err("empty match expression".to_owned());
    }

    let mut result: Option<SmtValue> = None;

    for arm in arms.iter().rev() {
        let arm_cond = encode_pattern_cond(scrut, &arm.pattern, env, vctx)?;
        let mut arm_env = env.clone();
        bind_pattern_vars(&arm.pattern, scrut, &mut arm_env, vctx)?;

        let full_cond = if let Some(guard) = &arm.guard {
            let guard_val = encode_pure_expr_inner(guard, &arm_env, vctx, defs, precheck)?;
            let guard_bool = guard_val.to_bool()?;
            SmtValue::Bool(smt::bool_and(&[&arm_cond, &guard_bool]))
        } else {
            SmtValue::Bool(arm_cond.clone())
        };

        let body_val = encode_pure_expr_inner(&arm.body, &arm_env, vctx, defs, precheck)?;

        result = Some(match result {
            Some(else_val) => {
                let cond_bool = full_cond.to_bool()?;
                encode_ite(&cond_bool, &body_val, &else_val)?
            }
            None => body_val, // last arm = default
        });
    }

    result.ok_or_else(|| "empty match".to_owned())
}

// ── Pattern matching helpers ────────────────────────────────────────

/// Find the ADT sort that matches a scrutinee's Z3 sort.
/// Returns `(enum_name, &DatatypeSort)` if found.
pub(super) fn resolve_scrut_adt<'a>(
    scrut: &SmtValue,
    vctx: &'a VerifyContext,
) -> Option<(&'a str, &'a smt::DatatypeSort)> {
    if let SmtValue::Dynamic(d) = scrut {
        let scrut_sort = smt::sort_name(&smt::dynamic_sort(d));
        for (name, dt) in &vctx.adt_sorts {
            if smt::sort_name(&dt.sort()) == scrut_sort {
                return Some((name.as_str(), dt));
            }
        }
    }
    None
}

/// Encode a pattern match condition as a Z3 Bool.
///
/// Constructor patterns are resolved against the scrutinee's ADT sort
/// (type-directed), not by scanning all ADTs globally.
pub(super) fn encode_pattern_cond(
    scrut: &SmtValue,
    pattern: &crate::ir::types::IRPattern,
    _env: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
) -> Result<Bool, String> {
    use crate::ir::types::IRPattern;
    match pattern {
        IRPattern::PWild | IRPattern::PVar { .. } => Ok(smt::bool_const(true)),
        IRPattern::PCtor { name, .. } => {
            // Type-directed: resolve against the scrutinee's ADT sort
            if let Some((_enum_name, dt)) = resolve_scrut_adt(scrut, vctx) {
                for variant in &dt.variants {
                    let ctor_name = smt::func_decl_name(&variant.constructor);
                    if ctor_name == *name || format!("{_enum_name}::{ctor_name}") == *name {
                        let scrut_dyn = scrut.to_dynamic();
                        let result = smt::func_decl_apply(&variant.tester, &[&scrut_dyn]);
                        return smt::dynamic_as_bool(&result)
                            .ok_or_else(|| format!("ADT tester did not return Bool for {name}"));
                    }
                }
                return Err(format!(
                    "unknown constructor '{name}' for enum '{_enum_name}'"
                ));
            }
            // Fallback: flat Int encoding for fieldless enums
            let scrut_int = scrut.as_int()?;
            for ((type_name, variant_name), id) in &vctx.variants.to_id {
                if variant_name == name || format!("{type_name}::{variant_name}") == *name {
                    return Ok(smt::int_eq(scrut_int, &smt::int_lit(*id)));
                }
            }
            Err(format!("unknown constructor pattern: {name}"))
        }
        IRPattern::POr { left, right } => {
            let l = encode_pattern_cond(scrut, left, _env, vctx)?;
            let r = encode_pattern_cond(scrut, right, _env, vctx)?;
            Ok(smt::bool_or(&[&l, &r]))
        }
    }
}

/// Bind pattern variables into the environment.
///
/// For ADT-encoded enums with constructor fields, extracts field values
/// using Z3 datatype accessor functions. For fieldless enums, no bindings
/// are needed from the constructor itself.
pub(super) fn bind_pattern_vars(
    pattern: &crate::ir::types::IRPattern,
    scrut: &SmtValue,
    env: &mut HashMap<String, SmtValue>,
    vctx: &VerifyContext,
) -> Result<(), String> {
    use crate::ir::types::IRPattern;
    match pattern {
        IRPattern::PVar { name } => {
            env.insert(name.clone(), scrut.clone());
            Ok(())
        }
        IRPattern::PWild => Ok(()),
        IRPattern::PCtor { name, fields } => {
            if fields.is_empty() {
                return Ok(());
            }
            // Type-directed: resolve against the scrutinee's ADT sort
            if let Some((_enum_name, dt)) = resolve_scrut_adt(scrut, vctx) {
                for variant in &dt.variants {
                    let ctor_name = smt::func_decl_name(&variant.constructor);
                    if ctor_name == *name
                        || !_enum_name.is_empty() && format!("{_enum_name}::{ctor_name}") == *name
                    {
                        // Extract fields by name — match each pattern field to
                        // the accessor with the same name, not by position.
                        let scrut_dyn = scrut.to_dynamic();
                        for field_pat in fields {
                            let accessor = variant
                                .accessors
                                .iter()
                                .find(|a| smt::func_decl_name(a) == field_pat.name)
                                .ok_or_else(|| {
                                    format!(
                                        "unknown field '{}' in pattern for constructor '{name}'",
                                        field_pat.name
                                    )
                                })?;
                            let field_val = smt::func_decl_apply(accessor, &[&scrut_dyn]);
                            let smt_val = dynamic_to_smt_value(field_val);
                            bind_pattern_vars(&field_pat.pattern, &smt_val, env, vctx)?;
                        }
                        return Ok(());
                    }
                }
            }
            Err(format!(
                "constructor field destructuring requires algebraic datatype encoding — \
                 enum variant '{name}' not found in registered ADT sorts"
            ))
        }
        IRPattern::POr { left, right } => {
            bind_pattern_vars(left, scrut, env, vctx)?;
            bind_pattern_vars(right, scrut, env, vctx)
        }
    }
}

/// Collect variable names bound by a pattern (for binder-aware traversal).
pub(super) fn collect_pattern_binders(
    pat: &crate::ir::types::IRPattern,
    bound: &mut HashSet<String>,
) {
    match pat {
        crate::ir::types::IRPattern::PVar { name } => {
            bound.insert(name.clone());
        }
        crate::ir::types::IRPattern::PCtor { fields, .. } => {
            for f in fields {
                collect_pattern_binders(&f.pattern, bound);
            }
        }
        crate::ir::types::IRPattern::POr { left, right } => {
            collect_pattern_binders(left, bound);
            collect_pattern_binders(right, bound);
        }
        crate::ir::types::IRPattern::PWild => {}
    }
}

#[cfg(test)]
#[allow(clippy::needless_borrows_for_generic_args)]
mod tests {
    use super::*;
    use crate::ir::types::{
        IRExpr, IRFunction, IRMatchArm, IRPattern, IRProgram, IRType, IRTypeEntry, IRVariant,
        LitVal,
    };

    fn empty_ir() -> IRProgram {
        IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        }
    }

    fn enum_ir() -> IRProgram {
        IRProgram {
            types: vec![IRTypeEntry {
                name: "Status".to_owned(),
                ty: IRType::Enum {
                    name: "Status".to_owned(),
                    variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
                },
            }],
            ..empty_ir()
        }
    }

    #[test]
    fn make_z3_var_covers_supported_and_unsupported_types() {
        assert!(matches!(
            make_z3_var("x", &IRType::Int),
            Ok(SmtValue::Int(_))
        ));
        assert!(matches!(
            make_z3_var("b", &IRType::Bool),
            Ok(SmtValue::Bool(_))
        ));
        assert!(matches!(
            make_z3_var("r", &IRType::Real),
            Ok(SmtValue::Real(_))
        ));
        assert!(matches!(
            make_z3_var(
                "s",
                &IRType::Set {
                    element: Box::new(IRType::Int)
                }
            ),
            Ok(SmtValue::Array(_))
        ));
        assert!(matches!(
            make_z3_var(
                "x",
                &IRType::Refinement {
                    base: Box::new(IRType::Int),
                    predicate: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                        span: None,
                    }),
                }
            ),
            Ok(SmtValue::Int(_))
        ));
        assert!(make_z3_var(
            "e",
            &IRType::Entity {
                name: "Order".to_owned()
            }
        )
        .is_err());
    }

    #[test]
    fn encode_pure_lit_and_ite_cover_all_literal_kinds() {
        assert!(matches!(
            encode_pure_lit(&LitVal::Int { value: 3 }, &IRType::Int),
            Ok(SmtValue::Int(_))
        ));
        assert!(matches!(
            encode_pure_lit(&LitVal::Bool { value: true }, &IRType::Bool),
            Ok(SmtValue::Bool(_))
        ));
        assert!(matches!(
            encode_pure_lit(&LitVal::Real { value: 1.5 }, &IRType::Real),
            Ok(SmtValue::Real(_))
        ));
        assert!(matches!(
            encode_pure_lit(&LitVal::Float { value: 2.5 }, &IRType::Float),
            Ok(SmtValue::Real(_))
        ));
        assert!(matches!(
            encode_pure_lit(
                &LitVal::Str {
                    value: "abc".to_owned()
                },
                &IRType::String
            ),
            Ok(SmtValue::Int(_))
        ));

        let cond = smt::bool_const(true);
        assert!(matches!(
            encode_ite(&cond, &smt::int_val(1), &smt::int_val(2)),
            Ok(SmtValue::Int(_))
        ));
        assert!(matches!(
            encode_ite(&cond, &smt::bool_val(true), &smt::bool_val(false)),
            Ok(SmtValue::Bool(_))
        ));
        assert!(matches!(
            encode_ite(&cond, &smt::real_val(1, 1), &smt::real_val(2, 1)),
            Ok(SmtValue::Real(_))
        ));
        assert!(matches!(
            encode_ite(&cond, &smt::int_val(1), &smt::bool_val(false)),
            Ok(SmtValue::Dynamic(_))
        ));
    }

    #[test]
    fn build_domain_predicate_handles_enum_and_refinement() {
        let ir = enum_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);

        let enum_ty = IRType::Enum {
            name: "Status".to_owned(),
            variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
        };
        let bound = smt::int_var("status");
        let pred = build_domain_predicate(&enum_ty, &bound, &HashMap::new(), &vctx, &defs, None)
            .expect("enum predicate")
            .expect("flat enum domain predicate");

        let solver = AbideSolver::new();
        solver.assert(&pred);
        solver.assert(&smt::int_eq(
            bound.as_int().expect("int bound"),
            &smt::int_lit(2),
        ));
        assert_eq!(solver.check(), SatResult::Unsat);

        let refinement = IRType::Refinement {
            base: Box::new(IRType::Int),
            predicate: Box::new(IRExpr::BinOp {
                op: "OpGt".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "$".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
        };
        let refinement_pred = build_domain_predicate(
            &refinement,
            &smt::int_val(1),
            &HashMap::new(),
            &vctx,
            &defs,
            None,
        )
        .expect("refinement predicate")
        .expect("refinement guard");
        let solver = AbideSolver::new();
        solver.assert(&smt::bool_not(&refinement_pred));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn encode_pure_aggregate_covers_bool_and_enum_domains() {
        let ir = enum_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let env = HashMap::new();

        let count_true = encode_pure_aggregate(
            crate::ir::types::IRAggKind::Count,
            "b",
            &IRType::Bool,
            &IRExpr::Var {
                name: "b".to_owned(),
                ty: IRType::Bool,
                span: None,
            },
            None,
            &env,
            &vctx,
            &defs,
            None,
        )
        .expect("count aggregate");
        let solver = AbideSolver::new();
        solver.assert(&smt::bool_not(&smt::int_eq(
            count_true.as_int().expect("count int"),
            &smt::int_lit(1),
        )));
        assert_eq!(solver.check(), SatResult::Unsat);

        let sum_enum_ids = encode_pure_aggregate(
            crate::ir::types::IRAggKind::Sum,
            "s",
            &IRType::Enum {
                name: "Status".to_owned(),
                variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
            },
            &IRExpr::Var {
                name: "s".to_owned(),
                ty: IRType::Int,
                span: None,
            },
            None,
            &env,
            &vctx,
            &defs,
            None,
        )
        .expect("sum aggregate");
        let solver = AbideSolver::new();
        solver.assert(&smt::bool_not(&smt::int_eq(
            sum_enum_ids.as_int().expect("sum int"),
            &smt::int_lit(1),
        )));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn encode_pattern_and_match_helpers_cover_common_cases() {
        let ir = enum_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let env = HashMap::from([("x".to_owned(), smt::int_val(1))]);

        let match_expr = IRExpr::Match {
            scrutinee: Box::new(IRExpr::Var {
                name: "x".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            arms: vec![
                IRMatchArm {
                    pattern: IRPattern::PCtor {
                        name: "Done".to_owned(),
                        fields: vec![],
                    },
                    guard: None,
                    body: IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },
                        span: None,
                    },
                },
                IRMatchArm {
                    pattern: IRPattern::PWild,
                    guard: None,
                    body: IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },
                        span: None,
                    },
                },
            ],
            span: None,
        };
        let result = encode_pure_expr(&match_expr, &env, &vctx, &defs).expect("match encoding");
        let solver = AbideSolver::new();
        solver.assert(&smt::bool_not(&smt::int_eq(
            result.as_int().expect("match int"),
            &smt::int_lit(1),
        )));
        assert_eq!(solver.check(), SatResult::Unsat);

        let cond = encode_pattern_cond(
            &smt::int_val(0),
            &IRPattern::POr {
                left: Box::new(IRPattern::PCtor {
                    name: "Pending".to_owned(),
                    fields: vec![],
                }),
                right: Box::new(IRPattern::PWild),
            },
            &HashMap::new(),
            &vctx,
        )
        .expect("pattern cond");
        let solver = AbideSolver::new();
        solver.assert(&smt::bool_not(&cond));
        assert_eq!(solver.check(), SatResult::Unsat);

        let mut binders = HashSet::new();
        collect_pattern_binders(
            &IRPattern::POr {
                left: Box::new(IRPattern::PVar {
                    name: "lhs".to_owned(),
                }),
                right: Box::new(IRPattern::PVar {
                    name: "rhs".to_owned(),
                }),
            },
            &mut binders,
        );
        assert!(binders.contains("lhs"));
        assert!(binders.contains("rhs"));

        let mut bound_env = HashMap::new();
        bind_pattern_vars(
            &IRPattern::PVar {
                name: "captured".to_owned(),
            },
            &smt::int_val(7),
            &mut bound_env,
            &vctx,
        )
        .expect("bind pattern var");
        assert!(matches!(bound_env.get("captured"), Some(SmtValue::Int(_))));
    }

    #[test]
    fn encode_pure_expr_checked_rejects_falsifiable_preconditions() {
        let function = IRFunction {
            name: "positive".to_owned(),
            ty: IRType::Fn {
                param: Box::new(IRType::Int),
                result: Box::new(IRType::Int),
            },
            requires: vec![IRExpr::BinOp {
                op: "OpGt".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }],
            ensures: vec![],
            decreases: None,
            body: IRExpr::Lam {
                param: "x".to_owned(),
                param_type: IRType::Int,
                body: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                span: None,
            },
            prop_target: None,
            span: None,
            file: None,
        };
        let ir = IRProgram {
            functions: vec![function],
            ..empty_ir()
        };
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let env = HashMap::new();
        let precheck = PrecheckCtx {
            fn_requires: &[],
            extra_assumptions: &[],
            self_fn: None,
        };
        let app = IRExpr::App {
            func: Box::new(IRExpr::Var {
                name: "positive".to_owned(),
                ty: IRType::Fn {
                    param: Box::new(IRType::Int),
                    result: Box::new(IRType::Int),
                },
                span: None,
            }),
            arg: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },
                span: None,
            }),
            ty: IRType::Int,
            span: None,
        };
        let err = encode_pure_expr_checked(&app, &env, &vctx, &defs, &precheck)
            .expect_err("falsifiable precondition should be rejected");
        assert_eq!(err, crate::messages::FN_CALL_PRECONDITION_FAILED);
    }
}
