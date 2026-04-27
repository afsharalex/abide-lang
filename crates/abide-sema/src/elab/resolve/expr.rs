//! Expression resolution — name and constructor resolution in expression trees.

use super::super::types::{EExpr, EPattern, Ty};
use std::collections::HashMap;

use super::Ctx;

fn infer_field_type(ctx: &Ctx, base: &EExpr, field_name: &str) -> Ty {
    let entity_name: Option<String> = match base.ty() {
        Ty::Entity(name) => Some(name.clone()),
        Ty::Named(name) if ctx.entities.contains_key(name.as_str()) => Some(name.clone()),
        other => {
            let name = other.name();
            ctx.entities.contains_key(name).then(|| name.to_owned())
        }
    };

    if let Some(entity_name) = entity_name {
        if let Some(entity) = ctx.entities.get(entity_name.as_str()) {
            if let Some(field) = entity.fields.iter().find(|f| f.name == field_name) {
                return field.ty.clone();
            }
        }
    }

    Ty::Error
}

fn infer_qualcall_type(type_name: &str, func_name: &str, args: &[EExpr]) -> Ty {
    let bool_ty = Ty::Builtin(crate::elab::types::BuiltinTy::Bool);
    let int_ty = Ty::Builtin(crate::elab::types::BuiltinTy::Int);
    match (type_name, func_name) {
        ("Set", "union" | "intersect" | "diff") => args
            .first()
            .map(|arg| arg.ty().clone())
            .unwrap_or(Ty::Error),
        ("Set", "member" | "subset" | "disjoint") => bool_ty,
        ("Seq", "head") => match args.first().map(EExpr::ty) {
            Some(Ty::Seq(element)) => element.as_ref().clone(),
            _ => Ty::Error,
        },
        ("Seq", "tail" | "concat") => args
            .first()
            .map(|arg| arg.ty().clone())
            .unwrap_or(Ty::Error),
        ("Seq", "length") => int_ty,
        ("Seq", "empty") => bool_ty,
        ("Map", "has") => bool_ty,
        ("Map", "domain") => match args.first().map(EExpr::ty) {
            Some(Ty::Map(key, _)) => Ty::Set(Box::new(key.as_ref().clone())),
            _ => Ty::Error,
        },
        ("Map", "range") => match args.first().map(EExpr::ty) {
            Some(Ty::Map(_, value)) => Ty::Set(Box::new(value.as_ref().clone())),
            _ => Ty::Error,
        },
        ("Map", "merge") => args
            .first()
            .map(|arg| arg.ty().clone())
            .unwrap_or(Ty::Error),
        _ => Ty::Error,
    }
}

fn infer_index_type(map: &EExpr) -> Ty {
    match map.ty() {
        Ty::Map(_, value) => value.as_ref().clone(),
        Ty::Seq(element) => element.as_ref().clone(),
        _ => Ty::Error,
    }
}

/// Resolve names and constructors within an expression tree.
#[allow(clippy::too_many_lines)]
pub(super) fn resolve_expr(ctx: &Ctx, bound: &HashMap<String, Ty>, expr: &EExpr) -> EExpr {
    match expr {
        EExpr::Var(_, name, sp) => {
            if let Some(bound_ty) = bound.get(name) {
                // Bound variable: use the declared type from the binding scope.
                // Don't alias-rewrite or constructor-resolve.
                EExpr::Var(bound_ty.clone(), name.clone(), *sp)
            } else {
                let resolved_name = ctx.canonical_name(name).to_owned();
                let resolved_ty = resolve_var_type(ctx, &resolved_name);
                EExpr::Var(resolved_ty, resolved_name, *sp)
            }
        }
        EExpr::Field(_ty, e, f, sp) => {
            let resolved_base = resolve_expr(ctx, bound, e);
            let resolved_ty = infer_field_type(ctx, &resolved_base, f);
            EExpr::Field(resolved_ty, Box::new(resolved_base), f.clone(), *sp)
        }
        EExpr::Prime(ty, e, sp) => {
            EExpr::Prime(ty.clone(), Box::new(resolve_expr(ctx, bound, e)), *sp)
        }
        EExpr::BinOp(ty, op, a, b, sp) => EExpr::BinOp(
            ty.clone(),
            *op,
            Box::new(resolve_expr(ctx, bound, a)),
            Box::new(resolve_expr(ctx, bound, b)),
            *sp,
        ),
        EExpr::UnOp(ty, op, e, sp) => {
            EExpr::UnOp(ty.clone(), *op, Box::new(resolve_expr(ctx, bound, e)), *sp)
        }
        EExpr::Call(ty, f, args, sp) => EExpr::Call(
            ty.clone(),
            Box::new(resolve_expr(ctx, bound, f)),
            args.iter().map(|e| resolve_expr(ctx, bound, e)).collect(),
            *sp,
        ),
        EExpr::QualCall(_ty, type_name, func_name, args, sp) => {
            let resolved_args: Vec<EExpr> =
                args.iter().map(|e| resolve_expr(ctx, bound, e)).collect();
            let resolved_ty = infer_qualcall_type(type_name, func_name, &resolved_args);
            EExpr::QualCall(
                resolved_ty,
                type_name.clone(),
                func_name.clone(),
                resolved_args,
                *sp,
            )
        }
        EExpr::CallR(ty, f, refs, args, sp) => EExpr::CallR(
            ty.clone(),
            Box::new(resolve_expr(ctx, bound, f)),
            refs.iter().map(|e| resolve_expr(ctx, bound, e)).collect(),
            args.iter().map(|e| resolve_expr(ctx, bound, e)).collect(),
            *sp,
        ),
        EExpr::Quant(ty, q, v, vty, body, sp) => {
            let resolved_vty = ctx.resolve_ty(vty);
            let mut inner_bound = bound.clone();
            inner_bound.insert(v.clone(), resolved_vty.clone());
            EExpr::Quant(
                ty.clone(),
                *q,
                v.clone(),
                resolved_vty,
                Box::new(resolve_expr(ctx, &inner_bound, body)),
                *sp,
            )
        }
        EExpr::Always(ty, e, sp) => {
            EExpr::Always(ty.clone(), Box::new(resolve_expr(ctx, bound, e)), *sp)
        }
        EExpr::Eventually(ty, e, sp) => {
            EExpr::Eventually(ty.clone(), Box::new(resolve_expr(ctx, bound, e)), *sp)
        }
        EExpr::Until(ty, l, r, sp) => EExpr::Until(
            ty.clone(),
            Box::new(resolve_expr(ctx, bound, l)),
            Box::new(resolve_expr(ctx, bound, r)),
            *sp,
        ),
        EExpr::Historically(ty, e, sp) => {
            EExpr::Historically(ty.clone(), Box::new(resolve_expr(ctx, bound, e)), *sp)
        }
        EExpr::Once(ty, e, sp) => {
            EExpr::Once(ty.clone(), Box::new(resolve_expr(ctx, bound, e)), *sp)
        }
        EExpr::Previously(ty, e, sp) => {
            EExpr::Previously(ty.clone(), Box::new(resolve_expr(ctx, bound, e)), *sp)
        }
        EExpr::Since(ty, l, r, sp) => EExpr::Since(
            ty.clone(),
            Box::new(resolve_expr(ctx, bound, l)),
            Box::new(resolve_expr(ctx, bound, r)),
            *sp,
        ),
        EExpr::Assert(ty, e, sp) => {
            EExpr::Assert(ty.clone(), Box::new(resolve_expr(ctx, bound, e)), *sp)
        }
        EExpr::Assume(ty, e, sp) => {
            EExpr::Assume(ty.clone(), Box::new(resolve_expr(ctx, bound, e)), *sp)
        }
        EExpr::CtorRecord(ty, qual, name, fields, sp) => {
            // Resolve the type: find which enum contains this constructor
            let resolved_ty = if matches!(ty, Ty::Named(_)) {
                if let Some(q) = qual {
                    // Qualified: @Enum::Ctor — look up the enum directly
                    ctx.types
                        .get(q.as_str())
                        .cloned()
                        .unwrap_or_else(|| ty.clone())
                } else {
                    // Unqualified: @Ctor { field: val,... }
                    // Disambiguate by matching user-provided field names against
                    // each candidate enum's declared fields. This avoids HashMap
                    // iteration order nondeterminism when multiple enums share
                    // a constructor name.
                    let user_field_names: Vec<&str> =
                        fields.iter().map(|(n, _)| n.as_str()).collect();
                    let mut candidates: Vec<&Ty> = Vec::new();
                    for t in ctx.types.values() {
                        if let Ty::Enum(en, ctors) = t {
                            if ctors.contains(name) {
                                // Check if declared fields match user fields
                                if let Some(variants) = ctx.variant_fields.get(en.as_str()) {
                                    for (vname, vfields) in variants {
                                        if vname == name {
                                            let decl_names: Vec<&str> =
                                                vfields.iter().map(|(n, _)| n.as_str()).collect();
                                            if user_field_names
                                                .iter()
                                                .all(|f| decl_names.contains(f))
                                            {
                                                candidates.push(t);
                                            }
                                            break;
                                        }
                                    }
                                } else {
                                    // No field info — fieldless enum, include as candidate
                                    candidates.push(t);
                                }
                            }
                        }
                    }
                    if candidates.len() == 1 {
                        candidates[0].clone()
                    } else {
                        // Zero or multiple matches — leave unresolved so later validation handles it
                        ty.clone()
                    }
                }
            } else {
                ty.clone()
            };
            EExpr::CtorRecord(
                resolved_ty,
                qual.clone(),
                name.clone(),
                fields
                    .iter()
                    .map(|(n, e)| (n.clone(), resolve_expr(ctx, bound, e)))
                    .collect(),
                *sp,
            )
        }
        // struct constructor — resolve the struct type and recurse into fields
        EExpr::StructCtor(ty, name, fields, sp) => {
            let resolved_ty = if matches!(ty, Ty::Named(_)) {
                ctx.types
                    .get(name.as_str())
                    .cloned()
                    .unwrap_or_else(|| ty.clone())
            } else {
                ty.clone()
            };
            EExpr::StructCtor(
                resolved_ty,
                name.clone(),
                fields
                    .iter()
                    .map(|(n, e)| (n.clone(), resolve_expr(ctx, bound, e)))
                    .collect(),
                *sp,
            )
        }
        EExpr::Assign(ty, lhs, rhs, sp) => EExpr::Assign(
            ty.clone(),
            Box::new(resolve_expr(ctx, bound, lhs)),
            Box::new(resolve_expr(ctx, bound, rhs)),
            *sp,
        ),
        EExpr::NamedPair(ty, n, e, sp) => EExpr::NamedPair(
            ty.clone(),
            n.clone(),
            Box::new(resolve_expr(ctx, bound, e)),
            *sp,
        ),
        EExpr::Seq(ty, a, b, sp) => EExpr::Seq(
            ty.clone(),
            Box::new(resolve_expr(ctx, bound, a)),
            Box::new(resolve_expr(ctx, bound, b)),
            *sp,
        ),
        EExpr::SameStep(ty, a, b, sp) => EExpr::SameStep(
            ty.clone(),
            Box::new(resolve_expr(ctx, bound, a)),
            Box::new(resolve_expr(ctx, bound, b)),
            *sp,
        ),
        EExpr::Let(binds, body, sp) => {
            let mut inner_bound = bound.clone();
            let bs = binds
                .iter()
                .map(|(n, mt, e)| {
                    let resolved_mt = mt.as_ref().map(|t| ctx.resolve_ty(t));
                    let resolved = (
                        n.clone(),
                        resolved_mt.clone(),
                        resolve_expr(ctx, &inner_bound, e),
                    );
                    inner_bound.insert(n.clone(), resolved_mt.unwrap_or(Ty::Error));
                    resolved
                })
                .collect();
            EExpr::Let(bs, Box::new(resolve_expr(ctx, &inner_bound, body)), *sp)
        }
        EExpr::Lam(params, mret, body, sp) => {
            let mut inner_bound = bound.clone();
            for (n, t) in params {
                inner_bound.insert(n.clone(), ctx.resolve_ty(t));
            }
            EExpr::Lam(
                params
                    .iter()
                    .map(|(n, t)| (n.clone(), ctx.resolve_ty(t)))
                    .collect(),
                mret.as_ref().map(|t| ctx.resolve_ty(t)),
                Box::new(resolve_expr(ctx, &inner_bound, body)),
                *sp,
            )
        }
        EExpr::Match(scrut, arms, sp) => {
            let resolved_scrut = resolve_expr(ctx, bound, scrut);
            let resolved_arms = arms
                .iter()
                .map(|(pat, guard, body)| {
                    let mut arm_bound: HashMap<String, Ty> = bound.clone();
                    collect_epattern_vars(pat, &mut arm_bound);
                    let resolved_guard = guard.as_ref().map(|g| resolve_expr(ctx, &arm_bound, g));
                    let resolved_body = resolve_expr(ctx, &arm_bound, body);
                    (pat.clone(), resolved_guard, resolved_body)
                })
                .collect();
            EExpr::Match(Box::new(resolved_scrut), resolved_arms, *sp)
        }
        EExpr::SetComp(ty, proj, var, vty, filter, sp) => {
            let resolved_vty = ctx.resolve_ty(vty);
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.clone(), resolved_vty.clone());
            EExpr::SetComp(
                ty.clone(),
                proj.as_ref()
                    .map(|p| Box::new(resolve_expr(ctx, &inner_bound, p))),
                var.clone(),
                resolved_vty,
                Box::new(resolve_expr(ctx, &inner_bound, filter)),
                *sp,
            )
        }
        EExpr::MapUpdate(_ty, m, k, v, sp) => {
            let resolved_map = resolve_expr(ctx, bound, m);
            let resolved_key = resolve_expr(ctx, bound, k);
            let resolved_value = resolve_expr(ctx, bound, v);
            EExpr::MapUpdate(
                resolved_map.ty().clone(),
                Box::new(resolved_map),
                Box::new(resolved_key),
                Box::new(resolved_value),
                *sp,
            )
        }
        EExpr::Index(_ty, m, k, sp) => {
            let resolved_map = resolve_expr(ctx, bound, m);
            let resolved_key = resolve_expr(ctx, bound, k);
            let resolved_ty = infer_index_type(&resolved_map);
            EExpr::Index(
                resolved_ty,
                Box::new(resolved_map),
                Box::new(resolved_key),
                *sp,
            )
        }
        EExpr::Qual(_, s, n, sp) => {
            let ty = ctx
                .types
                .get(s.as_str())
                .or_else(|| {
                    let last = last_segment(s);
                    ctx.types.get(last)
                })
                .cloned()
                .unwrap_or_else(|| Ty::Named(s.clone()));
            EExpr::Qual(ty, s.clone(), n.clone(), *sp)
        }
        EExpr::TupleLit(ty, es, sp) => EExpr::TupleLit(
            ty.clone(),
            es.iter().map(|e| resolve_expr(ctx, bound, e)).collect(),
            *sp,
        ),
        EExpr::In(ty, a, b, sp) => EExpr::In(
            ty.clone(),
            Box::new(resolve_expr(ctx, bound, a)),
            Box::new(resolve_expr(ctx, bound, b)),
            *sp,
        ),
        EExpr::Card(ty, e, sp) => {
            EExpr::Card(ty.clone(), Box::new(resolve_expr(ctx, bound, e)), *sp)
        }
        EExpr::Pipe(ty, a, b, sp) => EExpr::Pipe(
            ty.clone(),
            Box::new(resolve_expr(ctx, bound, a)),
            Box::new(resolve_expr(ctx, bound, b)),
            *sp,
        ),
        EExpr::Block(items, sp) => EExpr::Block(
            items.iter().map(|e| resolve_expr(ctx, bound, e)).collect(),
            *sp,
        ),
        EExpr::VarDecl(name, ty, init, rest, sp) => {
            let resolved_ty = ty.as_ref().map(|t| ctx.resolve_ty(t));
            let resolved_init = resolve_expr(ctx, bound, init);
            let mut inner_bound = bound.clone();
            inner_bound.insert(name.clone(), resolved_ty.clone().unwrap_or(Ty::Error));
            let resolved_rest = resolve_expr(ctx, &inner_bound, rest);
            EExpr::VarDecl(
                name.clone(),
                resolved_ty,
                Box::new(resolved_init),
                Box::new(resolved_rest),
                *sp,
            )
        }
        EExpr::While(cond, contracts, body, sp) => {
            let resolved_contracts = contracts
                .iter()
                .map(|c| super::resolve_contract(ctx, bound, bound, c))
                .collect();
            EExpr::While(
                Box::new(resolve_expr(ctx, bound, cond)),
                resolved_contracts,
                Box::new(resolve_expr(ctx, bound, body)),
                *sp,
            )
        }
        EExpr::IfElse(cond, then_body, else_body, sp) => EExpr::IfElse(
            Box::new(resolve_expr(ctx, bound, cond)),
            Box::new(resolve_expr(ctx, bound, then_body)),
            else_body
                .as_ref()
                .map(|e| Box::new(resolve_expr(ctx, bound, e))),
            *sp,
        ),
        // ── Collection literals: resolve elements and infer collection type ──
        EExpr::SetLit(_ty, elems, sp) => {
            let resolved_elems: Vec<EExpr> =
                elems.iter().map(|e| resolve_expr(ctx, bound, e)).collect();
            // Infer element type from first element (or leave as unresolved)
            let elem_ty = resolved_elems.first().map_or(Ty::Error, |e| e.ty().clone());
            EExpr::SetLit(Ty::Set(Box::new(elem_ty)), resolved_elems, *sp)
        }
        EExpr::SeqLit(_ty, elems, sp) => {
            let resolved_elems: Vec<EExpr> =
                elems.iter().map(|e| resolve_expr(ctx, bound, e)).collect();
            let elem_ty = resolved_elems.first().map_or(Ty::Error, |e| e.ty().clone());
            EExpr::SeqLit(Ty::Seq(Box::new(elem_ty)), resolved_elems, *sp)
        }
        EExpr::MapLit(_ty, entries, sp) => {
            let resolved_entries: Vec<(EExpr, EExpr)> = entries
                .iter()
                .map(|(k, v)| (resolve_expr(ctx, bound, k), resolve_expr(ctx, bound, v)))
                .collect();
            let key_ty = resolved_entries
                .first()
                .map_or(Ty::Error, |(k, _)| k.ty().clone());
            let val_ty = resolved_entries
                .first()
                .map_or(Ty::Error, |(_, v)| v.ty().clone());
            EExpr::MapLit(
                Ty::Map(Box::new(key_ty), Box::new(val_ty)),
                resolved_entries,
                *sp,
            )
        }
        // resolve aggregate domain + body,
        // then infer the result type. count → Int; others → body type.
        EExpr::Aggregate(_ty, kind, var, domain, body, in_filter, sp) => {
            use crate::ast::AggKind;
            let resolved_domain = ctx.resolve_ty(domain);
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.clone(), resolved_domain.clone());
            let resolved_body = resolve_expr(ctx, &inner_bound, body);
            let resolved_filter = in_filter
                .as_ref()
                .map(|f| Box::new(resolve_expr(ctx, &inner_bound, f)));
            let result_ty = match kind {
                AggKind::Count => Ty::Builtin(crate::elab::types::BuiltinTy::Int),
                AggKind::Sum | AggKind::Product | AggKind::Min | AggKind::Max => {
                    // Infer from body type; default to Int if unresolved.
                    match resolved_body.ty() {
                        Ty::Builtin(crate::elab::types::BuiltinTy::Real) => {
                            Ty::Builtin(crate::elab::types::BuiltinTy::Real)
                        }
                        Ty::Builtin(crate::elab::types::BuiltinTy::Float) => {
                            Ty::Builtin(crate::elab::types::BuiltinTy::Float)
                        }
                        _ => Ty::Builtin(crate::elab::types::BuiltinTy::Int),
                    }
                }
            };
            EExpr::Aggregate(
                result_ty,
                *kind,
                var.clone(),
                resolved_domain,
                Box::new(resolved_body),
                resolved_filter,
                *sp,
            )
        }
        // resolve `saw Extern::command(args)`.
        //
        // Only explicit two-segment type-qualified forms are intended for the
        // extern-boundary slice. We still preserve unqualified and 3+ segment
        // shapes here so `validate_saw_expressions` can reject them with the
        // dedicated boundary diagnostic after alias canonicalization.
        EExpr::Saw(ty, sys, evt, args, sp) => {
            let resolved_args: Vec<Option<Box<EExpr>>> = args
                .iter()
                .map(|a| a.as_ref().map(|e| Box::new(resolve_expr(ctx, bound, e))))
                .collect();

            let canonical_sys = if sys.is_empty() || sys.contains("::") {
                // Unqualified or 3+ segment: pass through unchanged for the
                // dedicated validation pass.
                sys.clone()
            } else {
                ctx.canonical_name(sys).to_owned()
            };

            EExpr::Saw(ty.clone(), canonical_sys, evt.clone(), resolved_args, *sp)
        }
        e => e.clone(),
    }
}

/// Collect variable names bound by a pattern into the given map.
pub(super) fn collect_epattern_vars(pat: &EPattern, vars: &mut HashMap<String, Ty>) {
    match pat {
        EPattern::Var(name) => {
            vars.insert(name.clone(), Ty::Error);
        }
        EPattern::Ctor(_, fields) => {
            for (_, fpat) in fields {
                collect_epattern_vars(fpat, vars);
            }
        }
        EPattern::Wild => {}
        EPattern::Or(left, right) => {
            collect_epattern_vars(left, vars);
            collect_epattern_vars(right, vars);
        }
    }
}

pub(super) fn resolve_var_type(ctx: &Ctx, name: &str) -> Ty {
    if let Some(parent_ty) = find_constructor_type(ctx, name) {
        return parent_ty;
    }
    if let Some(t) = ctx.types.get(name) {
        return t.clone();
    }
    Ty::Error
}

/// When a constructor expression has `Ty::Unresolved` (e.g. `@None` ambiguous across
/// multiple monomorphized generics), use the declared field type to resolve it.
/// If the field type is an enum and the constructor name is one of its variants,
/// patch the expression's type to the field's enum type.
pub(super) fn resolve_ctor_type_from_context(expr: &mut EExpr, field_ty: &Ty) {
    let Ty::Enum(_, ctors) = field_ty else { return };
    match expr {
        EExpr::Var(ref mut ty, name, _) if matches!(ty, Ty::Error) => {
            if ctors.iter().any(|c| c == name) {
                *ty = field_ty.clone();
            }
        }
        // Call wrapping a constructor: @Some(42) → Call(Var(@Some), [42])
        EExpr::Call(ref mut ty, ref mut callee, _, _) if matches!(ty, Ty::Error) => {
            if let EExpr::Var(ref mut inner_ty, name, _) = callee.as_mut() {
                if matches!(inner_ty, Ty::Error) && ctors.iter().any(|c| c == name) {
                    *inner_ty = field_ty.clone();
                    *ty = field_ty.clone();
                }
            }
        }
        EExpr::CtorRecord(ref mut ty, _, name, _, _) if matches!(ty, Ty::Error) => {
            if ctors.iter().any(|c| c == name) {
                *ty = field_ty.clone();
            }
        }
        _ => {}
    }
}

pub(super) fn find_constructor_type(ctx: &Ctx, name: &str) -> Option<Ty> {
    let mut matches: Vec<&Ty> = Vec::new();
    for ty in ctx.types.values() {
        if let Ty::Enum(_, ctors) = ty {
            if ctors.iter().any(|c| c == name) {
                matches.push(ty);
            }
        }
    }
    if matches.len() == 1 {
        return Some(matches[0].clone());
    }
    if matches.len() > 1 {
        // Prefer non-monomorphized (non-generic) types over monomorphized ones.
        // Monomorphized types have `<` in their name (e.g. "Option<Int>").
        let non_mono: Vec<&Ty> = matches
            .iter()
            .filter(|t| {
                if let Ty::Enum(n, _) = t {
                    !n.contains('<')
                } else {
                    true
                }
            })
            .copied()
            .collect();
        if non_mono.len() == 1 {
            return Some(non_mono[0].clone());
        }
        if non_mono.is_empty() {
            // All matches are monomorphized instances of generic(s).
            // Don't pick arbitrarily — leave unresolved for context-driven resolution.
            return None;
        }
        // Multiple non-monomorphized matches — pre-existing ambiguity, return first
        return Some(non_mono[0].clone());
    }
    None
}

pub(super) fn last_segment(s: &str) -> &str {
    s.rsplit("::").next().unwrap_or(s)
}
