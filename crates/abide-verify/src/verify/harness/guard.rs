use std::collections::HashMap;

use super::*;

/// Context for guard expression encoding — tracks entity bindings from
/// enclosing quantifiers, similar to `PropertyCtx` in `mod.rs`.
struct GuardCtx {
    /// Quantifier-bound variables: `var_name` → (`entity_name`, `slot_index`)
    bindings: HashMap<String, (String, usize)>,
    /// Event parameter Z3 variables
    params: HashMap<String, SmtValue>,
    /// system name for flat state field resolution
    system_name: String,
    /// entity-typed param names → entity type name
    entity_param_types: HashMap<String, String>,
    /// store-typed system params → entity type name
    store_param_types: HashMap<String, String>,
}

impl GuardCtx {
    fn with_binding(&self, var: &str, entity: &str, slot: usize) -> Self {
        let mut bindings = self.bindings.clone();
        bindings.insert(var.to_owned(), (entity.to_owned(), slot));
        Self {
            bindings,
            params: self.params.clone(),
            system_name: self.system_name.clone(),
            entity_param_types: self.entity_param_types.clone(),
            store_param_types: self.store_param_types.clone(),
        }
    }
}

pub(super) fn infer_store_quant_entity(
    var: &str,
    body: &IRExpr,
    store_param_types: &HashMap<String, String>,
) -> Option<String> {
    match body {
        IRExpr::Index { map, key, .. } => match (map.as_ref(), key.as_ref()) {
            (
                IRExpr::Var {
                    name: store_name, ..
                },
                IRExpr::Var { name: key_name, .. },
            ) if key_name == var => store_param_types.get(store_name).cloned(),
            _ => None,
        },
        IRExpr::BinOp { left, right, .. } => infer_store_quant_entity(var, left, store_param_types)
            .or_else(|| infer_store_quant_entity(var, right, store_param_types)),
        IRExpr::UnOp { operand, .. } => infer_store_quant_entity(var, operand, store_param_types),
        _ => None,
    }
}

pub(super) fn encode_store_membership(
    pool: &SlotPool,
    entity_name: &str,
    key: &SmtValue,
    step: usize,
) -> SmtValue {
    let n_slots = pool.slots_for(entity_name);
    let mut disjuncts = Vec::new();
    for slot in 0..n_slots {
        if let Some(SmtValue::Bool(active)) = pool.active_at(entity_name, slot, step) {
            let slot_id = smt::int_val(slot as i64);
            let cond = smt::smt_eq(key, &slot_id).expect("internal: store membership eq");
            disjuncts.push(smt::bool_and(&[&cond, active]));
        }
    }
    if disjuncts.is_empty() {
        return SmtValue::Bool(smt::bool_const(false));
    }
    let refs: Vec<&Bool> = disjuncts.iter().collect();
    SmtValue::Bool(smt::bool_or(&refs))
}

/// Encode an event guard expression, expanding entity quantifiers over slots.
///
/// Uses `GuardCtx` to track entity bindings from enclosing quantifiers,
/// ensuring that field references resolve correctly across nested quantifiers.
#[allow(dead_code)]
pub(super) fn encode_guard_expr(
    pool: &SlotPool,
    vctx: &VerifyContext,
    expr: &IRExpr,
    step_params: &HashMap<String, SmtValue>,
    store_param_types: &HashMap<String, String>,
    step: usize,
) -> Bool {
    try_encode_guard_expr(pool, vctx, expr, step_params, store_param_types, step)
        .unwrap_or_else(|msg| panic!("{msg}"))
}

pub(crate) fn try_encode_guard_expr(
    pool: &SlotPool,
    vctx: &VerifyContext,
    expr: &IRExpr,
    step_params: &HashMap<String, SmtValue>,
    store_param_types: &HashMap<String, String>,
    step: usize,
) -> Result<Bool, String> {
    let ctx = GuardCtx {
        bindings: HashMap::new(),
        params: step_params.clone(),
        system_name: String::new(),
        entity_param_types: HashMap::new(),
        store_param_types: store_param_types.clone(),
    };
    try_encode_guard_inner(pool, vctx, &ctx, expr, step)
}

/// /14: encode guard with system field context and entity param types.
#[allow(clippy::too_many_arguments)]
#[allow(dead_code)]
pub(super) fn encode_guard_expr_for_system(
    pool: &SlotPool,
    vctx: &VerifyContext,
    expr: &IRExpr,
    step_params: &HashMap<String, SmtValue>,
    step: usize,
    system_name: &str,
    entity_param_types: &HashMap<String, String>,
    store_param_types: &HashMap<String, String>,
) -> Bool {
    try_encode_guard_expr_for_system(
        pool,
        vctx,
        expr,
        step_params,
        step,
        system_name,
        entity_param_types,
        store_param_types,
    )
    .unwrap_or_else(|msg| panic!("{msg}"))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn try_encode_guard_expr_for_system(
    pool: &SlotPool,
    vctx: &VerifyContext,
    expr: &IRExpr,
    step_params: &HashMap<String, SmtValue>,
    step: usize,
    system_name: &str,
    entity_param_types: &HashMap<String, String>,
    store_param_types: &HashMap<String, String>,
) -> Result<Bool, String> {
    let ctx = GuardCtx {
        bindings: HashMap::new(),
        params: step_params.clone(),
        system_name: system_name.to_owned(),
        entity_param_types: entity_param_types.clone(),
        store_param_types: store_param_types.clone(),
    };
    try_encode_guard_inner(pool, vctx, &ctx, expr, step)
}

#[allow(dead_code)]
fn encode_guard_inner(
    pool: &SlotPool,
    vctx: &VerifyContext,
    ctx: &GuardCtx,
    expr: &IRExpr,
    step: usize,
) -> Bool {
    try_encode_guard_inner(pool, vctx, ctx, expr, step).unwrap_or_else(|msg| panic!("{msg}"))
}

fn try_encode_guard_inner(
    pool: &SlotPool,
    vctx: &VerifyContext,
    ctx: &GuardCtx,
    expr: &IRExpr,
    step: usize,
) -> Result<Bool, String> {
    match expr {
        IRExpr::Exists {
            var,
            domain: IRType::Entity { name: entity_name },
            body,
            ..
        } => {
            let n_slots = pool.slots_for(entity_name);
            let mut disjuncts = Vec::new();
            for slot in 0..n_slots {
                let active = pool.active_at(entity_name, slot, step);
                let inner_ctx = ctx.with_binding(var, entity_name, slot);
                let body_val = try_encode_guard_inner(pool, vctx, &inner_ctx, body, step)?;
                if let Some(SmtValue::Bool(act)) = active {
                    disjuncts.push(smt::bool_and(&[act, &body_val]));
                }
            }
            if disjuncts.is_empty() {
                return Ok(smt::bool_const(false));
            }
            let refs: Vec<&Bool> = disjuncts.iter().collect();
            Ok(smt::bool_or(&refs))
        }
        IRExpr::Forall {
            var,
            domain: IRType::Entity { name: entity_name },
            body,
            ..
        } => {
            let n_slots = pool.slots_for(entity_name);
            let mut conjuncts = Vec::new();
            for slot in 0..n_slots {
                let active = pool.active_at(entity_name, slot, step);
                let inner_ctx = ctx.with_binding(var, entity_name, slot);
                let body_val = try_encode_guard_inner(pool, vctx, &inner_ctx, body, step)?;
                if let Some(SmtValue::Bool(act)) = active {
                    conjuncts.push(smt::bool_implies(act, &body_val));
                }
            }
            if conjuncts.is_empty() {
                return Ok(smt::bool_const(true));
            }
            let refs: Vec<&Bool> = conjuncts.iter().collect();
            Ok(smt::bool_and(&refs))
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpAnd" || op == "OpOr" || op == "OpImplies" => {
            let l = try_encode_guard_inner(pool, vctx, ctx, left, step)?;
            let r = try_encode_guard_inner(pool, vctx, ctx, right, step)?;
            Ok(match op.as_str() {
                "OpAnd" => smt::bool_and(&[&l, &r]),
                "OpOr" => smt::bool_or(&[&l, &r]),
                "OpImplies" => smt::bool_implies(&l, &r),
                _ => unreachable!(),
            })
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => Ok(smt::bool_not(
            &try_encode_guard_inner(pool, vctx, ctx, operand, step)?,
        )),
        IRExpr::Lit {
            value: LitVal::Bool { value },
            ..
        } => Ok(smt::bool_const(*value)),
        // Non-boolean expressions (comparisons, field access, etc.) —
        // encode as value using the guard context bindings
        other => Ok(try_encode_guard_value(pool, vctx, ctx, other, step)?.to_bool()?),
    }
}

/// Encode a value expression within a guard context.
/// Resolves field references using the guard's entity bindings.
#[allow(dead_code)]
fn encode_guard_value(
    pool: &SlotPool,
    vctx: &VerifyContext,
    ctx: &GuardCtx,
    expr: &IRExpr,
    step: usize,
) -> SmtValue {
    try_encode_guard_value(pool, vctx, ctx, expr, step).unwrap_or_else(|msg| panic!("{msg}"))
}

fn try_encode_guard_value(
    pool: &SlotPool,
    vctx: &VerifyContext,
    ctx: &GuardCtx,
    expr: &IRExpr,
    step: usize,
) -> Result<SmtValue, String> {
    match expr {
        IRExpr::Lit { value, .. } => Ok(encode_slot_literal(value)),
        IRExpr::Var { name, .. } => {
            // Check event params first
            if let Some(val) = ctx.params.get(name.as_str()) {
                return Ok(val.clone());
            }
            // Check entity bindings (last-bound entity for bare field names)
            for (entity, slot) in ctx.bindings.values() {
                if let Some(val) = pool.field_at(entity, *slot, name, step) {
                    return Ok(val.clone());
                }
            }
            // try system flat state field
            if !ctx.system_name.is_empty() {
                if let Some(val) = pool.system_field_at(&ctx.system_name, name, step) {
                    return Ok(val.clone());
                }
            }
            // Fallback to encode_slot_expr for remaining resolution
            let fallback_ctx = SlotEncodeCtx {
                pool,
                vctx,
                entity: "",
                slot: 0,
                params: ctx.params.clone(),
                bindings: ctx.bindings.clone(),
                system_name: &ctx.system_name,
                entity_param_types: &ctx.entity_param_types,
                store_param_types: &ctx.store_param_types,
            };
            try_encode_slot_expr(&fallback_ctx, expr, step)
        }
        // Field, App, and other complex expressions — delegate to
        // encode_slot_expr which handles entity param field access,
        // system struct fields, and function calls.
        IRExpr::Field { .. } | IRExpr::App { .. } => {
            let fallback_ctx = SlotEncodeCtx {
                pool,
                vctx,
                entity: "",
                slot: 0,
                params: ctx.params.clone(),
                bindings: ctx.bindings.clone(),
                system_name: &ctx.system_name,
                entity_param_types: &ctx.entity_param_types,
                store_param_types: &ctx.store_param_types,
            };
            try_encode_slot_expr(&fallback_ctx, expr, step)
        }
        IRExpr::Ctor {
            enum_name, ctor, ..
        } => {
            let id = vctx.variants.try_id_of(enum_name, ctor)?;
            Ok(smt::int_val(id))
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let l = try_encode_guard_value(pool, vctx, ctx, left, step)?;
            let r = try_encode_guard_value(pool, vctx, ctx, right, step)?;
            Ok(smt::binop(op, &l, &r)?)
        }
        IRExpr::UnOp { op, operand, .. } => {
            let v = try_encode_guard_value(pool, vctx, ctx, operand, step)?;
            Ok(smt::unop(op, &v)?)
        }
        IRExpr::Prime { expr, .. } => try_encode_guard_value(pool, vctx, ctx, expr, step + 1),
        // Fallback: delegate to encode_slot_expr which handles App, Field
        // on entity params, and other complex expression forms.
        other => {
            let fallback_ctx = SlotEncodeCtx {
                pool,
                vctx,
                entity: "",
                slot: 0,
                params: ctx.params.clone(),
                bindings: ctx.bindings.clone(),
                system_name: &ctx.system_name,
                entity_param_types: &ctx.entity_param_types,
                store_param_types: &ctx.store_param_types,
            };
            try_encode_slot_expr(&fallback_ctx, other, step)
        }
    }
}
