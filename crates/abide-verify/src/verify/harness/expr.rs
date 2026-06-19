use super::*;
use crate::ir::types::IRMatchArm;
use crate::verify::collections;
use crate::verify::encode;
use crate::verify::walkers;

fn finite_slot_domain_values(ctx: &SlotEncodeCtx<'_>, domain: &IRType) -> Option<Vec<SmtValue>> {
    match domain {
        IRType::Bool => Some(vec![smt::bool_val(false), smt::bool_val(true)]),
        IRType::Enum { name, variants } if !domain.has_variant_fields() => Some(
            variants
                .iter()
                .enumerate()
                .map(|(idx, variant)| {
                    ctx.vctx
                        .variants
                        .try_id_of(name, &variant.name)
                        .map_or_else(|_| smt::int_val(idx as i64), smt::int_val)
                })
                .collect(),
        ),
        _ => None,
    }
}

pub fn encode_slot_expr(ctx: &SlotEncodeCtx<'_>, expr: &IRExpr, step: usize) -> SmtValue {
    try_encode_slot_expr(ctx, expr, step).unwrap_or_else(|msg| panic!("{msg}"))
}

pub fn try_encode_slot_expr(
    ctx: &SlotEncodeCtx<'_>,
    expr: &IRExpr,
    step: usize,
) -> Result<SmtValue, String> {
    if let Some(value) = try_encode_slot_literal_expr(expr) {
        return Ok(value);
    }
    if let Some(value) = try_encode_slot_var_or_field_expr(ctx, expr, step) {
        return value;
    }
    if let Some(value) = try_encode_slot_constructor_expr(ctx, expr, step) {
        return value;
    }
    if let Some(value) = try_encode_slot_choose_expr(ctx, expr, step) {
        return value;
    }
    if let Some(value) = try_encode_slot_operator_expr(ctx, expr, step) {
        return value;
    }
    if let Some(value) = try_encode_slot_app_expr(ctx, expr, step) {
        return value;
    }
    if let Some(value) = try_encode_slot_collection_expr(ctx, expr, step) {
        return value;
    }
    if let Some(value) = try_encode_slot_control_expr(ctx, expr, step) {
        return value;
    }
    if let Some(value) = try_encode_slot_match_expr(ctx, expr, step) {
        return value;
    }

    Err(format!(
        "slot expression encoding not yet supported: {expr:?}"
    ))
}

pub(super) fn try_encode_slot_literal_expr(expr: &IRExpr) -> Option<SmtValue> {
    let IRExpr::Lit { value, .. } = expr else {
        return None;
    };
    Some(encode_slot_literal(value))
}

pub(super) fn try_encode_slot_var_or_field_expr(
    ctx: &SlotEncodeCtx<'_>,
    expr: &IRExpr,
    step: usize,
) -> Option<Result<SmtValue, String>> {
    match expr {
        IRExpr::Var { name, .. } => {
            if let Some(val) = ctx.params.get(name) {
                return Some(Ok(val.clone()));
            }
            if let Some((_, slot)) = ctx.bindings.get(name.as_str()) {
                return Some(Ok(smt::int_val(*slot as i64)));
            }
            if let Some(val) = ctx.pool.field_at(ctx.entity, ctx.slot, name, step) {
                return Some(Ok(val.clone()));
            }
            for (entity, slot) in ctx.bindings.values() {
                if let Some(val) = ctx.pool.field_at(entity, *slot, name, step) {
                    return Some(Ok(val.clone()));
                }
            }
            if !ctx.system_name.is_empty() {
                if let Some(val) = ctx.pool.system_field_at(ctx.system_name, name, step) {
                    return Some(Ok(val.clone()));
                }
            }
            Some(Err(format!(
                "slot variable not found: {}.{name} slot={} step={step}",
                ctx.entity, ctx.slot
            )))
        }
        IRExpr::Field {
            expr: recv, field, ..
        } => Some(try_encode_slot_field_expr(ctx, recv, field, step)),
        _ => None,
    }
}

fn try_encode_slot_field_expr(
    ctx: &SlotEncodeCtx<'_>,
    recv: &IRExpr,
    field: &str,
    step: usize,
) -> Result<SmtValue, String> {
    if let IRExpr::Var { name, .. } = recv {
        let qualified = format!("{name}.{field}");
        if let Some(val) = ctx.params.get(&qualified) {
            return Ok(val.clone());
        }
        if let Some((entity, slot)) = ctx.bindings.get(name.as_str()) {
            if let Some(val) = ctx.pool.field_at(entity, *slot, field, step) {
                return Ok(val.clone());
            }
        }
        if !ctx.system_name.is_empty() && ctx.pool.is_system_struct_field(ctx.system_name, name) {
            if let Some(val) = ctx.pool.system_field_at(ctx.system_name, &qualified, step) {
                return Ok(val.clone());
            }
        }
        if let Some(ent_name) = ctx.entity_param_types.get(name.as_str()) {
            if let Some(param_val) = ctx.params.get(name.as_str()) {
                let n_slots = ctx.pool.slots_for(ent_name);
                let mut result: Option<SmtValue> = None;
                for slot in (0..n_slots).rev() {
                    if let Some(field_val) = ctx.pool.field_at(ent_name, slot, field, step) {
                        let slot_id = smt::int_val(slot as i64);
                        let cond = smt::smt_eq(param_val, &slot_id)?;
                        result = Some(match result {
                            None => field_val.clone(),
                            Some(else_val) => smt::smt_ite(&cond, field_val, &else_val),
                        });
                    }
                }
                if let Some(val) = result {
                    return Ok(val);
                }
            }
        }
    }
    if let Some(val) = ctx.pool.field_at(ctx.entity, ctx.slot, field, step) {
        return Ok(val.clone());
    }
    Err(format!(
        "slot field not found: {}.{field} slot={} step={step}",
        ctx.entity, ctx.slot
    ))
}

pub(super) fn try_encode_slot_constructor_expr(
    ctx: &SlotEncodeCtx<'_>,
    expr: &IRExpr,
    step: usize,
) -> Option<Result<SmtValue, String>> {
    let IRExpr::Ctor {
        enum_name,
        ctor,
        args,
        ..
    } = expr
    else {
        return None;
    };
    Some(try_encode_slot_constructor(
        ctx, enum_name, ctor, args, step,
    ))
}

fn try_encode_slot_constructor(
    ctx: &SlotEncodeCtx<'_>,
    enum_name: &str,
    ctor: &str,
    args: &[(String, IRExpr)],
    step: usize,
) -> Result<SmtValue, String> {
    if let Some(dt) = ctx.vctx.adt_sorts.get(enum_name) {
        for variant in &dt.variants {
            if ctor_name_matches(enum_name, &smt::func_decl_name(&variant.constructor), ctor) {
                let arity = variant.accessors.len();
                if arity > 0 && args.is_empty() {
                    return Err(format!(
                        "constructor '{ctor}' of '{enum_name}' requires {arity} field argument(s)"
                    ));
                }
                if args.is_empty() {
                    let result = smt::func_decl_apply(&variant.constructor, &[]);
                    return Ok(walkers::dynamic_to_smt_value(result));
                }

                let declared_names: Vec<String> =
                    variant.accessors.iter().map(smt::func_decl_name).collect();
                for (field_name, _) in args {
                    if !declared_names.iter().any(|name| name == field_name) {
                        return Err(format!(
                            "unknown field '{field_name}' in constructor '{ctor}' of '{enum_name}'"
                        ));
                    }
                }
                let args_map: HashMap<&str, &IRExpr> = args
                    .iter()
                    .map(|(name, expr)| (name.as_str(), expr))
                    .collect();
                let mut z3_args: Vec<smt::Dynamic> = Vec::new();
                for name in &declared_names {
                    let Some(field_expr) = args_map.get(name.as_str()) else {
                        return Err(format!(
                            "constructor '{ctor}' of '{enum_name}' is missing field '{name}'"
                        ));
                    };
                    z3_args.push(try_encode_slot_expr(ctx, field_expr, step)?.to_dynamic());
                }
                let refs: Vec<&smt::Dynamic> = z3_args.iter().collect();
                let result = smt::func_decl_apply(&variant.constructor, &refs);
                return Ok(walkers::dynamic_to_smt_value(result));
            }
        }
    }
    let id = ctx
        .vctx
        .variants
        .try_id_of(enum_name, unqualify_ctor_name(ctor))?;
    Ok(smt::int_val(id))
}

fn unqualify_ctor_name(ctor: &str) -> &str {
    ctor.rsplit_once("::").map_or(ctor, |(_, name)| name)
}

fn ctor_name_matches(enum_name: &str, declared_ctor: &str, candidate: &str) -> bool {
    declared_ctor == candidate
        || unqualify_ctor_name(candidate) == declared_ctor
        || format!("{enum_name}::{declared_ctor}") == candidate
}

pub(super) fn try_encode_slot_choose_expr(
    ctx: &SlotEncodeCtx<'_>,
    expr: &IRExpr,
    step: usize,
) -> Option<Result<SmtValue, String>> {
    let IRExpr::Choose {
        var,
        domain,
        predicate,
        ..
    } = expr
    else {
        return None;
    };
    let Some(witness) = direct_slot_choose_witness(var, domain, predicate.as_deref()) else {
        return Some(Err(format!(
            "slot expression encoding not yet supported: {expr:?}"
        )));
    };
    Some(try_encode_slot_expr(ctx, &witness, step))
}

pub(super) fn try_encode_slot_operator_expr(
    ctx: &SlotEncodeCtx<'_>,
    expr: &IRExpr,
    step: usize,
) -> Option<Result<SmtValue, String>> {
    match expr {
        IRExpr::BinOp {
            op, left, right, ..
        } => Some(try_encode_slot_binop_expr(ctx, op, left, right, step)),
        IRExpr::UnOp { op, operand, .. } => Some(try_encode_slot_unop_expr(ctx, op, operand, step)),
        _ => None,
    }
}

fn try_encode_slot_binop_expr(
    ctx: &SlotEncodeCtx<'_>,
    op: &str,
    left: &IRExpr,
    right: &IRExpr,
    step: usize,
) -> Result<SmtValue, String> {
    let l = try_encode_slot_expr(ctx, left, step)?;
    let r = try_encode_slot_expr(ctx, right, step)?;
    if op == "OpSeqConcat" {
        let Some(IRType::Seq { element }) = expr_type(left) else {
            return Err("Seq::concat requires sequence operands".to_owned());
        };
        return smt::seq_concat(&l, &r, element);
    }
    if op == "OpMapHas" {
        let Some(IRType::Map { value, .. }) = expr_type(left) else {
            return Err("Map::has requires a map-typed left operand".to_owned());
        };
        return smt::map_has(&l, &r, value);
    }
    if op == "OpMapMerge" {
        let Some(IRType::Map { key, value }) = expr_type(left) else {
            return Err("Map::merge requires map operands".to_owned());
        };
        return smt::map_merge(&l, &r, key, value);
    }
    // Numeric `/`/`%` in a transition guard/update may be undefined when the
    // divisor is zero; record a well-definedness obligation (guarded by the
    // surrounding command/action guard) so a reachable transition-update
    // div-by-zero is surfaced rather than absorbed into solver-total arithmetic.
    if crate::verify::property::div_mod_requires_nonzero(op, &r) {
        crate::verify::property::record_harness_div_obligation(r.clone());
    }
    smt::binop(op, &l, &r)
}

fn try_encode_slot_unop_expr(
    ctx: &SlotEncodeCtx<'_>,
    op: &str,
    operand: &IRExpr,
    step: usize,
) -> Result<SmtValue, String> {
    let v = try_encode_slot_expr(ctx, operand, step)?;
    if op == "OpSeqHead" {
        let Some(IRType::Seq { element }) = expr_type(operand) else {
            return smt::unop(op, &v);
        };
        return smt::seq_head(&v, element);
    }
    if op == "OpSeqTail" {
        if let IRExpr::SeqLit { elements, ty, .. } = operand {
            let tail = IRExpr::SeqLit {
                elements: elements.iter().skip(1).cloned().collect(),
                ty: ty.clone(),
                span: None,
            };
            return try_encode_slot_expr(ctx, &tail, step);
        }
        let Some(IRType::Seq { element }) = expr_type(operand) else {
            return smt::unop(op, &v);
        };
        return smt::seq_tail(&v, element);
    }
    if op == "OpSeqLength" {
        let Some(IRType::Seq { element }) = expr_type(operand) else {
            return smt::unop(op, &v);
        };
        return smt::seq_length(&v, element);
    }
    if op == "OpSeqEmpty" {
        let Some(IRType::Seq { element }) = expr_type(operand) else {
            return smt::unop(op, &v);
        };
        let len = smt::seq_length(&v, element)?;
        return Ok(SmtValue::Bool(smt::smt_eq(&len, &smt::int_val(0))?));
    }
    if op == "OpMapDomain" {
        if let IRExpr::MapLit { entries, .. } = operand {
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
            return try_encode_slot_expr(ctx, &set_lit, step);
        }
        let Some(IRType::Map { key, value }) = expr_type(operand) else {
            return Err("Map::domain requires a map operand".to_owned());
        };
        return smt::map_domain(&v, key, value);
    }
    if op == "OpMapRange" {
        if let IRExpr::MapLit { entries, .. } = operand {
            let set_lit = IRExpr::SetLit {
                elements: entries.iter().map(|(_, value)| value.clone()).collect(),
                ty: IRType::Set {
                    element: Box::new(match expr_type(operand) {
                        Some(IRType::Map { value, .. }) => value.as_ref().clone(),
                        _ => IRType::Int,
                    }),
                },
                span: None,
            };
            return try_encode_slot_expr(ctx, &set_lit, step);
        }
        let Some(IRType::Map { key, value }) = expr_type(operand) else {
            return Err("Map::range requires a map operand".to_owned());
        };
        return smt::map_range(&v, key, value);
    }
    smt::unop(op, &v)
}

pub(super) fn try_encode_slot_app_expr(
    ctx: &SlotEncodeCtx<'_>,
    expr: &IRExpr,
    step: usize,
) -> Option<Result<SmtValue, String>> {
    if !matches!(expr, IRExpr::App { .. }) {
        return None;
    }
    Some(try_encode_slot_app(ctx, expr, step))
}

fn try_encode_slot_app(
    ctx: &SlotEncodeCtx<'_>,
    expr: &IRExpr,
    step: usize,
) -> Result<SmtValue, String> {
    if let Some(value) = try_encode_ctor_app(ctx, expr, step)? {
        return Ok(value);
    }
    let Some((kind, full_name, args)) = defenv::classify_app_chain_public(
        &ctx.vctx.defs,
        expr,
        Some(ctx.system_name),
        &ctx.vctx.system_queries,
    ) else {
        return Err(format!(
            "slot expression encoding not yet supported: {expr:?}"
        ));
    };

    if kind != AppHeadKind::Query {
        if let Some(expanded) = ctx.vctx.defs.expand_app(expr) {
            return try_encode_slot_expr(ctx, &expanded, step);
        }
        return Err(format!(
            "slot expression reached pure application `{full_name}` \
             without expansion; App in slot encoding is reserved for \
             query evaluation"
        ));
    }

    let (query_system, query_name) = full_name
        .split_once("::")
        .map(|(system, query)| (system.to_owned(), query.to_owned()))
        .expect("query classification should always produce a qualified name");
    let Some(query) = ctx
        .vctx
        .system_queries
        .get(&(query_system.clone(), query_name.clone()))
    else {
        return Err(format!(
            "slot expression encoding not yet supported: {expr:?}"
        ));
    };
    assert_eq!(
        query.params.len(),
        args.len(),
        "query arity mismatch in slot expression: expected {} args for {}::{}, got {}",
        query.params.len(),
        query_system,
        query_name,
        args.len()
    );

    let mut params = ctx.params.clone();
    let mut entity_param_types = ctx.entity_param_types.clone();
    for (param, arg_expr) in query.params.iter().zip(args.iter()) {
        let value = try_encode_slot_expr(ctx, arg_expr, step)?;
        params.insert(param.name.clone(), value);
        if let IRType::Entity { name } = &param.ty {
            entity_param_types.insert(param.name.clone(), name.clone());
        }
    }

    let inner_ctx = SlotEncodeCtx {
        pool: ctx.pool,
        vctx: ctx.vctx,
        entity: ctx.entity,
        slot: ctx.slot,
        params,
        bindings: ctx.bindings.clone(),
        system_name: query_system.as_str(),
        entity_param_types: &entity_param_types,
        store_param_types: ctx.store_param_types,
    };
    let value = try_encode_slot_expr(&inner_ctx, &query.body, step)?;
    if query.requires.is_empty() {
        return Ok(value);
    }

    let mut requirements = Vec::new();
    for req in &query.requires {
        requirements.push(
            try_encode_slot_expr(&inner_ctx, req, step)?
                .as_bool()
                .map_err(|msg| {
                    format!(
                        "query refinement precondition for `{query_system}::{query_name}` \
                         is not boolean: {msg}"
                    )
                })?
                .clone(),
        );
    }

    match value {
        SmtValue::Bool(body) => {
            let mut parts: Vec<&Bool> = requirements.iter().collect();
            parts.push(&body);
            Ok(SmtValue::Bool(smt::bool_and(&parts)))
        }
        other => Err(format!(
            "query `{query_system}::{query_name}` has parameter refinements, \
             but non-boolean query values with preconditions are not yet supported \
             in executable guard encoding: {other:?}"
        )),
    }
}

pub(super) fn try_encode_slot_collection_expr(
    ctx: &SlotEncodeCtx<'_>,
    expr: &IRExpr,
    step: usize,
) -> Option<Result<SmtValue, String>> {
    match expr {
        IRExpr::MapUpdate {
            map, key, value, ..
        } => Some(try_encode_slot_map_update_expr(ctx, map, key, value, step)),
        IRExpr::Index { map, key, ty, .. } => {
            Some(try_encode_slot_index_expr(ctx, map, key, ty, step))
        }
        IRExpr::MapLit { entries, ty, .. } => {
            Some(try_encode_slot_map_lit_expr(ctx, entries, ty, step))
        }
        IRExpr::SetLit { elements, ty, .. } => {
            Some(try_encode_slot_set_lit_expr(ctx, elements, ty, step))
        }
        IRExpr::SeqLit { elements, ty, .. } => {
            Some(try_encode_slot_seq_lit_expr(ctx, elements, ty, step))
        }
        IRExpr::SetComp {
            var,
            domain,
            source: None,
            filter,
            projection,
            ty,
            ..
        } if finite_slot_domain_values(ctx, domain).is_some() => {
            Some(try_encode_slot_finite_set_comp_expr(
                ctx,
                var,
                domain,
                filter,
                projection.as_deref(),
                ty,
                step,
            ))
        }
        IRExpr::Card { expr: inner, .. } => Some(try_encode_slot_card_expr(ctx, inner, step)),
        _ => None,
    }
}

fn try_encode_slot_map_update_expr(
    ctx: &SlotEncodeCtx<'_>,
    map: &IRExpr,
    key: &IRExpr,
    value: &IRExpr,
    step: usize,
) -> Result<SmtValue, String> {
    let arr = try_encode_slot_expr(ctx, map, step)?;
    let k = try_encode_slot_expr(ctx, key, step)?;
    let v = try_encode_slot_expr(ctx, value, step)?;
    collections::encode_collection_update(&arr, &k, &v, expr_type(map))
        .map_err(|e| format!("slot map update encoding failed: {e}"))
}

fn try_encode_slot_index_expr(
    ctx: &SlotEncodeCtx<'_>,
    map: &IRExpr,
    key: &IRExpr,
    ty: &IRType,
    step: usize,
) -> Result<SmtValue, String> {
    if let IRExpr::Var {
        name: store_name, ..
    } = map
    {
        if let Some(entity_name) = ctx.store_param_types.get(store_name.as_str()) {
            let k = try_encode_slot_expr(ctx, key, step)?;
            return Ok(encode_store_membership(ctx.pool, entity_name, &k, step));
        }
    }
    let arr = try_encode_slot_expr(ctx, map, step)?;
    let k = try_encode_slot_expr(ctx, key, step)?;
    collections::encode_collection_index(&arr, &k, expr_type(map), ty)
        .map_err(|e| format!("slot index encoding failed: {e}"))
}

fn try_encode_slot_map_lit_expr(
    ctx: &SlotEncodeCtx<'_>,
    entries: &[(IRExpr, IRExpr)],
    ty: &IRType,
    step: usize,
) -> Result<SmtValue, String> {
    collections::encode_map_literal(entries, ty, |expr| try_encode_slot_expr(ctx, expr, step))
}

fn try_encode_slot_set_lit_expr(
    ctx: &SlotEncodeCtx<'_>,
    elements: &[IRExpr],
    ty: &IRType,
    step: usize,
) -> Result<SmtValue, String> {
    collections::encode_set_literal(elements, ty, |elem| try_encode_slot_expr(ctx, elem, step))
}

fn try_encode_slot_seq_lit_expr(
    ctx: &SlotEncodeCtx<'_>,
    elements: &[IRExpr],
    ty: &IRType,
    step: usize,
) -> Result<SmtValue, String> {
    collections::encode_seq_literal(elements, ty, |elem| try_encode_slot_expr(ctx, elem, step))
}

fn try_encode_slot_finite_set_comp_expr(
    ctx: &SlotEncodeCtx<'_>,
    var: &str,
    domain: &IRType,
    filter: &IRExpr,
    projection: Option<&IRExpr>,
    ty: &IRType,
    step: usize,
) -> Result<SmtValue, String> {
    let IRType::Set { element } = ty else {
        return Err(format!("SetComp with non-Set result type: {ty:?}"));
    };
    let elem_sort = smt::ir_type_to_sort(element);
    let false_val = smt::bool_val(false).to_dynamic();
    let true_val = smt::bool_val(true).to_dynamic();
    let mut arr = smt::const_array(&elem_sort, &false_val);

    let domain_values = finite_slot_domain_values(ctx, domain).ok_or_else(|| {
        format!("unsupported finite set comprehension domain in action context: {domain:?}")
    })?;

    for value in domain_values {
        let mut params = ctx.params.clone();
        params.insert(var.to_owned(), value.clone());
        let inner_ctx = SlotEncodeCtx {
            pool: ctx.pool,
            vctx: ctx.vctx,
            entity: ctx.entity,
            slot: ctx.slot,
            params,
            bindings: ctx.bindings.clone(),
            system_name: ctx.system_name,
            entity_param_types: ctx.entity_param_types,
            store_param_types: ctx.store_param_types,
        };
        let filter_val = try_encode_slot_expr(&inner_ctx, filter, step)?.to_bool()?;
        let key = if let Some(projection) = projection {
            try_encode_slot_expr(&inner_ctx, projection, step)?
        } else {
            value
        };
        let stored = arr.store(&key.to_dynamic(), &true_val);
        arr = smt::array_ite(&filter_val, &stored, &arr);
    }

    Ok(SmtValue::Array(arr))
}

fn try_encode_slot_card_expr(
    ctx: &SlotEncodeCtx<'_>,
    inner: &IRExpr,
    step: usize,
) -> Result<SmtValue, String> {
    Ok(match inner {
        IRExpr::SetLit { .. } | IRExpr::SeqLit { .. } | IRExpr::MapLit { .. } => {
            // abide-audit: allow-silent-fallback -- bounded count or slot conversion intentionally collapses invalid capacity to zero
            let count = collections::finite_literal_cardinality(inner).unwrap_or(0);
            // abide-audit: allow-silent-fallback -- bounded count or slot conversion intentionally collapses invalid capacity to zero
            smt::int_val(i64::try_from(count).unwrap_or(0))
        }
        IRExpr::SetComp {
            var,
            source: Some(source),
            filter,
            projection,
            ..
        } => try_encode_slot_sourced_set_comp_card(
            ctx,
            var,
            source,
            filter,
            projection.as_deref(),
            step,
        )?,
        IRExpr::SetComp {
            var,
            domain,
            source: None,
            filter,
            projection,
            ..
        } if finite_slot_domain_values(ctx, domain).is_some() => {
            try_encode_slot_finite_set_comp_card(
                ctx,
                var,
                domain,
                filter,
                projection.as_deref(),
                step,
            )?
        }
        _ => {
            if let Some(IRType::Seq { element }) = expr_type(inner) {
                let seq = try_encode_slot_expr(ctx, inner, step)?;
                return smt::seq_length(&seq, element);
            }
            return Err(format!(
                "unsupported cardinality in action context: {inner:?}"
            ));
        }
    })
}

fn try_encode_slot_sourced_set_comp_card(
    ctx: &SlotEncodeCtx<'_>,
    var: &str,
    source: &IRExpr,
    filter: &IRExpr,
    projection: Option<&IRExpr>,
    step: usize,
) -> Result<SmtValue, String> {
    let elements = match source {
        IRExpr::SetLit { elements, .. } | IRExpr::SeqLit { elements, .. } => elements,
        _ => {
            return Err(format!(
                "unsupported cardinality in action context: {source:?}"
            ));
        }
    };
    collections::encode_unique_projected_cardinality(elements, |element_expr| {
        let value = try_encode_slot_expr(ctx, element_expr, step)?;
        let mut params = ctx.params.clone();
        params.insert(var.to_owned(), value.clone());
        let inner_ctx = SlotEncodeCtx {
            pool: ctx.pool,
            vctx: ctx.vctx,
            entity: ctx.entity,
            slot: ctx.slot,
            params,
            bindings: ctx.bindings.clone(),
            system_name: ctx.system_name,
            entity_param_types: ctx.entity_param_types,
            store_param_types: ctx.store_param_types,
        };
        let filter_val = try_encode_slot_expr(&inner_ctx, filter, step)?.to_bool()?;
        let key = if let Some(projection) = projection {
            try_encode_slot_expr(&inner_ctx, projection, step)?
        } else {
            value
        };
        Ok((filter_val, key))
    })
}

fn try_encode_slot_finite_set_comp_card(
    ctx: &SlotEncodeCtx<'_>,
    var: &str,
    domain: &IRType,
    filter: &IRExpr,
    projection: Option<&IRExpr>,
    step: usize,
) -> Result<SmtValue, String> {
    let domain_values = finite_slot_domain_values(ctx, domain).ok_or_else(|| {
        format!("unsupported finite set comprehension domain in action context: {domain:?}")
    })?;

    collections::encode_unique_projected_cardinality(domain_values, |value| {
        let mut params = ctx.params.clone();
        params.insert(var.to_owned(), value.clone());
        let inner_ctx = SlotEncodeCtx {
            pool: ctx.pool,
            vctx: ctx.vctx,
            entity: ctx.entity,
            slot: ctx.slot,
            params,
            bindings: ctx.bindings.clone(),
            system_name: ctx.system_name,
            entity_param_types: ctx.entity_param_types,
            store_param_types: ctx.store_param_types,
        };
        let filter_val = try_encode_slot_expr(&inner_ctx, filter, step)?.to_bool()?;
        let key = if let Some(projection) = projection {
            try_encode_slot_expr(&inner_ctx, projection, step)?
        } else {
            value
        };
        Ok((filter_val, key))
    })
}

pub(super) fn try_encode_slot_control_expr(
    ctx: &SlotEncodeCtx<'_>,
    expr: &IRExpr,
    step: usize,
) -> Option<Result<SmtValue, String>> {
    match expr {
        IRExpr::Prime { expr, .. } => Some(try_encode_slot_expr(ctx, expr, step + 1)),
        IRExpr::Exists {
            var,
            domain: IRType::Int,
            body,
            ..
        } => Some(try_encode_slot_store_quantifier(
            ctx, var, body, step, false, expr,
        )),
        IRExpr::Forall {
            var,
            domain: IRType::Int,
            body,
            ..
        } => Some(try_encode_slot_store_quantifier(
            ctx, var, body, step, true, expr,
        )),
        _ => None,
    }
}

pub(super) fn try_encode_slot_match_expr(
    ctx: &SlotEncodeCtx<'_>,
    expr: &IRExpr,
    step: usize,
) -> Option<Result<SmtValue, String>> {
    let IRExpr::Match {
        scrutinee, arms, ..
    } = expr
    else {
        return None;
    };
    Some(try_encode_slot_match(ctx, scrutinee, arms, step))
}

fn try_encode_slot_match(
    ctx: &SlotEncodeCtx<'_>,
    scrutinee: &IRExpr,
    arms: &[IRMatchArm],
    step: usize,
) -> Result<SmtValue, String> {
    if arms.is_empty() {
        return Err("slot match expression has no arms".to_owned());
    }
    let scrut = try_encode_slot_expr(ctx, scrutinee, step)?;
    let mut result: Option<SmtValue> = None;

    for arm in arms.iter().rev() {
        let mut arm_params = ctx.params.clone();
        encode::bind_pattern_vars(&arm.pattern, &scrut, &mut arm_params, ctx.vctx)?;
        let arm_ctx = SlotEncodeCtx {
            pool: ctx.pool,
            vctx: ctx.vctx,
            entity: ctx.entity,
            slot: ctx.slot,
            params: arm_params,
            bindings: ctx.bindings.clone(),
            system_name: ctx.system_name,
            entity_param_types: ctx.entity_param_types,
            store_param_types: ctx.store_param_types,
        };

        let mut arm_cond =
            encode::encode_pattern_cond(&scrut, &arm.pattern, &HashMap::new(), ctx.vctx)?;
        if let Some(guard) = &arm.guard {
            let guard_bool = try_encode_slot_expr(&arm_ctx, guard, step)?.to_bool()?;
            arm_cond = smt::bool_and(&[&arm_cond, &guard_bool]);
        }
        let arm_value = try_encode_slot_expr(&arm_ctx, &arm.body, step)?;
        result = Some(match result {
            Some(else_value) => smt::smt_ite(&arm_cond, &arm_value, &else_value),
            None => arm_value,
        });
    }

    Ok(result.expect("non-empty match arms should produce a value"))
}

fn try_encode_slot_store_quantifier(
    ctx: &SlotEncodeCtx<'_>,
    var: &str,
    body: &IRExpr,
    step: usize,
    universal: bool,
    original: &IRExpr,
) -> Result<SmtValue, String> {
    let Some(entity_name) = infer_store_quant_entity(var, body, ctx.store_param_types) else {
        return Err(format!(
            "slot expression encoding not yet supported: {original:?}"
        ));
    };
    let n_slots = ctx.pool.slots_for(&entity_name);
    let mut parts = Vec::new();
    for slot in 0..n_slots {
        let mut params = ctx.params.clone();
        params.insert(var.to_owned(), smt::int_val(slot as i64));
        let mut entity_param_types = ctx.entity_param_types.clone();
        entity_param_types.insert(var.to_owned(), entity_name.clone());
        let inner_ctx = SlotEncodeCtx {
            pool: ctx.pool,
            vctx: ctx.vctx,
            entity: ctx.entity,
            slot: ctx.slot,
            params,
            bindings: ctx.bindings.clone(),
            system_name: ctx.system_name,
            entity_param_types: &entity_param_types,
            store_param_types: ctx.store_param_types,
        };
        parts.push(try_encode_slot_expr(&inner_ctx, body, step)?.to_bool()?);
    }
    if parts.is_empty() {
        return Ok(SmtValue::Bool(smt::bool_const(universal)));
    }
    let refs: Vec<&Bool> = parts.iter().collect();
    Ok(SmtValue::Bool(if universal {
        smt::bool_and(&refs)
    } else {
        smt::bool_or(&refs)
    }))
}

fn try_encode_ctor_app(
    ctx: &SlotEncodeCtx<'_>,
    expr: &IRExpr,
    step: usize,
) -> Result<Option<SmtValue>, String> {
    let Some((enum_name, ctor, args)) = decompose_ctor_app(expr) else {
        return Ok(None);
    };
    let Some(dt) = ctx.vctx.adt_sorts.get(enum_name) else {
        return Ok(None);
    };
    let Some(variant) = dt
        .variants
        .iter()
        .find(|variant| smt::func_decl_name(&variant.constructor) == ctor)
    else {
        return Err(format!("unknown constructor '{ctor}' of '{enum_name}'"));
    };
    if variant.accessors.len() != args.len() {
        return Err(format!(
            "constructor '{ctor}' of '{enum_name}' expects {} argument(s), got {}",
            variant.accessors.len(),
            args.len()
        ));
    }
    let z3_args = args
        .iter()
        .map(|arg| try_encode_slot_expr(ctx, arg, step).map(|value| value.to_dynamic()))
        .collect::<Result<Vec<_>, _>>()?;
    let refs = z3_args.iter().collect::<Vec<_>>();
    Ok(Some(walkers::dynamic_to_smt_value(smt::func_decl_apply(
        &variant.constructor,
        &refs,
    ))))
}

fn decompose_ctor_app(expr: &IRExpr) -> Option<(&str, &str, Vec<&IRExpr>)> {
    let mut args = Vec::new();
    let mut head = expr;
    while let IRExpr::App { func, arg, .. } = head {
        args.push(arg.as_ref());
        head = func.as_ref();
    }
    let IRExpr::Ctor {
        enum_name,
        ctor,
        args: named_args,
        ..
    } = head
    else {
        return None;
    };
    if !named_args.is_empty() {
        return None;
    }
    args.reverse();
    Some((enum_name, ctor, args))
}

#[derive(Default)]
struct IntChooseBounds {
    lower: Option<i64>,
    upper: Option<i64>,
    equal: Option<i64>,
}

fn direct_slot_choose_witness(
    var: &str,
    domain: &IRType,
    predicate: Option<&IRExpr>,
) -> Option<IRExpr> {
    if !matches!(domain, IRType::Int) {
        return None;
    }
    let predicate = predicate?;
    let mut bounds = IntChooseBounds::default();
    collect_int_choose_bounds(predicate, var, &mut bounds).then(|| {
        let value = bounds.equal?;
        let valid_lower = bounds.lower.is_none_or(|lower| value >= lower);
        let valid_upper = bounds.upper.is_none_or(|upper| value <= upper);
        (valid_lower && valid_upper).then_some(IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value },
            span: None,
        })
    })?
}

fn collect_int_choose_bounds(expr: &IRExpr, var: &str, bounds: &mut IntChooseBounds) -> bool {
    match expr {
        IRExpr::Lit {
            value: LitVal::Bool { value: true },
            ..
        } => true,
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpAnd" || op == "and" || op == "&&" => {
            collect_int_choose_bounds(left, var, bounds)
                && collect_int_choose_bounds(right, var, bounds)
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => apply_int_choose_comparison(op, left, right, var, bounds),
        _ => false,
    }
}

fn apply_int_choose_comparison(
    op: &str,
    left: &IRExpr,
    right: &IRExpr,
    var: &str,
    bounds: &mut IntChooseBounds,
) -> bool {
    if candidate_var(left, var) {
        return int_literal(right).is_some_and(|literal| update_choose_bounds(op, literal, bounds));
    }
    if candidate_var(right, var) {
        let Some(inverted) = invert_comparison(op) else {
            return false;
        };
        return int_literal(left)
            .is_some_and(|literal| update_choose_bounds(inverted, literal, bounds));
    }
    false
}

fn candidate_var(expr: &IRExpr, var: &str) -> bool {
    matches!(expr, IRExpr::Var { name, .. } if name == var || name == "$")
}

fn int_literal(expr: &IRExpr) -> Option<i64> {
    match expr {
        IRExpr::Lit {
            value: LitVal::Int { value },
            ..
        } => Some(*value),
        _ => None,
    }
}

fn invert_comparison(op: &str) -> Option<&'static str> {
    match op {
        "OpGt" | ">" => Some("OpLt"),
        "OpGe" | ">=" => Some("OpLe"),
        "OpLt" | "<" => Some("OpGt"),
        "OpLe" | "<=" => Some("OpGe"),
        "OpEq" | "==" => Some("OpEq"),
        _ => None,
    }
}

fn update_choose_bounds(op: &str, literal: i64, bounds: &mut IntChooseBounds) -> bool {
    match op {
        "OpEq" | "==" => {
            bounds.equal = Some(literal);
            true
        }
        "OpGt" | ">" => literal
            .checked_add(1)
            .is_some_and(|lower| update_lower_bound(bounds, lower)),
        "OpGe" | ">=" => update_lower_bound(bounds, literal),
        "OpLt" | "<" => literal
            .checked_sub(1)
            .is_some_and(|upper| update_upper_bound(bounds, upper)),
        "OpLe" | "<=" => update_upper_bound(bounds, literal),
        _ => false,
    }
}

fn update_lower_bound(bounds: &mut IntChooseBounds, lower: i64) -> bool {
    bounds.lower = Some(bounds.lower.map_or(lower, |current| current.max(lower)));
    true
}

fn update_upper_bound(bounds: &mut IntChooseBounds, upper: i64) -> bool {
    bounds.upper = Some(bounds.upper.map_or(upper, |current| current.min(upper)));
    true
}

pub(super) fn encode_slot_literal(lit: &LitVal) -> SmtValue {
    match lit {
        LitVal::Int { value } => smt::int_val(*value),
        LitVal::Bool { value } => smt::bool_val(*value),
        LitVal::Real { value } => {
            // Canonical real semantics: quantize to the shared millionth scale
            // so the SMT encoding matches the concrete witness (abide_core::arith).
            let (num, den) = abide_core::arith::real_to_rational(*value);
            smt::real_val(num, den)
        }
        // `float` is IEEE-754 binary64, a distinct sort from `real` (DDR-059).
        LitVal::Float { value } => smt::float_lit(*value),
        LitVal::Str { value } => smt::int_val(crate::verify::literal::string_literal_id(value)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::types::{IRPattern, IRProgram, IRTypeEntry, IRVariant};
    use crate::verify::smt::{AbideSolver, SatResult};
    use crate::verify::unsupported_corpus;

    fn empty_test_program() -> IRProgram {
        IRProgram {
            interfaces: vec![],
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

    fn enum_test_program() -> IRProgram {
        IRProgram {
            types: vec![IRTypeEntry {
                name: "Status".to_owned(),
                ty: status_ty(),
            }],
            ..empty_test_program()
        }
    }

    fn status_ty() -> IRType {
        IRType::Enum {
            name: "Status".to_owned(),
            variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
        }
    }

    fn empty_slot_encode_ctx<'a>(
        pool: &'a SlotPool,
        vctx: &'a VerifyContext,
        entity_param_types: &'a HashMap<String, String>,
        store_param_types: &'a HashMap<String, String>,
    ) -> SlotEncodeCtx<'a> {
        SlotEncodeCtx {
            pool,
            vctx,
            entity: "",
            slot: 0,
            params: HashMap::new(),
            bindings: HashMap::new(),
            system_name: "",
            entity_param_types,
            store_param_types,
        }
    }

    #[test]
    fn slot_literal_encoding_distinguishes_string_literals() {
        let good = encode_slot_literal(&LitVal::Str {
            value: "good".to_owned(),
        });
        let bad = encode_slot_literal(&LitVal::Str {
            value: "bad".to_owned(),
        });

        assert_eq!(
            good.as_int().expect("good string int").as_i64(),
            Some(crate::verify::literal::string_literal_id("good"))
        );
        assert_eq!(
            bad.as_int().expect("bad string int").as_i64(),
            Some(crate::verify::literal::string_literal_id("bad"))
        );
        assert_ne!(
            good.as_int().expect("good string int").as_i64(),
            bad.as_int().expect("bad string int").as_i64()
        );
    }

    #[test]
    fn slot_constructor_accepts_qualified_fieldless_enum_variant() {
        let program = enum_test_program();
        let vctx = VerifyContext::from_ir(&program);
        let pool = create_slot_pool(&[], &HashMap::new(), 0);
        let entity_param_types = HashMap::new();
        let store_param_types = HashMap::new();
        let ctx = empty_slot_encode_ctx(&pool, &vctx, &entity_param_types, &store_param_types);

        let plain = try_encode_slot_constructor(&ctx, "Status", "Pending", &[], 0)
            .expect("plain constructor");
        let qualified = try_encode_slot_constructor(&ctx, "Status", "Status::Pending", &[], 0)
            .expect("qualified constructor");

        assert_eq!(
            plain.as_int().expect("plain int").as_i64(),
            qualified.as_int().expect("qualified int").as_i64()
        );
    }

    #[test]
    fn slot_match_encodes_fieldless_enum_arms() {
        let program = enum_test_program();
        let vctx = VerifyContext::from_ir(&program);
        let pool = create_slot_pool(&[], &HashMap::new(), 0);
        let entity_param_types = HashMap::new();
        let store_param_types = HashMap::new();
        let ctx = empty_slot_encode_ctx(&pool, &vctx, &entity_param_types, &store_param_types);

        let match_expr = IRExpr::Match {
            scrutinee: Box::new(IRExpr::Ctor {
                enum_name: "Status".to_owned(),
                ctor: "Status::Pending".to_owned(),
                args: vec![],
                span: None,
            }),
            arms: vec![
                IRMatchArm {
                    pattern: IRPattern::PCtor {
                        name: "Status::Pending".to_owned(),
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
                        value: LitVal::Int { value: 2 },
                        span: None,
                    },
                },
            ],
            span: None,
        };

        let encoded = try_encode_slot_expr(&ctx, &match_expr, 0).expect("slot match should encode");
        let solver = AbideSolver::new();
        solver.assert(&smt::bool_not(&smt::int_eq(
            encoded.as_int().expect("match int"),
            &smt::int_lit(1),
        )));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn set_comprehension_cardinality_rejects_unsupported_domain_without_zero_fallback() {
        let program = empty_test_program();
        let vctx = VerifyContext::from_ir(&program);
        let pool = create_slot_pool(&[], &HashMap::new(), 0);
        let entity_param_types = HashMap::new();
        let store_param_types = HashMap::new();
        let ctx = empty_slot_encode_ctx(&pool, &vctx, &entity_param_types, &store_param_types);

        let err = try_encode_slot_finite_set_comp_card(
            &ctx,
            "n",
            &IRType::Int,
            &IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            None,
            0,
        )
        .expect_err("unsupported set-comprehension cardinality must not encode as zero");

        assert!(
            err.contains("unsupported finite set comprehension domain"),
            "{err}"
        );
    }

    #[test]
    fn set_comprehension_value_rejects_unsupported_domain_without_empty_fallback() {
        let program = empty_test_program();
        let vctx = VerifyContext::from_ir(&program);
        let pool = create_slot_pool(&[], &HashMap::new(), 0);
        let entity_param_types = HashMap::new();
        let store_param_types = HashMap::new();
        let ctx = empty_slot_encode_ctx(&pool, &vctx, &entity_param_types, &store_param_types);

        let err = try_encode_slot_finite_set_comp_expr(
            &ctx,
            "n",
            &IRType::Int,
            &IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            None,
            &IRType::Set {
                element: Box::new(IRType::Int),
            },
            0,
        )
        .expect_err("unsupported set-comprehension value must not encode as empty");

        assert!(
            err.contains("unsupported finite set comprehension domain"),
            "{err}"
        );
    }

    #[test]
    fn slot_encoder_rejects_shared_unsupported_ir_corpus() {
        let program = empty_test_program();
        let vctx = VerifyContext::from_ir(&program);
        let pool = create_slot_pool(&[], &HashMap::new(), 0);
        let entity_param_types = HashMap::new();
        let store_param_types = HashMap::new();
        let ctx = empty_slot_encode_ctx(&pool, &vctx, &entity_param_types, &store_param_types);

        for case in unsupported_corpus::pure_expression_rejection_cases() {
            try_encode_slot_expr(&ctx, &case.expr, 0).expect_err(
                "unsupported slot corpus case must not encode to a successful SMT value",
            );
        }
    }
}
