use super::*;

#[allow(clippy::too_many_lines)]
pub fn encode_slot_expr(ctx: &SlotEncodeCtx<'_>, expr: &IRExpr, step: usize) -> SmtValue {
    try_encode_slot_expr(ctx, expr, step).unwrap_or_else(|msg| panic!("{msg}"))
}

#[allow(clippy::too_many_lines)]
pub fn try_encode_slot_expr(
    ctx: &SlotEncodeCtx<'_>,
    expr: &IRExpr,
    step: usize,
) -> Result<SmtValue, String> {
    match expr {
        IRExpr::Lit { value, .. } => Ok(encode_slot_literal(value)),

        IRExpr::Var { name, .. } => {
            // Check action/event parameters first
            if let Some(val) = ctx.params.get(name) {
                return Ok(val.clone());
            }
            // Bound entity variables may need their slot index directly,
            // e.g. for membership tests like `users[u]`.
            if let Some((_, slot)) = ctx.bindings.get(name.as_str()) {
                return Ok(smt::int_val(*slot as i64));
            }
            // Resolve to this slot's field variable
            if let Some(val) = ctx.pool.field_at(ctx.entity, ctx.slot, name, step) {
                return Ok(val.clone());
            }
            // Try cross-entity bindings (from prior Choose blocks)
            for (entity, slot) in ctx.bindings.values() {
                if let Some(val) = ctx.pool.field_at(entity, *slot, name, step) {
                    return Ok(val.clone());
                }
            }
            // try system flat state field
            if !ctx.system_name.is_empty() {
                if let Some(val) = ctx.pool.system_field_at(ctx.system_name, name, step) {
                    return Ok(val.clone());
                }
            }
            Err(format!(
                "slot variable not found: {}.{name} slot={} step={step}",
                ctx.entity, ctx.slot
            ))
        }

        IRExpr::Ctor {
            enum_name, ctor, ..
        } => {
            let id = ctx.vctx.variants.try_id_of(enum_name, ctor)?;
            Ok(smt::int_val(id))
        }

        IRExpr::BinOp {
            op, left, right, ..
        } => {
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
            Ok(smt::binop(op, &l, &r)?)
        }

        IRExpr::UnOp { op, operand, .. } => {
            let v = try_encode_slot_expr(ctx, operand, step)?;
            if op == "OpSeqHead" {
                let Some(IRType::Seq { element }) = expr_type(operand) else {
                    return smt::unop(op, &v);
                };
                return smt::seq_head(&v, element);
            }
            if op == "OpSeqTail" {
                if let IRExpr::SeqLit { elements, ty, .. } = operand.as_ref() {
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
                    return try_encode_slot_expr(ctx, &set_lit, step);
                }
                let Some(IRType::Map { key, value }) = expr_type(operand) else {
                    return Err("Map::domain requires a map operand".to_owned());
                };
                return smt::map_domain(&v, key, value);
            }
            if op == "OpMapRange" {
                if let IRExpr::MapLit { entries, .. } = operand.as_ref() {
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
            Ok(smt::unop(op, &v)?)
        }

        IRExpr::Field {
            expr: recv, field, ..
        } => {
            if let IRExpr::Var { name, .. } = recv.as_ref() {
                // Check shared Choose variable params: `var.field` → shared Z3 var
                let qualified = format!("{name}.{field}");
                if let Some(val) = ctx.params.get(&qualified) {
                    return Ok(val.clone());
                }
                // Check cross-entity bindings (e.g., r.product_id where
                // r is from a prior Choose over Reservation)
                if let Some((entity, slot)) = ctx.bindings.get(name.as_str()) {
                    if let Some(val) = ctx.pool.field_at(entity, *slot, field, step) {
                        return Ok(val.clone());
                    }
                }
                // struct-typed system field access (e.g., ui.screen)
                if !ctx.system_name.is_empty()
                    && ctx.pool.is_system_struct_field(ctx.system_name, name)
                {
                    if let Some(val) = ctx.pool.system_field_at(ctx.system_name, &qualified, step) {
                        return Ok(val.clone());
                    }
                }
                // entity-typed step parameter field access.
                // `item.status` where item is an entity-typed param: resolve
                // by looking up the param slot value and the entity's field.
                if let Some(ent_name) = ctx.entity_param_types.get(name.as_str()) {
                    if let Some(param_val) = ctx.params.get(name.as_str()) {
                        let n_slots = ctx.pool.slots_for(ent_name);
                        // Build ITE chain: if param==0 then field_0
                        // elif param==1 then field_1...
                        let mut result: Option<SmtValue> = None;
                        for slot in (0..n_slots).rev() {
                            if let Some(field_val) = ctx.pool.field_at(ent_name, slot, field, step)
                            {
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
            // Fall back to current entity context
            if let Some(val) = ctx.pool.field_at(ctx.entity, ctx.slot, field, step) {
                return Ok(val.clone());
            }
            Err(format!(
                "slot field not found: {}.{field} slot={} step={step}",
                ctx.entity, ctx.slot
            ))
        }

        IRExpr::App { .. } => {
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
            try_encode_slot_expr(&inner_ctx, &query.body, step)
        }

        IRExpr::Prime { expr, .. } => try_encode_slot_expr(ctx, expr, step + 1),

        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            let arr = try_encode_slot_expr(ctx, map, step)?;
            let k = try_encode_slot_expr(ctx, key, step)?;
            let v = try_encode_slot_expr(ctx, value, step)?;
            if let Some(IRType::Map {
                value: value_ty, ..
            }) = expr_type(map)
            {
                return smt::map_store(&arr, &k, &v, value_ty);
            }
            Ok(SmtValue::Array(
                arr.as_array()
                    .map_err(|e| format!("slot map update array encoding failed: {e}"))?
                    .store(&k.to_dynamic(), &v.to_dynamic()),
            ))
        }

        IRExpr::Index { map, key, ty, .. } => {
            if let IRExpr::Var {
                name: store_name, ..
            } = map.as_ref()
            {
                if let Some(entity_name) = ctx.store_param_types.get(store_name.as_str()) {
                    let k = try_encode_slot_expr(ctx, key, step)?;
                    return Ok(encode_store_membership(ctx.pool, entity_name, &k, step));
                }
            }
            let arr = try_encode_slot_expr(ctx, map, step)?;
            let k = try_encode_slot_expr(ctx, key, step)?;
            if let Some(IRType::Map { value, .. }) = expr_type(map) {
                return smt::map_lookup(&arr, &k, value);
            }
            if let Some(IRType::Seq { element }) = expr_type(map) {
                return smt::seq_index(&arr, &k, element);
            }
            Ok(smt::dynamic_to_typed_value(
                arr.as_array()
                    .map_err(|e| format!("slot index array encoding failed: {e}"))?
                    .select(&k.to_dynamic()),
                ty,
            ))
        }

        IRExpr::MapLit { entries, ty, .. } => {
            // Build constant array with default value, then store each entry
            let (key_ty, val_ty) = match ty {
                IRType::Map { key, value } => (key.as_ref(), value.as_ref()),
                _ => return Err(format!("MapLit with non-Map type: {ty:?}")),
            };
            let key_sort = smt::ir_type_to_sort(key_ty);
            let default_val = smt::map_none_dynamic(val_ty);
            let mut arr = smt::const_array(&key_sort, &default_val);
            for entry in entries {
                let k = try_encode_slot_expr(ctx, &entry.0, step)?;
                let v = try_encode_slot_expr(ctx, &entry.1, step)?;
                arr = arr.store(&k.to_dynamic(), &smt::map_some_dynamic(val_ty, &v));
            }
            Ok(SmtValue::Array(arr))
        }

        IRExpr::SetLit { elements, ty, .. } => {
            // Set as characteristic function: Array<T, Bool>
            let elem_ty = match ty {
                IRType::Set { element } => element.as_ref(),
                _ => return Err(format!("SetLit with non-Set type: {ty:?}")),
            };
            let elem_sort = smt::ir_type_to_sort(elem_ty);
            let false_val = smt::bool_val(false).to_dynamic();
            let mut arr = smt::const_array(&elem_sort, &false_val);
            let true_val = smt::bool_val(true).to_dynamic();
            for elem in elements {
                let e = try_encode_slot_expr(ctx, elem, step)?;
                arr = arr.store(&e.to_dynamic(), &true_val);
            }
            Ok(SmtValue::Array(arr))
        }

        IRExpr::SeqLit { elements, ty, .. } => {
            let elem_ty = match ty {
                IRType::Seq { element } => element.as_ref(),
                _ => return Err(format!("SeqLit with non-Seq type: {ty:?}")),
            };
            let elems = elements
                .iter()
                .map(|elem| try_encode_slot_expr(ctx, elem, step))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(smt::seq_literal(elem_ty, &elems))
        }

        IRExpr::Card { expr: inner, .. } => Ok(match inner.as_ref() {
            IRExpr::SetLit { elements, .. } => {
                let unique: std::collections::HashSet<String> =
                    elements.iter().map(|e| format!("{e:?}")).collect();
                smt::int_val(i64::try_from(unique.len()).unwrap_or(0))
            }
            IRExpr::SeqLit { elements, .. } => {
                smt::int_val(i64::try_from(elements.len()).unwrap_or(0))
            }
            IRExpr::MapLit { entries, .. } => {
                let unique_keys: std::collections::HashSet<String> =
                    entries.iter().map(|(k, _)| format!("{k:?}")).collect();
                smt::int_val(i64::try_from(unique_keys.len()).unwrap_or(0))
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
        }),

        IRExpr::Exists {
            var,
            domain: IRType::Int,
            body,
            ..
        } => {
            let Some(entity_name) = infer_store_quant_entity(var, body, ctx.store_param_types)
            else {
                return Err(format!(
                    "slot expression encoding not yet supported: {expr:?}"
                ));
            };
            let n_slots = ctx.pool.slots_for(&entity_name);
            let mut disjuncts = Vec::new();
            for slot in 0..n_slots {
                let mut params = ctx.params.clone();
                params.insert(var.clone(), smt::int_val(slot as i64));
                let mut entity_param_types = ctx.entity_param_types.clone();
                entity_param_types.insert(var.clone(), entity_name.clone());
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
                disjuncts.push(try_encode_slot_expr(&inner_ctx, body, step)?.to_bool()?);
            }
            if disjuncts.is_empty() {
                return Ok(SmtValue::Bool(smt::bool_const(false)));
            }
            let refs: Vec<&Bool> = disjuncts.iter().collect();
            Ok(SmtValue::Bool(smt::bool_or(&refs)))
        }

        IRExpr::Forall {
            var,
            domain: IRType::Int,
            body,
            ..
        } => {
            let Some(entity_name) = infer_store_quant_entity(var, body, ctx.store_param_types)
            else {
                return Err(format!(
                    "slot expression encoding not yet supported: {expr:?}"
                ));
            };
            let n_slots = ctx.pool.slots_for(&entity_name);
            let mut conjuncts = Vec::new();
            for slot in 0..n_slots {
                let mut params = ctx.params.clone();
                params.insert(var.clone(), smt::int_val(slot as i64));
                let mut entity_param_types = ctx.entity_param_types.clone();
                entity_param_types.insert(var.clone(), entity_name.clone());
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
                conjuncts.push(try_encode_slot_expr(&inner_ctx, body, step)?.to_bool()?);
            }
            if conjuncts.is_empty() {
                return Ok(SmtValue::Bool(smt::bool_const(true)));
            }
            let refs: Vec<&Bool> = conjuncts.iter().collect();
            Ok(SmtValue::Bool(smt::bool_and(&refs)))
        }

        other => Err(format!(
            "slot expression encoding not yet supported: {other:?}"
        )),
    }
}

pub(super) fn encode_slot_literal(lit: &LitVal) -> SmtValue {
    match lit {
        LitVal::Int { value } => smt::int_val(*value),
        LitVal::Bool { value } => smt::bool_val(*value),
        LitVal::Real { value } | LitVal::Float { value } => {
            #[allow(clippy::cast_possible_truncation)]
            let scaled = (*value * 1_000_000.0) as i64;
            smt::real_val(scaled, 1_000_000)
        }
        LitVal::Str { .. } => smt::int_val(0),
    }
}
