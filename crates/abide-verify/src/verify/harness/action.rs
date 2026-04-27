use super::*;

/// Encode an entity action as a transition relation for a specific slot.
///
/// Returns a `Bool` formula: `guard(slot, step) AND updates(slot, step, step+1) AND frame(slot, step, step+1)`.
///
/// `params` supplies pre-built Z3 variables for action parameters (from `Apply` args/refs).
#[allow(clippy::implicit_hasher)]
pub fn encode_action(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entity: &IREntity,
    action: &IRTransition,
    slot: usize,
    step: usize,
    params: &HashMap<String, SmtValue>,
) -> Bool {
    try_encode_action(pool, vctx, entity, action, slot, step, params)
        .unwrap_or_else(|msg| panic!("{msg}"))
}

#[allow(clippy::implicit_hasher)]
pub fn try_encode_action(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entity: &IREntity,
    action: &IRTransition,
    slot: usize,
    step: usize,
    params: &HashMap<String, SmtValue>,
) -> Result<Bool, String> {
    assert!(
        step < pool.bound,
        "step {step} out of bounds for bound {}",
        pool.bound
    );

    let empty_ept: HashMap<String, String> = HashMap::new();
    let ctx = SlotEncodeCtx {
        pool,
        vctx,
        entity: &entity.name,
        slot,
        params: params.clone(),
        bindings: HashMap::new(),
        system_name: "",
        entity_param_types: &empty_ept,
        store_param_types: &empty_ept,
    };

    let mut conjuncts = Vec::new();

    // Guard: encode the requires clause for this slot at this step
    let guard = try_encode_slot_expr(&ctx, &action.guard, step)?;
    conjuncts.push(guard.to_bool()?);

    // Updates: for each primed assignment, set the field at step+1
    let updated_fields: Vec<String> = action.updates.iter().map(|u| u.field.clone()).collect();

    for update in &action.updates {
        let new_val = try_encode_slot_expr(&ctx, &update.value, step)?;
        if let Some(field_next) = pool.field_at(&entity.name, slot, &update.field, step + 1) {
            conjuncts.push(smt::smt_eq(&new_val, field_next)?);
        }
    }

    // Frame: fields NOT in updates stay the same
    for field in &entity.fields {
        if !updated_fields.contains(&field.name) {
            if let (Some(curr), Some(next)) = (
                pool.field_at(&entity.name, slot, &field.name, step),
                pool.field_at(&entity.name, slot, &field.name, step + 1),
            ) {
                conjuncts.push(smt::smt_eq(curr, next)?);
            }
        }
    }

    // Active flag stays true (action doesn't deactivate)
    if let (Some(SmtValue::Bool(act_curr)), Some(SmtValue::Bool(act_next))) = (
        pool.active_at(&entity.name, slot, step),
        pool.active_at(&entity.name, slot, step + 1),
    ) {
        conjuncts.push(act_curr.clone()); // must be active to act
        conjuncts.push(act_next.clone()); // stays active after
    }

    // enforce fsm transition validity. For each
    // fsm declared on this entity whose field this action mutates,
    // assert `(old == new) OR (old, new) ∈ fsm.transitions`. Identity
    // updates (`field' = field`) are exempted per — only
    // actual changes are checked. The verifier reports a counterexample
    // for any action that drives the field along an edge not in the
    // table.
    for fsm in &entity.fsm_decls {
        if !updated_fields.contains(&fsm.field) {
            continue;
        }
        let Some(old_val) = pool.field_at(&entity.name, slot, &fsm.field, step) else {
            continue;
        };
        let Some(new_val) = pool.field_at(&entity.name, slot, &fsm.field, step + 1) else {
            continue;
        };
        let mut allowed: Vec<Bool> = Vec::new();
        // Identity case — `field' = field` is always legal regardless
        // of the table.
        if let Ok(eq) = smt::smt_eq(old_val, new_val) {
            allowed.push(eq);
        }
        // Each table entry contributes one `pre == from AND post == to`
        // disjunct. Variant ids come from the shared variant assigner
        // so they agree with how `IRExpr::Ctor` is encoded elsewhere.
        for trans in &fsm.transitions {
            let from_id = vctx.variants.try_id_of(&fsm.enum_name, &trans.from)?;
            let to_id = vctx.variants.try_id_of(&fsm.enum_name, &trans.to)?;
            let from_val = smt::int_val(from_id);
            let to_val = smt::int_val(to_id);
            if let (Ok(pre_eq), Ok(post_eq)) = (
                smt::smt_eq(old_val, &from_val),
                smt::smt_eq(new_val, &to_val),
            ) {
                allowed.push(smt::bool_and(&[&pre_eq, &post_eq]));
            }
        }
        if !allowed.is_empty() {
            let refs: Vec<&Bool> = allowed.iter().collect();
            conjuncts.push(smt::bool_or(&refs));
        }
    }

    let refs: Vec<&Bool> = conjuncts.iter().collect();
    Ok(smt::bool_and(&refs))
}

/// Encode a transition with explicit read/write variable maps.
///
/// Unlike `encode_action` which reads from `step` and writes to `step+1`,
/// this function reads guards and update value expressions from `read_vars`
/// and writes updates to `write_vars`. Fields not updated are framed from
/// `read_vars` to `write_vars`.
///
/// Used for sequential Apply chaining: first Apply reads from step k and
/// writes to intermediate vars; next Apply reads from those and writes to
/// step k+1.
#[allow(clippy::implicit_hasher)]
pub fn encode_action_with_vars(
    entity: &IREntity,
    action: &IRTransition,
    _slot: usize,
    read_vars: &HashMap<String, SmtValue>,
    write_vars: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    params: &HashMap<String, SmtValue>,
) -> Bool {
    try_encode_action_with_vars(entity, action, _slot, read_vars, write_vars, vctx, params)
        .unwrap_or_else(|msg| panic!("{msg}"))
}

#[allow(clippy::implicit_hasher)]
pub fn try_encode_action_with_vars(
    entity: &IREntity,
    action: &IRTransition,
    _slot: usize,
    read_vars: &HashMap<String, SmtValue>,
    write_vars: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    params: &HashMap<String, SmtValue>,
) -> Result<Bool, String> {
    // Build a context that resolves field names from read_vars
    let mut conjuncts = Vec::new();

    // Guard: evaluate against read_vars
    let guard = try_eval_expr_with_vars(&action.guard, entity, read_vars, vctx, params)?;
    conjuncts.push(guard.to_bool()?);

    // Updates: evaluate value from read_vars, constrain write_vars
    let updated_fields: Vec<String> = action.updates.iter().map(|u| u.field.clone()).collect();
    for update in &action.updates {
        let new_val = try_eval_expr_with_vars(&update.value, entity, read_vars, vctx, params)?;
        if let Some(write_val) = write_vars.get(&update.field) {
            conjuncts.push(smt::smt_eq(&new_val, write_val)?);
        }
    }

    // Frame: fields NOT in updates copied from read to write
    for field in &entity.fields {
        if !updated_fields.contains(&field.name) {
            if let (Some(read_val), Some(write_val)) =
                (read_vars.get(&field.name), write_vars.get(&field.name))
            {
                conjuncts.push(smt::smt_eq(read_val, write_val)?);
            }
        }
    }

    // enforce fsm transition validity in the
    // chained-apply path too. Without this, an event that performs
    // multiple sequential applies on the same entity could bypass the
    // single-apply fsm constraint added in `encode_action`. Each fsm
    // declared on this entity whose field this action mutates gets a
    // `(old == new) OR ⋁ (old == from_i ∧ new == to_i)` constraint
    // built against the chained read/write vars (not the pool, since
    // intermediate state lives in fresh SMT vars). Identity updates
    // are exempt — only actual changes are checked.
    for fsm in &entity.fsm_decls {
        if !updated_fields.contains(&fsm.field) {
            continue;
        }
        let Some(old_val) = read_vars.get(&fsm.field) else {
            continue;
        };
        let Some(new_val) = write_vars.get(&fsm.field) else {
            continue;
        };
        let mut allowed: Vec<Bool> = Vec::new();
        if let Ok(eq) = smt::smt_eq(old_val, new_val) {
            allowed.push(eq);
        }
        for trans in &fsm.transitions {
            let from_id = vctx.variants.try_id_of(&fsm.enum_name, &trans.from)?;
            let to_id = vctx.variants.try_id_of(&fsm.enum_name, &trans.to)?;
            let from_val = smt::int_val(from_id);
            let to_val = smt::int_val(to_id);
            if let (Ok(pre_eq), Ok(post_eq)) = (
                smt::smt_eq(old_val, &from_val),
                smt::smt_eq(new_val, &to_val),
            ) {
                allowed.push(smt::bool_and(&[&pre_eq, &post_eq]));
            }
        }
        if !allowed.is_empty() {
            let refs: Vec<&Bool> = allowed.iter().collect();
            conjuncts.push(smt::bool_or(&refs));
        }
    }

    if conjuncts.is_empty() {
        return Ok(smt::bool_const(true));
    }
    let refs: Vec<&Bool> = conjuncts.iter().collect();
    Ok(smt::bool_and(&refs))
}

/// Evaluate an IR expression using explicit variable maps instead of `SlotPool`.
///
/// Resolves field names from `vars` (a map of `field_name` → `SmtValue`).
/// Falls back to `params` for action parameters.
#[allow(clippy::only_used_in_recursion)]
#[allow(dead_code)]
fn eval_expr_with_vars(
    expr: &IRExpr,
    entity: &IREntity,
    vars: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    params: &HashMap<String, SmtValue>,
) -> SmtValue {
    try_eval_expr_with_vars(expr, entity, vars, vctx, params).unwrap_or_else(|msg| panic!("{msg}"))
}

#[allow(clippy::only_used_in_recursion)]
pub(super) fn try_eval_expr_with_vars(
    expr: &IRExpr,
    entity: &IREntity,
    vars: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    params: &HashMap<String, SmtValue>,
) -> Result<SmtValue, String> {
    match expr {
        IRExpr::Lit { value, .. } => Ok(encode_slot_literal(value)),
        IRExpr::Var { name, .. } => {
            if let Some(val) = params.get(name) {
                return Ok(val.clone());
            }
            if let Some(val) = vars.get(name) {
                return Ok(val.clone());
            }
            Err(format!("variable not found in chained encoding: {name}"))
        }
        IRExpr::Field {
            expr: recv, field, ..
        } => {
            if let IRExpr::Var { name, .. } = recv.as_ref() {
                // Qualified lookup in params (cross-entity or event-level refs)
                let qualified = format!("{name}.{field}");
                if let Some(val) = params.get(&qualified) {
                    return Ok(val.clone());
                }
                // Same-entity field: only resolve from vars (intermediate state)
                if let Some(val) = vars.get(field) {
                    return Ok(val.clone());
                }
                // Check unqualified in params as last resort
                if let Some(val) = params.get(field) {
                    return Ok(val.clone());
                }
            }
            // No blind fallback — strict resolution only
            Err(format!(
                "field {field} not found in chained encoding (vars: {:?}, params: {:?})",
                vars.keys().collect::<Vec<_>>(),
                params.keys().collect::<Vec<_>>()
            ))
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
            let l = try_eval_expr_with_vars(left, entity, vars, vctx, params)?;
            let r = try_eval_expr_with_vars(right, entity, vars, vctx, params)?;
            Ok(smt::binop(op, &l, &r)?)
        }
        IRExpr::UnOp { op, operand, .. } => {
            let v = try_eval_expr_with_vars(operand, entity, vars, vctx, params)?;
            Ok(smt::unop(op, &v)?)
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            let arr = try_eval_expr_with_vars(map, entity, vars, vctx, params)?;
            let k = try_eval_expr_with_vars(key, entity, vars, vctx, params)?;
            let v = try_eval_expr_with_vars(value, entity, vars, vctx, params)?;
            Ok(SmtValue::Array(
                arr.as_array()
                    .map_err(|e| format!("chained map update array encoding failed: {e}"))?
                    .store(&k.to_dynamic(), &v.to_dynamic()),
            ))
        }
        IRExpr::Index { map, key, .. } => {
            let arr = try_eval_expr_with_vars(map, entity, vars, vctx, params)?;
            let k = try_eval_expr_with_vars(key, entity, vars, vctx, params)?;
            Ok(SmtValue::Dynamic(
                arr.as_array()
                    .map_err(|e| format!("chained index array encoding failed: {e}"))?
                    .select(&k.to_dynamic()),
            ))
        }
        _ => Err(format!(
            "unsupported expression in chained action encoding: {:?}",
            std::mem::discriminant(expr)
        )),
    }
}

/// Encode a `create` action: find an inactive slot and activate it.
///
/// Returns a `Bool` formula: `exists slot_i. !active(i, step) AND active(i, step+1) AND fields...`
///
/// Each disjunct also frames all OTHER slots of the same entity so that
/// non-selected slots cannot take arbitrary values.
#[allow(clippy::implicit_hasher)]
pub fn encode_create(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entity_name: &str,
    entity_ir: Option<&IREntity>,
    create_fields: &[(String, IRExpr)],
    step: usize,
    step_params: &HashMap<String, SmtValue>,
) -> Bool {
    try_encode_create(
        pool,
        vctx,
        entity_name,
        entity_ir,
        create_fields,
        step,
        step_params,
    )
    .unwrap_or_else(|msg| panic!("{msg}"))
}

#[allow(clippy::implicit_hasher)]
pub fn try_encode_create(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entity_name: &str,
    entity_ir: Option<&IREntity>,
    create_fields: &[(String, IRExpr)],
    step: usize,
    step_params: &HashMap<String, SmtValue>,
) -> Result<Bool, String> {
    assert!(
        step < pool.bound,
        "step {step} out of bounds for bound {}",
        pool.bound
    );

    let empty_ept: HashMap<String, String> = HashMap::new();
    let n_slots = pool.slots_for(entity_name);
    let mut slot_disjuncts = Vec::new();

    for slot in 0..n_slots {
        let ctx = SlotEncodeCtx {
            pool,
            vctx,
            entity: entity_name,
            slot,
            params: step_params.clone(),
            bindings: HashMap::new(),
            system_name: "",
            entity_param_types: &empty_ept,
            store_param_types: &empty_ept,
        };

        let mut conjuncts = Vec::new();

        // Slot must be inactive at current step
        if let Some(SmtValue::Bool(act_curr)) = pool.active_at(entity_name, slot, step) {
            conjuncts.push(smt::bool_not(act_curr));
        }
        // Activate at next step
        if let Some(SmtValue::Bool(act_next)) = pool.active_at(entity_name, slot, step + 1) {
            conjuncts.push(act_next.clone());
        }

        // Set field values at next step from create block
        let create_field_names: HashSet<&str> =
            create_fields.iter().map(|(n, _)| n.as_str()).collect();
        for (field_name, value_expr) in create_fields {
            let val = try_encode_slot_expr(&ctx, value_expr, step)?;
            if let Some(field_next) = pool.field_at(entity_name, slot, field_name, step + 1) {
                conjuncts.push(smt::smt_eq(&val, field_next)?);
            }
        }

        // Apply entity defaults for fields NOT specified in the create block.
        // Without this, unconstrained fields could take any value, making the
        // verification overly permissive.
        //
        // When `initial_constraint` is present (from `in {...}` or `where`),
        // assert the constraint with `$` / field name substituted for the
        // field's next-step value, instead of fixing to a single default.
        if let Some(ent) = entity_ir {
            for field in &ent.fields {
                if create_field_names.contains(field.name.as_str()) {
                    continue; // already set by create block
                }
                if let Some(ref constraint_expr) = field.initial_constraint {
                    // Nondeterministic: encode the constraint with $ bound to field_next.
                    if let Some(field_next) =
                        pool.field_at(entity_name, slot, &field.name, step + 1)
                    {
                        let mut params = ctx.params.clone();
                        params.insert("$".to_owned(), field_next.clone());
                        params.insert(field.name.clone(), field_next.clone());
                        let pred_ctx = SlotEncodeCtx {
                            pool: ctx.pool,
                            vctx: ctx.vctx,
                            entity: ctx.entity,
                            slot: ctx.slot,
                            params,
                            bindings: ctx.bindings.clone(),
                            system_name: "",
                            entity_param_types: &empty_ept,
                            store_param_types: &empty_ept,
                        };
                        let val = try_encode_slot_expr(&pred_ctx, constraint_expr, step + 1)?;
                        if let SmtValue::Bool(b) = val {
                            conjuncts.push(b);
                        }
                    }
                } else if let Some(ref default_expr) = field.default {
                    // Deterministic: field_next == default
                    let val = try_encode_slot_expr(&ctx, default_expr, step)?;
                    if let Some(field_next) =
                        pool.field_at(entity_name, slot, &field.name, step + 1)
                    {
                        conjuncts.push(smt::smt_eq(&val, field_next)?);
                    }
                }
            }
        }

        // Frame all OTHER slots of this entity within the disjunct
        if let Some(ent) = entity_ir {
            let slot_frame = frame_entity_slots_except(pool, ent, slot, step);
            conjuncts.extend(slot_frame);
        }

        let refs: Vec<&Bool> = conjuncts.iter().collect();
        if !refs.is_empty() {
            slot_disjuncts.push(smt::bool_and(&refs));
        }
    }

    // Any slot can be chosen for creation
    let refs: Vec<&Bool> = slot_disjuncts.iter().collect();
    if refs.is_empty() {
        Ok(smt::bool_const(false)) // no slots available
    } else {
        Ok(smt::bool_or(&refs))
    }
}

/// Build a `HashMap<String, SmtValue>` mapping action parameter names to Z3 values
/// from the positional `args` and `refs` of an `Apply` action.
///
/// `action.params[i].name` maps to `encode(args[i])`, and `action.refs[i].name` maps
/// to the slot-resolved value for the entity variable name in `refs[i]`.
#[allow(dead_code)]
fn build_apply_params(
    ctx: &SlotEncodeCtx<'_>,
    action: &IRTransition,
    args: &[IRExpr],
    refs: &[String],
    step: usize,
) -> HashMap<String, SmtValue> {
    try_build_apply_params(ctx, action, args, refs, step).unwrap_or_else(|msg| panic!("{msg}"))
}

pub(super) fn try_build_apply_params(
    ctx: &SlotEncodeCtx<'_>,
    action: &IRTransition,
    args: &[IRExpr],
    refs: &[String],
    step: usize,
) -> Result<HashMap<String, SmtValue>, String> {
    let mut map = HashMap::new();

    // Wire positional args to action params
    for (param, arg_expr) in action.params.iter().zip(args.iter()) {
        let val = try_encode_slot_expr(ctx, arg_expr, step)?;
        map.insert(param.name.clone(), val);
    }

    // Wire refs to action refs (entity variable names → resolve from slot context)
    for (ref_decl, ref_name) in action.refs.iter().zip(refs.iter()) {
        // refs are entity variable names — resolve from params first, then slot fields
        if let Some(val) = ctx.params.get(ref_name) {
            map.insert(ref_decl.name.clone(), val.clone());
        } else if let Some(val) = ctx.pool.field_at(ctx.entity, ctx.slot, ref_name, step) {
            map.insert(ref_decl.name.clone(), val.clone());
        }
    }

    Ok(map)
}
