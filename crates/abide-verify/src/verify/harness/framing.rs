use std::collections::HashSet;

use super::*;

/// Generate stutter (idle) constraint: all fields and active flags unchanged.
pub fn stutter_constraint(pool: &SlotPool, entities: &[IREntity], step: usize) -> Bool {
    assert!(
        step < pool.bound,
        "step {step} out of bounds for bound {}",
        pool.bound
    );

    let mut conjuncts = Vec::new();

    for entity in entities {
        let n_slots = pool.slots_for(&entity.name);
        for slot in 0..n_slots {
            if let (Some(SmtValue::Bool(curr)), Some(SmtValue::Bool(next))) = (
                pool.active_at(&entity.name, slot, step),
                pool.active_at(&entity.name, slot, step + 1),
            ) {
                conjuncts.push(smt::bool_eq(next, curr));
            }
            for field in &entity.fields {
                if let (Some(curr), Some(next)) = (
                    pool.field_at(&entity.name, slot, &field.name, step),
                    pool.field_at(&entity.name, slot, &field.name, step + 1),
                ) {
                    conjuncts.push(smt::smt_eq(curr, next).expect("internal: stutter smt_eq"));
                }
            }
        }
    }

    let refs: Vec<&Bool> = conjuncts.iter().collect();
    smt::bool_and(&refs)
}

pub(super) fn frame_untouched_slots(
    pool: &SlotPool,
    entities: &[IREntity],
    touched: &HashSet<(String, usize)>,
    step: usize,
) -> Vec<Bool> {
    let mut conjuncts = Vec::new();

    for entity in entities {
        let n_slots = pool.slots_for(&entity.name);
        for slot in 0..n_slots {
            if touched.contains(&(entity.name.clone(), slot)) {
                continue;
            }
            if let (Some(SmtValue::Bool(curr)), Some(SmtValue::Bool(next))) = (
                pool.active_at(&entity.name, slot, step),
                pool.active_at(&entity.name, slot, step + 1),
            ) {
                conjuncts.push(smt::bool_eq(next, curr));
            }
            for field in &entity.fields {
                if let (Some(curr), Some(next)) = (
                    pool.field_at(&entity.name, slot, &field.name, step),
                    pool.field_at(&entity.name, slot, &field.name, step + 1),
                ) {
                    conjuncts
                        .push(smt::smt_eq(curr, next).expect("internal: frame untouched smt_eq"));
                }
            }
        }
    }

    conjuncts
}

pub(super) fn frame_entity_slots_except(
    pool: &SlotPool,
    entity: &IREntity,
    excluded_slot: usize,
    step: usize,
) -> Vec<Bool> {
    let mut conjuncts = Vec::new();
    let n_slots = pool.slots_for(&entity.name);

    for slot in 0..n_slots {
        if slot == excluded_slot {
            continue;
        }
        if let (Some(SmtValue::Bool(curr)), Some(SmtValue::Bool(next))) = (
            pool.active_at(&entity.name, slot, step),
            pool.active_at(&entity.name, slot, step + 1),
        ) {
            conjuncts.push(smt::bool_eq(next, curr));
        }
        for field in &entity.fields {
            if let (Some(curr), Some(next)) = (
                pool.field_at(&entity.name, slot, &field.name, step),
                pool.field_at(&entity.name, slot, &field.name, step + 1),
            ) {
                conjuncts.push(smt::smt_eq(curr, next).expect("internal: frame except smt_eq"));
            }
        }
    }

    conjuncts
}

#[allow(clippy::implicit_hasher)]
pub fn frame_specific_slots(
    pool: &SlotPool,
    entities: &[IREntity],
    slots_to_frame: &HashSet<(String, usize)>,
    step: usize,
) -> Vec<Bool> {
    let mut frames = Vec::new();
    for (entity_name, slot_idx) in slots_to_frame {
        if let Some(entity) = entities.iter().find(|e| e.name == *entity_name) {
            if let (Some(SmtValue::Bool(curr)), Some(SmtValue::Bool(next))) = (
                pool.active_at(entity_name, *slot_idx, step),
                pool.active_at(entity_name, *slot_idx, step + 1),
            ) {
                frames.push(smt::bool_eq(next, curr));
            }
            for field in &entity.fields {
                if let (Some(curr), Some(next)) = (
                    pool.field_at(entity_name, *slot_idx, &field.name, step),
                    pool.field_at(entity_name, *slot_idx, &field.name, step + 1),
                ) {
                    frames.push(
                        smt::smt_eq(curr, next).expect("internal: frame specific slot smt_eq"),
                    );
                }
            }
        }
    }
    frames
}

#[allow(clippy::implicit_hasher)]
pub fn frame_system_fields(
    pool: &SlotPool,
    system: &IRSystem,
    touched_fields: &HashSet<String>,
    step: usize,
) -> Vec<Bool> {
    let mut frames = Vec::new();
    for field in &system.fields {
        if touched_fields.contains(&field.name) {
            continue;
        }
        if let (Some(curr), Some(next)) = (
            pool.system_field_at(&system.name, &field.name, step),
            pool.system_field_at(&system.name, &field.name, step + 1),
        ) {
            frames.push(smt::smt_eq(curr, next).expect("internal: frame system field smt_eq"));
        }
    }
    frames
}

#[allow(clippy::implicit_hasher)]
pub fn extract_primed_system_fields(
    body: &[IRAction],
    system_field_names: &HashSet<String>,
) -> HashSet<String> {
    let mut touched = HashSet::new();
    for action in body {
        if let IRAction::ExprStmt { expr } = action {
            collect_primed_fields(expr, system_field_names, &mut touched);
        }
    }
    touched
}

fn collect_primed_fields(
    expr: &IRExpr,
    sys_fields: &HashSet<String>,
    touched: &mut HashSet<String>,
) {
    match expr {
        IRExpr::BinOp { left, right, .. } => {
            collect_primed_fields(left, sys_fields, touched);
            collect_primed_fields(right, sys_fields, touched);
        }
        IRExpr::Prime { expr: inner, .. } => match inner.as_ref() {
            IRExpr::Var { name, .. } if sys_fields.contains(name) => {
                touched.insert(name.clone());
            }
            IRExpr::Field {
                expr: recv, field, ..
            } => {
                if let IRExpr::Var { name, .. } = recv.as_ref() {
                    let compound = format!("{name}.{field}");
                    if sys_fields.contains(&compound) {
                        touched.insert(compound);
                    }
                }
            }
            _ => {}
        },
        _ => {}
    }
}

pub fn system_field_initial_constraints(
    pool: &SlotPool,
    vctx: &VerifyContext,
    system: &IRSystem,
) -> Vec<Bool> {
    try_system_field_initial_constraints(pool, vctx, system).unwrap_or_else(|msg| panic!("{msg}"))
}

pub fn try_system_field_initial_constraints(
    pool: &SlotPool,
    vctx: &VerifyContext,
    system: &IRSystem,
) -> Result<Vec<Bool>, String> {
    let empty_ept: HashMap<String, String> = HashMap::new();
    let mut constraints = Vec::new();
    for field in &system.fields {
        if let Some(ref default_expr) = field.default {
            if let Some(var_at_0) = pool.system_field_at(&system.name, &field.name, 0) {
                let ctx = SlotEncodeCtx {
                    pool,
                    vctx,
                    entity: "",
                    slot: 0,
                    params: HashMap::new(),
                    bindings: HashMap::new(),
                    system_name: &system.name,
                    entity_param_types: &empty_ept,
                    store_param_types: &empty_ept,
                };
                let val = try_encode_slot_expr(&ctx, default_expr, 0)?;
                constraints.push(smt::smt_eq(var_at_0, &val)?);
            }
        }
    }
    Ok(constraints)
}

pub(super) fn system_field_name_sets(systems: &[IRSystem]) -> HashMap<String, HashSet<String>> {
    systems
        .iter()
        .filter(|s| !s.fields.is_empty())
        .map(|s| {
            let names: HashSet<String> = s.fields.iter().map(|f| f.name.clone()).collect();
            (s.name.clone(), names)
        })
        .collect()
}

pub(super) fn system_field_frame_conjuncts(
    pool: &SlotPool,
    vctx: &VerifyContext,
    systems: &[IRSystem],
    owner: &IRSystem,
    body: &[IRAction],
    step: usize,
) -> Vec<Bool> {
    let system_field_sets = system_field_name_sets(systems);
    let mut sys_frames = Vec::new();
    if let Some(field_set) = system_field_sets.get(&owner.name) {
        let touched = extract_primed_system_fields(body, field_set);
        sys_frames.extend(frame_system_fields(pool, owner, &touched, step));
        sys_frames.extend(system_field_fsm_conjuncts(
            pool, vctx, owner, &touched, step,
        ));
    }
    for other_sys in systems {
        if other_sys.name != owner.name && !other_sys.fields.is_empty() {
            let empty = HashSet::new();
            sys_frames.extend(frame_system_fields(pool, other_sys, &empty, step));
        }
    }
    sys_frames
}

pub(super) fn system_field_fsm_conjuncts(
    pool: &SlotPool,
    vctx: &VerifyContext,
    system: &IRSystem,
    touched_fields: &HashSet<String>,
    step: usize,
) -> Vec<Bool> {
    let mut conjuncts = Vec::new();
    for fsm in &system.fsm_decls {
        if !touched_fields.contains(&fsm.field) {
            continue;
        }
        let Some(old_val) = pool.system_field_at(&system.name, &fsm.field, step) else {
            continue;
        };
        let Some(new_val) = pool.system_field_at(&system.name, &fsm.field, step + 1) else {
            continue;
        };
        let mut allowed = Vec::new();
        if let Ok(eq) = smt::smt_eq(old_val, new_val) {
            allowed.push(eq);
        }
        for trans in &fsm.transitions {
            let from_id = match vctx.variants.try_id_of(&fsm.enum_name, &trans.from) {
                Ok(id) => id,
                Err(_) => continue,
            };
            let to_id = match vctx.variants.try_id_of(&fsm.enum_name, &trans.to) {
                Ok(id) => id,
                Err(_) => continue,
            };
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
    conjuncts
}
