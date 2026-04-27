use std::collections::{HashMap, HashSet};

use super::*;

pub fn transition_constraints(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    step: usize,
    assumption_set: &IRAssumptionSet,
) -> Bool {
    assert!(
        step < pool.bound,
        "step {step} out of bounds for bound {}",
        pool.bound
    );

    let mut disjuncts = Vec::new();

    for system in systems {
        for event in &system.steps {
            let event_formula = encode_step(pool, vctx, entities, systems, event, step);
            let sys_frames =
                system_field_frame_conjuncts(pool, vctx, systems, system, &event.body, step);
            if sys_frames.is_empty() {
                disjuncts.push(event_formula);
            } else {
                let mut all = vec![event_formula];
                all.extend(sys_frames);
                let refs: Vec<&Bool> = all.iter().collect();
                disjuncts.push(smt::bool_and(&refs));
            }
        }
    }

    if assumption_set.stutter {
        let mut stutter_parts = vec![stutter_constraint(pool, entities, step)];
        for system in systems {
            if !system.fields.is_empty() {
                let empty_touched = HashSet::new();
                stutter_parts.extend(frame_system_fields(pool, system, &empty_touched, step));
            }
        }
        let refs: Vec<&Bool> = stutter_parts.iter().collect();
        disjuncts.push(smt::bool_and(&refs));
    }

    let refs: Vec<&Bool> = disjuncts.iter().collect();
    smt::bool_or(&refs)
}

pub struct FireTracking {
    pub fire_vars: HashMap<(String, String), Vec<Bool>>,
    pub clause_fire_vars: HashMap<(String, String, usize), Vec<Bool>>,
    pub stutter_vars: Vec<Bool>,
    pub constraints: Vec<Bool>,
}

pub fn transition_constraints_with_fire(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    bound: usize,
    assumption_set: &IRAssumptionSet,
) -> FireTracking {
    try_transition_constraints_with_fire(pool, vctx, entities, systems, bound, assumption_set)
        .unwrap_or_else(|msg| panic!("{msg}"))
}

pub fn try_transition_constraints_with_fire(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    bound: usize,
    assumption_set: &IRAssumptionSet,
) -> Result<FireTracking, String> {
    let mut fire_vars: HashMap<(String, String), Vec<Bool>> = HashMap::new();
    let mut clause_fire_vars: HashMap<(String, String, usize), Vec<Bool>> = HashMap::new();
    let mut stutter_vars = Vec::new();
    let mut constraints = Vec::new();

    for system in systems {
        for (clause_idx, event) in system.steps.iter().enumerate() {
            let key = (system.name.clone(), event.name.clone());
            fire_vars.entry(key).or_default();
            clause_fire_vars
                .entry((system.name.clone(), event.name.clone(), clause_idx))
                .or_default();
        }
    }

    for step in 0..bound {
        let mut step_indicators: Vec<Bool> = Vec::new();
        let mut command_clauses: HashMap<(String, String), Vec<Bool>> = HashMap::new();

        for system in systems {
            for (clause_idx, event) in system.steps.iter().enumerate() {
                let key = (system.name.clone(), event.name.clone());
                let clause_fire_var = smt::bool_var(&format!(
                    "fire_{}_{}_c{}_t{step}",
                    system.name, event.name, clause_idx
                ));
                let clause_fire_bool = clause_fire_var
                    .to_bool()
                    .expect("internal: clause fire var");

                let event_formula = try_encode_step(pool, vctx, entities, systems, event, step)?;
                let sys_frames =
                    system_field_frame_conjuncts(pool, vctx, systems, system, &event.body, step);
                let event_formula = if sys_frames.is_empty() {
                    event_formula
                } else {
                    let mut parts = vec![event_formula];
                    parts.extend(sys_frames);
                    let refs: Vec<&Bool> = parts.iter().collect();
                    smt::bool_and(&refs)
                };
                constraints.push(smt::bool_implies(&clause_fire_bool, &event_formula));

                command_clauses
                    .entry(key)
                    .or_default()
                    .push(clause_fire_bool.clone());
                clause_fire_vars
                    .get_mut(&(system.name.clone(), event.name.clone(), clause_idx))
                    .expect("clause fire key exists")
                    .push(clause_fire_bool.clone());
                step_indicators.push(clause_fire_bool);
            }
        }

        for (key, clause_bools) in command_clauses {
            let command_fire_var = smt::bool_var(&format!("fire_{}_{}_t{step}", key.0, key.1));
            let command_fire_bool = command_fire_var
                .to_bool()
                .expect("internal: command fire var");
            let clause_refs: Vec<&Bool> = clause_bools.iter().collect();
            let command_fired = smt::bool_or(&clause_refs);
            constraints.push(smt::bool_eq(&command_fire_bool, &command_fired));
            fire_vars
                .get_mut(&key)
                .expect("command fire key exists")
                .push(command_fire_bool);
        }

        if assumption_set.stutter {
            let stutter_var = smt::bool_var(&format!("stutter_t{step}"));
            let stutter_bool = stutter_var.to_bool().expect("internal: stutter var");
            let mut stutter_parts = vec![stutter_constraint(pool, entities, step)];
            for system in systems {
                if !system.fields.is_empty() {
                    let empty_touched = HashSet::new();
                    stutter_parts.extend(frame_system_fields(pool, system, &empty_touched, step));
                }
            }
            let stutter_refs: Vec<&Bool> = stutter_parts.iter().collect();
            let stutter_formula = smt::bool_and(&stutter_refs);
            constraints.push(smt::bool_implies(&stutter_bool, &stutter_formula));
            step_indicators.push(stutter_bool.clone());
            stutter_vars.push(stutter_bool);
        }

        let indicator_refs: Vec<&Bool> = step_indicators.iter().collect();
        constraints.push(smt::bool_or(&indicator_refs));
        for i in 0..step_indicators.len() {
            for j in (i + 1)..step_indicators.len() {
                constraints.push(smt::bool_not(&smt::bool_and(&[
                    &step_indicators[i],
                    &step_indicators[j],
                ])));
            }
        }
    }

    Ok(FireTracking {
        fire_vars,
        clause_fire_vars,
        stutter_vars,
        constraints,
    })
}

pub struct LassoLoop {
    pub loop_indicators: Vec<Bool>,
    pub constraints: Vec<Bool>,
}

pub fn lasso_loopback(pool: &SlotPool, entities: &[IREntity], systems: &[IRSystem]) -> LassoLoop {
    let bound = pool.bound;
    let mut loop_indicators = Vec::new();
    let mut constraints = Vec::new();

    for l in 0..bound {
        let indicator = smt::bool_var(&format!("loop_l_{l}"));
        let indicator_bool = indicator.to_bool().expect("internal: loop indicator");

        let mut equalities = Vec::new();
        for entity in entities {
            let n_slots = pool.slots_for(&entity.name);
            for slot in 0..n_slots {
                if let (Some(SmtValue::Bool(at_bound)), Some(SmtValue::Bool(at_l))) = (
                    pool.active_at(&entity.name, slot, bound),
                    pool.active_at(&entity.name, slot, l),
                ) {
                    equalities.push(smt::bool_eq(at_bound, at_l));
                }
                for field in &entity.fields {
                    if let (Some(val_bound), Some(val_l)) = (
                        pool.field_at(&entity.name, slot, &field.name, bound),
                        pool.field_at(&entity.name, slot, &field.name, l),
                    ) {
                        if let Ok(eq) = smt::smt_eq(val_bound, val_l) {
                            equalities.push(eq);
                        }
                    }
                }
            }
        }
        for system in systems {
            for field in &system.fields {
                if let (Some(val_bound), Some(val_l)) = (
                    pool.system_field_at(&system.name, &field.name, bound),
                    pool.system_field_at(&system.name, &field.name, l),
                ) {
                    if let Ok(eq) = smt::smt_eq(val_bound, val_l) {
                        equalities.push(eq);
                    }
                }
            }
        }

        if equalities.is_empty() {
            loop_indicators.push(indicator_bool);
            continue;
        }

        let eq_refs: Vec<&Bool> = equalities.iter().collect();
        let loopback_eq = smt::bool_and(&eq_refs);
        constraints.push(smt::bool_implies(&indicator_bool, &loopback_eq));
        loop_indicators.push(indicator_bool);
    }

    let ind_refs: Vec<&Bool> = loop_indicators.iter().collect();
    constraints.push(smt::bool_or(&ind_refs));
    for i in 0..loop_indicators.len() {
        for j in (i + 1)..loop_indicators.len() {
            constraints.push(smt::bool_not(&smt::bool_and(&[
                &loop_indicators[i],
                &loop_indicators[j],
            ])));
        }
    }

    LassoLoop {
        loop_indicators,
        constraints,
    }
}

pub fn encode_step_enabled(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    event: &IRStep,
    step: usize,
) -> Bool {
    try_encode_step_enabled(pool, vctx, entities, systems, event, step)
        .unwrap_or_else(|msg| panic!("{msg}"))
}

pub fn try_encode_step_enabled(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    event: &IRStep,
    step: usize,
) -> Result<Bool, String> {
    try_encode_step_enabled_inner(pool, vctx, entities, systems, event, step, None, 0)
}

#[allow(clippy::implicit_hasher)]
pub fn encode_step_enabled_with_params(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    event: &IRStep,
    step: usize,
    params: HashMap<String, SmtValue>,
) -> Bool {
    try_encode_step_enabled_with_params(pool, vctx, entities, systems, event, step, params)
        .unwrap_or_else(|msg| panic!("{msg}"))
}

#[allow(clippy::implicit_hasher)]
pub fn try_encode_step_enabled_with_params(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    event: &IRStep,
    step: usize,
    params: HashMap<String, SmtValue>,
) -> Result<Bool, String> {
    try_encode_step_enabled_inner(pool, vctx, entities, systems, event, step, Some(params), 0)
}

#[allow(clippy::too_many_arguments)]
#[allow(dead_code)]
fn encode_step_enabled_inner(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    event: &IRStep,
    step: usize,
    override_params: Option<HashMap<String, SmtValue>>,
    depth: usize,
) -> Bool {
    try_encode_step_enabled_inner(
        pool,
        vctx,
        entities,
        systems,
        event,
        step,
        override_params,
        depth,
    )
    .unwrap_or_else(|msg| panic!("{msg}"))
}

#[allow(clippy::too_many_arguments)]
fn try_encode_step_enabled_inner(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    event: &IRStep,
    step: usize,
    override_params: Option<HashMap<String, SmtValue>>,
    depth: usize,
) -> Result<Bool, String> {
    let empty_ept: HashMap<String, String> = HashMap::new();
    let mut conditions = Vec::new();

    let params = override_params.unwrap_or_else(|| build_step_params(&event.params, step));
    let store_param_types: HashMap<String, String> = systems
        .iter()
        .find(|s| {
            s.steps
                .iter()
                .any(|st| std::ptr::eq(st, event) || st.name == event.name)
        })
        .map(|s| {
            s.store_params
                .iter()
                .map(|p| (p.name.clone(), p.entity_type.clone()))
                .collect()
        })
        .unwrap_or_default();

    if !matches!(
        &event.guard,
        IRExpr::Lit {
            value: LitVal::Bool { value: true },
            ..
        }
    ) {
        conditions.push(try_encode_guard_expr(
            pool,
            vctx,
            &event.guard,
            &params,
            &store_param_types,
            step,
        )?);
    }

    for action in &event.body {
        match action {
            IRAction::Choose {
                entity: ent_name,
                filter,
                ..
            } => {
                let n_slots = pool.slots_for(ent_name);
                let entity_ir = entities.iter().find(|e| e.name == *ent_name);
                let mut slot_disjuncts = Vec::new();
                for slot in 0..n_slots {
                    if let Some(SmtValue::Bool(active)) = pool.active_at(ent_name, slot, step) {
                        if entity_ir.is_some() {
                            let ctx = SlotEncodeCtx {
                                pool,
                                vctx,
                                entity: ent_name,
                                slot,
                                params: params.clone(),
                                bindings: HashMap::new(),
                                system_name: "",
                                entity_param_types: &empty_ept,
                                store_param_types: &empty_ept,
                            };
                            let filt = try_encode_slot_expr(&ctx, filter, step)?;
                            let filt_bool = filt.to_bool()?;
                            slot_disjuncts.push(smt::bool_and(&[active, &filt_bool]));
                        }
                    }
                }
                if slot_disjuncts.is_empty() {
                    return Ok(smt::bool_const(false));
                }
                let refs: Vec<&Bool> = slot_disjuncts.iter().collect();
                conditions.push(smt::bool_or(&refs));
            }
            IRAction::LetCrossCall { .. } | IRAction::Match { .. } => {
                return Err(
                    "macro-step let/match is not yet supported in step-enabled checks".to_owned(),
                );
            }
            IRAction::Create {
                entity: ent_name, ..
            } => {
                let n_slots = pool.slots_for(ent_name);
                let mut slot_disjuncts = Vec::new();
                for slot in 0..n_slots {
                    if let Some(SmtValue::Bool(active)) = pool.active_at(ent_name, slot, step) {
                        slot_disjuncts.push(smt::bool_not(active));
                    }
                }
                if slot_disjuncts.is_empty() {
                    return Ok(smt::bool_const(false));
                }
                let refs: Vec<&Bool> = slot_disjuncts.iter().collect();
                conditions.push(smt::bool_or(&refs));
            }
            IRAction::Apply {
                target,
                transition,
                args,
                refs: apply_refs,
            } => {
                let resolved_entity = entities.iter().find(|e| e.name == *target).or_else(|| {
                    let from_param = event.params.iter().find_map(|p| {
                        if p.name == *target {
                            if let IRType::Entity { name } = &p.ty {
                                return Some(name.as_str());
                            }
                        }
                        None
                    });
                    if let Some(entity_name) = from_param {
                        return entities.iter().find(|e| e.name == entity_name);
                    }
                    let matches: Vec<_> = entities
                        .iter()
                        .filter(|e| e.transitions.iter().any(|t| t.name == *transition))
                        .collect();
                    if matches.len() == 1 {
                        Some(matches[0])
                    } else {
                        None
                    }
                });
                let Some(ent) = resolved_entity else {
                    continue;
                };
                let Some(trans) = ent.transitions.iter().find(|t| t.name == *transition) else {
                    continue;
                };

                let target_param_eq: Option<&SmtValue> = if event
                    .params
                    .iter()
                    .any(|p| p.name == *target && matches!(p.ty, IRType::Entity { .. }))
                {
                    params.get(target.as_str())
                } else {
                    None
                };

                let n_slots = pool.slots_for(&ent.name);
                let mut slot_disjuncts = Vec::new();
                for slot in 0..n_slots {
                    let mut conjuncts = Vec::new();
                    if let Some(SmtValue::Bool(active)) = pool.active_at(&ent.name, slot, step) {
                        conjuncts.push(active.clone());
                    } else {
                        continue;
                    }

                    let slot_ctx = SlotEncodeCtx {
                        pool,
                        vctx,
                        entity: &ent.name,
                        slot,
                        params: params.clone(),
                        bindings: HashMap::new(),
                        system_name: "",
                        entity_param_types: &empty_ept,
                        store_param_types: &empty_ept,
                    };
                    let action_params =
                        try_build_apply_params(&slot_ctx, trans, args, apply_refs, step)?;
                    let action_ctx = SlotEncodeCtx {
                        pool,
                        vctx,
                        entity: &ent.name,
                        slot,
                        params: action_params,
                        bindings: HashMap::new(),
                        system_name: "",
                        entity_param_types: &empty_ept,
                        store_param_types: &empty_ept,
                    };
                    let guard_val = try_encode_slot_expr(&action_ctx, &trans.guard, step)?;
                    let guard_bool = guard_val.to_bool()?;
                    conjuncts.push(guard_bool);

                    if let Some(param_val) = target_param_eq {
                        #[allow(clippy::cast_possible_wrap)]
                        let slot_val = smt::int_val(slot as i64);
                        if let Ok(eq) = smt::smt_eq(param_val, &slot_val) {
                            conjuncts.push(eq);
                        }
                    }

                    let refs: Vec<&Bool> = conjuncts.iter().collect();
                    slot_disjuncts.push(smt::bool_and(&refs));
                }
                if slot_disjuncts.is_empty() {
                    return Ok(smt::bool_const(false));
                }
                let refs: Vec<&Bool> = slot_disjuncts.iter().collect();
                conditions.push(smt::bool_or(&refs));
            }
            IRAction::ForAll { .. } => {}
            IRAction::CrossCall {
                system: sys_name,
                command: cmd_name,
                args: cross_args,
            } => {
                if depth < 5 {
                    if let Some(target_sys) = systems.iter().find(|s| s.name == *sys_name) {
                        let matching: Vec<&IRStep> = target_sys
                            .steps
                            .iter()
                            .filter(|s| s.name == *cmd_name)
                            .collect();
                        if !matching.is_empty() {
                            let empty_ept: HashMap<String, String> = HashMap::new();
                            let clause_bools: Vec<Bool> = matching
                                .iter()
                                .filter(|target_step| target_step.params.len() == cross_args.len())
                                .map(|target_step| {
                                    let arg_ctx = SlotEncodeCtx {
                                        pool,
                                        vctx,
                                        entity: "",
                                        slot: 0,
                                        params: params.clone(),
                                        bindings: HashMap::new(),
                                        system_name: "",
                                        entity_param_types: &empty_ept,
                                        store_param_types: &empty_ept,
                                    };
                                    let mut cross_params: HashMap<String, SmtValue> =
                                        HashMap::new();
                                    for (target_param, arg_expr) in
                                        target_step.params.iter().zip(cross_args.iter())
                                    {
                                        let val = try_encode_slot_expr(&arg_ctx, arg_expr, step)?;
                                        cross_params.insert(target_param.name.clone(), val);
                                    }
                                    try_encode_step_enabled_inner(
                                        pool,
                                        vctx,
                                        entities,
                                        systems,
                                        target_step,
                                        step,
                                        Some(cross_params),
                                        depth + 1,
                                    )
                                })
                                .collect::<Result<Vec<_>, _>>()?;
                            if !clause_bools.is_empty() {
                                let refs: Vec<&Bool> = clause_bools.iter().collect();
                                conditions.push(smt::bool_or(&refs));
                            }
                        }
                    }
                }
            }
            IRAction::ExprStmt { expr } => {
                let empty_spt: HashMap<String, String> = HashMap::new();
                let val = try_encode_guard_expr(pool, vctx, expr, &params, &empty_spt, step)?;
                conditions.push(val);
            }
        }
    }

    if conditions.is_empty() {
        Ok(smt::bool_const(true))
    } else {
        let refs: Vec<&Bool> = conditions.iter().collect();
        Ok(smt::bool_and(&refs))
    }
}
