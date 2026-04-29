use super::*;

#[allow(clippy::too_many_arguments)]
#[allow(dead_code)]
pub(in crate::verify::harness::step) fn encode_nested_op(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    op: &IRAction,
    bound_var: &str,
    bound_ent_name: &str,
    bound_entity_ir: &IREntity,
    bound_slot: usize,
    step: usize,
    base_params: &HashMap<String, SmtValue>,
    depth: usize,
    // Chain of outer bound variables from enclosing Choose/ForAll scopes.
    // Each entry is (var_name, entity_name, entity_ir, slot).
    // Enables Apply targeting an outer variable to resolve to its specific slot
    // instead of a disjunction over all slots.
    outer_bindings: &[(&str, &str, &IREntity, usize)],
) -> (Vec<Bool>, HashSet<(String, usize)>) {
    try_encode_nested_op(
        pool,
        vctx,
        entities,
        all_systems,
        op,
        bound_var,
        bound_ent_name,
        bound_entity_ir,
        bound_slot,
        step,
        base_params,
        depth,
        outer_bindings,
    )
    .unwrap_or_else(|msg| panic!("{msg}"))
}

#[allow(clippy::too_many_arguments)]
#[allow(clippy::type_complexity)]
pub(in crate::verify::harness::step) fn try_encode_nested_op(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    op: &IRAction,
    bound_var: &str,
    bound_ent_name: &str,
    bound_entity_ir: &IREntity,
    bound_slot: usize,
    step: usize,
    base_params: &HashMap<String, SmtValue>,
    depth: usize,
    outer_bindings: &[(&str, &str, &IREntity, usize)],
) -> Result<(Vec<Bool>, HashSet<(String, usize)>), String> {
    let mut formulas = Vec::new();
    let mut additional_touched: HashSet<(String, usize)> = HashSet::new();

    // Build params that include the bound variable's field mappings for this slot.
    // This allows nested expressions to resolve `bound_var.field` references.
    let mut slot_params = base_params.clone();
    for field in &bound_entity_ir.fields {
        if let Some(val) = pool.field_at(bound_ent_name, bound_slot, &field.name, step) {
            slot_params.insert(format!("{bound_var}.{}", field.name), val.clone());
        }
    }

    let empty_ept: HashMap<String, String> = HashMap::new();

    match op {
        IRAction::Create {
            entity: create_ent,
            fields,
        } => {
            let create_entity_ir = entities.iter().find(|e| e.name == *create_ent);
            let create_fields: Vec<(String, IRExpr)> = fields
                .iter()
                .map(|f| (f.name.clone(), f.value.clone()))
                .collect();
            let create_formula = try_encode_create(
                pool,
                vctx,
                create_ent,
                create_entity_ir,
                &create_fields,
                step,
                &slot_params,
            )?;
            formulas.push(create_formula);
            let n_slots = pool.slots_for(create_ent);
            for s in 0..n_slots {
                additional_touched.insert((create_ent.clone(), s));
            }
        }

        IRAction::CrossCall {
            system: target_system,
            command: command_name,
            args: cross_args,
        } => {
            if let Some(target_sys) = all_systems.iter().find(|s| s.name == *target_system) {
                let matching_steps: Vec<_> = target_sys
                    .actions
                    .iter()
                    .filter(|s| s.name == *command_name)
                    .collect();
                if matching_steps.is_empty() {
                    // No matching steps — should have been caught by validation.
                } else {
                    // Collect (formula, touched) pairs per branch, then apply
                    // per-branch framing so each disjunct frames slots in the
                    // union that it didn't individually touch.
                    let mut branch_results: Vec<(Bool, HashSet<(String, usize)>)> = Vec::new();
                    for target_step in &matching_steps {
                        if target_step.params.len() == cross_args.len() {
                            let arg_ctx = SlotEncodeCtx {
                                pool,
                                vctx,
                                entity: bound_ent_name,
                                slot: bound_slot,
                                params: slot_params.clone(),
                                bindings: HashMap::new(),
                                system_name: "",
                                entity_param_types: &empty_ept,
                                store_param_types: &empty_ept,
                            };
                            let mut cross_params: HashMap<String, SmtValue> = HashMap::new();
                            for (target_param, arg_expr) in
                                target_step.params.iter().zip(cross_args.iter())
                            {
                                let val = try_encode_slot_expr(&arg_ctx, arg_expr, step)?;
                                cross_params.insert(target_param.name.clone(), val);
                            }
                            let (cross_formula, cross_touched) = try_encode_step_inner(
                                pool,
                                vctx,
                                entities,
                                all_systems,
                                target_step,
                                step,
                                depth + 1,
                                Some(cross_params),
                            )?;
                            branch_results.push((cross_formula, cross_touched));
                        } else {
                            branch_results.push((smt::bool_const(false), HashSet::new()));
                        }
                    }
                    if !branch_results.is_empty() {
                        // Compute the union of all touched sets
                        let all_touched: HashSet<(String, usize)> = branch_results
                            .iter()
                            .flat_map(|(_, t)| t.iter().cloned())
                            .collect();
                        // Apply per-branch framing: each branch frames slots it didn't touch
                        let framed_disjuncts: Vec<Bool> = branch_results
                            .into_iter()
                            .map(|(formula, branch_touched)| {
                                let untouched_by_branch: HashSet<(String, usize)> =
                                    all_touched.difference(&branch_touched).cloned().collect();
                                if untouched_by_branch.is_empty() {
                                    formula
                                } else {
                                    let frame = frame_specific_slots(
                                        pool,
                                        entities,
                                        &untouched_by_branch,
                                        step,
                                    );
                                    let mut parts = vec![formula];
                                    parts.extend(frame);
                                    let refs: Vec<&Bool> = parts.iter().collect();
                                    smt::bool_and(&refs)
                                }
                            })
                            .collect();
                        let refs: Vec<&Bool> = framed_disjuncts.iter().collect();
                        formulas.push(smt::bool_or(&refs));
                        additional_touched.extend(all_touched);
                    }
                }
            }
        }

        IRAction::LetCrossCall { .. } | IRAction::Match { .. } => {
            return Err(
                "macro-step let/match is not yet supported inside choose/for blocks".to_owned(),
            );
        }

        IRAction::ExprStmt { expr } => {
            let expr_ctx = SlotEncodeCtx {
                pool,
                vctx,
                entity: bound_ent_name,
                slot: bound_slot,
                params: slot_params,
                bindings: HashMap::new(),
                system_name: "",
                entity_param_types: &empty_ept,
                store_param_types: &empty_ept,
            };
            let val = try_encode_slot_expr(&expr_ctx, expr, step)?;
            formulas.push(val.to_bool()?);
        }

        IRAction::Choose {
            var: inner_var,
            entity: inner_ent,
            filter,
            ops: inner_ops,
        } => {
            let inner_n_slots = pool.slots_for(inner_ent);
            let inner_entity_ir = entities.iter().find(|e| e.name == *inner_ent);
            // Augment outer bindings with the current bound variable so that
            // deeper nested ops can resolve Apply targets to our specific slot.
            let mut inner_bindings = outer_bindings.to_vec();
            inner_bindings.push((bound_var, bound_ent_name, bound_entity_ir, bound_slot));
            let mut inner_slot_options = Vec::new();

            for inner_slot in 0..inner_n_slots {
                let inner_ctx = SlotEncodeCtx {
                    pool,
                    vctx,
                    entity: inner_ent,
                    slot: inner_slot,
                    params: slot_params.clone(),
                    bindings: HashMap::new(),
                    system_name: "",
                    entity_param_types: &empty_ept,
                    store_param_types: &empty_ept,
                };
                let mut inner_conjuncts = Vec::new();

                // Must be active
                if let Some(SmtValue::Bool(active)) = pool.active_at(inner_ent, inner_slot, step) {
                    inner_conjuncts.push(active.clone());
                }
                // Filter must hold
                let filt = try_encode_slot_expr(&inner_ctx, filter, step)?;
                inner_conjuncts.push(filt.to_bool()?);

                // Encode inner ops
                if let Some(inner_ent_ir) = inner_entity_ir {
                    let mut inner_slot_has_action = false;
                    for inner_op in inner_ops {
                        match inner_op {
                            IRAction::Apply {
                                target,
                                transition,
                                args,
                                refs: apply_refs,
                            } if target == inner_var => {
                                // Target matches inner bound var — encode on inner entity
                                if let Some(trans) = inner_ent_ir
                                    .transitions
                                    .iter()
                                    .find(|t| t.name == *transition)
                                {
                                    let action_params = try_build_apply_params(
                                        &inner_ctx, trans, args, apply_refs, step,
                                    )?;
                                    let action_formula = try_encode_action(
                                        pool,
                                        vctx,
                                        inner_ent_ir,
                                        trans,
                                        inner_slot,
                                        step,
                                        &action_params,
                                    )?;
                                    inner_conjuncts.push(action_formula);
                                    inner_slot_has_action = true;
                                }
                            }
                            _ => {
                                // Cross-entity Apply or other nested action —
                                // delegate to encode_nested_op which resolves the
                                // target to the correct entity and slot.
                                let (nested_f, nested_t) = try_encode_nested_op(
                                    pool,
                                    vctx,
                                    entities,
                                    all_systems,
                                    inner_op,
                                    inner_var,
                                    inner_ent,
                                    inner_ent_ir,
                                    inner_slot,
                                    step,
                                    &slot_params,
                                    depth,
                                    &inner_bindings,
                                )?;
                                inner_conjuncts.extend(nested_f);
                                additional_touched.extend(nested_t);
                            }
                        }
                    }

                    // If no op directly acted on the inner chosen slot, frame it
                    // so the solver cannot mutate it arbitrarily.
                    if !inner_slot_has_action {
                        for field in &inner_ent_ir.fields {
                            if let (Some(curr), Some(next)) = (
                                pool.field_at(inner_ent, inner_slot, &field.name, step),
                                pool.field_at(inner_ent, inner_slot, &field.name, step + 1),
                            ) {
                                inner_conjuncts.push(smt::smt_eq(curr, next)?);
                            }
                        }
                        if let (Some(SmtValue::Bool(act_curr)), Some(SmtValue::Bool(act_next))) = (
                            pool.active_at(inner_ent, inner_slot, step),
                            pool.active_at(inner_ent, inner_slot, step + 1),
                        ) {
                            inner_conjuncts.push(smt::bool_eq(act_next, act_curr));
                        }
                    }

                    // Frame other slots of inner entity
                    let slot_frame =
                        frame_entity_slots_except(pool, inner_ent_ir, inner_slot, step);
                    inner_conjuncts.extend(slot_frame);
                }

                let refs: Vec<&Bool> = inner_conjuncts.iter().collect();
                if !refs.is_empty() {
                    inner_slot_options.push(smt::bool_and(&refs));
                }
            }

            let refs: Vec<&Bool> = inner_slot_options.iter().collect();
            if !refs.is_empty() {
                formulas.push(smt::bool_or(&refs));
            }
            for s in 0..inner_n_slots {
                additional_touched.insert((inner_ent.clone(), s));
            }
        }

        IRAction::ForAll {
            var: inner_var,
            entity: inner_ent,
            ops: inner_ops,
        } => {
            let inner_n_slots = pool.slots_for(inner_ent);
            let inner_entity_ir = entities.iter().find(|e| e.name == *inner_ent);
            // Augment outer bindings with current bound variable
            let mut inner_bindings = outer_bindings.to_vec();
            inner_bindings.push((bound_var, bound_ent_name, bound_entity_ir, bound_slot));

            for inner_slot in 0..inner_n_slots {
                let inner_ctx = SlotEncodeCtx {
                    pool,
                    vctx,
                    entity: inner_ent,
                    slot: inner_slot,
                    params: slot_params.clone(),
                    bindings: HashMap::new(),
                    system_name: "",
                    entity_param_types: &empty_ept,
                    store_param_types: &empty_ept,
                };
                let mut op_conjuncts = Vec::new();

                if let Some(inner_ent_ir) = inner_entity_ir {
                    let mut inner_slot_has_action = false;
                    for inner_op in inner_ops {
                        match inner_op {
                            IRAction::Apply {
                                target,
                                transition,
                                args,
                                refs: apply_refs,
                            } if target == inner_var => {
                                // Target matches inner bound var — encode on inner entity
                                if let Some(trans) = inner_ent_ir
                                    .transitions
                                    .iter()
                                    .find(|t| t.name == *transition)
                                {
                                    let action_params = try_build_apply_params(
                                        &inner_ctx, trans, args, apply_refs, step,
                                    )?;
                                    let action_formula = try_encode_action(
                                        pool,
                                        vctx,
                                        inner_ent_ir,
                                        trans,
                                        inner_slot,
                                        step,
                                        &action_params,
                                    )?;
                                    op_conjuncts.push(action_formula);
                                    inner_slot_has_action = true;
                                }
                            }
                            _ => {
                                // Cross-entity Apply or other nested action
                                let (nested_f, nested_t) = try_encode_nested_op(
                                    pool,
                                    vctx,
                                    entities,
                                    all_systems,
                                    inner_op,
                                    inner_var,
                                    inner_ent,
                                    inner_ent_ir,
                                    inner_slot,
                                    step,
                                    &slot_params,
                                    depth,
                                    &inner_bindings,
                                )?;
                                op_conjuncts.extend(nested_f);
                                additional_touched.extend(nested_t);
                            }
                        }
                    }

                    // If no op directly acted on this slot, frame it so the
                    // solver cannot mutate the active entity's fields.
                    if !inner_slot_has_action {
                        for field in &inner_ent_ir.fields {
                            if let (Some(curr), Some(next)) = (
                                pool.field_at(inner_ent, inner_slot, &field.name, step),
                                pool.field_at(inner_ent, inner_slot, &field.name, step + 1),
                            ) {
                                op_conjuncts.push(
                                    smt::smt_eq(curr, next)
                                        .expect("internal: nested forall slot frame smt_eq"),
                                );
                            }
                        }
                        if let (Some(SmtValue::Bool(act_curr)), Some(SmtValue::Bool(act_next))) = (
                            pool.active_at(inner_ent, inner_slot, step),
                            pool.active_at(inner_ent, inner_slot, step + 1),
                        ) {
                            op_conjuncts.push(smt::bool_eq(act_next, act_curr));
                        }
                    }
                }

                // For each slot: (active AND ops) OR (!active AND frame)
                if let Some(SmtValue::Bool(active)) = pool.active_at(inner_ent, inner_slot, step) {
                    let active_branch = if op_conjuncts.is_empty() {
                        active.clone()
                    } else {
                        let mut active_parts = vec![active.clone()];
                        active_parts.extend(op_conjuncts);
                        let refs: Vec<&Bool> = active_parts.iter().collect();
                        smt::bool_and(&refs)
                    };

                    let mut frame_parts = vec![smt::bool_not(active)];
                    if let Some(SmtValue::Bool(act_next)) =
                        pool.active_at(inner_ent, inner_slot, step + 1)
                    {
                        frame_parts.push(smt::bool_eq(act_next, active));
                    }
                    if let Some(inner_ent_ir) = inner_entity_ir {
                        for field in &inner_ent_ir.fields {
                            if let (Some(curr), Some(next)) = (
                                pool.field_at(inner_ent, inner_slot, &field.name, step),
                                pool.field_at(inner_ent, inner_slot, &field.name, step + 1),
                            ) {
                                frame_parts.push(
                                    smt::smt_eq(curr, next)
                                        .expect("internal: nested forall frame smt_eq"),
                                );
                            }
                        }
                    }

                    let frame_refs: Vec<&Bool> = frame_parts.iter().collect();
                    let inactive_branch = smt::bool_and(&frame_refs);
                    formulas.push(smt::bool_or(&[&active_branch, &inactive_branch]));
                }

                additional_touched.insert((inner_ent.clone(), inner_slot));
            }
        }

        IRAction::Apply {
            target,
            transition,
            args,
            refs: apply_refs,
        } => {
            // Resolve which entity and slot the Apply targets.
            // Priority: immediate bound var → outer bound var chain → entity name/transition fallback
            let resolved_binding: Option<(&str, &IREntity, usize)> = if target == bound_var {
                Some((bound_ent_name, bound_entity_ir, bound_slot))
            } else {
                outer_bindings
                    .iter()
                    .find(|(var, _, _, _)| *var == target.as_str())
                    .map(|(_, ent_name, ent_ir, slot)| (*ent_name, *ent_ir, *slot))
            };

            if let Some((ent_name, ent_ir, slot)) = resolved_binding {
                // Target is a bound variable (immediate or outer) — encode on
                // its specific slot, preserving the chosen slot identity.
                if let Some(trans) = ent_ir.transitions.iter().find(|t| t.name == *transition) {
                    let ctx = SlotEncodeCtx {
                        pool,
                        vctx,
                        entity: ent_name,
                        slot,
                        params: slot_params,
                        bindings: HashMap::new(),
                        system_name: "",
                        entity_param_types: &empty_ept,
                        store_param_types: &empty_ept,
                    };
                    let action_params =
                        try_build_apply_params(&ctx, trans, args, apply_refs, step)?;
                    let action_formula =
                        try_encode_action(pool, vctx, ent_ir, trans, slot, step, &action_params)?;
                    formulas.push(action_formula);
                    additional_touched.insert((ent_name.to_string(), slot));
                }
            } else {
                // Apply targeting an unresolved variable — resolve by entity
                // name or transition name, encode with slot disjunction.
                let resolved = entities.iter().find(|e| e.name == *target).or_else(|| {
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
                if let Some(ent) = resolved {
                    let ent_name = &ent.name;
                    if let Some(trans) = ent.transitions.iter().find(|t| t.name == *transition) {
                        let n_slots = pool.slots_for(ent_name);
                        let mut slot_options = Vec::new();
                        for s in 0..n_slots {
                            let ctx = SlotEncodeCtx {
                                pool,
                                vctx,
                                entity: ent_name,
                                slot: s,
                                params: slot_params.clone(),
                                bindings: HashMap::new(),
                                system_name: "",
                                entity_param_types: &empty_ept,
                                store_param_types: &empty_ept,
                            };
                            let action_params =
                                try_build_apply_params(&ctx, trans, args, apply_refs, step)?;
                            let mut slot_conjuncts = Vec::new();
                            let formula =
                                try_encode_action(pool, vctx, ent, trans, s, step, &action_params)?;
                            slot_conjuncts.push(formula);
                            let slot_frame = frame_entity_slots_except(pool, ent, s, step);
                            slot_conjuncts.extend(slot_frame);
                            let refs: Vec<&Bool> = slot_conjuncts.iter().collect();
                            slot_options.push(smt::bool_and(&refs));
                        }
                        let refs: Vec<&Bool> = slot_options.iter().collect();
                        if !refs.is_empty() {
                            formulas.push(smt::bool_or(&refs));
                        }
                        for s in 0..n_slots {
                            additional_touched.insert((ent_name.clone(), s));
                        }
                    }
                }
            }
        }
    }

    Ok((formulas, additional_touched))
}
