use super::nested::try_encode_nested_op;
use super::*;

#[allow(clippy::too_many_lines, clippy::too_many_arguments)]
pub(crate) fn encode_step_inner(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    event: &IRSystemAction,
    step: usize,
    depth: usize,
    override_params: Option<HashMap<String, SmtValue>>,
) -> (Bool, HashSet<(String, usize)>) {
    try_encode_step_inner(
        pool,
        vctx,
        entities,
        all_systems,
        event,
        step,
        depth,
        override_params,
    )
    .unwrap_or_else(|msg| panic!("{msg}"))
}

#[derive(Clone)]
pub(super) struct MacroBranch {
    formula: Bool,
    touched: HashSet<(String, usize)>,
    locals: HashMap<String, SmtValue>,
    return_value: Option<SmtValue>,
}

#[allow(clippy::too_many_arguments)]
pub(super) fn contains_macro_actions(actions: &[IRAction]) -> bool {
    actions.iter().any(|action| match action {
        IRAction::LetCrossCall { .. } | IRAction::Match { .. } => true,
        IRAction::Choose { ops, .. } | IRAction::ForAll { ops, .. } => contains_macro_actions(ops),
        _ => false,
    })
}

#[allow(clippy::too_many_lines, clippy::too_many_arguments)]
pub(crate) fn try_encode_step_inner(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    event: &IRSystemAction,
    step: usize,
    depth: usize,
    override_params: Option<HashMap<String, SmtValue>>,
) -> Result<(Bool, HashSet<(String, usize)>), String> {
    if contains_macro_actions(&event.body) {
        try_encode_step_inner_macro(
            pool,
            vctx,
            entities,
            all_systems,
            event,
            step,
            depth,
            override_params,
        )
    } else {
        try_encode_step_inner_legacy(
            pool,
            vctx,
            entities,
            all_systems,
            event,
            step,
            depth,
            override_params,
        )
    }
}

#[allow(clippy::too_many_lines, clippy::too_many_arguments)]
pub(crate) fn try_encode_step_inner_legacy(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    event: &IRSystemAction,
    step: usize,
    depth: usize,
    override_params: Option<HashMap<String, SmtValue>>,
) -> Result<(Bool, HashSet<(String, usize)>), String> {
    assert!(
        depth <= 10,
        "CrossCall recursion depth exceeded (depth {depth}) — possible cyclic cross-system calls"
    );
    assert!(
        step < pool.bound,
        "step {step} out of bounds for bound {}",
        pool.bound
    );

    let mut conjuncts = Vec::new();
    // Track which entity types have ALL their slots handled internally
    // (Choose/ForAll/bare Apply do their own per-slot framing).
    let mut touched: HashSet<(String, usize)> = HashSet::new();
    // Counter for unique chain instance IDs (prevents aliasing when
    // multiple Choose blocks reuse the same var name in one step).
    let mut chain_id: usize = 0;

    // Build event parameter Z3 variables once per step, share across all contexts.
    // If override_params is provided (e.g., from CrossCall), use those instead
    // so that the caller's argument values are wired into this event.
    let step_params = override_params.unwrap_or_else(|| build_step_params(&event.params, step));

    // build entity param type info for the guard/body encoders.
    // Maps entity-typed param names to their entity type so that
    // Field(Var("item"), "status") can resolve at any step by looking up
    // the param's entity slot in the pool.
    let entity_param_types: HashMap<String, String> = event
        .params
        .iter()
        .filter_map(|p| match &p.ty {
            IRType::Entity { name } => Some((p.name.clone(), name.clone())),
            _ => None,
        })
        .collect();

    // derive the owning system for system field and store parameter resolution.
    let owning_system = all_systems.iter().find(|s| {
        s.actions
            .iter()
            .any(|st| std::ptr::eq(st, event) || st.name == event.name)
    });
    let owning_system_name: String = owning_system.map(|s| s.name.clone()).unwrap_or_default();
    let store_param_types: HashMap<String, String> = owning_system
        .map(|s| {
            s.store_params
                .iter()
                .map(|p| (p.name.clone(), p.entity_type.clone()))
                .collect()
        })
        .unwrap_or_default();

    // Event guard encoding with support for quantifiers over entity slots.
    // For guards that are trivially `true`, skip encoding.
    // For non-trivial guards, use `encode_guard_expr` which handles:
    // - Quantifiers (`exists o: Order |...`, `forall o: Order |...`) by
    // expanding over active slots
    // - Boolean connectives by recursing
    // - Param-only or literal guards via `encode_slot_expr` with event params
    if !matches!(
        &event.guard,
        IRExpr::Lit {
            value: LitVal::Bool { value: true },
            ..
        }
    ) {
        let guard = if owning_system_name.is_empty() {
            try_encode_guard_expr(
                pool,
                vctx,
                &event.guard,
                &step_params,
                &store_param_types,
                step,
            )
        } else {
            try_encode_guard_expr_for_system(
                pool,
                vctx,
                &event.guard,
                &step_params,
                step,
                &owning_system_name,
                &entity_param_types,
                &store_param_types,
            )
        }?;
        conjuncts.push(guard);
    }

    // Map Choose-bound variable names to their entity types for Apply target resolution.
    let mut var_to_entity: HashMap<String, String> = HashMap::new();

    // Populate var_to_entity from event params with entity types
    for p in &event.params {
        if let IRType::Entity { name } = &p.ty {
            var_to_entity.insert(p.name.clone(), name.clone());
        }
    }

    // Accumulated Choose variable params: after a `choose r: Reservation...`
    // is encoded, fresh Z3 variables for `r`'s fields are created and
    // constrained to match the chosen slot. Subsequent actions can then
    // reference `r.product_id` via these shared variables without requiring
    // a cross-product of slot assignments.
    let mut choose_var_params: HashMap<String, SmtValue> = HashMap::new();

    for action in &event.body {
        match action {
            // Per-slot framing in Choose.
            // Each disjunct includes framing for all OTHER slots of the same entity,
            // so non-selected slots cannot take arbitrary values.
            //
            // After encoding, creates shared Z3 variables for the Choose-bound
            // variable's entity fields, constrained to the chosen slot's values.
            // This enables subsequent Choose blocks to reference cross-entity
            // fields (e.g., `r.product_id`) efficiently.
            IRAction::Choose {
                var,
                entity: ent_name,
                filter,
                ops,
            } => {
                // Track var → entity mapping for Apply target resolution
                var_to_entity.insert(var.clone(), ent_name.clone());

                let n_slots = pool.slots_for(ent_name);
                let entity_ir = entities.iter().find(|e| e.name == *ent_name);
                let mut slot_options = Vec::new();

                // Merge event params with accumulated Choose variable params
                let mut merged_params = step_params.clone();
                merged_params.extend(choose_var_params.clone());
                let mut nested_touched: HashSet<(String, usize)> = HashSet::new();

                for slot in 0..n_slots {
                    let ctx = SlotEncodeCtx {
                        pool,
                        vctx,
                        entity: ent_name,
                        slot,
                        params: merged_params.clone(),
                        bindings: HashMap::new(),
                        system_name: "",
                        entity_param_types: &entity_param_types,
                        store_param_types: &store_param_types,
                    };

                    let mut slot_conjuncts = Vec::new();

                    // Must be active
                    if let Some(SmtValue::Bool(active)) = pool.active_at(ent_name, slot, step) {
                        slot_conjuncts.push(active.clone());
                    }

                    // Filter must hold
                    let filt = try_encode_slot_expr(&ctx, filter, step)?;
                    slot_conjuncts.push(filt.to_bool()?);

                    // Apply nested ops — detect multi-apply chains and use
                    // intermediate variables for sequential composition.
                    if let Some(ent) = entity_ir {
                        // Collect Apply ops targeting the Choose-bound entity
                        let same_entity_applies: Vec<_> = ops
                            .iter()
                            .filter_map(|op| {
                                if let IRAction::Apply {
                                    target,
                                    transition,
                                    args,
                                    refs: apply_refs,
                                } = op
                                {
                                    if target == var {
                                        return Some((transition, args, apply_refs));
                                    }
                                }
                                None
                            })
                            .collect();

                        if same_entity_applies.len() <= 1 {
                            // Single Apply — use standard encoding
                            for op in ops {
                                match op {
                                    IRAction::Apply {
                                        transition,
                                        args,
                                        refs: apply_refs,
                                        ..
                                    } => {
                                        if let Some(trans) =
                                            ent.transitions.iter().find(|t| t.name == *transition)
                                        {
                                            let action_params = try_build_apply_params(
                                                &ctx, trans, args, apply_refs, step,
                                            )?;
                                            let action_formula = try_encode_action(
                                                pool,
                                                vctx,
                                                ent,
                                                trans,
                                                slot,
                                                step,
                                                &action_params,
                                            )?;
                                            slot_conjuncts.push(action_formula);
                                        }
                                    }
                                    _ => {
                                        if let Some(ent) = entity_ir {
                                            let (nested_f, nested_t) = try_encode_nested_op(
                                                pool,
                                                vctx,
                                                entities,
                                                all_systems,
                                                op,
                                                var,
                                                ent_name,
                                                ent,
                                                slot,
                                                step,
                                                &merged_params,
                                                depth,
                                                &[],
                                            )?;
                                            slot_conjuncts.extend(nested_f);
                                            nested_touched.extend(nested_t);
                                        }
                                    }
                                }
                            }
                        } else {
                            // Multi-apply chain — create intermediate variables.
                            // Chain: step_k → inter_0 → inter_1 →... → step_k+1
                            let n_applies = same_entity_applies.len();

                            // Build variable maps for each stage
                            // Stage 0 reads: step k fields
                            // Stage i writes: intermediate_i (or step k+1 if last)
                            let read_step_k: HashMap<String, SmtValue> = ent
                                .fields
                                .iter()
                                .filter_map(|f| {
                                    pool.field_at(ent_name, slot, &f.name, step)
                                        .map(|v| (f.name.clone(), v.clone()))
                                })
                                .collect();

                            let write_step_k1: HashMap<String, SmtValue> = ent
                                .fields
                                .iter()
                                .filter_map(|f| {
                                    pool.field_at(ent_name, slot, &f.name, step + 1)
                                        .map(|v| (f.name.clone(), v.clone()))
                                })
                                .collect();

                            // Create N-1 intermediate variable maps
                            let intermediates: Vec<HashMap<String, SmtValue>> = (0..n_applies - 1)
                                .map(|i| {
                                    ent.fields
                                        .iter()
                                        .map(|f| {
 // Fully scoped: entity, slot, field, step,
 // chain instance ID, and stage index.
 // Prevents aliasing across steps, events,
 // and multiple Choose blocks with same var name.
                                            let name = format!(
                                                "{}_s{}_{}_t{step}_ch{chain_id}_inter{i}",
                                                ent_name, slot, f.name
                                            );
                                            let var = match &f.ty {
                                                IRType::Bool => smt::bool_var(&name),
                                                IRType::Real | IRType::Float => {
                                                    smt::real_var(&name)
                                                }
                                                IRType::Map { .. } | IRType::Set { .. } => {
                                                    smt::array_var(&name, &f.ty)
                                                        .expect("internal: array sort expected for Map/Set field")
                                                }
                                                IRType::Seq { element } => SmtValue::Dynamic(
                                                    smt::dynamic_const(
                                                        &name,
                                                        &smt::seq_sort(element).sort(),
                                                    ),
                                                ),
                                                _ => smt::int_var(&name),
                                            };
                                            (f.name.clone(), var)
                                        })
                                        .collect()
                                })
                                .collect();

                            for (i, (transition, args, apply_refs)) in
                                same_entity_applies.iter().enumerate()
                            {
                                let Some(trans) =
                                    ent.transitions.iter().find(|t| t.name == **transition)
                                else {
                                    continue;
                                };

                                // Read from: step k (first) or intermediate_{i-1}
                                let read_from = if i == 0 {
                                    &read_step_k
                                } else {
                                    &intermediates[i - 1]
                                };

                                // Build action params from the intermediate state.
                                // First Apply uses standard build_apply_params (step k).
                                // Later Applies evaluate args AND refs from intermediate vars.
                                let action_params = if i == 0 {
                                    try_build_apply_params(&ctx, trans, args, apply_refs, step)?
                                } else {
                                    let mut params = HashMap::new();
                                    // Positional params
                                    for (pi, param) in trans.params.iter().enumerate() {
                                        if let Some(arg_expr) = args.get(pi) {
                                            let val = try_eval_expr_with_vars(
                                                arg_expr,
                                                ent,
                                                read_from,
                                                vctx,
                                                &ctx.params,
                                            )?;
                                            params.insert(param.name.clone(), val);
                                        }
                                    }
                                    // Refs: resolve from intermediate vars
                                    for (ri, tref) in trans.refs.iter().enumerate() {
                                        if let Some(ref_name) = apply_refs.get(ri) {
                                            if let Some(val) = read_from.get(ref_name) {
                                                params.insert(tref.name.clone(), val.clone());
                                            }
                                        }
                                    }
                                    params
                                };

                                // Write to: intermediate_i (middle) or step k+1 (last)
                                let write_to = if i == n_applies - 1 {
                                    &write_step_k1
                                } else {
                                    &intermediates[i]
                                };

                                let formula = try_encode_action_with_vars(
                                    ent,
                                    trans,
                                    slot,
                                    read_from,
                                    write_to,
                                    vctx,
                                    &action_params,
                                )?;
                                slot_conjuncts.push(formula);
                            }

                            // Active flag: must be active at step k AND stays active at step k+1
                            // (matches single-apply semantics in encode_action)
                            if let (
                                Some(SmtValue::Bool(act_curr)),
                                Some(SmtValue::Bool(act_next)),
                            ) = (
                                pool.active_at(ent_name, slot, step),
                                pool.active_at(ent_name, slot, step + 1),
                            ) {
                                slot_conjuncts.push(act_curr.clone());
                                slot_conjuncts.push(act_next.clone());
                            }

                            // Handle non-Apply ops in the Choose (Create, CrossCall, etc.)
                            for op in ops {
                                match op {
                                    IRAction::Apply { target, .. } if target == var => {
                                        // Already handled above
                                    }
                                    IRAction::Apply { target, .. } => {
                                        // Apply targeting a different variable inside a Choose
                                        // is malformed IR — the Apply target should match
                                        // the Choose-bound variable.
                                        panic!(
                                            "Apply target {target} does not match Choose var {var} \
                                             — cross-target Apply in Choose is not supported"
                                        );
                                    }
                                    _ => {
                                        if let Some(ent) = entity_ir {
                                            let (nested_f, nested_t) = try_encode_nested_op(
                                                pool,
                                                vctx,
                                                entities,
                                                all_systems,
                                                op,
                                                var,
                                                ent_name,
                                                ent,
                                                slot,
                                                step,
                                                &merged_params,
                                                depth,
                                                &[],
                                            )?;
                                            slot_conjuncts.extend(nested_f);
                                            nested_touched.extend(nested_t);
                                        }
                                    }
                                }
                            }
                            chain_id += 1; // unique ID per multi-apply chain
                        }
                    }

                    // Constrain shared Choose variable fields to match this slot.
                    // For each field of the chosen entity, assert that the shared
                    // variable equals the slot's field at this step.
                    if let Some(ent) = entity_ir {
                        for field in &ent.fields {
                            let shared_name = format!("choose_{var}_{}_t{step}", field.name);
                            let shared_var = match &field.ty {
                                IRType::Bool => smt::bool_var(&shared_name),
                                IRType::Real | IRType::Float => smt::real_var(&shared_name),
                                _ => smt::int_var(&shared_name),
                            };
                            if let Some(slot_val) = pool.field_at(ent_name, slot, &field.name, step)
                            {
                                match (&shared_var, slot_val) {
                                    (SmtValue::Int(s), SmtValue::Int(f)) => {
                                        slot_conjuncts.push(smt::int_eq(s, f));
                                    }
                                    (SmtValue::Bool(s), SmtValue::Bool(f)) => {
                                        slot_conjuncts.push(smt::bool_eq(s, f));
                                    }
                                    (SmtValue::Real(s), SmtValue::Real(f)) => {
                                        slot_conjuncts.push(smt::real_eq(s, f));
                                    }
                                    _ => {}
                                }
                            }
                        }
                    }

                    // Frame all OTHER slots of this entity within the disjunct.
                    if let Some(ent) = entity_ir {
                        let slot_frame = frame_entity_slots_except(pool, ent, slot, step);
                        slot_conjuncts.extend(slot_frame);
                    }

                    let refs: Vec<&Bool> = slot_conjuncts.iter().collect();
                    if !refs.is_empty() {
                        slot_options.push(smt::bool_and(&refs));
                    }
                }

                // At least one slot must satisfy Choose
                let refs: Vec<&Bool> = slot_options.iter().collect();
                if !refs.is_empty() {
                    conjuncts.push(smt::bool_or(&refs));
                    for slot in 0..n_slots {
                        touched.insert((ent_name.clone(), slot));
                    }
                }
                // Mark entities touched by nested ops (Create, CrossCall, etc.)
                touched.extend(nested_touched);

                // Register shared Choose variable fields as params for
                // subsequent actions to resolve `var.field` references.
                if let Some(ent) = entity_ir {
                    for field in &ent.fields {
                        let shared_name = format!("choose_{var}_{}_t{step}", field.name);
                        let shared_var = match &field.ty {
                            IRType::Bool => smt::bool_var(&shared_name),
                            IRType::Real | IRType::Float => smt::real_var(&shared_name),
                            _ => smt::int_var(&shared_name),
                        };
                        // Register as `var.field` for Field resolution
                        choose_var_params
                            .insert(format!("{var}.{}", field.name), shared_var.clone());
                        // Also register as bare `field` if the var itself is referenced
                        // (some filters use bare field names from Choose context)
                    }
                }
            }

            // Bare Apply (top-level in event body).
            // Target may be a variable name (e.g., "o") or entity type name.
            // IR lowering stores the variable name from the source expression.
            // We try entity type first; if not found, it's a variable reference
            // that should have been scoped by an enclosing Choose (which is the
            // normal pattern — bare Apply without Choose is unusual).
            IRAction::Apply {
                target,
                transition,
                args,
                refs: apply_refs,
            } => {
                // Resolve target: entity type name → Choose-bound variable → transition-based fallback
                let resolved_entity = entities.iter().find(|e| e.name == *target).or_else(|| {
                    // Target is a variable name — check Choose bindings first
                    if let Some(entity_name) = var_to_entity.get(target.as_str()) {
                        return entities.iter().find(|e| e.name == *entity_name);
                    }
                    // Last resort: find entity with this transition (only if unambiguous)
                    let matches: Vec<_> = entities
                        .iter()
                        .filter(|e| e.transitions.iter().any(|t| t.name == *transition))
                        .collect();
                    if matches.len() == 1 {
                        Some(matches[0])
                    } else {
                        None // ambiguous or not found — skip
                    }
                });
                let Some(ent) = resolved_entity else {
                    panic!(
                        "Apply target resolution failed: target={target:?}, transition={transition:?} \
                         — could not resolve entity (var_to_entity keys: {:?}, entity names: {:?})",
                        var_to_entity.keys().collect::<Vec<_>>(),
                        entities.iter().map(|e| &e.name).collect::<Vec<_>>()
                    );
                };
                let Some(trans) = ent.transitions.iter().find(|t| t.name == *transition) else {
                    panic!(
                        "Apply transition not found: entity={}, transition={transition:?} \
                         — available transitions: {:?}",
                        ent.name,
                        ent.transitions.iter().map(|t| &t.name).collect::<Vec<_>>()
                    );
                };
                // Use resolved entity name, not the target variable name
                let ent_name = &ent.name;
                let n_slots = pool.slots_for(ent_name);

                // If `target` is an entity-typed event parameter, the per-step
                // `param_<target>_<step>` Z3 var represents the slot index the
                // event was called with. We tie each slot disjunct to that
                // value so the SAT solver picks a single slot per fire AND
                // so per-tuple fairness () can read the param var
                // to identify which tuple actually fired. Without this tie,
                // the param var is unconstrained relative to the body's slot
                // pick — `param_<target>_<step> == k` would not actually mean
                // "the event acted on slot k", and per-tuple obligations
                // would be decoupled from real slot mutations.
                let target_param_eq: Option<&SmtValue> = if event
                    .params
                    .iter()
                    .any(|p| p.name == *target && matches!(p.ty, IRType::Entity { .. }))
                {
                    step_params.get(target.as_str())
                } else {
                    None
                };

                let mut slot_options = Vec::new();
                for slot in 0..n_slots {
                    let apply_ctx = SlotEncodeCtx {
                        pool,
                        vctx,
                        entity: ent_name,
                        slot,
                        params: {
                            let mut p = step_params.clone();
                            p.extend(choose_var_params.clone());
                            p
                        },
                        bindings: HashMap::new(),
                        system_name: "",
                        entity_param_types: &entity_param_types,
                        store_param_types: &store_param_types,
                    };
                    let action_params =
                        try_build_apply_params(&apply_ctx, trans, args, apply_refs, step)?;
                    let mut slot_conjuncts = Vec::new();
                    let formula =
                        try_encode_action(pool, vctx, ent, trans, slot, step, &action_params)?;
                    slot_conjuncts.push(formula);
                    // Tie the param var to this slot index when applicable.
                    if let Some(param_val) = target_param_eq {
                        #[allow(clippy::cast_possible_wrap)]
                        let slot_val = smt::int_val(slot as i64);
                        if let Ok(eq) = smt::smt_eq(param_val, &slot_val) {
                            slot_conjuncts.push(eq);
                        }
                    }
                    // Frame all OTHER slots of this entity
                    let slot_frame = frame_entity_slots_except(pool, ent, slot, step);
                    slot_conjuncts.extend(slot_frame);
                    let refs: Vec<&Bool> = slot_conjuncts.iter().collect();
                    slot_options.push(smt::bool_and(&refs));
                }
                let refs: Vec<&Bool> = slot_options.iter().collect();
                if !refs.is_empty() {
                    conjuncts.push(smt::bool_or(&refs));
                }
                // Mark all slots as touched — per-slot framing handled above
                for slot in 0..n_slots {
                    touched.insert((ent_name.clone(), slot));
                }
            }

            IRAction::Create {
                entity: ent_name,
                fields,
            } => {
                let entity_ir = entities.iter().find(|e| e.name == *ent_name);
                let create_fields: Vec<(String, IRExpr)> = fields
                    .iter()
                    .map(|f| (f.name.clone(), f.value.clone()))
                    .collect();
                let create = try_encode_create(
                    pool,
                    vctx,
                    ent_name,
                    entity_ir,
                    &create_fields,
                    step,
                    &step_params,
                )?;
                conjuncts.push(create);
                // Mark all slots of this entity as potentially touched
                let n_slots = pool.slots_for(ent_name);
                for slot in 0..n_slots {
                    touched.insert((ent_name.clone(), slot));
                }
            }

            // Issue 2: ForAll encoding — conjunction over all active slots.
            // For each slot:
            // (active AND ops AND active_next) OR (!active AND frame_this_slot)
            // This ensures inactive slots are explicitly framed (not left unconstrained).
            IRAction::ForAll {
                var,
                entity: ent_name,
                ops,
            } => {
                let n_slots = pool.slots_for(ent_name);
                let entity_ir = entities.iter().find(|e| e.name == *ent_name);
                let mut nested_touched: HashSet<(String, usize)> = HashSet::new();
                let forall_base_params = {
                    let mut p = step_params.clone();
                    p.extend(choose_var_params.clone());
                    p
                };

                for slot in 0..n_slots {
                    let ctx = SlotEncodeCtx {
                        pool,
                        vctx,
                        entity: ent_name,
                        slot,
                        params: forall_base_params.clone(),
                        bindings: HashMap::new(),
                        system_name: "",
                        entity_param_types: &entity_param_types,
                        store_param_types: &store_param_types,
                    };

                    let mut op_conjuncts = Vec::new();

                    for op in ops {
                        match op {
                            IRAction::Apply {
                                target: _,
                                transition,
                                args,
                                refs: apply_refs,
                            } => {
                                if let Some(ent) = entity_ir {
                                    if let Some(trans) =
                                        ent.transitions.iter().find(|t| t.name == *transition)
                                    {
                                        let action_params = try_build_apply_params(
                                            &ctx, trans, args, apply_refs, step,
                                        )?;
                                        let action_formula = try_encode_action(
                                            pool,
                                            vctx,
                                            ent,
                                            trans,
                                            slot,
                                            step,
                                            &action_params,
                                        )?;
                                        op_conjuncts.push(action_formula);
                                    }
                                }
                            }
                            _ => {
                                if let Some(ent) = entity_ir {
                                    let (nested_f, nested_t) = try_encode_nested_op(
                                        pool,
                                        vctx,
                                        entities,
                                        all_systems,
                                        op,
                                        var,
                                        ent_name,
                                        ent,
                                        slot,
                                        step,
                                        &forall_base_params,
                                        depth,
                                        &[],
                                    )?;
                                    op_conjuncts.extend(nested_f);
                                    nested_touched.extend(nested_t);
                                }
                            }
                        }
                    }

                    // For each slot: (active AND ops) OR (!active AND frame)
                    if let Some(SmtValue::Bool(active)) = pool.active_at(ent_name, slot, step) {
                        // Active branch: active AND ops
                        let active_branch = if op_conjuncts.is_empty() {
                            active.clone()
                        } else {
                            let mut active_parts = vec![active.clone()];
                            active_parts.extend(op_conjuncts);
                            let refs: Vec<&Bool> = active_parts.iter().collect();
                            smt::bool_and(&refs)
                        };

                        // Inactive branch: !active AND frame (all fields + active flag unchanged)
                        let mut frame_parts = vec![smt::bool_not(active)];
                        // Active flag unchanged
                        if let Some(SmtValue::Bool(act_next)) =
                            pool.active_at(ent_name, slot, step + 1)
                        {
                            frame_parts.push(smt::bool_eq(act_next, active));
                        }
                        // All fields unchanged
                        if let Some(ent) = entity_ir {
                            for field in &ent.fields {
                                if let (Some(curr), Some(next)) = (
                                    pool.field_at(ent_name, slot, &field.name, step),
                                    pool.field_at(ent_name, slot, &field.name, step + 1),
                                ) {
                                    frame_parts.push(
                                        smt::smt_eq(curr, next)
                                            .expect("internal: forall frame smt_eq"),
                                    );
                                }
                            }
                        }

                        let frame_refs: Vec<&Bool> = frame_parts.iter().collect();
                        let inactive_branch = smt::bool_and(&frame_refs);

                        conjuncts.push(smt::bool_or(&[&active_branch, &inactive_branch]));
                    }

                    touched.insert((ent_name.clone(), slot));
                }
                // Mark entities touched by nested ops (Create, CrossCall, etc.)
                touched.extend(nested_touched);
            }

            IRAction::CrossCall {
                system: target_system,
                command: command_name,
                args: cross_args,
            } => {
                // Find the target system and ALL matching steps, then encode
                // a disjunction with per-branch framing. Multi-clause commands
                // have multiple steps with the same name but different guards;
                // each branch may touch different slots, so each disjunct must
                // frame the slots in the union that it didn't individually touch.
                if let Some(target_sys) = all_systems.iter().find(|s| s.name == *target_system) {
                    let matching_steps: Vec<_> = target_sys
                        .actions
                        .iter()
                        .filter(|s| s.name == *command_name)
                        .collect();
                    // Collect (formula, touched) pairs per branch
                    let mut branch_results: Vec<(Bool, HashSet<(String, usize)>)> = Vec::new();
                    for target_step in &matching_steps {
                        if target_step.params.len() != cross_args.len() {
                            // Arity mismatches are validated in scene checking,
                            // but keep harness encoding total so verify checks
                            // never panic during recursive CrossCall expansion.
                            branch_results.push((smt::bool_const(false), HashSet::new()));
                            continue;
                        }
                        // Build override params: evaluate each CrossCall arg in
                        // the current step's context (using step_params) and
                        // bind it to the corresponding target step param name.
                        let mut cross_params: HashMap<String, SmtValue> = HashMap::new();
                        let arg_ctx = SlotEncodeCtx {
                            pool,
                            vctx,
                            entity: "",
                            slot: 0,
                            params: {
                                let mut p = step_params.clone();
                                p.extend(choose_var_params.clone());
                                p
                            },
                            bindings: HashMap::new(),
                            system_name: "",
                            entity_param_types: &entity_param_types,
                            store_param_types: &store_param_types,
                        };
                        for (target_param, arg_expr) in
                            target_step.params.iter().zip(cross_args.iter())
                        {
                            let val = try_encode_slot_expr(&arg_ctx, arg_expr, step)?;
                            cross_params.insert(target_param.name.clone(), val);
                        }

                        // Recursively encode the target step with wired params.
                        // The callee does NOT apply its own global frame, so
                        // per-branch framing is handled below.
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
                        conjuncts.push(smt::bool_or(&refs));
                        touched.extend(all_touched);
                    }
                }
            }

            IRAction::ExprStmt { expr } => {
                // Encode the expression and assert it as a boolean constraint
                let expr_ctx = SlotEncodeCtx {
                    pool,
                    vctx,
                    entity: "",
                    slot: 0,
                    params: {
                        let mut p = step_params.clone();
                        p.extend(choose_var_params.clone());
                        p
                    },
                    bindings: HashMap::new(),
                    system_name: &owning_system_name,
                    entity_param_types: &entity_param_types,
                    store_param_types: &store_param_types,
                };
                let val = try_encode_slot_expr(&expr_ctx, expr, step)?;
                conjuncts.push(val.to_bool()?);
            }
            IRAction::LetCrossCall { .. } | IRAction::Match { .. } => {
                return Err("internal: macro-step actions reached legacy step encoder".to_owned());
            }
        }
    }

    // Return action formula + touched set. Global framing is applied by the
    // top-level caller, NOT here — this allows CrossCall to compose without
    // conflicting frame constraints.
    let formula = {
        let refs: Vec<&Bool> = conjuncts.iter().collect();
        if refs.is_empty() {
            smt::bool_const(true)
        } else {
            smt::bool_and(&refs)
        }
    };
    Ok((formula, touched))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn try_encode_step_inner_macro(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    event: &IRSystemAction,
    step: usize,
    depth: usize,
    override_params: Option<HashMap<String, SmtValue>>,
) -> Result<(Bool, HashSet<(String, usize)>), String> {
    let branches = try_encode_step_branches_dispatch(
        pool,
        vctx,
        entities,
        all_systems,
        event,
        step,
        depth,
        override_params,
    )?;
    let all_touched: HashSet<(String, usize)> = branches
        .iter()
        .flat_map(|b| b.touched.iter().cloned())
        .collect();
    let disjuncts: Vec<Bool> = branches
        .into_iter()
        .map(|branch| {
            let untouched_by_branch: HashSet<(String, usize)> =
                all_touched.difference(&branch.touched).cloned().collect();
            if untouched_by_branch.is_empty() {
                branch.formula
            } else {
                let frame = frame_specific_slots(pool, entities, &untouched_by_branch, step);
                let mut parts = vec![branch.formula];
                parts.extend(frame);
                let refs: Vec<&Bool> = parts.iter().collect();
                smt::bool_and(&refs)
            }
        })
        .collect();
    let refs: Vec<&Bool> = disjuncts.iter().collect();
    Ok((
        if refs.is_empty() {
            smt::bool_const(false)
        } else {
            smt::bool_or(&refs)
        },
        all_touched,
    ))
}

#[allow(clippy::too_many_lines, clippy::too_many_arguments)]
pub(super) fn try_encode_step_branches_dispatch(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    event: &IRSystemAction,
    step: usize,
    depth: usize,
    override_params: Option<HashMap<String, SmtValue>>,
) -> Result<Vec<MacroBranch>, String> {
    if !contains_macro_actions(&event.body) {
        let step_params = override_params.unwrap_or_else(|| build_step_params(&event.params, step));
        let (formula, touched) = try_encode_step_inner_legacy(
            pool,
            vctx,
            entities,
            all_systems,
            event,
            step,
            depth,
            Some(step_params.clone()),
        )?;
        let (owning_system_name, entity_param_types, store_param_types) =
            step_scope_metadata(all_systems, event);
        let mut branch = MacroBranch {
            formula,
            touched,
            locals: HashMap::new(),
            return_value: None,
        };
        if let Some(ret) = &event.return_expr {
            let ctx = SlotEncodeCtx {
                pool,
                vctx,
                entity: "",
                slot: 0,
                params: step_params,
                bindings: HashMap::new(),
                system_name: &owning_system_name,
                entity_param_types: &entity_param_types,
                store_param_types: &store_param_types,
            };
            let (value, constraints) = try_encode_macro_value_expr(&ctx, ret, step)?;
            if !constraints.is_empty() {
                let mut parts = vec![branch.formula.clone()];
                parts.extend(constraints);
                let refs: Vec<&Bool> = parts.iter().collect();
                branch.formula = smt::bool_and(&refs);
            }
            branch.return_value = Some(value);
        }
        return Ok(vec![branch]);
    }

    let step_params = override_params.unwrap_or_else(|| build_step_params(&event.params, step));
    let (owning_system_name, entity_param_types, store_param_types) =
        step_scope_metadata(all_systems, event);

    let mut initial_parts = Vec::new();
    if !matches!(
        &event.guard,
        IRExpr::Lit {
            value: LitVal::Bool { value: true },
            ..
        }
    ) {
        initial_parts.push(try_encode_guard_expr_for_system(
            pool,
            vctx,
            &event.guard,
            &step_params,
            step,
            &owning_system_name,
            &entity_param_types,
            &store_param_types,
        )?);
    }
    let initial_formula = if initial_parts.is_empty() {
        smt::bool_const(true)
    } else {
        let refs: Vec<&Bool> = initial_parts.iter().collect();
        smt::bool_and(&refs)
    };

    let mut branches = vec![MacroBranch {
        formula: initial_formula,
        touched: HashSet::new(),
        locals: HashMap::new(),
        return_value: None,
    }];
    let var_to_entity: HashMap<String, String> = event
        .params
        .iter()
        .filter_map(|p| match &p.ty {
            IRType::Entity { name } => Some((p.name.clone(), name.clone())),
            _ => None,
        })
        .collect();

    for action in &event.body {
        branches = try_apply_macro_action(
            pool,
            vctx,
            entities,
            all_systems,
            action,
            step,
            depth,
            &step_params,
            &owning_system_name,
            &entity_param_types,
            &store_param_types,
            &var_to_entity,
            branches,
        )?;
    }

    if let Some(ret) = &event.return_expr {
        for branch in &mut branches {
            let ctx = SlotEncodeCtx {
                pool,
                vctx,
                entity: "",
                slot: 0,
                params: merged_branch_params(&step_params, &branch.locals),
                bindings: HashMap::new(),
                system_name: &owning_system_name,
                entity_param_types: &entity_param_types,
                store_param_types: &store_param_types,
            };
            let (value, constraints) = try_encode_macro_value_expr(&ctx, ret, step)?;
            if !constraints.is_empty() {
                let mut parts = vec![branch.formula.clone()];
                parts.extend(constraints);
                let refs: Vec<&Bool> = parts.iter().collect();
                branch.formula = smt::bool_and(&refs);
            }
            branch.return_value = Some(value);
        }
    }

    Ok(branches)
}

pub(super) fn step_scope_metadata(
    all_systems: &[IRSystem],
    event: &IRSystemAction,
) -> (String, HashMap<String, String>, HashMap<String, String>) {
    let owning_system = all_systems.iter().find(|s| {
        s.actions
            .iter()
            .any(|st| std::ptr::eq(st, event) || st.name == event.name)
    });
    let owning_system_name = owning_system.map(|s| s.name.clone()).unwrap_or_default();
    let entity_param_types: HashMap<String, String> = event
        .params
        .iter()
        .filter_map(|p| match &p.ty {
            IRType::Entity { name } => Some((p.name.clone(), name.clone())),
            _ => None,
        })
        .collect();
    let store_param_types: HashMap<String, String> = owning_system
        .map(|s| {
            s.store_params
                .iter()
                .map(|p| (p.name.clone(), p.entity_type.clone()))
                .collect()
        })
        .unwrap_or_default();
    (owning_system_name, entity_param_types, store_param_types)
}

pub(super) fn merged_branch_params(
    step_params: &HashMap<String, SmtValue>,
    locals: &HashMap<String, SmtValue>,
) -> HashMap<String, SmtValue> {
    let mut params = step_params.clone();
    params.extend(locals.clone());
    params
}

pub(super) fn fresh_smt_value(prefix: &str, ty: &IRType) -> SmtValue {
    match ty {
        IRType::Bool => smt::bool_var(prefix),
        IRType::Real | IRType::Float => smt::real_var(prefix),
        IRType::Int | IRType::Identity => smt::int_var(prefix),
        _ => walkers::dynamic_to_smt_value(smt::dynamic_fresh(prefix, &smt::ir_type_to_sort(ty))),
    }
}

pub(super) fn try_encode_macro_value_expr(
    ctx: &SlotEncodeCtx<'_>,
    expr: &IRExpr,
    step: usize,
) -> Result<(SmtValue, Vec<Bool>), String> {
    match expr {
        IRExpr::Choose {
            var, predicate, ty, ..
        } => {
            let fresh = fresh_smt_value(&format!("choose_{var}_t{step}"), ty);
            let mut constraints = Vec::new();
            if let Some(pred) = predicate {
                let mut pred_params = ctx.params.clone();
                pred_params.insert(var.clone(), fresh.clone());
                let pred_ctx = SlotEncodeCtx {
                    pool: ctx.pool,
                    vctx: ctx.vctx,
                    entity: ctx.entity,
                    slot: ctx.slot,
                    params: pred_params,
                    bindings: ctx.bindings.clone(),
                    system_name: ctx.system_name,
                    entity_param_types: ctx.entity_param_types,
                    store_param_types: ctx.store_param_types,
                };
                constraints.push(try_encode_slot_expr(&pred_ctx, pred, step)?.to_bool()?);
            }
            Ok((fresh, constraints))
        }
        IRExpr::Let { bindings, body, .. } => {
            let mut params = ctx.params.clone();
            let mut constraints = Vec::new();
            for binding in bindings {
                let bind_ctx = SlotEncodeCtx {
                    pool: ctx.pool,
                    vctx: ctx.vctx,
                    entity: ctx.entity,
                    slot: ctx.slot,
                    params: params.clone(),
                    bindings: ctx.bindings.clone(),
                    system_name: ctx.system_name,
                    entity_param_types: ctx.entity_param_types,
                    store_param_types: ctx.store_param_types,
                };
                let (value, cs) = try_encode_macro_value_expr(&bind_ctx, &binding.expr, step)?;
                constraints.extend(cs);
                params.insert(binding.name.clone(), value);
            }
            let body_ctx = SlotEncodeCtx {
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
            let (value, mut body_constraints) = try_encode_macro_value_expr(&body_ctx, body, step)?;
            constraints.append(&mut body_constraints);
            Ok((value, constraints))
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond_bool = try_encode_slot_expr(ctx, cond, step)?.to_bool()?;
            let (then_val, then_constraints) = try_encode_macro_value_expr(ctx, then_body, step)?;
            let else_expr = else_body
                .as_ref()
                .ok_or_else(|| "macro-step return if/else requires an else branch".to_owned())?;
            let (else_val, else_constraints) = try_encode_macro_value_expr(ctx, else_expr, step)?;
            let result = smt::smt_ite(&cond_bool, &then_val, &else_val);
            let mut constraints = Vec::new();
            for c in then_constraints {
                constraints.push(smt::bool_implies(&cond_bool, &c));
            }
            let not_cond = smt::bool_not(&cond_bool);
            for c in else_constraints {
                constraints.push(smt::bool_implies(&not_cond, &c));
            }
            Ok((result, constraints))
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            let (scrut, mut constraints) = try_encode_macro_value_expr(ctx, scrutinee, step)?;
            let mut arm_conds = Vec::new();
            let mut result: Option<SmtValue> = None;
            for arm in arms.iter().rev() {
                let mut arm_env = ctx.params.clone();
                encode::bind_pattern_vars(&arm.pattern, &scrut, &mut arm_env, ctx.vctx)?;
                let arm_ctx = SlotEncodeCtx {
                    pool: ctx.pool,
                    vctx: ctx.vctx,
                    entity: ctx.entity,
                    slot: ctx.slot,
                    params: arm_env,
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
                arm_conds.push(arm_cond.clone());
                let (arm_val, arm_constraints) =
                    try_encode_macro_value_expr(&arm_ctx, &arm.body, step)?;
                if let Some(current) = result.take() {
                    result = Some(smt::smt_ite(&arm_cond, &arm_val, &current));
                } else {
                    result = Some(arm_val);
                }
                for c in arm_constraints {
                    constraints.push(smt::bool_implies(&arm_cond, &c));
                }
            }
            if arm_conds.is_empty() {
                return Err("macro-step return match has no arms".to_owned());
            }
            let cond_refs: Vec<&Bool> = arm_conds.iter().collect();
            constraints.push(smt::bool_or(&cond_refs));
            Ok((result.expect("non-empty arms"), constraints))
        }
        _ => Ok((try_encode_slot_expr(ctx, expr, step)?, Vec::new())),
    }
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
pub(super) fn try_apply_macro_action(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    action: &IRAction,
    step: usize,
    depth: usize,
    step_params: &HashMap<String, SmtValue>,
    owning_system_name: &str,
    entity_param_types: &HashMap<String, String>,
    store_param_types: &HashMap<String, String>,
    var_to_entity: &HashMap<String, String>,
    branches: Vec<MacroBranch>,
) -> Result<Vec<MacroBranch>, String> {
    let mut next = Vec::new();
    for branch in branches {
        let params = merged_branch_params(step_params, &branch.locals);
        match action {
            IRAction::Choose {
                var,
                entity,
                filter,
                ops,
            } => {
                let n_slots = pool.slots_for(entity);
                let entity_ir = entities.iter().find(|e| e.name == *entity);
                let mut choose_branches = Vec::new();
                for slot in 0..n_slots {
                    let ctx = SlotEncodeCtx {
                        pool,
                        vctx,
                        entity,
                        slot,
                        params: params.clone(),
                        bindings: HashMap::new(),
                        system_name: owning_system_name,
                        entity_param_types,
                        store_param_types,
                    };
                    let mut conjuncts = vec![branch.formula.clone()];
                    if let Some(SmtValue::Bool(active)) = pool.active_at(entity, slot, step) {
                        conjuncts.push(active.clone());
                    }
                    conjuncts.push(try_encode_slot_expr(&ctx, filter, step)?.to_bool()?);

                    let mut touched = branch.touched.clone();
                    let mut slot_has_action = false;
                    let mut nested_touched = HashSet::new();

                    if let Some(ent_ir) = entity_ir {
                        for op in ops {
                            match op {
                                IRAction::Apply {
                                    target,
                                    transition,
                                    args,
                                    refs: apply_refs,
                                } if target == var => {
                                    if let Some(trans) =
                                        ent_ir.transitions.iter().find(|t| t.name == *transition)
                                    {
                                        let action_params = try_build_apply_params(
                                            &ctx, trans, args, apply_refs, step,
                                        )?;
                                        conjuncts.push(try_encode_action(
                                            pool,
                                            vctx,
                                            ent_ir,
                                            trans,
                                            slot,
                                            step,
                                            &action_params,
                                        )?);
                                        slot_has_action = true;
                                        touched.insert((entity.clone(), slot));
                                    }
                                }
                                _ => {
                                    let (nested_f, nested_slots) = try_encode_nested_op(
                                        pool,
                                        vctx,
                                        entities,
                                        all_systems,
                                        op,
                                        var,
                                        entity,
                                        ent_ir,
                                        slot,
                                        step,
                                        &params,
                                        depth,
                                        &[],
                                    )?;
                                    conjuncts.extend(nested_f);
                                    nested_touched.extend(nested_slots);
                                }
                            }
                        }

                        if !slot_has_action {
                            for field in &ent_ir.fields {
                                if let (Some(curr), Some(next_val)) = (
                                    pool.field_at(entity, slot, &field.name, step),
                                    pool.field_at(entity, slot, &field.name, step + 1),
                                ) {
                                    conjuncts.push(smt::smt_eq(curr, next_val)?);
                                }
                            }
                            if let (
                                Some(SmtValue::Bool(act_curr)),
                                Some(SmtValue::Bool(act_next)),
                            ) = (
                                pool.active_at(entity, slot, step),
                                pool.active_at(entity, slot, step + 1),
                            ) {
                                conjuncts.push(smt::bool_eq(act_next, act_curr));
                            }
                        }

                        conjuncts.extend(frame_entity_slots_except(pool, ent_ir, slot, step));
                    }

                    touched.extend(nested_touched);
                    for s in 0..n_slots {
                        touched.insert((entity.clone(), s));
                    }
                    let refs: Vec<&Bool> = conjuncts.iter().collect();
                    choose_branches.push(MacroBranch {
                        formula: smt::bool_and(&refs),
                        touched,
                        locals: branch.locals.clone(),
                        return_value: branch.return_value.clone(),
                    });
                }
                next.extend(choose_branches);
                continue;
            }
            IRAction::ForAll { .. } => {
                return Err(
                    "macro-step commands do not yet support for blocks in command bodies"
                        .to_owned(),
                );
            }
            IRAction::Create { entity, fields } => {
                let entity_ir = entities.iter().find(|e| e.name == *entity);
                let create_fields: Vec<(String, IRExpr)> = fields
                    .iter()
                    .map(|f| (f.name.clone(), f.value.clone()))
                    .collect();
                let create = try_encode_create(
                    pool,
                    vctx,
                    entity,
                    entity_ir,
                    &create_fields,
                    step,
                    &params,
                )?;
                let parts = [branch.formula.clone(), create];
                let refs: Vec<&Bool> = parts.iter().collect();
                let mut touched = branch.touched.clone();
                for slot in 0..pool.slots_for(entity) {
                    touched.insert((entity.clone(), slot));
                }
                next.push(MacroBranch {
                    formula: smt::bool_and(&refs),
                    touched,
                    locals: branch.locals.clone(),
                    return_value: branch.return_value.clone(),
                });
            }
            IRAction::ExprStmt { expr } => {
                let expr_ctx = SlotEncodeCtx {
                    pool,
                    vctx,
                    entity: "",
                    slot: 0,
                    params,
                    bindings: HashMap::new(),
                    system_name: owning_system_name,
                    entity_param_types,
                    store_param_types,
                };
                let expr_bool = try_encode_slot_expr(&expr_ctx, expr, step)?.to_bool()?;
                let parts = [branch.formula.clone(), expr_bool];
                let refs: Vec<&Bool> = parts.iter().collect();
                next.push(MacroBranch {
                    formula: smt::bool_and(&refs),
                    touched: branch.touched.clone(),
                    locals: branch.locals.clone(),
                    return_value: branch.return_value.clone(),
                });
            }
            IRAction::Apply {
                target,
                transition,
                args,
                refs: apply_refs,
            } => {
                let resolved_entity = entities.iter().find(|e| e.name == *target).or_else(|| {
                    if let Some(entity_name) = var_to_entity.get(target.as_str()) {
                        return entities.iter().find(|e| e.name == *entity_name);
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
                    return Err(format!(
                        "Apply target resolution failed in macro-step: target={target}, transition={transition}"
                    ));
                };
                let Some(trans) = ent.transitions.iter().find(|t| t.name == *transition) else {
                    return Err(format!(
                        "Apply transition not found in macro-step: entity={}, transition={transition}",
                        ent.name
                    ));
                };
                let ent_name = &ent.name;
                let target_param_eq: Option<&SmtValue> =
                    if event_param_is_entity(target, entity_param_types) {
                        params.get(target.as_str())
                    } else {
                        None
                    };
                for slot in 0..pool.slots_for(ent_name) {
                    let apply_ctx = SlotEncodeCtx {
                        pool,
                        vctx,
                        entity: ent_name,
                        slot,
                        params: params.clone(),
                        bindings: HashMap::new(),
                        system_name: owning_system_name,
                        entity_param_types,
                        store_param_types,
                    };
                    let action_params =
                        try_build_apply_params(&apply_ctx, trans, args, apply_refs, step)?;
                    let mut parts = vec![
                        branch.formula.clone(),
                        try_encode_action(pool, vctx, ent, trans, slot, step, &action_params)?,
                    ];
                    if let Some(param_val) = target_param_eq {
                        let slot_val = smt::int_val(slot as i64);
                        parts.push(smt::smt_eq(param_val, &slot_val)?);
                    }
                    let refs: Vec<&Bool> = parts.iter().collect();
                    let mut touched = branch.touched.clone();
                    for s in 0..pool.slots_for(ent_name) {
                        touched.insert((ent_name.clone(), s));
                    }
                    next.push(MacroBranch {
                        formula: smt::bool_and(&refs),
                        touched,
                        locals: branch.locals.clone(),
                        return_value: branch.return_value.clone(),
                    });
                }
            }
            IRAction::CrossCall {
                system,
                command,
                args,
            } => {
                let call_branches = try_encode_macro_call(
                    pool,
                    vctx,
                    entities,
                    all_systems,
                    system,
                    command,
                    args,
                    step,
                    depth,
                    &params,
                    owning_system_name,
                    entity_param_types,
                    store_param_types,
                )?;
                for call_branch in call_branches {
                    let mut touched = branch.touched.clone();
                    touched.extend(call_branch.touched);
                    let refs: Vec<&Bool> = [&branch.formula, &call_branch.formula]
                        .into_iter()
                        .collect();
                    next.push(MacroBranch {
                        formula: smt::bool_and(&refs),
                        touched,
                        locals: branch.locals.clone(),
                        return_value: branch.return_value.clone(),
                    });
                }
            }
            IRAction::LetCrossCall {
                name,
                system,
                command,
                args,
            } => {
                let call_branches = try_encode_macro_call(
                    pool,
                    vctx,
                    entities,
                    all_systems,
                    system,
                    command,
                    args,
                    step,
                    depth,
                    &params,
                    owning_system_name,
                    entity_param_types,
                    store_param_types,
                )?;
                for call_branch in call_branches {
                    let Some(value) = call_branch.return_value.clone() else {
                        return Err(format!(
                            "macro-step binding requires `{system}::{command}` to return a value"
                        ));
                    };
                    let mut touched = branch.touched.clone();
                    touched.extend(call_branch.touched);
                    let mut locals = branch.locals.clone();
                    locals.insert(name.clone(), value);
                    let refs: Vec<&Bool> = [&branch.formula, &call_branch.formula]
                        .into_iter()
                        .collect();
                    next.push(MacroBranch {
                        formula: smt::bool_and(&refs),
                        touched,
                        locals,
                        return_value: branch.return_value.clone(),
                    });
                }
            }
            IRAction::Match { scrutinee, arms } => {
                let call_branches = match scrutinee {
                    crate::ir::types::IRActionMatchScrutinee::Var { name } => vec![MacroBranch {
                        formula: smt::bool_const(true),
                        touched: HashSet::new(),
                        locals: {
                            let mut m = HashMap::new();
                            let Some(val) = branch.locals.get(name).cloned() else {
                                return Err(format!(
                                    "macro-step match references unknown local `{name}`"
                                ));
                            };
                            m.insert(name.clone(), val);
                            m
                        },
                        return_value: branch.locals.get(name).cloned(),
                    }],
                    crate::ir::types::IRActionMatchScrutinee::CrossCall {
                        system,
                        command,
                        args,
                    } => try_encode_macro_call(
                        pool,
                        vctx,
                        entities,
                        all_systems,
                        system,
                        command,
                        args,
                        step,
                        depth,
                        &params,
                        owning_system_name,
                        entity_param_types,
                        store_param_types,
                    )?,
                };
                for call_branch in call_branches {
                    let Some(scrut) = call_branch.return_value.clone() else {
                        return Err(
                            "macro-step match requires a returned command outcome".to_owned()
                        );
                    };
                    for arm in arms {
                        let mut arm_cond = encode::encode_pattern_cond(
                            &scrut,
                            &arm.pattern,
                            &HashMap::new(),
                            vctx,
                        )?;
                        let mut arm_locals = branch.locals.clone();
                        encode::bind_pattern_vars(&arm.pattern, &scrut, &mut arm_locals, vctx)?;
                        if let Some(guard) = &arm.guard {
                            let guard_ctx = SlotEncodeCtx {
                                pool,
                                vctx,
                                entity: "",
                                slot: 0,
                                params: merged_branch_params(&params, &arm_locals),
                                bindings: HashMap::new(),
                                system_name: owning_system_name,
                                entity_param_types,
                                store_param_types,
                            };
                            let guard_bool =
                                try_encode_slot_expr(&guard_ctx, guard, step)?.to_bool()?;
                            arm_cond = smt::bool_and(&[&arm_cond, &guard_bool]);
                        }
                        let arm_start = MacroBranch {
                            formula: {
                                let refs: Vec<&Bool> =
                                    [&branch.formula, &call_branch.formula, &arm_cond]
                                        .into_iter()
                                        .collect();
                                smt::bool_and(&refs)
                            },
                            touched: {
                                let mut touched = branch.touched.clone();
                                touched.extend(call_branch.touched.clone());
                                touched
                            },
                            locals: arm_locals,
                            return_value: branch.return_value.clone(),
                        };
                        let mut arm_branches = vec![arm_start];
                        for nested in &arm.body {
                            arm_branches = try_apply_macro_action(
                                pool,
                                vctx,
                                entities,
                                all_systems,
                                nested,
                                step,
                                depth,
                                step_params,
                                owning_system_name,
                                entity_param_types,
                                store_param_types,
                                var_to_entity,
                                arm_branches,
                            )?;
                        }
                        next.extend(arm_branches);
                    }
                }
            }
        }
    }
    Ok(next)
}

pub(super) fn event_param_is_entity(
    target: &str,
    entity_param_types: &HashMap<String, String>,
) -> bool {
    entity_param_types.contains_key(target)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn try_encode_macro_call(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    target_system: &str,
    command_name: &str,
    cross_args: &[IRExpr],
    step: usize,
    depth: usize,
    params: &HashMap<String, SmtValue>,
    owning_system_name: &str,
    entity_param_types: &HashMap<String, String>,
    store_param_types: &HashMap<String, String>,
) -> Result<Vec<MacroBranch>, String> {
    let Some(target_sys) = all_systems.iter().find(|s| s.name == *target_system) else {
        return Ok(vec![]);
    };
    let matching_steps: Vec<_> = target_sys
        .actions
        .iter()
        .filter(|s| s.name == *command_name)
        .collect();
    let arg_ctx = SlotEncodeCtx {
        pool,
        vctx,
        entity: "",
        slot: 0,
        params: params.clone(),
        bindings: HashMap::new(),
        system_name: owning_system_name,
        entity_param_types,
        store_param_types,
    };
    let mut branches = Vec::new();
    for target_step in &matching_steps {
        if target_step.params.len() != cross_args.len() {
            continue;
        }
        let mut cross_params = HashMap::new();
        for (target_param, arg_expr) in target_step.params.iter().zip(cross_args.iter()) {
            let val = try_encode_slot_expr(&arg_ctx, arg_expr, step)?;
            cross_params.insert(target_param.name.clone(), val);
        }
        branches.extend(try_encode_step_branches_dispatch(
            pool,
            vctx,
            entities,
            all_systems,
            target_step,
            step,
            depth + 1,
            Some(cross_params),
        )?);
    }
    Ok(branches)
}
