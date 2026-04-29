use super::*;

pub fn fairness_constraints(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    fire: &FireTracking,
    lasso: &LassoLoop,
    assumption_set: &IRAssumptionSet,
) -> Vec<Bool> {
    try_fairness_constraints(pool, vctx, entities, systems, fire, lasso, assumption_set)
        .unwrap_or_else(|msg| panic!("{msg}"))
}

pub fn try_fairness_constraints(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    fire: &FireTracking,
    lasso: &LassoLoop,
    assumption_set: &IRAssumptionSet,
) -> Result<Vec<Bool>, String> {
    let bound = pool.bound;
    let mut constraints = Vec::new();

    // Build O(1) lookup tables for fairness membership keyed by
    // (system, event). The assumption set is normalized in so
    // an event is in at most one of weak_fair / strong_fair.
    let weak_set: HashSet<(&str, &str)> = assumption_set
        .weak_fair
        .iter()
        .map(|r| (r.system.as_str(), r.command.as_str()))
        .collect();
    let strong_set: HashSet<(&str, &str)> = assumption_set
        .strong_fair
        .iter()
        .map(|r| (r.system.as_str(), r.command.as_str()))
        .collect();
    let per_tuple_set: HashSet<(&str, &str)> = assumption_set
        .per_tuple
        .iter()
        .map(|r| (r.system.as_str(), r.command.as_str()))
        .collect();

    for system in systems {
        for event in &system.actions {
            let pair = (system.name.as_str(), event.name.as_str());
            let is_strong = strong_set.contains(&pair);
            let is_fair = is_strong || weak_set.contains(&pair);
            if !is_fair {
                continue;
            }
            let key = (system.name.clone(), event.name.clone());
            let Some(fire_vec) = fire.fire_vars.get(&key) else {
                continue;
            };

            // per-tuple fairness for parameterized events.
            // We try per-tuple first. If all params are entity-typed,
            // expand into per-tuple obligations and skip the per-event
            // obligation (per-tuple is strictly stronger). Otherwise
            // fall through to per-event.
            let per_tuple_tuples = if per_tuple_set.contains(&pair) {
                enumerate_entity_param_tuples(event, pool)
            } else {
                None
            };

            if let Some(tuples) = per_tuple_tuples {
                for tuple in &tuples {
                    for l in 0..bound {
                        let loop_ind = &lasso.loop_indicators[l];

                        // Per-tuple enabledness at each step
                        let mut enabled_per_step = Vec::new();
                        for step in l..bound {
                            let enabled = try_encode_step_enabled_with_params(
                                pool,
                                vctx,
                                entities,
                                systems,
                                event,
                                step,
                                tuple.clone(),
                            )?;
                            enabled_per_step.push(enabled);
                        }
                        let enabled_condition = if is_strong {
                            let refs: Vec<&Bool> = enabled_per_step.iter().collect();
                            smt::bool_or(&refs)
                        } else {
                            let refs: Vec<&Bool> = enabled_per_step.iter().collect();
                            smt::bool_and(&refs)
                        };

                        // Per-tuple fired: at some step, fire_e is true AND
                        // its per-step params equal this tuple. The per-step
                        // `param_<name>_<step>` Z3 vars are shared with the
                        // body encoding, so constraining them to a tuple is
                        // equivalent to "fired with these args".
                        let mut fired_per_step = Vec::new();
                        for (step, fire_at_step) in fire_vec.iter().enumerate().take(bound).skip(l)
                        {
                            let step_params = build_step_params(&event.params, step);
                            let mut param_eqs = Vec::new();
                            for (name, target) in tuple {
                                if let Some(actual) = step_params.get(name) {
                                    if let Ok(eq) = smt::smt_eq(actual, target) {
                                        param_eqs.push(eq);
                                    }
                                }
                            }
                            let params_match = if param_eqs.is_empty() {
                                smt::bool_const(true)
                            } else {
                                let refs: Vec<&Bool> = param_eqs.iter().collect();
                                smt::bool_and(&refs)
                            };
                            fired_per_step.push(smt::bool_and(&[fire_at_step, &params_match]));
                        }
                        let fire_refs: Vec<&Bool> = fired_per_step.iter().collect();
                        let fires_somewhere = smt::bool_or(&fire_refs);

                        let fairness = smt::bool_implies(&enabled_condition, &fires_somewhere);
                        constraints.push(smt::bool_implies(loop_ind, &fairness));
                    }
                }
                continue; // per-tuple subsumes per-event for this event
            }

            // Per-event encoding (default for non-parameterized events,
            // or fallback for events with non-entity params).
            for l in 0..bound {
                let loop_ind = &lasso.loop_indicators[l];

                // Collect enabledness at each loop step
                let mut enabled_per_step = Vec::new();
                for step in l..bound {
                    let enabled =
                        try_encode_step_enabled(pool, vctx, entities, systems, event, step)?;
                    enabled_per_step.push(enabled);
                }

                let enabled_condition = if is_strong {
                    // Strong fairness: enabled at SOME step (disjunction)
                    let refs: Vec<&Bool> = enabled_per_step.iter().collect();
                    smt::bool_or(&refs)
                } else {
                    // Weak fairness: enabled at EVERY step (conjunction)
                    let refs: Vec<&Bool> = enabled_per_step.iter().collect();
                    smt::bool_and(&refs)
                };

                // Fires somewhere in loop
                let fire_disj: Vec<_> = fire_vec[l..bound].to_vec();
                let fire_refs: Vec<&Bool> = fire_disj.iter().collect();
                let fires_somewhere = smt::bool_or(&fire_refs);

                // Fairness: enabled_condition → fires somewhere
                let fairness = smt::bool_implies(&enabled_condition, &fires_somewhere);
                constraints.push(smt::bool_implies(loop_ind, &fairness));
            }
        }
    }

    Ok(constraints)
}

/// Enumerate the per-tuple parameter domain for a fair event ().
///
/// Supported only when every parameter has an entity type — the slot
/// space for an entity is bounded (`pool.slots_for(name)`), so the
/// cartesian product is finite. Events with `Int`/`String`/etc. params
/// return `None`, signalling the caller to fall back to per-event
/// fairness. (Per-tuple semantics for unbounded parameter domains
/// requires k-liveness, deferred per.)
///
/// Each returned `HashMap` maps a param name to its slot-index Z3 value.
pub(super) fn enumerate_entity_param_tuples(
    event: &IRSystemAction,
    pool: &SlotPool,
) -> Option<Vec<HashMap<String, SmtValue>>> {
    // Collect (param_name, entity_name) for each entity-typed param.
    // Bail out if any param is non-entity.
    let mut entity_params: Vec<(&str, &str)> = Vec::new();
    for p in &event.params {
        match &p.ty {
            IRType::Entity { name } => entity_params.push((p.name.as_str(), name.as_str())),
            _ => return None,
        }
    }

    // Zero-param events shouldn't be in per_tuple (per ),
    // but be defensive: an empty param list means a single empty tuple.
    if entity_params.is_empty() {
        return Some(vec![HashMap::new()]);
    }

    // Cartesian product over slot indices for each entity-typed param.
    let mut tuples: Vec<HashMap<String, SmtValue>> = vec![HashMap::new()];
    for (param_name, ent_name) in &entity_params {
        let n_slots = pool.slots_for(ent_name);
        if n_slots == 0 {
            // No slots for this entity → no tuples → no per-tuple
            // obligations. Caller falls back to per-event (which will
            // also be vacuous for this event).
            return None;
        }
        let mut next_tuples = Vec::with_capacity(tuples.len() * n_slots);
        for tup in &tuples {
            for slot_idx in 0..n_slots {
                let mut new_tup = tup.clone();
                #[allow(clippy::cast_possible_wrap)]
                new_tup.insert((*param_name).to_string(), smt::int_val(slot_idx as i64));
                next_tuples.push(new_tup);
            }
        }
        tuples = next_tuples;
    }
    Some(tuples)
}
