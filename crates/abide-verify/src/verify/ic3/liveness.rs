use super::*;

/// Try IC3/PDR on a liveness property via the liveness-to-safety reduction.
///
/// Adds monitor columns (pending, saved state, justice counters) to the CHC
/// State relation and encodes the monitor transition alongside entity transitions.
/// The error condition is `accepting = true` (loop detected with pending obligation).
///
/// `trigger` and `response` are the P and Q from `always (P implies eventually Q)`.
/// `fair_events` lists (system, event) pairs with weak fairness.
/// `entity_var` / `entity_name` are set for entity-quantified patterns.
#[allow(clippy::implicit_hasher)]
#[allow(clippy::too_many_arguments)]
pub fn try_ic3_liveness(
    ir: &IRProgram,
    vctx: &VerifyContext,
    system_names: &[String],
    trigger: &IRExpr,
    response: &IRExpr,
    entity_var: Option<&str>,
    entity_name_for_binding: Option<&str>,
    fair_events: &[(String, String)],
    slots_per_entity: &HashMap<String, usize>,
    // If true, the trigger fires once and never re-triggers (eventuality).
    is_oneshot: bool,
    // For quantified liveness: restrict trigger/response to this specific slot
    // instead of OR-ing over all slots (which gives existential, not universal).
    target_slot: Option<usize>,
    timeout_ms: u64,
) -> Ic3Result {
    // Expand scope to include CrossCall-reachable systems
    let mut all_system_names: Vec<String> = system_names.to_vec();
    let mut scanned: HashSet<String> = HashSet::new();
    let mut to_scan = all_system_names.clone();
    while let Some(sys_name) = to_scan.pop() {
        if !scanned.insert(sys_name.clone()) {
            continue;
        }
        if let Some(sys) = ir.systems.iter().find(|s| s.name == sys_name) {
            if !all_system_names.contains(&sys.name) {
                all_system_names.push(sys.name.clone());
            }
            for event in &sys.actions {
                collect_crosscall_targets(&event.body, &mut to_scan);
            }
        }
    }

    let relevant_entities: Vec<&IREntity> = ir
        .entities
        .iter()
        .filter(|e| slots_per_entity.contains_key(&e.name))
        .collect();

    let relevant_systems: Vec<&IRSystem> = ir
        .systems
        .iter()
        .filter(|s| all_system_names.contains(&s.name))
        .collect();

    let chc = match build_liveness_chc(
        &relevant_entities,
        &relevant_systems,
        vctx,
        trigger,
        is_oneshot,
        response,
        entity_var,
        entity_name_for_binding,
        fair_events,
        slots_per_entity,
        target_slot,
    ) {
        Ok(s) => s,
        Err(e) => return Ic3Result::Unknown(format!("liveness CHC encoding failed: {e}")),
    };

    let result = chc::check_chc(&chc, "Error", timeout_ms);
    match result {
        ChcResult::Proved => Ic3Result::Proved,
        ChcResult::Counterexample(_) => {
            // Liveness violation detected — the monitor found a loop.
            // For now, return a simple violation without detailed trace.
            Ic3Result::Violated(vec![])
        }
        ChcResult::Unknown(reason) => Ic3Result::Unknown(reason),
    }
}

/// Build CHC for liveness-to-safety reduction.
///
/// Extends the entity system CHC with monitor columns for:
/// - `pending`: Bool — response obligation active
/// - `saved_{entity}_{slot}_{field}`: same sort — state snapshot at trigger
/// - `saved_{entity}_{slot}_active`: Bool — active flag snapshot
/// - `justice_{i}`: Bool — fair event fired since freeze (coarse: any event satisfies all)
///
/// Error condition: `pending AND state == saved AND all justice` (loop detected).
#[allow(clippy::too_many_arguments)]
pub(super) fn build_liveness_chc(
    entities: &[&IREntity],
    systems: &[&IRSystem],
    vctx: &VerifyContext,
    trigger: &IRExpr,
    is_oneshot: bool,
    response: &IRExpr,
    entity_var: Option<&str>,
    entity_name_for_binding: Option<&str>,
    fair_events: &[(String, String)],
    slots_per_entity: &HashMap<String, usize>,
    // For quantified liveness: restrict trigger/response to this specific slot.
    // None = OR over all slots (existential — only correct for non-quantified).
    // Some(slot) = single slot (for per-slot iteration that achieves universal).
    target_slot: Option<usize>,
) -> Result<String, String> {
    // ── 1. Build column layout ──────────────────────────────────────
    // Entity columns (same as build_system_chc)
    let mut entity_columns: Vec<SlotColumn> = Vec::new();
    for entity in entities {
        let n_slots = slots_per_entity.get(&entity.name).copied().unwrap_or(1);
        for slot in 0..n_slots {
            for (fi, f) in entity.fields.iter().enumerate() {
                entity_columns.push(SlotColumn {
                    var_name: format!("{}_{}_f{}", entity.name, slot, fi),
                    sort_name: ir_type_to_sort_name(&f.ty),
                });
            }
            entity_columns.push(SlotColumn {
                var_name: format!("{}_{}_active", entity.name, slot),
                sort_name: "Bool".to_owned(),
            });
        }
    }

    // Monitor columns
    let mut monitor_columns: Vec<SlotColumn> = Vec::new();
    // pending: response obligation active
    monitor_columns.push(SlotColumn {
        var_name: "mon_pending".to_owned(),
        sort_name: "Bool".to_owned(),
    });
    // discharged: obligation was satisfied (prevents re-triggering for oneshot)
    monitor_columns.push(SlotColumn {
        var_name: "mon_discharged".to_owned(),
        sort_name: "Bool".to_owned(),
    });
    // frozen: saved state has been captured (nondeterministic freeze)
    monitor_columns.push(SlotColumn {
        var_name: "mon_frozen".to_owned(),
        sort_name: "Bool".to_owned(),
    });
    // saved state (one per entity/slot/field + active)
    for entity in entities {
        let n_slots = slots_per_entity.get(&entity.name).copied().unwrap_or(1);
        for slot in 0..n_slots {
            for (fi, f) in entity.fields.iter().enumerate() {
                monitor_columns.push(SlotColumn {
                    var_name: format!("mon_saved_{}_{}_f{}", entity.name, slot, fi),
                    sort_name: ir_type_to_sort_name(&f.ty),
                });
            }
            monitor_columns.push(SlotColumn {
                var_name: format!("mon_saved_{}_{}_active", entity.name, slot),
                sort_name: "Bool".to_owned(),
            });
        }
    }
    // Justice counters (one per fair event): true once ANY event fires since freeze.
    // Coarse over-approximation: any non-stutter transition satisfies all justice.
    // This is sound for proving because it only makes the accepting condition EASIER
    // to satisfy, so any IC3 PROVED result is genuine.
    for (i, _) in fair_events.iter().enumerate() {
        monitor_columns.push(SlotColumn {
            var_name: format!("mon_justice_{i}"),
            sort_name: "Bool".to_owned(),
        });
    }

    // All columns = entity + monitor
    let all_columns: Vec<&SlotColumn> = entity_columns
        .iter()
        .chain(monitor_columns.iter())
        .collect();

    // Next-state monitor column variable names (primed)
    let mut next_monitor_names: Vec<String> = Vec::new();
    for mc in &monitor_columns {
        next_monitor_names.push(format!("{}_next", mc.var_name));
    }

    let mut chc = String::new();

    // Declare State relation
    chc.push_str("(declare-rel State (");
    for col in &all_columns {
        chc.push_str(&col.sort_name);
        chc.push(' ');
    }
    chc.push_str("))\n");
    chc.push_str("(declare-rel Error ())\n");

    // Declare variables (current state)
    for col in &all_columns {
        chc.push_str(&format!(
            "(declare-var {} {})\n",
            col.var_name, col.sort_name
        ));
    }
    // Declare next-state monitor variables
    for (i, mc) in monitor_columns.iter().enumerate() {
        chc.push_str(&format!(
            "(declare-var {} {})\n",
            next_monitor_names[i], mc.sort_name
        ));
    }

    let entity_vars_str: String = entity_columns
        .iter()
        .map(|c| c.var_name.as_str())
        .collect::<Vec<_>>()
        .join(" ");
    let monitor_vars_str: String = monitor_columns
        .iter()
        .map(|c| c.var_name.as_str())
        .collect::<Vec<_>>()
        .join(" ");
    let all_vars_str = format!("{entity_vars_str} {monitor_vars_str}");

    // ── 2. Encode trigger and response as SMT ───────────────────────
    //
    // For quantified liveness (entity_var is Some):
    // - target_slot = Some(slot): encode for ONE specific slot (universal semantics).
    // The caller iterates over all slots, calling IC3 once per slot.
    // - target_slot = None: OR over all slots (existential — UNSOUND for universal
    // quantifiers, kept only as dead path for safety).
    //
    // For non-quantified liveness (entity_var is None): target_slot is ignored.
    let trigger_smt = if let (Some(_var), Some(ent_name)) = (entity_var, entity_name_for_binding) {
        let entity = entities
            .iter()
            .find(|e| e.name == ent_name)
            .ok_or_else(|| format!("entity {ent_name} not found"))?;

        if let Some(slot) = target_slot {
            // Per-slot: encode trigger for just this one slot
            let active = format!("{ent_name}_{slot}_active");
            let p = guard_to_smt_sys(trigger, entity, vctx, ent_name, slot)?;
            let q = guard_to_smt_sys(response, entity, vctx, ent_name, slot)?;
            format!("(and {active} {p} (not {q}) (not mon_pending))")
        } else {
            // Fallback: OR over all slots (existential — not used for quantified)
            let n_slots = slots_per_entity.get(ent_name).copied().unwrap_or(1);
            let mut slot_triggers = Vec::new();
            for slot in 0..n_slots {
                let active = format!("{ent_name}_{slot}_active");
                let p = guard_to_smt_sys(trigger, entity, vctx, ent_name, slot)?;
                let q = guard_to_smt_sys(response, entity, vctx, ent_name, slot)?;
                slot_triggers.push(format!("(and {active} {p} (not {q}) (not mon_pending))"));
            }
            if slot_triggers.len() == 1 {
                slot_triggers.pop().unwrap()
            } else {
                format!("(or {})", slot_triggers.join(" "))
            }
        }
    } else {
        let p = negate_property_smt_system(trigger, entities, vctx, slots_per_entity)
            .map(|s| format!("(not {s})"))?;
        let q = negate_property_smt_system(response, entities, vctx, slots_per_entity)
            .map(|s| format!("(not {s})"))?;
        format!("(and {p} (not {q}) (not mon_pending))")
    };

    let response_smt = if let (Some(_var), Some(ent_name)) = (entity_var, entity_name_for_binding) {
        let entity = entities
            .iter()
            .find(|e| e.name == ent_name)
            .ok_or_else(|| format!("entity {ent_name} not found"))?;

        if let Some(slot) = target_slot {
            // Per-slot: encode response for just this one slot
            let active = format!("{ent_name}_{slot}_active");
            let q = guard_to_smt_sys(response, entity, vctx, ent_name, slot)?;
            format!("(and {active} {q})")
        } else {
            // Fallback: OR over all slots
            let n_slots = slots_per_entity.get(ent_name).copied().unwrap_or(1);
            let mut slot_responses = Vec::new();
            for slot in 0..n_slots {
                let active = format!("{ent_name}_{slot}_active");
                let q = guard_to_smt_sys(response, entity, vctx, ent_name, slot)?;
                slot_responses.push(format!("(and {active} {q})"));
            }
            if slot_responses.len() == 1 {
                slot_responses.pop().unwrap()
            } else {
                format!("(or {})", slot_responses.join(" "))
            }
        }
    } else {
        negate_property_smt_system(response, entities, vctx, slots_per_entity)
            .map(|s| format!("(not {s})"))?
    };

    // ── 3. Monitor transition as SMT ────────────────────────────────
    //
    // Uses "nondeterministic freeze" approach (Biere-Artho-Schuppan):
    // - `pending`: tracks whether a response obligation is active
    // - `frozen`: whether the saved state snapshot has been captured
    // - `saved_*`: state snapshot, captured when frozen becomes true
    // - `fired_i`: whether fair event i has fired since freeze
    // - `enabled_i`: whether fair event i was enabled at some point since freeze
    //
    // Per-event tracking: each event rule sets fired_i = true only for the
    // specific event that fires. enabled_i accumulates across ALL rules.
    // Accepting: for_all_i(NOT enabled_i OR fired_i) — weak fairness.

    // For oneshot (eventuality), add (not mon_discharged) to trigger guard
    let full_trigger_smt = if is_oneshot {
        format!("(and {trigger_smt} (not mon_discharged))")
    } else {
        trigger_smt.clone()
    };

    // pending_next = ITE(trigger_fires, true, ITE(discharge, false, pending))
    let pending_next_str = format!(
        "(ite {full_trigger_smt} true (ite (and mon_pending {response_smt}) false mon_pending))"
    );

    // discharged_next: true once Q holds while pending (permanent, never resets)
    let discharged_next_str = format!("(ite (and mon_pending {response_smt}) true mon_discharged)");

    // ── 3a. Build monitor next-state strings ───────────────────────
    // NO-FREEZE: pending/discharged updated, frozen preserved, saved preserved, justice=true
    let mut monitor_no_freeze: Vec<String> = Vec::new();
    monitor_no_freeze.push(pending_next_str.clone()); // pending
    monitor_no_freeze.push(discharged_next_str.clone()); // discharged
    monitor_no_freeze.push("mon_frozen".to_owned()); // frozen stays same
    for entity in entities {
        let n_slots = slots_per_entity.get(&entity.name).copied().unwrap_or(1);
        for slot in 0..n_slots {
            for (fi, _f) in entity.fields.iter().enumerate() {
                monitor_no_freeze.push(format!("mon_saved_{}_{}_f{}", entity.name, slot, fi));
            }
            monitor_no_freeze.push(format!("mon_saved_{}_{}_active", entity.name, slot));
        }
    }
    for _ in fair_events {
        monitor_no_freeze.push("true".to_owned()); // justice: true on any event fire
    }
    let monitor_no_freeze_str = monitor_no_freeze.join(" ");

    // FREEZE: pending/discharged updated, frozen=true, saved=captured, justice=false
    let mut monitor_freeze: Vec<String> = Vec::new();
    monitor_freeze.push(pending_next_str.clone()); // pending
    monitor_freeze.push(discharged_next_str.clone()); // discharged
    monitor_freeze.push("true".to_owned()); // frozen becomes true
    for entity in entities {
        let n_slots = slots_per_entity.get(&entity.name).copied().unwrap_or(1);
        for slot in 0..n_slots {
            for (fi, _f) in entity.fields.iter().enumerate() {
                monitor_freeze.push(format!("{}_{}_f{}", entity.name, slot, fi));
            }
            monitor_freeze.push(format!("{}_{}_active", entity.name, slot));
        }
    }
    for _ in fair_events {
        monitor_freeze.push("false".to_owned()); // justice: reset on freeze
    }
    let monitor_freeze_str = monitor_freeze.join(" ");

    // Freeze guard: can only freeze while pending and not yet frozen
    let freeze_guard = "(and mon_pending (not mon_frozen))";

    // ── 4. Initial state ────────────────────────────────────────────
    chc.push_str("(rule (State ");
    for entity in entities {
        let n_slots = slots_per_entity.get(&entity.name).copied().unwrap_or(1);
        for slot in 0..n_slots {
            for (fi, f) in entity.fields.iter().enumerate() {
                if let Some(ref default_expr) = f.default {
                    chc.push_str(&expr_to_smt(default_expr, entity, vctx)?);
                } else {
                    chc.push_str(&format!("{}_{}_f{}", entity.name, slot, fi));
                }
                chc.push(' ');
            }
            chc.push_str("false "); // inactive
        }
    }
    // Monitor initial: pending=false, discharged=false, frozen=false,
    // saved=arbitrary, fired=unconstrained, enabled=unconstrained
    chc.push_str("false "); // pending
    chc.push_str("false "); // discharged
    chc.push_str("false "); // frozen
    for entity in entities {
        let n_slots = slots_per_entity.get(&entity.name).copied().unwrap_or(1);
        for slot in 0..n_slots {
            for (fi, _f) in entity.fields.iter().enumerate() {
                chc.push_str(&format!("mon_saved_{}_{}_f{} ", entity.name, slot, fi));
            }
            chc.push_str(&format!("mon_saved_{}_{}_active ", entity.name, slot));
        }
    }
    for (i, _) in fair_events.iter().enumerate() {
        chc.push_str(&format!("mon_justice_{i} ")); // unconstrained
    }
    chc.push_str(") init)\n");

    // ── 5. Stutter rule (entity frame + monitor frame) ──────────────
    // Stutter preserves ALL state including monitor. The monitor does NOT
    // update pending/discharged on stutter because the trigger/response
    // formulas evaluate against entity state which doesn't change on stutter.
    chc.push_str(&format!(
        "(rule (=> (State {all_vars_str}) (State {all_vars_str})) stutter)\n"
    ));

    // ── 6. Transition rules ─────────────────────────────────────────
    // For each system event, encode the entity transition + monitor update.
    // All events use the same monitor strings (coarse justice tracking).
    if systems.is_empty() {
        // Pure entity transitions
        for entity in entities {
            let n_slots = slots_per_entity.get(&entity.name).copied().unwrap_or(1);
            for slot in 0..n_slots {
                for transition in &entity.transitions {
                    let guard =
                        guard_to_smt_sys(&transition.guard, entity, vctx, &entity.name, slot)?;
                    let entity_next_str = build_transition_next(
                        entities,
                        slots_per_entity,
                        entity,
                        &entity.name,
                        slot,
                        transition,
                        vctx,
                    )?;
                    let active_var = format!("{}_{}_active", entity.name, slot);

                    chc.push_str(&format!(
                        "(rule (=> (and (State {all_vars_str}) {active_var} {guard}) \
                         (State {entity_next_str} {monitor_no_freeze_str})) \
                         trans_{}_{}_{slot})\n",
                        entity.name, transition.name
                    ));
                    chc.push_str(&format!(
                        "(rule (=> (and (State {all_vars_str}) {active_var} {guard} {freeze_guard}) \
                         (State {entity_next_str} {monitor_freeze_str})) \
                         trans_{}_{}_{slot}_freeze)\n",
                        entity.name, transition.name
                    ));
                }

                // Create rule
                let create_next_str = build_create_next(
                    entities,
                    slots_per_entity,
                    entity,
                    &entity.name,
                    slot,
                    &[],
                    vctx,
                )?;
                let inactive_var = format!("{}_{}_active", entity.name, slot);
                let mut create_guard = if slot == 0 {
                    format!("(not {inactive_var})")
                } else {
                    format!(
                        "(and (not {inactive_var}) {}_{}_active)",
                        entity.name,
                        slot - 1
                    )
                };

                // Add initial_constraint guards for nondeterministic fields
                for (fi, f) in entity.fields.iter().enumerate() {
                    if let Some(ref constraint) = f.initial_constraint {
                        let field_var = format!("{}_{}_f{}", entity.name, slot, fi);
                        if let Ok(constraint_smt) =
                            constraint_to_smt_with_dollar(constraint, &field_var, entity, vctx)
                        {
                            create_guard = format!("(and {create_guard} {constraint_smt})");
                        }
                    }
                }

                chc.push_str(&format!(
                    "(rule (=> (and (State {all_vars_str}) {create_guard}) \
                     (State {create_next_str} {monitor_no_freeze_str})) \
                     create_{}_{slot})\n",
                    entity.name
                ));
                chc.push_str(&format!(
                    "(rule (=> (and (State {all_vars_str}) {create_guard} {freeze_guard}) \
                     (State {create_next_str} {monitor_freeze_str})) \
                     create_{}_{slot}_freeze)\n",
                    entity.name
                ));
            }
        }
    }

    // System event rules — encode using existing CHC event encoder.
    for system in systems {
        for event in &system.actions {
            let mut visited = HashSet::new();
            visited.insert((system.name.clone(), event.name.clone()));

            encode_liveness_event_chc(
                &mut chc,
                &event.body,
                &event.guard,
                entities,
                vctx,
                slots_per_entity,
                &all_vars_str,
                &monitor_no_freeze_str,
                &monitor_freeze_str,
                freeze_guard,
                systems,
                &format!("{}_{}", system.name, event.name),
                &[],
                &mut visited,
            )?;
        }
    }

    // ── 7. Domain constraints ───────────────────────────────────────
    for entity in entities {
        let n_slots = slots_per_entity.get(&entity.name).copied().unwrap_or(1);
        for slot in 0..n_slots {
            for (fi, f) in entity.fields.iter().enumerate() {
                if let IRType::Enum { name, variants } = &f.ty {
                    if variants.iter().any(|variant| !variant.fields.is_empty()) {
                        continue;
                    }
                    if let Some(&(min_id, max_id)) = vctx.enum_ranges.get(name) {
                        let var = format!("{}_{}_f{}", entity.name, slot, fi);
                        let active = format!("{}_{}_active", entity.name, slot);
                        chc.push_str(&format!(
                            "(rule (=> (and (State {all_vars_str}) {active} \
                             (or (< {var} {min_id}) (> {var} {max_id}))) Error) \
                             domain_{}_{}_{fi})\n",
                            entity.name, slot
                        ));
                    }
                }
            }
        }
    }

    // ── 8. Error condition: accepting = true ─────────────────────────
    // accepting = pending AND frozen AND state_matches AND weak_fairness
    // weak_fairness = for_all_i(NOT enabled_i OR fired_i)
    let mut state_match_parts: Vec<String> = Vec::new();
    for entity in entities {
        let n_slots = slots_per_entity.get(&entity.name).copied().unwrap_or(1);
        for slot in 0..n_slots {
            for (fi, _f) in entity.fields.iter().enumerate() {
                let current = format!("{}_{}_f{}", entity.name, slot, fi);
                let saved = format!("mon_saved_{}_{}_f{}", entity.name, slot, fi);
                state_match_parts.push(format!("(= {current} {saved})"));
            }
            let current_act = format!("{}_{}_active", entity.name, slot);
            let saved_act = format!("mon_saved_{}_{}_active", entity.name, slot);
            state_match_parts.push(format!("(= {current_act} {saved_act})"));
        }
    }

    let mut accepting_parts = vec!["mon_pending".to_owned(), "mon_frozen".to_owned()];
    accepting_parts.extend(state_match_parts);
    // Weak fairness: for each fair event, NOT enabled OR fired
    for (i, _) in fair_events.iter().enumerate() {
        accepting_parts.push(format!("mon_justice_{i}"));
    }

    let accepting = format!("(and {})", accepting_parts.join(" "));
    chc.push_str(&format!(
        "(rule (=> (and (State {all_vars_str}) {accepting}) Error) accepting)\n"
    ));

    Ok(chc)
}

/// Encode system event body into liveness CHC rules with nondeterministic freeze.
/// Each transition produces two rules: no-freeze and freeze.
#[allow(clippy::too_many_arguments)]
fn encode_liveness_event_chc(
    chc: &mut String,
    body: &[IRAction],
    guard: &IRExpr,
    entities: &[&IREntity],
    vctx: &VerifyContext,
    slots_per_entity: &HashMap<String, usize>,
    all_vars_str: &str,
    monitor_no_freeze_str: &str,
    monitor_freeze_str: &str,
    freeze_guard: &str,
    all_systems: &[&IRSystem],
    rule_prefix: &str,
    extra_guards: &[String],
    visited: &mut HashSet<(String, String)>,
) -> Result<(), String> {
    // Helper: emit a CHC rule in both freeze and no-freeze variants.
    #[allow(clippy::too_many_arguments)]
    fn emit_dual_rules(
        chc: &mut String,
        all_vars_str: &str,
        guard_str: &str,
        entity_next_str: &str,
        monitor_no_freeze_str: &str,
        monitor_freeze_str: &str,
        freeze_guard: &str,
        rule_name: &str,
    ) {
        // No-freeze rule
        chc.push_str(&format!(
            "(rule (=> (and (State {all_vars_str}) {guard_str}) \
             (State {entity_next_str} {monitor_no_freeze_str})) {rule_name})\n"
        ));
        // Freeze rule (only when pending and not frozen)
        chc.push_str(&format!(
            "(rule (=> (and (State {all_vars_str}) {guard_str} {freeze_guard}) \
             (State {entity_next_str} {monitor_freeze_str})) {rule_name}_freeze)\n"
        ));
    }

    for action in body {
        match action {
            IRAction::Choose {
                entity: ent_name,
                filter,
                ops,
                ..
            } => {
                let entity = entities
                    .iter()
                    .find(|e| e.name == *ent_name)
                    .ok_or_else(|| format!("entity {ent_name} not found in Choose"))?;
                let n_slots = slots_per_entity.get(ent_name).copied().unwrap_or(1);
                for slot in 0..n_slots {
                    let filter_smt = guard_to_smt_sys(filter, entity, vctx, ent_name, slot)?;
                    let active_var = format!("{ent_name}_{slot}_active");
                    let mut nested_guards = extra_guards.to_vec();
                    nested_guards.push(active_var);
                    nested_guards.push(filter_smt);

                    for (oi, op) in ops.iter().enumerate() {
                        if let IRAction::Apply {
                            transition: trans_name,
                            ..
                        } = op
                        {
                            let trans = entity
                                .transitions
                                .iter()
                                .find(|t| t.name == *trans_name)
                                .ok_or_else(|| {
                                format!("transition {trans_name} not found on entity {ent_name}")
                            })?;
                            let trans_guard =
                                guard_to_smt_sys(&trans.guard, entity, vctx, ent_name, slot)?;
                            let entity_next_str = build_transition_next(
                                entities,
                                slots_per_entity,
                                entity,
                                ent_name,
                                slot,
                                trans,
                                vctx,
                            )?;
                            let mut all_guards = nested_guards.clone();
                            all_guards.push(trans_guard);
                            if !matches!(
                                guard,
                                IRExpr::Lit {
                                    value: LitVal::Bool { value: true },
                                    ..
                                }
                            ) {
                                if let Ok(g) = encode_non_entity_guard(guard) {
                                    if g != "true" {
                                        all_guards.push(g);
                                    }
                                }
                            }
                            let guard_str = if all_guards.is_empty() {
                                "true".to_owned()
                            } else {
                                format!("(and {})", all_guards.join(" "))
                            };
                            emit_dual_rules(
                                chc,
                                all_vars_str,
                                &guard_str,
                                &entity_next_str,
                                monitor_no_freeze_str,
                                monitor_freeze_str,
                                freeze_guard,
                                &format!("{rule_prefix}_choose_{oi}_s{slot}"),
                            );
                        }
                    }
                }
            }
            IRAction::ForAll {
                entity: ent_name,
                ops,
                ..
            } => {
                let entity = entities
                    .iter()
                    .find(|e| e.name == *ent_name)
                    .ok_or_else(|| format!("entity {ent_name} not found in ForAll"))?;
                let n_slots = slots_per_entity.get(ent_name).copied().unwrap_or(1);
                for slot in 0..n_slots {
                    let active_var = format!("{ent_name}_{slot}_active");
                    let mut nested_guards = extra_guards.to_vec();
                    nested_guards.push(active_var);

                    for (oi, op) in ops.iter().enumerate() {
                        if let IRAction::Apply {
                            transition: trans_name,
                            ..
                        } = op
                        {
                            if let Some(trans) =
                                entity.transitions.iter().find(|t| t.name == *trans_name)
                            {
                                let trans_guard =
                                    guard_to_smt_sys(&trans.guard, entity, vctx, ent_name, slot)?;
                                let entity_next_str = build_transition_next(
                                    entities,
                                    slots_per_entity,
                                    entity,
                                    ent_name,
                                    slot,
                                    trans,
                                    vctx,
                                )?;
                                let mut all_guards = nested_guards.clone();
                                all_guards.push(trans_guard);
                                let guard_str = format!("(and {})", all_guards.join(" "));
                                emit_dual_rules(
                                    chc,
                                    all_vars_str,
                                    &guard_str,
                                    &entity_next_str,
                                    monitor_no_freeze_str,
                                    monitor_freeze_str,
                                    freeze_guard,
                                    &format!("{rule_prefix}_forall_{oi}_s{slot}"),
                                );
                            }
                        }
                    }
                }
            }
            IRAction::Create {
                entity: ent_name, ..
            } => {
                let entity = entities
                    .iter()
                    .find(|e| e.name == *ent_name)
                    .ok_or_else(|| format!("entity {ent_name} not found in Create"))?;
                let n_slots = slots_per_entity.get(ent_name).copied().unwrap_or(1);
                for slot in 0..n_slots {
                    let create_next_str = build_create_next(
                        entities,
                        slots_per_entity,
                        entity,
                        &entity.name,
                        slot,
                        &[],
                        vctx,
                    )?;
                    let inactive_var = format!("{ent_name}_{slot}_active");
                    let create_guard = if slot == 0 {
                        format!("(not {inactive_var})")
                    } else {
                        format!(
                            "(and (not {inactive_var}) {}_{}_active)",
                            ent_name,
                            slot - 1
                        )
                    };
                    let mut all_guards = extra_guards.to_vec();
                    all_guards.push(create_guard);
                    // Add initial_constraint guards for nondeterministic fields
                    for (fi, f) in entity.fields.iter().enumerate() {
                        if let Some(ref constraint) = f.initial_constraint {
                            let field_var = format!("{ent_name}_{slot}_f{fi}");
                            if let Ok(constraint_smt) =
                                constraint_to_smt_with_dollar(constraint, &field_var, entity, vctx)
                            {
                                all_guards.push(constraint_smt);
                            }
                        }
                    }
                    let guard_str = format!("(and {})", all_guards.join(" "));
                    emit_dual_rules(
                        chc,
                        all_vars_str,
                        &guard_str,
                        &create_next_str,
                        monitor_no_freeze_str,
                        monitor_freeze_str,
                        freeze_guard,
                        &format!("{rule_prefix}_create_{slot}"),
                    );
                }
            }
            IRAction::CrossCall {
                system: target_sys,
                command: target_evt,
                ..
            } => {
                let sys = all_systems
                    .iter()
                    .find(|s| s.name == *target_sys)
                    .ok_or_else(|| format!("CrossCall target system {target_sys} not found"))?;
                let evt = sys
                    .actions
                    .iter()
                    .find(|e| e.name == *target_evt)
                    .ok_or_else(|| {
                        format!("CrossCall target event {target_sys}.{target_evt} not found")
                    })?;
                let key = (target_sys.clone(), target_evt.clone());
                if visited.insert(key.clone()) {
                    encode_liveness_event_chc(
                        chc,
                        &evt.body,
                        &evt.guard,
                        entities,
                        vctx,
                        slots_per_entity,
                        all_vars_str,
                        monitor_no_freeze_str,
                        monitor_freeze_str,
                        freeze_guard,
                        all_systems,
                        &format!("{rule_prefix}_cc_{target_sys}_{target_evt}"),
                        extra_guards,
                        visited,
                    )?;
                    visited.remove(&key);
                }
            }
            _ => {}
        }
    }
    Ok(())
}
