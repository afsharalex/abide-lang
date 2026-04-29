use super::*;

/// Encode a system event body as CHC transition rules.
///
/// Walks the event action tree and generates composite rules that combine
/// event guards, choose filters, and transition effects. Context guards from
/// parent blocks are propagated through `extra_guards` so callee rules stay
/// constrained by the calling context.
///
/// `ForAll` is encoded as per-slot independent transitions, not a single
/// combined all-slot rule. That over-approximates reachable states, which is
/// conservative for safety proofs.
///
/// All encoding errors propagate. Missing transitions, systems, events, and
/// cyclic `CrossCall` graphs produce hard errors.
#[allow(
    clippy::too_many_arguments,
    clippy::too_many_lines,
    clippy::format_push_string
)]
pub(in crate::verify::ic3) fn encode_step_chc(
    chc: &mut String,
    actions: &[IRAction],
    event_guard: &IRExpr,
    entities: &[&IREntity],
    vctx: &VerifyContext,
    slots_per_entity: &HashMap<String, usize>,
    all_vars_str: &str,
    all_systems: &[&IRSystem],
    rule_prefix: &str,
    extra_guards: &[String],
    visited: &mut HashSet<(String, String)>,
) -> Result<(), String> {
    for (ai, action) in actions.iter().enumerate() {
        match action {
            IRAction::Choose {
                var,
                entity: ent_name,
                filter,
                ops,
            } => {
                let entity = entities
                    .iter()
                    .find(|e| e.name == *ent_name)
                    .ok_or_else(|| format!("entity {ent_name} not found"))?;
                let n_slots = slots_per_entity.get(ent_name).copied().unwrap_or(1);

                for slot in 0..n_slots {
                    let evt_guard = guard_to_smt_sys(event_guard, entity, vctx, ent_name, slot)?;
                    let filter_smt = guard_to_smt_sys(filter, entity, vctx, ent_name, slot)?;
                    let active_var = format!("{ent_name}_{slot}_active");

                    let mut choose_guards = extra_guards.to_vec();
                    choose_guards.push(active_var);
                    choose_guards.push(evt_guard);
                    choose_guards.push(filter_smt);

                    encode_ops_chc(
                        chc,
                        ops,
                        entities,
                        entity,
                        ent_name,
                        slot,
                        var,
                        vctx,
                        slots_per_entity,
                        all_vars_str,
                        all_systems,
                        &format!("{rule_prefix}_choose_{ai}_s{slot}"),
                        &choose_guards,
                        visited,
                    )?;
                }
            }
            IRAction::ForAll {
                var,
                entity: ent_name,
                ops,
            } => {
                let entity = entities
                    .iter()
                    .find(|e| e.name == *ent_name)
                    .ok_or_else(|| format!("entity {ent_name} not found for ForAll"))?;
                let n_slots = slots_per_entity.get(ent_name).copied().unwrap_or(1);

                for slot in 0..n_slots {
                    let evt_guard = guard_to_smt_sys(event_guard, entity, vctx, ent_name, slot)?;
                    let active_var = format!("{ent_name}_{slot}_active");

                    let mut forall_guards = extra_guards.to_vec();
                    forall_guards.push(active_var);
                    forall_guards.push(evt_guard);

                    encode_ops_chc(
                        chc,
                        ops,
                        entities,
                        entity,
                        ent_name,
                        slot,
                        var,
                        vctx,
                        slots_per_entity,
                        all_vars_str,
                        all_systems,
                        &format!("{rule_prefix}_forall_{ai}_s{slot}"),
                        &forall_guards,
                        visited,
                    )?;
                }
            }
            IRAction::Create {
                entity: ent_name,
                fields: create_fields,
            } => {
                // Top-level Create — event guard may not reference entity fields
                let evt_guard_smt = encode_non_entity_guard(event_guard)?;
                let mut guards = extra_guards.to_vec();
                if evt_guard_smt != "true" {
                    guards.push(evt_guard_smt);
                }
                encode_create_chc(
                    chc,
                    entities,
                    vctx,
                    slots_per_entity,
                    all_vars_str,
                    ent_name,
                    create_fields,
                    &guards,
                    &format!("{rule_prefix}_create_{ai}"),
                )?;
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

                // Cycle guard: detect recursive CrossCall chains
                let key = (target_sys.clone(), target_evt.clone());
                if !visited.insert(key.clone()) {
                    return Err(format!(
                        "cyclic CrossCall detected: {target_sys}.{target_evt}"
                    ));
                }

                // Propagate caller's event guard as extra context for callee
                let evt_guard_smt = encode_non_entity_guard(event_guard)?;
                let mut cc_guards = extra_guards.to_vec();
                if evt_guard_smt != "true" {
                    cc_guards.push(evt_guard_smt);
                }

                let result = encode_step_chc(
                    chc,
                    &evt.body,
                    &evt.guard,
                    entities,
                    vctx,
                    slots_per_entity,
                    all_vars_str,
                    all_systems,
                    &format!("{rule_prefix}_cc_{target_sys}_{target_evt}"),
                    &cc_guards,
                    visited,
                );
                visited.remove(&key);
                result?;
            }
            IRAction::ExprStmt { .. } => {
                // No state change — correct to not generate a rule.
            }
            IRAction::LetCrossCall { .. } | IRAction::Match { .. } => {
                return Err(
                    "macro-step command let/match is not yet supported in IC3 encoding".to_owned(),
                );
            }
            IRAction::Apply { .. } => {
                return Err(
                    "bare Apply outside Choose/ForAll in event body — malformed IR".to_owned(),
                );
            }
        }
    }
    Ok(())
}

/// Encode ops within a Choose/ForAll context (with a bound entity slot).
///
/// Handles all action types: Apply, Create, `CrossCall`, nested Choose/ForAll.
/// Context guards from the parent are propagated to every generated rule.
/// `bound_var` is the variable name from the enclosing Choose/ForAll — Apply
/// targets are validated against it to catch malformed IR.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
pub(in crate::verify::ic3) fn encode_ops_chc(
    chc: &mut String,
    ops: &[IRAction],
    entities: &[&IREntity],
    bound_entity: &IREntity,
    bound_ent_name: &str,
    bound_slot: usize,
    bound_var: &str,
    vctx: &VerifyContext,
    slots_per_entity: &HashMap<String, usize>,
    all_vars_str: &str,
    all_systems: &[&IRSystem],
    rule_prefix: &str,
    guards: &[String],
    visited: &mut HashSet<(String, String)>,
) -> Result<(), String> {
    // Reject multi-apply on same entity — IC3's per-Apply CHC rules model
    // sequential transitions as separate derivation steps, not atomic
    // intra-event composition. BMC handles this via intermediate variable
    // chaining; IC3 would need combined rules with intermediate constraints.
    let same_entity_apply_count = ops
        .iter()
        .filter(|op| matches!(op, IRAction::Apply { target, .. } if target == bound_var))
        .count();
    if same_entity_apply_count > 1 {
        return Err("multi-apply on same entity in IC3 encoding not supported \
             (sequential composition requires intermediate CHC constraints)"
            .to_owned());
    }

    for (oi, op) in ops.iter().enumerate() {
        match op {
            IRAction::Apply {
                target,
                transition: trans_name,
                ..
            } => {
                if target != bound_var {
                    return Err(format!(
                        "Apply target {target} does not match bound variable \
                         {bound_var} from enclosing Choose/ForAll — malformed IR"
                    ));
                }
                let trans = bound_entity
                    .transitions
                    .iter()
                    .find(|t| t.name == *trans_name)
                    .ok_or_else(|| {
                        format!("transition {trans_name} not found on entity {bound_ent_name}")
                    })?;
                let trans_guard =
                    guard_to_smt_sys(&trans.guard, bound_entity, vctx, bound_ent_name, bound_slot)?;
                let next_str = build_transition_next(
                    entities,
                    slots_per_entity,
                    bound_entity,
                    bound_ent_name,
                    bound_slot,
                    trans,
                    vctx,
                )?;
                let mut all_guards = guards.to_vec();
                all_guards.push(trans_guard);
                chc.push_str(&format_chc_rule(
                    all_vars_str,
                    &all_guards,
                    &next_str,
                    &format!("{rule_prefix}_{trans_name}"),
                ));
            }
            IRAction::Create {
                entity: ent_name,
                fields: create_fields,
            } => {
                encode_create_chc(
                    chc,
                    entities,
                    vctx,
                    slots_per_entity,
                    all_vars_str,
                    ent_name,
                    create_fields,
                    guards,
                    &format!("{rule_prefix}_create_{oi}"),
                )?;
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

                // Cycle guard
                let key = (target_sys.clone(), target_evt.clone());
                if !visited.insert(key.clone()) {
                    return Err(format!(
                        "cyclic CrossCall detected: {target_sys}.{target_evt}"
                    ));
                }
                let result = encode_step_chc(
                    chc,
                    &evt.body,
                    &evt.guard,
                    entities,
                    vctx,
                    slots_per_entity,
                    all_vars_str,
                    all_systems,
                    &format!("{rule_prefix}_cc_{oi}_{target_sys}_{target_evt}"),
                    guards,
                    visited,
                );
                visited.remove(&key);
                result?;
            }
            IRAction::Choose {
                var,
                entity: ent_name,
                filter,
                ops: inner_ops,
            } => {
                // Nested Choose inside ForAll/Choose
                let entity = entities
                    .iter()
                    .find(|e| e.name == *ent_name)
                    .ok_or_else(|| format!("entity {ent_name} not found in nested Choose"))?;
                let n_slots = slots_per_entity.get(ent_name).copied().unwrap_or(1);
                for slot in 0..n_slots {
                    let filter_smt = guard_to_smt_sys(filter, entity, vctx, ent_name, slot)?;
                    let active_var = format!("{ent_name}_{slot}_active");
                    let mut nested = guards.to_vec();
                    nested.push(active_var);
                    nested.push(filter_smt);
                    encode_ops_chc(
                        chc,
                        inner_ops,
                        entities,
                        entity,
                        ent_name,
                        slot,
                        var,
                        vctx,
                        slots_per_entity,
                        all_vars_str,
                        all_systems,
                        &format!("{rule_prefix}_choose_{oi}_s{slot}"),
                        &nested,
                        visited,
                    )?;
                }
            }
            IRAction::ForAll {
                var,
                entity: ent_name,
                ops: inner_ops,
            } => {
                // Nested ForAll
                let entity = entities
                    .iter()
                    .find(|e| e.name == *ent_name)
                    .ok_or_else(|| format!("entity {ent_name} not found in nested ForAll"))?;
                let n_slots = slots_per_entity.get(ent_name).copied().unwrap_or(1);
                for slot in 0..n_slots {
                    let active_var = format!("{ent_name}_{slot}_active");
                    let mut nested = guards.to_vec();
                    nested.push(active_var);
                    encode_ops_chc(
                        chc,
                        inner_ops,
                        entities,
                        entity,
                        ent_name,
                        slot,
                        var,
                        vctx,
                        slots_per_entity,
                        all_vars_str,
                        all_systems,
                        &format!("{rule_prefix}_forall_{oi}_s{slot}"),
                        &nested,
                        visited,
                    )?;
                }
            }
            IRAction::ExprStmt { .. } => {
                // No state change — correct to skip.
            }
            IRAction::LetCrossCall { .. } | IRAction::Match { .. } => {
                return Err(
                    "macro-step command let/match is not yet supported in IC3 nested encoding"
                        .to_owned(),
                );
            }
        }
    }
    Ok(())
}

/// Try to encode an event guard that doesn't reference entity fields.
///
/// Returns `"true"` for boolean true, propagates error for guards that
/// require entity context (e.g., field comparisons outside Choose/ForAll).
pub(in crate::verify::ic3) fn encode_non_entity_guard(guard: &IRExpr) -> Result<String, String> {
    match guard {
        IRExpr::Lit {
            value: LitVal::Bool { value: true },
            ..
        } => Ok("true".to_owned()),
        IRExpr::Lit {
            value: LitVal::Bool { value: false },
            ..
        } => Ok("false".to_owned()),
        _ => Err(format!(
            "event guard requires entity context but appears outside Choose/ForAll: {:?}",
            std::mem::discriminant(guard)
        )),
    }
}

/// Build next-state string with transition updates for a specific entity slot.
///
/// The target slot gets transition updates; everything else is framed.
pub(in crate::verify::ic3) fn build_transition_next(
    entities: &[&IREntity],
    slots_per_entity: &HashMap<String, usize>,
    target_entity: &IREntity,
    target_ent_name: &str,
    target_slot: usize,
    transition: &IRTransition,
    vctx: &VerifyContext,
) -> Result<String, String> {
    let mut next_vals = Vec::new();
    for ent in entities {
        let ns = slots_per_entity.get(&ent.name).copied().unwrap_or(1);
        for s in 0..ns {
            for (fi, f) in ent.fields.iter().enumerate() {
                if ent.name == target_ent_name && s == target_slot {
                    if let Some(upd) = transition.updates.iter().find(|u| u.field == f.name) {
                        next_vals.push(expr_to_smt_sys(
                            &upd.value,
                            target_entity,
                            vctx,
                            target_ent_name,
                            target_slot,
                        )?);
                    } else {
                        next_vals.push(format!("{}_{}_f{}", ent.name, s, fi));
                    }
                } else {
                    next_vals.push(format!("{}_{}_f{}", ent.name, s, fi));
                }
            }
            if ent.name == target_ent_name && s == target_slot {
                next_vals.push("true".to_owned());
            } else {
                next_vals.push(format!("{}_{}_active", ent.name, s));
            }
        }
    }
    Ok(next_vals.join(" "))
}

/// Build next-state string with entity creation for a specific slot.
///
/// The target slot gets created (fields from `create_fields` or defaults, `active=true`).
/// Everything else is framed. Propagates encoding errors — never falls back to frame.
pub(in crate::verify::ic3) fn build_create_next(
    entities: &[&IREntity],
    slots_per_entity: &HashMap<String, usize>,
    create_entity: &IREntity,
    create_ent_name: &str,
    create_slot: usize,
    create_fields: &[IRCreateField],
    vctx: &VerifyContext,
) -> Result<String, String> {
    let mut next_vals = Vec::new();
    for ent in entities {
        let ns = slots_per_entity.get(&ent.name).copied().unwrap_or(1);
        for s in 0..ns {
            for (fi, f) in ent.fields.iter().enumerate() {
                if ent.name == create_ent_name && s == create_slot {
                    if let Some(cf) = create_fields.iter().find(|cf| cf.name == f.name) {
                        next_vals.push(expr_to_smt(&cf.value, create_entity, vctx)?);
                    } else if f.initial_constraint.is_some() {
                        // Nondeterministic: leave as free variable
                        next_vals.push(format!("{}_{}_f{}", ent.name, s, fi));
                    } else if let Some(ref def) = f.default {
                        next_vals.push(expr_to_smt(def, create_entity, vctx)?);
                    } else {
                        // No explicit value and no default: unconstrained
                        next_vals.push(format!("{}_{}_f{}", ent.name, s, fi));
                    }
                } else {
                    next_vals.push(format!("{}_{}_f{}", ent.name, s, fi));
                }
            }
            if ent.name == create_ent_name && s == create_slot {
                next_vals.push("true".to_owned());
            } else {
                next_vals.push(format!("{}_{}_active", ent.name, s));
            }
        }
    }
    Ok(next_vals.join(" "))
}

/// Encode a Create action as CHC rules — one rule per available (inactive) slot.
#[allow(clippy::too_many_arguments)]
pub(in crate::verify::ic3) fn encode_create_chc(
    chc: &mut String,
    entities: &[&IREntity],
    vctx: &VerifyContext,
    slots_per_entity: &HashMap<String, usize>,
    all_vars_str: &str,
    create_ent_name: &str,
    create_fields: &[IRCreateField],
    extra_guards: &[String],
    rule_prefix: &str,
) -> Result<(), String> {
    let entity = entities
        .iter()
        .find(|e| e.name == create_ent_name)
        .ok_or_else(|| format!("entity {create_ent_name} not found for Create"))?;
    let n_slots = slots_per_entity.get(create_ent_name).copied().unwrap_or(1);
    for slot in 0..n_slots {
        let inactive = format!("{create_ent_name}_{slot}_active");
        let next_str = build_create_next(
            entities,
            slots_per_entity,
            entity,
            create_ent_name,
            slot,
            create_fields,
            vctx,
        )?;
        let mut guards = extra_guards.to_vec();
        guards.push(format!("(not {inactive})"));
        // Symmetry breaking: slot i can only be created if slot i-1 is active
        if slot > 0 {
            guards.push(format!("{}_{}_active", create_ent_name, slot - 1));
        }
        // Add initial_constraint guards for nondeterministic fields
        let create_field_names: Vec<&str> =
            create_fields.iter().map(|cf| cf.name.as_str()).collect();
        for (fi, f) in entity.fields.iter().enumerate() {
            if create_field_names.contains(&f.name.as_str()) {
                continue; // field explicitly set in create block
            }
            if let Some(ref constraint) = f.initial_constraint {
                let field_var = format!("{create_ent_name}_{slot}_f{fi}");
                if let Ok(constraint_smt) =
                    constraint_to_smt_with_dollar(constraint, &field_var, entity, vctx)
                {
                    guards.push(constraint_smt);
                }
            }
        }
        chc.push_str(&format_chc_rule(
            all_vars_str,
            &guards,
            &next_str,
            &format!("{rule_prefix}_{create_ent_name}_s{slot}"),
        ));
    }
    Ok(())
}

/// Format a CHC rule with AND of all guard conditions.
pub(in crate::verify::ic3) fn format_chc_rule(
    all_vars_str: &str,
    guards: &[String],
    next_str: &str,
    rule_name: &str,
) -> String {
    if guards.is_empty() {
        format!("(rule (=> (State {all_vars_str}) (State {next_str})) {rule_name})\n")
    } else {
        let guard_str = guards.join(" ");
        format!(
            "(rule (=> (and (State {all_vars_str}) {guard_str}) \
             (State {next_str})) {rule_name})\n"
        )
    }
}
