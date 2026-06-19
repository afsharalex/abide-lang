use super::*;

#[derive(Clone, Copy)]
pub(in crate::verify::ic3) struct Ic3SystemActionCtx<'a> {
    pub(in crate::verify::ic3) entities: &'a [&'a IREntity],
    pub(in crate::verify::ic3) vctx: &'a VerifyContext,
    pub(in crate::verify::ic3) slots_per_entity: &'a HashMap<String, usize>,
    pub(in crate::verify::ic3) all_vars_str: &'a str,
    pub(in crate::verify::ic3) all_systems: &'a [&'a IRSystem],
}

#[derive(Clone, Copy)]
pub(in crate::verify::ic3) struct EncodeStepChcInput<'a> {
    pub(in crate::verify::ic3) actions: &'a [IRAction],
    pub(in crate::verify::ic3) event_guard: &'a IRExpr,
    pub(in crate::verify::ic3) rule_prefix: &'a str,
    pub(in crate::verify::ic3) extra_guards: &'a [String],
}

#[derive(Clone, Copy)]
pub(in crate::verify::ic3) struct BoundActionSlot<'a> {
    pub(in crate::verify::ic3) entity: &'a IREntity,
    pub(in crate::verify::ic3) entity_name: &'a str,
    pub(in crate::verify::ic3) slot: usize,
    pub(in crate::verify::ic3) var: &'a str,
}

#[derive(Clone, Copy)]
pub(in crate::verify::ic3) struct EncodeOpsChcInput<'a> {
    pub(in crate::verify::ic3) ops: &'a [IRAction],
    pub(in crate::verify::ic3) bound: BoundActionSlot<'a>,
    pub(in crate::verify::ic3) rule_prefix: &'a str,
    pub(in crate::verify::ic3) guards: &'a [String],
}

struct MacroCallChcInput<'a> {
    target_sys: &'a str,
    target_evt: &'a str,
    rule_prefix: &'a str,
    guards: &'a [String],
    local_terms: &'a HashMap<String, String>,
}

struct ActionMatchScrutineeInput<'a> {
    scrutinee: &'a crate::ir::types::IRActionMatchScrutinee,
    rule_prefix: &'a str,
    action_index: usize,
    guards: &'a [String],
    local_terms: &'a HashMap<String, String>,
}

struct CreateChcInput<'a> {
    entity_name: &'a str,
    fields: &'a [IRCreateField],
    guards: &'a [String],
    rule_prefix: &'a str,
}

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
pub(in crate::verify::ic3) fn encode_step_chc(
    chc: &mut String,
    ctx: Ic3SystemActionCtx<'_>,
    input: EncodeStepChcInput<'_>,
    visited: &mut HashSet<(String, String)>,
) -> Result<(), String> {
    encode_step_chc_scoped(chc, ctx, input, visited, &HashMap::new())
}

/// Whether an event-body action is a standalone state mutation for the
/// purpose of IC3's atomic-composition guard. `ExprStmt` emits no CHC rule,
/// and a macro-step binding (`LetCrossCall`) whose target command has an
/// empty (non-mutating) body is a pure value computation; everything else
/// (`Choose`/`ForAll`/`Create`/`CrossCall`/`Apply`/`Match`) mutates state.
/// A non-empty target body is treated conservatively as mutating.
fn action_mutates_state(action: &IRAction, all_systems: &[&IRSystem]) -> bool {
    match action {
        IRAction::ExprStmt { .. } => false,
        IRAction::LetCrossCall {
            system, command, ..
        } => all_systems
            .iter()
            .find(|s| s.name == *system)
            .and_then(|s| s.actions.iter().find(|a| a.name == *command))
            .is_none_or(|a| !a.body.is_empty()),
        _ => true,
    }
}

fn encode_step_chc_scoped(
    chc: &mut String,
    action_ctx: Ic3SystemActionCtx<'_>,
    input: EncodeStepChcInput<'_>,
    visited: &mut HashSet<(String, String)>,
    local_terms: &HashMap<String, String>,
) -> Result<(), String> {
    let Ic3SystemActionCtx {
        entities,
        vctx,
        slots_per_entity,
        all_vars_str: _,
        all_systems,
    } = action_ctx;
    let EncodeStepChcInput {
        actions,
        event_guard,
        rule_prefix,
        extra_guards,
    } = input;
    // IC3 encodes each top-level action of an event body as an independent
    // CHC rule and cannot express the atomic sequential composition of
    // multiple state-mutating actions: intermediate effects are not threaded
    // between rules and no-rule forms (e.g. ExprStmt) are silently dropped,
    // under-approximating the event. If a body contains more than one
    // state-mutating action it is rejected so the caller downgrades to
    // Unknown instead of returning a definitive (possibly false) PROVED.
    // A pure macro-step prelude (`let x = <pure call>`) followed by a single
    // effectful action — the supported `let .. match ..` routing — stays
    // atomic and is encoded faithfully. The recursive calls below (Match
    // arms, CrossCall targets) re-enter this function, so nested multi-op
    // bodies are caught at every level.
    let mutating_actions = actions
        .iter()
        .filter(|a| action_mutates_state(a, all_systems))
        .count();
    if mutating_actions > 1 {
        return Err(format!(
            "multi-op event body `{rule_prefix}` ({mutating_actions} state-mutating actions) \
             is not supported by IC3: independent per-action CHC rules cannot express atomic \
             sequential composition; downgrading conservatively"
        ));
    }
    let mut local_terms = local_terms.clone();
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
                    choose_guards.push(wrap_action_locals(filter_smt, &local_terms));

                    encode_ops_chc_scoped(
                        chc,
                        action_ctx,
                        EncodeOpsChcInput {
                            ops,
                            bound: BoundActionSlot {
                                entity,
                                entity_name: ent_name,
                                slot,
                                var,
                            },
                            rule_prefix: &format!("{rule_prefix}_choose_{ai}_s{slot}"),
                            guards: &choose_guards,
                        },
                        visited,
                        &local_terms,
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

                    encode_ops_chc_scoped(
                        chc,
                        action_ctx,
                        EncodeOpsChcInput {
                            ops,
                            bound: BoundActionSlot {
                                entity,
                                entity_name: ent_name,
                                slot,
                                var,
                            },
                            rule_prefix: &format!("{rule_prefix}_forall_{ai}_s{slot}"),
                            guards: &forall_guards,
                        },
                        visited,
                        &local_terms,
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
                    action_ctx,
                    CreateChcInput {
                        entity_name: ent_name,
                        fields: create_fields,
                        guards: &guards,
                        rule_prefix: &format!("{rule_prefix}_create_{ai}"),
                    },
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

                let result = encode_step_chc_scoped(
                    chc,
                    action_ctx,
                    EncodeStepChcInput {
                        actions: &evt.body,
                        event_guard: &evt.guard,
                        rule_prefix: &format!("{rule_prefix}_cc_{target_sys}_{target_evt}"),
                        extra_guards: &cc_guards,
                    },
                    visited,
                    &local_terms,
                );
                visited.remove(&key);
                result?;
            }
            IRAction::ExprStmt { .. } => {
                // No state change — correct to not generate a rule.
            }
            IRAction::LetCrossCall {
                name,
                system: target_sys,
                command: target_evt,
                ..
            } => {
                let call_guards = top_level_action_guards(extra_guards, event_guard, &local_terms)?;
                let return_value = encode_macro_call_chc(
                    chc,
                    action_ctx,
                    MacroCallChcInput {
                        target_sys,
                        target_evt,
                        rule_prefix: &format!("{rule_prefix}_let_{ai}_{target_sys}_{target_evt}"),
                        guards: &call_guards,
                        local_terms: &local_terms,
                    },
                    visited,
                )?
                .ok_or_else(|| {
                    format!("macro-step binding requires `{target_sys}::{target_evt}` to return a value")
                })?;
                local_terms.insert(name.clone(), return_value);
            }
            IRAction::Match { scrutinee, arms } => {
                let match_guards =
                    top_level_action_guards(extra_guards, event_guard, &local_terms)?;
                let scrut = encode_action_match_scrutinee(
                    chc,
                    action_ctx,
                    ActionMatchScrutineeInput {
                        scrutinee,
                        rule_prefix,
                        action_index: ai,
                        guards: &match_guards,
                        local_terms: &local_terms,
                    },
                    visited,
                )?;
                for (arm_index, arm) in arms.iter().enumerate() {
                    let mut arm_guards = extra_guards.to_vec();
                    arm_guards.push(ic3_match_pattern_cond(&scrut, &arm.pattern, vctx)?);
                    let mut arm_locals = local_terms.clone();
                    for (name, term) in ic3_match_pattern_bindings(&scrut, &arm.pattern, vctx)? {
                        arm_locals.insert(name, term);
                    }
                    if let Some(guard) = &arm.guard {
                        arm_guards.push(encode_non_entity_guard_with_locals(guard, &arm_locals)?);
                    }
                    encode_step_chc_scoped(
                        chc,
                        action_ctx,
                        EncodeStepChcInput {
                            actions: &arm.body,
                            event_guard,
                            rule_prefix: &format!("{rule_prefix}_match_{ai}_arm{arm_index}"),
                            extra_guards: &arm_guards,
                        },
                        visited,
                        &arm_locals,
                    )?;
                }
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
#[allow(dead_code)]
pub(in crate::verify::ic3) fn encode_ops_chc(
    chc: &mut String,
    ctx: Ic3SystemActionCtx<'_>,
    input: EncodeOpsChcInput<'_>,
    visited: &mut HashSet<(String, String)>,
) -> Result<(), String> {
    encode_ops_chc_scoped(chc, ctx, input, visited, &HashMap::new())
}

fn encode_ops_chc_scoped(
    chc: &mut String,
    action_ctx: Ic3SystemActionCtx<'_>,
    input: EncodeOpsChcInput<'_>,
    visited: &mut HashSet<(String, String)>,
    local_terms: &HashMap<String, String>,
) -> Result<(), String> {
    let Ic3SystemActionCtx {
        entities,
        vctx,
        slots_per_entity,
        all_vars_str,
        all_systems,
    } = action_ctx;
    let EncodeOpsChcInput {
        ops,
        bound,
        rule_prefix,
        guards,
    } = input;
    let BoundActionSlot {
        entity: bound_entity,
        entity_name: bound_ent_name,
        slot: bound_slot,
        var: bound_var,
    } = bound;
    let mut local_terms = local_terms.clone();
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
                    action_ctx,
                    CreateChcInput {
                        entity_name: ent_name,
                        fields: create_fields,
                        guards,
                        rule_prefix: &format!("{rule_prefix}_create_{oi}"),
                    },
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
                let result = encode_step_chc_scoped(
                    chc,
                    action_ctx,
                    EncodeStepChcInput {
                        actions: &evt.body,
                        event_guard: &evt.guard,
                        rule_prefix: &format!("{rule_prefix}_cc_{oi}_{target_sys}_{target_evt}"),
                        extra_guards: guards,
                    },
                    visited,
                    &local_terms,
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
                    nested.push(wrap_action_locals(filter_smt, &local_terms));
                    encode_ops_chc_scoped(
                        chc,
                        action_ctx,
                        EncodeOpsChcInput {
                            ops: inner_ops,
                            bound: BoundActionSlot {
                                entity,
                                entity_name: ent_name,
                                slot,
                                var,
                            },
                            rule_prefix: &format!("{rule_prefix}_choose_{oi}_s{slot}"),
                            guards: &nested,
                        },
                        visited,
                        &local_terms,
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
                    encode_ops_chc_scoped(
                        chc,
                        action_ctx,
                        EncodeOpsChcInput {
                            ops: inner_ops,
                            bound: BoundActionSlot {
                                entity,
                                entity_name: ent_name,
                                slot,
                                var,
                            },
                            rule_prefix: &format!("{rule_prefix}_forall_{oi}_s{slot}"),
                            guards: &nested,
                        },
                        visited,
                        &local_terms,
                    )?;
                }
            }
            IRAction::ExprStmt { .. } => {
                // No state change — correct to skip.
            }
            IRAction::LetCrossCall {
                name,
                system: target_sys,
                command: target_evt,
                ..
            } => {
                let return_value = encode_macro_call_chc(
                    chc,
                    action_ctx,
                    MacroCallChcInput {
                        target_sys,
                        target_evt,
                        rule_prefix: &format!("{rule_prefix}_let_{oi}_{target_sys}_{target_evt}"),
                        guards,
                        local_terms: &local_terms,
                    },
                    visited,
                )?
                .ok_or_else(|| {
                    format!("macro-step binding requires `{target_sys}::{target_evt}` to return a value")
                })?;
                local_terms.insert(name.clone(), return_value);
            }
            IRAction::Match { scrutinee, arms } => {
                let scrut = encode_action_match_scrutinee(
                    chc,
                    action_ctx,
                    ActionMatchScrutineeInput {
                        scrutinee,
                        rule_prefix,
                        action_index: oi,
                        guards,
                        local_terms: &local_terms,
                    },
                    visited,
                )?;
                for (arm_index, arm) in arms.iter().enumerate() {
                    let mut arm_guards = guards.to_vec();
                    arm_guards.push(ic3_match_pattern_cond(&scrut, &arm.pattern, vctx)?);
                    let mut arm_locals = local_terms.clone();
                    for (name, term) in ic3_match_pattern_bindings(&scrut, &arm.pattern, vctx)? {
                        arm_locals.insert(name, term);
                    }
                    if let Some(guard) = &arm.guard {
                        arm_guards.push(encode_action_guard_with_locals(
                            guard,
                            bound_entity,
                            vctx,
                            bound_ent_name,
                            bound_slot,
                            &arm_locals,
                        )?);
                    }
                    encode_ops_chc_scoped(
                        chc,
                        action_ctx,
                        EncodeOpsChcInput {
                            ops: &arm.body,
                            bound,
                            rule_prefix: &format!("{rule_prefix}_match_{oi}_arm{arm_index}"),
                            guards: &arm_guards,
                        },
                        visited,
                        &arm_locals,
                    )?;
                }
            }
        }
    }
    Ok(())
}

fn top_level_action_guards(
    extra_guards: &[String],
    event_guard: &IRExpr,
    local_terms: &HashMap<String, String>,
) -> Result<Vec<String>, String> {
    let mut guards = extra_guards.to_vec();
    let evt_guard = encode_non_entity_guard_with_locals(event_guard, local_terms)?;
    if evt_guard != "true" {
        guards.push(evt_guard);
    }
    Ok(guards)
}

fn encode_macro_call_chc(
    chc: &mut String,
    ctx: Ic3SystemActionCtx<'_>,
    input: MacroCallChcInput<'_>,
    visited: &mut HashSet<(String, String)>,
) -> Result<Option<String>, String> {
    let Ic3SystemActionCtx {
        entities,
        vctx,
        slots_per_entity: _,
        all_vars_str: _,
        all_systems,
    } = ctx;
    let MacroCallChcInput {
        target_sys,
        target_evt,
        rule_prefix,
        guards,
        local_terms,
    } = input;
    let sys = all_systems
        .iter()
        .find(|s| s.name == *target_sys)
        .ok_or_else(|| format!("CrossCall target system {target_sys} not found"))?;
    let evt = sys
        .actions
        .iter()
        .find(|e| e.name == *target_evt)
        .ok_or_else(|| format!("CrossCall target event {target_sys}.{target_evt} not found"))?;

    let key = (target_sys.to_owned(), target_evt.to_owned());
    if !visited.insert(key.clone()) {
        return Err(format!(
            "cyclic CrossCall detected: {target_sys}.{target_evt}"
        ));
    }
    let result = encode_step_chc_scoped(
        chc,
        ctx,
        EncodeStepChcInput {
            actions: &evt.body,
            event_guard: &evt.guard,
            rule_prefix,
            extra_guards: guards,
        },
        visited,
        local_terms,
    );
    visited.remove(&key);
    result?;

    evt.return_expr
        .as_ref()
        .map(|expr| encode_macro_return_expr(expr, entities, vctx, local_terms))
        .transpose()
}

fn encode_action_match_scrutinee(
    chc: &mut String,
    ctx: Ic3SystemActionCtx<'_>,
    input: ActionMatchScrutineeInput<'_>,
    visited: &mut HashSet<(String, String)>,
) -> Result<String, String> {
    let ActionMatchScrutineeInput {
        scrutinee,
        rule_prefix,
        action_index,
        guards,
        local_terms,
    } = input;
    match scrutinee {
        crate::ir::types::IRActionMatchScrutinee::Var { name } => local_terms
            .get(name)
            .cloned()
            .ok_or_else(|| format!("macro-step match references unknown local `{name}`")),
        crate::ir::types::IRActionMatchScrutinee::CrossCall {
            system: target_sys,
            command: target_evt,
            ..
        } => {
            let returned = encode_macro_call_chc(
                chc,
                ctx,
                MacroCallChcInput {
                    target_sys,
                    target_evt,
                    rule_prefix: &format!(
                        "{rule_prefix}_match_{action_index}_call_{target_sys}_{target_evt}"
                    ),
                    guards,
                    local_terms,
                },
                visited,
            )?;
            returned
                .ok_or_else(|| "macro-step match requires a returned command outcome".to_owned())
        }
    }
}

fn encode_macro_return_expr(
    expr: &IRExpr,
    entities: &[&IREntity],
    vctx: &VerifyContext,
    local_terms: &HashMap<String, String>,
) -> Result<String, String> {
    let local_names = action_local_names(local_terms);
    let smt = if let Some(entity) = entities.first() {
        expr_to_smt_scoped(expr, entity, vctx, &local_names)?
    } else {
        let dummy = IREntity {
            name: "__Unit".to_owned(),
            fields: vec![],
            transitions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };
        expr_to_smt_scoped(expr, &dummy, vctx, &local_names)?
    };
    Ok(wrap_action_locals(smt, local_terms))
}

fn action_local_names(local_terms: &HashMap<String, String>) -> HashSet<String> {
    local_terms.keys().cloned().collect()
}

fn wrap_action_locals(smt: String, local_terms: &HashMap<String, String>) -> String {
    local_terms.iter().fold(smt, |acc, (name, term)| {
        format!("(let (({name} {term})) {acc})")
    })
}

fn encode_action_guard_with_locals(
    guard: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    ent_name: &str,
    slot: usize,
    local_terms: &HashMap<String, String>,
) -> Result<String, String> {
    let local_names = action_local_names(local_terms);
    let smt = guard_to_smt_sys_scoped(guard, entity, vctx, ent_name, slot, &local_names)?;
    Ok(wrap_action_locals(smt, local_terms))
}

fn encode_non_entity_guard_with_locals(
    guard: &IRExpr,
    local_terms: &HashMap<String, String>,
) -> Result<String, String> {
    let smt = match guard {
        IRExpr::Lit {
            value: LitVal::Bool { value },
            ..
        } => value.to_string(),
        IRExpr::Var { name, ty, .. } if *ty == IRType::Bool && local_terms.contains_key(name) => {
            name.clone()
        }
        _ => return encode_non_entity_guard(guard),
    };
    Ok(wrap_action_locals(smt, local_terms))
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
fn encode_create_chc(
    chc: &mut String,
    ctx: Ic3SystemActionCtx<'_>,
    input: CreateChcInput<'_>,
) -> Result<(), String> {
    let Ic3SystemActionCtx {
        entities,
        vctx,
        slots_per_entity,
        all_vars_str,
        ..
    } = ctx;
    let CreateChcInput {
        entity_name: create_ent_name,
        fields: create_fields,
        guards: extra_guards,
        rule_prefix,
    } = input;
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn local_non_entity_guards_accept_literals_and_bound_bool_vars_only() {
        let locals = HashMap::from([("ok".to_owned(), "true".to_owned())]);

        assert_eq!(
            encode_non_entity_guard_with_locals(&bool_lit(false), &locals)
                .expect("literal false guard"),
            "(let ((ok true)) false)"
        );
        assert_eq!(
            encode_non_entity_guard_with_locals(&bool_var("ok"), &locals)
                .expect("bound bool local guard"),
            "(let ((ok true)) ok)"
        );
        assert!(
            encode_non_entity_guard_with_locals(&bool_var("missing"), &locals).is_err(),
            "unbound bool variables are not valid non-entity guards"
        );
        assert!(
            encode_non_entity_guard_with_locals(&int_var("ok"), &locals).is_err(),
            "non-bool local variables are not valid guards"
        );
    }

    #[test]
    fn action_guards_with_locals_thread_local_names_into_entity_guard_encoding() {
        let entity = empty_entity("Order");
        let vctx = VerifyContext::from_ir(&empty_program());
        let locals = HashMap::from([("ok".to_owned(), "true".to_owned())]);

        let encoded = encode_action_guard_with_locals(
            &bool_var("ok"),
            &entity,
            &vctx,
            "Order",
            0,
            &locals,
        )
        .expect("local bool guard should encode through scoped guard path");

        assert_eq!(encoded, "(let ((ok true)) ok)");
        assert!(
            !encoded.contains("xyzzy"),
            "local action guards should use the encoded guard expression"
        );
    }

    #[test]
    fn create_chc_adds_previous_slot_guard_only_after_slot_zero() {
        let entity = empty_entity("Order");
        let vctx = VerifyContext::from_ir(&empty_program());
        let entities = [&entity];
        let slots = HashMap::from([("Order".to_owned(), 2_usize)]);
        let systems: [&IRSystem; 0] = [];
        let mut chc = String::new();

        encode_create_chc(
            &mut chc,
            Ic3SystemActionCtx {
                entities: &entities,
                vctx: &vctx,
                slots_per_entity: &slots,
                all_vars_str: "Order_0_active Order_1_active",
                all_systems: &systems,
            },
            CreateChcInput {
                entity_name: "Order",
                fields: &[],
                guards: &[],
                rule_prefix: "create_test",
            },
        )
        .expect("create rules");

        let slot0 = rule_line(&chc, "create_test_Order_s0");
        assert!(
            !slot0.contains("Order_-1_active"),
            "slot-zero create rule must not reference a previous slot, got: {slot0}"
        );
        let slot1 = rule_line(&chc, "create_test_Order_s1");
        assert!(
            slot1.contains("(not Order_1_active) Order_0_active)"),
            "slot-one create rule should require slot one inactive and slot zero active, got: {slot1}"
        );
    }

    fn bool_lit(value: bool) -> IRExpr {
        IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value },
            span: None,
        }
    }

    fn bool_var(name: &str) -> IRExpr {
        IRExpr::Var {
            name: name.to_owned(),
            ty: IRType::Bool,
            span: None,
        }
    }

    fn int_var(name: &str) -> IRExpr {
        IRExpr::Var {
            name: name.to_owned(),
            ty: IRType::Int,
            span: None,
        }
    }

    fn empty_entity(name: &str) -> IREntity {
        IREntity {
            name: name.to_owned(),
            fields: vec![],
            transitions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        }
    }

    fn empty_program() -> IRProgram {
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

    fn rule_line<'a>(chc: &'a str, rule_name: &str) -> &'a str {
        chc.lines()
            .find(|line| line.contains(rule_name))
            .unwrap_or_else(|| panic!("expected CHC rule `{rule_name}` in:\n{chc}"))
    }
}
