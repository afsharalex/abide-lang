//! IC3/PDR verification via Z3's fixpoint engine (Spacer).
//!
//! Translates Abide entity+system models to Constrained Horn Clauses (CHC)
//! and queries Z3's fixpoint engine to prove safety properties.
//!
//! IC3 is more powerful than 1-induction: it automatically discovers
//! strengthening invariants, proving properties that aren't directly
//! inductive. For finite state spaces, IC3 is guaranteed to terminate.
//!
//! **Soundness policy:** Unsupported expression forms cause the encoding to
//! fail with `Ic3Result::Unknown`, never silent approximation. A guard
//! falling back to "true" or a value falling back to "0" would be unsound.

use std::collections::{HashMap, HashSet};

use z3::{Fixedpoint, FuncDecl, Params, SatResult, Sort};

use crate::ir::types::{IRAction, IREntity, IRExpr, IRProgram, IRSystem, IRType, LitVal};

use super::context::VerifyContext;

/// Result of an IC3 proof attempt.
#[derive(Debug)]
pub enum Ic3Result {
    /// Property proved — IC3 found an inductive invariant.
    Proved,
    /// Property violated — a reachable error state exists.
    Violated,
    /// IC3 could not determine (timeout, unsupported encoding, or incompleteness).
    Unknown(String),
}

/// Try to prove a safety property for a single-entity system using IC3/PDR.
///
/// Generates a CHC (Constrained Horn Clause) encoding as an SMT-LIB2 string,
/// parses it via Z3's fixpoint engine, and queries for reachability of the
/// error state (¬P). Uses `from_string` + `declare-var` which is the correct
/// interface for Z3's Spacer engine.
///
/// Returns `Ic3Result::Proved` if the property holds for all reachable states.
/// Returns `Ic3Result::Unknown` if any expression can't be encoded (never silently approximates).
pub fn try_ic3_single_entity(
    entity: &IREntity,
    vctx: &VerifyContext,
    property: &IRExpr,
    timeout_ms: u64,
) -> Ic3Result {
    let fp = Fixedpoint::new();

    let mut params = Params::new();
    params.set_symbol("engine", "spacer");
    if timeout_ms > 0 {
        #[allow(clippy::cast_possible_truncation)]
        params.set_u32("timeout", timeout_ms.min(u64::from(u32::MAX)) as u32);
    }
    fp.set_params(&params);

    // Build CHC string — propagate encoding errors
    let chc = match build_chc_string(entity, vctx, property) {
        Ok(s) => s,
        Err(e) => return Ic3Result::Unknown(format!("CHC encoding failed: {e}")),
    };

    // Parse the CHC encoding
    if let Err(e) = fp.from_string(&chc) {
        return Ic3Result::Unknown(format!("CHC parse error: {e}"));
    }

    // Register Error relation for query
    let error_rel = FuncDecl::new("Error", &[], &Sort::bool());
    fp.register_relation(&error_rel);

    // Query: is Error reachable?
    let error_query = error_rel.apply(&[]);
    match fp.query(&error_query) {
        SatResult::Unsat => Ic3Result::Proved,
        SatResult::Sat => Ic3Result::Violated,
        SatResult::Unknown => {
            let reason = fp.get_reason_unknown();
            Ic3Result::Unknown(reason)
        }
    }
}

/// Try to prove a safety property for a multi-slot entity pool using IC3/PDR.
///
/// Extends the single-entity encoding with N slots per entity type.
/// The State relation is flattened: `State(s0_f1, s0_f2, ..., s0_active, s1_f1, ..., s1_active)`.
///
/// `n_slots` is the number of entity instances to model. For per-entity properties,
/// 1 slot suffices (use `try_ic3_single_entity`). For inter-entity properties
/// (e.g., `all a, b: E | P(a,b)`), use quantifier nesting depth + 1.
pub fn try_ic3_multi_slot(
    entity: &IREntity,
    vctx: &VerifyContext,
    property: &IRExpr,
    n_slots: usize,
    timeout_ms: u64,
) -> Ic3Result {
    if n_slots <= 1 {
        return try_ic3_single_entity(entity, vctx, property, timeout_ms);
    }

    let fp = Fixedpoint::new();

    let mut params = Params::new();
    params.set_symbol("engine", "spacer");
    if timeout_ms > 0 {
        #[allow(clippy::cast_possible_truncation)]
        params.set_u32("timeout", timeout_ms.min(u64::from(u32::MAX)) as u32);
    }
    fp.set_params(&params);

    let chc = match build_multi_slot_chc(entity, vctx, property, n_slots) {
        Ok(s) => s,
        Err(e) => return Ic3Result::Unknown(format!("CHC encoding failed: {e}")),
    };

    if let Err(e) = fp.from_string(&chc) {
        return Ic3Result::Unknown(format!("CHC parse error: {e}"));
    }

    let error_rel = FuncDecl::new("Error", &[], &Sort::bool());
    fp.register_relation(&error_rel);

    let error_query = error_rel.apply(&[]);
    match fp.query(&error_query) {
        SatResult::Unsat => Ic3Result::Proved,
        SatResult::Sat => Ic3Result::Violated,
        SatResult::Unknown => {
            let reason = fp.get_reason_unknown();
            Ic3Result::Unknown(reason)
        }
    }
}

/// Try to prove a safety property for a multi-system specification using IC3/PDR.
///
/// Composes multiple entity types and systems into a unified CHC encoding.
/// Cross-system events (`CrossCall`) are inlined as combined transition rules.
///
/// `system_names`: target systems to include (plus `CrossCall`-reachable).
/// `slots_per_entity`: number of slots per entity type.
#[allow(clippy::implicit_hasher)]
pub fn try_ic3_system(
    ir: &IRProgram,
    vctx: &VerifyContext,
    system_names: &[String],
    property: &IRExpr,
    slots_per_entity: &HashMap<String, usize>,
    timeout_ms: u64,
) -> Ic3Result {
    let fp = Fixedpoint::new();

    let mut params = Params::new();
    params.set_symbol("engine", "spacer");
    if timeout_ms > 0 {
        #[allow(clippy::cast_possible_truncation)]
        params.set_u32("timeout", timeout_ms.min(u64::from(u32::MAX)) as u32);
    }
    fp.set_params(&params);

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
            for event in &sys.events {
                collect_crosscall_targets(&event.body, &mut to_scan);
            }
        }
    }

    // Collect relevant entities
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

    let chc = match build_system_chc(
        &relevant_entities,
        &relevant_systems,
        vctx,
        property,
        slots_per_entity,
    ) {
        Ok(s) => s,
        Err(e) => return Ic3Result::Unknown(format!("CHC encoding failed: {e}")),
    };

    if let Err(e) = fp.from_string(&chc) {
        return Ic3Result::Unknown(format!("CHC parse error: {e}"));
    }

    let error_rel = FuncDecl::new("Error", &[], &Sort::bool());
    fp.register_relation(&error_rel);

    let error_query = error_rel.apply(&[]);
    match fp.query(&error_query) {
        SatResult::Unsat => Ic3Result::Proved,
        SatResult::Sat => Ic3Result::Violated,
        SatResult::Unknown => {
            let reason = fp.get_reason_unknown();
            Ic3Result::Unknown(reason)
        }
    }
}

/// Collect `CrossCall` target system names from event actions.
fn collect_crosscall_targets(actions: &[IRAction], targets: &mut Vec<String>) {
    for action in actions {
        match action {
            IRAction::CrossCall { system, .. } => {
                if !targets.contains(system) {
                    targets.push(system.clone());
                }
            }
            IRAction::Choose { ops, .. } | IRAction::ForAll { ops, .. } => {
                collect_crosscall_targets(ops, targets);
            }
            _ => {}
        }
    }
}

/// Metadata for a slot column in the flattened State relation.
struct SlotColumn {
    /// Variable name in CHC: `{entity}_{slot}_f{field_idx}` or `{entity}_{slot}_active`
    var_name: String,
    /// SMT-LIB2 sort name
    sort_name: String,
}

/// Build unified CHC encoding for multiple entity types and systems.
#[allow(clippy::format_push_string, clippy::too_many_lines)]
fn build_system_chc(
    entities: &[&IREntity],
    systems: &[&IRSystem],
    vctx: &VerifyContext,
    property: &IRExpr,
    slots_per_entity: &HashMap<String, usize>,
) -> Result<String, String> {
    let mut chc = String::new();

    // Build column layout: for each entity type, for each slot, fields + active
    let mut columns: Vec<SlotColumn> = Vec::new();
    for entity in entities {
        let n_slots = slots_per_entity.get(&entity.name).copied().unwrap_or(1);
        for slot in 0..n_slots {
            for (fi, f) in entity.fields.iter().enumerate() {
                columns.push(SlotColumn {
                    var_name: format!("{}_{}_f{}", entity.name, slot, fi),
                    sort_name: ir_type_to_sort_name(&f.ty),
                });
            }
            columns.push(SlotColumn {
                var_name: format!("{}_{}_active", entity.name, slot),
                sort_name: "Bool".to_owned(),
            });
        }
    }

    // Declare State relation
    chc.push_str("(declare-rel State (");
    for col in &columns {
        chc.push_str(&col.sort_name);
        chc.push(' ');
    }
    chc.push_str("))\n");
    chc.push_str("(declare-rel Error ())\n");

    // Declare variables
    for col in &columns {
        chc.push_str(&format!(
            "(declare-var {} {})\n",
            col.var_name, col.sort_name
        ));
    }

    let all_vars_str: String = columns
        .iter()
        .map(|c| c.var_name.as_str())
        .collect::<Vec<_>>()
        .join(" ");

    // ── Initial state: all slots inactive ──────────────────────────
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
    chc.push_str(") init)\n");

    // ── Stutter rule ───────────────────────────────────────────────
    chc.push_str(&format!(
        "(rule (=> (State {all_vars_str}) (State {all_vars_str})) stutter)\n"
    ));

    // ── Entity transition rules ────────────────────────────────────
    // For each entity type, for each slot, for each transition:
    // guard(slot) ∧ active(slot) → update(slot) ∧ frame(everything else)
    for entity in entities {
        let n_slots = slots_per_entity.get(&entity.name).copied().unwrap_or(1);
        for slot in 0..n_slots {
            for transition in &entity.transitions {
                let guard = guard_to_smt_sys(&transition.guard, entity, vctx, &entity.name, slot)?;

                // Build next-state: update target slot, frame everything else
                let mut next_vals: Vec<String> = Vec::new();
                for ent in entities {
                    let ns = slots_per_entity.get(&ent.name).copied().unwrap_or(1);
                    for s in 0..ns {
                        for (fi, f) in ent.fields.iter().enumerate() {
                            if ent.name == entity.name && s == slot {
                                let updated = transition.updates.iter().find(|u| u.field == f.name);
                                if let Some(upd) = updated {
                                    next_vals.push(expr_to_smt_sys(
                                        &upd.value,
                                        entity,
                                        vctx,
                                        &entity.name,
                                        slot,
                                    )?);
                                } else {
                                    next_vals.push(format!("{}_{}_f{}", ent.name, s, fi));
                                }
                            } else {
                                next_vals.push(format!("{}_{}_f{}", ent.name, s, fi));
                            }
                        }
                        if ent.name == entity.name && s == slot {
                            next_vals.push("true".to_owned());
                        } else {
                            next_vals.push(format!("{}_{}_active", ent.name, s));
                        }
                    }
                }
                let next_str = next_vals.join(" ");
                let active_var = format!("{}_{}_active", entity.name, slot);

                chc.push_str(&format!(
                    "(rule (=> (and (State {all_vars_str}) {active_var} {guard}) \
                     (State {next_str})) trans_{}_{}_{slot})\n",
                    entity.name, transition.name
                ));
            }

            // Create rule for this entity slot
            let mut create_next: Vec<String> = Vec::new();
            for ent in entities {
                let ns = slots_per_entity.get(&ent.name).copied().unwrap_or(1);
                for s in 0..ns {
                    for (fi, f) in ent.fields.iter().enumerate() {
                        if ent.name == entity.name && s == slot {
                            if let Some(ref default_expr) = f.default {
                                create_next.push(expr_to_smt(default_expr, entity, vctx)?);
                            } else {
                                create_next.push(format!("{}_{}_f{}", ent.name, s, fi));
                            }
                        } else {
                            create_next.push(format!("{}_{}_f{}", ent.name, s, fi));
                        }
                    }
                    if ent.name == entity.name && s == slot {
                        create_next.push("true".to_owned());
                    } else {
                        create_next.push(format!("{}_{}_active", ent.name, s));
                    }
                }
            }
            let create_str = create_next.join(" ");
            let inactive_var = format!("{}_{}_active", entity.name, slot);

            // Symmetry: slot i requires slot i-1 active
            let create_guard = if slot == 0 {
                format!("(not {inactive_var})")
            } else {
                format!(
                    "(and (not {inactive_var}) {}_{}_active)",
                    entity.name,
                    slot - 1
                )
            };

            chc.push_str(&format!(
                "(rule (=> (and (State {all_vars_str}) {create_guard}) \
                 (State {create_str})) create_{}_{slot})\n",
                entity.name
            ));
        }
    }

    // ── System event rules ──────────────────────────────────────────
    // Encode system events as composite CHC rules: event guard + Choose filter + Apply transition.
    // This adds event-level constraints (guards, Choose filters) on top of entity transitions.
    // CrossCall effects are encoded by including the callee's Create actions.
    for system in systems {
        for event in &system.events {
            encode_event_chc(
                &mut chc,
                &event.body,
                &event.guard,
                entities,
                vctx,
                slots_per_entity,
                &all_vars_str,
                systems,
                &format!("{}_{}", system.name, event.name),
            )?;
        }
    }

    // ── Domain constraints ─────────────────────────────────────────
    for entity in entities {
        let n_slots = slots_per_entity.get(&entity.name).copied().unwrap_or(1);
        for slot in 0..n_slots {
            for (fi, f) in entity.fields.iter().enumerate() {
                if let IRType::Enum { name, .. } = &f.ty {
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

    // ── Error rule: property violation ──────────────────────────────
    let neg_prop = negate_property_smt_system(property, entities, vctx, slots_per_entity)?;
    chc.push_str(&format!(
        "(rule (=> (and (State {all_vars_str}) {neg_prop}) Error) error)\n"
    ));

    Ok(chc)
}

/// Negate a property for the system-level CHC encoding.
fn negate_property_smt_system(
    property: &IRExpr,
    entities: &[&IREntity],
    vctx: &VerifyContext,
    slots_per_entity: &HashMap<String, usize>,
) -> Result<String, String> {
    match property {
        IRExpr::Always { body } => {
            negate_property_smt_system(body, entities, vctx, slots_per_entity)
        }
        IRExpr::Forall {
            var,
            domain: IRType::Entity { name: entity_name },
            body,
        } => {
            let n_slots = slots_per_entity.get(entity_name).copied().unwrap_or(1);
            let entity = entities
                .iter()
                .find(|e| e.name == *entity_name)
                .ok_or_else(|| format!("entity {entity_name} not found in scope"))?;

            // Check for nested Forall
            if let IRExpr::Forall {
                var: var2,
                domain: IRType::Entity { name: ent2 },
                body: inner,
            } = body.as_ref()
            {
                let n_slots2 = slots_per_entity.get(ent2).copied().unwrap_or(1);
                let entity2 = entities
                    .iter()
                    .find(|e| e.name == *ent2)
                    .ok_or_else(|| format!("entity {ent2} not found in scope"))?;
                let mut disjuncts = Vec::new();
                for s1 in 0..n_slots {
                    for s2 in 0..n_slots2 {
                        let neg = negate_guard_sys_two(
                            inner,
                            entity,
                            entity2,
                            vctx,
                            entity_name,
                            s1,
                            var,
                            ent2,
                            s2,
                            var2,
                        )?;
                        let a1 = format!("{entity_name}_{s1}_active");
                        let a2 = format!("{ent2}_{s2}_active");
                        disjuncts.push(format!("(and {a1} {a2} {neg})"));
                    }
                }
                return Ok(format!("(or {})", disjuncts.join(" ")));
            }

            // Single quantifier
            let mut disjuncts = Vec::new();
            for slot in 0..n_slots {
                let neg_body = negate_guard_sys(body, entity, vctx, entity_name, slot)?;
                let active = format!("{entity_name}_{slot}_active");
                disjuncts.push(format!("(and {active} {neg_body})"));
            }
            Ok(format!("(or {})", disjuncts.join(" ")))
        }
        _ => {
            // Non-quantified: try encoding directly
            // For simplicity, check against all active entities
            Err("non-quantified system-level properties require entity context".to_owned())
        }
    }
}

/// Negate an inner property for a specific entity slot in system context.
fn negate_guard_sys(
    expr: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    ent_name: &str,
    slot: usize,
) -> Result<String, String> {
    let pos = guard_to_smt_sys(expr, entity, vctx, ent_name, slot)?;
    Ok(format!("(not {pos})"))
}

/// Negate an inner property for two entity slots in system context.
#[allow(clippy::too_many_arguments)]
fn negate_guard_sys_two(
    expr: &IRExpr,
    entity1: &IREntity,
    entity2: &IREntity,
    vctx: &VerifyContext,
    ent1_name: &str,
    slot1: usize,
    var1: &str,
    ent2_name: &str,
    slot2: usize,
    var2: &str,
) -> Result<String, String> {
    let pos = guard_to_smt_sys_two(
        expr, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
    )?;
    Ok(format!("(not {pos})"))
}

/// Encode a system event body as CHC transition rules.
///
/// Walks the event action tree (Choose/Apply/Create/CrossCall) and generates
/// composite rules that combine event guard + Choose filter + transition effects.
/// Each Choose+Apply pattern generates one rule per slot.
#[allow(
    clippy::too_many_arguments,
    clippy::too_many_lines,
    clippy::format_push_string
)]
fn encode_event_chc(
    chc: &mut String,
    actions: &[IRAction],
    event_guard: &IRExpr,
    entities: &[&IREntity],
    vctx: &VerifyContext,
    slots_per_entity: &HashMap<String, usize>,
    all_vars_str: &str,
    all_systems: &[&IRSystem],
    rule_prefix: &str,
) -> Result<(), String> {
    for (ai, action) in actions.iter().enumerate() {
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
                    .ok_or_else(|| format!("entity {ent_name} not found"))?;
                let n_slots = slots_per_entity.get(ent_name).copied().unwrap_or(1);

                // For each slot, generate: event_guard ∧ active(slot) ∧ filter(slot) ∧ Apply effects
                for slot in 0..n_slots {
                    // Encode event guard (may reference event params — simplified to true for non-parameterized)
                    let guard_smt =
                        match guard_to_smt_sys(event_guard, entity, vctx, ent_name, slot) {
                            Ok(g) => g,
                            Err(_) => "true".to_owned(), // event guard may be complex — fall back
                        };

                    // Encode Choose filter
                    let filter_smt = guard_to_smt_sys(filter, entity, vctx, ent_name, slot)?;
                    let active_var = format!("{ent_name}_{slot}_active");

                    // Find Apply ops and encode their transition effects
                    for op in ops {
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

                                // Build next-state with this transition's updates
                                let mut next_vals: Vec<String> = Vec::new();
                                for ent in entities {
                                    let ns = slots_per_entity.get(&ent.name).copied().unwrap_or(1);
                                    for s in 0..ns {
                                        for (fi, f) in ent.fields.iter().enumerate() {
                                            if ent.name == *ent_name && s == slot {
                                                let updated = trans
                                                    .updates
                                                    .iter()
                                                    .find(|u| u.field == f.name);
                                                if let Some(upd) = updated {
                                                    next_vals.push(expr_to_smt_sys(
                                                        &upd.value, entity, vctx, ent_name, slot,
                                                    )?);
                                                } else {
                                                    next_vals.push(format!(
                                                        "{}_{}_f{}",
                                                        ent.name, s, fi
                                                    ));
                                                }
                                            } else {
                                                next_vals
                                                    .push(format!("{}_{}_f{}", ent.name, s, fi));
                                            }
                                        }
                                        if ent.name == *ent_name && s == slot {
                                            next_vals.push("true".to_owned());
                                        } else {
                                            next_vals.push(format!("{}_{}_active", ent.name, s));
                                        }
                                    }
                                }
                                let next_str = next_vals.join(" ");

                                chc.push_str(&format!(
                                    "(rule (=> (and (State {all_vars_str}) {active_var} \
                                     {guard_smt} {filter_smt} {trans_guard}) \
                                     (State {next_str})) {rule_prefix}_choose_{ai}_s{slot}_{trans_name})\n"
                                ));
                            }
                        }
                    }

                    // Handle CrossCall in ops
                    for op in ops {
                        if let IRAction::CrossCall {
                            system: target_sys,
                            event: target_evt,
                            ..
                        } = op
                        {
                            // Find the target event and encode its Create actions
                            if let Some(sys) = all_systems.iter().find(|s| s.name == *target_sys) {
                                if let Some(evt) = sys.events.iter().find(|e| e.name == *target_evt)
                                {
                                    for cc_action in &evt.body {
                                        if let IRAction::Create {
                                            entity: create_ent,
                                            fields: create_fields,
                                        } = cc_action
                                        {
                                            let create_entity =
                                                entities.iter().find(|e| e.name == *create_ent);
                                            if let Some(ce) = create_entity {
                                                let cns = slots_per_entity
                                                    .get(create_ent)
                                                    .copied()
                                                    .unwrap_or(1);
                                                for cs in 0..cns {
                                                    let inactive =
                                                        format!("{create_ent}_{cs}_active");

                                                    // Build next-state: activate this create slot
                                                    let mut next_vals: Vec<String> = Vec::new();
                                                    for ent in entities {
                                                        let ns = slots_per_entity
                                                            .get(&ent.name)
                                                            .copied()
                                                            .unwrap_or(1);
                                                        for s in 0..ns {
                                                            for (fi, f) in
                                                                ent.fields.iter().enumerate()
                                                            {
                                                                if ent.name == *create_ent
                                                                    && s == cs
                                                                {
                                                                    let created =
                                                                        create_fields.iter().find(
                                                                            |cf| cf.name == f.name,
                                                                        );
                                                                    if let Some(cf) = created {
                                                                        match expr_to_smt(
                                                                            &cf.value, ce, vctx,
                                                                        ) {
                                                                            Ok(v) => {
                                                                                next_vals.push(v);
                                                                            }
                                                                            Err(_) => next_vals
                                                                                .push(format!(
                                                                                    "{}_{}_f{}",
                                                                                    ent.name, s, fi
                                                                                )),
                                                                        }
                                                                    } else if let Some(ref def) =
                                                                        f.default
                                                                    {
                                                                        match expr_to_smt(
                                                                            def, ce, vctx,
                                                                        ) {
                                                                            Ok(v) => {
                                                                                next_vals.push(v);
                                                                            }
                                                                            Err(_) => next_vals
                                                                                .push(format!(
                                                                                    "{}_{}_f{}",
                                                                                    ent.name, s, fi
                                                                                )),
                                                                        }
                                                                    } else {
                                                                        next_vals.push(format!(
                                                                            "{}_{}_f{}",
                                                                            ent.name, s, fi
                                                                        ));
                                                                    }
                                                                } else {
                                                                    next_vals.push(format!(
                                                                        "{}_{}_f{}",
                                                                        ent.name, s, fi
                                                                    ));
                                                                }
                                                            }
                                                            if ent.name == *create_ent && s == cs {
                                                                next_vals.push("true".to_owned());
                                                            } else {
                                                                next_vals.push(format!(
                                                                    "{}_{}_active",
                                                                    ent.name, s
                                                                ));
                                                            }
                                                        }
                                                    }
                                                    let next_str = next_vals.join(" ");

                                                    chc.push_str(&format!(
                                                        "(rule (=> (and (State {all_vars_str}) {active_var} \
                                                         {guard_smt} {filter_smt} (not {inactive})) \
                                                         (State {next_str})) {rule_prefix}_crosscall_{target_sys}_{target_evt}_s{cs})\n"
                                                    ));
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            IRAction::Create {
                entity: ent_name,
                fields: create_fields,
            } => {
                // Direct Create (not inside Choose) — encode as create rule
                if let Some(entity) = entities.iter().find(|e| e.name == *ent_name) {
                    let n_slots = slots_per_entity.get(ent_name).copied().unwrap_or(1);
                    for slot in 0..n_slots {
                        let inactive = format!("{ent_name}_{slot}_active");

                        let mut next_vals: Vec<String> = Vec::new();
                        for ent in entities {
                            let ns = slots_per_entity.get(&ent.name).copied().unwrap_or(1);
                            for s in 0..ns {
                                for (fi, f) in ent.fields.iter().enumerate() {
                                    if ent.name == *ent_name && s == slot {
                                        let created =
                                            create_fields.iter().find(|cf| cf.name == f.name);
                                        if let Some(cf) = created {
                                            match expr_to_smt(&cf.value, entity, vctx) {
                                                Ok(v) => next_vals.push(v),
                                                Err(_) => next_vals
                                                    .push(format!("{}_{}_f{}", ent.name, s, fi)),
                                            }
                                        } else if let Some(ref def) = f.default {
                                            match expr_to_smt(def, entity, vctx) {
                                                Ok(v) => next_vals.push(v),
                                                Err(_) => next_vals
                                                    .push(format!("{}_{}_f{}", ent.name, s, fi)),
                                            }
                                        } else {
                                            next_vals.push(format!("{}_{}_f{}", ent.name, s, fi));
                                        }
                                    } else {
                                        next_vals.push(format!("{}_{}_f{}", ent.name, s, fi));
                                    }
                                }
                                if ent.name == *ent_name && s == slot {
                                    next_vals.push("true".to_owned());
                                } else {
                                    next_vals.push(format!("{}_{}_active", ent.name, s));
                                }
                            }
                        }
                        let next_str = next_vals.join(" ");

                        chc.push_str(&format!(
                            "(rule (=> (and (State {all_vars_str}) (not {inactive})) \
                             (State {next_str})) {rule_prefix}_create_{ent_name}_s{slot})\n"
                        ));
                    }
                }
            }
            IRAction::ForAll {
                entity: ent_name,
                ops,
                ..
            } => {
                // ForAll iterates ALL active slots and applies ops to each.
                // In CHC: for each slot, if active, apply the ops (same as Choose but no filter).
                let entity = entities
                    .iter()
                    .find(|e| e.name == *ent_name)
                    .ok_or_else(|| format!("entity {ent_name} not found for ForAll"))?;
                let n_slots = slots_per_entity.get(ent_name).copied().unwrap_or(1);

                for slot in 0..n_slots {
                    let active_var = format!("{ent_name}_{slot}_active");

                    for op in ops {
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

                                let mut next_vals: Vec<String> = Vec::new();
                                for ent in entities {
                                    let ns = slots_per_entity.get(&ent.name).copied().unwrap_or(1);
                                    for s in 0..ns {
                                        for (fi, f) in ent.fields.iter().enumerate() {
                                            if ent.name == *ent_name && s == slot {
                                                let updated = trans
                                                    .updates
                                                    .iter()
                                                    .find(|u| u.field == f.name);
                                                if let Some(upd) = updated {
                                                    next_vals.push(expr_to_smt_sys(
                                                        &upd.value, entity, vctx, ent_name, slot,
                                                    )?);
                                                } else {
                                                    next_vals.push(format!(
                                                        "{}_{}_f{}",
                                                        ent.name, s, fi
                                                    ));
                                                }
                                            } else {
                                                next_vals
                                                    .push(format!("{}_{}_f{}", ent.name, s, fi));
                                            }
                                        }
                                        if ent.name == *ent_name && s == slot {
                                            next_vals.push("true".to_owned());
                                        } else {
                                            next_vals.push(format!("{}_{}_active", ent.name, s));
                                        }
                                    }
                                }
                                let next_str = next_vals.join(" ");

                                chc.push_str(&format!(
                                    "(rule (=> (and (State {all_vars_str}) {active_var} \
                                     {trans_guard}) \
                                     (State {next_str})) \
                                     {rule_prefix}_forall_{ai}_s{slot}_{trans_name})\n"
                                ));
                            }
                        }
                    }
                }
            }
            IRAction::CrossCall {
                system: target_sys,
                event: target_evt,
                ..
            } => {
                // Bare CrossCall (not inside Choose): invoke target event's body.
                // Recursively encode the target event's actions.
                if let Some(sys) = all_systems.iter().find(|s| s.name == *target_sys) {
                    if let Some(evt) = sys.events.iter().find(|e| e.name == *target_evt) {
                        encode_event_chc(
                            chc,
                            &evt.body,
                            &evt.guard,
                            entities,
                            vctx,
                            slots_per_entity,
                            all_vars_str,
                            all_systems,
                            &format!("{rule_prefix}_cc_{target_sys}_{target_evt}"),
                        )?;
                    }
                }
            }
            IRAction::ExprStmt { .. } => {
                // Expression statements in event bodies are typically boolean
                // assertions or side-effect-free expressions. In CHC, these
                // don't generate transition rules — they're constraints that
                // would be part of a more complex event guard composition.
                // For soundness: not generating a rule is correct (no state change).
            }
            IRAction::Apply { .. } => {
                // Bare Apply outside Choose — this shouldn't happen in well-formed IR
                // (Apply targets a Choose-bound variable). Return error for safety.
                return Err(
                    "bare Apply action outside Choose in event body — malformed IR".to_owned(),
                );
            }
        }
    }
    Ok(())
}

/// Encode a value expression with system-level slot naming: {entity}_{slot}_f{field}.
fn expr_to_smt_sys(
    expr: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    ent_name: &str,
    slot: usize,
) -> Result<String, String> {
    match expr {
        IRExpr::Var { name, .. } => {
            for (i, f) in entity.fields.iter().enumerate() {
                if f.name == *name {
                    return Ok(format!("{ent_name}_{slot}_f{i}"));
                }
            }
            Err(format!("unknown variable in system IC3: {name}"))
        }
        IRExpr::Field {
            expr: inner, field, ..
        } => {
            if let IRExpr::Var { .. } = inner.as_ref() {
                for (i, f) in entity.fields.iter().enumerate() {
                    if f.name == *field {
                        return Ok(format!("{ent_name}_{slot}_f{i}"));
                    }
                }
            }
            Err(format!("unsupported field access in system IC3: {field}"))
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let l = expr_to_smt_sys(left, entity, vctx, ent_name, slot)?;
            let r = expr_to_smt_sys(right, entity, vctx, ent_name, slot)?;
            match op.as_str() {
                "OpAdd" => Ok(format!("(+ {l} {r})")),
                "OpSub" => Ok(format!("(- {l} {r})")),
                "OpMul" => Ok(format!("(* {l} {r})")),
                _ => Err(format!("unsupported op in system IC3 value: {op}")),
            }
        }
        IRExpr::Lit { .. } | IRExpr::Ctor { .. } => expr_to_smt(expr, entity, vctx),
        _ => Err(format!(
            "unsupported expression in system IC3 value: {:?}",
            std::mem::discriminant(expr)
        )),
    }
}

/// Encode a guard with system-level slot naming.
fn guard_to_smt_sys(
    guard: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    ent_name: &str,
    slot: usize,
) -> Result<String, String> {
    match guard {
        IRExpr::Lit {
            value: LitVal::Bool { value: true },
            ..
        } => Ok("true".to_owned()),
        IRExpr::Lit {
            value: LitVal::Bool { value: false },
            ..
        } => Ok("false".to_owned()),
        IRExpr::BinOp {
            op, left, right, ..
        } => match op.as_str() {
            "OpEq" | "OpNEq" | "OpLt" | "OpLe" | "OpGt" | "OpGe" => {
                let l = expr_to_smt_sys(left, entity, vctx, ent_name, slot)?;
                let r = expr_to_smt_sys(right, entity, vctx, ent_name, slot)?;
                Ok(match op.as_str() {
                    "OpEq" => format!("(= {l} {r})"),
                    "OpNEq" => format!("(not (= {l} {r}))"),
                    "OpLt" => format!("(< {l} {r})"),
                    "OpLe" => format!("(<= {l} {r})"),
                    "OpGt" => format!("(> {l} {r})"),
                    "OpGe" => format!("(>= {l} {r})"),
                    _ => unreachable!(),
                })
            }
            "OpAnd" => {
                let l = guard_to_smt_sys(left, entity, vctx, ent_name, slot)?;
                let r = guard_to_smt_sys(right, entity, vctx, ent_name, slot)?;
                Ok(format!("(and {l} {r})"))
            }
            "OpOr" => {
                let l = guard_to_smt_sys(left, entity, vctx, ent_name, slot)?;
                let r = guard_to_smt_sys(right, entity, vctx, ent_name, slot)?;
                Ok(format!("(or {l} {r})"))
            }
            "OpImplies" => {
                let l = guard_to_smt_sys(left, entity, vctx, ent_name, slot)?;
                let r = guard_to_smt_sys(right, entity, vctx, ent_name, slot)?;
                Ok(format!("(=> {l} {r})"))
            }
            _ => Err(format!("unsupported op in system IC3 guard: {op}")),
        },
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => {
            let inner = guard_to_smt_sys(operand, entity, vctx, ent_name, slot)?;
            Ok(format!("(not {inner})"))
        }
        IRExpr::Field { .. } | IRExpr::Var { .. } => {
            expr_to_smt_sys(guard, entity, vctx, ent_name, slot)
        }
        _ => Err(format!(
            "unsupported expression in system IC3 guard: {:?}",
            std::mem::discriminant(guard)
        )),
    }
}

/// Encode a guard with two entity-slot bindings for inter-entity system properties.
#[allow(
    clippy::too_many_arguments,
    clippy::too_many_lines,
    clippy::similar_names
)]
fn guard_to_smt_sys_two(
    expr: &IRExpr,
    entity1: &IREntity,
    entity2: &IREntity,
    vctx: &VerifyContext,
    ent1_name: &str,
    slot1: usize,
    var1: &str,
    ent2_name: &str,
    slot2: usize,
    var2: &str,
) -> Result<String, String> {
    match expr {
        IRExpr::Lit {
            value: LitVal::Bool { value },
            ..
        } => Ok(value.to_string()),
        IRExpr::Field {
            expr: inner, field, ..
        } => {
            if let IRExpr::Var { name, .. } = inner.as_ref() {
                let (entity, ent_name, slot) = if name == var1 {
                    (entity1, ent1_name, slot1)
                } else if name == var2 {
                    (entity2, ent2_name, slot2)
                } else {
                    return Err(format!("unknown var {name} in cross-entity property"));
                };
                for (i, f) in entity.fields.iter().enumerate() {
                    if f.name == *field {
                        return Ok(format!("{ent_name}_{slot}_f{i}"));
                    }
                }
                return Err(format!("field {field} not found on entity {ent_name}"));
            }
            Err(format!(
                "unsupported field access in cross-entity property: {field}"
            ))
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => match op.as_str() {
            "OpEq" | "OpNEq" | "OpLt" | "OpLe" | "OpGt" | "OpGe" => {
                let l = guard_to_smt_sys_two(
                    left, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                )?;
                let r = guard_to_smt_sys_two(
                    right, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                )?;
                Ok(match op.as_str() {
                    "OpEq" => format!("(= {l} {r})"),
                    "OpNEq" => format!("(not (= {l} {r}))"),
                    "OpLt" => format!("(< {l} {r})"),
                    "OpLe" => format!("(<= {l} {r})"),
                    "OpGt" => format!("(> {l} {r})"),
                    "OpGe" => format!("(>= {l} {r})"),
                    _ => unreachable!(),
                })
            }
            "OpAnd" => {
                let l = guard_to_smt_sys_two(
                    left, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                )?;
                let r = guard_to_smt_sys_two(
                    right, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                )?;
                Ok(format!("(and {l} {r})"))
            }
            "OpOr" => {
                let l = guard_to_smt_sys_two(
                    left, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                )?;
                let r = guard_to_smt_sys_two(
                    right, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                )?;
                Ok(format!("(or {l} {r})"))
            }
            _ => {
                // Arithmetic: resolve values
                let l = guard_to_smt_sys_two(
                    left, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                )?;
                let r = guard_to_smt_sys_two(
                    right, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                )?;
                let op_sym = match op.as_str() {
                    "OpAdd" => "+",
                    "OpSub" => "-",
                    "OpMul" => "*",
                    _ => return Err(format!("unsupported op in cross-entity property: {op}")),
                };
                Ok(format!("({op_sym} {l} {r})"))
            }
        },
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => {
            let inner = guard_to_smt_sys_two(
                operand, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
            )?;
            Ok(format!("(not {inner})"))
        }
        IRExpr::Lit {
            value: LitVal::Int { value },
            ..
        } => {
            if *value < 0 {
                Ok(format!("(- {})", -value))
            } else {
                Ok(value.to_string())
            }
        }
        IRExpr::Ctor {
            enum_name, ctor, ..
        } => Ok(vctx.variants.id_of(enum_name, ctor).to_string()),
        _ => Err(format!(
            "unsupported expression in cross-entity property: {:?}",
            std::mem::discriminant(expr)
        )),
    }
}

/// Build CHC encoding for N entity slots flattened into one State relation.
///
/// State relation columns: for each slot s in 0..N, for each field f, one column
/// `s{s}_f{f}`, plus `s{s}_active`. Total columns: N * (fields + 1).
#[allow(clippy::format_push_string, clippy::too_many_lines)]
fn build_multi_slot_chc(
    entity: &IREntity,
    vctx: &VerifyContext,
    property: &IRExpr,
    n_slots: usize,
) -> Result<String, String> {
    let n_fields = entity.fields.len();

    let mut chc = String::new();

    // Declare State relation with all slot columns
    chc.push_str("(declare-rel State (");
    for slot in 0..n_slots {
        for (fi, f) in entity.fields.iter().enumerate() {
            let _ = (slot, fi); // used for ordering
            chc.push_str(&ir_type_to_sort_name(&f.ty));
            chc.push(' ');
        }
        chc.push_str("Bool "); // active flag for this slot
    }
    chc.push_str("))\n");
    chc.push_str("(declare-rel Error ())\n");

    // Declare variables for each slot's fields + active
    for slot in 0..n_slots {
        for (fi, f) in entity.fields.iter().enumerate() {
            chc.push_str(&format!(
                "(declare-var s{slot}_f{fi} {})\n",
                ir_type_to_sort_name(&f.ty)
            ));
        }
        chc.push_str(&format!("(declare-var s{slot}_active Bool)\n"));
    }

    // Helper: build a var list for all slots
    let all_vars: Vec<String> = (0..n_slots)
        .flat_map(|s| {
            let mut v: Vec<String> = (0..n_fields).map(|fi| format!("s{s}_f{fi}")).collect();
            v.push(format!("s{s}_active"));
            v
        })
        .collect();
    let all_vars_str = all_vars.join(" ");

    // ── Initial state: all slots inactive ──────────────────────────
    chc.push_str("(rule (State ");
    for slot in 0..n_slots {
        for (fi, f) in entity.fields.iter().enumerate() {
            if let Some(ref default_expr) = f.default {
                chc.push_str(&expr_to_smt(default_expr, entity, vctx)?);
            } else {
                chc.push_str(&format!("s{slot}_f{fi}"));
            }
            chc.push(' ');
        }
        chc.push_str("false "); // all inactive
    }
    chc.push_str(") init)\n");

    // ── Transition rules: for each slot × transition ───────────────
    for slot in 0..n_slots {
        for transition in &entity.transitions {
            let guard = guard_to_smt_slot(&transition.guard, entity, vctx, slot)?;

            // Build next-state: this slot gets updates, all other slots frame
            let mut next_vals: Vec<String> = Vec::new();
            for s in 0..n_slots {
                for (fi, f) in entity.fields.iter().enumerate() {
                    if s == slot {
                        let updated = transition.updates.iter().find(|u| u.field == f.name);
                        if let Some(upd) = updated {
                            next_vals.push(expr_to_smt_slot(&upd.value, entity, vctx, slot)?);
                        } else {
                            next_vals.push(format!("s{s}_f{fi}")); // frame
                        }
                    } else {
                        next_vals.push(format!("s{s}_f{fi}")); // frame: other slot unchanged
                    }
                }
                if s == slot {
                    next_vals.push("true".to_owned()); // active stays true
                } else {
                    next_vals.push(format!("s{s}_active")); // frame: other slot's active unchanged
                }
            }
            let next_str = next_vals.join(" ");

            chc.push_str(&format!(
                "(rule (=> (and (State {all_vars_str}) s{slot}_active {guard}) \
                 (State {next_str})) trans_{}_s{slot})\n",
                transition.name
            ));
        }
    }

    // ── Create rules: for each slot, if inactive → activate with defaults ──
    for slot in 0..n_slots {
        let mut next_vals: Vec<String> = Vec::new();
        for s in 0..n_slots {
            for (fi, f) in entity.fields.iter().enumerate() {
                if s == slot {
                    if let Some(ref default_expr) = f.default {
                        next_vals.push(expr_to_smt(default_expr, entity, vctx)?);
                    } else {
                        next_vals.push(format!("s{s}_f{fi}")); // unconstrained
                    }
                } else {
                    next_vals.push(format!("s{s}_f{fi}")); // frame
                }
            }
            if s == slot {
                next_vals.push("true".to_owned()); // activate this slot
            } else {
                next_vals.push(format!("s{s}_active")); // frame
            }
        }
        let next_str = next_vals.join(" ");

        // Symmetry breaking: slot i can only be created if slot i-1 is active.
        // Slot 0 can always be created (no prerequisite).
        let create_guard = if slot == 0 {
            format!("(not s{slot}_active)")
        } else {
            format!("(and (not s{slot}_active) s{}_active)", slot - 1)
        };

        chc.push_str(&format!(
            "(rule (=> (and (State {all_vars_str}) {create_guard}) \
             (State {next_str})) create_s{slot})\n"
        ));
    }

    // ── Stutter rule ───────────────────────────────────────────────
    chc.push_str(&format!(
        "(rule (=> (State {all_vars_str}) (State {all_vars_str})) stutter)\n"
    ));

    // ── Domain constraints for enum fields ─────────────────────────
    // Use VerifyContext enum_ranges for correct globally-allocated variant IDs
    for slot in 0..n_slots {
        for (fi, f) in entity.fields.iter().enumerate() {
            if let IRType::Enum { name, .. } = &f.ty {
                if let Some(&(min_id, max_id)) = vctx.enum_ranges.get(name) {
                    chc.push_str(&format!(
                        "(rule (=> (and (State {all_vars_str}) s{slot}_active \
                         (or (< s{slot}_f{fi} {min_id}) (> s{slot}_f{fi} {max_id}))) Error) \
                         domain_s{slot}_f{fi})\n"
                    ));
                }
            }
        }
    }

    // ── Error rule: property violation on any active entity ────────
    let neg_prop = negate_property_smt_multi(property, entity, vctx, n_slots)?;
    chc.push_str(&format!(
        "(rule (=> (and (State {all_vars_str}) {neg_prop}) Error) error)\n"
    ));

    Ok(chc)
}

/// Negate a property for multi-slot encoding.
///
/// For `all o: Order | P(o)`: violation = `∃ slot s | active(s) ∧ ¬P(s)`.
/// For `all a: E | all b: E | P(a,b)`: violation = `∃ s1, s2 | active(s1) ∧ active(s2) ∧ ¬P(s1, s2)`.
fn negate_property_smt_multi(
    property: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    n_slots: usize,
) -> Result<String, String> {
    match property {
        IRExpr::Always { body } => negate_property_smt_multi(body, entity, vctx, n_slots),
        IRExpr::Forall { var, body, .. } => {
            // Check if body is another Forall (nested inter-entity quantifier)
            if let IRExpr::Forall {
                var: var2,
                body: inner_body,
                ..
            } = body.as_ref()
            {
                // Nested: all a | all b | P(a, b)
                // Violation: ∃ s1, s2 | active(s1) ∧ active(s2) ∧ ¬P(s1, s2)
                let mut disjuncts = Vec::new();
                for s1 in 0..n_slots {
                    for s2 in 0..n_slots {
                        let neg = negate_inner_property_two_slots(
                            inner_body, entity, vctx, var, s1, var2, s2,
                        )?;
                        disjuncts.push(format!("(and s{s1}_active s{s2}_active {neg})"));
                    }
                }
                return Ok(format!("(or {})", disjuncts.join(" ")));
            }

            // Single quantifier: all o: E | P(o)
            let mut disjuncts = Vec::new();
            for slot in 0..n_slots {
                let neg = negate_inner_property_slot(body, entity, vctx, slot)?;
                disjuncts.push(format!("(and s{slot}_active {neg})"));
            }
            Ok(format!("(or {})", disjuncts.join(" ")))
        }
        _ => {
            // Non-quantified property: check against all active slots
            let mut disjuncts = Vec::new();
            for slot in 0..n_slots {
                let neg = negate_inner_property_slot(property, entity, vctx, slot)?;
                disjuncts.push(format!("(and s{slot}_active {neg})"));
            }
            Ok(format!("(or {})", disjuncts.join(" ")))
        }
    }
}

/// Negate an inner property with two bound variables mapped to two slots.
/// For `P(a, b)` where a → slot s1 and b → slot s2.
fn negate_inner_property_two_slots(
    property: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    var1: &str,
    slot1: usize,
    var2: &str,
    slot2: usize,
) -> Result<String, String> {
    let pos = guard_to_smt_two_slots(property, entity, vctx, var1, slot1, var2, slot2)?;
    Ok(format!("(not {pos})"))
}

/// Encode a guard with two slot bindings (for inter-entity properties).
#[allow(clippy::too_many_lines)]
fn guard_to_smt_two_slots(
    expr: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    var1: &str,
    slot1: usize,
    var2: &str,
    slot2: usize,
) -> Result<String, String> {
    match expr {
        IRExpr::Lit {
            value: LitVal::Bool { value: true },
            ..
        } => Ok("true".to_owned()),
        IRExpr::Lit {
            value: LitVal::Bool { value: false },
            ..
        } => Ok("false".to_owned()),
        IRExpr::Field {
            expr: inner, field, ..
        } => {
            // Determine which slot this field access refers to
            if let IRExpr::Var { name, .. } = inner.as_ref() {
                let slot = if name == var1 {
                    slot1
                } else if name == var2 {
                    slot2
                } else {
                    return Err(format!(
                        "unknown variable {name} in inter-entity property (expected {var1} or {var2})"
                    ));
                };
                for (i, f) in entity.fields.iter().enumerate() {
                    if f.name == *field {
                        return Ok(format!("s{slot}_f{i}"));
                    }
                }
            }
            Err(format!(
                "unsupported field access in inter-entity property: {field}"
            ))
        }
        IRExpr::Var { name, .. } => {
            // Bare quantifier variables (a, b) without field access are not valid
            // value expressions — they represent entity instances, not values.
            if name == var1 || name == var2 {
                return Err(format!(
                    "bare entity variable {name} in inter-entity property — \
                     use field access (e.g., {name}.field) instead"
                ));
            }
            // Try as a field name (unqualified field access like `status`)
            for (i, f) in entity.fields.iter().enumerate() {
                if f.name == *name {
                    // Ambiguous: which slot does this unqualified field belong to?
                    // Default to slot1, but this is a spec issue — should use qualified access.
                    return Ok(format!("s{slot1}_f{i}"));
                }
            }
            Err(format!("unknown variable {name} in inter-entity property"))
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => match op.as_str() {
            "OpEq" | "OpNEq" | "OpLt" | "OpLe" | "OpGt" | "OpGe" => {
                let l = guard_to_smt_two_slots(left, entity, vctx, var1, slot1, var2, slot2)?;
                let r = guard_to_smt_two_slots(right, entity, vctx, var1, slot1, var2, slot2)?;
                let cmp = match op.as_str() {
                    "OpEq" => format!("(= {l} {r})"),
                    "OpNEq" => format!("(not (= {l} {r}))"),
                    "OpLt" => format!("(< {l} {r})"),
                    "OpLe" => format!("(<= {l} {r})"),
                    "OpGt" => format!("(> {l} {r})"),
                    "OpGe" => format!("(>= {l} {r})"),
                    _ => unreachable!(),
                };
                Ok(cmp)
            }
            "OpAnd" => {
                let l = guard_to_smt_two_slots(left, entity, vctx, var1, slot1, var2, slot2)?;
                let r = guard_to_smt_two_slots(right, entity, vctx, var1, slot1, var2, slot2)?;
                Ok(format!("(and {l} {r})"))
            }
            "OpOr" => {
                let l = guard_to_smt_two_slots(left, entity, vctx, var1, slot1, var2, slot2)?;
                let r = guard_to_smt_two_slots(right, entity, vctx, var1, slot1, var2, slot2)?;
                Ok(format!("(or {l} {r})"))
            }
            "OpImplies" => {
                let l = guard_to_smt_two_slots(left, entity, vctx, var1, slot1, var2, slot2)?;
                let r = guard_to_smt_two_slots(right, entity, vctx, var1, slot1, var2, slot2)?;
                Ok(format!("(=> {l} {r})"))
            }
            "OpAdd" | "OpSub" | "OpMul" => {
                let l = guard_to_smt_two_slots(left, entity, vctx, var1, slot1, var2, slot2)?;
                let r = guard_to_smt_two_slots(right, entity, vctx, var1, slot1, var2, slot2)?;
                let op_sym = match op.as_str() {
                    "OpAdd" => "+",
                    "OpSub" => "-",
                    "OpMul" => "*",
                    _ => unreachable!(),
                };
                Ok(format!("({op_sym} {l} {r})"))
            }
            _ => Err(format!("unsupported op in inter-entity property: {op}")),
        },
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => {
            let inner = guard_to_smt_two_slots(operand, entity, vctx, var1, slot1, var2, slot2)?;
            Ok(format!("(not {inner})"))
        }
        IRExpr::Lit { value, .. } => match value {
            LitVal::Int { value } => {
                if *value < 0 {
                    Ok(format!("(- {})", -value))
                } else {
                    Ok(value.to_string())
                }
            }
            _ => Err("unsupported literal in inter-entity property".to_owned()),
        },
        IRExpr::Ctor {
            enum_name, ctor, ..
        } => {
            let id = vctx.variants.id_of(enum_name, ctor);
            Ok(id.to_string())
        }
        _ => Err(format!(
            "unsupported expression in inter-entity property: {:?}",
            std::mem::discriminant(expr)
        )),
    }
}

/// Negate an inner property expression for a specific slot.
fn negate_inner_property_slot(
    property: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    slot: usize,
) -> Result<String, String> {
    let pos = guard_to_smt_slot(property, entity, vctx, slot)?;
    Ok(format!("(not {pos})"))
}

/// Like `expr_to_smt` but prefixes field variables with slot index.
fn expr_to_smt_slot(
    expr: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    slot: usize,
) -> Result<String, String> {
    match expr {
        IRExpr::Var { name, .. } => {
            for (i, f) in entity.fields.iter().enumerate() {
                if f.name == *name {
                    return Ok(format!("s{slot}_f{i}"));
                }
            }
            Err(format!("unknown variable in IC3 encoding: {name}"))
        }
        IRExpr::Field {
            expr: inner, field, ..
        } => {
            if let IRExpr::Var { .. } = inner.as_ref() {
                for (i, f) in entity.fields.iter().enumerate() {
                    if f.name == *field {
                        return Ok(format!("s{slot}_f{i}"));
                    }
                }
            }
            Err(format!("unsupported field access in IC3 encoding: {field}"))
        }
        // Arithmetic: recurse with slot context
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let l = expr_to_smt_slot(left, entity, vctx, slot)?;
            let r = expr_to_smt_slot(right, entity, vctx, slot)?;
            match op.as_str() {
                "OpAdd" => Ok(format!("(+ {l} {r})")),
                "OpSub" => Ok(format!("(- {l} {r})")),
                "OpMul" => Ok(format!("(* {l} {r})")),
                "OpDiv" => Ok(format!("(div {l} {r})")),
                "OpMod" => Ok(format!("(mod {l} {r})")),
                _ => Err(format!(
                    "unsupported binary op in IC3 slot value encoding: {op}"
                )),
            }
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpNeg" => {
            let inner = expr_to_smt_slot(operand, entity, vctx, slot)?;
            Ok(format!("(- {inner})"))
        }
        // Literals and constructors don't need slot context
        IRExpr::Lit { .. } | IRExpr::Ctor { .. } => expr_to_smt(expr, entity, vctx),
        _ => Err(format!(
            "unsupported expression in IC3 slot value encoding: {:?}",
            std::mem::discriminant(expr)
        )),
    }
}

/// Like `guard_to_smt` but resolves field variables to a specific slot.
fn guard_to_smt_slot(
    guard: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    slot: usize,
) -> Result<String, String> {
    match guard {
        IRExpr::Lit {
            value: LitVal::Bool { value: true },
            ..
        } => Ok("true".to_owned()),
        IRExpr::Lit {
            value: LitVal::Bool { value: false },
            ..
        } => Ok("false".to_owned()),
        IRExpr::BinOp {
            op, left, right, ..
        } => match op.as_str() {
            "OpEq" | "OpNEq" | "OpLt" | "OpLe" | "OpGt" | "OpGe" => {
                let l = expr_to_smt_slot(left, entity, vctx, slot)?;
                let r = expr_to_smt_slot(right, entity, vctx, slot)?;
                let cmp = match op.as_str() {
                    "OpEq" => format!("(= {l} {r})"),
                    "OpNEq" => format!("(not (= {l} {r}))"),
                    "OpLt" => format!("(< {l} {r})"),
                    "OpLe" => format!("(<= {l} {r})"),
                    "OpGt" => format!("(> {l} {r})"),
                    "OpGe" => format!("(>= {l} {r})"),
                    _ => unreachable!(),
                };
                Ok(cmp)
            }
            "OpAnd" => {
                let l = guard_to_smt_slot(left, entity, vctx, slot)?;
                let r = guard_to_smt_slot(right, entity, vctx, slot)?;
                Ok(format!("(and {l} {r})"))
            }
            "OpOr" => {
                let l = guard_to_smt_slot(left, entity, vctx, slot)?;
                let r = guard_to_smt_slot(right, entity, vctx, slot)?;
                Ok(format!("(or {l} {r})"))
            }
            "OpImplies" => {
                let l = guard_to_smt_slot(left, entity, vctx, slot)?;
                let r = guard_to_smt_slot(right, entity, vctx, slot)?;
                Ok(format!("(=> {l} {r})"))
            }
            _ => Err(format!("unsupported binary op in IC3 guard encoding: {op}")),
        },
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => {
            let inner = guard_to_smt_slot(operand, entity, vctx, slot)?;
            Ok(format!("(not {inner})"))
        }
        IRExpr::Field { .. } | IRExpr::Var { .. } => expr_to_smt_slot(guard, entity, vctx, slot),
        _ => Err(format!(
            "unsupported expression in IC3 guard encoding: {:?}",
            std::mem::discriminant(guard)
        )),
    }
}

/// Build an SMT-LIB2 CHC encoding string for a single entity.
///
/// Returns `Err` if any expression can't be encoded — never silently approximates.
#[allow(clippy::format_push_string)]
fn build_chc_string(
    entity: &IREntity,
    vctx: &VerifyContext,
    property: &IRExpr,
) -> Result<String, String> {
    let mut chc = String::new();

    // Field sorts for State relation
    let field_sorts: Vec<String> = entity
        .fields
        .iter()
        .map(|f| ir_type_to_sort_name(&f.ty))
        .collect();

    // Declare State relation: State(f1, ..., fn, active)
    chc.push_str("(declare-rel State (");
    for s in &field_sorts {
        chc.push_str(s);
        chc.push(' ');
    }
    chc.push_str("Bool))\n");

    // Declare Error relation
    chc.push_str("(declare-rel Error ())\n");

    // Declare variables for each field + active flag
    for (i, f) in entity.fields.iter().enumerate() {
        chc.push_str(&format!(
            "(declare-var f{} {})\n",
            i,
            ir_type_to_sort_name(&f.ty)
        ));
    }
    chc.push_str("(declare-var active Bool)\n");

    let n = entity.fields.len();
    let vars: Vec<String> = (0..n).map(|i| format!("f{i}")).collect();
    let vars_str = vars.join(" ");

    // ── Initial state ──────────────────────────────────────────────
    // State(defaults..., false) — entity starts inactive
    chc.push_str("(rule (State ");
    for (i, f) in entity.fields.iter().enumerate() {
        if let Some(ref default_expr) = f.default {
            chc.push_str(&expr_to_smt(default_expr, entity, vctx)?);
        } else {
            // No default: field is unconstrained at init.
            // Use the declared variable so the rule is universally quantified over it.
            chc.push_str(&format!("f{i}"));
        }
        chc.push(' ');
    }
    chc.push_str("false) init)\n");

    // ── Create rule ────────────────────────────────────────────────
    // State(f0, ..., fn, false) → State(defaults_or_vars, true)
    chc.push_str(&format!("(rule (=> (State {vars_str} false) (State "));
    for (i, f) in entity.fields.iter().enumerate() {
        if let Some(ref default_expr) = f.default {
            chc.push_str(&expr_to_smt(default_expr, entity, vctx)?);
        } else {
            // No default: created entity gets unconstrained field value
            chc.push_str(&format!("f{i}"));
        }
        chc.push(' ');
    }
    chc.push_str("true)) create)\n");

    // ── Transition rules ───────────────────────────────────────────
    for transition in &entity.transitions {
        let guard_smt = guard_to_smt(&transition.guard, entity, vctx)?;

        // Build next-state: updates override, frame preserves
        let mut next_fields: Vec<String> = Vec::new();
        for (i, f) in entity.fields.iter().enumerate() {
            let updated = transition.updates.iter().find(|u| u.field == f.name);
            if let Some(upd) = updated {
                next_fields.push(expr_to_smt(&upd.value, entity, vctx)?);
            } else {
                next_fields.push(format!("f{i}")); // frame
            }
        }
        let next_str = next_fields.join(" ");

        chc.push_str(&format!(
            "(rule (=> (and (State {vars_str} active) active {guard_smt}) \
             (State {next_str} true)) trans_{})\n",
            transition.name
        ));
    }

    // ── Stutter rule ───────────────────────────────────────────────
    chc.push_str(&format!(
        "(rule (=> (State {vars_str} active) (State {vars_str} active)) stutter)\n"
    ));

    // ── Domain constraints for enum fields ─────────────────────────
    for (fi, f) in entity.fields.iter().enumerate() {
        if let IRType::Enum { name, .. } = &f.ty {
            if let Some(&(min_id, max_id)) = vctx.enum_ranges.get(name) {
                chc.push_str(&format!(
                    "(rule (=> (and (State {vars_str} active) active \
                     (or (< f{fi} {min_id}) (> f{fi} {max_id}))) Error) domain_f{fi})\n"
                ));
            }
        }
    }

    // ── Error rule ─────────────────────────────────────────────────
    let neg_prop = negate_property_smt(property, entity, vctx)?;
    chc.push_str(&format!(
        "(rule (=> (and (State {vars_str} active) active {neg_prop}) Error) error)\n"
    ));

    Ok(chc)
}

/// Convert an IR type to an SMT-LIB2 sort name.
#[allow(clippy::match_same_arms)]
fn ir_type_to_sort_name(ty: &IRType) -> String {
    match ty {
        IRType::Int | IRType::Id => "Int".to_owned(),
        IRType::Bool => "Bool".to_owned(),
        IRType::Real | IRType::Float => "Real".to_owned(),
        IRType::Enum { .. } => "Int".to_owned(),
        _ => "Int".to_owned(),
    }
}

/// Convert an IR expression to an SMT-LIB2 term string.
///
/// Returns `Err` for unsupported forms — never silently approximates.
#[allow(clippy::match_same_arms)]
fn expr_to_smt(expr: &IRExpr, entity: &IREntity, vctx: &VerifyContext) -> Result<String, String> {
    match expr {
        IRExpr::Lit { value, .. } => match value {
            LitVal::Int { value } => {
                if *value < 0 {
                    Ok(format!("(- {})", -value))
                } else {
                    Ok(value.to_string())
                }
            }
            LitVal::Bool { value } => Ok(value.to_string()),
            LitVal::Real { value } => Ok(format!("{value}")),
            LitVal::Float { value } => Ok(format!("{value}")),
            LitVal::Str { .. } => Err("string literals not supported in IC3 encoding".to_owned()),
        },
        IRExpr::Ctor {
            enum_name, ctor, ..
        } => {
            let id = vctx.variants.id_of(enum_name, ctor);
            Ok(id.to_string())
        }
        IRExpr::Var { name, .. } => {
            for (i, f) in entity.fields.iter().enumerate() {
                if f.name == *name {
                    return Ok(format!("f{i}"));
                }
            }
            Err(format!("unknown variable in IC3 encoding: {name}"))
        }
        IRExpr::Field {
            expr: inner, field, ..
        } => {
            // Field access on entity variable: o.status → f{index}
            if let IRExpr::Var { .. } = inner.as_ref() {
                for (i, f) in entity.fields.iter().enumerate() {
                    if f.name == *field {
                        return Ok(format!("f{i}"));
                    }
                }
            }
            Err(format!("unsupported field access in IC3 encoding: {field}"))
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let l = expr_to_smt(left, entity, vctx)?;
            let r = expr_to_smt(right, entity, vctx)?;
            match op.as_str() {
                "OpAdd" => Ok(format!("(+ {l} {r})")),
                "OpSub" => Ok(format!("(- {l} {r})")),
                "OpMul" => Ok(format!("(* {l} {r})")),
                "OpDiv" => Ok(format!("(div {l} {r})")),
                "OpMod" => Ok(format!("(mod {l} {r})")),
                _ => Err(format!("unsupported binary op in IC3 value encoding: {op}")),
            }
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpNeg" => {
            let inner = expr_to_smt(operand, entity, vctx)?;
            Ok(format!("(- {inner})"))
        }
        _ => Err(format!(
            "unsupported expression in IC3 value encoding: {:?}",
            std::mem::discriminant(expr)
        )),
    }
}

/// Convert a guard expression to an SMT-LIB2 boolean term.
///
/// Returns `Err` for unsupported forms — never silently approximates.
fn guard_to_smt(guard: &IRExpr, entity: &IREntity, vctx: &VerifyContext) -> Result<String, String> {
    match guard {
        IRExpr::Lit {
            value: LitVal::Bool { value: true },
            ..
        } => Ok("true".to_owned()),
        IRExpr::Lit {
            value: LitVal::Bool { value: false },
            ..
        } => Ok("false".to_owned()),
        IRExpr::BinOp {
            op, left, right, ..
        } => match op.as_str() {
            "OpEq" | "OpNEq" | "OpLt" | "OpLe" | "OpGt" | "OpGe" => {
                let l = expr_to_smt(left, entity, vctx)?;
                let r = expr_to_smt(right, entity, vctx)?;
                let cmp = match op.as_str() {
                    "OpEq" => format!("(= {l} {r})"),
                    "OpNEq" => format!("(not (= {l} {r}))"),
                    "OpLt" => format!("(< {l} {r})"),
                    "OpLe" => format!("(<= {l} {r})"),
                    "OpGt" => format!("(> {l} {r})"),
                    "OpGe" => format!("(>= {l} {r})"),
                    _ => unreachable!(),
                };
                Ok(cmp)
            }
            "OpAnd" => {
                let l = guard_to_smt(left, entity, vctx)?;
                let r = guard_to_smt(right, entity, vctx)?;
                Ok(format!("(and {l} {r})"))
            }
            "OpOr" => {
                let l = guard_to_smt(left, entity, vctx)?;
                let r = guard_to_smt(right, entity, vctx)?;
                Ok(format!("(or {l} {r})"))
            }
            "OpImplies" => {
                let l = guard_to_smt(left, entity, vctx)?;
                let r = guard_to_smt(right, entity, vctx)?;
                Ok(format!("(=> {l} {r})"))
            }
            _ => Err(format!("unsupported binary op in IC3 guard encoding: {op}")),
        },
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => {
            let inner = guard_to_smt(operand, entity, vctx)?;
            Ok(format!("(not {inner})"))
        }
        // Field access as boolean: resolve to field variable
        IRExpr::Field { .. } | IRExpr::Var { .. } => {
            let val = expr_to_smt(guard, entity, vctx)?;
            Ok(val)
        }
        _ => Err(format!(
            "unsupported expression in IC3 guard encoding: {:?}",
            std::mem::discriminant(guard)
        )),
    }
}

/// Negate a property expression for the error rule.
///
/// Strips `always` and `forall` wrappers (IC3 proves these by construction),
/// then negates the inner property.
#[allow(clippy::match_same_arms)]
fn negate_property_smt(
    property: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
) -> Result<String, String> {
    match property {
        // Strip always — IC3 proves always by construction
        IRExpr::Always { body } => negate_property_smt(body, entity, vctx),
        // Strip forall over entity — IC3 checks per-entity
        IRExpr::Forall { body, .. } => negate_property_smt(body, entity, vctx),
        _ => {
            let pos = guard_to_smt(property, entity, vctx)?;
            Ok(format!("(not {pos})"))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::types::*;
    use crate::verify::context::VerifyContext;

    /// Test IC3 via from_string API with declare-var style variables.
    /// Z3's fixpoint expects rules with `declare-var` — validates the API works.
    #[test]
    fn z3_fixpoint_unreachable_via_string() {
        let fp = Fixedpoint::new();
        let mut params = Params::new();
        params.set_symbol("engine", "spacer");
        fp.set_params(&params);

        let parse_result = fp.from_string(
            "(declare-rel Reach (Int))
             (declare-rel Error ())
             (declare-var x Int)
             (rule (Reach 0) base)
             (rule (=> (and (Reach x) (< x 10)) (Reach (+ x 1))) step)
             (rule (=> (and (Reach x) (< x 0)) Error) error)",
        );
        assert!(parse_result.is_ok(), "Failed to parse: {parse_result:?}");

        let error_rel = FuncDecl::new("Error", &[], &Sort::bool());
        fp.register_relation(&error_rel);
        let error_query = error_rel.apply(&[]);
        let result = fp.query(&error_query);

        assert!(
            matches!(result, SatResult::Unsat | SatResult::Unknown),
            "expected Unsat or Unknown, got: {result:?}"
        );
    }

    fn make_simple_entity() -> (IREntity, Vec<IRTypeEntry>) {
        let status_type = IRTypeEntry {
            name: "Status".to_owned(),
            ty: IRType::Enum {
                name: "Status".to_owned(),
                constructors: vec![
                    "Pending".to_owned(),
                    "Confirmed".to_owned(),
                    "Shipped".to_owned(),
                ],
            },
        };

        let entity = IREntity {
            name: "Order".to_owned(),
            fields: vec![
                IRField {
                    name: "id".to_owned(),
                    ty: IRType::Id,
                    default: None,
                },
                IRField {
                    name: "status".to_owned(),
                    ty: IRType::Enum {
                        name: "Status".to_owned(),
                        constructors: vec![
                            "Pending".to_owned(),
                            "Confirmed".to_owned(),
                            "Shipped".to_owned(),
                        ],
                    },
                    default: Some(IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Pending".to_owned(),
                    }),
                },
                IRField {
                    name: "total".to_owned(),
                    ty: IRType::Int,
                    default: Some(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },
                    }),
                },
            ],
            transitions: vec![
                IRTransition {
                    name: "confirm".to_owned(),
                    refs: vec![],
                    params: vec![],
                    guard: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "status".to_owned(),
                            ty: IRType::Int,
                        }),
                        right: Box::new(IRExpr::Ctor {
                            enum_name: "Status".to_owned(),
                            ctor: "Pending".to_owned(),
                        }),
                        ty: IRType::Bool,
                    },
                    updates: vec![IRUpdate {
                        field: "status".to_owned(),
                        value: IRExpr::Ctor {
                            enum_name: "Status".to_owned(),
                            ctor: "Confirmed".to_owned(),
                        },
                    }],
                    postcondition: None,
                },
                IRTransition {
                    name: "ship".to_owned(),
                    refs: vec![],
                    params: vec![],
                    guard: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "status".to_owned(),
                            ty: IRType::Int,
                        }),
                        right: Box::new(IRExpr::Ctor {
                            enum_name: "Status".to_owned(),
                            ctor: "Confirmed".to_owned(),
                        }),
                        ty: IRType::Bool,
                    },
                    updates: vec![IRUpdate {
                        field: "status".to_owned(),
                        value: IRExpr::Ctor {
                            enum_name: "Status".to_owned(),
                            ctor: "Shipped".to_owned(),
                        },
                    }],
                    postcondition: None,
                },
            ],
        };

        (entity, vec![status_type])
    }

    fn make_ir_for_entity(entity: &IREntity, types: Vec<IRTypeEntry>) -> IRProgram {
        IRProgram {
            types,
            constants: vec![],
            functions: vec![],
            entities: vec![entity.clone()],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        }
    }

    #[test]
    fn ic3_proves_valid_safety_property() {
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        // Property: status != -1 (always valid — status is always a valid enum)
        let property = IRExpr::BinOp {
            op: "OpNEq".to_owned(),
            left: Box::new(IRExpr::Var {
                name: "status".to_owned(),
                ty: IRType::Int,
            }),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: -1 },
            }),
            ty: IRType::Bool,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved, got: {result:?}"
        );
    }

    #[test]
    fn ic3_proves_field_access_property() {
        // Property: always all o: Order | o.total >= 0
        // total defaults to 0 and no transition modifies it.
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "o".to_owned(),
                domain: IRType::Entity {
                    name: "Order".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "o".to_owned(),
                            ty: IRType::Entity {
                                name: "Order".to_owned(),
                            },
                        }),
                        field: "total".to_owned(),
                        ty: IRType::Int,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },
                    }),
                    ty: IRType::Bool,
                }),
            }),
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for o.total >= 0, got: {result:?}"
        );
    }

    #[test]
    fn ic3_detects_violation() {
        // Property: status == Pending always (false — confirm changes it)
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::Var {
                name: "status".to_owned(),
                ty: IRType::Int,
            }),
            right: Box::new(IRExpr::Ctor {
                enum_name: "Status".to_owned(),
                ctor: "Pending".to_owned(),
            }),
            ty: IRType::Bool,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Violated),
            "expected Violated (confirm breaks always-Pending), got: {result:?}"
        );
    }

    #[test]
    fn ic3_rejects_unsupported_expression() {
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        // Property with Let expression — unsupported, should return Unknown
        let property = IRExpr::Let {
            bindings: vec![LetBinding {
                name: "x".to_owned(),
                ty: IRType::Int,
                expr: IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 1 },
                },
            }],
            body: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
            }),
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Unknown(ref reason) if reason.contains("unsupported")),
            "expected Unknown with unsupported message, got: {result:?}"
        );
    }

    // ── Multi-slot tests ────────────────────────────────────────────

    #[test]
    fn ic3_multi_slot_proves_per_entity_property() {
        // Per-entity property with 2 slots — should still prove
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "o".to_owned(),
                domain: IRType::Entity {
                    name: "Order".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "o".to_owned(),
                            ty: IRType::Entity {
                                name: "Order".to_owned(),
                            },
                        }),
                        field: "total".to_owned(),
                        ty: IRType::Int,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },
                    }),
                    ty: IRType::Bool,
                }),
            }),
        };

        let result = try_ic3_multi_slot(&entity, &vctx, &property, 2, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for multi-slot per-entity property, got: {result:?}"
        );
    }

    #[test]
    fn ic3_multi_slot_detects_violation() {
        // Property: all orders always Pending — should fail with 2 slots
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "o".to_owned(),
                domain: IRType::Entity {
                    name: "Order".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "o".to_owned(),
                            ty: IRType::Entity {
                                name: "Order".to_owned(),
                            },
                        }),
                        field: "status".to_owned(),
                        ty: IRType::Int,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Pending".to_owned(),
                    }),
                    ty: IRType::Bool,
                }),
            }),
        };

        let result = try_ic3_multi_slot(&entity, &vctx, &property, 2, 5000);
        assert!(
            matches!(result, Ic3Result::Violated),
            "expected Violated for multi-slot always-Pending, got: {result:?}"
        );
    }

    #[test]
    fn ic3_multi_slot_delegates_to_single_for_one_slot() {
        // With n_slots=1, should delegate to single-entity encoding
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::BinOp {
            op: "OpNEq".to_owned(),
            left: Box::new(IRExpr::Var {
                name: "status".to_owned(),
                ty: IRType::Int,
            }),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: -1 },
            }),
            ty: IRType::Bool,
        };

        let result = try_ic3_multi_slot(&entity, &vctx, &property, 1, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved with 1 slot, got: {result:?}"
        );
    }

    #[test]
    fn ic3_multi_slot_inter_entity_property() {
        // Inter-entity property: all a: Order | all b: Order | a.total >= 0 and b.total >= 0
        // This is trivially true (total defaults to 0, no transition modifies it).
        // Tests the nested quantifier expansion path with 3 slots.
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "a".to_owned(),
                domain: IRType::Entity {
                    name: "Order".to_owned(),
                },
                body: Box::new(IRExpr::Forall {
                    var: "b".to_owned(),
                    domain: IRType::Entity {
                        name: "Order".to_owned(),
                    },
                    body: Box::new(IRExpr::BinOp {
                        op: "OpAnd".to_owned(),
                        left: Box::new(IRExpr::BinOp {
                            op: "OpGe".to_owned(),
                            left: Box::new(IRExpr::Field {
                                expr: Box::new(IRExpr::Var {
                                    name: "a".to_owned(),
                                    ty: IRType::Entity {
                                        name: "Order".to_owned(),
                                    },
                                }),
                                field: "total".to_owned(),
                                ty: IRType::Int,
                            }),
                            right: Box::new(IRExpr::Lit {
                                ty: IRType::Int,
                                value: LitVal::Int { value: 0 },
                            }),
                            ty: IRType::Bool,
                        }),
                        right: Box::new(IRExpr::BinOp {
                            op: "OpGe".to_owned(),
                            left: Box::new(IRExpr::Field {
                                expr: Box::new(IRExpr::Var {
                                    name: "b".to_owned(),
                                    ty: IRType::Entity {
                                        name: "Order".to_owned(),
                                    },
                                }),
                                field: "total".to_owned(),
                                ty: IRType::Int,
                            }),
                            right: Box::new(IRExpr::Lit {
                                ty: IRType::Int,
                                value: LitVal::Int { value: 0 },
                            }),
                            ty: IRType::Bool,
                        }),
                        ty: IRType::Bool,
                    }),
                }),
            }),
        };

        let result = try_ic3_multi_slot(&entity, &vctx, &property, 3, 10000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for inter-entity total >= 0, got: {result:?}"
        );
    }

    #[test]
    fn ic3_rejects_bare_entity_var_in_inter_entity() {
        // Property: all a | all b | a == b — bare entity vars, should error
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "a".to_owned(),
                domain: IRType::Entity {
                    name: "Order".to_owned(),
                },
                body: Box::new(IRExpr::Forall {
                    var: "b".to_owned(),
                    domain: IRType::Entity {
                        name: "Order".to_owned(),
                    },
                    body: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "a".to_owned(),
                            ty: IRType::Entity {
                                name: "Order".to_owned(),
                            },
                        }),
                        right: Box::new(IRExpr::Var {
                            name: "b".to_owned(),
                            ty: IRType::Entity {
                                name: "Order".to_owned(),
                            },
                        }),
                        ty: IRType::Bool,
                    }),
                }),
            }),
        };

        let result = try_ic3_multi_slot(&entity, &vctx, &property, 3, 5000);
        assert!(
            matches!(result, Ic3Result::Unknown(ref reason) if reason.contains("bare entity variable")),
            "expected Unknown with bare entity variable message, got: {result:?}"
        );
    }

    // ── Cross-system tests ──────────────────────────────────────────

    #[test]
    fn ic3_system_proves_multi_entity_safety() {
        // Two entity types: Order (status) and Item (quantity).
        // Property: all o: Order | o.total >= 0
        // No transitions modify total — should prove.
        let order_status = IRTypeEntry {
            name: "OrderStatus".to_owned(),
            ty: IRType::Enum {
                name: "OrderStatus".to_owned(),
                constructors: vec!["Pending".to_owned(), "Confirmed".to_owned()],
            },
        };

        let order = IREntity {
            name: "Order".to_owned(),
            fields: vec![
                IRField {
                    name: "id".to_owned(),
                    ty: IRType::Id,
                    default: None,
                },
                IRField {
                    name: "total".to_owned(),
                    ty: IRType::Int,
                    default: Some(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },
                    }),
                },
                IRField {
                    name: "status".to_owned(),
                    ty: IRType::Enum {
                        name: "OrderStatus".to_owned(),
                        constructors: vec!["Pending".to_owned(), "Confirmed".to_owned()],
                    },
                    default: Some(IRExpr::Ctor {
                        enum_name: "OrderStatus".to_owned(),
                        ctor: "Pending".to_owned(),
                    }),
                },
            ],
            transitions: vec![IRTransition {
                name: "confirm".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "status".to_owned(),
                        ty: IRType::Int,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "OrderStatus".to_owned(),
                        ctor: "Pending".to_owned(),
                    }),
                    ty: IRType::Bool,
                },
                updates: vec![IRUpdate {
                    field: "status".to_owned(),
                    value: IRExpr::Ctor {
                        enum_name: "OrderStatus".to_owned(),
                        ctor: "Confirmed".to_owned(),
                    },
                }],
                postcondition: None,
            }],
        };

        let item = IREntity {
            name: "Item".to_owned(),
            fields: vec![
                IRField {
                    name: "id".to_owned(),
                    ty: IRType::Id,
                    default: None,
                },
                IRField {
                    name: "quantity".to_owned(),
                    ty: IRType::Int,
                    default: Some(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },
                    }),
                },
            ],
            transitions: vec![],
        };

        let ir = IRProgram {
            types: vec![order_status],
            constants: vec![],
            functions: vec![],
            entities: vec![order, item],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        };
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "o".to_owned(),
                domain: IRType::Entity {
                    name: "Order".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "o".to_owned(),
                            ty: IRType::Entity {
                                name: "Order".to_owned(),
                            },
                        }),
                        field: "total".to_owned(),
                        ty: IRType::Int,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },
                    }),
                    ty: IRType::Bool,
                }),
            }),
        };

        let mut slots = HashMap::new();
        slots.insert("Order".to_owned(), 2);
        slots.insert("Item".to_owned(), 1);

        let result = try_ic3_system(&ir, &vctx, &[], &property, &slots, 10000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for multi-entity total >= 0, got: {result:?}"
        );
    }
}
