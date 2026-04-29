//! IC3/PDR verification via CHC backends.
//!
//! Translates Abide entity+system models to Constrained Horn Clauses (CHC)
//! and queries the active CHC backend to prove safety properties.
//!
//! IC3 is more powerful than 1-induction: it automatically discovers
//! strengthening invariants, proving properties that aren't directly
//! inductive. For finite state spaces, IC3 is guaranteed to terminate.
//!
//! **Soundness policy:** Unsupported expression forms cause the encoding to
//! fail with `Ic3Result::Unknown`, never silent approximation. A guard
//! falling back to "true" or a value falling back to "0" would be unsound.

use std::collections::{HashMap, HashSet};

use super::chc;
use super::property;
use super::smt::ChcResult;

use crate::ir::types::{
    IRAction, IRCreateField, IREntity, IRExpr, IRProgram, IRSystem, IRTransition, IRType, LitVal,
};

use super::context::VerifyContext;
mod liveness;
mod multi_slot;
mod system;
mod trace;
pub use self::liveness::try_ic3_liveness;
use self::multi_slot::*;
use self::system::*;
use self::trace::*;

/// Result of an IC3 proof attempt.
#[derive(Debug)]
pub enum Ic3Result {
    /// Property proved — IC3 found an inductive invariant.
    Proved,
    /// Property violated — a reachable error state exists.
    /// Carries a counterexample trace (may be empty if extraction failed).
    Violated(Vec<Ic3TraceStep>),
    /// IC3 could not determine (timeout, unsupported encoding, or incompleteness).
    Unknown(String),
}

/// A single step in an IC3 counterexample trace.
#[derive(Debug, Clone)]
pub struct Ic3TraceStep {
    pub step: usize,
    /// Field assignments: `(entity_name, field_name, value_string)`.
    pub assignments: Vec<(String, String, String)>,
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
    let property = match property::normalize_verifier_choose_expr(property) {
        Ok(expr) => expr,
        Err(e) => return Ic3Result::Unknown(format!("CHC encoding failed: {e}")),
    };

    // Build CHC string — propagate encoding errors
    let chc = match build_chc_string(entity, vctx, &property) {
        Ok(s) => s,
        Err(e) => return Ic3Result::Unknown(format!("CHC encoding failed: {e}")),
    };

    let result = chc::check_chc(&chc, "Error", timeout_ms);
    match result {
        ChcResult::Proved => Ic3Result::Proved,
        ChcResult::Counterexample(answer) => {
            // Build column layout: fields + active flag (matches CHC State relation)
            let mut columns: Vec<TraceColumn> = entity
                .fields
                .iter()
                .enumerate()
                .map(|(fi, f)| (entity.name.clone(), f.name.clone(), fi))
                .collect();
            columns.push((entity.name.clone(), "active".to_owned(), usize::MAX));
            let trace = parse_state_snapshots(&answer, &columns);
            Ic3Result::Violated(trace)
        }
        ChcResult::Unknown(reason) => Ic3Result::Unknown(reason),
    }
}

/// Try to prove a safety property for a multi-slot entity pool using IC3/PDR.
///
/// Extends the single-entity encoding with N slots per entity type.
/// The State relation is flattened: `State(s0_f1, s0_f2,..., s0_active, s1_f1,..., s1_active)`.
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
    let property = match property::normalize_verifier_choose_expr(property) {
        Ok(expr) => expr,
        Err(e) => return Ic3Result::Unknown(format!("CHC encoding failed: {e}")),
    };

    if n_slots <= 1 {
        return try_ic3_single_entity(entity, vctx, &property, timeout_ms);
    }

    let chc = match build_multi_slot_chc(entity, vctx, &property, n_slots) {
        Ok(s) => s,
        Err(e) => return Ic3Result::Unknown(format!("CHC encoding failed: {e}")),
    };

    let result = chc::check_chc(&chc, "Error", timeout_ms);
    match result {
        ChcResult::Proved => Ic3Result::Proved,
        ChcResult::Counterexample(answer) => {
            let columns = build_multi_slot_columns(entity, n_slots);
            let trace = parse_state_snapshots(&answer, &columns);
            Ic3Result::Violated(trace)
        }
        ChcResult::Unknown(reason) => Ic3Result::Unknown(reason),
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
    let property = match property::normalize_verifier_choose_expr(property) {
        Ok(expr) => expr,
        Err(e) => return Ic3Result::Unknown(format!("CHC encoding failed: {e}")),
    };

    // Validate that all requested system names exist in the IR
    for name in system_names {
        if !ir.systems.iter().any(|s| s.name == *name) {
            return Ic3Result::Unknown(format!("system {name} not found in IR"));
        }
    }

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
        &property,
        slots_per_entity,
    ) {
        Ok(s) => s,
        Err(e) => return Ic3Result::Unknown(format!("CHC encoding failed: {e}")),
    };

    let result = chc::check_chc(&chc, "Error", timeout_ms);
    match result {
        ChcResult::Proved => Ic3Result::Proved,
        ChcResult::Counterexample(answer) => {
            let columns = build_system_columns(&relevant_entities, slots_per_entity);
            let trace = parse_state_snapshots(&answer, &columns);
            Ic3Result::Violated(trace)
        }
        ChcResult::Unknown(reason) => Ic3Result::Unknown(reason),
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

/// Column metadata for trace extraction: `(entity_name, field_name, field_index)`.
/// The last column per slot is the `active` flag `(entity_name, "active", usize::MAX)`.
type TraceColumn = (String, String, usize);
type Ic3SlotEntityLocals = HashMap<String, usize>;
type Ic3SystemEntityLocals = HashMap<String, (String, usize)>;

#[cfg(test)]
mod tests;
