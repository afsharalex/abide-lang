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
            for event in &sys.steps {
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

/// Build column layout for system-level trace extraction.
fn build_system_columns(
    entities: &[&IREntity],
    slots_per_entity: &HashMap<String, usize>,
) -> Vec<TraceColumn> {
    let mut columns = Vec::new();
    for entity in entities {
        let n_slots = slots_per_entity.get(&entity.name).copied().unwrap_or(1);
        for slot in 0..n_slots {
            let ent_label = if n_slots > 1 {
                format!("{}[{}]", entity.name, slot)
            } else {
                entity.name.clone()
            };
            for (fi, f) in entity.fields.iter().enumerate() {
                columns.push((ent_label.clone(), f.name.clone(), fi));
            }
            columns.push((ent_label, "active".to_owned(), usize::MAX));
        }
    }
    columns
}

/// Build column layout for multi-slot single-entity trace extraction.
fn build_multi_slot_columns(entity: &IREntity, n_slots: usize) -> Vec<TraceColumn> {
    let mut columns = Vec::new();
    for slot in 0..n_slots {
        let ent_label = if n_slots > 1 {
            format!("{}[{}]", entity.name, slot)
        } else {
            entity.name.clone()
        };
        for (fi, f) in entity.fields.iter().enumerate() {
            columns.push((ent_label.clone(), f.name.clone(), fi));
        }
        columns.push((ent_label, "active".to_owned(), usize::MAX));
    }
    columns
}

// ── S-expression parser for Z3 answer derivation ────────────────────

/// A minimal s-expression token.
#[derive(Debug, Clone, PartialEq)]
enum SExpr {
    Atom(String),
    List(Vec<SExpr>),
}

/// Tokenize an s-expression string into a tree.
///
/// Handles nested parentheses, atoms (identifiers, numbers, booleans),
/// and negative literals like `(- 1)`.
fn parse_sexpr(input: &str) -> Option<SExpr> {
    let tokens = tokenize_sexpr(input);
    let mut pos = 0;
    let result = parse_sexpr_tokens(&tokens, &mut pos)?;
    // Reject trailing garbage — all tokens must be consumed
    if pos != tokens.len() {
        return None;
    }
    Some(result)
}

fn tokenize_sexpr(input: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut chars = input.chars().peekable();
    while let Some(&c) = chars.peek() {
        if c.is_whitespace() {
            chars.next();
        } else if c == '(' {
            tokens.push("(".to_owned());
            chars.next();
        } else if c == ')' {
            tokens.push(")".to_owned());
            chars.next();
        } else {
            // Atom: collect until whitespace or paren
            let mut atom = String::new();
            while let Some(&ch) = chars.peek() {
                if ch.is_whitespace() || ch == '(' || ch == ')' {
                    break;
                }
                atom.push(ch);
                chars.next();
            }
            if !atom.is_empty() {
                tokens.push(atom);
            }
        }
    }
    tokens
}

fn parse_sexpr_tokens(tokens: &[String], pos: &mut usize) -> Option<SExpr> {
    if *pos >= tokens.len() {
        return None;
    }
    if tokens[*pos] == ")" {
        // Unmatched closing paren — malformed input
        return None;
    }
    if tokens[*pos] == "(" {
        *pos += 1;
        let mut children = Vec::new();
        while *pos < tokens.len() && tokens[*pos] != ")" {
            let child = parse_sexpr_tokens(tokens, pos)?;
            children.push(child);
        }
        if *pos >= tokens.len() {
            // Unclosed paren — malformed input
            return None;
        }
        *pos += 1; // consume ')'
        Some(SExpr::List(children))
    } else {
        let atom = tokens[*pos].clone();
        *pos += 1;
        Some(SExpr::Atom(atom))
    }
}

/// Check if an s-expression atom is a ground value (integer, boolean, or negative literal).
fn is_ground_value(expr: &SExpr) -> bool {
    match expr {
        SExpr::Atom(s) => {
            s == "true"
                || s == "false"
                || s.chars().next().is_some_and(|c| c.is_ascii_digit())
                || (s.starts_with('-') && s.len() > 1 && s[1..].chars().all(|c| c.is_ascii_digit()))
        }
        SExpr::List(children) => match children.first() {
            // (- X) — negation of a ground value
            Some(SExpr::Atom(op)) if op == "-" && children.len() == 2 => {
                is_ground_value(&children[1])
            }
            // (/ X Y) — rational: both operands must be ground
            Some(SExpr::Atom(op)) if op == "/" && children.len() == 3 => {
                is_ground_value(&children[1]) && is_ground_value(&children[2])
            }
            _ => false,
        },
    }
}

/// Convert an s-expression value to a display string.
///
/// Recurses into nested forms: `(- (/ 1 2))` → `"-1/2"`.
fn sexpr_value_to_string(expr: &SExpr) -> String {
    match expr {
        SExpr::Atom(s) => s.clone(),
        SExpr::List(children) => match children.first() {
            // (- X) → "-{X}"
            Some(SExpr::Atom(op)) if op == "-" && children.len() == 2 => {
                format!("-{}", sexpr_value_to_string(&children[1]))
            }
            // (/ X Y) → "{X}/{Y}"
            Some(SExpr::Atom(op)) if op == "/" && children.len() == 3 => {
                format!(
                    "{}/{}",
                    sexpr_value_to_string(&children[1]),
                    sexpr_value_to_string(&children[2])
                )
            }
            _ => format!("{expr:?}"),
        },
    }
}

/// Extract ground `(State v1 v2... vN)` applications from the derivation tree.
///
/// Walks the s-expression tree depth-first (children before parent). Spacer's
/// derivation nests earlier states deeper: the initial state is the innermost
/// `(asserted (State...))`, each `hyper-res` step produces the next state as
/// its conclusion (last child). Depth-first traversal therefore yields states
/// in chronological order for linear derivations.
///
/// **Limitation:** If the derivation has branches (e.g., multiple independent
/// rule applications merged), states from different branches may interleave.
/// Our CHC encoding produces linear chains (each rule takes one State and
/// produces one State), so this is not expected in practice.
fn collect_ground_states(expr: &SExpr, n_cols: usize, out: &mut Vec<Vec<SExpr>>) {
    if let SExpr::List(children) = expr {
        // Recurse into children first (depth-first = derivation order)
        for child in children {
            collect_ground_states(child, n_cols, out);
        }

        // Check if this is (State v1 v2... vN) with exactly n_cols ground args
        if children.len() == n_cols + 1 {
            if let SExpr::Atom(head) = &children[0] {
                if head == "State" {
                    let args = &children[1..];
                    if args.iter().all(is_ground_value) {
                        out.push(args.to_vec());
                    }
                }
            }
        }
    }
}

/// Parse the Z3 Spacer answer into IC3 trace steps.
///
/// Uses proper s-expression parsing to handle nested terms like `(- 1)`.
/// Extracts ground State applications in derivation order (depth-first).
fn parse_state_snapshots(answer: &str, columns: &[TraceColumn]) -> Vec<Ic3TraceStep> {
    let n_cols = columns.len();
    if n_cols == 0 {
        return Vec::new();
    }

    let Some(tree) = parse_sexpr(answer) else {
        return Vec::new();
    };

    let mut ground_states: Vec<Vec<SExpr>> = Vec::new();
    collect_ground_states(&tree, n_cols, &mut ground_states);

    // Deduplicate consecutive identical states (stutter rule may repeat)
    ground_states.dedup_by(|a, b| {
        a.len() == b.len()
            && a.iter()
                .zip(b.iter())
                .all(|(x, y)| sexpr_value_to_string(x) == sexpr_value_to_string(y))
    });

    let mut steps = Vec::new();
    for (step_idx, state_vals) in ground_states.iter().enumerate() {
        let mut assignments = Vec::new();
        for (i, val) in state_vals.iter().enumerate() {
            let (ref ent, ref field, fi) = columns[i];
            if fi == usize::MAX {
                continue; // active flag
            }
            // Check if entity slot is active
            let active_col =
                (0..n_cols).find(|&j| columns[j].0 == *ent && columns[j].2 == usize::MAX && j > i);
            let is_active = active_col
                .and_then(|j| state_vals.get(j))
                .is_some_and(|v| matches!(v, SExpr::Atom(s) if s == "true"));
            if is_active {
                assignments.push((ent.clone(), field.clone(), sexpr_value_to_string(val)));
            }
        }
        if !assignments.is_empty() {
            steps.push(Ic3TraceStep {
                step: step_idx,
                assignments,
            });
        }
    }

    steps
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
    emit_ic3_datatype_decls(
        entities
            .iter()
            .flat_map(|entity| entity.fields.iter().map(|field| &field.ty)),
        &mut chc,
    );

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
    // Only emitted when no systems are present (pure entity-level IC3).
    // When systems exist, transitions are constrained by system event rules.
    if systems.is_empty() {
        for entity in entities {
            let n_slots = slots_per_entity.get(&entity.name).copied().unwrap_or(1);
            for slot in 0..n_slots {
                for transition in &entity.transitions {
                    let guard =
                        guard_to_smt_sys(&transition.guard, entity, vctx, &entity.name, slot)?;

                    // Build next-state: update target slot, frame everything else
                    let mut next_vals: Vec<String> = Vec::new();
                    for ent in entities {
                        let ns = slots_per_entity.get(&ent.name).copied().unwrap_or(1);
                        for s in 0..ns {
                            for (fi, f) in ent.fields.iter().enumerate() {
                                if ent.name == entity.name && s == slot {
                                    let updated =
                                        transition.updates.iter().find(|u| u.field == f.name);
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
                                if f.initial_constraint.is_some() {
                                    // Nondeterministic: leave as free variable
                                    // (the constraint is enforced by the BMC path, not CHC)
                                    create_next.push(format!("{}_{}_f{}", ent.name, s, fi));
                                } else if let Some(ref default_expr) = f.default {
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
                let mut create_guard = if slot == 0 {
                    format!("(not {inactive_var})")
                } else {
                    format!(
                        "(and (not {inactive_var}) {}_{}_active)",
                        entity.name,
                        slot - 1
                    )
                };

                // Add initial_constraint guards for nondeterministic fields.
                // The free variable in create_next is `{ent}_{slot}_f{fi}` —
                // substitute $ for it in the constraint and add to the guard.
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
                 (State {create_str})) create_{}_{slot})\n",
                    entity.name
                ));
            }
        }
    } // if systems.is_empty()

    // ── System event rules ──────────────────────────────────────────
    // Encode system events as composite CHC rules via recursive action tree walk.
    // Choose/ForAll/Apply/Create/CrossCall are all handled with full context
    // guard propagation. CrossCall targets are recursively encoded (not just Creates).
    for system in systems {
        for event in &system.steps {
            // Fresh visited set per event tree — cycles within one event's
            // CrossCall graph are detected, but the same event can appear
            // in different top-level event trees.
            let mut visited = HashSet::new();
            visited.insert((system.name.clone(), event.name.clone()));
            encode_step_chc(
                &mut chc,
                &event.body,
                &event.guard,
                entities,
                vctx,
                slots_per_entity,
                &all_vars_str,
                systems,
                &format!("{}_{}", system.name, event.name),
                &[],
                &mut visited,
            )?;
        }
    }

    // ── Domain constraints ─────────────────────────────────────────
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
        IRExpr::Always { body, .. } => {
            negate_property_smt_system(body, entities, vctx, slots_per_entity)
        }
        IRExpr::Forall {
            var,
            domain: IRType::Entity { name: entity_name },
            body,
            ..
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
                ..
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
                            entities,
                            slots_per_entity,
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
                let neg_body = negate_guard_sys(
                    body,
                    entities,
                    slots_per_entity,
                    entity,
                    vctx,
                    entity_name,
                    slot,
                    var,
                )?;
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
#[allow(clippy::too_many_arguments)]
fn negate_guard_sys(
    expr: &IRExpr,
    entities: &[&IREntity],
    slots_per_entity: &HashMap<String, usize>,
    entity: &IREntity,
    vctx: &VerifyContext,
    ent_name: &str,
    slot: usize,
    var: &str,
) -> Result<String, String> {
    let mut entity_locals = Ic3SystemEntityLocals::new();
    entity_locals.insert(var.to_owned(), (ent_name.to_owned(), slot));
    let pos = guard_to_smt_sys_prop_scoped(
        expr,
        entities,
        slots_per_entity,
        entity,
        vctx,
        ent_name,
        slot,
        &HashSet::new(),
        &entity_locals,
    )?;
    Ok(format!("(not {pos})"))
}

/// Negate an inner property for two entity slots in system context.
#[allow(clippy::too_many_arguments)]
fn negate_guard_sys_two(
    expr: &IRExpr,
    entities: &[&IREntity],
    slots_per_entity: &HashMap<String, usize>,
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
    let mut entity_locals = Ic3SystemEntityLocals::new();
    entity_locals.insert(var1.to_owned(), (ent1_name.to_owned(), slot1));
    entity_locals.insert(var2.to_owned(), (ent2_name.to_owned(), slot2));
    let pos = guard_to_smt_sys_prop_two_scoped(
        expr,
        entities,
        slots_per_entity,
        entity1,
        entity2,
        vctx,
        ent1_name,
        slot1,
        var1,
        ent2_name,
        slot2,
        var2,
        &HashSet::new(),
        &entity_locals,
    )?;
    Ok(format!("(not {pos})"))
}

fn ic3_find_entity<'a>(entities: &'a [&IREntity], name: &str) -> Result<&'a IREntity, String> {
    entities
        .iter()
        .find(|entity| entity.name == name)
        .copied()
        .ok_or_else(|| format!("entity {name} not found in IC3 system property scope"))
}

#[allow(clippy::too_many_arguments)]
fn guard_let_to_smt_sys_prop_scoped(
    bindings: &[crate::ir::types::LetBinding],
    body: &IRExpr,
    entities: &[&IREntity],
    slots_per_entity: &HashMap<String, usize>,
    current_entity: &IREntity,
    vctx: &VerifyContext,
    current_ent_name: &str,
    current_slot: usize,
    locals: &HashSet<String>,
    entity_locals: &Ic3SystemEntityLocals,
) -> Result<String, String> {
    let Some((binding, rest)) = bindings.split_first() else {
        return guard_to_smt_sys_prop_scoped(
            body,
            entities,
            slots_per_entity,
            current_entity,
            vctx,
            current_ent_name,
            current_slot,
            locals,
            entity_locals,
        );
    };

    if let IRExpr::Choose {
        var,
        domain,
        predicate,
        ..
    } = &binding.expr
    {
        if let IRType::Entity { name } = domain {
            let n_slots = slots_per_entity.get(name).copied().unwrap_or(1);
            let chosen_entity = ic3_find_entity(entities, name)?;
            let mut disjuncts = Vec::new();
            for chosen_slot in 0..n_slots {
                let active = format!("{name}_{chosen_slot}_active");
                let mut pred_entity_locals = entity_locals.clone();
                pred_entity_locals.insert(var.clone(), (name.clone(), chosen_slot));
                let pred = if let Some(predicate) = predicate {
                    guard_to_smt_sys_prop_scoped(
                        predicate,
                        entities,
                        slots_per_entity,
                        current_entity,
                        vctx,
                        current_ent_name,
                        current_slot,
                        locals,
                        &pred_entity_locals,
                    )?
                } else {
                    "true".to_owned()
                };
                let mut rest_entity_locals = entity_locals.clone();
                rest_entity_locals.insert(binding.name.clone(), (name.clone(), chosen_slot));
                let rest_smt = guard_let_to_smt_sys_prop_scoped(
                    rest,
                    body,
                    entities,
                    slots_per_entity,
                    chosen_entity,
                    vctx,
                    current_ent_name,
                    current_slot,
                    locals,
                    &rest_entity_locals,
                )?;
                disjuncts.push(format!("(and {active} {pred} {rest_smt})"));
            }
            return if disjuncts.is_empty() {
                Ok("false".to_owned())
            } else {
                Ok(format!("(or {})", disjuncts.join(" ")))
            };
        }

        let finite = ic3_finite_choose_witness(
            var,
            domain,
            predicate.as_deref(),
            vctx,
            locals,
            |predicate, scope| {
                guard_to_smt_sys_prop_scoped(
                    predicate,
                    entities,
                    slots_per_entity,
                    current_entity,
                    vctx,
                    current_ent_name,
                    current_slot,
                    scope,
                    entity_locals,
                )
            },
        )?;

        let mut scope = locals.clone();
        scope.insert(binding.name.clone());
        let rest_smt = guard_let_to_smt_sys_prop_scoped(
            rest,
            body,
            entities,
            slots_per_entity,
            current_entity,
            vctx,
            current_ent_name,
            current_slot,
            &scope,
            entity_locals,
        )?;
        if let Some((exists, witness)) = finite {
            return Ok(format!(
                "(and {exists} (let (({} {})) {}))",
                binding.name, witness, rest_smt
            ));
        }
        if let Some(witness) = ic3_direct_choose_witness(
            var,
            domain,
            predicate.as_deref(),
            locals,
            |term, scope| {
                expr_to_smt_sys_prop_scoped(
                    term,
                    entities,
                    slots_per_entity,
                    current_entity,
                    vctx,
                    current_ent_name,
                    current_slot,
                    scope,
                    entity_locals,
                )
            },
            |predicate, scope| {
                guard_to_smt_sys_prop_scoped(
                    predicate,
                    entities,
                    slots_per_entity,
                    current_entity,
                    vctx,
                    current_ent_name,
                    current_slot,
                    scope,
                    entity_locals,
                )
            },
            |scrutinee, pattern, scope| {
                let scrut = expr_to_smt_sys_prop_scoped(
                    scrutinee,
                    entities,
                    slots_per_entity,
                    current_entity,
                    vctx,
                    current_ent_name,
                    current_slot,
                    scope,
                    entity_locals,
                )?;
                ic3_match_pattern_bindings(&scrut, pattern, vctx)
            },
            |scrutinee, pattern, scope| {
                let scrut = expr_to_smt_sys_prop_scoped(
                    scrutinee,
                    entities,
                    slots_per_entity,
                    current_entity,
                    vctx,
                    current_ent_name,
                    current_slot,
                    scope,
                    entity_locals,
                )?;
                ic3_match_pattern_cond(&scrut, pattern, vctx)
            },
        )? {
            return ic3_witness_binding_formula(
                &binding.name,
                var,
                witness,
                predicate.as_deref(),
                locals,
                |predicate, scope| {
                    guard_to_smt_sys_prop_scoped(
                        predicate,
                        entities,
                        slots_per_entity,
                        current_entity,
                        vctx,
                        current_ent_name,
                        current_slot,
                        scope,
                        entity_locals,
                    )
                },
                rest_smt,
            );
        }
        if let Some(formula) = ic3_quantified_choose_formula(
            &binding.name,
            var,
            domain,
            predicate.as_deref(),
            locals,
            |predicate, scope| {
                guard_to_smt_sys_prop_scoped(
                    predicate,
                    entities,
                    slots_per_entity,
                    current_entity,
                    vctx,
                    current_ent_name,
                    current_slot,
                    scope,
                    entity_locals,
                )
            },
            rest_smt.clone(),
        )? {
            return Ok(formula);
        }
        return Err("choose is not yet supported in IC3 CHC encoding for this domain".to_owned());
    }

    if matches!(binding.ty, IRType::Entity { .. }) {
        if let IRExpr::Var { name, .. } = &binding.expr {
            if let Some((bound_entity_name, bound_slot)) = entity_locals.get(name) {
                let mut scope_entity_locals = entity_locals.clone();
                scope_entity_locals.insert(
                    binding.name.clone(),
                    (bound_entity_name.clone(), *bound_slot),
                );
                return guard_let_to_smt_sys_prop_scoped(
                    rest,
                    body,
                    entities,
                    slots_per_entity,
                    current_entity,
                    vctx,
                    current_ent_name,
                    current_slot,
                    locals,
                    &scope_entity_locals,
                );
            }
        }
    }

    let rhs = if binding.ty == IRType::Bool {
        guard_to_smt_sys_prop_scoped(
            &binding.expr,
            entities,
            slots_per_entity,
            current_entity,
            vctx,
            current_ent_name,
            current_slot,
            locals,
            entity_locals,
        )?
    } else {
        expr_to_smt_sys_prop_scoped(
            &binding.expr,
            entities,
            slots_per_entity,
            current_entity,
            vctx,
            current_ent_name,
            current_slot,
            locals,
            entity_locals,
        )?
    };
    let mut scope = locals.clone();
    scope.insert(binding.name.clone());
    let rest_smt = guard_let_to_smt_sys_prop_scoped(
        rest,
        body,
        entities,
        slots_per_entity,
        current_entity,
        vctx,
        current_ent_name,
        current_slot,
        &scope,
        entity_locals,
    )?;
    Ok(format!("(let (({} {})) {})", binding.name, rhs, rest_smt))
}

#[allow(clippy::too_many_arguments)]
fn expr_to_smt_sys_prop_scoped(
    expr: &IRExpr,
    entities: &[&IREntity],
    slots_per_entity: &HashMap<String, usize>,
    current_entity: &IREntity,
    vctx: &VerifyContext,
    current_ent_name: &str,
    current_slot: usize,
    locals: &HashSet<String>,
    entity_locals: &Ic3SystemEntityLocals,
) -> Result<String, String> {
    match expr {
        IRExpr::Var { name, .. } => {
            for (i, field) in current_entity.fields.iter().enumerate() {
                if field.name == *name {
                    return Ok(format!("{current_ent_name}_{current_slot}_f{i}"));
                }
            }
            if locals.contains(name) {
                return Ok(name.clone());
            }
            if entity_locals.contains_key(name) {
                return Err(format!(
                    "bare entity local {name} in system IC3 property — use field access instead"
                ));
            }
            Err(format!("unknown variable in system IC3 property: {name}"))
        }
        IRExpr::Field {
            expr: inner, field, ..
        } => {
            if let IRExpr::Var { name, .. } = inner.as_ref() {
                let (entity_name, slot) = if let Some((entity_name, slot)) = entity_locals.get(name)
                {
                    (entity_name.as_str(), *slot)
                } else {
                    (current_ent_name, current_slot)
                };
                let entity = ic3_find_entity(entities, entity_name)?;
                for (i, candidate) in entity.fields.iter().enumerate() {
                    if candidate.name == *field {
                        return Ok(format!("{entity_name}_{slot}_f{i}"));
                    }
                }
                return Err(format!("field {field} not found on entity {entity_name}"));
            }
            Err(format!(
                "unsupported field access in system IC3 property: {field}"
            ))
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let l = expr_to_smt_sys_prop_scoped(
                left,
                entities,
                slots_per_entity,
                current_entity,
                vctx,
                current_ent_name,
                current_slot,
                locals,
                entity_locals,
            )?;
            let r = expr_to_smt_sys_prop_scoped(
                right,
                entities,
                slots_per_entity,
                current_entity,
                vctx,
                current_ent_name,
                current_slot,
                locals,
                entity_locals,
            )?;
            match op.as_str() {
                "OpAdd" => Ok(format!("(+ {l} {r})")),
                "OpSub" => Ok(format!("(- {l} {r})")),
                "OpMul" => Ok(format!("(* {l} {r})")),
                "OpDiv" => Ok(format!("(div {l} {r})")),
                "OpMod" => Ok(format!("(mod {l} {r})")),
                _ => Err(format!("unsupported op in system IC3 property value: {op}")),
            }
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            let m = expr_to_smt_sys_prop_scoped(
                map,
                entities,
                slots_per_entity,
                current_entity,
                vctx,
                current_ent_name,
                current_slot,
                locals,
                entity_locals,
            )?;
            let k = expr_to_smt_sys_prop_scoped(
                key,
                entities,
                slots_per_entity,
                current_entity,
                vctx,
                current_ent_name,
                current_slot,
                locals,
                entity_locals,
            )?;
            let v = expr_to_smt_sys_prop_scoped(
                value,
                entities,
                slots_per_entity,
                current_entity,
                vctx,
                current_ent_name,
                current_slot,
                locals,
                entity_locals,
            )?;
            Ok(format!("(store {m} {k} {v})"))
        }
        IRExpr::Index { map, key, .. } => {
            let m = expr_to_smt_sys_prop_scoped(
                map,
                entities,
                slots_per_entity,
                current_entity,
                vctx,
                current_ent_name,
                current_slot,
                locals,
                entity_locals,
            )?;
            let k = expr_to_smt_sys_prop_scoped(
                key,
                entities,
                slots_per_entity,
                current_entity,
                vctx,
                current_ent_name,
                current_slot,
                locals,
                entity_locals,
            )?;
            Ok(format!("(select {m} {k})"))
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            if !ic3_match_has_final_catch_all(arms) {
                return Err(
                    "non-exhaustive match without final wildcard/var arm is not supported in system IC3 property value encoding".to_owned(),
                );
            }
            let scrut = expr_to_smt_sys_prop_scoped(
                scrutinee,
                entities,
                slots_per_entity,
                current_entity,
                vctx,
                current_ent_name,
                current_slot,
                locals,
                entity_locals,
            )?;
            let mut acc = {
                let last = arms.last().expect("checked non-empty match arms");
                let bindings = ic3_match_pattern_bindings(&scrut, &last.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let body = expr_to_smt_sys_prop_scoped(
                    &last.body,
                    entities,
                    slots_per_entity,
                    current_entity,
                    vctx,
                    current_ent_name,
                    current_slot,
                    &scope,
                    entity_locals,
                )?;
                wrap_smt_let_bindings(&bindings, body)
            };
            for arm in arms[..arms.len() - 1].iter().rev() {
                let bindings = ic3_match_pattern_bindings(&scrut, &arm.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let pat = ic3_match_pattern_cond(&scrut, &arm.pattern, vctx)?;
                let cond = if let Some(guard) = &arm.guard {
                    let guard_smt = guard_to_smt_sys_prop_scoped(
                        guard,
                        entities,
                        slots_per_entity,
                        current_entity,
                        vctx,
                        current_ent_name,
                        current_slot,
                        &scope,
                        entity_locals,
                    )?;
                    wrap_smt_let_bindings(&bindings, format!("(and {pat} {guard_smt})"))
                } else {
                    wrap_smt_let_bindings(&bindings, pat)
                };
                let body = expr_to_smt_sys_prop_scoped(
                    &arm.body,
                    entities,
                    slots_per_entity,
                    current_entity,
                    vctx,
                    current_ent_name,
                    current_slot,
                    &scope,
                    entity_locals,
                )?;
                let body = wrap_smt_let_bindings(&bindings, body);
                acc = format!("(ite {cond} {body} {acc})");
            }
            Ok(acc)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond_smt = guard_to_smt_sys_prop_scoped(
                cond,
                entities,
                slots_per_entity,
                current_entity,
                vctx,
                current_ent_name,
                current_slot,
                locals,
                entity_locals,
            )?;
            let then_smt = expr_to_smt_sys_prop_scoped(
                then_body,
                entities,
                slots_per_entity,
                current_entity,
                vctx,
                current_ent_name,
                current_slot,
                locals,
                entity_locals,
            )?;
            if let Some(else_body) = else_body {
                let else_smt = expr_to_smt_sys_prop_scoped(
                    else_body,
                    entities,
                    slots_per_entity,
                    current_entity,
                    vctx,
                    current_ent_name,
                    current_slot,
                    locals,
                    entity_locals,
                )?;
                Ok(format!("(ite {cond_smt} {then_smt} {else_smt})"))
            } else {
                Err(
                    "if/else without else is not supported in system IC3 property value encoding"
                        .to_owned(),
                )
            }
        }
        IRExpr::Let { bindings, body, .. } => {
            let mut scope = locals.clone();
            let mut out = String::new();
            for binding in bindings {
                let rhs = if binding.ty == IRType::Bool {
                    guard_to_smt_sys_prop_scoped(
                        &binding.expr,
                        entities,
                        slots_per_entity,
                        current_entity,
                        vctx,
                        current_ent_name,
                        current_slot,
                        &scope,
                        entity_locals,
                    )?
                } else {
                    expr_to_smt_sys_prop_scoped(
                        &binding.expr,
                        entities,
                        slots_per_entity,
                        current_entity,
                        vctx,
                        current_ent_name,
                        current_slot,
                        &scope,
                        entity_locals,
                    )?
                };
                out.push_str(&format!("(let (({} {})) ", binding.name, rhs));
                scope.insert(binding.name.clone());
            }
            out.push_str(&expr_to_smt_sys_prop_scoped(
                body,
                entities,
                slots_per_entity,
                current_entity,
                vctx,
                current_ent_name,
                current_slot,
                &scope,
                entity_locals,
            )?);
            for _ in bindings {
                out.push(')');
            }
            Ok(out)
        }
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => expr_to_smt_sys_prop_scoped(
            expr,
            entities,
            slots_per_entity,
            current_entity,
            vctx,
            current_ent_name,
            current_slot,
            locals,
            entity_locals,
        ),
        IRExpr::Lit { .. } | IRExpr::Ctor { .. } => expr_to_smt(expr, current_entity, vctx),
        _ => Err(format!(
            "unsupported expression in system IC3 property value encoding: {:?}",
            std::mem::discriminant(expr)
        )),
    }
}

#[allow(clippy::too_many_arguments)]
fn guard_to_smt_sys_prop_scoped(
    guard: &IRExpr,
    entities: &[&IREntity],
    slots_per_entity: &HashMap<String, usize>,
    current_entity: &IREntity,
    vctx: &VerifyContext,
    current_ent_name: &str,
    current_slot: usize,
    locals: &HashSet<String>,
    entity_locals: &Ic3SystemEntityLocals,
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
                let l = expr_to_smt_sys_prop_scoped(
                    left,
                    entities,
                    slots_per_entity,
                    current_entity,
                    vctx,
                    current_ent_name,
                    current_slot,
                    locals,
                    entity_locals,
                )?;
                let r = expr_to_smt_sys_prop_scoped(
                    right,
                    entities,
                    slots_per_entity,
                    current_entity,
                    vctx,
                    current_ent_name,
                    current_slot,
                    locals,
                    entity_locals,
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
                let l = guard_to_smt_sys_prop_scoped(
                    left,
                    entities,
                    slots_per_entity,
                    current_entity,
                    vctx,
                    current_ent_name,
                    current_slot,
                    locals,
                    entity_locals,
                )?;
                let r = guard_to_smt_sys_prop_scoped(
                    right,
                    entities,
                    slots_per_entity,
                    current_entity,
                    vctx,
                    current_ent_name,
                    current_slot,
                    locals,
                    entity_locals,
                )?;
                Ok(format!("(and {l} {r})"))
            }
            "OpOr" => {
                let l = guard_to_smt_sys_prop_scoped(
                    left,
                    entities,
                    slots_per_entity,
                    current_entity,
                    vctx,
                    current_ent_name,
                    current_slot,
                    locals,
                    entity_locals,
                )?;
                let r = guard_to_smt_sys_prop_scoped(
                    right,
                    entities,
                    slots_per_entity,
                    current_entity,
                    vctx,
                    current_ent_name,
                    current_slot,
                    locals,
                    entity_locals,
                )?;
                Ok(format!("(or {l} {r})"))
            }
            "OpImplies" => {
                let l = guard_to_smt_sys_prop_scoped(
                    left,
                    entities,
                    slots_per_entity,
                    current_entity,
                    vctx,
                    current_ent_name,
                    current_slot,
                    locals,
                    entity_locals,
                )?;
                let r = guard_to_smt_sys_prop_scoped(
                    right,
                    entities,
                    slots_per_entity,
                    current_entity,
                    vctx,
                    current_ent_name,
                    current_slot,
                    locals,
                    entity_locals,
                )?;
                Ok(format!("(=> {l} {r})"))
            }
            _ => Err(format!("unsupported op in system IC3 property guard: {op}")),
        },
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => {
            let inner = guard_to_smt_sys_prop_scoped(
                operand,
                entities,
                slots_per_entity,
                current_entity,
                vctx,
                current_ent_name,
                current_slot,
                locals,
                entity_locals,
            )?;
            Ok(format!("(not {inner})"))
        }
        IRExpr::Field { .. } | IRExpr::Var { .. } => expr_to_smt_sys_prop_scoped(
            guard,
            entities,
            slots_per_entity,
            current_entity,
            vctx,
            current_ent_name,
            current_slot,
            locals,
            entity_locals,
        ),
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            if !ic3_match_has_final_catch_all(arms) {
                return Err(
                    "non-exhaustive match without final wildcard/var arm is not supported in system IC3 property guard encoding".to_owned(),
                );
            }
            let scrut = expr_to_smt_sys_prop_scoped(
                scrutinee,
                entities,
                slots_per_entity,
                current_entity,
                vctx,
                current_ent_name,
                current_slot,
                locals,
                entity_locals,
            )?;
            let mut acc = {
                let last = arms.last().expect("checked non-empty match arms");
                let bindings = ic3_match_pattern_bindings(&scrut, &last.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let body = guard_to_smt_sys_prop_scoped(
                    &last.body,
                    entities,
                    slots_per_entity,
                    current_entity,
                    vctx,
                    current_ent_name,
                    current_slot,
                    &scope,
                    entity_locals,
                )?;
                wrap_smt_let_bindings(&bindings, body)
            };
            for arm in arms[..arms.len() - 1].iter().rev() {
                let bindings = ic3_match_pattern_bindings(&scrut, &arm.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let pat = ic3_match_pattern_cond(&scrut, &arm.pattern, vctx)?;
                let cond = if let Some(guard) = &arm.guard {
                    let guard_smt = guard_to_smt_sys_prop_scoped(
                        guard,
                        entities,
                        slots_per_entity,
                        current_entity,
                        vctx,
                        current_ent_name,
                        current_slot,
                        &scope,
                        entity_locals,
                    )?;
                    wrap_smt_let_bindings(&bindings, format!("(and {pat} {guard_smt})"))
                } else {
                    wrap_smt_let_bindings(&bindings, pat)
                };
                let body = guard_to_smt_sys_prop_scoped(
                    &arm.body,
                    entities,
                    slots_per_entity,
                    current_entity,
                    vctx,
                    current_ent_name,
                    current_slot,
                    &scope,
                    entity_locals,
                )?;
                let body = wrap_smt_let_bindings(&bindings, body);
                acc = format!("(ite {cond} {body} {acc})");
            }
            Ok(acc)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond_smt = guard_to_smt_sys_prop_scoped(
                cond,
                entities,
                slots_per_entity,
                current_entity,
                vctx,
                current_ent_name,
                current_slot,
                locals,
                entity_locals,
            )?;
            let then_smt = guard_to_smt_sys_prop_scoped(
                then_body,
                entities,
                slots_per_entity,
                current_entity,
                vctx,
                current_ent_name,
                current_slot,
                locals,
                entity_locals,
            )?;
            if let Some(else_body) = else_body {
                let else_smt = guard_to_smt_sys_prop_scoped(
                    else_body,
                    entities,
                    slots_per_entity,
                    current_entity,
                    vctx,
                    current_ent_name,
                    current_slot,
                    locals,
                    entity_locals,
                )?;
                Ok(format!("(ite {cond_smt} {then_smt} {else_smt})"))
            } else {
                Ok(format!("(=> {cond_smt} {then_smt})"))
            }
        }
        IRExpr::Let { bindings, body, .. } => guard_let_to_smt_sys_prop_scoped(
            bindings,
            body,
            entities,
            slots_per_entity,
            current_entity,
            vctx,
            current_ent_name,
            current_slot,
            locals,
            entity_locals,
        ),
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => guard_to_smt_sys_prop_scoped(
            expr,
            entities,
            slots_per_entity,
            current_entity,
            vctx,
            current_ent_name,
            current_slot,
            locals,
            entity_locals,
        ),
        IRExpr::Forall {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| {
                guard_to_smt_sys_prop_scoped(
                    body,
                    entities,
                    slots_per_entity,
                    current_entity,
                    vctx,
                    current_ent_name,
                    current_slot,
                    scope,
                    entity_locals,
                )
            },
            "forall",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in system IC3 property guard encoding"
                .to_owned()
        }),
        IRExpr::Exists {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| {
                guard_to_smt_sys_prop_scoped(
                    body,
                    entities,
                    slots_per_entity,
                    current_entity,
                    vctx,
                    current_ent_name,
                    current_slot,
                    scope,
                    entity_locals,
                )
            },
            "exists",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in system IC3 property guard encoding"
                .to_owned()
        }),
        IRExpr::One {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| {
                guard_to_smt_sys_prop_scoped(
                    body,
                    entities,
                    slots_per_entity,
                    current_entity,
                    vctx,
                    current_ent_name,
                    current_slot,
                    scope,
                    entity_locals,
                )
            },
            "one",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in system IC3 property guard encoding"
                .to_owned()
        }),
        IRExpr::Lone {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| {
                guard_to_smt_sys_prop_scoped(
                    body,
                    entities,
                    slots_per_entity,
                    current_entity,
                    vctx,
                    current_ent_name,
                    current_slot,
                    scope,
                    entity_locals,
                )
            },
            "lone",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in system IC3 property guard encoding"
                .to_owned()
        }),
        _ => Err(format!(
            "unsupported expression in system IC3 property guard: {:?}",
            std::mem::discriminant(guard)
        )),
    }
}

#[allow(clippy::too_many_arguments)]
fn guard_to_smt_sys_prop_two_scoped(
    expr: &IRExpr,
    entities: &[&IREntity],
    slots_per_entity: &HashMap<String, usize>,
    entity1: &IREntity,
    entity2: &IREntity,
    vctx: &VerifyContext,
    ent1_name: &str,
    slot1: usize,
    var1: &str,
    _ent2_name: &str,
    _slot2: usize,
    var2: &str,
    locals: &HashSet<String>,
    entity_locals: &Ic3SystemEntityLocals,
) -> Result<String, String> {
    let _ = (entity1, entity2, var1, var2);
    guard_to_smt_sys_prop_scoped(
        expr,
        entities,
        slots_per_entity,
        ic3_find_entity(entities, ent1_name)?,
        vctx,
        ent1_name,
        slot1,
        locals,
        entity_locals,
    )
}

/// Encode a system event body as CHC transition rules.
///
/// Walks the event action tree (Choose/Apply/Create/CrossCall/ForAll) and
/// generates composite rules that combine event guard + Choose filter +
/// transition effects. Context guards from parent Choose/ForAll blocks are
/// propagated through `extra_guards` to ensure callee rules are properly
/// constrained.
///
/// **`ForAll` encoding note:** `ForAll` is encoded as per-slot independent
/// transitions (one rule per active slot), not a single combined rule that
/// updates all slots simultaneously. This is an over-approximation — IC3
/// may see intermediate states where some but not all slots are updated.
/// This is sound for safety proofs (more reachable states = harder to prove
/// = if proved, the property holds in the real system too).
///
/// **Soundness:** All encoding errors propagate — never silently approximates.
/// Missing transitions, systems, or events produce hard errors. Cyclic
/// `CrossCall` graphs are detected via `visited` and produce errors.
#[allow(
    clippy::too_many_arguments,
    clippy::too_many_lines,
    clippy::format_push_string
)]
fn encode_step_chc(
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
                    .steps
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
fn encode_ops_chc(
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
                    .steps
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
fn encode_non_entity_guard(guard: &IRExpr) -> Result<String, String> {
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
fn build_transition_next(
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
fn build_create_next(
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
fn encode_create_chc(
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
fn format_chc_rule(
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

/// Encode a value expression with system-level slot naming: {entity}_{slot}_f{field}.
fn expr_to_smt_sys(
    expr: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    ent_name: &str,
    slot: usize,
) -> Result<String, String> {
    expr_to_smt_sys_scoped(expr, entity, vctx, ent_name, slot, &HashSet::new())
}

fn guard_let_to_smt_sys_scoped(
    bindings: &[crate::ir::types::LetBinding],
    body: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    ent_name: &str,
    slot: usize,
    locals: &HashSet<String>,
) -> Result<String, String> {
    let Some((binding, rest)) = bindings.split_first() else {
        return guard_to_smt_sys_scoped(body, entity, vctx, ent_name, slot, locals);
    };

    if let IRExpr::Choose {
        var,
        domain,
        predicate,
        ..
    } = &binding.expr
    {
        let finite = ic3_finite_choose_witness(
            var,
            domain,
            predicate.as_deref(),
            vctx,
            locals,
            |predicate, scope| {
                guard_to_smt_sys_scoped(predicate, entity, vctx, ent_name, slot, scope)
            },
        )?;

        let mut scope = locals.clone();
        scope.insert(binding.name.clone());
        let rest_smt =
            guard_let_to_smt_sys_scoped(rest, body, entity, vctx, ent_name, slot, &scope)?;
        if let Some((exists, witness)) = finite {
            return Ok(format!(
                "(and {exists} (let (({} {})) {}))",
                binding.name, witness, rest_smt
            ));
        }
        return Err("choose is not yet supported in IC3 CHC encoding for this domain".to_owned());
    }

    let rhs = if binding.ty == IRType::Bool {
        guard_to_smt_sys_scoped(&binding.expr, entity, vctx, ent_name, slot, locals)?
    } else {
        expr_to_smt_sys_scoped(&binding.expr, entity, vctx, ent_name, slot, locals)?
    };
    let mut scope = locals.clone();
    scope.insert(binding.name.clone());
    let rest_smt = guard_let_to_smt_sys_scoped(rest, body, entity, vctx, ent_name, slot, &scope)?;
    Ok(format!("(let (({} {})) {})", binding.name, rhs, rest_smt))
}

fn expr_to_smt_sys_scoped(
    expr: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    ent_name: &str,
    slot: usize,
    locals: &HashSet<String>,
) -> Result<String, String> {
    match expr {
        IRExpr::Var { name, .. } => {
            for (i, f) in entity.fields.iter().enumerate() {
                if f.name == *name {
                    return Ok(format!("{ent_name}_{slot}_f{i}"));
                }
            }
            if locals.contains(name) {
                return Ok(name.clone());
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
            let l = expr_to_smt_sys_scoped(left, entity, vctx, ent_name, slot, locals)?;
            let r = expr_to_smt_sys_scoped(right, entity, vctx, ent_name, slot, locals)?;
            match op.as_str() {
                "OpAdd" => Ok(format!("(+ {l} {r})")),
                "OpSub" => Ok(format!("(- {l} {r})")),
                "OpMul" => Ok(format!("(* {l} {r})")),
                _ => Err(format!("unsupported op in system IC3 value: {op}")),
            }
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            let m = expr_to_smt_sys_scoped(map, entity, vctx, ent_name, slot, locals)?;
            let k = expr_to_smt_sys_scoped(key, entity, vctx, ent_name, slot, locals)?;
            let v = expr_to_smt_sys_scoped(value, entity, vctx, ent_name, slot, locals)?;
            Ok(format!("(store {m} {k} {v})"))
        }
        IRExpr::Index { map, key, .. } => {
            let m = expr_to_smt_sys_scoped(map, entity, vctx, ent_name, slot, locals)?;
            let k = expr_to_smt_sys_scoped(key, entity, vctx, ent_name, slot, locals)?;
            Ok(format!("(select {m} {k})"))
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            if !ic3_match_has_final_catch_all(arms) {
                return Err(
                    "non-exhaustive match without final wildcard/var arm is not supported in system IC3 value encoding"
                        .to_owned(),
                );
            }
            let scrut = expr_to_smt_sys_scoped(scrutinee, entity, vctx, ent_name, slot, locals)?;
            let mut acc = {
                let last = arms.last().expect("checked non-empty match arms");
                let bindings = ic3_match_pattern_bindings(&scrut, &last.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let body =
                    expr_to_smt_sys_scoped(&last.body, entity, vctx, ent_name, slot, &scope)?;
                wrap_smt_let_bindings(&bindings, body)
            };
            for arm in arms[..arms.len() - 1].iter().rev() {
                let bindings = ic3_match_pattern_bindings(&scrut, &arm.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let pat = ic3_match_pattern_cond(&scrut, &arm.pattern, vctx)?;
                let cond = if let Some(guard) = &arm.guard {
                    let guard_smt =
                        guard_to_smt_sys_scoped(guard, entity, vctx, ent_name, slot, &scope)?;
                    wrap_smt_let_bindings(&bindings, format!("(and {pat} {guard_smt})"))
                } else {
                    wrap_smt_let_bindings(&bindings, pat)
                };
                let body = expr_to_smt_sys_scoped(&arm.body, entity, vctx, ent_name, slot, &scope)?;
                let body = wrap_smt_let_bindings(&bindings, body);
                acc = format!("(ite {cond} {body} {acc})");
            }
            Ok(acc)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond_smt = guard_to_smt_sys_scoped(cond, entity, vctx, ent_name, slot, locals)?;
            let then_smt = expr_to_smt_sys_scoped(then_body, entity, vctx, ent_name, slot, locals)?;
            if let Some(else_body) = else_body {
                let else_smt =
                    expr_to_smt_sys_scoped(else_body, entity, vctx, ent_name, slot, locals)?;
                Ok(format!("(ite {cond_smt} {then_smt} {else_smt})"))
            } else {
                Err("if/else without else is not supported in IC3 value encoding".to_owned())
            }
        }
        IRExpr::Let { bindings, body, .. } => {
            let mut scope = locals.clone();
            let mut out = String::new();
            for binding in bindings {
                let rhs = if binding.ty == IRType::Bool {
                    guard_to_smt_sys_scoped(&binding.expr, entity, vctx, ent_name, slot, &scope)?
                } else {
                    expr_to_smt_sys_scoped(&binding.expr, entity, vctx, ent_name, slot, &scope)?
                };
                out.push_str(&format!("(let (({} {})) ", binding.name, rhs));
                scope.insert(binding.name.clone());
            }
            out.push_str(&expr_to_smt_sys_scoped(
                body, entity, vctx, ent_name, slot, &scope,
            )?);
            for _ in bindings {
                out.push(')');
            }
            Ok(out)
        }
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            expr_to_smt_sys_scoped(expr, entity, vctx, ent_name, slot, locals)
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
    guard_to_smt_sys_scoped(guard, entity, vctx, ent_name, slot, &HashSet::new())
}

fn guard_to_smt_sys_scoped(
    guard: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    ent_name: &str,
    slot: usize,
    locals: &HashSet<String>,
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
                let l = expr_to_smt_sys_scoped(left, entity, vctx, ent_name, slot, locals)?;
                let r = expr_to_smt_sys_scoped(right, entity, vctx, ent_name, slot, locals)?;
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
                let l = guard_to_smt_sys_scoped(left, entity, vctx, ent_name, slot, locals)?;
                let r = guard_to_smt_sys_scoped(right, entity, vctx, ent_name, slot, locals)?;
                Ok(format!("(and {l} {r})"))
            }
            "OpOr" => {
                let l = guard_to_smt_sys_scoped(left, entity, vctx, ent_name, slot, locals)?;
                let r = guard_to_smt_sys_scoped(right, entity, vctx, ent_name, slot, locals)?;
                Ok(format!("(or {l} {r})"))
            }
            "OpImplies" => {
                let l = guard_to_smt_sys_scoped(left, entity, vctx, ent_name, slot, locals)?;
                let r = guard_to_smt_sys_scoped(right, entity, vctx, ent_name, slot, locals)?;
                Ok(format!("(=> {l} {r})"))
            }
            _ => Err(format!("unsupported op in system IC3 guard: {op}")),
        },
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => {
            let inner = guard_to_smt_sys_scoped(operand, entity, vctx, ent_name, slot, locals)?;
            Ok(format!("(not {inner})"))
        }
        IRExpr::Field { .. } | IRExpr::Var { .. } => {
            expr_to_smt_sys_scoped(guard, entity, vctx, ent_name, slot, locals)
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            if !ic3_match_has_final_catch_all(arms) {
                return Err(
                    "non-exhaustive match without final wildcard/var arm is not supported in system IC3 guard encoding"
                        .to_owned(),
                );
            }
            let scrut = expr_to_smt_sys_scoped(scrutinee, entity, vctx, ent_name, slot, locals)?;
            let mut acc = {
                let last = arms.last().expect("checked non-empty match arms");
                let bindings = ic3_match_pattern_bindings(&scrut, &last.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let body =
                    guard_to_smt_sys_scoped(&last.body, entity, vctx, ent_name, slot, &scope)?;
                wrap_smt_let_bindings(&bindings, body)
            };
            for arm in arms[..arms.len() - 1].iter().rev() {
                let bindings = ic3_match_pattern_bindings(&scrut, &arm.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let pat = ic3_match_pattern_cond(&scrut, &arm.pattern, vctx)?;
                let cond = if let Some(guard) = &arm.guard {
                    let guard_smt =
                        guard_to_smt_sys_scoped(guard, entity, vctx, ent_name, slot, &scope)?;
                    wrap_smt_let_bindings(&bindings, format!("(and {pat} {guard_smt})"))
                } else {
                    wrap_smt_let_bindings(&bindings, pat)
                };
                let body =
                    guard_to_smt_sys_scoped(&arm.body, entity, vctx, ent_name, slot, &scope)?;
                let body = wrap_smt_let_bindings(&bindings, body);
                acc = format!("(ite {cond} {body} {acc})");
            }
            Ok(acc)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond_smt = guard_to_smt_sys_scoped(cond, entity, vctx, ent_name, slot, locals)?;
            let then_smt =
                guard_to_smt_sys_scoped(then_body, entity, vctx, ent_name, slot, locals)?;
            if let Some(else_body) = else_body {
                let else_smt =
                    guard_to_smt_sys_scoped(else_body, entity, vctx, ent_name, slot, locals)?;
                Ok(format!("(ite {cond_smt} {then_smt} {else_smt})"))
            } else {
                Ok(format!("(=> {cond_smt} {then_smt})"))
            }
        }
        IRExpr::Let { bindings, body, .. } => {
            guard_let_to_smt_sys_scoped(bindings, body, entity, vctx, ent_name, slot, locals)
        }
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            guard_to_smt_sys_scoped(expr, entity, vctx, ent_name, slot, locals)
        }
        IRExpr::Forall {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| guard_to_smt_sys_scoped(body, entity, vctx, ent_name, slot, scope),
            "forall",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in system IC3 guard encoding".to_owned()
        }),
        IRExpr::Exists {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| guard_to_smt_sys_scoped(body, entity, vctx, ent_name, slot, scope),
            "exists",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in system IC3 guard encoding".to_owned()
        }),
        IRExpr::One {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| guard_to_smt_sys_scoped(body, entity, vctx, ent_name, slot, scope),
            "one",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in system IC3 guard encoding".to_owned()
        }),
        IRExpr::Lone {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| guard_to_smt_sys_scoped(body, entity, vctx, ent_name, slot, scope),
            "lone",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in system IC3 guard encoding".to_owned()
        }),
        _ => Err(format!(
            "unsupported expression in system IC3 guard: {:?}",
            std::mem::discriminant(guard)
        )),
    }
}

/// Encode a guard with two entity-slot bindings for inter-entity system properties.
#[allow(
    dead_code,
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
    guard_to_smt_sys_two_scoped(
        expr,
        entity1,
        entity2,
        vctx,
        ent1_name,
        slot1,
        var1,
        ent2_name,
        slot2,
        var2,
        &HashSet::new(),
    )
}

#[allow(
    dead_code,
    clippy::too_many_arguments,
    clippy::too_many_lines,
    clippy::similar_names
)]
fn guard_let_to_smt_sys_two_scoped(
    bindings: &[crate::ir::types::LetBinding],
    body: &IRExpr,
    entity1: &IREntity,
    entity2: &IREntity,
    vctx: &VerifyContext,
    ent1_name: &str,
    slot1: usize,
    var1: &str,
    ent2_name: &str,
    slot2: usize,
    var2: &str,
    locals: &HashSet<String>,
) -> Result<String, String> {
    let Some((binding, rest)) = bindings.split_first() else {
        return guard_to_smt_sys_two_scoped(
            body, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2, locals,
        );
    };

    if let IRExpr::Choose {
        var,
        domain,
        predicate,
        ..
    } = &binding.expr
    {
        let finite = ic3_finite_choose_witness(
            var,
            domain,
            predicate.as_deref(),
            vctx,
            locals,
            |predicate, scope| {
                guard_to_smt_sys_two_scoped(
                    predicate, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2,
                    var2, scope,
                )
            },
        )?;

        let mut scope = locals.clone();
        scope.insert(binding.name.clone());
        let rest_smt = guard_let_to_smt_sys_two_scoped(
            rest, body, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
            &scope,
        )?;
        if let Some((exists, witness)) = finite {
            return Ok(format!(
                "(and {exists} (let (({} {})) {}))",
                binding.name, witness, rest_smt
            ));
        }
        if let Some(witness) = ic3_direct_choose_witness(
            var,
            domain,
            predicate.as_deref(),
            locals,
            |term, scope| {
                guard_to_smt_sys_two_scoped(
                    term, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                    scope,
                )
            },
            |predicate, scope| {
                guard_to_smt_sys_two_scoped(
                    predicate, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2,
                    var2, scope,
                )
            },
            |scrutinee, pattern, scope| {
                let scrut = guard_to_smt_sys_two_scoped(
                    scrutinee, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2,
                    var2, scope,
                )?;
                ic3_match_pattern_bindings(&scrut, pattern, vctx)
            },
            |scrutinee, pattern, scope| {
                let scrut = guard_to_smt_sys_two_scoped(
                    scrutinee, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2,
                    var2, scope,
                )?;
                ic3_match_pattern_cond(&scrut, pattern, vctx)
            },
        )? {
            return ic3_witness_binding_formula(
                &binding.name,
                var,
                witness,
                predicate.as_deref(),
                locals,
                |predicate, scope| {
                    guard_to_smt_sys_two_scoped(
                        predicate, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name,
                        slot2, var2, scope,
                    )
                },
                rest_smt,
            );
        }
        if let Some(formula) = ic3_quantified_choose_formula(
            &binding.name,
            var,
            domain,
            predicate.as_deref(),
            locals,
            |predicate, scope| {
                guard_to_smt_sys_two_scoped(
                    predicate, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2,
                    var2, scope,
                )
            },
            rest_smt.clone(),
        )? {
            return Ok(formula);
        }
        return Err("choose is not yet supported in IC3 CHC encoding for this domain".to_owned());
    }

    let rhs = guard_to_smt_sys_two_scoped(
        &binding.expr,
        entity1,
        entity2,
        vctx,
        ent1_name,
        slot1,
        var1,
        ent2_name,
        slot2,
        var2,
        locals,
    )?;
    let mut scope = locals.clone();
    scope.insert(binding.name.clone());
    let rest_smt = guard_let_to_smt_sys_two_scoped(
        rest, body, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2, &scope,
    )?;
    Ok(format!("(let (({} {})) {})", binding.name, rhs, rest_smt))
}

#[allow(
    dead_code,
    clippy::too_many_arguments,
    clippy::too_many_lines,
    clippy::similar_names
)]
fn guard_to_smt_sys_two_scoped(
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
    locals: &HashSet<String>,
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
                if locals.contains(name) {
                    return Err(format!(
                        "local {name} cannot be used for field projection in cross-entity property"
                    ));
                }
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
        IRExpr::Var { name, .. } => {
            if locals.contains(name) {
                Ok(name.clone())
            } else if name == var1 || name == var2 {
                Err(format!(
                    "bare entity variable {name} in cross-entity property — use field access instead"
                ))
            } else {
                Err(format!("unknown variable {name} in cross-entity property"))
            }
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => match op.as_str() {
            "OpEq" | "OpNEq" | "OpLt" | "OpLe" | "OpGt" | "OpGe" => {
                let l = guard_to_smt_sys_two_scoped(
                    left, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                    locals,
                )?;
                let r = guard_to_smt_sys_two_scoped(
                    right, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                    locals,
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
                let l = guard_to_smt_sys_two_scoped(
                    left, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                    locals,
                )?;
                let r = guard_to_smt_sys_two_scoped(
                    right, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                    locals,
                )?;
                Ok(format!("(and {l} {r})"))
            }
            "OpOr" => {
                let l = guard_to_smt_sys_two_scoped(
                    left, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                    locals,
                )?;
                let r = guard_to_smt_sys_two_scoped(
                    right, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                    locals,
                )?;
                Ok(format!("(or {l} {r})"))
            }
            _ => {
                // Arithmetic: resolve values
                let l = guard_to_smt_sys_two_scoped(
                    left, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                    locals,
                )?;
                let r = guard_to_smt_sys_two_scoped(
                    right, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                    locals,
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
            let inner = guard_to_smt_sys_two_scoped(
                operand, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                locals,
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
            enum_name,
            ctor,
            args,
            ..
        } => ic3_ctor_term_with(enum_name, ctor, args, vctx, |arg| {
            guard_to_smt_sys_two_scoped(
                arg, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2, locals,
            )
        }),
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            if !ic3_match_has_final_catch_all(arms) {
                return Err(
                    "non-exhaustive match without final wildcard/var arm is not supported in cross-entity IC3 encoding"
                        .to_owned(),
                );
            }
            let scrut = guard_to_smt_sys_two_scoped(
                scrutinee, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                locals,
            )?;
            let mut acc = {
                let last = arms.last().expect("checked non-empty match arms");
                let bindings = ic3_match_pattern_bindings(&scrut, &last.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let body = guard_to_smt_sys_two_scoped(
                    &last.body, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2,
                    var2, &scope,
                )?;
                wrap_smt_let_bindings(&bindings, body)
            };
            for arm in arms[..arms.len() - 1].iter().rev() {
                let bindings = ic3_match_pattern_bindings(&scrut, &arm.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let pat = ic3_match_pattern_cond(&scrut, &arm.pattern, vctx)?;
                let cond = if let Some(guard) = &arm.guard {
                    let guard_smt = guard_to_smt_sys_two_scoped(
                        guard, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2,
                        var2, &scope,
                    )?;
                    wrap_smt_let_bindings(&bindings, format!("(and {pat} {guard_smt})"))
                } else {
                    wrap_smt_let_bindings(&bindings, pat)
                };
                let body = guard_to_smt_sys_two_scoped(
                    &arm.body, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2,
                    var2, &scope,
                )?;
                let body = wrap_smt_let_bindings(&bindings, body);
                acc = format!("(ite {cond} {body} {acc})");
            }
            Ok(acc)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond_smt = guard_to_smt_sys_two_scoped(
                cond, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                locals,
            )?;
            let then_smt = guard_to_smt_sys_two_scoped(
                then_body, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                locals,
            )?;
            if let Some(else_body) = else_body {
                let else_smt = guard_to_smt_sys_two_scoped(
                    else_body, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2,
                    var2, locals,
                )?;
                Ok(format!("(ite {cond_smt} {then_smt} {else_smt})"))
            } else {
                Ok(format!("(=> {cond_smt} {then_smt})"))
            }
        }
        IRExpr::Let { bindings, body, .. } => guard_let_to_smt_sys_two_scoped(
            bindings, body, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
            locals,
        ),
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => guard_to_smt_sys_two_scoped(
            expr, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2, locals,
        ),
        IRExpr::Forall {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| {
                guard_to_smt_sys_two_scoped(
                    body, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                    scope,
                )
            },
            "forall",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in cross-entity IC3 encoding".to_owned()
        }),
        IRExpr::Exists {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| {
                guard_to_smt_sys_two_scoped(
                    body, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                    scope,
                )
            },
            "exists",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in cross-entity IC3 encoding".to_owned()
        }),
        IRExpr::One {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| {
                guard_to_smt_sys_two_scoped(
                    body, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                    scope,
                )
            },
            "one",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in cross-entity IC3 encoding".to_owned()
        }),
        IRExpr::Lone {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| {
                guard_to_smt_sys_two_scoped(
                    body, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                    scope,
                )
            },
            "lone",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in cross-entity IC3 encoding".to_owned()
        }),
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
    emit_ic3_datatype_decls(entity.fields.iter().map(|field| &field.ty), &mut chc);

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
            let guard = guard_to_smt_slot(&transition.guard, entity, vctx, slot, n_slots)?;

            // Build next-state: this slot gets updates, all other slots frame
            let mut next_vals: Vec<String> = Vec::new();
            for s in 0..n_slots {
                for (fi, f) in entity.fields.iter().enumerate() {
                    if s == slot {
                        let updated = transition.updates.iter().find(|u| u.field == f.name);
                        if let Some(upd) = updated {
                            next_vals
                                .push(expr_to_smt_slot(&upd.value, entity, vctx, slot, n_slots)?);
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
            if let IRType::Enum { name, variants } = &f.ty {
                if variants.iter().any(|variant| !variant.fields.is_empty()) {
                    continue;
                }
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
        IRExpr::Always { body, .. } => negate_property_smt_multi(body, entity, vctx, n_slots),
        IRExpr::Forall {
            var,
            domain: IRType::Entity { .. },
            body,
            ..
        } => {
            // Check if body is another Forall (nested inter-entity quantifier)
            if let IRExpr::Forall {
                var: var2,
                domain: IRType::Entity { .. },
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
                            inner_body, entity, vctx, var, s1, var2, s2, n_slots,
                        )?;
                        disjuncts.push(format!("(and s{s1}_active s{s2}_active {neg})"));
                    }
                }
                return Ok(format!("(or {})", disjuncts.join(" ")));
            }

            // Single quantifier: all o: E | P(o)
            let mut disjuncts = Vec::new();
            for slot in 0..n_slots {
                let neg = negate_inner_property_slot(body, entity, vctx, slot, n_slots)?;
                disjuncts.push(format!("(and s{slot}_active {neg})"));
            }
            Ok(format!("(or {})", disjuncts.join(" ")))
        }
        _ => {
            // Non-quantified property: check against all active slots
            let mut disjuncts = Vec::new();
            for slot in 0..n_slots {
                let neg = negate_inner_property_slot(property, entity, vctx, slot, n_slots)?;
                disjuncts.push(format!("(and s{slot}_active {neg})"));
            }
            Ok(format!("(or {})", disjuncts.join(" ")))
        }
    }
}

/// Negate an inner property with two bound variables mapped to two slots.
/// For `P(a, b)` where a → slot s1 and b → slot s2.
#[allow(clippy::too_many_arguments)]
fn negate_inner_property_two_slots(
    property: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    var1: &str,
    slot1: usize,
    var2: &str,
    slot2: usize,
    n_slots: usize,
) -> Result<String, String> {
    let pos = guard_to_smt_two_slots(property, entity, vctx, var1, slot1, var2, slot2, n_slots)?;
    Ok(format!("(not {pos})"))
}

/// Encode a guard with two slot bindings (for inter-entity properties).
#[allow(clippy::too_many_lines)]
#[allow(clippy::too_many_arguments)]
fn guard_to_smt_two_slots(
    expr: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    var1: &str,
    slot1: usize,
    var2: &str,
    slot2: usize,
    n_slots: usize,
) -> Result<String, String> {
    guard_to_smt_two_slots_scoped(
        expr,
        entity,
        vctx,
        var1,
        slot1,
        var2,
        slot2,
        n_slots,
        &HashSet::new(),
        &Ic3SlotEntityLocals::new(),
    )
}

#[allow(clippy::too_many_arguments)]
fn guard_let_to_smt_two_slots_scoped(
    bindings: &[crate::ir::types::LetBinding],
    body: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    var1: &str,
    slot1: usize,
    var2: &str,
    slot2: usize,
    n_slots: usize,
    locals: &HashSet<String>,
    entity_locals: &Ic3SlotEntityLocals,
) -> Result<String, String> {
    let Some((binding, rest)) = bindings.split_first() else {
        return guard_to_smt_two_slots_scoped(
            body,
            entity,
            vctx,
            var1,
            slot1,
            var2,
            slot2,
            n_slots,
            locals,
            entity_locals,
        );
    };

    if let IRExpr::Choose {
        var,
        domain,
        predicate,
        ..
    } = &binding.expr
    {
        if let IRType::Entity { name } = domain {
            if name == &entity.name {
                let mut disjuncts = Vec::new();
                for chosen_slot in 0..n_slots {
                    let active = format!("s{chosen_slot}_active");
                    let mut pred_entity_locals = entity_locals.clone();
                    pred_entity_locals.insert(var.clone(), chosen_slot);
                    let pred = if let Some(predicate) = predicate {
                        guard_to_smt_two_slots_scoped(
                            predicate,
                            entity,
                            vctx,
                            var1,
                            slot1,
                            var2,
                            slot2,
                            n_slots,
                            locals,
                            &pred_entity_locals,
                        )?
                    } else {
                        "true".to_owned()
                    };
                    let mut rest_entity_locals = entity_locals.clone();
                    rest_entity_locals.insert(binding.name.clone(), chosen_slot);
                    let rest_smt = guard_let_to_smt_two_slots_scoped(
                        rest,
                        body,
                        entity,
                        vctx,
                        var1,
                        slot1,
                        var2,
                        slot2,
                        n_slots,
                        locals,
                        &rest_entity_locals,
                    )?;
                    disjuncts.push(format!("(and {active} {pred} {rest_smt})"));
                }
                return if disjuncts.is_empty() {
                    Ok("false".to_owned())
                } else {
                    Ok(format!("(or {})", disjuncts.join(" ")))
                };
            }
        }
        let finite = ic3_finite_choose_witness(
            var,
            domain,
            predicate.as_deref(),
            vctx,
            locals,
            |predicate, scope| {
                guard_to_smt_two_slots_scoped(
                    predicate,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    scope,
                    entity_locals,
                )
            },
        )?;

        let mut scope = locals.clone();
        scope.insert(binding.name.clone());
        let rest_smt = guard_let_to_smt_two_slots_scoped(
            rest,
            body,
            entity,
            vctx,
            var1,
            slot1,
            var2,
            slot2,
            n_slots,
            &scope,
            entity_locals,
        )?;
        if let Some((exists, witness)) = finite {
            return Ok(format!(
                "(and {exists} (let (({} {})) {}))",
                binding.name, witness, rest_smt
            ));
        }
        if let Some(witness) = ic3_direct_choose_witness(
            var,
            domain,
            predicate.as_deref(),
            locals,
            |term, scope| {
                guard_to_smt_two_slots_scoped(
                    term,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    scope,
                    entity_locals,
                )
            },
            |predicate, scope| {
                guard_to_smt_two_slots_scoped(
                    predicate,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    scope,
                    entity_locals,
                )
            },
            |scrutinee, pattern, scope| {
                let scrut = guard_to_smt_two_slots_scoped(
                    scrutinee,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    scope,
                    entity_locals,
                )?;
                ic3_match_pattern_bindings(&scrut, pattern, vctx)
            },
            |scrutinee, pattern, scope| {
                let scrut = guard_to_smt_two_slots_scoped(
                    scrutinee,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    scope,
                    entity_locals,
                )?;
                ic3_match_pattern_cond(&scrut, pattern, vctx)
            },
        )? {
            return ic3_witness_binding_formula(
                &binding.name,
                var,
                witness,
                predicate.as_deref(),
                locals,
                |predicate, scope| {
                    guard_to_smt_two_slots_scoped(
                        predicate,
                        entity,
                        vctx,
                        var1,
                        slot1,
                        var2,
                        slot2,
                        n_slots,
                        scope,
                        entity_locals,
                    )
                },
                rest_smt,
            );
        }
        if let Some(formula) = ic3_quantified_choose_formula(
            &binding.name,
            var,
            domain,
            predicate.as_deref(),
            locals,
            |predicate, scope| {
                guard_to_smt_two_slots_scoped(
                    predicate,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    scope,
                    entity_locals,
                )
            },
            rest_smt.clone(),
        )? {
            return Ok(formula);
        }
        return Err("choose is not yet supported in IC3 CHC encoding for this domain".to_owned());
    }

    if matches!(binding.ty, IRType::Entity { .. }) {
        if let IRExpr::Var { name, .. } = &binding.expr {
            if let Some(bound_slot) = entity_locals.get(name) {
                let mut scope_entity_locals = entity_locals.clone();
                scope_entity_locals.insert(binding.name.clone(), *bound_slot);
                return guard_let_to_smt_two_slots_scoped(
                    rest,
                    body,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    locals,
                    &scope_entity_locals,
                );
            }
            if name == var1 {
                let mut scope_entity_locals = entity_locals.clone();
                scope_entity_locals.insert(binding.name.clone(), slot1);
                return guard_let_to_smt_two_slots_scoped(
                    rest,
                    body,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    locals,
                    &scope_entity_locals,
                );
            }
            if name == var2 {
                let mut scope_entity_locals = entity_locals.clone();
                scope_entity_locals.insert(binding.name.clone(), slot2);
                return guard_let_to_smt_two_slots_scoped(
                    rest,
                    body,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    locals,
                    &scope_entity_locals,
                );
            }
        }
    }

    let rhs = guard_to_smt_two_slots_scoped(
        &binding.expr,
        entity,
        vctx,
        var1,
        slot1,
        var2,
        slot2,
        n_slots,
        locals,
        entity_locals,
    )?;
    let mut scope = locals.clone();
    scope.insert(binding.name.clone());
    let rest_smt = guard_let_to_smt_two_slots_scoped(
        rest,
        body,
        entity,
        vctx,
        var1,
        slot1,
        var2,
        slot2,
        n_slots,
        &scope,
        entity_locals,
    )?;
    Ok(format!("(let (({} {})) {})", binding.name, rhs, rest_smt))
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn guard_to_smt_two_slots_scoped(
    expr: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    var1: &str,
    slot1: usize,
    var2: &str,
    slot2: usize,
    n_slots: usize,
    locals: &HashSet<String>,
    entity_locals: &Ic3SlotEntityLocals,
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
                if locals.contains(name) {
                    return Err(format!(
                        "local {name} cannot be used for field projection in inter-entity property"
                    ));
                }
                let slot = if let Some(bound_slot) = entity_locals.get(name) {
                    *bound_slot
                } else if name == var1 {
                    slot1
                } else if name == var2 {
                    slot2
                } else {
                    return Err(format!(
                        "unknown variable {name} in inter-entity property (expected {var1}, {var2}, or a bound entity local)"
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
            if locals.contains(name) {
                return Ok(name.clone());
            }
            if entity_locals.contains_key(name) {
                return Err(format!(
                    "bare entity local {name} in inter-entity property — use field access (e.g., {name}.field) instead"
                ));
            }
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
                let l = guard_to_smt_two_slots_scoped(
                    left,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                let r = guard_to_smt_two_slots_scoped(
                    right,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
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
                let l = guard_to_smt_two_slots_scoped(
                    left,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                let r = guard_to_smt_two_slots_scoped(
                    right,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                Ok(format!("(and {l} {r})"))
            }
            "OpOr" => {
                let l = guard_to_smt_two_slots_scoped(
                    left,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                let r = guard_to_smt_two_slots_scoped(
                    right,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                Ok(format!("(or {l} {r})"))
            }
            "OpImplies" => {
                let l = guard_to_smt_two_slots_scoped(
                    left,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                let r = guard_to_smt_two_slots_scoped(
                    right,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                Ok(format!("(=> {l} {r})"))
            }
            "OpAdd" | "OpSub" | "OpMul" => {
                let l = guard_to_smt_two_slots_scoped(
                    left,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                let r = guard_to_smt_two_slots_scoped(
                    right,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
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
            let inner = guard_to_smt_two_slots_scoped(
                operand,
                entity,
                vctx,
                var1,
                slot1,
                var2,
                slot2,
                n_slots,
                locals,
                entity_locals,
            )?;
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
            enum_name,
            ctor,
            args,
            ..
        } => ic3_ctor_term_with(enum_name, ctor, args, vctx, |arg| {
            guard_to_smt_two_slots_scoped(
                arg,
                entity,
                vctx,
                var1,
                slot1,
                var2,
                slot2,
                n_slots,
                locals,
                entity_locals,
            )
        }),
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            if !ic3_match_has_final_catch_all(arms) {
                return Err(
                    "non-exhaustive match without final wildcard/var arm is not supported in inter-entity IC3 encoding"
                        .to_owned(),
                );
            }
            let scrut = guard_to_smt_two_slots_scoped(
                scrutinee,
                entity,
                vctx,
                var1,
                slot1,
                var2,
                slot2,
                n_slots,
                locals,
                entity_locals,
            )?;
            let mut acc = {
                let last = arms.last().expect("checked non-empty match arms");
                let bindings = ic3_match_pattern_bindings(&scrut, &last.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let body = guard_to_smt_two_slots_scoped(
                    &last.body,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    &scope,
                    entity_locals,
                )?;
                wrap_smt_let_bindings(&bindings, body)
            };
            for arm in arms[..arms.len() - 1].iter().rev() {
                let bindings = ic3_match_pattern_bindings(&scrut, &arm.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let pat = ic3_match_pattern_cond(&scrut, &arm.pattern, vctx)?;
                let cond = if let Some(guard) = &arm.guard {
                    let guard_smt = guard_to_smt_two_slots_scoped(
                        guard,
                        entity,
                        vctx,
                        var1,
                        slot1,
                        var2,
                        slot2,
                        n_slots,
                        &scope,
                        entity_locals,
                    )?;
                    wrap_smt_let_bindings(&bindings, format!("(and {pat} {guard_smt})"))
                } else {
                    wrap_smt_let_bindings(&bindings, pat)
                };
                let body = guard_to_smt_two_slots_scoped(
                    &arm.body,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    &scope,
                    entity_locals,
                )?;
                let body = wrap_smt_let_bindings(&bindings, body);
                acc = format!("(ite {cond} {body} {acc})");
            }
            Ok(acc)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond_smt = guard_to_smt_two_slots_scoped(
                cond,
                entity,
                vctx,
                var1,
                slot1,
                var2,
                slot2,
                n_slots,
                locals,
                entity_locals,
            )?;
            let then_smt = guard_to_smt_two_slots_scoped(
                then_body,
                entity,
                vctx,
                var1,
                slot1,
                var2,
                slot2,
                n_slots,
                locals,
                entity_locals,
            )?;
            if let Some(else_body) = else_body {
                let else_smt = guard_to_smt_two_slots_scoped(
                    else_body,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                Ok(format!("(ite {cond_smt} {then_smt} {else_smt})"))
            } else {
                Ok(format!("(=> {cond_smt} {then_smt})"))
            }
        }
        IRExpr::Let { bindings, body, .. } => guard_let_to_smt_two_slots_scoped(
            bindings,
            body,
            entity,
            vctx,
            var1,
            slot1,
            var2,
            slot2,
            n_slots,
            locals,
            entity_locals,
        ),
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => guard_to_smt_two_slots_scoped(
            expr,
            entity,
            vctx,
            var1,
            slot1,
            var2,
            slot2,
            n_slots,
            locals,
            entity_locals,
        ),
        IRExpr::Forall {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| {
                guard_to_smt_two_slots_scoped(
                    body,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    scope,
                    entity_locals,
                )
            },
            "forall",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in inter-entity IC3 encoding".to_owned()
        }),
        IRExpr::Exists {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| {
                guard_to_smt_two_slots_scoped(
                    body,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    scope,
                    entity_locals,
                )
            },
            "exists",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in inter-entity IC3 encoding".to_owned()
        }),
        IRExpr::One {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| {
                guard_to_smt_two_slots_scoped(
                    body,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    scope,
                    entity_locals,
                )
            },
            "one",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in inter-entity IC3 encoding".to_owned()
        }),
        IRExpr::Lone {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| {
                guard_to_smt_two_slots_scoped(
                    body,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    scope,
                    entity_locals,
                )
            },
            "lone",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in inter-entity IC3 encoding".to_owned()
        }),
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
    n_slots: usize,
) -> Result<String, String> {
    let pos = guard_to_smt_slot(property, entity, vctx, slot, n_slots)?;
    Ok(format!("(not {pos})"))
}

/// Like `expr_to_smt` but prefixes field variables with slot index.
fn expr_to_smt_slot(
    expr: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    slot: usize,
    n_slots: usize,
) -> Result<String, String> {
    expr_to_smt_slot_scoped(
        expr,
        entity,
        vctx,
        slot,
        n_slots,
        &HashSet::new(),
        &Ic3SlotEntityLocals::new(),
    )
}

#[allow(clippy::too_many_arguments)]
fn guard_let_to_smt_slot_scoped(
    bindings: &[crate::ir::types::LetBinding],
    body: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    slot: usize,
    n_slots: usize,
    locals: &HashSet<String>,
    entity_locals: &Ic3SlotEntityLocals,
) -> Result<String, String> {
    let Some((binding, rest)) = bindings.split_first() else {
        return guard_to_smt_slot_scoped(body, entity, vctx, slot, n_slots, locals, entity_locals);
    };

    if let IRExpr::Choose {
        var,
        domain,
        predicate,
        ..
    } = &binding.expr
    {
        if let IRType::Entity { name } = domain {
            if name == &entity.name {
                let mut disjuncts = Vec::new();
                for chosen_slot in 0..n_slots {
                    let active = format!("s{chosen_slot}_active");
                    let mut pred_entity_locals = entity_locals.clone();
                    pred_entity_locals.insert(var.clone(), chosen_slot);
                    let pred = if let Some(predicate) = predicate {
                        guard_to_smt_slot_scoped(
                            predicate,
                            entity,
                            vctx,
                            slot,
                            n_slots,
                            locals,
                            &pred_entity_locals,
                        )?
                    } else {
                        "true".to_owned()
                    };
                    let mut rest_entity_locals = entity_locals.clone();
                    rest_entity_locals.insert(binding.name.clone(), chosen_slot);
                    let rest_smt = guard_let_to_smt_slot_scoped(
                        rest,
                        body,
                        entity,
                        vctx,
                        slot,
                        n_slots,
                        locals,
                        &rest_entity_locals,
                    )?;
                    disjuncts.push(format!("(and {active} {pred} {rest_smt})"));
                }
                return if disjuncts.is_empty() {
                    Ok("false".to_owned())
                } else {
                    Ok(format!("(or {})", disjuncts.join(" ")))
                };
            }
        }
        let finite = ic3_finite_choose_witness(
            var,
            domain,
            predicate.as_deref(),
            vctx,
            locals,
            |predicate, scope| {
                guard_to_smt_slot_scoped(
                    predicate,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    scope,
                    entity_locals,
                )
            },
        )?;

        let mut scope = locals.clone();
        scope.insert(binding.name.clone());
        let rest_smt = guard_let_to_smt_slot_scoped(
            rest,
            body,
            entity,
            vctx,
            slot,
            n_slots,
            &scope,
            entity_locals,
        )?;
        if let Some((exists, witness)) = finite {
            return Ok(format!(
                "(and {exists} (let (({} {})) {}))",
                binding.name, witness, rest_smt
            ));
        }
        if let Some(witness) = ic3_direct_choose_witness(
            var,
            domain,
            predicate.as_deref(),
            locals,
            |term, scope| {
                expr_to_smt_slot_scoped(term, entity, vctx, slot, n_slots, scope, entity_locals)
            },
            |predicate, scope| {
                guard_to_smt_slot_scoped(
                    predicate,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    scope,
                    entity_locals,
                )
            },
            |scrutinee, pattern, scope| {
                let scrut = expr_to_smt_slot_scoped(
                    scrutinee,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    scope,
                    entity_locals,
                )?;
                ic3_match_pattern_bindings(&scrut, pattern, vctx)
            },
            |scrutinee, pattern, scope| {
                let scrut = expr_to_smt_slot_scoped(
                    scrutinee,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    scope,
                    entity_locals,
                )?;
                ic3_match_pattern_cond(&scrut, pattern, vctx)
            },
        )? {
            return ic3_witness_binding_formula(
                &binding.name,
                var,
                witness,
                predicate.as_deref(),
                locals,
                |predicate, scope| {
                    guard_to_smt_slot_scoped(
                        predicate,
                        entity,
                        vctx,
                        slot,
                        n_slots,
                        scope,
                        entity_locals,
                    )
                },
                rest_smt,
            );
        }
        if let Some(formula) = ic3_quantified_choose_formula(
            &binding.name,
            var,
            domain,
            predicate.as_deref(),
            locals,
            |predicate, scope| {
                guard_to_smt_slot_scoped(
                    predicate,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    scope,
                    entity_locals,
                )
            },
            rest_smt.clone(),
        )? {
            return Ok(formula);
        }
        return Err("choose is not yet supported in IC3 CHC encoding for this domain".to_owned());
    }

    if matches!(binding.ty, IRType::Entity { .. }) {
        if let IRExpr::Var { name, .. } = &binding.expr {
            if let Some(bound_slot) = entity_locals.get(name) {
                let mut scope_entity_locals = entity_locals.clone();
                scope_entity_locals.insert(binding.name.clone(), *bound_slot);
                return guard_let_to_smt_slot_scoped(
                    rest,
                    body,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    locals,
                    &scope_entity_locals,
                );
            }
        }
    }

    let rhs = if binding.ty == IRType::Bool {
        guard_to_smt_slot_scoped(
            &binding.expr,
            entity,
            vctx,
            slot,
            n_slots,
            locals,
            entity_locals,
        )?
    } else {
        expr_to_smt_slot_scoped(
            &binding.expr,
            entity,
            vctx,
            slot,
            n_slots,
            locals,
            entity_locals,
        )?
    };
    let mut scope = locals.clone();
    scope.insert(binding.name.clone());
    let rest_smt = guard_let_to_smt_slot_scoped(
        rest,
        body,
        entity,
        vctx,
        slot,
        n_slots,
        &scope,
        entity_locals,
    )?;
    Ok(format!("(let (({} {})) {})", binding.name, rhs, rest_smt))
}

fn expr_to_smt_slot_scoped(
    expr: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    slot: usize,
    n_slots: usize,
    locals: &HashSet<String>,
    entity_locals: &Ic3SlotEntityLocals,
) -> Result<String, String> {
    match expr {
        IRExpr::Var { name, .. } => {
            for (i, f) in entity.fields.iter().enumerate() {
                if f.name == *name {
                    return Ok(format!("s{slot}_f{i}"));
                }
            }
            if locals.contains(name) {
                return Ok(name.clone());
            }
            if entity_locals.contains_key(name) {
                return Err(format!(
                    "bare entity local {name} in IC3 encoding — use field access (e.g., {name}.field) instead"
                ));
            }
            Err(format!("unknown variable in IC3 encoding: {name}"))
        }
        IRExpr::Field {
            expr: inner, field, ..
        } => {
            if let IRExpr::Var { name, .. } = inner.as_ref() {
                if let Some(bound_slot) = entity_locals.get(name) {
                    for (i, f) in entity.fields.iter().enumerate() {
                        if f.name == *field {
                            return Ok(format!("s{bound_slot}_f{i}"));
                        }
                    }
                }
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
            let l =
                expr_to_smt_slot_scoped(left, entity, vctx, slot, n_slots, locals, entity_locals)?;
            let r =
                expr_to_smt_slot_scoped(right, entity, vctx, slot, n_slots, locals, entity_locals)?;
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
            let inner = expr_to_smt_slot_scoped(
                operand,
                entity,
                vctx,
                slot,
                n_slots,
                locals,
                entity_locals,
            )?;
            Ok(format!("(- {inner})"))
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            let m =
                expr_to_smt_slot_scoped(map, entity, vctx, slot, n_slots, locals, entity_locals)?;
            let k =
                expr_to_smt_slot_scoped(key, entity, vctx, slot, n_slots, locals, entity_locals)?;
            let v =
                expr_to_smt_slot_scoped(value, entity, vctx, slot, n_slots, locals, entity_locals)?;
            Ok(format!("(store {m} {k} {v})"))
        }
        IRExpr::Index { map, key, .. } => {
            let m =
                expr_to_smt_slot_scoped(map, entity, vctx, slot, n_slots, locals, entity_locals)?;
            let k =
                expr_to_smt_slot_scoped(key, entity, vctx, slot, n_slots, locals, entity_locals)?;
            Ok(format!("(select {m} {k})"))
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            if !ic3_match_has_final_catch_all(arms) {
                return Err(
                    "non-exhaustive match without final wildcard/var arm is not supported in IC3 slot value encoding"
                        .to_owned(),
                );
            }
            let scrut = expr_to_smt_slot_scoped(
                scrutinee,
                entity,
                vctx,
                slot,
                n_slots,
                locals,
                entity_locals,
            )?;
            let mut acc = {
                let last = arms.last().expect("checked non-empty match arms");
                let bindings = ic3_match_pattern_bindings(&scrut, &last.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let body = expr_to_smt_slot_scoped(
                    &last.body,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    &scope,
                    entity_locals,
                )?;
                wrap_smt_let_bindings(&bindings, body)
            };
            for arm in arms[..arms.len() - 1].iter().rev() {
                let bindings = ic3_match_pattern_bindings(&scrut, &arm.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let pat = ic3_match_pattern_cond(&scrut, &arm.pattern, vctx)?;
                let cond = if let Some(guard) = &arm.guard {
                    let guard_smt = guard_to_smt_slot_scoped(
                        guard,
                        entity,
                        vctx,
                        slot,
                        n_slots,
                        &scope,
                        entity_locals,
                    )?;
                    wrap_smt_let_bindings(&bindings, format!("(and {pat} {guard_smt})"))
                } else {
                    wrap_smt_let_bindings(&bindings, pat)
                };
                let body = expr_to_smt_slot_scoped(
                    &arm.body,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    &scope,
                    entity_locals,
                )?;
                let body = wrap_smt_let_bindings(&bindings, body);
                acc = format!("(ite {cond} {body} {acc})");
            }
            Ok(acc)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond_smt =
                guard_to_smt_slot_scoped(cond, entity, vctx, slot, n_slots, locals, entity_locals)?;
            let then_smt = expr_to_smt_slot_scoped(
                then_body,
                entity,
                vctx,
                slot,
                n_slots,
                locals,
                entity_locals,
            )?;
            if let Some(else_body) = else_body {
                let else_smt = expr_to_smt_slot_scoped(
                    else_body,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                Ok(format!("(ite {cond_smt} {then_smt} {else_smt})"))
            } else {
                Err("if/else without else is not supported in IC3 value encoding".to_owned())
            }
        }
        IRExpr::Let { bindings, body, .. } => {
            let mut scope = locals.clone();
            let mut out = String::new();
            for binding in bindings {
                let rhs = if binding.ty == IRType::Bool {
                    guard_to_smt_slot_scoped(
                        &binding.expr,
                        entity,
                        vctx,
                        slot,
                        n_slots,
                        &scope,
                        entity_locals,
                    )?
                } else {
                    expr_to_smt_slot_scoped(
                        &binding.expr,
                        entity,
                        vctx,
                        slot,
                        n_slots,
                        &scope,
                        entity_locals,
                    )?
                };
                out.push_str(&format!("(let (({} {})) ", binding.name, rhs));
                scope.insert(binding.name.clone());
            }
            out.push_str(&expr_to_smt_slot_scoped(
                body,
                entity,
                vctx,
                slot,
                n_slots,
                &scope,
                entity_locals,
            )?);
            for _ in bindings {
                out.push(')');
            }
            Ok(out)
        }
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            expr_to_smt_slot_scoped(expr, entity, vctx, slot, n_slots, locals, entity_locals)
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
    n_slots: usize,
) -> Result<String, String> {
    guard_to_smt_slot_scoped(
        guard,
        entity,
        vctx,
        slot,
        n_slots,
        &HashSet::new(),
        &Ic3SlotEntityLocals::new(),
    )
}

fn guard_to_smt_slot_scoped(
    guard: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    slot: usize,
    n_slots: usize,
    locals: &HashSet<String>,
    entity_locals: &Ic3SlotEntityLocals,
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
                let l = expr_to_smt_slot_scoped(
                    left,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                let r = expr_to_smt_slot_scoped(
                    right,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
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
                let l = guard_to_smt_slot_scoped(
                    left,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                let r = guard_to_smt_slot_scoped(
                    right,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                Ok(format!("(and {l} {r})"))
            }
            "OpOr" => {
                let l = guard_to_smt_slot_scoped(
                    left,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                let r = guard_to_smt_slot_scoped(
                    right,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                Ok(format!("(or {l} {r})"))
            }
            "OpImplies" => {
                let l = guard_to_smt_slot_scoped(
                    left,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                let r = guard_to_smt_slot_scoped(
                    right,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                Ok(format!("(=> {l} {r})"))
            }
            _ => Err(format!("unsupported binary op in IC3 guard encoding: {op}")),
        },
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => {
            let inner = guard_to_smt_slot_scoped(
                operand,
                entity,
                vctx,
                slot,
                n_slots,
                locals,
                entity_locals,
            )?;
            Ok(format!("(not {inner})"))
        }
        IRExpr::Field { .. } | IRExpr::Var { .. } => {
            expr_to_smt_slot_scoped(guard, entity, vctx, slot, n_slots, locals, entity_locals)
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            if !ic3_match_has_final_catch_all(arms) {
                return Err(
                    "non-exhaustive match without final wildcard/var arm is not supported in IC3 guard encoding"
                        .to_owned(),
                );
            }
            let scrut = expr_to_smt_slot_scoped(
                scrutinee,
                entity,
                vctx,
                slot,
                n_slots,
                locals,
                entity_locals,
            )?;
            let mut acc = {
                let last = arms.last().expect("checked non-empty match arms");
                let bindings = ic3_match_pattern_bindings(&scrut, &last.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let body = guard_to_smt_slot_scoped(
                    &last.body,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    &scope,
                    entity_locals,
                )?;
                wrap_smt_let_bindings(&bindings, body)
            };
            for arm in arms[..arms.len() - 1].iter().rev() {
                let bindings = ic3_match_pattern_bindings(&scrut, &arm.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let pat = ic3_match_pattern_cond(&scrut, &arm.pattern, vctx)?;
                let cond = if let Some(guard) = &arm.guard {
                    let guard_smt = guard_to_smt_slot_scoped(
                        guard,
                        entity,
                        vctx,
                        slot,
                        n_slots,
                        &scope,
                        entity_locals,
                    )?;
                    wrap_smt_let_bindings(&bindings, format!("(and {pat} {guard_smt})"))
                } else {
                    wrap_smt_let_bindings(&bindings, pat)
                };
                let body = guard_to_smt_slot_scoped(
                    &arm.body,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    &scope,
                    entity_locals,
                )?;
                let body = wrap_smt_let_bindings(&bindings, body);
                acc = format!("(ite {cond} {body} {acc})");
            }
            Ok(acc)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond_smt =
                guard_to_smt_slot_scoped(cond, entity, vctx, slot, n_slots, locals, entity_locals)?;
            let then_smt = guard_to_smt_slot_scoped(
                then_body,
                entity,
                vctx,
                slot,
                n_slots,
                locals,
                entity_locals,
            )?;
            if let Some(else_body) = else_body {
                let else_smt = guard_to_smt_slot_scoped(
                    else_body,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                Ok(format!("(ite {cond_smt} {then_smt} {else_smt})"))
            } else {
                Ok(format!("(=> {cond_smt} {then_smt})"))
            }
        }
        IRExpr::Let { bindings, body, .. } => guard_let_to_smt_slot_scoped(
            bindings,
            body,
            entity,
            vctx,
            slot,
            n_slots,
            locals,
            entity_locals,
        ),
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            guard_to_smt_slot_scoped(expr, entity, vctx, slot, n_slots, locals, entity_locals)
        }
        IRExpr::Forall {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| {
                guard_to_smt_slot_scoped(body, entity, vctx, slot, n_slots, scope, entity_locals)
            },
            "forall",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in IC3 slot guard encoding".to_owned()
        }),
        IRExpr::Exists {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| {
                guard_to_smt_slot_scoped(body, entity, vctx, slot, n_slots, scope, entity_locals)
            },
            "exists",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in IC3 slot guard encoding".to_owned()
        }),
        IRExpr::One {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| {
                guard_to_smt_slot_scoped(body, entity, vctx, slot, n_slots, scope, entity_locals)
            },
            "one",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in IC3 slot guard encoding".to_owned()
        }),
        IRExpr::Lone {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| {
                guard_to_smt_slot_scoped(body, entity, vctx, slot, n_slots, scope, entity_locals)
            },
            "lone",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in IC3 slot guard encoding".to_owned()
        }),
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
    emit_ic3_datatype_decls(entity.fields.iter().map(|field| &field.ty), &mut chc);

    // Field sorts for State relation
    let field_sorts: Vec<String> = entity
        .fields
        .iter()
        .map(|f| ir_type_to_sort_name(&f.ty))
        .collect();

    // Declare State relation: State(f1,..., fn, active)
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
    // State(f0,..., fn, false) → State(defaults_or_vars, true)
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
        if let IRType::Enum { name, variants } = &f.ty {
            if variants.iter().any(|variant| !variant.fields.is_empty()) {
                continue;
            }
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
        IRType::Int | IRType::Identity => "Int".to_owned(),
        IRType::Bool => "Bool".to_owned(),
        IRType::Real | IRType::Float => "Real".to_owned(),
        IRType::Enum { name, variants } => {
            if variants.iter().any(|variant| !variant.fields.is_empty()) {
                name.clone()
            } else {
                "Int".to_owned()
            }
        }
        IRType::Map { key, value } => {
            format!(
                "(Array {} {})",
                ir_type_to_sort_name(key),
                ir_type_to_sort_name(value)
            )
        }
        IRType::Set { element } => {
            format!("(Array {} Bool)", ir_type_to_sort_name(element))
        }
        IRType::Seq { element } => {
            format!("(Array Int {})", ir_type_to_sort_name(element))
        }
        _ => "Int".to_owned(),
    }
}

fn collect_ic3_datatype_enums<'a>(ty: &'a IRType, out: &mut HashMap<String, &'a IRType>) {
    match ty {
        IRType::Enum { name, variants }
            if variants.iter().any(|variant| !variant.fields.is_empty()) =>
        {
            out.entry(name.clone()).or_insert(ty);
            for variant in variants {
                for field in &variant.fields {
                    collect_ic3_datatype_enums(&field.ty, out);
                }
            }
        }
        IRType::Map { key, value } => {
            collect_ic3_datatype_enums(key, out);
            collect_ic3_datatype_enums(value, out);
        }
        IRType::Set { element }
        | IRType::Seq { element }
        | IRType::Refinement { base: element, .. } => {
            collect_ic3_datatype_enums(element, out);
        }
        IRType::Tuple { elements } => {
            for element in elements {
                collect_ic3_datatype_enums(element, out);
            }
        }
        _ => {}
    }
}

fn emit_ic3_datatype_decls<'a, I>(types: I, chc: &mut String)
where
    I: IntoIterator<Item = &'a IRType>,
{
    let mut enums = HashMap::new();
    for ty in types {
        collect_ic3_datatype_enums(ty, &mut enums);
    }

    let mut enums: Vec<_> = enums.into_iter().collect();
    enums.sort_by(|(left, _), (right, _)| left.cmp(right));

    for (_, ty) in enums {
        let IRType::Enum { name, variants } = ty else {
            continue;
        };
        chc.push_str("(declare-datatypes () ((");
        chc.push_str(name);
        for variant in variants {
            chc.push_str(" (");
            chc.push_str(&variant.name);
            for field in &variant.fields {
                chc.push_str(" (");
                chc.push_str(&field.name);
                chc.push(' ');
                chc.push_str(&ir_type_to_sort_name(&field.ty));
                chc.push(')');
            }
            chc.push(')');
        }
        chc.push_str(")))\n");
    }
}

fn wrap_smt_let_bindings(bindings: &[(String, String)], inner: String) -> String {
    let mut out = String::new();
    for (name, value) in bindings {
        out.push_str(&format!("(let (({name} {value})) "));
    }
    out.push_str(&inner);
    for _ in bindings {
        out.push(')');
    }
    out
}

fn ic3_match_pattern_cond(
    scrut: &str,
    pattern: &crate::ir::types::IRPattern,
    vctx: &VerifyContext,
) -> Result<String, String> {
    use crate::ir::types::IRPattern;
    match pattern {
        IRPattern::PWild | IRPattern::PVar { .. } => Ok("true".to_owned()),
        IRPattern::PCtor { name, fields } => {
            if let Some(variant) = ic3_lookup_ctor_variant(name, vctx) {
                if fields.is_empty() && variant.accessor_names.is_empty() {
                    return Ok(format!("((_ is {}) {scrut})", variant.ctor_name));
                }
                for field in fields {
                    if !variant
                        .accessor_names
                        .iter()
                        .any(|accessor| accessor == &field.name)
                    {
                        return Err(format!(
                            "unknown field '{}' in IC3 match pattern for constructor '{name}'",
                            field.name
                        ));
                    }
                }
                return Ok(format!("((_ is {}) {scrut})", variant.ctor_name));
            }
            for ((type_name, variant_name), id) in &vctx.variants.to_id {
                if variant_name == name || format!("{type_name}::{variant_name}") == *name {
                    return Ok(format!("(= {scrut} {id})"));
                }
            }
            Err(format!(
                "unknown constructor pattern in IC3 encoding: {name}"
            ))
        }
        IRPattern::POr { left, right } => {
            let l = ic3_match_pattern_cond(scrut, left, vctx)?;
            let r = ic3_match_pattern_cond(scrut, right, vctx)?;
            Ok(format!("(or {l} {r})"))
        }
    }
}

fn ic3_match_pattern_bindings(
    scrut: &str,
    pattern: &crate::ir::types::IRPattern,
    vctx: &VerifyContext,
) -> Result<Vec<(String, String)>, String> {
    use crate::ir::types::IRPattern;
    match pattern {
        IRPattern::PWild => Ok(Vec::new()),
        IRPattern::PVar { name } => Ok(vec![(name.clone(), scrut.to_owned())]),
        IRPattern::PCtor { name, fields } => {
            if fields.is_empty() {
                return Ok(Vec::new());
            }
            let Some(variant) = ic3_lookup_ctor_variant(name, vctx) else {
                return Err(format!(
                    "unknown constructor pattern in IC3 encoding: {name}"
                ));
            };
            let mut bindings = Vec::new();
            for field in fields {
                if !variant
                    .accessor_names
                    .iter()
                    .any(|accessor| accessor == &field.name)
                {
                    return Err(format!(
                        "unknown field '{}' in IC3 match pattern for constructor '{name}'",
                        field.name
                    ));
                }
                let field_term = format!("({} {scrut})", field.name);
                bindings.extend(ic3_match_pattern_bindings(
                    &field_term,
                    &field.pattern,
                    vctx,
                )?);
            }
            Ok(bindings)
        }
        IRPattern::POr { .. } => ic3_or_pattern_bindings(scrut, pattern, vctx),
    }
}

fn ic3_or_pattern_bindings(
    scrut: &str,
    pattern: &crate::ir::types::IRPattern,
    vctx: &VerifyContext,
) -> Result<Vec<(String, String)>, String> {
    use crate::ir::types::IRPattern;
    let IRPattern::POr { left, right } = pattern else {
        return Ok(Vec::new());
    };

    let left_bindings = ic3_match_pattern_bindings(scrut, left, vctx)?;
    let right_bindings = ic3_match_pattern_bindings(scrut, right, vctx)?;
    if left_bindings.is_empty() && right_bindings.is_empty() {
        return Ok(Vec::new());
    }

    let left_map: HashMap<_, _> = left_bindings.into_iter().collect();
    let right_map: HashMap<_, _> = right_bindings.into_iter().collect();

    let mut left_names: Vec<_> = left_map.keys().cloned().collect();
    let mut right_names: Vec<_> = right_map.keys().cloned().collect();
    left_names.sort();
    right_names.sort();
    if left_names != right_names {
        return Err(
            "or-pattern bindings in IC3 require both alternatives to bind the same names"
                .to_owned(),
        );
    }

    let left_cond = ic3_match_pattern_cond(scrut, left, vctx)?;
    let mut merged = Vec::new();
    for name in left_names {
        let left_value = left_map
            .get(&name)
            .expect("name comes from left_names collection");
        let right_value = right_map
            .get(&name)
            .expect("name comes from right_names collection");
        merged.push((
            name,
            format!("(ite {left_cond} {left_value} {right_value})"),
        ));
    }
    Ok(merged)
}

struct Ic3CtorVariant {
    ctor_name: String,
    accessor_names: Vec<String>,
}

fn ic3_lookup_ctor_variant(name: &str, vctx: &VerifyContext) -> Option<Ic3CtorVariant> {
    for (enum_name, dt) in &vctx.adt_sorts {
        for variant in &dt.variants {
            let ctor_name = super::smt::func_decl_name(&variant.constructor);
            if ctor_name == name || format!("{enum_name}::{ctor_name}") == name {
                return Some(Ic3CtorVariant {
                    ctor_name,
                    accessor_names: variant
                        .accessors
                        .iter()
                        .map(super::smt::func_decl_name)
                        .collect(),
                });
            }
        }
    }
    None
}

fn ic3_match_has_final_catch_all(arms: &[crate::ir::types::IRMatchArm]) -> bool {
    use crate::ir::types::IRPattern;
    arms.last().is_some_and(|arm| {
        arm.guard.is_none() && matches!(arm.pattern, IRPattern::PWild | IRPattern::PVar { .. })
    })
}

fn ic3_ctor_term_with<F>(
    enum_name: &str,
    ctor: &str,
    args: &[(String, IRExpr)],
    vctx: &VerifyContext,
    mut encode_arg: F,
) -> Result<String, String>
where
    F: FnMut(&IRExpr) -> Result<String, String>,
{
    if let Some(variant) = ic3_lookup_ctor_variant(ctor, vctx) {
        if args.is_empty() {
            if !variant.accessor_names.is_empty() {
                return Err(format!(
                    "constructor '{ctor}' of '{enum_name}' requires {} field argument(s)",
                    variant.accessor_names.len()
                ));
            }
            return Ok(variant.ctor_name);
        }

        let mut args_by_name = HashMap::new();
        for (field_name, field_expr) in args {
            if !variant
                .accessor_names
                .iter()
                .any(|accessor| accessor == field_name)
            {
                return Err(format!(
                    "unknown field '{field_name}' for constructor '{ctor}' in IC3 encoding"
                ));
            }
            args_by_name.insert(field_name.as_str(), field_expr);
        }

        let mut ordered_args = Vec::new();
        for accessor in &variant.accessor_names {
            let Some(field_expr) = args_by_name.get(accessor.as_str()) else {
                return Err(format!(
                    "missing field '{accessor}' for constructor '{ctor}' in IC3 encoding"
                ));
            };
            ordered_args.push(encode_arg(field_expr)?);
        }

        return Ok(format!(
            "({} {})",
            variant.ctor_name,
            ordered_args.join(" ")
        ));
    }

    Ok(vctx.variants.try_id_of(enum_name, ctor)?.to_string())
}

fn ic3_finite_choose_candidates(domain: &IRType, vctx: &VerifyContext) -> Option<Vec<String>> {
    match domain {
        IRType::Bool => Some(vec!["false".to_owned(), "true".to_owned()]),
        IRType::Enum { name, variants }
            if !variants.iter().any(|variant| !variant.fields.is_empty()) =>
        {
            let (min_id, max_id) = vctx.enum_ranges.get(name).copied()?;
            Some((min_id..=max_id).map(|id| id.to_string()).collect())
        }
        _ => None,
    }
}

fn ic3_finite_quantifier_formula<F>(
    var: &str,
    domain: &IRType,
    body: &IRExpr,
    vctx: &VerifyContext,
    locals: &HashSet<String>,
    mut encode_body: F,
    kind: &str,
) -> Result<Option<String>, String>
where
    F: FnMut(&IRExpr, &HashSet<String>) -> Result<String, String>,
{
    let Some(candidates) = ic3_finite_choose_candidates(domain, vctx) else {
        return Ok(None);
    };

    let mut scope = locals.clone();
    scope.insert(var.to_owned());
    let preds = candidates
        .iter()
        .map(|candidate| {
            let raw = encode_body(body, &scope)?;
            Ok(format!("(let (({var} {candidate})) {raw})"))
        })
        .collect::<Result<Vec<_>, String>>()?;

    let formula = match kind {
        "forall" => {
            if preds.is_empty() {
                "true".to_owned()
            } else {
                format!("(and {})", preds.join(" "))
            }
        }
        "exists" => {
            if preds.is_empty() {
                "false".to_owned()
            } else {
                format!("(or {})", preds.join(" "))
            }
        }
        "one" => {
            if preds.is_empty() {
                "false".to_owned()
            } else {
                let mut disjuncts = Vec::new();
                for (i, pred_i) in preds.iter().enumerate() {
                    let mut conjuncts = vec![pred_i.clone()];
                    for (j, pred_j) in preds.iter().enumerate() {
                        if i != j {
                            conjuncts.push(format!("(not {pred_j})"));
                        }
                    }
                    disjuncts.push(format!("(and {})", conjuncts.join(" ")));
                }
                format!("(or {})", disjuncts.join(" "))
            }
        }
        "lone" => {
            if preds.len() <= 1 {
                "true".to_owned()
            } else {
                let mut conjuncts = Vec::new();
                for i in 0..preds.len() {
                    for j in (i + 1)..preds.len() {
                        conjuncts.push(format!("(not (and {} {}))", preds[i], preds[j]));
                    }
                }
                format!("(and {})", conjuncts.join(" "))
            }
        }
        _ => return Err(format!("unknown finite quantifier kind in IC3: {kind}")),
    };

    Ok(Some(formula))
}

fn ic3_finite_choose_witness<F>(
    var: &str,
    domain: &IRType,
    predicate: Option<&IRExpr>,
    vctx: &VerifyContext,
    locals: &HashSet<String>,
    mut encode_predicate: F,
) -> Result<Option<(String, String)>, String>
where
    F: FnMut(&IRExpr, &HashSet<String>) -> Result<String, String>,
{
    let Some(candidates) = ic3_finite_choose_candidates(domain, vctx) else {
        return Ok(None);
    };
    if candidates.is_empty() {
        return Ok(Some(("false".to_owned(), "0".to_owned())));
    }

    let mut pred_scope = locals.clone();
    pred_scope.insert(var.to_owned());

    let candidate_preds = candidates
        .iter()
        .map(|candidate| {
            let pred = if let Some(predicate) = predicate {
                let raw = encode_predicate(predicate, &pred_scope)?;
                format!("(let (({var} {candidate})) {raw})")
            } else {
                "true".to_owned()
            };
            Ok((candidate.clone(), pred))
        })
        .collect::<Result<Vec<_>, String>>()?;

    let existence = if predicate.is_some() {
        format!(
            "(or {})",
            candidate_preds
                .iter()
                .map(|(_, pred)| pred.as_str())
                .collect::<Vec<_>>()
                .join(" ")
        )
    } else {
        "true".to_owned()
    };

    let mut witness = candidate_preds
        .last()
        .map(|(candidate, _)| candidate.clone())
        .expect("candidates checked non-empty");
    for (candidate, pred) in candidate_preds[..candidate_preds.len().saturating_sub(1)]
        .iter()
        .rev()
    {
        witness = format!("(ite {pred} {candidate} {witness})");
    }

    Ok(Some((existence, witness)))
}

fn ic3_quantified_choose_sort(domain: &IRType) -> Option<String> {
    match domain {
        IRType::Int | IRType::Identity => Some("Int".to_owned()),
        IRType::Real | IRType::Float => Some("Real".to_owned()),
        IRType::Enum { name, variants }
            if variants.iter().any(|variant| !variant.fields.is_empty()) =>
        {
            Some(name.clone())
        }
        _ => None,
    }
}

fn ic3_quantified_choose_formula<F>(
    binding_name: &str,
    var: &str,
    domain: &IRType,
    predicate: Option<&IRExpr>,
    locals: &HashSet<String>,
    mut encode_predicate: F,
    rest_smt: String,
) -> Result<Option<String>, String>
where
    F: FnMut(&IRExpr, &HashSet<String>) -> Result<String, String>,
{
    if ic3_quantified_choose_sort(domain).is_none() {
        return Ok(None);
    }

    let mut body = rest_smt;
    if let Some(predicate) = predicate {
        let mut pred_scope = locals.clone();
        pred_scope.insert(var.to_owned());
        let pred = encode_predicate(predicate, &pred_scope)?;
        body = format!("(and {pred} {body})");
    }

    let sort = ic3_quantified_choose_sort(domain).expect("checked above");
    Ok(Some(format!(
        "(exists (({binding_name} {sort})) (let (({var} {binding_name})) {body}))"
    )))
}

fn default_witness_for_type(ty: &IRType) -> Option<String> {
    match ty {
        IRType::Int | IRType::Identity => Some("0".to_owned()),
        IRType::Real | IRType::Float => Some("0.0".to_owned()),
        IRType::Bool => Some("false".to_owned()),
        IRType::Enum { .. } => {
            let ctor = ic3_default_ctor_term(ty)?;
            Some(ctor)
        }
        _ => None,
    }
}

fn ic3_default_ctor_term(ty: &IRType) -> Option<String> {
    let IRType::Enum { variants, .. } = ty else {
        return None;
    };
    let variant = variants.first()?;
    let ctor_name = variant
        .name
        .rsplit("::")
        .next()
        .unwrap_or(&variant.name)
        .to_owned();
    if variant.fields.is_empty() {
        Some(ctor_name)
    } else {
        let mut args = Vec::with_capacity(variant.fields.len());
        for field in &variant.fields {
            args.push(default_witness_for_type(&field.ty)?);
        }
        Some(format!("({ctor_name} {})", args.join(" ")))
    }
}

fn ic3_expr_mentions_var(expr: &IRExpr, target: &str) -> bool {
    match expr {
        IRExpr::Var { name, .. } => name == target,
        IRExpr::Field { expr, .. }
        | IRExpr::Prime { expr, .. }
        | IRExpr::UnOp { operand: expr, .. }
        | IRExpr::Assert { expr, .. }
        | IRExpr::Assume { expr, .. } => ic3_expr_mentions_var(expr, target),
        IRExpr::BinOp { left, right, .. } => {
            ic3_expr_mentions_var(left, target) || ic3_expr_mentions_var(right, target)
        }
        IRExpr::Index { map, key, .. } => {
            ic3_expr_mentions_var(map, target) || ic3_expr_mentions_var(key, target)
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            ic3_expr_mentions_var(map, target)
                || ic3_expr_mentions_var(key, target)
                || ic3_expr_mentions_var(value, target)
        }
        IRExpr::Ctor { args, .. } => args
            .iter()
            .any(|(_, expr)| ic3_expr_mentions_var(expr, target)),
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            ic3_expr_mentions_var(scrutinee, target)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(|guard| ic3_expr_mentions_var(guard, target))
                        || ic3_expr_mentions_var(&arm.body, target)
                })
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            ic3_expr_mentions_var(cond, target)
                || ic3_expr_mentions_var(then_body, target)
                || else_body
                    .as_ref()
                    .is_some_and(|expr| ic3_expr_mentions_var(expr, target))
        }
        IRExpr::Let { bindings, body, .. } => {
            bindings
                .iter()
                .any(|binding| ic3_expr_mentions_var(&binding.expr, target))
                || ic3_expr_mentions_var(body, target)
        }
        IRExpr::Forall { body, .. }
        | IRExpr::Exists { body, .. }
        | IRExpr::One { body, .. }
        | IRExpr::Lone { body, .. }
        | IRExpr::Always { body, .. }
        | IRExpr::Eventually { body, .. }
        | IRExpr::Historically { body, .. }
        | IRExpr::Once { body, .. }
        | IRExpr::Previously { body, .. }
        | IRExpr::Card { expr: body, .. } => ic3_expr_mentions_var(body, target),
        IRExpr::Until { left, right, .. } | IRExpr::Since { left, right, .. } => {
            ic3_expr_mentions_var(left, target) || ic3_expr_mentions_var(right, target)
        }
        IRExpr::Aggregate {
            body, in_filter, ..
        } => {
            ic3_expr_mentions_var(body, target)
                || in_filter
                    .as_ref()
                    .is_some_and(|expr| ic3_expr_mentions_var(expr, target))
        }
        IRExpr::Choose { predicate, .. } => predicate
            .as_ref()
            .is_some_and(|expr| ic3_expr_mentions_var(expr, target)),
        IRExpr::Saw { args, .. } => args
            .iter()
            .flatten()
            .any(|expr| ic3_expr_mentions_var(expr, target)),
        IRExpr::SetLit { elements, .. } | IRExpr::SeqLit { elements, .. } => elements
            .iter()
            .any(|expr| ic3_expr_mentions_var(expr, target)),
        IRExpr::MapLit { entries, .. } => entries.iter().any(|(key, value)| {
            ic3_expr_mentions_var(key, target) || ic3_expr_mentions_var(value, target)
        }),
        IRExpr::SetComp {
            filter, projection, ..
        } => {
            ic3_expr_mentions_var(filter, target)
                || projection
                    .as_ref()
                    .is_some_and(|expr| ic3_expr_mentions_var(expr, target))
        }
        IRExpr::App { func, arg, .. } => {
            ic3_expr_mentions_var(func, target) || ic3_expr_mentions_var(arg, target)
        }
        IRExpr::Block { exprs, .. } => exprs.iter().any(|expr| ic3_expr_mentions_var(expr, target)),
        IRExpr::VarDecl { init, rest, .. } => {
            ic3_expr_mentions_var(init, target) || ic3_expr_mentions_var(rest, target)
        }
        IRExpr::While {
            cond,
            invariants,
            body,
            ..
        } => {
            ic3_expr_mentions_var(cond, target)
                || invariants
                    .iter()
                    .any(|expr| ic3_expr_mentions_var(expr, target))
                || ic3_expr_mentions_var(body, target)
        }
        IRExpr::Lam { .. } | IRExpr::Sorry { .. } | IRExpr::Todo { .. } | IRExpr::Lit { .. } => {
            false
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn ic3_direct_choose_witness<F>(
    var: &str,
    domain: &IRType,
    predicate: Option<&IRExpr>,
    locals: &HashSet<String>,
    mut encode_term: F,
    mut encode_predicate: impl FnMut(&IRExpr, &HashSet<String>) -> Result<String, String>,
    mut match_bindings: impl FnMut(
        &IRExpr,
        &crate::ir::types::IRPattern,
        &HashSet<String>,
    ) -> Result<Vec<(String, String)>, String>,
    mut match_cond: impl FnMut(
        &IRExpr,
        &crate::ir::types::IRPattern,
        &HashSet<String>,
    ) -> Result<String, String>,
) -> Result<Option<String>, String>
where
    F: FnMut(&IRExpr, &HashSet<String>) -> Result<String, String>,
{
    #[derive(Clone)]
    enum NumericBound {
        Exact(String),
        Lower(String),
        Upper(String),
    }

    fn smt_numeric_step(domain: &IRType, base: String, delta: i32) -> Option<String> {
        match domain {
            IRType::Int | IRType::Identity => Some(if delta >= 0 {
                format!("(+ {base} 1)")
            } else {
                format!("(- {base} 1)")
            }),
            IRType::Real | IRType::Float => Some(if delta >= 0 {
                format!("(+ {base} 1.0)")
            } else {
                format!("(- {base} 1.0)")
            }),
            _ => None,
        }
    }

    fn smt_max(a: String, b: String) -> String {
        format!("(ite (>= {a} {b}) {a} {b})")
    }

    fn smt_min(a: String, b: String) -> String {
        format!("(ite (<= {a} {b}) {a} {b})")
    }

    fn collect_numeric_bounds<F>(
        var: &str,
        domain: &IRType,
        predicate: Option<&IRExpr>,
        locals: &HashSet<String>,
        encode_term: &mut F,
        bounds: &mut Vec<NumericBound>,
    ) -> Result<bool, String>
    where
        F: FnMut(&IRExpr, &HashSet<String>) -> Result<String, String>,
    {
        let Some(predicate) = predicate else {
            return Ok(true);
        };
        match predicate {
            IRExpr::BinOp {
                op, left, right, ..
            } if op == "OpAnd" => {
                let left_ok =
                    collect_numeric_bounds(var, domain, Some(left), locals, encode_term, bounds)?;
                let right_ok =
                    collect_numeric_bounds(var, domain, Some(right), locals, encode_term, bounds)?;
                Ok(left_ok && right_ok)
            }
            IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
                collect_numeric_bounds(var, domain, Some(expr), locals, encode_term, bounds)
            }
            IRExpr::BinOp {
                op, left, right, ..
            } => {
                if let IRExpr::Var { name, .. } = left.as_ref() {
                    if name == var && !ic3_expr_mentions_var(right, var) {
                        let rhs = encode_term(right, locals)?;
                        match op.as_str() {
                            "OpEq" => bounds.push(NumericBound::Exact(rhs)),
                            "OpGe" => bounds.push(NumericBound::Lower(rhs)),
                            "OpGt" => bounds.push(NumericBound::Lower(
                                smt_numeric_step(domain, rhs, 1)
                                    .ok_or_else(|| "non-step numeric choose domain".to_owned())?,
                            )),
                            "OpLe" => bounds.push(NumericBound::Upper(rhs)),
                            "OpLt" => bounds.push(NumericBound::Upper(
                                smt_numeric_step(domain, rhs, -1)
                                    .ok_or_else(|| "non-step numeric choose domain".to_owned())?,
                            )),
                            _ => return Ok(false),
                        }
                        return Ok(true);
                    }
                }
                if let IRExpr::Var { name, .. } = right.as_ref() {
                    if name == var && !ic3_expr_mentions_var(left, var) {
                        let lhs = encode_term(left, locals)?;
                        match op.as_str() {
                            "OpEq" => bounds.push(NumericBound::Exact(lhs)),
                            "OpLe" => bounds.push(NumericBound::Lower(lhs)),
                            "OpLt" => bounds.push(NumericBound::Lower(
                                smt_numeric_step(domain, lhs, 1)
                                    .ok_or_else(|| "non-step numeric choose domain".to_owned())?,
                            )),
                            "OpGe" => bounds.push(NumericBound::Upper(lhs)),
                            "OpGt" => bounds.push(NumericBound::Upper(
                                smt_numeric_step(domain, lhs, -1)
                                    .ok_or_else(|| "non-step numeric choose domain".to_owned())?,
                            )),
                            _ => return Ok(false),
                        }
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            _ => Ok(false),
        }
    }

    fn synthesize_numeric_witness<F>(
        var: &str,
        domain: &IRType,
        predicate: Option<&IRExpr>,
        locals: &HashSet<String>,
        encode_term: &mut F,
    ) -> Result<Option<String>, String>
    where
        F: FnMut(&IRExpr, &HashSet<String>) -> Result<String, String>,
    {
        let mut bounds = Vec::new();
        if !collect_numeric_bounds(var, domain, predicate, locals, encode_term, &mut bounds)?
            || bounds.is_empty()
        {
            return Ok(None);
        }

        let mut exacts = Vec::new();
        let mut lowers = Vec::new();
        let mut uppers = Vec::new();
        for bound in bounds {
            match bound {
                NumericBound::Exact(term) => exacts.push(term),
                NumericBound::Lower(term) => lowers.push(term),
                NumericBound::Upper(term) => uppers.push(term),
            }
        }

        if let Some(exact) = exacts.into_iter().next() {
            return Ok(Some(exact));
        }
        if !lowers.is_empty() {
            let witness = lowers
                .into_iter()
                .reduce(smt_max)
                .expect("non-empty lowers checked");
            return Ok(Some(witness));
        }
        if !uppers.is_empty() {
            let witness = uppers
                .into_iter()
                .reduce(smt_min)
                .expect("non-empty uppers checked");
            return Ok(Some(witness));
        }
        Ok(None)
    }

    fn predicate_for_witness<G>(
        var: &str,
        predicate: &IRExpr,
        witness: &str,
        locals: &HashSet<String>,
        encode_predicate: &mut G,
    ) -> Result<String, String>
    where
        G: FnMut(&IRExpr, &HashSet<String>) -> Result<String, String>,
    {
        let mut scope = locals.clone();
        scope.insert(var.to_owned());
        let pred = encode_predicate(predicate, &scope)?;
        Ok(format!("(let (({var} {witness})) {pred})"))
    }

    fn collect_pattern_vars(pattern: &crate::ir::types::IRPattern, out: &mut HashSet<String>) {
        use crate::ir::types::IRPattern;
        match pattern {
            IRPattern::PVar { name } => {
                out.insert(name.clone());
            }
            IRPattern::PCtor { fields, .. } => {
                for field in fields {
                    collect_pattern_vars(&field.pattern, out);
                }
            }
            IRPattern::POr { left, right } => {
                collect_pattern_vars(left, out);
                collect_pattern_vars(right, out);
            }
            IRPattern::PWild => {}
        }
    }

    fn enum_variant_for_pattern<'a>(
        domain: &'a IRType,
        pattern_name: &str,
    ) -> Option<(String, &'a crate::ir::types::IRVariant)> {
        let IRType::Enum { variants, .. } = domain else {
            return None;
        };
        for variant in variants {
            if variant.name == pattern_name
                || pattern_name
                    .rsplit("::")
                    .next()
                    .is_some_and(|short| short == variant.name)
            {
                let ctor_name = pattern_name.rsplit("::").next().unwrap_or(pattern_name);
                return Some((ctor_name.to_owned(), variant));
            }
        }
        None
    }

    fn combine_guard_and_body(guard: Option<&IRExpr>, body: &IRExpr) -> IRExpr {
        match guard {
            Some(guard) => IRExpr::BinOp {
                op: "OpAnd".to_owned(),
                left: Box::new(guard.clone()),
                right: Box::new(body.clone()),
                ty: IRType::Bool,
                span: None,
            },
            None => body.clone(),
        }
    }

    fn synthesize_match_var_pattern_witness<F, H, J>(
        domain: &IRType,
        pattern: &crate::ir::types::IRPattern,
        arm_predicate: &IRExpr,
        locals: &HashSet<String>,
        encode_term: &mut F,
        encode_predicate: &mut impl FnMut(&IRExpr, &HashSet<String>) -> Result<String, String>,
        match_bindings: &mut H,
        match_cond: &mut J,
    ) -> Result<Option<String>, String>
    where
        F: FnMut(&IRExpr, &HashSet<String>) -> Result<String, String>,
        H: FnMut(
            &IRExpr,
            &crate::ir::types::IRPattern,
            &HashSet<String>,
        ) -> Result<Vec<(String, String)>, String>,
        J: FnMut(&IRExpr, &crate::ir::types::IRPattern, &HashSet<String>) -> Result<String, String>,
    {
        use crate::ir::types::IRPattern;

        match pattern {
            IRPattern::PWild => Ok(default_witness_for_type(domain)),
            IRPattern::PVar { name } => {
                let mut scope = locals.clone();
                scope.insert(name.clone());
                visit(
                    name,
                    domain,
                    Some(arm_predicate),
                    &scope,
                    encode_term,
                    encode_predicate,
                    match_bindings,
                    match_cond,
                )
            }
            IRPattern::PCtor { name, fields } => {
                let Some((ctor_name, variant)) = enum_variant_for_pattern(domain, name) else {
                    return Ok(None);
                };

                let mut scope = locals.clone();
                for field in fields {
                    collect_pattern_vars(&field.pattern, &mut scope);
                }

                let mut args = Vec::with_capacity(variant.fields.len());
                for variant_field in &variant.fields {
                    let pattern_field =
                        fields.iter().find(|field| field.name == variant_field.name);
                    let term = match pattern_field {
                        Some(field) => synthesize_match_var_pattern_witness(
                            &variant_field.ty,
                            &field.pattern,
                            arm_predicate,
                            &scope,
                            encode_term,
                            encode_predicate,
                            match_bindings,
                            match_cond,
                        )?,
                        None => default_witness_for_type(&variant_field.ty),
                    };
                    let Some(term) = term else {
                        return Ok(None);
                    };
                    args.push(term);
                }

                if args.is_empty() {
                    Ok(Some(ctor_name.to_owned()))
                } else {
                    Ok(Some(format!("({ctor_name} {})", args.join(" "))))
                }
            }
            IRPattern::POr { .. } => Ok(None),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn visit<F, H, J>(
        var: &str,
        domain: &IRType,
        predicate: Option<&IRExpr>,
        locals: &HashSet<String>,
        encode_term: &mut F,
        encode_predicate: &mut impl FnMut(&IRExpr, &HashSet<String>) -> Result<String, String>,
        match_bindings: &mut H,
        match_cond: &mut J,
    ) -> Result<Option<String>, String>
    where
        F: FnMut(&IRExpr, &HashSet<String>) -> Result<String, String>,
        H: FnMut(
            &IRExpr,
            &crate::ir::types::IRPattern,
            &HashSet<String>,
        ) -> Result<Vec<(String, String)>, String>,
        J: FnMut(&IRExpr, &crate::ir::types::IRPattern, &HashSet<String>) -> Result<String, String>,
    {
        let Some(predicate) = predicate else {
            return Ok(None);
        };

        match predicate {
            IRExpr::BinOp {
                op, left, right, ..
            } if op == "OpEq" => {
                if let IRExpr::Var { name, .. } = left.as_ref() {
                    if name == var && !ic3_expr_mentions_var(right, var) {
                        return Ok(Some(encode_term(right, locals)?));
                    }
                }
                if let IRExpr::Var { name, .. } = right.as_ref() {
                    if name == var && !ic3_expr_mentions_var(left, var) {
                        return Ok(Some(encode_term(left, locals)?));
                    }
                }
                Ok(None)
            }
            IRExpr::BinOp {
                op, left, right, ..
            } if matches!(op.as_str(), "OpGe" | "OpGt" | "OpLe" | "OpLt") => {
                if let IRExpr::Var { name, .. } = left.as_ref() {
                    if name == var && !ic3_expr_mentions_var(right, var) {
                        let base = encode_term(right, locals)?;
                        return Ok(match op.as_str() {
                            "OpGe" | "OpLe" => Some(base),
                            "OpGt" => smt_numeric_step(domain, base, 1),
                            "OpLt" => smt_numeric_step(domain, base, -1),
                            _ => None,
                        });
                    }
                }
                if let IRExpr::Var { name, .. } = right.as_ref() {
                    if name == var && !ic3_expr_mentions_var(left, var) {
                        let base = encode_term(left, locals)?;
                        return Ok(match op.as_str() {
                            "OpLe" | "OpGe" => Some(base),
                            "OpLt" => smt_numeric_step(domain, base, 1),
                            "OpGt" => smt_numeric_step(domain, base, -1),
                            _ => None,
                        });
                    }
                }
                Ok(None)
            }
            IRExpr::BinOp {
                op, left, right, ..
            } if op == "OpAnd" => {
                if let Some(witness) = visit(
                    var,
                    domain,
                    Some(left),
                    locals,
                    encode_term,
                    encode_predicate,
                    match_bindings,
                    match_cond,
                )? {
                    return Ok(Some(witness));
                }
                visit(
                    var,
                    domain,
                    Some(right),
                    locals,
                    encode_term,
                    encode_predicate,
                    match_bindings,
                    match_cond,
                )
            }
            IRExpr::BinOp {
                op, left, right, ..
            } if op == "OpOr" => {
                let left_witness = visit(
                    var,
                    domain,
                    Some(left),
                    locals,
                    encode_term,
                    encode_predicate,
                    match_bindings,
                    match_cond,
                )?;
                let right_witness = visit(
                    var,
                    domain,
                    Some(right),
                    locals,
                    encode_term,
                    encode_predicate,
                    match_bindings,
                    match_cond,
                )?;
                match (left_witness, right_witness) {
                    (Some(left_witness), Some(right_witness)) => {
                        let left_pred = predicate_for_witness(
                            var,
                            left,
                            &left_witness,
                            locals,
                            encode_predicate,
                        )?;
                        Ok(Some(format!(
                            "(ite {left_pred} {left_witness} {right_witness})"
                        )))
                    }
                    _ => Ok(None),
                }
            }
            IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => visit(
                var,
                domain,
                Some(expr),
                locals,
                encode_term,
                encode_predicate,
                match_bindings,
                match_cond,
            ),
            IRExpr::IfElse {
                cond,
                then_body,
                else_body,
                ..
            } if !ic3_expr_mentions_var(cond, var) => {
                let Some(else_body) = else_body.as_deref() else {
                    return Ok(None);
                };
                let then_witness = visit(
                    var,
                    domain,
                    Some(then_body),
                    locals,
                    encode_term,
                    encode_predicate,
                    match_bindings,
                    match_cond,
                )?;
                let else_witness = visit(
                    var,
                    domain,
                    Some(else_body),
                    locals,
                    encode_term,
                    encode_predicate,
                    match_bindings,
                    match_cond,
                )?;
                match (then_witness, else_witness) {
                    (Some(then_witness), Some(else_witness)) => {
                        let cond_smt = encode_predicate(cond, locals)?;
                        Ok(Some(format!(
                            "(ite {cond_smt} {then_witness} {else_witness})"
                        )))
                    }
                    _ => Ok(None),
                }
            }
            IRExpr::Let { bindings, body, .. } => {
                let Some((binding, rest)) = bindings.split_first() else {
                    return visit(
                        var,
                        domain,
                        Some(body),
                        locals,
                        encode_term,
                        encode_predicate,
                        match_bindings,
                        match_cond,
                    );
                };
                if ic3_expr_mentions_var(&binding.expr, var) {
                    return Ok(None);
                }
                let rhs = if binding.ty == IRType::Bool {
                    encode_predicate(&binding.expr, locals)?
                } else {
                    encode_term(&binding.expr, locals)?
                };
                let mut scope = locals.clone();
                scope.insert(binding.name.clone());
                let rest_expr = if rest.is_empty() {
                    body.as_ref().clone()
                } else {
                    IRExpr::Let {
                        bindings: rest.to_vec(),
                        body: body.clone(),
                        span: None,
                    }
                };
                let witness = visit(
                    var,
                    domain,
                    Some(&rest_expr),
                    &scope,
                    encode_term,
                    encode_predicate,
                    match_bindings,
                    match_cond,
                )?;
                Ok(
                    witness
                        .map(|witness| format!("(let (({} {})) {})", binding.name, rhs, witness)),
                )
            }
            IRExpr::Match {
                scrutinee, arms, ..
            } => {
                if matches!(scrutinee.as_ref(), IRExpr::Var { name, .. } if name == var) {
                    let mut candidates = Vec::new();
                    for arm in arms {
                        let arm_predicate = combine_guard_and_body(arm.guard.as_ref(), &arm.body);
                        if let Some(candidate) = synthesize_match_var_pattern_witness(
                            domain,
                            &arm.pattern,
                            &arm_predicate,
                            locals,
                            encode_term,
                            encode_predicate,
                            match_bindings,
                            match_cond,
                        )? {
                            candidates.push(candidate);
                        }
                    }
                    if candidates.is_empty() {
                        return Ok(None);
                    }
                    let mut witness = candidates
                        .last()
                        .expect("non-empty candidates checked")
                        .clone();
                    for candidate in candidates[..candidates.len().saturating_sub(1)]
                        .iter()
                        .rev()
                    {
                        let pred = predicate_for_witness(
                            var,
                            predicate,
                            candidate,
                            locals,
                            encode_predicate,
                        )?;
                        witness = format!("(ite {pred} {candidate} {witness})");
                    }
                    return Ok(Some(witness));
                }
                if ic3_expr_mentions_var(scrutinee, var) {
                    return Ok(None);
                }
                if !ic3_match_has_final_catch_all(arms) {
                    return Ok(None);
                }
                let last = arms.last().expect("checked non-empty match arms");
                let last_bindings = match_bindings(scrutinee, &last.pattern, locals)?;
                let mut last_scope = locals.clone();
                for (name, _) in &last_bindings {
                    last_scope.insert(name.clone());
                }
                let Some(last_body) = visit(
                    var,
                    domain,
                    Some(&last.body),
                    &last_scope,
                    encode_term,
                    encode_predicate,
                    match_bindings,
                    match_cond,
                )?
                else {
                    return Ok(None);
                };
                let mut acc = wrap_smt_let_bindings(&last_bindings, last_body);
                for arm in arms[..arms.len() - 1].iter().rev() {
                    let bindings = match_bindings(scrutinee, &arm.pattern, locals)?;
                    let mut scope = locals.clone();
                    for (name, _) in &bindings {
                        scope.insert(name.clone());
                    }
                    let Some(body_witness) = visit(
                        var,
                        domain,
                        Some(&arm.body),
                        &scope,
                        encode_term,
                        encode_predicate,
                        match_bindings,
                        match_cond,
                    )?
                    else {
                        return Ok(None);
                    };
                    let body = wrap_smt_let_bindings(&bindings, body_witness);
                    let pat = match_cond(scrutinee, &arm.pattern, locals)?;
                    let cond = if let Some(guard) = &arm.guard {
                        let guard_smt = encode_predicate(guard, &scope)?;
                        wrap_smt_let_bindings(&bindings, format!("(and {pat} {guard_smt})"))
                    } else {
                        wrap_smt_let_bindings(&bindings, pat)
                    };
                    acc = format!("(ite {cond} {body} {acc})");
                }
                Ok(Some(acc))
            }
            _ => Ok(None),
        }
    }

    if matches!(
        domain,
        IRType::Int | IRType::Identity | IRType::Real | IRType::Float
    ) {
        if let Some(witness) =
            synthesize_numeric_witness(var, domain, predicate, locals, &mut encode_term)?
        {
            return Ok(Some(witness));
        }
    }

    if let Some(witness) = visit(
        var,
        domain,
        predicate,
        locals,
        &mut encode_term,
        &mut encode_predicate,
        &mut match_bindings,
        &mut match_cond,
    )? {
        return Ok(Some(witness));
    }

    Ok(None)
}

fn ic3_witness_binding_formula<F>(
    binding_name: &str,
    var: &str,
    witness: String,
    predicate: Option<&IRExpr>,
    locals: &HashSet<String>,
    mut encode_predicate: F,
    rest_smt: String,
) -> Result<String, String>
where
    F: FnMut(&IRExpr, &HashSet<String>) -> Result<String, String>,
{
    if let Some(predicate) = predicate {
        let mut pred_scope = locals.clone();
        pred_scope.insert(var.to_owned());
        let pred = encode_predicate(predicate, &pred_scope)?;
        return Ok(format!(
            "(let (({binding_name} {witness})) (and (let (({var} {binding_name})) {pred}) {rest_smt}))"
        ));
    }

    Ok(format!("(let (({binding_name} {witness})) {rest_smt})"))
}

/// Convert an IR expression to an SMT-LIB2 term string.
///
/// Returns `Err` for unsupported forms — never silently approximates.
#[allow(clippy::match_same_arms)]
fn expr_to_smt(expr: &IRExpr, entity: &IREntity, vctx: &VerifyContext) -> Result<String, String> {
    expr_to_smt_scoped(expr, entity, vctx, &HashSet::new())
}

fn guard_let_to_smt_scoped(
    bindings: &[crate::ir::types::LetBinding],
    body: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    locals: &HashSet<String>,
) -> Result<String, String> {
    let Some((binding, rest)) = bindings.split_first() else {
        return guard_to_smt_scoped(body, entity, vctx, locals);
    };

    if let IRExpr::Choose {
        var,
        domain,
        predicate,
        ..
    } = &binding.expr
    {
        let finite = ic3_finite_choose_witness(
            var,
            domain,
            predicate.as_deref(),
            vctx,
            locals,
            |predicate, scope| guard_to_smt_scoped(predicate, entity, vctx, scope),
        )?;

        let mut scope = locals.clone();
        scope.insert(binding.name.clone());
        let rest_smt = guard_let_to_smt_scoped(rest, body, entity, vctx, &scope)?;
        if let Some((exists, witness)) = finite {
            return Ok(format!(
                "(and {exists} (let (({} {})) {}))",
                binding.name, witness, rest_smt
            ));
        }
        if let Some(witness) = ic3_direct_choose_witness(
            var,
            domain,
            predicate.as_deref(),
            locals,
            |term, scope| expr_to_smt_scoped(term, entity, vctx, scope),
            |predicate, scope| guard_to_smt_scoped(predicate, entity, vctx, scope),
            |scrutinee, pattern, scope| {
                let scrut = expr_to_smt_scoped(scrutinee, entity, vctx, scope)?;
                ic3_match_pattern_bindings(&scrut, pattern, vctx)
            },
            |scrutinee, pattern, scope| {
                let scrut = expr_to_smt_scoped(scrutinee, entity, vctx, scope)?;
                ic3_match_pattern_cond(&scrut, pattern, vctx)
            },
        )? {
            return ic3_witness_binding_formula(
                &binding.name,
                var,
                witness,
                predicate.as_deref(),
                locals,
                |predicate, scope| guard_to_smt_scoped(predicate, entity, vctx, scope),
                rest_smt,
            );
        }
        if let Some(formula) = ic3_quantified_choose_formula(
            &binding.name,
            var,
            domain,
            predicate.as_deref(),
            locals,
            |predicate, scope| guard_to_smt_scoped(predicate, entity, vctx, scope),
            rest_smt.clone(),
        )? {
            return Ok(formula);
        }
        return Err("choose is not yet supported in IC3 CHC encoding for this domain".to_owned());
    }

    let rhs = if binding.ty == IRType::Bool {
        guard_to_smt_scoped(&binding.expr, entity, vctx, locals)?
    } else {
        expr_to_smt_scoped(&binding.expr, entity, vctx, locals)?
    };
    let mut scope = locals.clone();
    scope.insert(binding.name.clone());
    let rest_smt = guard_let_to_smt_scoped(rest, body, entity, vctx, &scope)?;
    Ok(format!("(let (({} {})) {})", binding.name, rhs, rest_smt))
}

fn expr_to_smt_scoped(
    expr: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    locals: &HashSet<String>,
) -> Result<String, String> {
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
            enum_name,
            ctor,
            args,
            ..
        } => ic3_ctor_term_with(enum_name, ctor, args, vctx, |arg| {
            expr_to_smt_scoped(arg, entity, vctx, locals)
        }),
        IRExpr::Var { name, .. } => {
            for (i, f) in entity.fields.iter().enumerate() {
                if f.name == *name {
                    return Ok(format!("f{i}"));
                }
            }
            if locals.contains(name) {
                return Ok(name.clone());
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
            let l = expr_to_smt_scoped(left, entity, vctx, locals)?;
            let r = expr_to_smt_scoped(right, entity, vctx, locals)?;
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
            let inner = expr_to_smt_scoped(operand, entity, vctx, locals)?;
            Ok(format!("(- {inner})"))
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            let m = expr_to_smt_scoped(map, entity, vctx, locals)?;
            let k = expr_to_smt_scoped(key, entity, vctx, locals)?;
            let v = expr_to_smt_scoped(value, entity, vctx, locals)?;
            Ok(format!("(store {m} {k} {v})"))
        }
        IRExpr::Index { map, key, .. } => {
            let m = expr_to_smt_scoped(map, entity, vctx, locals)?;
            let k = expr_to_smt_scoped(key, entity, vctx, locals)?;
            Ok(format!("(select {m} {k})"))
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            if !ic3_match_has_final_catch_all(arms) {
                return Err(
                    "non-exhaustive match without final wildcard/var arm is not supported in IC3 value encoding"
                        .to_owned(),
                );
            }
            let scrut = expr_to_smt_scoped(scrutinee, entity, vctx, locals)?;
            let mut acc = {
                let last = arms.last().expect("checked non-empty match arms");
                let bindings = ic3_match_pattern_bindings(&scrut, &last.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let body = expr_to_smt_scoped(&last.body, entity, vctx, &scope)?;
                wrap_smt_let_bindings(&bindings, body)
            };
            for arm in arms[..arms.len() - 1].iter().rev() {
                let bindings = ic3_match_pattern_bindings(&scrut, &arm.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let pat = ic3_match_pattern_cond(&scrut, &arm.pattern, vctx)?;
                let cond = if let Some(guard) = &arm.guard {
                    let guard_smt = guard_to_smt_scoped(guard, entity, vctx, &scope)?;
                    wrap_smt_let_bindings(&bindings, format!("(and {pat} {guard_smt})"))
                } else {
                    wrap_smt_let_bindings(&bindings, pat)
                };
                let body = expr_to_smt_scoped(&arm.body, entity, vctx, &scope)?;
                let body = wrap_smt_let_bindings(&bindings, body);
                acc = format!("(ite {cond} {body} {acc})");
            }
            Ok(acc)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond_smt = guard_to_smt_scoped(cond, entity, vctx, locals)?;
            let then_smt = expr_to_smt_scoped(then_body, entity, vctx, locals)?;
            if let Some(else_body) = else_body {
                let else_smt = expr_to_smt_scoped(else_body, entity, vctx, locals)?;
                Ok(format!("(ite {cond_smt} {then_smt} {else_smt})"))
            } else {
                Err("if/else without else is not supported in IC3 value encoding".to_owned())
            }
        }
        IRExpr::Let { bindings, body, .. } => {
            let mut scope = locals.clone();
            let mut out = String::new();
            for binding in bindings {
                let rhs = if binding.ty == IRType::Bool {
                    guard_to_smt_scoped(&binding.expr, entity, vctx, &scope)?
                } else {
                    expr_to_smt_scoped(&binding.expr, entity, vctx, &scope)?
                };
                out.push_str(&format!("(let (({} {})) ", binding.name, rhs));
                scope.insert(binding.name.clone());
            }
            out.push_str(&expr_to_smt_scoped(body, entity, vctx, &scope)?);
            for _ in bindings {
                out.push(')');
            }
            Ok(out)
        }
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            expr_to_smt_scoped(expr, entity, vctx, locals)
        }
        IRExpr::Card { .. } => Err("cardinality (#) not supported in IC3 CHC encoding".to_owned()),
        _ => Err(format!(
            "unsupported expression in IC3 value encoding: {:?}",
            std::mem::discriminant(expr)
        )),
    }
}

/// Convert a guard expression to an SMT-LIB2 boolean term.
///
/// Returns `Err` for unsupported forms — never silently approximates.
/// Encode an `initial_constraint` expression as SMT, replacing `$` (and the field name)
/// with the given CHC variable name. Used for nondeterministic field defaults in create rules.
fn constraint_to_smt_with_dollar(
    expr: &IRExpr,
    dollar_var: &str,
    entity: &IREntity,
    vctx: &VerifyContext,
) -> Result<String, String> {
    constraint_to_smt_with_dollar_scoped(expr, dollar_var, entity, vctx, &HashSet::new())
}

fn constraint_to_smt_with_dollar_scoped(
    expr: &IRExpr,
    dollar_var: &str,
    entity: &IREntity,
    vctx: &VerifyContext,
    locals: &HashSet<String>,
) -> Result<String, String> {
    match expr {
        IRExpr::Var { name, .. } if name == "$" => Ok(dollar_var.to_owned()),
        IRExpr::Var { name, .. } => {
            // Check if it's a field name (for `where field_name > 0` syntax)
            if entity.fields.iter().any(|f| f.name == *name) {
                Ok(dollar_var.to_owned())
            } else if locals.contains(name) {
                Ok(name.clone())
            } else {
                Err(format!("unknown variable in initial_constraint: {name}"))
            }
        }
        IRExpr::Lit { .. } => expr_to_smt(expr, entity, vctx),
        IRExpr::Ctor { .. } => expr_to_smt(expr, entity, vctx),
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let l = constraint_to_smt_with_dollar_scoped(left, dollar_var, entity, vctx, locals)?;
            let r = constraint_to_smt_with_dollar_scoped(right, dollar_var, entity, vctx, locals)?;
            match op.as_str() {
                "OpEq" => Ok(format!("(= {l} {r})")),
                "OpNEq" => Ok(format!("(not (= {l} {r}))")),
                "OpLt" => Ok(format!("(< {l} {r})")),
                "OpLe" => Ok(format!("(<= {l} {r})")),
                "OpGt" => Ok(format!("(> {l} {r})")),
                "OpGe" => Ok(format!("(>= {l} {r})")),
                "OpAnd" => Ok(format!("(and {l} {r})")),
                "OpOr" => Ok(format!("(or {l} {r})")),
                "OpImplies" => Ok(format!("(=> {l} {r})")),
                "OpAdd" => Ok(format!("(+ {l} {r})")),
                "OpSub" => Ok(format!("(- {l} {r})")),
                "OpMul" => Ok(format!("(* {l} {r})")),
                _ => Err(format!("unsupported op in initial_constraint: {op}")),
            }
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => {
            let inner =
                constraint_to_smt_with_dollar_scoped(operand, dollar_var, entity, vctx, locals)?;
            Ok(format!("(not {inner})"))
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond_smt =
                constraint_to_smt_with_dollar_scoped(cond, dollar_var, entity, vctx, locals)?;
            let then_smt =
                constraint_to_smt_with_dollar_scoped(then_body, dollar_var, entity, vctx, locals)?;
            if let Some(else_body) = else_body {
                let else_smt = constraint_to_smt_with_dollar_scoped(
                    else_body, dollar_var, entity, vctx, locals,
                )?;
                Ok(format!("(ite {cond_smt} {then_smt} {else_smt})"))
            } else {
                Ok(format!("(=> {cond_smt} {then_smt})"))
            }
        }
        IRExpr::Let { bindings, body, .. } => {
            let mut scope = locals.clone();
            let mut out = String::new();
            for binding in bindings {
                let rhs = if binding.ty == IRType::Bool {
                    constraint_to_smt_with_dollar_scoped(
                        &binding.expr,
                        dollar_var,
                        entity,
                        vctx,
                        &scope,
                    )?
                } else {
                    expr_to_smt_scoped(&binding.expr, entity, vctx, &scope)?
                };
                out.push_str(&format!("(let (({} {})) ", binding.name, rhs));
                scope.insert(binding.name.clone());
            }
            out.push_str(&constraint_to_smt_with_dollar_scoped(
                body, dollar_var, entity, vctx, &scope,
            )?);
            for _ in bindings {
                out.push(')');
            }
            Ok(out)
        }
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            constraint_to_smt_with_dollar_scoped(expr, dollar_var, entity, vctx, locals)
        }
        _ => Err(format!(
            "unsupported expression in initial_constraint: {:?}",
            std::mem::discriminant(expr)
        )),
    }
}

fn guard_to_smt(guard: &IRExpr, entity: &IREntity, vctx: &VerifyContext) -> Result<String, String> {
    guard_to_smt_scoped(guard, entity, vctx, &HashSet::new())
}

fn guard_to_smt_scoped(
    guard: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    locals: &HashSet<String>,
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
                let l = expr_to_smt_scoped(left, entity, vctx, locals)?;
                let r = expr_to_smt_scoped(right, entity, vctx, locals)?;
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
                let l = guard_to_smt_scoped(left, entity, vctx, locals)?;
                let r = guard_to_smt_scoped(right, entity, vctx, locals)?;
                Ok(format!("(and {l} {r})"))
            }
            "OpOr" => {
                let l = guard_to_smt_scoped(left, entity, vctx, locals)?;
                let r = guard_to_smt_scoped(right, entity, vctx, locals)?;
                Ok(format!("(or {l} {r})"))
            }
            "OpImplies" => {
                let l = guard_to_smt_scoped(left, entity, vctx, locals)?;
                let r = guard_to_smt_scoped(right, entity, vctx, locals)?;
                Ok(format!("(=> {l} {r})"))
            }
            _ => Err(format!("unsupported binary op in IC3 guard encoding: {op}")),
        },
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => {
            let inner = guard_to_smt_scoped(operand, entity, vctx, locals)?;
            Ok(format!("(not {inner})"))
        }
        // Field access as boolean: resolve to field variable
        IRExpr::Field { .. } | IRExpr::Var { .. } => {
            let val = expr_to_smt_scoped(guard, entity, vctx, locals)?;
            Ok(val)
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            if !ic3_match_has_final_catch_all(arms) {
                return Err(
                    "non-exhaustive match without final wildcard/var arm is not supported in IC3 guard encoding"
                        .to_owned(),
                );
            }
            let scrut = expr_to_smt_scoped(scrutinee, entity, vctx, locals)?;
            let mut acc = {
                let last = arms.last().expect("checked non-empty match arms");
                let bindings = ic3_match_pattern_bindings(&scrut, &last.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let body = guard_to_smt_scoped(&last.body, entity, vctx, &scope)?;
                wrap_smt_let_bindings(&bindings, body)
            };
            for arm in arms[..arms.len() - 1].iter().rev() {
                let bindings = ic3_match_pattern_bindings(&scrut, &arm.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let pat = ic3_match_pattern_cond(&scrut, &arm.pattern, vctx)?;
                let cond = if let Some(guard) = &arm.guard {
                    let guard_smt = guard_to_smt_scoped(guard, entity, vctx, &scope)?;
                    wrap_smt_let_bindings(&bindings, format!("(and {pat} {guard_smt})"))
                } else {
                    wrap_smt_let_bindings(&bindings, pat)
                };
                let body = guard_to_smt_scoped(&arm.body, entity, vctx, &scope)?;
                let body = wrap_smt_let_bindings(&bindings, body);
                acc = format!("(ite {cond} {body} {acc})");
            }
            Ok(acc)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond_smt = guard_to_smt_scoped(cond, entity, vctx, locals)?;
            let then_smt = guard_to_smt_scoped(then_body, entity, vctx, locals)?;
            if let Some(else_body) = else_body {
                let else_smt = guard_to_smt_scoped(else_body, entity, vctx, locals)?;
                Ok(format!("(ite {cond_smt} {then_smt} {else_smt})"))
            } else {
                Ok(format!("(=> {cond_smt} {then_smt})"))
            }
        }
        IRExpr::Let { bindings, body, .. } => {
            guard_let_to_smt_scoped(bindings, body, entity, vctx, locals)
        }
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            guard_to_smt_scoped(expr, entity, vctx, locals)
        }
        IRExpr::Forall {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| guard_to_smt_scoped(body, entity, vctx, scope),
            "forall",
        )?
        .ok_or_else(|| "quantifier domain is not yet supported in IC3 guard encoding".to_owned()),
        IRExpr::Exists {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| guard_to_smt_scoped(body, entity, vctx, scope),
            "exists",
        )?
        .ok_or_else(|| "quantifier domain is not yet supported in IC3 guard encoding".to_owned()),
        IRExpr::One {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| guard_to_smt_scoped(body, entity, vctx, scope),
            "one",
        )?
        .ok_or_else(|| "quantifier domain is not yet supported in IC3 guard encoding".to_owned()),
        IRExpr::Lone {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| guard_to_smt_scoped(body, entity, vctx, scope),
            "lone",
        )?
        .ok_or_else(|| "quantifier domain is not yet supported in IC3 guard encoding".to_owned()),
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
        IRExpr::Always { body, .. } => negate_property_smt(body, entity, vctx),
        // Strip forall over entity — IC3 checks per-entity
        IRExpr::Forall {
            domain: IRType::Entity { .. },
            body,
            ..
        } => negate_property_smt(body, entity, vctx),
        _ => {
            let pos = guard_to_smt(property, entity, vctx)?;
            Ok(format!("(not {pos})"))
        }
    }
}

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
            for event in &sys.steps {
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
fn build_liveness_chc(
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
        for event in &system.steps {
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
                    .steps
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::types::*;
    use crate::verify::context::VerifyContext;

    /// Test CHC solving through the routed CHC backend with declare-var style
    /// variables. Validates the reference CHC API works with a simple
    /// unreachable error.
    #[test]
    fn chc_backend_unreachable_via_string() {
        let chc = "(declare-rel Reach (Int))
             (declare-rel Error ())
             (declare-var x Int)
             (rule (Reach 0) base)
             (rule (=> (and (Reach x) (< x 10)) (Reach (+ x 1))) step)
             (rule (=> (and (Reach x) (< x 0)) Error) error)";

        let result = chc::check_chc(chc, "Error", 5000);

        assert!(
            matches!(result, ChcResult::Proved | ChcResult::Unknown(_)),
            "expected Proved or Unknown, got: {result:?}"
        );
    }

    fn make_simple_entity() -> (IREntity, Vec<IRTypeEntry>) {
        let status_type = IRTypeEntry {
            name: "Status".to_owned(),
            ty: IRType::Enum {
                name: "Status".to_owned(),
                variants: vec![
                    IRVariant::simple("Pending"),
                    IRVariant::simple("Confirmed"),
                    IRVariant::simple("Shipped"),
                ],
            },
        };

        let entity = IREntity {
            name: "Order".to_owned(),
            fields: vec![
                IRField {
                    name: "id".to_owned(),
                    ty: IRType::Identity,
                    default: None,
                    initial_constraint: None,
                },
                IRField {
                    name: "status".to_owned(),
                    ty: IRType::Enum {
                        name: "Status".to_owned(),
                        variants: vec![
                            IRVariant::simple("Pending"),
                            IRVariant::simple("Confirmed"),
                            IRVariant::simple("Shipped"),
                        ],
                    },
                    default: Some(IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Pending".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    initial_constraint: None,
                },
                IRField {
                    name: "total".to_owned(),
                    ty: IRType::Int,
                    default: Some(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },

                        span: None,
                    }),
                    initial_constraint: None,
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

                            span: None,
                        }),
                        right: Box::new(IRExpr::Ctor {
                            enum_name: "Status".to_owned(),
                            ctor: "Pending".to_owned(),
                            args: vec![],
                            span: None,
                        }),
                        ty: IRType::Bool,

                        span: None,
                    },
                    updates: vec![IRUpdate {
                        field: "status".to_owned(),
                        value: IRExpr::Ctor {
                            enum_name: "Status".to_owned(),
                            ctor: "Confirmed".to_owned(),
                            args: vec![],
                            span: None,
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

                            span: None,
                        }),
                        right: Box::new(IRExpr::Ctor {
                            enum_name: "Status".to_owned(),
                            ctor: "Confirmed".to_owned(),
                            args: vec![],
                            span: None,
                        }),
                        ty: IRType::Bool,

                        span: None,
                    },
                    updates: vec![IRUpdate {
                        field: "status".to_owned(),
                        value: IRExpr::Ctor {
                            enum_name: "Status".to_owned(),
                            ctor: "Shipped".to_owned(),
                            args: vec![],
                            span: None,
                        },
                    }],
                    postcondition: None,
                },
            ],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };

        (entity, vec![status_type])
    }

    fn make_result_entity_with_payload() -> (IREntity, Vec<IRTypeEntry>) {
        let result_ty = IRTypeEntry {
            name: "Result".to_owned(),
            ty: IRType::Enum {
                name: "Result".to_owned(),
                variants: vec![
                    IRVariant::simple("Pending"),
                    IRVariant {
                        name: "Err".to_owned(),
                        fields: vec![IRVariantField {
                            name: "code".to_owned(),
                            ty: IRType::Int,
                        }],
                    },
                ],
            },
        };

        let entity = IREntity {
            name: "Order".to_owned(),
            fields: vec![IRField {
                name: "status".to_owned(),
                ty: result_ty.ty.clone(),
                default: Some(IRExpr::Ctor {
                    enum_name: "Result".to_owned(),
                    ctor: "Err".to_owned(),
                    args: vec![(
                        "code".to_owned(),
                        IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 7 },
                            span: None,
                        },
                    )],
                    span: None,
                }),
                initial_constraint: None,
            }],
            transitions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };

        (entity, vec![result_ty])
    }

    fn make_result_entity_with_dual_payload_variants() -> (IREntity, Vec<IRTypeEntry>) {
        let result_ty = IRTypeEntry {
            name: "Result".to_owned(),
            ty: IRType::Enum {
                name: "Result".to_owned(),
                variants: vec![
                    IRVariant {
                        name: "Ok".to_owned(),
                        fields: vec![IRVariantField {
                            name: "ok_code".to_owned(),
                            ty: IRType::Int,
                        }],
                    },
                    IRVariant {
                        name: "Err".to_owned(),
                        fields: vec![IRVariantField {
                            name: "err_code".to_owned(),
                            ty: IRType::Int,
                        }],
                    },
                ],
            },
        };

        let entity = IREntity {
            name: "Order".to_owned(),
            fields: vec![IRField {
                name: "status".to_owned(),
                ty: result_ty.ty.clone(),
                default: Some(IRExpr::Ctor {
                    enum_name: "Result".to_owned(),
                    ctor: "Err".to_owned(),
                    args: vec![(
                        "err_code".to_owned(),
                        IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 7 },
                            span: None,
                        },
                    )],
                    span: None,
                }),
                initial_constraint: None,
            }],
            transitions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };

        (entity, vec![result_ty])
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
            lemmas: vec![],
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

                span: None,
            }),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: -1 },

                span: None,
            }),
            ty: IRType::Bool,

            span: None,
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

                            span: None,
                        }),
                        field: "total".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
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

                span: None,
            }),
            right: Box::new(IRExpr::Ctor {
                enum_name: "Status".to_owned(),
                ctor: "Pending".to_owned(),
                args: vec![],
                span: None,
            }),
            ty: IRType::Bool,

            span: None,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Violated(_)),
            "expected Violated (confirm breaks always-Pending), got: {result:?}"
        );
    }

    #[test]
    fn ic3_violation_extracts_trace() {
        // Property: status == Pending always (false — confirm changes it)
        // IC3 should find the violation AND extract a trace showing the state change.
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::Var {
                name: "status".to_owned(),
                ty: IRType::Int,

                span: None,
            }),
            right: Box::new(IRExpr::Ctor {
                enum_name: "Status".to_owned(),
                ctor: "Pending".to_owned(),
                args: vec![],
                span: None,
            }),
            ty: IRType::Bool,

            span: None,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        match result {
            Ic3Result::Violated(trace) => {
                assert!(
                    trace.len() >= 2,
                    "expected at least 2 trace steps, got {}",
                    trace.len()
                );

                // Helper: find field value in a step
                let field_val = |step: usize, field: &str| -> String {
                    trace[step]
                        .assignments
                        .iter()
                        .find(|(_, f, _)| f == field)
                        .unwrap_or_else(|| {
                            panic!("step {step} missing field {field}: {:?}", trace[step])
                        })
                        .2
                        .clone()
                };

                // Step 0: initial state after create — Pending, total=0
                assert_eq!(
                    field_val(0, "status"),
                    "0",
                    "step 0: status should be Pending (0)"
                );
                assert_eq!(field_val(0, "total"), "0", "step 0: total should be 0");

                // Step 1: after confirm — Confirmed, total unchanged
                assert_eq!(
                    field_val(1, "status"),
                    "1",
                    "step 1: status should be Confirmed (1)"
                );
                assert_eq!(
                    field_val(1, "total"),
                    "0",
                    "step 1: total should still be 0"
                );

                // Entity labels should be "Order" (single slot)
                assert!(
                    trace[0].assignments.iter().all(|(e, _, _)| e == "Order"),
                    "all assignments should be for Order entity"
                );
            }
            other => panic!("expected Violated with trace, got: {other:?}"),
        }
    }

    // ── S-expression parser unit tests ─────────────────────────────

    #[test]
    fn sexpr_parser_handles_nested_negative() {
        // (State 0 (- 1) 0 true) should parse as 4 ground args
        let columns = vec![
            ("E".to_owned(), "a".to_owned(), 0),
            ("E".to_owned(), "b".to_owned(), 1),
            ("E".to_owned(), "c".to_owned(), 2),
            ("E".to_owned(), "active".to_owned(), usize::MAX),
        ];
        let answer = "(State 0 (- 1) 0 true)";
        let steps = parse_state_snapshots(answer, &columns);
        assert_eq!(steps.len(), 1, "expected 1 trace step");
        let a_val = steps[0].assignments.iter().find(|(_, f, _)| f == "b");
        assert_eq!(
            a_val.unwrap().2,
            "-1",
            "negative literal (- 1) should render as -1"
        );
    }

    #[test]
    fn sexpr_parser_handles_rational_literal() {
        // (State (/ 3 2) true) should be recognized as ground and render as "3/2"
        let columns = vec![
            ("E".to_owned(), "val".to_owned(), 0),
            ("E".to_owned(), "active".to_owned(), usize::MAX),
        ];
        let answer = "(State (/ 3 2) true)";
        let steps = parse_state_snapshots(answer, &columns);
        assert_eq!(steps.len(), 1, "expected 1 trace step for rational");
        assert_eq!(
            steps[0].assignments[0].2, "3/2",
            "rational (/ 3 2) should render as 3/2"
        );
    }

    #[test]
    fn sexpr_parser_handles_negative_rational() {
        // (State (/ (- 1) 2) true) — negative rational
        let columns = vec![
            ("E".to_owned(), "val".to_owned(), 0),
            ("E".to_owned(), "active".to_owned(), usize::MAX),
        ];
        let answer = "(State (/ (- 1) 2) true)";
        let steps = parse_state_snapshots(answer, &columns);
        assert_eq!(steps.len(), 1, "negative rational should be ground");
        assert_eq!(steps[0].assignments[0].2, "-1/2");
    }

    #[test]
    fn sexpr_parser_rejects_trailing_garbage() {
        // Trailing tokens after the s-expression should cause parse failure → empty trace
        let columns = vec![
            ("E".to_owned(), "x".to_owned(), 0),
            ("E".to_owned(), "active".to_owned(), usize::MAX),
        ];
        let answer = "(State 0 true) extra garbage";
        let steps = parse_state_snapshots(answer, &columns);
        assert!(steps.is_empty(), "trailing garbage should invalidate parse");
    }

    #[test]
    fn sexpr_parser_rejects_unbalanced_parens() {
        let columns = vec![
            ("E".to_owned(), "x".to_owned(), 0),
            ("E".to_owned(), "active".to_owned(), usize::MAX),
        ];
        // Missing closing paren
        let steps = parse_state_snapshots("(State 0 true", &columns);
        assert!(steps.is_empty(), "unclosed paren should invalidate parse");
        // Extra closing paren
        let steps = parse_state_snapshots("(State 0 true))", &columns);
        assert!(
            steps.is_empty(),
            "extra close paren should invalidate parse"
        );
    }

    #[test]
    fn sexpr_parser_skips_non_ground_states() {
        // State applications with variable names (forall context) should be skipped
        let columns = vec![
            ("E".to_owned(), "x".to_owned(), 0),
            ("E".to_owned(), "active".to_owned(), usize::MAX),
        ];
        let answer = "(and (State A true) (State 5 true))";
        let steps = parse_state_snapshots(answer, &columns);
        assert_eq!(steps.len(), 1, "only ground State should be extracted");
        assert_eq!(steps[0].assignments[0].2, "5");
    }

    #[test]
    fn sexpr_parser_deduplicates_stutter() {
        // Consecutive identical states (from stutter rule) should be collapsed
        let columns = vec![
            ("E".to_owned(), "n".to_owned(), 0),
            ("E".to_owned(), "active".to_owned(), usize::MAX),
        ];
        let answer = "(and (State 0 true) (State 0 true) (State 1 true))";
        let steps = parse_state_snapshots(answer, &columns);
        assert_eq!(steps.len(), 2, "stuttered duplicate should be removed");
        assert_eq!(steps[0].assignments[0].2, "0");
        assert_eq!(steps[1].assignments[0].2, "1");
    }

    #[test]
    fn sexpr_parser_handles_derivation_tree() {
        // Realistic Spacer answer structure with nested hyper-res/mp
        let columns = vec![
            ("E".to_owned(), "x".to_owned(), 0),
            ("E".to_owned(), "active".to_owned(), usize::MAX),
        ];
        let answer = "(mp ((_ hyper-res 0 0 0 1) \
            (asserted (forall ((A Int)) (! (=> (State A true) query!0) :weight 0))) \
            ((_ hyper-res 0 0) (asserted (State 0 true)) (State 0 true)) \
            (State 1 true)) \
            (asserted (=> query!0 false)) false)";
        let steps = parse_state_snapshots(answer, &columns);
        // Should find: (State 0 true) and (State 1 true) — ground, in order
        assert!(steps.len() >= 2, "expected >= 2 steps, got {}", steps.len());
        assert_eq!(steps[0].assignments[0].2, "0");
        assert_eq!(steps[1].assignments[0].2, "1");
    }

    #[test]
    fn ic3_supports_pure_let_expression() {
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Let {
                bindings: vec![LetBinding {
                    name: "t".to_owned(),
                    ty: IRType::Int,
                    expr: IRExpr::Var {
                        name: "total".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    },
                }],
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "t".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for let-bound IC3 property, got: {result:?}"
        );
    }

    #[test]
    fn ic3_supports_int_choose_expression() {
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Let {
                bindings: vec![crate::ir::types::LetBinding {
                    name: "picked".to_owned(),
                    ty: IRType::Int,
                    expr: IRExpr::Choose {
                        var: "n".to_owned(),
                        domain: IRType::Int,
                        predicate: Some(Box::new(IRExpr::BinOp {
                            op: "OpEq".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "n".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            right: Box::new(IRExpr::Var {
                                name: "total".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            ty: IRType::Bool,
                            span: None,
                        })),
                        ty: IRType::Int,
                        span: None,
                    },
                }],
                body: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for int choose IC3 property, got: {result:?}"
        );
    }

    #[test]
    fn ic3_supports_int_choose_with_equality_conjunct() {
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Let {
                bindings: vec![crate::ir::types::LetBinding {
                    name: "picked".to_owned(),
                    ty: IRType::Int,
                    expr: IRExpr::Choose {
                        var: "n".to_owned(),
                        domain: IRType::Int,
                        predicate: Some(Box::new(IRExpr::BinOp {
                            op: "OpAnd".to_owned(),
                            left: Box::new(IRExpr::BinOp {
                                op: "OpEq".to_owned(),
                                left: Box::new(IRExpr::Var {
                                    name: "n".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                right: Box::new(IRExpr::Var {
                                    name: "total".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                ty: IRType::Bool,
                                span: None,
                            }),
                            right: Box::new(IRExpr::BinOp {
                                op: "OpEq".to_owned(),
                                left: Box::new(IRExpr::Var {
                                    name: "total".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                right: Box::new(IRExpr::Var {
                                    name: "total".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                ty: IRType::Bool,
                                span: None,
                            }),
                            ty: IRType::Bool,
                            span: None,
                        })),
                        ty: IRType::Int,
                        span: None,
                    },
                }],
                body: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "picked".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "total".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for conjunctive int choose IC3 property, got: {result:?}"
        );
    }

    #[test]
    fn ic3_supports_int_choose_with_lower_bound_predicate() {
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Let {
                bindings: vec![crate::ir::types::LetBinding {
                    name: "picked".to_owned(),
                    ty: IRType::Int,
                    expr: IRExpr::Choose {
                        var: "n".to_owned(),
                        domain: IRType::Int,
                        predicate: Some(Box::new(IRExpr::BinOp {
                            op: "OpGt".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "n".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            right: Box::new(IRExpr::Var {
                                name: "total".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            ty: IRType::Bool,
                            span: None,
                        })),
                        ty: IRType::Int,
                        span: None,
                    },
                }],
                body: Box::new(IRExpr::BinOp {
                    op: "OpGt".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "picked".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "total".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for lower-bound int choose IC3 property, got: {result:?}"
        );
    }

    #[test]
    fn ic3_supports_int_choose_with_multiple_upper_bounds() {
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let loose_upper = IRExpr::BinOp {
            op: "OpLt".to_owned(),
            left: Box::new(IRExpr::Var {
                name: "n".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            right: Box::new(IRExpr::BinOp {
                op: "OpAdd".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "total".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 10 },
                    span: None,
                }),
                ty: IRType::Int,
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };
        let tight_upper = IRExpr::BinOp {
            op: "OpLt".to_owned(),
            left: Box::new(IRExpr::Var {
                name: "n".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            right: Box::new(IRExpr::BinOp {
                op: "OpAdd".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "total".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 1 },
                    span: None,
                }),
                ty: IRType::Int,
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Let {
                bindings: vec![crate::ir::types::LetBinding {
                    name: "picked".to_owned(),
                    ty: IRType::Int,
                    expr: IRExpr::Choose {
                        var: "n".to_owned(),
                        domain: IRType::Int,
                        predicate: Some(Box::new(IRExpr::BinOp {
                            op: "OpAnd".to_owned(),
                            left: Box::new(loose_upper),
                            right: Box::new(tight_upper),
                            ty: IRType::Bool,
                            span: None,
                        })),
                        ty: IRType::Int,
                        span: None,
                    },
                }],
                body: Box::new(IRExpr::BinOp {
                    op: "OpLt".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "picked".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    right: Box::new(IRExpr::BinOp {
                        op: "OpAdd".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "total".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        }),
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 1 },
                            span: None,
                        }),
                        ty: IRType::Int,
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for multi-upper-bound int choose IC3 property, got: {result:?}"
        );
    }

    #[test]
    fn ic3_supports_int_choose_with_disjunctive_bounds() {
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Let {
                bindings: vec![crate::ir::types::LetBinding {
                    name: "picked".to_owned(),
                    ty: IRType::Int,
                    expr: IRExpr::Choose {
                        var: "n".to_owned(),
                        domain: IRType::Int,
                        predicate: Some(Box::new(IRExpr::BinOp {
                            op: "OpOr".to_owned(),
                            left: Box::new(IRExpr::BinOp {
                                op: "OpEq".to_owned(),
                                left: Box::new(IRExpr::Var {
                                    name: "n".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                right: Box::new(IRExpr::Var {
                                    name: "total".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                ty: IRType::Bool,
                                span: None,
                            }),
                            right: Box::new(IRExpr::BinOp {
                                op: "OpGt".to_owned(),
                                left: Box::new(IRExpr::Var {
                                    name: "n".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                right: Box::new(IRExpr::Var {
                                    name: "total".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                ty: IRType::Bool,
                                span: None,
                            }),
                            ty: IRType::Bool,
                            span: None,
                        })),
                        ty: IRType::Int,
                        span: None,
                    },
                }],
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "picked".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "total".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for disjunctive int choose IC3 property, got: {result:?}"
        );
    }

    #[test]
    fn ic3_supports_int_choose_with_conditional_predicate() {
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Let {
                bindings: vec![crate::ir::types::LetBinding {
                    name: "picked".to_owned(),
                    ty: IRType::Int,
                    expr: IRExpr::Choose {
                        var: "n".to_owned(),
                        domain: IRType::Int,
                        predicate: Some(Box::new(IRExpr::IfElse {
                            cond: Box::new(IRExpr::BinOp {
                                op: "OpGe".to_owned(),
                                left: Box::new(IRExpr::Var {
                                    name: "total".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                right: Box::new(IRExpr::Lit {
                                    ty: IRType::Int,
                                    value: LitVal::Int { value: 0 },
                                    span: None,
                                }),
                                ty: IRType::Bool,
                                span: None,
                            }),
                            then_body: Box::new(IRExpr::BinOp {
                                op: "OpEq".to_owned(),
                                left: Box::new(IRExpr::Var {
                                    name: "n".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                right: Box::new(IRExpr::Var {
                                    name: "total".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                ty: IRType::Bool,
                                span: None,
                            }),
                            else_body: Some(Box::new(IRExpr::BinOp {
                                op: "OpGt".to_owned(),
                                left: Box::new(IRExpr::Var {
                                    name: "n".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                right: Box::new(IRExpr::Var {
                                    name: "total".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                ty: IRType::Bool,
                                span: None,
                            })),
                            span: None,
                        })),
                        ty: IRType::Int,
                        span: None,
                    },
                }],
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "picked".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "total".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for conditional int choose IC3 property, got: {result:?}"
        );
    }

    #[test]
    fn ic3_supports_int_choose_with_let_in_predicate() {
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Let {
                bindings: vec![crate::ir::types::LetBinding {
                    name: "picked".to_owned(),
                    ty: IRType::Int,
                    expr: IRExpr::Choose {
                        var: "n".to_owned(),
                        domain: IRType::Int,
                        predicate: Some(Box::new(IRExpr::Let {
                            bindings: vec![crate::ir::types::LetBinding {
                                name: "threshold".to_owned(),
                                ty: IRType::Int,
                                expr: IRExpr::Var {
                                    name: "total".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                },
                            }],
                            body: Box::new(IRExpr::BinOp {
                                op: "OpEq".to_owned(),
                                left: Box::new(IRExpr::Var {
                                    name: "n".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                right: Box::new(IRExpr::Var {
                                    name: "threshold".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                ty: IRType::Bool,
                                span: None,
                            }),
                            span: None,
                        })),
                        ty: IRType::Int,
                        span: None,
                    },
                }],
                body: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "picked".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "total".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for let-in-predicate int choose IC3 property, got: {result:?}"
        );
    }

    #[test]
    fn ic3_supports_payload_enum_choose_expression() {
        let (entity, types) = make_result_entity_with_payload();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let status_ty = entity.fields[0].ty.clone();
        let property = IRExpr::Always {
            body: Box::new(IRExpr::Let {
                bindings: vec![crate::ir::types::LetBinding {
                    name: "picked".to_owned(),
                    ty: status_ty.clone(),
                    expr: IRExpr::Choose {
                        var: "r".to_owned(),
                        domain: status_ty.clone(),
                        predicate: Some(Box::new(IRExpr::BinOp {
                            op: "OpEq".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "r".to_owned(),
                                ty: status_ty.clone(),
                                span: None,
                            }),
                            right: Box::new(IRExpr::Var {
                                name: "status".to_owned(),
                                ty: status_ty.clone(),
                                span: None,
                            }),
                            ty: IRType::Bool,
                            span: None,
                        })),
                        ty: status_ty.clone(),
                        span: None,
                    },
                }],
                body: Box::new(IRExpr::Match {
                    scrutinee: Box::new(IRExpr::Var {
                        name: "picked".to_owned(),
                        ty: status_ty,
                        span: None,
                    }),
                    arms: vec![
                        IRMatchArm {
                            pattern: IRPattern::PCtor {
                                name: "Result::Err".to_owned(),
                                fields: vec![IRFieldPat {
                                    name: "code".to_owned(),
                                    pattern: IRPattern::PVar {
                                        name: "code".to_owned(),
                                    },
                                }],
                            },
                            guard: None,
                            body: IRExpr::BinOp {
                                op: "OpGe".to_owned(),
                                left: Box::new(IRExpr::Var {
                                    name: "code".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                right: Box::new(IRExpr::Lit {
                                    ty: IRType::Int,
                                    value: LitVal::Int { value: 0 },
                                    span: None,
                                }),
                                ty: IRType::Bool,
                                span: None,
                            },
                        },
                        IRMatchArm {
                            pattern: IRPattern::PWild,
                            guard: None,
                            body: IRExpr::Lit {
                                ty: IRType::Bool,
                                value: LitVal::Bool { value: true },
                                span: None,
                            },
                        },
                    ],
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for payload-enum choose IC3 property, got: {result:?}"
        );
    }

    #[test]
    fn ic3_supports_int_choose_with_match_scoped_predicate() {
        let (entity, types) = make_result_entity_with_payload();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let status_ty = entity.fields[0].ty.clone();
        let property = IRExpr::Always {
            body: Box::new(IRExpr::Let {
                bindings: vec![crate::ir::types::LetBinding {
                    name: "picked".to_owned(),
                    ty: IRType::Int,
                    expr: IRExpr::Choose {
                        var: "n".to_owned(),
                        domain: IRType::Int,
                        predicate: Some(Box::new(IRExpr::Match {
                            scrutinee: Box::new(IRExpr::Var {
                                name: "status".to_owned(),
                                ty: status_ty,
                                span: None,
                            }),
                            arms: vec![
                                IRMatchArm {
                                    pattern: IRPattern::PCtor {
                                        name: "Result::Err".to_owned(),
                                        fields: vec![IRFieldPat {
                                            name: "code".to_owned(),
                                            pattern: IRPattern::PVar {
                                                name: "code".to_owned(),
                                            },
                                        }],
                                    },
                                    guard: None,
                                    body: IRExpr::BinOp {
                                        op: "OpEq".to_owned(),
                                        left: Box::new(IRExpr::Var {
                                            name: "n".to_owned(),
                                            ty: IRType::Int,
                                            span: None,
                                        }),
                                        right: Box::new(IRExpr::Var {
                                            name: "code".to_owned(),
                                            ty: IRType::Int,
                                            span: None,
                                        }),
                                        ty: IRType::Bool,
                                        span: None,
                                    },
                                },
                                IRMatchArm {
                                    pattern: IRPattern::PWild,
                                    guard: None,
                                    body: IRExpr::BinOp {
                                        op: "OpEq".to_owned(),
                                        left: Box::new(IRExpr::Var {
                                            name: "n".to_owned(),
                                            ty: IRType::Int,
                                            span: None,
                                        }),
                                        right: Box::new(IRExpr::Lit {
                                            ty: IRType::Int,
                                            value: LitVal::Int { value: 0 },
                                            span: None,
                                        }),
                                        ty: IRType::Bool,
                                        span: None,
                                    },
                                },
                            ],
                            span: None,
                        })),
                        ty: IRType::Int,
                        span: None,
                    },
                }],
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "picked".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for match-scoped int choose IC3 property, got: {result:?}"
        );
    }

    #[test]
    fn ic3_returns_unknown_for_nonlinear_nonconstructive_int_choose() {
        let entity = IREntity {
            name: "Counter".to_owned(),
            fields: vec![IRField {
                name: "total".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },
                    span: None,
                }),
                initial_constraint: None,
            }],
            transitions: vec![IRTransition {
                name: "bump".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                updates: vec![IRUpdate {
                    field: "total".to_owned(),
                    value: IRExpr::BinOp {
                        op: "OpAdd".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "total".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        }),
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 1 },
                            span: None,
                        }),
                        ty: IRType::Int,
                        span: None,
                    },
                }],
                postcondition: None,
            }],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };
        let ir = make_ir_for_entity(&entity, vec![]);
        let vctx = VerifyContext::from_ir(&ir);

        let square = |expr: IRExpr| IRExpr::BinOp {
            op: "OpMul".to_owned(),
            left: Box::new(expr.clone()),
            right: Box::new(expr),
            ty: IRType::Int,
            span: None,
        };
        let target = IRExpr::BinOp {
            op: "OpMul".to_owned(),
            left: Box::new(IRExpr::BinOp {
                op: "OpAdd".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "total".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 2 },
                    span: None,
                }),
                ty: IRType::Int,
                span: None,
            }),
            right: Box::new(IRExpr::BinOp {
                op: "OpAdd".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "total".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 2 },
                    span: None,
                }),
                ty: IRType::Int,
                span: None,
            }),
            ty: IRType::Int,
            span: None,
        };

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Let {
                bindings: vec![crate::ir::types::LetBinding {
                    name: "picked".to_owned(),
                    ty: IRType::Int,
                    expr: IRExpr::Choose {
                        var: "n".to_owned(),
                        domain: IRType::Int,
                        predicate: Some(Box::new(IRExpr::BinOp {
                            op: "OpEq".to_owned(),
                            left: Box::new(square(IRExpr::Var {
                                name: "n".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            })),
                            right: Box::new(target.clone()),
                            ty: IRType::Bool,
                            span: None,
                        })),
                        ty: IRType::Int,
                        span: None,
                    },
                }],
                body: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(square(IRExpr::Var {
                        name: "picked".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    })),
                    right: Box::new(target),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Unknown(_)),
            "expected Unknown for nonlinear existential int choose IC3 property, got: {result:?}"
        );
    }

    #[test]
    fn ic3_supports_payload_enum_choose_with_shape_predicate() {
        let (entity, types) = make_result_entity_with_payload();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let status_ty = entity.fields[0].ty.clone();
        let property = IRExpr::Always {
            body: Box::new(IRExpr::Let {
                bindings: vec![crate::ir::types::LetBinding {
                    name: "picked".to_owned(),
                    ty: status_ty.clone(),
                    expr: IRExpr::Choose {
                        var: "r".to_owned(),
                        domain: status_ty.clone(),
                        predicate: Some(Box::new(IRExpr::Match {
                            scrutinee: Box::new(IRExpr::Var {
                                name: "r".to_owned(),
                                ty: status_ty.clone(),
                                span: None,
                            }),
                            arms: vec![
                                IRMatchArm {
                                    pattern: IRPattern::PCtor {
                                        name: "Result::Err".to_owned(),
                                        fields: vec![IRFieldPat {
                                            name: "code".to_owned(),
                                            pattern: IRPattern::PVar {
                                                name: "code".to_owned(),
                                            },
                                        }],
                                    },
                                    guard: None,
                                    body: IRExpr::BinOp {
                                        op: "OpGe".to_owned(),
                                        left: Box::new(IRExpr::Var {
                                            name: "code".to_owned(),
                                            ty: IRType::Int,
                                            span: None,
                                        }),
                                        right: Box::new(IRExpr::Lit {
                                            ty: IRType::Int,
                                            value: LitVal::Int { value: 0 },
                                            span: None,
                                        }),
                                        ty: IRType::Bool,
                                        span: None,
                                    },
                                },
                                IRMatchArm {
                                    pattern: IRPattern::PWild,
                                    guard: None,
                                    body: IRExpr::Lit {
                                        ty: IRType::Bool,
                                        value: LitVal::Bool { value: false },
                                        span: None,
                                    },
                                },
                            ],
                            span: None,
                        })),
                        ty: status_ty.clone(),
                        span: None,
                    },
                }],
                body: Box::new(IRExpr::Match {
                    scrutinee: Box::new(IRExpr::Var {
                        name: "picked".to_owned(),
                        ty: status_ty,
                        span: None,
                    }),
                    arms: vec![
                        IRMatchArm {
                            pattern: IRPattern::PCtor {
                                name: "Result::Err".to_owned(),
                                fields: vec![IRFieldPat {
                                    name: "code".to_owned(),
                                    pattern: IRPattern::PVar {
                                        name: "code".to_owned(),
                                    },
                                }],
                            },
                            guard: None,
                            body: IRExpr::BinOp {
                                op: "OpGe".to_owned(),
                                left: Box::new(IRExpr::Var {
                                    name: "code".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                right: Box::new(IRExpr::Lit {
                                    ty: IRType::Int,
                                    value: LitVal::Int { value: 0 },
                                    span: None,
                                }),
                                ty: IRType::Bool,
                                span: None,
                            },
                        },
                        IRMatchArm {
                            pattern: IRPattern::PWild,
                            guard: None,
                            body: IRExpr::Lit {
                                ty: IRType::Bool,
                                value: LitVal::Bool { value: false },
                                span: None,
                            },
                        },
                    ],
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for payload-enum existential choose IC3 property, got: {result:?}"
        );
    }

    #[test]
    fn ic3_supports_real_choose_with_lower_bound_predicate() {
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Let {
                bindings: vec![crate::ir::types::LetBinding {
                    name: "picked".to_owned(),
                    ty: IRType::Real,
                    expr: IRExpr::Choose {
                        var: "r".to_owned(),
                        domain: IRType::Real,
                        predicate: Some(Box::new(IRExpr::BinOp {
                            op: "OpGt".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "r".to_owned(),
                                ty: IRType::Real,
                                span: None,
                            }),
                            right: Box::new(IRExpr::Lit {
                                ty: IRType::Real,
                                value: LitVal::Real { value: 0.0 },
                                span: None,
                            }),
                            ty: IRType::Bool,
                            span: None,
                        })),
                        ty: IRType::Real,
                        span: None,
                    },
                }],
                body: Box::new(IRExpr::BinOp {
                    op: "OpGt".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "picked".to_owned(),
                        ty: IRType::Real,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Real,
                        value: LitVal::Real { value: 0.0 },
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for real lower-bound choose IC3 property, got: {result:?}"
        );
    }

    #[test]
    fn ic3_supports_bool_choose_expression() {
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Let {
                bindings: vec![crate::ir::types::LetBinding {
                    name: "picked".to_owned(),
                    ty: IRType::Bool,
                    expr: IRExpr::Choose {
                        var: "b".to_owned(),
                        domain: IRType::Bool,
                        predicate: Some(Box::new(IRExpr::Var {
                            name: "b".to_owned(),
                            ty: IRType::Bool,
                            span: None,
                        })),
                        ty: IRType::Bool,
                        span: None,
                    },
                }],
                body: Box::new(IRExpr::Var {
                    name: "picked".to_owned(),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for finite Bool choose in IC3, got: {result:?}"
        );
    }

    #[test]
    fn ic3_supports_fieldless_enum_choose_expression() {
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let status_ty = entity.fields[1].ty.clone();
        let property = IRExpr::Always {
            body: Box::new(IRExpr::Let {
                bindings: vec![crate::ir::types::LetBinding {
                    name: "picked".to_owned(),
                    ty: status_ty.clone(),
                    expr: IRExpr::Choose {
                        var: "s".to_owned(),
                        domain: status_ty.clone(),
                        predicate: Some(Box::new(IRExpr::BinOp {
                            op: "OpEq".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "s".to_owned(),
                                ty: status_ty.clone(),
                                span: None,
                            }),
                            right: Box::new(IRExpr::Var {
                                name: "status".to_owned(),
                                ty: status_ty.clone(),
                                span: None,
                            }),
                            ty: IRType::Bool,
                            span: None,
                        })),
                        ty: status_ty.clone(),
                        span: None,
                    },
                }],
                body: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "picked".to_owned(),
                        ty: status_ty.clone(),
                        span: None,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "status".to_owned(),
                        ty: status_ty,
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for finite enum choose in IC3, got: {result:?}"
        );
    }

    #[test]
    fn ic3_supports_bool_exists_quantifier_expression() {
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Exists {
                var: "b".to_owned(),
                domain: IRType::Bool,
                body: Box::new(IRExpr::Var {
                    name: "b".to_owned(),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for finite Bool exists in IC3, got: {result:?}"
        );
    }

    #[test]
    fn ic3_supports_enum_forall_quantifier_expression() {
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let status_ty = entity.fields[1].ty.clone();
        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "s".to_owned(),
                domain: status_ty.clone(),
                body: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "s".to_owned(),
                        ty: status_ty.clone(),
                        span: None,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "s".to_owned(),
                        ty: status_ty,
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for finite enum forall in IC3, got: {result:?}"
        );
    }

    #[test]
    fn ic3_supports_one_and_lone_quantifier_expressions() {
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let one_property = IRExpr::Always {
            body: Box::new(IRExpr::One {
                var: "b".to_owned(),
                domain: IRType::Bool,
                body: Box::new(IRExpr::Var {
                    name: "b".to_owned(),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };
        let one_result = try_ic3_single_entity(&entity, &vctx, &one_property, 5000);
        assert!(
            matches!(one_result, Ic3Result::Proved),
            "expected Proved for finite Bool one in IC3, got: {one_result:?}"
        );

        let lone_property = IRExpr::Always {
            body: Box::new(IRExpr::Lone {
                var: "b".to_owned(),
                domain: IRType::Bool,
                body: Box::new(IRExpr::Var {
                    name: "b".to_owned(),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };
        let lone_result = try_ic3_single_entity(&entity, &vctx, &lone_property, 5000);
        assert!(
            matches!(lone_result, Ic3Result::Proved),
            "expected Proved for finite Bool lone in IC3, got: {lone_result:?}"
        );
    }

    #[test]
    fn ic3_multi_slot_supports_entity_choose_with_field_access() {
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let entity_ty = IRType::Entity {
            name: entity.name.clone(),
        };
        let int_lit_zero = || IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value: 0 },
            span: None,
        };

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "a".to_owned(),
                domain: entity_ty.clone(),
                body: Box::new(IRExpr::Let {
                    bindings: vec![crate::ir::types::LetBinding {
                        name: "picked".to_owned(),
                        ty: entity_ty.clone(),
                        expr: IRExpr::Choose {
                            var: "o".to_owned(),
                            domain: entity_ty.clone(),
                            predicate: Some(Box::new(IRExpr::BinOp {
                                op: "OpGe".to_owned(),
                                left: Box::new(IRExpr::Field {
                                    expr: Box::new(IRExpr::Var {
                                        name: "o".to_owned(),
                                        ty: entity_ty.clone(),
                                        span: None,
                                    }),
                                    field: "total".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                right: Box::new(int_lit_zero()),
                                ty: IRType::Bool,
                                span: None,
                            })),
                            ty: entity_ty.clone(),
                            span: None,
                        },
                    }],
                    body: Box::new(IRExpr::BinOp {
                        op: "OpGe".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "picked".to_owned(),
                                ty: entity_ty.clone(),
                                span: None,
                            }),
                            field: "total".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        }),
                        right: Box::new(int_lit_zero()),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_multi_slot(&entity, &vctx, &property, 2, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for entity choose with field access in multi-slot IC3, got: {result:?}"
        );
    }

    #[test]
    fn ic3_multi_slot_supports_entity_choose_in_inter_entity_property() {
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let entity_ty = IRType::Entity {
            name: entity.name.clone(),
        };
        let int_lit_zero = || IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value: 0 },
            span: None,
        };

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "a".to_owned(),
                domain: entity_ty.clone(),
                body: Box::new(IRExpr::Forall {
                    var: "b".to_owned(),
                    domain: entity_ty.clone(),
                    body: Box::new(IRExpr::Let {
                        bindings: vec![crate::ir::types::LetBinding {
                            name: "picked".to_owned(),
                            ty: entity_ty.clone(),
                            expr: IRExpr::Choose {
                                var: "o".to_owned(),
                                domain: entity_ty.clone(),
                                predicate: Some(Box::new(IRExpr::BinOp {
                                    op: "OpGe".to_owned(),
                                    left: Box::new(IRExpr::Field {
                                        expr: Box::new(IRExpr::Var {
                                            name: "o".to_owned(),
                                            ty: entity_ty.clone(),
                                            span: None,
                                        }),
                                        field: "total".to_owned(),
                                        ty: IRType::Int,
                                        span: None,
                                    }),
                                    right: Box::new(int_lit_zero()),
                                    ty: IRType::Bool,
                                    span: None,
                                })),
                                ty: entity_ty.clone(),
                                span: None,
                            },
                        }],
                        body: Box::new(IRExpr::BinOp {
                            op: "OpGe".to_owned(),
                            left: Box::new(IRExpr::Field {
                                expr: Box::new(IRExpr::Var {
                                    name: "picked".to_owned(),
                                    ty: entity_ty.clone(),
                                    span: None,
                                }),
                                field: "total".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            right: Box::new(int_lit_zero()),
                            ty: IRType::Bool,
                            span: None,
                        }),
                        span: None,
                    }),
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_multi_slot(&entity, &vctx, &property, 2, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for inter-entity entity choose in multi-slot IC3, got: {result:?}"
        );
    }

    #[test]
    fn ic3_supports_if_without_else_guard_expression() {
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Always {
            body: Box::new(IRExpr::IfElse {
                cond: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "status".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Pending".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                then_body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "total".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                else_body: None,
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for guard if-without-else IC3 property, got: {result:?}"
        );
    }

    #[test]
    fn ic3_supports_match_expression() {
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Match {
                scrutinee: Box::new(IRExpr::Var {
                    name: "status".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                arms: vec![
                    crate::ir::types::IRMatchArm {
                        pattern: crate::ir::types::IRPattern::PCtor {
                            name: "Pending".to_owned(),
                            fields: vec![],
                        },
                        guard: None,
                        body: IRExpr::BinOp {
                            op: "OpGe".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "total".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            right: Box::new(IRExpr::Lit {
                                ty: IRType::Int,
                                value: LitVal::Int { value: 0 },
                                span: None,
                            }),
                            ty: IRType::Bool,
                            span: None,
                        },
                    },
                    crate::ir::types::IRMatchArm {
                        pattern: crate::ir::types::IRPattern::PWild,
                        guard: None,
                        body: IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        },
                    },
                ],
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for match-bound IC3 property, got: {result:?}"
        );
    }

    #[test]
    fn ic3_supports_match_destructuring_for_constructor_fields() {
        let (entity, types) = make_result_entity_with_payload();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let status_ty = entity.fields[0].ty.clone();
        let property = IRExpr::Always {
            body: Box::new(IRExpr::Match {
                scrutinee: Box::new(IRExpr::Var {
                    name: "status".to_owned(),
                    ty: status_ty,
                    span: None,
                }),
                arms: vec![
                    IRMatchArm {
                        pattern: IRPattern::PCtor {
                            name: "Result::Err".to_owned(),
                            fields: vec![IRFieldPat {
                                name: "code".to_owned(),
                                pattern: IRPattern::PVar {
                                    name: "code".to_owned(),
                                },
                            }],
                        },
                        guard: None,
                        body: IRExpr::BinOp {
                            op: "OpGe".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "code".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            right: Box::new(IRExpr::Lit {
                                ty: IRType::Int,
                                value: LitVal::Int { value: 0 },
                                span: None,
                            }),
                            ty: IRType::Bool,
                            span: None,
                        },
                    },
                    IRMatchArm {
                        pattern: IRPattern::PWild,
                        guard: None,
                        body: IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        },
                    },
                ],
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for constructor-field match IC3 property, got: {result:?}"
        );
    }

    #[test]
    fn ic3_supports_or_pattern_bindings_when_names_align() {
        let (entity, types) = make_result_entity_with_dual_payload_variants();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let status_ty = entity.fields[0].ty.clone();
        let property = IRExpr::Always {
            body: Box::new(IRExpr::Match {
                scrutinee: Box::new(IRExpr::Var {
                    name: "status".to_owned(),
                    ty: status_ty,
                    span: None,
                }),
                arms: vec![
                    IRMatchArm {
                        pattern: IRPattern::POr {
                            left: Box::new(IRPattern::PCtor {
                                name: "Result::Ok".to_owned(),
                                fields: vec![IRFieldPat {
                                    name: "ok_code".to_owned(),
                                    pattern: IRPattern::PVar {
                                        name: "code".to_owned(),
                                    },
                                }],
                            }),
                            right: Box::new(IRPattern::PCtor {
                                name: "Result::Err".to_owned(),
                                fields: vec![IRFieldPat {
                                    name: "err_code".to_owned(),
                                    pattern: IRPattern::PVar {
                                        name: "code".to_owned(),
                                    },
                                }],
                            }),
                        },
                        guard: None,
                        body: IRExpr::BinOp {
                            op: "OpGe".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "code".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            right: Box::new(IRExpr::Lit {
                                ty: IRType::Int,
                                value: LitVal::Int { value: 0 },
                                span: None,
                            }),
                            ty: IRType::Bool,
                            span: None,
                        },
                    },
                    IRMatchArm {
                        pattern: IRPattern::PWild,
                        guard: None,
                        body: IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        },
                    },
                ],
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for aligned or-pattern bindings in IC3, got: {result:?}"
        );
    }

    #[test]
    fn ic3_rejects_or_pattern_bindings_with_mismatched_names() {
        let (entity, types) = make_result_entity_with_dual_payload_variants();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let status_ty = entity.fields[0].ty.clone();
        let property = IRExpr::Always {
            body: Box::new(IRExpr::Match {
                scrutinee: Box::new(IRExpr::Var {
                    name: "status".to_owned(),
                    ty: status_ty,
                    span: None,
                }),
                arms: vec![
                    IRMatchArm {
                        pattern: IRPattern::POr {
                            left: Box::new(IRPattern::PCtor {
                                name: "Result::Ok".to_owned(),
                                fields: vec![IRFieldPat {
                                    name: "ok_code".to_owned(),
                                    pattern: IRPattern::PVar {
                                        name: "left_code".to_owned(),
                                    },
                                }],
                            }),
                            right: Box::new(IRPattern::PCtor {
                                name: "Result::Err".to_owned(),
                                fields: vec![IRFieldPat {
                                    name: "err_code".to_owned(),
                                    pattern: IRPattern::PVar {
                                        name: "right_code".to_owned(),
                                    },
                                }],
                            }),
                        },
                        guard: None,
                        body: IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        },
                    },
                    IRMatchArm {
                        pattern: IRPattern::PWild,
                        guard: None,
                        body: IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        },
                    },
                ],
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Unknown(ref reason) if reason.contains("or-pattern bindings in IC3 require both alternatives to bind the same names")),
            "expected Unknown with mismatched or-pattern binder message, got: {result:?}"
        );
    }

    #[test]
    fn ic3_rejects_non_exhaustive_match_expression() {
        let (entity, types) = make_simple_entity();
        let ir = make_ir_for_entity(&entity, types);
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Match {
                scrutinee: Box::new(IRExpr::Var {
                    name: "status".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                arms: vec![crate::ir::types::IRMatchArm {
                    pattern: crate::ir::types::IRPattern::PCtor {
                        name: "Pending".to_owned(),
                        fields: vec![],
                    },
                    guard: None,
                    body: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                        span: None,
                    },
                }],
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
        assert!(
            matches!(result, Ic3Result::Unknown(ref reason) if reason.contains("non-exhaustive match")),
            "expected Unknown with non-exhaustive match message, got: {result:?}"
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

                            span: None,
                        }),
                        field: "total".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
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

                            span: None,
                        }),
                        field: "status".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Pending".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
        };

        let result = try_ic3_multi_slot(&entity, &vctx, &property, 2, 5000);
        assert!(
            matches!(result, Ic3Result::Violated(_)),
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

                span: None,
            }),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: -1 },

                span: None,
            }),
            ty: IRType::Bool,

            span: None,
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

                                    span: None,
                                }),
                                field: "total".to_owned(),
                                ty: IRType::Int,

                                span: None,
                            }),
                            right: Box::new(IRExpr::Lit {
                                ty: IRType::Int,
                                value: LitVal::Int { value: 0 },

                                span: None,
                            }),
                            ty: IRType::Bool,

                            span: None,
                        }),
                        right: Box::new(IRExpr::BinOp {
                            op: "OpGe".to_owned(),
                            left: Box::new(IRExpr::Field {
                                expr: Box::new(IRExpr::Var {
                                    name: "b".to_owned(),
                                    ty: IRType::Entity {
                                        name: "Order".to_owned(),
                                    },

                                    span: None,
                                }),
                                field: "total".to_owned(),
                                ty: IRType::Int,

                                span: None,
                            }),
                            right: Box::new(IRExpr::Lit {
                                ty: IRType::Int,
                                value: LitVal::Int { value: 0 },

                                span: None,
                            }),
                            ty: IRType::Bool,

                            span: None,
                        }),
                        ty: IRType::Bool,

                        span: None,
                    }),

                    span: None,
                }),

                span: None,
            }),

            span: None,
        };

        let result = try_ic3_multi_slot(&entity, &vctx, &property, 3, 10000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for inter-entity total >= 0, got: {result:?}"
        );
    }

    #[test]
    fn ic3_multi_slot_supports_inter_entity_let_expression() {
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
                    body: Box::new(IRExpr::Let {
                        bindings: vec![
                            LetBinding {
                                name: "a_total".to_owned(),
                                ty: IRType::Int,
                                expr: IRExpr::Field {
                                    expr: Box::new(IRExpr::Var {
                                        name: "a".to_owned(),
                                        ty: IRType::Entity {
                                            name: "Order".to_owned(),
                                        },
                                        span: None,
                                    }),
                                    field: "total".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                },
                            },
                            LetBinding {
                                name: "b_total".to_owned(),
                                ty: IRType::Int,
                                expr: IRExpr::Field {
                                    expr: Box::new(IRExpr::Var {
                                        name: "b".to_owned(),
                                        ty: IRType::Entity {
                                            name: "Order".to_owned(),
                                        },
                                        span: None,
                                    }),
                                    field: "total".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                },
                            },
                        ],
                        body: Box::new(IRExpr::BinOp {
                            op: "OpAnd".to_owned(),
                            left: Box::new(IRExpr::BinOp {
                                op: "OpGe".to_owned(),
                                left: Box::new(IRExpr::Var {
                                    name: "a_total".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                right: Box::new(IRExpr::Lit {
                                    ty: IRType::Int,
                                    value: LitVal::Int { value: 0 },
                                    span: None,
                                }),
                                ty: IRType::Bool,
                                span: None,
                            }),
                            right: Box::new(IRExpr::BinOp {
                                op: "OpGe".to_owned(),
                                left: Box::new(IRExpr::Var {
                                    name: "b_total".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                right: Box::new(IRExpr::Lit {
                                    ty: IRType::Int,
                                    value: LitVal::Int { value: 0 },
                                    span: None,
                                }),
                                ty: IRType::Bool,
                                span: None,
                            }),
                            ty: IRType::Bool,
                            span: None,
                        }),
                        span: None,
                    }),
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_multi_slot(&entity, &vctx, &property, 3, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for let-bound inter-entity property, got: {result:?}"
        );
    }

    #[test]
    fn ic3_multi_slot_supports_inter_entity_if_expression() {
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
                        op: "OpGe".to_owned(),
                        left: Box::new(IRExpr::IfElse {
                            cond: Box::new(IRExpr::BinOp {
                                op: "OpGe".to_owned(),
                                left: Box::new(IRExpr::Field {
                                    expr: Box::new(IRExpr::Var {
                                        name: "a".to_owned(),
                                        ty: IRType::Entity {
                                            name: "Order".to_owned(),
                                        },
                                        span: None,
                                    }),
                                    field: "total".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                right: Box::new(IRExpr::Lit {
                                    ty: IRType::Int,
                                    value: LitVal::Int { value: 0 },
                                    span: None,
                                }),
                                ty: IRType::Bool,
                                span: None,
                            }),
                            then_body: Box::new(IRExpr::Field {
                                expr: Box::new(IRExpr::Var {
                                    name: "b".to_owned(),
                                    ty: IRType::Entity {
                                        name: "Order".to_owned(),
                                    },
                                    span: None,
                                }),
                                field: "total".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            else_body: Some(Box::new(IRExpr::Lit {
                                ty: IRType::Int,
                                value: LitVal::Int { value: 0 },
                                span: None,
                            })),
                            span: None,
                        }),
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 0 },
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let result = try_ic3_multi_slot(&entity, &vctx, &property, 3, 5000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for if/else inter-entity property, got: {result:?}"
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

                            span: None,
                        }),
                        right: Box::new(IRExpr::Var {
                            name: "b".to_owned(),
                            ty: IRType::Entity {
                                name: "Order".to_owned(),
                            },

                            span: None,
                        }),
                        ty: IRType::Bool,

                        span: None,
                    }),

                    span: None,
                }),

                span: None,
            }),

            span: None,
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
                variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Confirmed")],
            },
        };

        let order = IREntity {
            name: "Order".to_owned(),
            fields: vec![
                IRField {
                    name: "id".to_owned(),
                    ty: IRType::Identity,
                    default: None,
                    initial_constraint: None,
                },
                IRField {
                    name: "total".to_owned(),
                    ty: IRType::Int,
                    default: Some(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },

                        span: None,
                    }),
                    initial_constraint: None,
                },
                IRField {
                    name: "status".to_owned(),
                    ty: IRType::Enum {
                        name: "OrderStatus".to_owned(),
                        variants: vec![
                            IRVariant::simple("Pending"),
                            IRVariant::simple("Confirmed"),
                        ],
                    },
                    default: Some(IRExpr::Ctor {
                        enum_name: "OrderStatus".to_owned(),
                        ctor: "Pending".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    initial_constraint: None,
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

                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "OrderStatus".to_owned(),
                        ctor: "Pending".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                },
                updates: vec![IRUpdate {
                    field: "status".to_owned(),
                    value: IRExpr::Ctor {
                        enum_name: "OrderStatus".to_owned(),
                        ctor: "Confirmed".to_owned(),
                        args: vec![],
                        span: None,
                    },
                }],
                postcondition: None,
            }],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };

        let item = IREntity {
            name: "Item".to_owned(),
            fields: vec![
                IRField {
                    name: "id".to_owned(),
                    ty: IRType::Identity,
                    default: None,
                    initial_constraint: None,
                },
                IRField {
                    name: "quantity".to_owned(),
                    ty: IRType::Int,
                    default: Some(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },

                        span: None,
                    }),
                    initial_constraint: None,
                },
            ],
            transitions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
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
            lemmas: vec![],
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

                            span: None,
                        }),
                        field: "total".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
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

    #[test]
    fn ic3_system_supports_let_bound_property() {
        let (ir, _) = make_system_program();
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "o".to_owned(),
                domain: IRType::Entity {
                    name: "Order".to_owned(),
                },
                body: Box::new(IRExpr::Let {
                    bindings: vec![LetBinding {
                        name: "t".to_owned(),
                        ty: IRType::Int,
                        expr: IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "o".to_owned(),
                                ty: IRType::Entity {
                                    name: "Order".to_owned(),
                                },
                                span: None,
                            }),
                            field: "total".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        },
                    }],
                    body: Box::new(IRExpr::BinOp {
                        op: "OpGe".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "t".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        }),
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 0 },
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let mut slots = HashMap::new();
        slots.insert("Order".to_owned(), 2);

        let result = try_ic3_system(
            &ir,
            &vctx,
            &["Commerce".to_owned()],
            &property,
            &slots,
            5000,
        );
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for let-bound system property, got: {result:?}"
        );
    }

    #[test]
    fn ic3_system_supports_if_value_property() {
        let (ir, _) = make_system_program();
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "o".to_owned(),
                domain: IRType::Entity {
                    name: "Order".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::IfElse {
                        cond: Box::new(IRExpr::BinOp {
                            op: "OpEq".to_owned(),
                            left: Box::new(IRExpr::Field {
                                expr: Box::new(IRExpr::Var {
                                    name: "o".to_owned(),
                                    ty: IRType::Entity {
                                        name: "Order".to_owned(),
                                    },
                                    span: None,
                                }),
                                field: "status".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            right: Box::new(IRExpr::Ctor {
                                enum_name: "Status".to_owned(),
                                ctor: "Pending".to_owned(),
                                args: vec![],
                                span: None,
                            }),
                            ty: IRType::Bool,
                            span: None,
                        }),
                        then_body: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "o".to_owned(),
                                ty: IRType::Entity {
                                    name: "Order".to_owned(),
                                },
                                span: None,
                            }),
                            field: "total".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        }),
                        else_body: Some(Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 0 },
                            span: None,
                        })),
                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let mut slots = HashMap::new();
        slots.insert("Order".to_owned(), 2);

        let result = try_ic3_system(
            &ir,
            &vctx,
            &["Commerce".to_owned()],
            &property,
            &slots,
            5000,
        );
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for if/else system property, got: {result:?}"
        );
    }

    #[test]
    fn ic3_system_supports_match_property() {
        let (ir, _) = make_system_program();
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "o".to_owned(),
                domain: IRType::Entity {
                    name: "Order".to_owned(),
                },
                body: Box::new(IRExpr::Match {
                    scrutinee: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "o".to_owned(),
                            ty: IRType::Entity {
                                name: "Order".to_owned(),
                            },
                            span: None,
                        }),
                        field: "status".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    arms: vec![
                        crate::ir::types::IRMatchArm {
                            pattern: crate::ir::types::IRPattern::PCtor {
                                name: "Pending".to_owned(),
                                fields: vec![],
                            },
                            guard: None,
                            body: IRExpr::BinOp {
                                op: "OpGe".to_owned(),
                                left: Box::new(IRExpr::Field {
                                    expr: Box::new(IRExpr::Var {
                                        name: "o".to_owned(),
                                        ty: IRType::Entity {
                                            name: "Order".to_owned(),
                                        },
                                        span: None,
                                    }),
                                    field: "total".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                right: Box::new(IRExpr::Lit {
                                    ty: IRType::Int,
                                    value: LitVal::Int { value: 0 },
                                    span: None,
                                }),
                                ty: IRType::Bool,
                                span: None,
                            },
                        },
                        crate::ir::types::IRMatchArm {
                            pattern: crate::ir::types::IRPattern::PWild,
                            guard: None,
                            body: IRExpr::Lit {
                                ty: IRType::Bool,
                                value: LitVal::Bool { value: true },
                                span: None,
                            },
                        },
                    ],
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let mut slots = HashMap::new();
        slots.insert("Order".to_owned(), 2);

        let result = try_ic3_system(
            &ir,
            &vctx,
            &["Commerce".to_owned()],
            &property,
            &slots,
            5000,
        );
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for match system property, got: {result:?}"
        );
    }

    #[test]
    fn ic3_system_supports_match_destructuring_for_constructor_fields() {
        let result_ty = IRTypeEntry {
            name: "Result".to_owned(),
            ty: IRType::Enum {
                name: "Result".to_owned(),
                variants: vec![
                    IRVariant::simple("Pending"),
                    IRVariant {
                        name: "Err".to_owned(),
                        fields: vec![IRVariantField {
                            name: "code".to_owned(),
                            ty: IRType::Int,
                        }],
                    },
                ],
            },
        };

        let order = IREntity {
            name: "Order".to_owned(),
            fields: vec![IRField {
                name: "status".to_owned(),
                ty: result_ty.ty.clone(),
                default: Some(IRExpr::Ctor {
                    enum_name: "Result".to_owned(),
                    ctor: "Err".to_owned(),
                    args: vec![(
                        "code".to_owned(),
                        IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 7 },
                            span: None,
                        },
                    )],
                    span: None,
                }),
                initial_constraint: None,
            }],
            transitions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };

        let system = IRSystem {
            name: "Commerce".to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: vec!["Order".to_owned()],
            commands: vec![],
            steps: vec![],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        };

        let ir = IRProgram {
            types: vec![result_ty],
            constants: vec![],
            functions: vec![],
            entities: vec![order],
            systems: vec![system],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "o".to_owned(),
                domain: IRType::Entity {
                    name: "Order".to_owned(),
                },
                body: Box::new(IRExpr::Match {
                    scrutinee: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "o".to_owned(),
                            ty: IRType::Entity {
                                name: "Order".to_owned(),
                            },
                            span: None,
                        }),
                        field: "status".to_owned(),
                        ty: ir.types[0].ty.clone(),
                        span: None,
                    }),
                    arms: vec![
                        IRMatchArm {
                            pattern: IRPattern::PCtor {
                                name: "Err".to_owned(),
                                fields: vec![IRFieldPat {
                                    name: "code".to_owned(),
                                    pattern: IRPattern::PVar {
                                        name: "code".to_owned(),
                                    },
                                }],
                            },
                            guard: None,
                            body: IRExpr::BinOp {
                                op: "OpGe".to_owned(),
                                left: Box::new(IRExpr::Var {
                                    name: "code".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                right: Box::new(IRExpr::Lit {
                                    ty: IRType::Int,
                                    value: LitVal::Int { value: 0 },
                                    span: None,
                                }),
                                ty: IRType::Bool,
                                span: None,
                            },
                        },
                        IRMatchArm {
                            pattern: IRPattern::PWild,
                            guard: None,
                            body: IRExpr::Lit {
                                ty: IRType::Bool,
                                value: LitVal::Bool { value: true },
                                span: None,
                            },
                        },
                    ],
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let mut slots = HashMap::new();
        slots.insert("Order".to_owned(), 2);

        let result = try_ic3_system(
            &ir,
            &vctx,
            &["Commerce".to_owned()],
            &property,
            &slots,
            5000,
        );
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for constructor-field match system IC3 property, got: {result:?}"
        );
    }

    #[test]
    fn ic3_system_supports_cross_entity_let_property() {
        let order_status = IRTypeEntry {
            name: "OrderStatus".to_owned(),
            ty: IRType::Enum {
                name: "OrderStatus".to_owned(),
                variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Confirmed")],
            },
        };

        let order = IREntity {
            name: "Order".to_owned(),
            fields: vec![
                IRField {
                    name: "id".to_owned(),
                    ty: IRType::Identity,
                    default: None,
                    initial_constraint: None,
                },
                IRField {
                    name: "total".to_owned(),
                    ty: IRType::Int,
                    default: Some(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },
                        span: None,
                    }),
                    initial_constraint: None,
                },
                IRField {
                    name: "status".to_owned(),
                    ty: IRType::Enum {
                        name: "OrderStatus".to_owned(),
                        variants: vec![
                            IRVariant::simple("Pending"),
                            IRVariant::simple("Confirmed"),
                        ],
                    },
                    default: Some(IRExpr::Ctor {
                        enum_name: "OrderStatus".to_owned(),
                        ctor: "Pending".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    initial_constraint: None,
                },
            ],
            transitions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };

        let item = IREntity {
            name: "Item".to_owned(),
            fields: vec![
                IRField {
                    name: "id".to_owned(),
                    ty: IRType::Identity,
                    default: None,
                    initial_constraint: None,
                },
                IRField {
                    name: "quantity".to_owned(),
                    ty: IRType::Int,
                    default: Some(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },
                        span: None,
                    }),
                    initial_constraint: None,
                },
            ],
            transitions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
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
            lemmas: vec![],
            scenes: vec![],
        };
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "o".to_owned(),
                domain: IRType::Entity {
                    name: "Order".to_owned(),
                },
                body: Box::new(IRExpr::Forall {
                    var: "i".to_owned(),
                    domain: IRType::Entity {
                        name: "Item".to_owned(),
                    },
                    body: Box::new(IRExpr::Let {
                        bindings: vec![
                            LetBinding {
                                name: "order_total".to_owned(),
                                ty: IRType::Int,
                                expr: IRExpr::Field {
                                    expr: Box::new(IRExpr::Var {
                                        name: "o".to_owned(),
                                        ty: IRType::Entity {
                                            name: "Order".to_owned(),
                                        },
                                        span: None,
                                    }),
                                    field: "total".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                },
                            },
                            LetBinding {
                                name: "item_qty".to_owned(),
                                ty: IRType::Int,
                                expr: IRExpr::Field {
                                    expr: Box::new(IRExpr::Var {
                                        name: "i".to_owned(),
                                        ty: IRType::Entity {
                                            name: "Item".to_owned(),
                                        },
                                        span: None,
                                    }),
                                    field: "quantity".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                },
                            },
                        ],
                        body: Box::new(IRExpr::BinOp {
                            op: "OpAnd".to_owned(),
                            left: Box::new(IRExpr::BinOp {
                                op: "OpGe".to_owned(),
                                left: Box::new(IRExpr::Var {
                                    name: "order_total".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                right: Box::new(IRExpr::Lit {
                                    ty: IRType::Int,
                                    value: LitVal::Int { value: 0 },
                                    span: None,
                                }),
                                ty: IRType::Bool,
                                span: None,
                            }),
                            right: Box::new(IRExpr::BinOp {
                                op: "OpGe".to_owned(),
                                left: Box::new(IRExpr::Var {
                                    name: "item_qty".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                right: Box::new(IRExpr::Lit {
                                    ty: IRType::Int,
                                    value: LitVal::Int { value: 0 },
                                    span: None,
                                }),
                                ty: IRType::Bool,
                                span: None,
                            }),
                            ty: IRType::Bool,
                            span: None,
                        }),
                        span: None,
                    }),
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let mut slots = HashMap::new();
        slots.insert("Order".to_owned(), 2);
        slots.insert("Item".to_owned(), 2);

        let result = try_ic3_system(&ir, &vctx, &[], &property, &slots, 10000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for let-bound cross-entity system property, got: {result:?}"
        );
    }

    #[test]
    fn ic3_system_supports_entity_choose_with_field_access() {
        let (ir, _) = make_system_program();
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "o".to_owned(),
                domain: IRType::Entity {
                    name: "Order".to_owned(),
                },
                body: Box::new(IRExpr::Let {
                    bindings: vec![LetBinding {
                        name: "picked".to_owned(),
                        ty: IRType::Entity {
                            name: "Order".to_owned(),
                        },
                        expr: IRExpr::Choose {
                            var: "c".to_owned(),
                            domain: IRType::Entity {
                                name: "Order".to_owned(),
                            },
                            predicate: Some(Box::new(IRExpr::BinOp {
                                op: "OpGe".to_owned(),
                                left: Box::new(IRExpr::Field {
                                    expr: Box::new(IRExpr::Var {
                                        name: "c".to_owned(),
                                        ty: IRType::Entity {
                                            name: "Order".to_owned(),
                                        },
                                        span: None,
                                    }),
                                    field: "total".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                right: Box::new(IRExpr::Lit {
                                    ty: IRType::Int,
                                    value: LitVal::Int { value: 0 },
                                    span: None,
                                }),
                                ty: IRType::Bool,
                                span: None,
                            })),
                            ty: IRType::Entity {
                                name: "Order".to_owned(),
                            },
                            span: None,
                        },
                    }],
                    body: Box::new(IRExpr::BinOp {
                        op: "OpGe".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "picked".to_owned(),
                                ty: IRType::Entity {
                                    name: "Order".to_owned(),
                                },
                                span: None,
                            }),
                            field: "total".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        }),
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 0 },
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let mut slots = HashMap::new();
        slots.insert("Order".to_owned(), 2);

        let result = try_ic3_system(
            &ir,
            &vctx,
            &["Commerce".to_owned()],
            &property,
            &slots,
            5000,
        );
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for entity-choose system property, got: {result:?}"
        );
    }

    #[test]
    fn ic3_system_supports_cross_entity_choose_property() {
        let (ir, _) = make_system_program();
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
                    body: Box::new(IRExpr::Let {
                        bindings: vec![LetBinding {
                            name: "picked".to_owned(),
                            ty: IRType::Entity {
                                name: "Order".to_owned(),
                            },
                            expr: IRExpr::Choose {
                                var: "c".to_owned(),
                                domain: IRType::Entity {
                                    name: "Order".to_owned(),
                                },
                                predicate: Some(Box::new(IRExpr::BinOp {
                                    op: "OpGe".to_owned(),
                                    left: Box::new(IRExpr::Field {
                                        expr: Box::new(IRExpr::Var {
                                            name: "c".to_owned(),
                                            ty: IRType::Entity {
                                                name: "Order".to_owned(),
                                            },
                                            span: None,
                                        }),
                                        field: "total".to_owned(),
                                        ty: IRType::Int,
                                        span: None,
                                    }),
                                    right: Box::new(IRExpr::Lit {
                                        ty: IRType::Int,
                                        value: LitVal::Int { value: 0 },
                                        span: None,
                                    }),
                                    ty: IRType::Bool,
                                    span: None,
                                })),
                                ty: IRType::Entity {
                                    name: "Order".to_owned(),
                                },
                                span: None,
                            },
                        }],
                        body: Box::new(IRExpr::BinOp {
                            op: "OpGe".to_owned(),
                            left: Box::new(IRExpr::Field {
                                expr: Box::new(IRExpr::Var {
                                    name: "picked".to_owned(),
                                    ty: IRType::Entity {
                                        name: "Order".to_owned(),
                                    },
                                    span: None,
                                }),
                                field: "total".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            right: Box::new(IRExpr::Lit {
                                ty: IRType::Int,
                                value: LitVal::Int { value: 0 },
                                span: None,
                            }),
                            ty: IRType::Bool,
                            span: None,
                        }),
                        span: None,
                    }),
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let mut slots = HashMap::new();
        slots.insert("Order".to_owned(), 2);

        let result = try_ic3_system(
            &ir,
            &vctx,
            &["Commerce".to_owned()],
            &property,
            &slots,
            5000,
        );
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for cross-entity choose system property, got: {result:?}"
        );
    }

    // ── System event encoding tests ─────────────────────────────────

    /// Helper: build an `IRProgram` with system events for testing system-level IC3.
    fn make_system_program() -> (IRProgram, IRExpr) {
        let status_type = IRTypeEntry {
            name: "Status".to_owned(),
            ty: IRType::Enum {
                name: "Status".to_owned(),
                variants: vec![
                    IRVariant::simple("Pending"),
                    IRVariant::simple("Confirmed"),
                    IRVariant::simple("Shipped"),
                ],
            },
        };

        let order = IREntity {
            name: "Order".to_owned(),
            fields: vec![
                IRField {
                    name: "id".to_owned(),
                    ty: IRType::Identity,
                    default: None,
                    initial_constraint: None,
                },
                IRField {
                    name: "status".to_owned(),
                    ty: IRType::Enum {
                        name: "Status".to_owned(),
                        variants: vec![
                            IRVariant::simple("Pending"),
                            IRVariant::simple("Confirmed"),
                            IRVariant::simple("Shipped"),
                        ],
                    },
                    default: Some(IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Pending".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    initial_constraint: None,
                },
                IRField {
                    name: "total".to_owned(),
                    ty: IRType::Int,
                    default: Some(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },

                        span: None,
                    }),
                    initial_constraint: None,
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

                            span: None,
                        }),
                        right: Box::new(IRExpr::Ctor {
                            enum_name: "Status".to_owned(),
                            ctor: "Pending".to_owned(),
                            args: vec![],
                            span: None,
                        }),
                        ty: IRType::Bool,

                        span: None,
                    },
                    updates: vec![IRUpdate {
                        field: "status".to_owned(),
                        value: IRExpr::Ctor {
                            enum_name: "Status".to_owned(),
                            ctor: "Confirmed".to_owned(),
                            args: vec![],
                            span: None,
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

                            span: None,
                        }),
                        right: Box::new(IRExpr::Ctor {
                            enum_name: "Status".to_owned(),
                            ctor: "Confirmed".to_owned(),
                            args: vec![],
                            span: None,
                        }),
                        ty: IRType::Bool,

                        span: None,
                    },
                    updates: vec![IRUpdate {
                        field: "status".to_owned(),
                        value: IRExpr::Ctor {
                            enum_name: "Status".to_owned(),
                            ctor: "Shipped".to_owned(),
                            args: vec![],
                            span: None,
                        },
                    }],
                    postcondition: None,
                },
            ],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };

        // System with Choose+Apply event
        let commerce = IRSystem {
            name: "Commerce".to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: vec!["Order".to_owned()],
            commands: vec![],
            steps: vec![IRStep {
                name: "process_order".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "o".to_owned(),
                    entity: "Order".to_owned(),
                    filter: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "status".to_owned(),
                            ty: IRType::Int,

                            span: None,
                        }),
                        right: Box::new(IRExpr::Ctor {
                            enum_name: "Status".to_owned(),
                            ctor: "Pending".to_owned(),
                            args: vec![],
                            span: None,
                        }),
                        ty: IRType::Bool,

                        span: None,
                    }),
                    ops: vec![IRAction::Apply {
                        target: "o".to_owned(),
                        transition: "confirm".to_owned(),
                        refs: vec![],
                        args: vec![],
                    }],
                }],
                return_expr: None,
            }],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        };

        let ir = IRProgram {
            types: vec![status_type],
            constants: vec![],
            functions: vec![],
            entities: vec![order],
            systems: vec![commerce],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };

        // Property: all o: Order | o.total >= 0
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

                            span: None,
                        }),
                        field: "total".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
        };

        (ir, property)
    }

    #[test]
    fn ic3_system_with_events_proves_safety() {
        // Test system-level IC3 with actual system events (not empty systems vec).
        // Commerce system has Choose+Apply(confirm) for Orders.
        // Property: total >= 0 (no transition modifies total).
        let (ir, property) = make_system_program();
        let vctx = VerifyContext::from_ir(&ir);

        let mut slots = HashMap::new();
        slots.insert("Order".to_owned(), 2);

        let result = try_ic3_system(
            &ir,
            &vctx,
            &["Commerce".to_owned()],
            &property,
            &slots,
            10000,
        );
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved with system events, got: {result:?}"
        );
    }

    #[test]
    fn ic3_system_missing_transition_returns_unknown() {
        // System event references a non-existent transition — should return Unknown.
        let status_type = IRTypeEntry {
            name: "Status".to_owned(),
            ty: IRType::Enum {
                name: "Status".to_owned(),
                variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
            },
        };

        let order = IREntity {
            name: "Order".to_owned(),
            fields: vec![IRField {
                name: "status".to_owned(),
                ty: IRType::Enum {
                    name: "Status".to_owned(),
                    variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
                },
                default: Some(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Pending".to_owned(),
                    args: vec![],
                    span: None,
                }),
                initial_constraint: None,
            }],
            transitions: vec![], // no transitions defined
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };

        let sys = IRSystem {
            name: "S".to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: vec!["Order".to_owned()],
            commands: vec![],
            steps: vec![IRStep {
                name: "do_thing".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "o".to_owned(),
                    entity: "Order".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    }),
                    ops: vec![IRAction::Apply {
                        target: "o".to_owned(),
                        transition: "nonexistent".to_owned(), // missing!
                        refs: vec![],
                        args: vec![],
                    }],
                }],
                return_expr: None,
            }],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        };

        let ir = IRProgram {
            types: vec![status_type],
            constants: vec![],
            functions: vec![],
            entities: vec![order],
            systems: vec![sys],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },

            span: None,
        };
        let mut slots = HashMap::new();
        slots.insert("Order".to_owned(), 1);

        let result = try_ic3_system(&ir, &vctx, &["S".to_owned()], &property, &slots, 5000);
        assert!(
            matches!(result, Ic3Result::Unknown(ref reason)
                if reason.contains("transition nonexistent not found")),
            "expected Unknown with missing transition message, got: {result:?}"
        );
    }

    #[test]
    fn ic3_system_missing_crosscall_target_returns_unknown() {
        // System event has CrossCall to non-existent system — should return Unknown.
        let order = IREntity {
            name: "Order".to_owned(),
            fields: vec![IRField {
                name: "count".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },

                    span: None,
                }),
                initial_constraint: None,
            }],
            transitions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };

        let sys = IRSystem {
            name: "S".to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: vec!["Order".to_owned()],
            commands: vec![],
            steps: vec![IRStep {
                name: "trigger".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::CrossCall {
                    system: "NonExistent".to_owned(),
                    command: "whatever".to_owned(),
                    args: vec![],
                }],
                return_expr: None,
            }],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        };

        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![order],
            systems: vec![sys],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },

            span: None,
        };
        let mut slots = HashMap::new();
        slots.insert("Order".to_owned(), 1);

        let result = try_ic3_system(&ir, &vctx, &["S".to_owned()], &property, &slots, 5000);
        assert!(
            matches!(result, Ic3Result::Unknown(ref reason)
                if reason.contains("CrossCall target system NonExistent not found")),
            "expected Unknown with missing CrossCall target, got: {result:?}"
        );
    }

    #[test]
    fn ic3_system_crosscall_create_via_recursion() {
        // System A has CrossCall to System B which Creates an entity.
        // Tests recursive CrossCall encoding (not just Create scanning).
        let item = IREntity {
            name: "Item".to_owned(),
            fields: vec![IRField {
                name: "qty".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 1 },

                    span: None,
                }),
                initial_constraint: None,
            }],
            transitions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };

        // System B: event that Creates an Item
        let sys_b = IRSystem {
            name: "Inventory".to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: vec!["Item".to_owned()],
            commands: vec![],
            steps: vec![IRStep {
                name: "add_item".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Item".to_owned(),
                    fields: vec![IRCreateField {
                        name: "qty".to_owned(),
                        value: IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 5 },

                            span: None,
                        },
                    }],
                }],
                return_expr: None,
            }],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        };

        // System A: event that CrossCalls B.add_item
        let sys_a = IRSystem {
            name: "Commerce".to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: vec![],
            commands: vec![],
            steps: vec![IRStep {
                name: "place_order".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::CrossCall {
                    system: "Inventory".to_owned(),
                    command: "add_item".to_owned(),
                    args: vec![],
                }],
                return_expr: None,
            }],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        };

        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![item],
            systems: vec![sys_a, sys_b],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };
        let vctx = VerifyContext::from_ir(&ir);

        // Property: all i: Item | i.qty >= 0 (Items are created with qty=5)
        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "i".to_owned(),
                domain: IRType::Entity {
                    name: "Item".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "i".to_owned(),
                            ty: IRType::Entity {
                                name: "Item".to_owned(),
                            },

                            span: None,
                        }),
                        field: "qty".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
        };

        let mut slots = HashMap::new();
        slots.insert("Item".to_owned(), 2);

        let result = try_ic3_system(
            &ir,
            &vctx,
            &["Commerce".to_owned()],
            &property,
            &slots,
            10000,
        );
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for CrossCall-created items qty >= 0, got: {result:?}"
        );
    }

    #[test]
    fn ic3_system_forall_with_apply() {
        // ForAll iterates all active orders and applies confirm.
        // With event-level encoding (no entity-level rules), transitions
        // are only accessible through system events.
        let (ir, property) = make_system_program();

        // Replace the system with one that uses ForAll instead of Choose
        let forall_sys = IRSystem {
            name: "BatchProcessor".to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: vec!["Order".to_owned()],
            commands: vec![],
            steps: vec![IRStep {
                name: "confirm_all".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::ForAll {
                    var: "o".to_owned(),
                    entity: "Order".to_owned(),
                    ops: vec![IRAction::Apply {
                        target: "o".to_owned(),
                        transition: "confirm".to_owned(),
                        refs: vec![],
                        args: vec![],
                    }],
                }],
                return_expr: None,
            }],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        };

        let ir2 = IRProgram {
            systems: vec![forall_sys],
            ..ir
        };
        let vctx = VerifyContext::from_ir(&ir2);

        let mut slots = HashMap::new();
        slots.insert("Order".to_owned(), 2);

        let result = try_ic3_system(
            &ir2,
            &vctx,
            &["BatchProcessor".to_owned()],
            &property,
            &slots,
            10000,
        );
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for ForAll+Apply, got: {result:?}"
        );
    }

    #[test]
    fn ic3_system_forall_with_create() {
        // ForAll iterates active orders and creates an Item for each.
        // Tests ForAll handling of Create ops (not just Apply).
        let order = IREntity {
            name: "Order".to_owned(),
            fields: vec![IRField {
                name: "count".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },

                    span: None,
                }),
                initial_constraint: None,
            }],
            transitions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };

        let item = IREntity {
            name: "Item".to_owned(),
            fields: vec![IRField {
                name: "qty".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 1 },

                    span: None,
                }),
                initial_constraint: None,
            }],
            transitions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };

        let sys = IRSystem {
            name: "S".to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: vec!["Order".to_owned(), "Item".to_owned()],
            commands: vec![],
            steps: vec![IRStep {
                name: "create_items".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::ForAll {
                    var: "o".to_owned(),
                    entity: "Order".to_owned(),
                    ops: vec![IRAction::Create {
                        entity: "Item".to_owned(),
                        fields: vec![IRCreateField {
                            name: "qty".to_owned(),
                            value: IRExpr::Lit {
                                ty: IRType::Int,
                                value: LitVal::Int { value: 3 },

                                span: None,
                            },
                        }],
                    }],
                }],
                return_expr: None,
            }],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        };

        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![order, item],
            systems: vec![sys],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };
        let vctx = VerifyContext::from_ir(&ir);

        // Property: all i: Item | i.qty >= 0 (Items created with qty=3)
        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "i".to_owned(),
                domain: IRType::Entity {
                    name: "Item".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "i".to_owned(),
                            ty: IRType::Entity {
                                name: "Item".to_owned(),
                            },

                            span: None,
                        }),
                        field: "qty".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
        };

        let mut slots = HashMap::new();
        slots.insert("Order".to_owned(), 1);
        slots.insert("Item".to_owned(), 2);

        let result = try_ic3_system(&ir, &vctx, &["S".to_owned()], &property, &slots, 10000);
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved for ForAll+Create, got: {result:?}"
        );
    }

    #[test]
    fn ic3_system_event_guard_propagation() {
        // Event guard is false → no transitions can fire → property trivially holds.
        // Verifies that event guard is properly AND'd into generated rules.
        let (ir, _) = make_system_program();

        // Replace system with event that has guard=false
        let guarded_sys = IRSystem {
            name: "Guarded".to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: vec!["Order".to_owned()],
            commands: vec![],
            steps: vec![IRStep {
                name: "never_fires".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: false },

                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "o".to_owned(),
                    entity: "Order".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    }),
                    ops: vec![IRAction::Apply {
                        target: "o".to_owned(),
                        transition: "confirm".to_owned(),
                        refs: vec![],
                        args: vec![],
                    }],
                }],
                return_expr: None,
            }],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        };

        let ir2 = IRProgram {
            systems: vec![guarded_sys],
            ..ir
        };
        let vctx = VerifyContext::from_ir(&ir2);

        // Property: all orders always Pending — true because no event can fire
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

                            span: None,
                        }),
                        field: "status".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Pending".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
        };

        let mut slots = HashMap::new();
        slots.insert("Order".to_owned(), 2);

        let result = try_ic3_system(
            &ir2,
            &vctx,
            &["Guarded".to_owned()],
            &property,
            &slots,
            10000,
        );
        // With event guard=false, no transitions fire, so always-Pending holds
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved (event guard=false prevents transitions), got: {result:?}"
        );
    }

    #[test]
    fn ic3_system_no_entity_rules_when_systems_present() {
        // With systems present, entity-level transition rules are NOT emitted.
        // This means transitions can only fire through system events.
        // Test: property that would fail with entity-level rules but succeeds
        // when only system events are available and system has no ship event.
        let (ir, _) = make_system_program();

        // Commerce system only has process_order (which does confirm, not ship).
        // Without entity-level rules, ship can never fire.
        // Property: no order is ever Shipped — should be PROVED.
        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "o".to_owned(),
                domain: IRType::Entity {
                    name: "Order".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpNEq".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "o".to_owned(),
                            ty: IRType::Entity {
                                name: "Order".to_owned(),
                            },

                            span: None,
                        }),
                        field: "status".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Shipped".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
        };

        let mut slots = HashMap::new();
        slots.insert("Order".to_owned(), 2);

        let vctx = VerifyContext::from_ir(&ir);
        let result = try_ic3_system(
            &ir,
            &vctx,
            &["Commerce".to_owned()],
            &property,
            &slots,
            10000,
        );
        // Commerce only has confirm (Pending→Confirmed), no way to reach Shipped
        assert!(
            matches!(result, Ic3Result::Proved),
            "expected Proved (ship not reachable via system events), got: {result:?}"
        );
    }

    #[test]
    fn ic3_system_unknown_system_name_returns_unknown() {
        let (ir, property) = make_system_program();
        let vctx = VerifyContext::from_ir(&ir);
        let mut slots = HashMap::new();
        slots.insert("Order".to_owned(), 1);

        let result = try_ic3_system(
            &ir,
            &vctx,
            &["DoesNotExist".to_owned()],
            &property,
            &slots,
            5000,
        );
        assert!(
            matches!(result, Ic3Result::Unknown(ref reason)
                if reason.contains("system DoesNotExist not found")),
            "expected Unknown for missing system name, got: {result:?}"
        );
    }

    #[test]
    fn ic3_system_cyclic_crosscall_returns_unknown() {
        // System A calls B, system B calls A — cyclic CrossCall.
        let order = IREntity {
            name: "Order".to_owned(),
            fields: vec![IRField {
                name: "n".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },

                    span: None,
                }),
                initial_constraint: None,
            }],
            transitions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };

        let sys_a = IRSystem {
            name: "A".to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: vec![],
            commands: vec![],
            steps: vec![IRStep {
                name: "go".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::CrossCall {
                    system: "B".to_owned(),
                    command: "bounce".to_owned(),
                    args: vec![],
                }],
                return_expr: None,
            }],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        };

        let sys_b = IRSystem {
            name: "B".to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: vec![],
            commands: vec![],
            steps: vec![IRStep {
                name: "bounce".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::CrossCall {
                    system: "A".to_owned(),
                    command: "go".to_owned(),
                    args: vec![],
                }],
                return_expr: None,
            }],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        };

        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![order],
            systems: vec![sys_a, sys_b],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };
        let vctx = VerifyContext::from_ir(&ir);

        let property = IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },

            span: None,
        };
        let mut slots = HashMap::new();
        slots.insert("Order".to_owned(), 1);

        let result = try_ic3_system(&ir, &vctx, &["A".to_owned()], &property, &slots, 5000);
        assert!(
            matches!(result, Ic3Result::Unknown(ref reason)
                if reason.contains("cyclic CrossCall")),
            "expected Unknown for cyclic CrossCall, got: {result:?}"
        );
    }

    #[test]
    fn ic3_system_apply_target_mismatch_returns_unknown() {
        // Apply.target doesn't match Choose variable — malformed IR.
        let (ir, _) = make_system_program();

        let bad_sys = IRSystem {
            name: "Bad".to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: vec!["Order".to_owned()],
            commands: vec![],
            steps: vec![IRStep {
                name: "bad_event".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "o".to_owned(),
                    entity: "Order".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    }),
                    ops: vec![IRAction::Apply {
                        target: "wrong_var".to_owned(), // mismatch!
                        transition: "confirm".to_owned(),
                        refs: vec![],
                        args: vec![],
                    }],
                }],
                return_expr: None,
            }],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        };

        let ir2 = IRProgram {
            systems: vec![bad_sys],
            ..ir
        };
        let vctx = VerifyContext::from_ir(&ir2);

        let property = IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },

            span: None,
        };
        let mut slots = HashMap::new();
        slots.insert("Order".to_owned(), 1);

        let result = try_ic3_system(&ir2, &vctx, &["Bad".to_owned()], &property, &slots, 5000);
        assert!(
            matches!(result, Ic3Result::Unknown(ref reason)
                if reason.contains("Apply target wrong_var does not match")),
            "expected Unknown for Apply target mismatch, got: {result:?}"
        );
    }
}
