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
    let fp = Fixedpoint::new();

    let mut params = Params::new();
    params.set_symbol("engine", "spacer");
    params.set_bool("xform.slice", false); // preserve column order for trace extraction
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
        SatResult::Sat => {
            // Build column layout: fields + active flag (matches CHC State relation)
            let mut columns: Vec<TraceColumn> = entity
                .fields
                .iter()
                .enumerate()
                .map(|(fi, f)| (entity.name.clone(), f.name.clone(), fi))
                .collect();
            columns.push((entity.name.clone(), "active".to_owned(), usize::MAX));
            let trace = extract_trace_from_answer(&fp, &columns);
            Ic3Result::Violated(trace)
        }
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
    params.set_bool("xform.slice", false);
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
        SatResult::Sat => {
            let columns = build_multi_slot_columns(entity, n_slots);
            let trace = extract_trace_from_answer(&fp, &columns);
            Ic3Result::Violated(trace)
        }
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
    params.set_bool("xform.slice", false); // preserve column order for trace extraction
    if timeout_ms > 0 {
        #[allow(clippy::cast_possible_truncation)]
        params.set_u32("timeout", timeout_ms.min(u64::from(u32::MAX)) as u32);
    }
    fp.set_params(&params);

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
        SatResult::Sat => {
            let columns = build_system_columns(&relevant_entities, slots_per_entity);
            let trace = extract_trace_from_answer(&fp, &columns);
            Ic3Result::Violated(trace)
        }
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

/// Column metadata for trace extraction: `(entity_name, field_name, field_index)`.
/// The last column per slot is the `active` flag `(entity_name, "active", usize::MAX)`.
type TraceColumn = (String, String, usize);

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

/// Extract a counterexample trace from Z3 Spacer's answer after a SAT result.
///
/// Parses ground `(State v1 v2 ... vN)` applications from the derivation tree.
/// Returns empty vec if answer is unavailable or unparseable.
fn extract_trace_from_answer(fp: &Fixedpoint, columns: &[TraceColumn]) -> Vec<Ic3TraceStep> {
    let Some(answer) = fp.get_answer() else {
        return Vec::new();
    };

    let answer_str = format!("{answer}");
    parse_state_snapshots(&answer_str, columns)
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

/// Extract ground `(State v1 v2 ... vN)` applications from the derivation tree.
///
/// Walks the s-expression tree depth-first (children before parent). Spacer's
/// derivation nests earlier states deeper: the initial state is the innermost
/// `(asserted (State ...))`, each `hyper-res` step produces the next state as
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

        // Check if this is (State v1 v2 ... vN) with exactly n_cols ground args
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
    } // if systems.is_empty()

    // ── System event rules ──────────────────────────────────────────
    // Encode system events as composite CHC rules via recursive action tree walk.
    // Choose/ForAll/Apply/Create/CrossCall are all handled with full context
    // guard propagation. CrossCall targets are recursively encoded (not just Creates).
    for system in systems {
        for event in &system.events {
            // Fresh visited set per event tree — cycles within one event's
            // CrossCall graph are detected, but the same event can appear
            // in different top-level event trees.
            let mut visited = HashSet::new();
            visited.insert((system.name.clone(), event.name.clone()));
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
                event: target_evt,
                ..
            } => {
                let sys = all_systems
                    .iter()
                    .find(|s| s.name == *target_sys)
                    .ok_or_else(|| format!("CrossCall target system {target_sys} not found"))?;
                let evt = sys
                    .events
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

                let result = encode_event_chc(
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
                event: target_evt,
                ..
            } => {
                let sys = all_systems
                    .iter()
                    .find(|s| s.name == *target_sys)
                    .ok_or_else(|| format!("CrossCall target system {target_sys} not found"))?;
                let evt = sys
                    .events
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
                let result = encode_event_chc(
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
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            let m = expr_to_smt_sys(map, entity, vctx, ent_name, slot)?;
            let k = expr_to_smt_sys(key, entity, vctx, ent_name, slot)?;
            let v = expr_to_smt_sys(value, entity, vctx, ent_name, slot)?;
            Ok(format!("(store {m} {k} {v})"))
        }
        IRExpr::Index { map, key, .. } => {
            let m = expr_to_smt_sys(map, entity, vctx, ent_name, slot)?;
            let k = expr_to_smt_sys(key, entity, vctx, ent_name, slot)?;
            Ok(format!("(select {m} {k})"))
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
        IRExpr::Always { body, .. } => negate_property_smt_multi(body, entity, vctx, n_slots),
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
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            let m = expr_to_smt_slot(map, entity, vctx, slot)?;
            let k = expr_to_smt_slot(key, entity, vctx, slot)?;
            let v = expr_to_smt_slot(value, entity, vctx, slot)?;
            Ok(format!("(store {m} {k} {v})"))
        }
        IRExpr::Index { map, key, .. } => {
            let m = expr_to_smt_slot(map, entity, vctx, slot)?;
            let k = expr_to_smt_slot(key, entity, vctx, slot)?;
            Ok(format!("(select {m} {k})"))
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
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            let m = expr_to_smt(map, entity, vctx)?;
            let k = expr_to_smt(key, entity, vctx)?;
            let v = expr_to_smt(value, entity, vctx)?;
            Ok(format!("(store {m} {k} {v})"))
        }
        IRExpr::Index { map, key, .. } => {
            let m = expr_to_smt(map, entity, vctx)?;
            let k = expr_to_smt(key, entity, vctx)?;
            Ok(format!("(select {m} {k})"))
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
        IRExpr::Always { body, .. } => negate_property_smt(body, entity, vctx),
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
                    ty: IRType::Id,
                    default: None,
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
                },
                IRField {
                    name: "total".to_owned(),
                    ty: IRType::Int,
                    default: Some(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },

                        span: None,
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

                    span: None,
                },
            }],
            body: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            }),

            span: None,
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
                    ty: IRType::Id,
                    default: None,
                },
                IRField {
                    name: "total".to_owned(),
                    ty: IRType::Int,
                    default: Some(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },

                        span: None,
                    }),
                },
                IRField {
                    name: "status".to_owned(),
                    ty: IRType::Enum {
                        name: "OrderStatus".to_owned(),
                        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Confirmed")],
                    },
                    default: Some(IRExpr::Ctor {
                        enum_name: "OrderStatus".to_owned(),
                        ctor: "Pending".to_owned(),
                        args: vec![],
                        span: None,
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

                        span: None,
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

    // ── System event encoding tests ─────────────────────────────────

    /// Helper: build an IRProgram with system events for testing system-level IC3.
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
                    ty: IRType::Id,
                    default: None,
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
                },
                IRField {
                    name: "total".to_owned(),
                    ty: IRType::Int,
                    default: Some(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },

                        span: None,
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
        };

        // System with Choose+Apply event
        let commerce = IRSystem {
            name: "Commerce".to_owned(),
            entities: vec!["Order".to_owned()],
            events: vec![IREvent {
                name: "process_order".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                postcondition: None,
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
            }],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
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
            }],
            transitions: vec![], // no transitions defined
        };

        let sys = IRSystem {
            name: "S".to_owned(),
            entities: vec!["Order".to_owned()],
            events: vec![IREvent {
                name: "do_thing".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                postcondition: None,
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
            }],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
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
            }],
            transitions: vec![],
        };

        let sys = IRSystem {
            name: "S".to_owned(),
            entities: vec!["Order".to_owned()],
            events: vec![IREvent {
                name: "trigger".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                postcondition: None,
                body: vec![IRAction::CrossCall {
                    system: "NonExistent".to_owned(),
                    event: "whatever".to_owned(),
                    args: vec![],
                }],
            }],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
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
            }],
            transitions: vec![],
        };

        // System B: event that Creates an Item
        let sys_b = IRSystem {
            name: "Inventory".to_owned(),
            entities: vec!["Item".to_owned()],
            events: vec![IREvent {
                name: "add_item".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                postcondition: None,
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
            }],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
        };

        // System A: event that CrossCalls B.add_item
        let sys_a = IRSystem {
            name: "Commerce".to_owned(),
            entities: vec![],
            events: vec![IREvent {
                name: "place_order".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                postcondition: None,
                body: vec![IRAction::CrossCall {
                    system: "Inventory".to_owned(),
                    event: "add_item".to_owned(),
                    args: vec![],
                }],
            }],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
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
            entities: vec!["Order".to_owned()],
            events: vec![IREvent {
                name: "confirm_all".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                postcondition: None,
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
            }],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
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
            }],
            transitions: vec![],
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
            }],
            transitions: vec![],
        };

        let sys = IRSystem {
            name: "S".to_owned(),
            entities: vec!["Order".to_owned(), "Item".to_owned()],
            events: vec![IREvent {
                name: "create_items".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                postcondition: None,
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
            }],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
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
            entities: vec!["Order".to_owned()],
            events: vec![IREvent {
                name: "never_fires".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: false },

                    span: None,
                },
                postcondition: None,
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
            }],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
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
            }],
            transitions: vec![],
        };

        let sys_a = IRSystem {
            name: "A".to_owned(),
            entities: vec![],
            events: vec![IREvent {
                name: "go".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                postcondition: None,
                body: vec![IRAction::CrossCall {
                    system: "B".to_owned(),
                    event: "bounce".to_owned(),
                    args: vec![],
                }],
            }],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
        };

        let sys_b = IRSystem {
            name: "B".to_owned(),
            entities: vec![],
            events: vec![IREvent {
                name: "bounce".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                postcondition: None,
                body: vec![IRAction::CrossCall {
                    system: "A".to_owned(),
                    event: "go".to_owned(),
                    args: vec![],
                }],
            }],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
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
            entities: vec!["Order".to_owned()],
            events: vec![IREvent {
                name: "bad_event".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                postcondition: None,
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
            }],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
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
