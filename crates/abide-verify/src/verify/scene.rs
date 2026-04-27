//! Scene block verification.
//!
//! Scene blocks are existential witnesses: given initial bindings and a sequence
//! of events, the solver checks whether a satisfying trace exists. The main
//! entry point is `check_scene_block`, which builds the SMT encoding and
//! dispatches to Z3.

use std::collections::{HashMap, HashSet};
use std::time::Instant;

use super::smt::{self, AbideSolver, Bool, Int, SatResult};

use crate::ir::types::{IRExpr, IRProgram, IRScene, IRSceneEvent, IRStep};

use super::context::VerifyContext;
use super::defenv;
use super::harness::{
    self, create_slot_pool_with_systems, domain_constraints, encode_step_with_params,
};
use super::property::{encode_prop_expr_with_ctx, encode_prop_value_with_ctx, PropertyCtx};
use super::scope::{
    collect_crosscall_systems, collect_saw_systems_expr, validate_crosscall_arities,
    VerifyStoreRange,
};
use super::smt::SmtValue;
use super::walkers::{
    collect_event_body_entities, collect_field_refs_in_expr, elapsed_ms,
    find_unsupported_scene_expr, scan_event_creates,
};
use super::{
    clamp_timeout_to_deadline, collect_var_refs_in_expr, expand_through_defs, expr_span,
    find_unsupported_in_actions,
};
use super::{VerificationResult, VerifyConfig};

// ── Scene helpers ────────────────────────────────────────────────────

/// Collect event indices referenced by ^| (exclusive choice) in ordering expressions.
pub(super) fn collect_xor_event_indices(
    expr: &IRExpr,
    var_to_idx: &HashMap<&str, usize>,
    xor_events: &mut HashSet<usize>,
) {
    if let IRExpr::BinOp {
        op, left, right, ..
    } = expr
    {
        if op == "OpXor" {
            for var in collect_ordering_leaf_vars(left) {
                if let Some(&idx) = var_to_idx.get(var) {
                    xor_events.insert(idx);
                }
            }
            for var in collect_ordering_leaf_vars(right) {
                if let Some(&idx) = var_to_idx.get(var) {
                    xor_events.insert(idx);
                }
            }
        }
        collect_xor_event_indices(left, var_to_idx, xor_events);
        collect_xor_event_indices(right, var_to_idx, xor_events);
    }
}

/// Collect event-level same-step pairs from `OpSameStep` ordering expressions.
pub(super) fn collect_same_step_event_pairs(
    ordering: &[IRExpr],
    var_to_idx: &HashMap<&str, usize>,
    pairs: &mut Vec<(usize, usize)>,
) {
    for expr in ordering {
        collect_same_step_event_pairs_expr(expr, var_to_idx, pairs);
    }
}

pub(super) fn collect_same_step_event_pairs_expr(
    expr: &IRExpr,
    var_to_idx: &HashMap<&str, usize>,
    pairs: &mut Vec<(usize, usize)>,
) {
    if let IRExpr::BinOp {
        op, left, right, ..
    } = expr
    {
        if op == "OpSameStep" {
            let left_vars: Vec<usize> = collect_ordering_leaf_vars(left)
                .into_iter()
                .filter_map(|v| var_to_idx.get(v).copied())
                .collect();
            let right_vars: Vec<usize> = collect_ordering_leaf_vars(right)
                .into_iter()
                .filter_map(|v| var_to_idx.get(v).copied())
                .collect();
            for &a in &left_vars {
                for &b in &right_vars {
                    pairs.push((a, b));
                }
            }
        }
        collect_same_step_event_pairs_expr(left, var_to_idx, pairs);
        collect_same_step_event_pairs_expr(right, var_to_idx, pairs);
    }
}

/// Encode scene ordering constraints with multi-instance support.
/// For multi-instance events, `a -> b` means last instance of a < first instance of b.
/// `^|` asserts XOR on fire variables.
pub(super) fn encode_scene_ordering_v2(
    expr: &IRExpr,
    var_to_idx: &HashMap<&str, usize>,
    event_instance_ranges: &[std::ops::Range<usize>],
    instances: &[FiringInst],
    solver: &AbideSolver,
    scene_name: &str,
) -> Result<(), String> {
    match expr {
        IRExpr::BinOp {
            op, left, right, ..
        } => match op.as_str() {
            "OpSeq" => {
                // a -> b: last instance of a < first instance of b
                if let (Some(l_event), Some(r_event)) = (
                    last_ordering_var(left, var_to_idx),
                    first_ordering_var(right, var_to_idx),
                ) {
                    let l_range = &event_instance_ranges[l_event];
                    let r_range = &event_instance_ranges[r_event];
                    if !l_range.is_empty() && !r_range.is_empty() {
                        let last_l = &instances[l_range.end - 1].step_var;
                        let first_r = &instances[r_range.start].step_var;
                        solver.assert(smt::int_lt(last_l, first_r));
                    }
                } else {
                    let left_vars = collect_ordering_leaf_vars(left);
                    let right_vars = collect_ordering_leaf_vars(right);
                    if left_vars.is_empty() || right_vars.is_empty() {
                        return Err(format!(
                            "scene '{scene_name}': ordering expression references \
                             unknown event variable in `assume` block"
                        ));
                    }
                }
                encode_scene_ordering_v2(
                    left,
                    var_to_idx,
                    event_instance_ranges,
                    instances,
                    solver,
                    scene_name,
                )?;
                encode_scene_ordering_v2(
                    right,
                    var_to_idx,
                    event_instance_ranges,
                    instances,
                    solver,
                    scene_name,
                )?;
            }
            "OpSameStep" => {
                // Handled by same-step grouping. Recurse for nested.
                encode_scene_ordering_v2(
                    left,
                    var_to_idx,
                    event_instance_ranges,
                    instances,
                    solver,
                    scene_name,
                )?;
                encode_scene_ordering_v2(
                    right,
                    var_to_idx,
                    event_instance_ranges,
                    instances,
                    solver,
                    scene_name,
                )?;
            }
            "OpConc" | "OpUnord" => {
                encode_scene_ordering_v2(
                    left,
                    var_to_idx,
                    event_instance_ranges,
                    instances,
                    solver,
                    scene_name,
                )?;
                encode_scene_ordering_v2(
                    right,
                    var_to_idx,
                    event_instance_ranges,
                    instances,
                    solver,
                    scene_name,
                )?;
            }
            "OpXor" => {
                // ^|: exactly one of the two events fires.
                // XOR on their fires variables.
                let left_events: Vec<usize> = collect_ordering_leaf_vars(left)
                    .into_iter()
                    .filter_map(|v| var_to_idx.get(v).copied())
                    .collect();
                let right_events: Vec<usize> = collect_ordering_leaf_vars(right)
                    .into_iter()
                    .filter_map(|v| var_to_idx.get(v).copied())
                    .collect();
                for &a in &left_events {
                    for &b in &right_events {
                        let a_range = &event_instance_ranges[a];
                        let b_range = &event_instance_ranges[b];
                        if a_range.is_empty() {
                            return Err(crate::messages::scene_xor_multi_instance(
                                scene_name,
                                &event_var_names_from_idx(a, var_to_idx),
                                0,
                            ));
                        }
                        if b_range.is_empty() {
                            return Err(crate::messages::scene_xor_multi_instance(
                                scene_name,
                                &event_var_names_from_idx(b, var_to_idx),
                                0,
                            ));
                        }
                        // ^| requires single-instance events (exactly 1 firing slot).
                        // Multi-instance ({some}, {N>1}) would allow extra firings
                        // that bypass the XOR constraint.
                        if a_range.len() > 1 {
                            return Err(crate::messages::scene_xor_multi_instance(
                                scene_name,
                                &event_var_names_from_idx(a, var_to_idx),
                                a_range.len(),
                            ));
                        }
                        if b_range.len() > 1 {
                            return Err(crate::messages::scene_xor_multi_instance(
                                scene_name,
                                &event_var_names_from_idx(b, var_to_idx),
                                b_range.len(),
                            ));
                        }
                        let a_fires =
                            instances[a_range.start].fires_var.as_ref().ok_or_else(|| {
                                crate::messages::scene_xor_no_fire_tracking(
                                    scene_name,
                                    &event_var_names_from_idx(a, var_to_idx),
                                )
                            })?;
                        let b_fires =
                            instances[b_range.start].fires_var.as_ref().ok_or_else(|| {
                                crate::messages::scene_xor_no_fire_tracking(
                                    scene_name,
                                    &event_var_names_from_idx(b, var_to_idx),
                                )
                            })?;
                        // XOR: (a_fires ∧ ¬b_fires) ∨ (¬a_fires ∧ b_fires)
                        let xor = smt::bool_or(&[
                            &smt::bool_and(&[a_fires, &smt::bool_not(b_fires)]),
                            &smt::bool_and(&[&smt::bool_not(a_fires), b_fires]),
                        ]);
                        solver.assert(&xor);
                    }
                }
                // Recurse for nested
                encode_scene_ordering_v2(
                    left,
                    var_to_idx,
                    event_instance_ranges,
                    instances,
                    solver,
                    scene_name,
                )?;
                encode_scene_ordering_v2(
                    right,
                    var_to_idx,
                    event_instance_ranges,
                    instances,
                    solver,
                    scene_name,
                )?;
            }
            _ => {}
        },
        IRExpr::Var { .. } => {}
        _ => {}
    }
    Ok(())
}

/// Reverse lookup: event index → variable name
pub(super) fn event_var_names_from_idx(idx: usize, var_to_idx: &HashMap<&str, usize>) -> String {
    var_to_idx
        .iter()
        .find(|(_, &i)| i == idx)
        .map_or_else(|| format!("event_{idx}"), |(name, _)| name.to_string())
}

/// A single firing instance in the scene trace.
pub(super) struct FiringInst {
    event_idx: usize,
    #[allow(dead_code)]
    inst_idx: usize,
    step_var: Int,
    fires_var: Option<Bool>,
}

/// Resolved scene event: validated reference to the scene event and its IR.
///
/// NOTE: Scene `when` blocks invoke commands. For multi-clause commands
/// (multiple steps with the same name but different guards), ALL matching
/// steps are stored. Parameter resolution uses the first step (all steps
/// for a command share the same params, validated by collect.rs). Scene
/// execution encodes a disjunction over all steps so the solver explores
/// every clause.
pub(super) struct ResolvedSceneEvent<'a> {
    scene_event: &'a IRSceneEvent,
    steps: Vec<&'a IRStep>,
}

/// Build `override_params` for a scene event at a given step.
#[allow(clippy::too_many_arguments)]
pub(super) fn build_scene_event_params(
    re: &ResolvedSceneEvent<'_>,
    pool: &harness::SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    given_bindings: &HashMap<String, (String, usize)>,
    store_ranges: &HashMap<String, VerifyStoreRange>,
    step: usize,
    _scene_name: &str,
) -> Result<HashMap<String, SmtValue>, String> {
    let mut override_params: HashMap<String, SmtValue> = HashMap::new();
    // Use the first step for param metadata (all steps share the same
    // params — validated by collect.rs).
    let step_ir = re.steps[0];
    for (param, arg) in step_ir.params.iter().zip(re.scene_event.args.iter()) {
        let arg_ctx = PropertyCtx::new().with_store_ranges(store_ranges.clone());
        let arg_ctx = given_bindings
            .iter()
            .fold(arg_ctx, |ctx, (var, (ent, slot))| {
                ctx.with_binding(var, ent, *slot)
            });
        let (val, constraints) = encode_prop_value_with_ctx(pool, vctx, defs, &arg_ctx, arg, step)
            .map_err(|msg| {
                format!(
                    "encoding error in scene event arg for {}::{}: {msg}",
                    re.scene_event.system, re.scene_event.event
                )
            })?;
        if !constraints.is_empty() {
            return Err(format!(
                "scene event args do not yet support choose witness constraints for {}::{}",
                re.scene_event.system, re.scene_event.event
            ));
        }
        override_params.insert(param.name.clone(), val);
    }
    Ok(override_params)
}

/// Collect all event variable names referenced in an ordering expression.
pub(super) fn collect_ordering_leaf_vars(expr: &IRExpr) -> Vec<&str> {
    match expr {
        IRExpr::Var { name, .. } => vec![name.as_str()],
        IRExpr::BinOp { left, right, .. } => {
            let mut vars = collect_ordering_leaf_vars(left);
            vars.extend(collect_ordering_leaf_vars(right));
            vars
        }
        _ => vec![],
    }
}

/// Get the step variable index of the last (rightmost) event in an ordering expr.
/// For `a -> b`, returns index of `b`. For a bare `Var("a")`, returns index of `a`.
pub(super) fn last_ordering_var(expr: &IRExpr, var_to_idx: &HashMap<&str, usize>) -> Option<usize> {
    match expr {
        IRExpr::Var { name, .. } => var_to_idx.get(name.as_str()).copied(),
        IRExpr::BinOp { op, right, .. } if op == "OpSeq" => last_ordering_var(right, var_to_idx),
        IRExpr::BinOp { right, .. } => last_ordering_var(right, var_to_idx),
        _ => None,
    }
}

/// Get the step variable index of the first (leftmost) event in an ordering expr.
/// For `a -> b`, returns index of `a`. For a bare `Var("a")`, returns index of `a`.
pub(super) fn first_ordering_var(
    expr: &IRExpr,
    var_to_idx: &HashMap<&str, usize>,
) -> Option<usize> {
    match expr {
        IRExpr::Var { name, .. } => var_to_idx.get(name.as_str()).copied(),
        IRExpr::BinOp { op, left, .. } if op == "OpSeq" => first_ordering_var(left, var_to_idx),
        IRExpr::BinOp { left, .. } => first_ordering_var(left, var_to_idx),
        _ => None,
    }
}

/// 1. Build scope and pool from scene systems
/// 2. Given: activate one slot per binding, constrain fields at step 0
/// 3. When: encode each event at its step (ordering from assume)
/// 4. Then: assert all then-expressions at the final step
/// 5. SAT → `ScenePass`, UNSAT → `SceneFail`
#[allow(clippy::too_many_lines)]
pub(super) fn check_scene_block(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    scene: &IRScene,
    config: &VerifyConfig,
    deadline: Option<Instant>,
) -> VerificationResult {
    let start = Instant::now();
    let n_events = scene.events.len();

    // Compute bound from cardinalities: total number of firing instances.
    // This must happen before pool/scope creation so they have enough capacity.
    let some_budget = n_events.max(2);
    let bound = {
        let mut total: usize = 0;
        for scene_event in &scene.events {
            total += match &scene_event.cardinality {
                crate::ir::types::Cardinality::Named(c) => match c.as_str() {
                    "one" | "lone" => 1,
                    "no" => 0,
                    "some" => some_budget,
                    _ => 1,
                },
                crate::ir::types::Cardinality::Exact { exactly } => *exactly as usize,
            };
        }
        total.max(1)
    };

    // ── 1. Build scope from scene systems ──────────────────────────
    // Each given binding needs one slot. Each entity type referenced
    // needs at least as many slots as given bindings of that type.
    let mut scope: HashMap<String, usize> = HashMap::new();
    let mut system_names: Vec<String> = scene.systems.clone();

    // Size entities from per-store declarations (SUM for same-entity-type
    // stores so each store gets its own slot range).
    for store in &scene.stores {
        #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
        let hi = store.hi.max(1) as usize;
        let existing = scope.get(&store.entity_type).copied().unwrap_or(0);
        scope.insert(store.entity_type.clone(), existing + hi);
    }

    // Count given bindings per entity type
    for given in &scene.givens {
        let entry = scope.entry(given.entity.clone()).or_insert(0);
        *entry += 1;
    }

    // Include systems referenced directly in scene events (not just the 'for' clause)
    for scene_event in &scene.events {
        if !system_names.contains(&scene_event.system) {
            system_names.push(scene_event.system.clone());
        }
    }
    for ordering_expr in &scene.ordering {
        collect_saw_systems_expr(ordering_expr, &mut system_names);
    }
    for assertion_expr in &scene.assertions {
        collect_saw_systems_expr(assertion_expr, &mut system_names);
    }
    for given_expr in &scene.given_constraints {
        collect_saw_systems_expr(given_expr, &mut system_names);
    }

    // Expand from systems — ensure all system entities are in scope.
    // Also follow CrossCalls transitively. Non-given entities need enough
    // slots for creates during the scenario. Use the bound (total firing
    // instances) which accounts for multi-fire cardinalities like {2}/{some}.
    let default_slots = bound.max(1);
    let mut systems_to_scan = system_names.clone();
    let mut scanned: HashSet<String> = HashSet::new();
    while let Some(sys_name) = systems_to_scan.pop() {
        if !scanned.insert(sys_name.clone()) {
            continue;
        }
        if let Some(sys) = ir.systems.iter().find(|s| s.name == sys_name) {
            if !system_names.contains(&sys.name) {
                system_names.push(sys.name.clone());
            }
            for event in &sys.steps {
                collect_crosscall_systems(&event.body, &mut systems_to_scan);
            }
            // Follow let bindings (program composition): a program's
            // let bindings define which systems it composes, so the
            // verifier must include those systems in scope.
            for lb in &sys.let_bindings {
                if !systems_to_scan.contains(&lb.system_type) {
                    systems_to_scan.push(lb.system_type.clone());
                }
            }
            for ent_name in &sys.entities {
                // Ensure enough slots for given bindings PLUS potential creates.
                // Given bindings occupy fixed slots at step 0; creates need
                // additional inactive slots. So total = given_count + default_slots.
                let given_count = scene
                    .givens
                    .iter()
                    .filter(|g| g.entity == *ent_name)
                    .count();
                let needed = given_count + default_slots;
                let entry = scope.entry(ent_name.clone()).or_insert(0);
                *entry = (*entry).max(needed);
            }
        }
    }

    if scope.is_empty() {
        return VerificationResult::SceneFail {
            name: scene.name.clone(),
            reason: crate::messages::SCENE_EMPTY_SCOPE.to_owned(),
            span: None,
            file: None,
        };
    }

    let relevant_entities: Vec<_> = ir
        .entities
        .iter()
        .filter(|e| scope.contains_key(&e.name))
        .cloned()
        .collect();

    let relevant_systems: Vec<_> = ir
        .systems
        .iter()
        .filter(|s| system_names.contains(&s.name))
        .cloned()
        .collect();

    // ── 2. Create pool and solver ──────────────────────────────────
    let pool = create_slot_pool_with_systems(&relevant_entities, &scope, bound, &relevant_systems);
    let solver = AbideSolver::new();
    if let Some(timeout_ms) = clamp_timeout_to_deadline(config.bmc_timeout_ms, deadline) {
        if timeout_ms > 0 {
            solver.set_timeout(timeout_ms);
        }
    } else {
        return VerificationResult::Unprovable {
            name: scene.name.clone(),
            hint: super::verification_timeout_hint(config),
            span: scene.span,
            file: scene.file.clone(),
        };
    }

    // Domain constraints at every step
    for c in domain_constraints(&pool, vctx, &relevant_entities) {
        solver.assert(&c);
    }

    // ── 2b. Compute scene store ranges ─────────────────────────────
    // Each store declaration gets a disjoint slot range within its entity
    // pool. Stores of the same entity type are SUM'd (not max'd).
    // store_name → (entity_type, start_slot, slot_count)
    let scene_store_ranges: HashMap<String, (String, usize, usize)> = {
        let mut ranges = HashMap::new();
        let mut running: HashMap<String, usize> = HashMap::new(); // entity_type → next start
        for store in &scene.stores {
            #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
            let count = store.hi.max(1) as usize;
            let start = running.get(&store.entity_type).copied().unwrap_or(0);
            ranges.insert(
                store.name.clone(),
                (store.entity_type.clone(), start, count),
            );
            running.insert(store.entity_type.clone(), start + count);
        }
        ranges
    };
    let scene_property_store_ranges: HashMap<String, VerifyStoreRange> = scene_store_ranges
        .iter()
        .map(|(store_name, (entity_type, start_slot, slot_count))| {
            (
                store_name.clone(),
                VerifyStoreRange {
                    entity_type: entity_type.clone(),
                    start_slot: *start_slot,
                    slot_count: *slot_count,
                },
            )
        })
        .collect();

    // ── 3. Encode given bindings ───────────────────────────────────
    // Each given binding activates one slot at step 0 and constrains its fields.
    // Track which slot each given variable is bound to.
    let mut given_bindings: HashMap<String, (String, usize)> = HashMap::new(); // var → (entity, slot)
    let mut next_slot: HashMap<String, usize> = HashMap::new(); // entity → next available slot
                                                                // Per-store slot tracking: store_name → next available slot within that store's range.
    let mut store_next_slot: HashMap<String, usize> = HashMap::new();

    for given in &scene.givens {
        let expanded = expand_through_defs(&given.constraint, defs);
        if let Some(kind) = find_unsupported_scene_expr(&expanded) {
            return VerificationResult::SceneFail {
                name: scene.name.clone(),
                reason: format!(
                    "unsupported expression kind in scene given for {}: {kind}",
                    given.var
                ),
                span: None,
                file: None,
            };
        }
    }

    for given in &scene.givens {
        // Allocate a slot — either within a named store's range or from
        // the global pool for the entity type.
        let current_slot = if let Some(store_name) = &given.store_name {
            if let Some((store_entity_type, start, count)) = scene_store_ranges.get(store_name) {
                // Validate entity type matches the store's entity type
                if *store_entity_type != given.entity {
                    return VerificationResult::SceneFail {
                        name: scene.name.clone(),
                        reason: format!(
                            "entity type mismatch: `let {} = one {} in {}` but store '{}' \
                             holds `{}`, not `{}`",
                            given.var,
                            given.entity,
                            store_name,
                            store_name,
                            store_entity_type,
                            given.entity,
                        ),
                        span: None,
                        file: None,
                    };
                }
                let next = store_next_slot.entry(store_name.clone()).or_insert(*start);
                if *next >= start + count {
                    return VerificationResult::SceneFail {
                        name: scene.name.clone(),
                        reason: format!(
                            "store '{}' is full: allocated {} of {} slots",
                            store_name,
                            *next - start,
                            count
                        ),
                        span: None,
                        file: None,
                    };
                }
                let slot = *next;
                *next += 1;
                slot
            } else {
                return VerificationResult::SceneFail {
                    name: scene.name.clone(),
                    reason: format!("unknown store '{}' in given for {}", store_name, given.var),
                    span: None,
                    file: None,
                };
            }
        } else {
            let slot = next_slot.entry(given.entity.clone()).or_insert(0);
            let current = *slot;
            *slot += 1;
            current
        };

        // Activate this slot at step 0
        if let Some(SmtValue::Bool(active)) = pool.active_at(&given.entity, current_slot, 0) {
            solver.assert(active);
        }

        // Encode the given constraint on this slot's fields at step 0
        let given_ctx = PropertyCtx::new()
            .with_store_ranges(scene_property_store_ranges.clone())
            .with_binding(&given.var, &given.entity, current_slot);
        let constraint =
            match encode_prop_expr_with_ctx(&pool, vctx, defs, &given_ctx, &given.constraint, 0) {
                Ok(c) => c,
                Err(msg) => {
                    return VerificationResult::SceneFail {
                        name: scene.name.clone(),
                        reason: format!(
                            "encoding error in given constraint for {}: {msg}",
                            given.var
                        ),
                        span: None,
                        file: None,
                    };
                }
            };
        solver.assert(&constraint);

        // Apply entity defaults for fields NOT explicitly constrained by the given block.
        // Expand the constraint through DefEnv first so that pred/prop references
        // are resolved, then collect field names to avoid default conflicts.
        let expanded_constraint = expand_through_defs(&given.constraint, defs);
        let mut constrained_fields = HashSet::new();
        collect_field_refs_in_expr(&expanded_constraint, &given.var, &mut constrained_fields);
        if let Some(entity_ir) = relevant_entities.iter().find(|e| e.name == given.entity) {
            for field in &entity_ir.fields {
                if constrained_fields.contains(field.name.as_str()) {
                    continue; // given constraint already sets this field
                }
                if let Some(ref default_expr) = field.default {
                    let empty_ept: HashMap<String, String> = HashMap::new();
                    let default_ctx = harness::SlotEncodeCtx {
                        pool: &pool,
                        vctx,
                        entity: &given.entity,
                        slot: current_slot,
                        params: HashMap::new(),
                        bindings: HashMap::new(),
                        system_name: "",
                        entity_param_types: &empty_ept,
                        store_param_types: &empty_ept,
                    };
                    let val = match harness::try_encode_slot_expr(&default_ctx, default_expr, 0) {
                        Ok(val) => val,
                        Err(reason) => {
                            return VerificationResult::SceneFail {
                                name: scene.name.clone(),
                                reason: format!("scene default field encoding failed: {reason}"),
                                span: None,
                                file: None,
                            };
                        }
                    };
                    if let Some(field_var) =
                        pool.field_at(&given.entity, current_slot, &field.name, 0)
                    {
                        match (&val, field_var) {
                            (SmtValue::Int(v), SmtValue::Int(f)) => {
                                solver.assert(smt::int_eq(f, v))
                            }
                            (SmtValue::Bool(v), SmtValue::Bool(f)) => {
                                solver.assert(smt::bool_eq(f, v));
                            }
                            (SmtValue::Real(v), SmtValue::Real(f)) => {
                                solver.assert(smt::real_eq(f, v));
                            }
                            _ => {} // skip Dynamic
                        }
                    }
                }
            }
        }

        given_bindings.insert(given.var.clone(), (given.entity.clone(), current_slot));
    }

    // ── 3b. Handle activate declarations ─────────────────────────
    // Each activation pre-activates named entity instances in a store
    // at step 0 and registers them as given bindings. The store name
    // is resolved via `scene_store_ranges` to get the entity type and
    // slot range.
    for activation in &scene.activations {
        let Some((entity_type, start, count)) = scene_store_ranges.get(&activation.store_name)
        else {
            return VerificationResult::SceneFail {
                name: scene.name.clone(),
                reason: format!("unknown store '{}'", activation.store_name),
                span: None,
                file: None,
            };
        };

        let next = store_next_slot
            .entry(activation.store_name.clone())
            .or_insert(*start);
        for inst_name in &activation.instances {
            if *next >= start + count {
                return VerificationResult::SceneFail {
                    name: scene.name.clone(),
                    reason: format!(
                        "store '{}' is full: allocated {} of {} slots",
                        activation.store_name,
                        *next - start,
                        count
                    ),
                    span: None,
                    file: None,
                };
            }
            let current_slot = *next;
            *next += 1;

            // Activate this slot at step 0
            if let Some(SmtValue::Bool(active)) = pool.active_at(entity_type, current_slot, 0) {
                solver.assert(active);
            }

            // Register the instance name as a given binding
            given_bindings.insert(inst_name.clone(), (entity_type.clone(), current_slot));
        }
    }

    // ── 3c. Assert given constraints at step 0 ───────────────────
    // Given constraints are initial-state assumptions, not end-state assertions.
    for gc in &scene.given_constraints {
        let expanded = expand_through_defs(gc, defs);
        if let Some(kind) = find_unsupported_scene_expr(&expanded) {
            return VerificationResult::SceneFail {
                name: scene.name.clone(),
                reason: format!("unsupported expression kind in scene given constraint: {kind}"),
                span: expr_span(gc),
                file: None,
            };
        }
        let gc_ctx = PropertyCtx::new()
            .with_store_ranges(scene_property_store_ranges.clone())
            .with_given_bindings(&given_bindings);
        match encode_prop_expr_with_ctx(&pool, vctx, defs, &gc_ctx, gc, 0) {
            Ok(c) => solver.assert(&c),
            Err(msg) => {
                return VerificationResult::SceneFail {
                    name: scene.name.clone(),
                    reason: format!("encoding error in given constraint: {msg}"),
                    span: expr_span(gc),
                    file: None,
                };
            }
        }
    }

    // Deactivate all other slots at step 0.
    // Collect all activated slots (from both global and store-based allocation)
    // so we only deactivate the truly unused ones.
    let activated_slots: HashSet<(String, usize)> = given_bindings
        .values()
        .map(|(entity, slot)| (entity.clone(), *slot))
        .collect();
    for entity in &relevant_entities {
        let n_slots = pool.slots_for(&entity.name);
        for slot in 0..n_slots {
            if activated_slots.contains(&(entity.name.clone(), slot)) {
                continue; // already activated by a given or activate declaration
            }
            if let Some(SmtValue::Bool(active)) = pool.active_at(&entity.name, slot, 0) {
                solver.assert(smt::bool_not(active));
            }
        }
    }

    // ── 4a. Validate scene events and determine referenced vars ────

    for assertion in &scene.assertions {
        let expanded = expand_through_defs(assertion, defs);
        if let Some(kind) = find_unsupported_scene_expr(&expanded) {
            return VerificationResult::SceneFail {
                name: scene.name.clone(),
                reason: format!("unsupported expression kind in scene then assertion: {kind}"),
                span: expr_span(assertion),
                file: None,
            };
        }
    }

    // Collect vars referenced in subsequent event args
    let referenced_vars: HashSet<String> = {
        let mut refs = HashSet::new();
        for ev in &scene.events {
            for arg in &ev.args {
                collect_var_refs_in_expr(arg, &mut refs);
            }
        }
        refs
    };

    // ── 4b. Validate events and resolve IR references ───────────────
    // Pre-validate all events before encoding. Collect the resolved
    // (system, event IR) pairs and result variable bindings.
    let mut resolved_events: Vec<ResolvedSceneEvent<'_>> = Vec::new();

    for scene_event in &scene.events {
        let sys = relevant_systems
            .iter()
            .find(|s| s.name == scene_event.system);
        let Some(sys) = sys else {
            return VerificationResult::SceneFail {
                name: scene.name.clone(),
                reason: format!(
                    "system {} not found for event {}",
                    scene_event.system, scene_event.event
                ),
                span: None,
                file: None,
            };
        };
        let matching_steps: Vec<_> = sys
            .steps
            .iter()
            .filter(|s| s.name == scene_event.event)
            .collect();
        if matching_steps.is_empty() {
            return VerificationResult::SceneFail {
                name: scene.name.clone(),
                reason: format!(
                    "event {} not found in system {}",
                    scene_event.event, scene_event.system
                ),
                span: None,
                file: None,
            };
        }

        // Use the first step for arity validation (all steps share the same
        // params — validated by collect.rs).
        let first_step = matching_steps[0];
        if scene_event.args.len() != first_step.params.len() {
            return VerificationResult::SceneFail {
                name: scene.name.clone(),
                reason: format!(
                    "arity mismatch: scene provides {} args for {}::{} but event expects {} params",
                    scene_event.args.len(),
                    scene_event.system,
                    scene_event.event,
                    first_step.params.len()
                ),
                span: None,
                file: None,
            };
        }

        for arg in &scene_event.args {
            let expanded = expand_through_defs(arg, defs);
            if let Some(kind) = find_unsupported_scene_expr(&expanded) {
                return VerificationResult::SceneFail {
                    name: scene.name.clone(),
                    reason: format!(
                        "unsupported expression kind in scene event arg for {}::{}: {kind}",
                        scene_event.system, scene_event.event
                    ),
                    span: None,
                    file: None,
                };
            }
        }

        for step in &matching_steps {
            if let Err(reason) = validate_crosscall_arities(&step.body, &relevant_systems, 0) {
                return VerificationResult::SceneFail {
                    name: scene.name.clone(),
                    reason,
                    span: None,
                    file: None,
                };
            }

            if let Some(kind) = find_unsupported_in_actions(&step.body) {
                return VerificationResult::SceneFail {
                    name: scene.name.clone(),
                    reason: format!(
                        "unsupported action in scene event {}::{}: {kind}",
                        scene_event.system, scene_event.event
                    ),
                    span: None,
                    file: None,
                };
            }
        }

        resolved_events.push(ResolvedSceneEvent {
            scene_event,
            steps: matching_steps,
        });
    }

    // Pre-compute result variable bindings (Creates from event bodies).
    // This must happen before the step variable encoding so bindings are
    // available for argument resolution at all possible steps.
    // Scan ALL matching steps (multi-clause commands) for Create actions
    // and validate they agree on the created entity type.
    for re in &resolved_events {
        if referenced_vars.contains(&re.scene_event.var) {
            let mut per_step_creates: Vec<Vec<String>> = Vec::new();
            for step_ir in &re.steps {
                per_step_creates.push(scan_event_creates(&step_ir.body, &relevant_systems));
            }
            // All steps must agree on create behavior: either all create
            // or none create. Mixed create/no-create is unsound because the
            // scene encoder activates the result slot unconditionally.
            let non_empty: Vec<&Vec<String>> =
                per_step_creates.iter().filter(|c| !c.is_empty()).collect();
            if !non_empty.is_empty()
                && non_empty.len() != per_step_creates.len()
                && per_step_creates.len() > 1
            {
                return VerificationResult::SceneFail {
                    name: scene.name.clone(),
                    reason: format!(
                        "multi-clause command {}::{} creates an entity in some steps \
                         but not others; scene result variable `{}` cannot be bound \
                         consistently (all implementing steps must create, or none)",
                        re.scene_event.system, re.scene_event.event, re.scene_event.var,
                    ),
                    span: None,
                    file: None,
                };
            }
            if let Some(first) = non_empty.first() {
                let first_entity = &first[0];
                for other in &non_empty[1..] {
                    if other[0] != *first_entity {
                        return VerificationResult::SceneFail {
                            name: scene.name.clone(),
                            reason: format!(
                                "multi-clause command {}::{} creates different entity types \
                                 across steps (`{}` vs `{}`); scene result variable `{}` \
                                 cannot be bound consistently",
                                re.scene_event.system,
                                re.scene_event.event,
                                first_entity,
                                other[0],
                                re.scene_event.var,
                            ),
                            span: None,
                            file: None,
                        };
                    }
                }
                let slot = next_slot.entry(first_entity.clone()).or_insert(0);
                let allocated_slot = *slot;
                *slot += 1;
                given_bindings.insert(
                    re.scene_event.var.clone(),
                    (first_entity.clone(), allocated_slot),
                );
            }
        }
    }

    // ── 4c. Resolve cardinalities and build firing instances ────────
    // Each event's cardinality determines how many firing instances it
    // gets. Each instance has a step variable (Int) and optionally a
    // fires variable (Bool) for optional firings.
    use crate::ir::types::Cardinality;

    let event_var_names: Vec<&str> = scene.events.iter().map(|e| e.var.as_str()).collect();
    let _n_ev = event_var_names.len();

    let var_to_idx: HashMap<&str, usize> = event_var_names
        .iter()
        .enumerate()
        .map(|(i, v)| (*v, i))
        .collect();

    // Collect events involved in ^| — these need {lone} fire tracking.
    // If declared as {one}, infer {lone} from ^| usage.
    let mut xor_events: HashSet<usize> = HashSet::new();
    for ordering_expr in &scene.ordering {
        collect_xor_event_indices(ordering_expr, &var_to_idx, &mut xor_events);
    }

    // Resolve cardinality for each event.
    // Returns (n_instances, min_fires, has_fire_tracking).
    struct EventCard {
        n_instances: usize,
        min_fires: usize,
        has_fire_tracking: bool,
    }

    // some_budget already computed above for bound calculation

    let mut event_cards: Vec<EventCard> = Vec::new();
    for (ei, re) in resolved_events.iter().enumerate() {
        let card = &re.scene_event.cardinality;
        let is_xor = xor_events.contains(&ei);
        let ec = match card {
            Cardinality::Named(c) => match c.as_str() {
                "one" if is_xor => EventCard {
                    n_instances: 1,
                    min_fires: 0,
                    has_fire_tracking: true,
                },
                "one" => EventCard {
                    n_instances: 1,
                    min_fires: 1,
                    has_fire_tracking: false,
                },
                "lone" => EventCard {
                    n_instances: 1,
                    min_fires: 0,
                    has_fire_tracking: true,
                },
                "no" => EventCard {
                    n_instances: 0,
                    min_fires: 0,
                    has_fire_tracking: false,
                },
                "some" => EventCard {
                    n_instances: some_budget,
                    min_fires: 1,
                    has_fire_tracking: true,
                },
                other => {
                    return VerificationResult::SceneFail {
                        name: scene.name.clone(),
                        reason: format!(
                            "unsupported cardinality '{other}' for scene event {}::{}",
                            re.scene_event.system, re.scene_event.event
                        ),
                        span: None,
                        file: None,
                    };
                }
            },
            Cardinality::Exact { exactly } => {
                let n = *exactly as usize;
                if is_xor && n > 1 {
                    return VerificationResult::SceneFail {
                        name: scene.name.clone(),
                        reason: format!(
                            "event '{}' has cardinality {{{n}}} but appears in `^|`; \
                             exclusive choice requires {{lone}} cardinality",
                            re.scene_event.var
                        ),
                        span: None,
                        file: None,
                    };
                }
                EventCard {
                    n_instances: n,
                    // When n==1 and event is in ^|, infer {lone}: min_fires=0
                    // so the XOR constraint controls whether it fires.
                    min_fires: if is_xor && n == 1 { 0 } else { n },
                    has_fire_tracking: is_xor,
                }
            }
        };
        event_cards.push(ec);
    }

    // Build firing instances. Each instance has a step variable and
    // optionally a fires variable.
    let mut instances: Vec<FiringInst> = Vec::new();
    // Map event index → range of instance indices
    let mut event_instance_ranges: Vec<std::ops::Range<usize>> = Vec::new();

    for (ei, ec) in event_cards.iter().enumerate() {
        let start = instances.len();
        for inst_idx in 0..ec.n_instances {
            let var_name = event_var_names[ei];
            let step_var = if ec.n_instances == 1 {
                smt::int_named(&format!("scene_step_{var_name}"))
            } else {
                smt::int_named(&format!("scene_step_{var_name}_{inst_idx}"))
            };
            let fires_var = if ec.has_fire_tracking {
                Some(smt::bool_named(&format!(
                    "scene_fires_{var_name}_{inst_idx}"
                )))
            } else {
                None
            };
            instances.push(FiringInst {
                event_idx: ei,
                inst_idx,
                step_var,
                fires_var,
            });
        }
        event_instance_ranges.push(start..instances.len());
    }

    // Verify instance count matches the pre-computed bound
    debug_assert_eq!(
        instances.len().max(1),
        bound,
        "instance count should match pre-computed bound"
    );

    // Assert bounds: each instance step in [0, bound)
    for inst in &instances {
        solver.assert(smt::int_ge(&inst.step_var, &smt::int_lit(0)));
        solver.assert(smt::int_lt(&inst.step_var, &smt::int_lit(bound as i64)));
    }

    // Assert internal ordering for multi-instance events: step_0 < step_1 <...
    for ec_range in &event_instance_ranges {
        if ec_range.len() > 1 {
            for i in ec_range.start..(ec_range.end - 1) {
                let curr = &instances[i].step_var;
                let next = &instances[i + 1].step_var;
                solver.assert(smt::int_lt(curr, next));
            }
        }
    }

    // Assert fire constraints
    for (ei, ec) in event_cards.iter().enumerate() {
        let range = &event_instance_ranges[ei];
        if ec.has_fire_tracking && ec.min_fires > 0 {
            // {some}: at least min_fires instances must fire
            let fire_vars: Vec<&Bool> = instances[range.clone()]
                .iter()
                .filter_map(|inst| inst.fires_var.as_ref())
                .collect();
            if !fire_vars.is_empty() {
                // At least min_fires must be true.
                // For {some} (min_fires=1): OR of all fires vars
                if ec.min_fires == 1 {
                    solver.assert(smt::bool_or(&fire_vars));
                } else {
                    // For arbitrary min_fires, encode as: at least N true
                    // using pairwise: too complex. Since min_fires == n_instances
                    // for {N} with fire tracking (only via ^|), just assert all.
                    for fv in &fire_vars {
                        solver.assert(*fv);
                    }
                }
            }
        }
        if !ec.has_fire_tracking && ec.min_fires > 0 {
            // {one} or {N} without fire tracking: all instances must fire
            // (already guaranteed by appearing in the disjunction unconditionally)
        }
    }

    // Assert distinctness: all instances at different steps, EXCEPT
    // same-step groups (from &) share a step.
    // Build same-step groups from OpSameStep ordering expressions.
    let mut group_parent: Vec<usize> = (0..instances.len()).collect();

    fn find_root(parent: &mut [usize], i: usize) -> usize {
        let mut r = i;
        while parent[r] != r {
            parent[r] = parent[parent[r]];
            r = parent[r];
        }
        r
    }

    // For & grouping, map event-level pairs to their first instance
    // (& only valid for single-instance events)
    {
        let mut same_step_event_pairs: Vec<(usize, usize)> = Vec::new();
        collect_same_step_event_pairs(&scene.ordering, &var_to_idx, &mut same_step_event_pairs);
        for (a, b) in &same_step_event_pairs {
            // Validate: & requires single-instance events
            if event_cards[*a].n_instances != 1 || event_cards[*b].n_instances != 1 {
                return VerificationResult::SceneFail {
                    name: scene.name.clone(),
                    reason: crate::messages::scene_same_step_multi_instance(
                        &scene.name,
                        event_var_names[*a],
                        event_cards[*a].n_instances,
                        event_var_names[*b],
                        event_cards[*b].n_instances,
                    ),
                    span: None,
                    file: None,
                };
            }
            let inst_a = event_instance_ranges[*a].start;
            let inst_b = event_instance_ranges[*b].start;
            let ra = find_root(&mut group_parent, inst_a);
            let rb = find_root(&mut group_parent, inst_b);
            if ra != rb {
                group_parent[rb] = ra;
            }
        }
    }

    // Validate same-step entity conflicts
    {
        let inst_group: Vec<usize> = (0..instances.len())
            .map(|i| find_root(&mut group_parent, i))
            .collect();
        let mut group_roots_set: Vec<usize> = Vec::new();
        for &g in &inst_group {
            if !group_roots_set.contains(&g) {
                group_roots_set.push(g);
            }
        }
        for &root in &group_roots_set {
            let members: Vec<usize> = (0..instances.len())
                .filter(|i| inst_group[*i] == root)
                .collect();
            if members.len() > 1 {
                let mut seen_entities: HashSet<String> = HashSet::new();
                for &ii in &members {
                    let re = &resolved_events[instances[ii].event_idx];
                    let mut event_entities = HashSet::new();
                    let mut visited_calls = HashSet::new();
                    for step in &re.steps {
                        collect_event_body_entities(
                            &step.body,
                            &relevant_systems,
                            &mut event_entities,
                            &mut visited_calls,
                        );
                    }
                    for ent_name in &event_entities {
                        if !seen_entities.insert(ent_name.clone()) {
                            return VerificationResult::SceneFail {
                                name: scene.name.clone(),
                                reason: crate::messages::scene_same_step_entity_conflict(
                                    &scene.name,
                                    ent_name,
                                ),
                                span: None,
                                file: None,
                            };
                        }
                    }
                }
            }
        }
    }

    // Assert distinctness between instances NOT in the same group
    {
        let inst_group: Vec<usize> = (0..instances.len())
            .map(|i| find_root(&mut group_parent, i))
            .collect();
        for i in 0..instances.len() {
            for j in (i + 1)..instances.len() {
                if inst_group[i] == inst_group[j] {
                    // Same group: assert equal step
                    solver.assert(smt::int_eq(&instances[i].step_var, &instances[j].step_var));
                } else {
                    // Different groups: assert distinct step
                    solver.assert(smt::bool_not(&smt::int_eq(
                        &instances[i].step_var,
                        &instances[j].step_var,
                    )));
                }
            }
        }
    }

    // Validate ordering expression variable names
    for ordering_expr in &scene.ordering {
        let leaf_vars = collect_ordering_leaf_vars(ordering_expr);
        for var_name in &leaf_vars {
            if !var_to_idx.contains_key(var_name) {
                return VerificationResult::SceneFail {
                    name: scene.name.clone(),
                    reason: crate::messages::scene_ordering_unknown_var(
                        &scene.name,
                        var_name,
                        &event_var_names.join(", "),
                    ),
                    span: None,
                    file: None,
                };
            }
        }
    }

    // Parse and assert ordering constraints from scene.ordering.
    // For multi-instance events, a -> b means: all of a's instances
    // precede all of b's instances (last_a < first_b).
    for ordering_expr in &scene.ordering {
        if let Err(reason) = encode_scene_ordering_v2(
            ordering_expr,
            &var_to_idx,
            &event_instance_ranges,
            &instances,
            &solver,
            &scene.name,
        ) {
            return VerificationResult::SceneFail {
                name: scene.name.clone(),
                reason,
                span: None,
                file: None,
            };
        }
    }

    // ── 4d. Encode instances at each possible step ──────────────────
    // At each step k, one instance (or same-step group) fires, or stutter.
    // Instances with fire tracking only fire when fires_var is true.
    let inst_group: Vec<usize> = (0..instances.len())
        .map(|i| find_root(&mut group_parent, i))
        .collect();
    let mut inst_group_roots: Vec<usize> = Vec::new();
    for &g in &inst_group {
        if !inst_group_roots.contains(&g) {
            inst_group_roots.push(g);
        }
    }

    for step in 0..bound {
        let mut step_disjuncts: Vec<Bool> = Vec::new();

        for &group_root in &inst_group_roots {
            let group_members: Vec<usize> = (0..instances.len())
                .filter(|i| inst_group[*i] == group_root)
                .collect();

            let step_guard =
                smt::int_eq(&instances[group_root].step_var, &smt::int_lit(step as i64));

            if group_members.len() == 1 {
                let ii = group_members[0];
                let inst = &instances[ii];
                let re = &resolved_events[inst.event_idx];

                let override_params = match build_scene_event_params(
                    re,
                    &pool,
                    vctx,
                    defs,
                    &given_bindings,
                    &scene_property_store_ranges,
                    step,
                    &scene.name,
                ) {
                    Ok(p) => p,
                    Err(reason) => {
                        return VerificationResult::SceneFail {
                            name: scene.name.clone(),
                            reason,
                            span: None,
                            file: None,
                        };
                    }
                };

                // Encode a disjunction over all steps implementing this command.
                let step_formulas: Vec<Bool> = re
                    .steps
                    .iter()
                    .map(|step_ir| {
                        encode_step_with_params(
                            &pool,
                            vctx,
                            &relevant_entities,
                            &relevant_systems,
                            step_ir,
                            step,
                            override_params.clone(),
                        )
                    })
                    .collect();
                let event_formula = if step_formulas.len() == 1 {
                    step_formulas.into_iter().next().unwrap()
                } else {
                    let refs: Vec<&Bool> = step_formulas.iter().collect();
                    smt::bool_or(&refs)
                };

                if let Some(fires) = &inst.fires_var {
                    // Optional firing: (step_guard ∧ fires ∧ event) ∨ (step_guard ∧ ¬fires ∧ stutter)
                    let fires_branch = smt::bool_and(&[&step_guard, fires, &event_formula]);
                    let stutter = harness::stutter_constraint(&pool, &relevant_entities, step);
                    let skip_branch =
                        smt::bool_and(&[&step_guard, &smt::bool_not(fires), &stutter]);
                    step_disjuncts.push(smt::bool_or(&[&fires_branch, &skip_branch]));
                } else {
                    // Must fire
                    step_disjuncts.push(smt::bool_and(&[&step_guard, &event_formula]));
                }
            } else {
                // Same-step group: encode combined with fire-tracking.
                // {lone} members are conditional: fires_var → event, ¬fires_var → skip.
                let mut group_formulas: Vec<Bool> = Vec::new();
                let mut combined_touched: HashSet<(String, usize)> = HashSet::new();

                for &ii in &group_members {
                    let inst = &instances[ii];
                    let re = &resolved_events[inst.event_idx];
                    let override_params = match build_scene_event_params(
                        re,
                        &pool,
                        vctx,
                        defs,
                        &given_bindings,
                        &scene_property_store_ranges,
                        step,
                        &scene.name,
                    ) {
                        Ok(p) => p,
                        Err(reason) => {
                            return VerificationResult::SceneFail {
                                name: scene.name.clone(),
                                reason,
                                span: None,
                                file: None,
                            };
                        }
                    };
                    // Encode a disjunction over all steps implementing this command,
                    // with per-branch framing so each branch constrains slots touched
                    // by other branches but not by itself.
                    let mut branch_results: Vec<(Bool, HashSet<(String, usize)>)> = Vec::new();
                    for step_ir in &re.steps {
                        let (f, t) = match harness::try_encode_step_inner(
                            &pool,
                            vctx,
                            &relevant_entities,
                            &relevant_systems,
                            step_ir,
                            step,
                            0,
                            Some(override_params.clone()),
                        ) {
                            Ok(v) => v,
                            Err(reason) => {
                                return VerificationResult::SceneFail {
                                    name: scene.name.clone(),
                                    reason: format!("scene step encoding failed: {reason}"),
                                    span: None,
                                    file: None,
                                };
                            }
                        };
                        branch_results.push((f, t));
                    }
                    // Compute union of touched across all branches
                    let all_branch_touched: HashSet<(String, usize)> = branch_results
                        .iter()
                        .flat_map(|(_, t)| t.iter().cloned())
                        .collect();
                    // Apply per-branch framing
                    let framed_branches: Vec<Bool> = branch_results
                        .into_iter()
                        .map(|(formula, branch_touched)| {
                            let extra: HashSet<(String, usize)> = all_branch_touched
                                .difference(&branch_touched)
                                .cloned()
                                .collect();
                            if extra.is_empty() {
                                formula
                            } else {
                                let frame = harness::frame_specific_slots(
                                    &pool,
                                    &relevant_entities,
                                    &extra,
                                    step,
                                );
                                let mut parts = vec![formula];
                                parts.extend(frame);
                                let refs: Vec<&Bool> = parts.iter().collect();
                                smt::bool_and(&refs)
                            }
                        })
                        .collect();
                    let formula = if framed_branches.len() == 1 {
                        framed_branches.into_iter().next().unwrap()
                    } else {
                        let refs: Vec<&Bool> = framed_branches.iter().collect();
                        smt::bool_or(&refs)
                    };
                    combined_touched.extend(all_branch_touched);
                    // For {lone} members, make the formula conditional on fires_var.
                    if let Some(fires) = &inst.fires_var {
                        group_formulas.push(smt::bool_implies(fires, &formula));
                    } else {
                        group_formulas.push(formula);
                    }
                }

                let mut all_parts = vec![step_guard];
                all_parts.extend(group_formulas);
                let combined = {
                    let refs: Vec<&Bool> = all_parts.iter().collect();
                    smt::bool_and(&refs)
                };
                let framed = harness::apply_global_frame(
                    &pool,
                    &relevant_entities,
                    &combined_touched,
                    step,
                    combined,
                );
                step_disjuncts.push(framed);
            }
        }

        // Stutter: no instance fires at this step
        let mut no_inst_parts: Vec<Bool> = Vec::new();
        for &root in &inst_group_roots {
            no_inst_parts.push(smt::bool_not(&smt::int_eq(
                &instances[root].step_var,
                &smt::int_lit(step as i64),
            )));
        }
        let stutter = harness::stutter_constraint(&pool, &relevant_entities, step);
        let no_inst_refs: Vec<&Bool> = no_inst_parts.iter().collect();
        let no_inst = smt::bool_and(&no_inst_refs);
        step_disjuncts.push(smt::bool_and(&[&no_inst, &stutter]));

        let refs: Vec<&Bool> = step_disjuncts.iter().collect();
        solver.assert(smt::bool_or(&refs));
    }

    // Assert result variable activation for create events
    for (ei, re) in resolved_events.iter().enumerate() {
        if let Some((result_entity, allocated_slot)) = given_bindings.get(&re.scene_event.var) {
            let is_result = scene.givens.iter().all(|g| g.var != re.scene_event.var);
            if is_result {
                // Use first instance of this event for result activation
                let range = &event_instance_ranges[ei];
                if !range.is_empty() {
                    let first_inst = &instances[range.start];
                    for step in 0..bound {
                        if let Some(SmtValue::Bool(active_next)) =
                            pool.active_at(result_entity, *allocated_slot, step + 1)
                        {
                            let mut guard =
                                smt::int_eq(&first_inst.step_var, &smt::int_lit(step as i64));
                            if let Some(fires) = &first_inst.fires_var {
                                guard = smt::bool_and(&[&guard, fires]);
                            }
                            solver.assert(smt::bool_implies(&guard, active_next));
                        }
                    }
                }
            }
        }
    }

    // ── 5. Encode then assertions at final step ────────────────────
    let final_step = bound; // after all events
    let mut then_ctx = PropertyCtx::new().with_store_ranges(scene_property_store_ranges);
    for (var, (entity, slot)) in &given_bindings {
        then_ctx = then_ctx.with_binding(var, entity, *slot);
    }

    for assertion in &scene.assertions {
        let prop =
            match encode_prop_expr_with_ctx(&pool, vctx, defs, &then_ctx, assertion, final_step) {
                Ok(p) => p,
                Err(msg) => {
                    return VerificationResult::SceneFail {
                        name: scene.name.clone(),
                        reason: format!("encoding error in then assertion: {msg}"),
                        span: expr_span(assertion),
                        file: None,
                    };
                }
            };
        solver.assert(&prop);
    }

    // ── 6. Check SAT ───────────────────────────────────────────────
    let elapsed = elapsed_ms(&start);

    match solver.check() {
        SatResult::Sat => VerificationResult::ScenePass {
            name: scene.name.clone(),
            time_ms: elapsed,
            span: None,
            file: None,
        },
        SatResult::Unsat => VerificationResult::SceneFail {
            name: scene.name.clone(),
            reason: crate::messages::SCENE_UNSATISFIABLE.to_owned(),
            span: None,
            file: None,
        },
        SatResult::Unknown(_) => VerificationResult::SceneFail {
            name: scene.name.clone(),
            reason: crate::messages::SCENE_UNKNOWN.to_owned(),
            span: None,
            file: None,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn empty_ir() -> IRProgram {
        IRProgram {
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

    fn empty_scene() -> IRScene {
        IRScene {
            name: "empty_scene".to_owned(),
            systems: vec![],
            stores: vec![],
            givens: vec![],
            events: vec![],
            ordering: vec![],
            assertions: vec![],
            given_constraints: vec![],
            activations: vec![],
            span: None,
            file: None,
        }
    }

    fn scene_with_unsupported_given() -> IRScene {
        IRScene {
            name: "unsupported_given".to_owned(),
            systems: vec![],
            stores: vec![],
            givens: vec![crate::ir::types::IRSceneGiven {
                var: "task".to_owned(),
                entity: "Task".to_owned(),
                store_name: None,
                constraint: IRExpr::Sorry { span: None },
            }],
            events: vec![],
            ordering: vec![],
            assertions: vec![],
            given_constraints: vec![],
            activations: vec![],
            span: None,
            file: None,
        }
    }

    fn store_decl(name: &str, entity_type: &str, hi: i64) -> crate::ir::types::IRStoreDecl {
        crate::ir::types::IRStoreDecl {
            name: name.to_owned(),
            entity_type: entity_type.to_owned(),
            lo: hi,
            hi,
        }
    }

    fn given(var: &str, entity: &str, store_name: Option<&str>) -> crate::ir::types::IRSceneGiven {
        crate::ir::types::IRSceneGiven {
            var: var.to_owned(),
            entity: entity.to_owned(),
            store_name: store_name.map(str::to_owned),
            constraint: bool_lit(true),
        }
    }

    fn store_scene(
        name: &str,
        stores: Vec<crate::ir::types::IRStoreDecl>,
        givens: Vec<crate::ir::types::IRSceneGiven>,
        given_constraints: Vec<IRExpr>,
        assertions: Vec<IRExpr>,
        activations: Vec<crate::ir::types::IRActivation>,
    ) -> IRScene {
        IRScene {
            name: name.to_owned(),
            systems: vec![],
            stores,
            givens,
            events: vec![],
            ordering: vec![],
            assertions,
            given_constraints,
            activations,
            span: None,
            file: None,
        }
    }

    fn bool_lit(value: bool) -> IRExpr {
        IRExpr::Lit {
            ty: crate::ir::types::IRType::Bool,
            value: crate::ir::types::LitVal::Bool { value },
            span: None,
        }
    }

    fn var(name: &str) -> IRExpr {
        IRExpr::Var {
            name: name.to_owned(),
            ty: crate::ir::types::IRType::Bool,
            span: None,
        }
    }

    fn bin(op: &str, left: IRExpr, right: IRExpr) -> IRExpr {
        IRExpr::BinOp {
            op: op.to_owned(),
            left: Box::new(left),
            right: Box::new(right),
            ty: crate::ir::types::IRType::Bool,
            span: None,
        }
    }

    fn firing(event_idx: usize, inst_idx: usize, fires_var: Option<Bool>) -> FiringInst {
        FiringInst {
            event_idx,
            inst_idx,
            step_var: smt::int_const(&format!("s_{event_idx}_{inst_idx}")),
            fires_var,
        }
    }

    #[test]
    fn scene_ordering_collectors_walk_nested_sequence_same_step_and_xor() {
        let expr = bin(
            "OpSeq",
            bin("OpSameStep", var("a"), var("b")),
            bin("OpXor", var("c"), var("d")),
        );
        assert_eq!(collect_ordering_leaf_vars(&expr), vec!["a", "b", "c", "d"]);

        let var_to_idx =
            HashMap::from([("a", 0usize), ("b", 1usize), ("c", 2usize), ("d", 3usize)]);
        assert_eq!(first_ordering_var(&expr, &var_to_idx), Some(0));
        assert_eq!(last_ordering_var(&expr, &var_to_idx), Some(3));

        let mut pairs = Vec::new();
        collect_same_step_event_pairs(&[expr.clone()], &var_to_idx, &mut pairs);
        assert_eq!(pairs, vec![(0, 1)]);

        let mut xor_events = HashSet::new();
        collect_xor_event_indices(&expr, &var_to_idx, &mut xor_events);
        assert_eq!(xor_events, HashSet::from([2, 3]));
        assert_eq!(event_var_names_from_idx(2, &var_to_idx), "c");
        assert_eq!(event_var_names_from_idx(99, &var_to_idx), "event_99");
    }

    #[test]
    fn scene_ordering_encoder_rejects_unknown_empty_and_untracked_xor_shapes() {
        let solver = AbideSolver::new();
        let var_to_idx = HashMap::from([("a", 0usize), ("b", 1usize)]);
        let instances = vec![
            firing(0, 0, Some(smt::bool_named("a_fires"))),
            firing(1, 0, Some(smt::bool_named("b_fires"))),
        ];

        let unknown = encode_scene_ordering_v2(
            &bin("OpSeq", var("a"), bool_lit(true)),
            &var_to_idx,
            &[0..1, 1..2],
            &instances,
            &solver,
            "ordering_errors",
        );
        assert!(matches!(unknown, Err(reason) if reason.contains("unknown event variable")));

        let empty_xor = encode_scene_ordering_v2(
            &bin("OpXor", var("a"), var("b")),
            &var_to_idx,
            &[0..0, 1..2],
            &instances,
            &solver,
            "ordering_errors",
        );
        assert!(matches!(empty_xor, Err(reason) if reason.contains("ordering_errors")));

        let no_fire_instances = vec![
            firing(0, 0, None),
            firing(1, 0, Some(smt::bool_named("b_fires_2"))),
        ];
        let no_fire = encode_scene_ordering_v2(
            &bin("OpXor", var("a"), var("b")),
            &var_to_idx,
            &[0..1, 1..2],
            &no_fire_instances,
            &solver,
            "ordering_errors",
        );
        assert!(matches!(no_fire, Err(reason) if reason.contains("ordering_errors")));
    }

    #[test]
    fn scene_ordering_encoder_accepts_basic_sequence_same_step_concurrency_and_xor() {
        let solver = AbideSolver::new();
        let var_to_idx = HashMap::from([("a", 0usize), ("b", 1usize), ("c", 2usize)]);
        let instances = vec![
            firing(0, 0, Some(smt::bool_named("a_fires_ok"))),
            firing(1, 0, Some(smt::bool_named("b_fires_ok"))),
            firing(2, 0, Some(smt::bool_named("c_fires_ok"))),
        ];
        let expr = bin(
            "OpConc",
            bin("OpSeq", var("a"), var("b")),
            bin("OpXor", var("b"), var("c")),
        );
        encode_scene_ordering_v2(
            &expr,
            &var_to_idx,
            &[0..1, 1..2, 2..3],
            &instances,
            &solver,
            "ordering_ok",
        )
        .expect("supported ordering should encode");
    }

    #[test]
    fn check_scene_block_reports_empty_scope_without_solver_work() {
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let result = check_scene_block(
            &ir,
            &vctx,
            &defs,
            &empty_scene(),
            &VerifyConfig::default(),
            None,
        );
        assert!(matches!(
            result,
            VerificationResult::SceneFail { name, reason, .. }
                if name == "empty_scene" && reason == crate::messages::SCENE_EMPTY_SCOPE
        ));
    }

    #[test]
    fn check_scene_block_reports_unsupported_given_before_slot_allocation() {
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let result = check_scene_block(
            &ir,
            &vctx,
            &defs,
            &scene_with_unsupported_given(),
            &VerifyConfig::default(),
            None,
        );
        assert!(matches!(
            result,
            VerificationResult::SceneFail { name, reason, .. }
                if name == "unsupported_given"
                    && reason.contains("unsupported expression kind in scene given")
        ));
    }

    #[test]
    fn check_scene_block_reports_store_binding_validation_errors() {
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let config = VerifyConfig::default();

        let mismatch = check_scene_block(
            &ir,
            &vctx,
            &defs,
            &store_scene(
                "mismatch",
                vec![store_decl("tasks", "Task", 1)],
                vec![given("order", "Order", Some("tasks"))],
                vec![],
                vec![],
                vec![],
            ),
            &config,
            None,
        );
        assert!(matches!(
            mismatch,
            VerificationResult::SceneFail { reason, .. } if reason.contains("entity type mismatch")
        ));

        let unknown_store = check_scene_block(
            &ir,
            &vctx,
            &defs,
            &store_scene(
                "unknown_store",
                vec![store_decl("tasks", "Task", 1)],
                vec![given("task", "Task", Some("missing"))],
                vec![],
                vec![],
                vec![],
            ),
            &config,
            None,
        );
        assert!(matches!(
            unknown_store,
            VerificationResult::SceneFail { reason, .. } if reason.contains("unknown store 'missing'")
        ));

        let full_store = check_scene_block(
            &ir,
            &vctx,
            &defs,
            &store_scene(
                "full_store",
                vec![store_decl("tasks", "Task", 1)],
                vec![
                    given("first", "Task", Some("tasks")),
                    given("second", "Task", Some("tasks")),
                ],
                vec![],
                vec![],
                vec![],
            ),
            &config,
            None,
        );
        assert!(matches!(
            full_store,
            VerificationResult::SceneFail { reason, .. } if reason.contains("store 'tasks' is full")
        ));
    }

    #[test]
    fn check_scene_block_reports_activation_and_expression_validation_errors() {
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let config = VerifyConfig::default();

        let unknown_activation_store = check_scene_block(
            &ir,
            &vctx,
            &defs,
            &store_scene(
                "unknown_activation_store",
                vec![store_decl("tasks", "Task", 1)],
                vec![],
                vec![],
                vec![],
                vec![crate::ir::types::IRActivation {
                    instances: vec!["task".to_owned()],
                    store_name: "missing".to_owned(),
                }],
            ),
            &config,
            None,
        );
        assert!(matches!(
            unknown_activation_store,
            VerificationResult::SceneFail { reason, .. } if reason.contains("unknown store 'missing'")
        ));

        let unsupported_given_constraint = check_scene_block(
            &ir,
            &vctx,
            &defs,
            &store_scene(
                "unsupported_given_constraint",
                vec![store_decl("tasks", "Task", 1)],
                vec![],
                vec![IRExpr::Todo { span: None }],
                vec![],
                vec![],
            ),
            &config,
            None,
        );
        assert!(matches!(
            unsupported_given_constraint,
            VerificationResult::SceneFail { reason, .. }
                if reason.contains("unsupported expression kind in scene given constraint")
        ));

        let unsupported_assertion = check_scene_block(
            &ir,
            &vctx,
            &defs,
            &store_scene(
                "unsupported_assertion",
                vec![store_decl("tasks", "Task", 1)],
                vec![],
                vec![],
                vec![IRExpr::Sorry { span: None }],
                vec![],
            ),
            &config,
            None,
        );
        assert!(matches!(
            unsupported_assertion,
            VerificationResult::SceneFail { reason, .. }
                if reason.contains("unsupported expression kind in scene then assertion")
        ));
    }
}
