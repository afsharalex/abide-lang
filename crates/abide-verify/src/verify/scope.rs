//! Scope computation — entity slot counts, system selection, invariant collection.

use std::collections::{HashMap, HashSet};

use crate::ir::types::{
    IRAction, IREntity, IRExpr, IRProgram, IRSystem, IRTheorem, IRType, IRVerify,
};

use super::defenv;
use super::temporal::LivenessPattern;

// ── Shared scope construction for verify-block proof techniques ────

/// Slot range owned by a single store within an entity pool.
/// Multiple stores of the same entity type share the pool but own
/// disjoint slot ranges (e.g., `pending: Order[0..3]` → slots 0-2,
/// `archived: Order[0..2]` → slots 3-4, total Order pool = 5).
#[derive(Debug, Clone)]
#[allow(dead_code)] // fields preserved for future store-scoped quantifier iteration
pub struct VerifyStoreRange {
    pub entity_type: String,
    pub start_slot: usize,
    pub slot_count: usize,
    pub min_active: usize,
    pub max_active: usize,
}

/// Compute the canonical entity scope and reachable systems for a
/// verify block. This is the **single source of truth** for the bounded
/// semantics scope used by every proof technique attached to a verify
/// block: linear BMC, lasso BMC, 1-induction, IC3/PDR, the liveness
/// reduction, and the direct deadlock probe.
///
/// Before extraction, six call sites
/// duplicated this logic with two different recipes — `check_verify_block`
/// and `check_verify_block_lasso` sized scope from each verify target's
/// `hi` bound, while `check_for_deadlock`, `try_induction_on_verify`,
/// `try_liveness_reduction`, and the lasso entry point all hardcoded
/// `or_insert(2)`. The mismatch let the deadlock probe disagree with
/// the actual BMC on the same verify block (and short-circuit before
/// the correct model was even built).
///
/// Returns:
/// - `scope`: entity name → slot count, sized from each verify target
///   `vs.hi.max(1)` and propagated through cross-call expansion.
/// - `system_names`: target systems plus all systems transitively
///   reachable via cross-calls.
/// - `bound`: the maximum `hi` across verify targets, also used as the
///   default slot count for cross-call-reachable entities (matching the
///   pre-extraction `existing.max(bound)` recipe in `check_verify_block`).
///
/// **Note for callers that need additional capacity:** `try_induction_on_verify`
/// and `try_liveness_reduction` may need to widen the returned scope
/// based on quantifier depth in the assert formulas. They should call
/// this helper first and then layer their per-caller adjustments on top
/// of the returned scope map.
pub(super) fn compute_verify_scope(
    ir: &IRProgram,
    verify_block: &IRVerify,
) -> (
    HashMap<String, usize>,
    Vec<String>,
    usize,
    HashMap<String, VerifyStoreRange>,
) {
    let mut scope: HashMap<String, usize> = HashMap::new();
    let mut system_names: Vec<String> = Vec::new();
    // Apply the depth override early so it seeds pool sizing and
    // cross-call expansion. Without this, transitive systems that inherit
    // the generic bound path would use the default 3 instead of the
    // user-specified depth.
    let mut bound: usize = if let Some(depth) = verify_block.depth {
        #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
        {
            (depth as usize).max(1)
        }
    } else {
        3
    };
    let mut store_ranges: HashMap<String, VerifyStoreRange> = HashMap::new();

    // Size entities from per-store declarations. Each store gets its own
    // slot range, and sizes are summed so same-type stores get
    // independent slots. Example: two `Order[0..3]` stores → 6 slots total.
    for store in &verify_block.stores {
        #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
        let slot_count = store.hi.max(1) as usize;
        #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
        let lo = store.lo.max(0) as usize;
        #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
        let max_active = store.hi.max(0) as usize;
        bound = bound.max(slot_count);
        let existing = scope.get(&store.entity_type).copied().unwrap_or(0);
        // Track this store's slot range before accumulating.
        store_ranges.insert(
            store.name.clone(),
            VerifyStoreRange {
                entity_type: store.entity_type.clone(),
                start_slot: existing,
                slot_count,
                min_active: lo,
                max_active,
            },
        );
        // Each store gets its own slot range within the entity pool.
        scope.insert(store.entity_type.clone(), existing + slot_count);
    }

    // Collect system names from the verify target list.
    for vs in &verify_block.systems {
        system_names.push(vs.name.clone());
        // If no stores were declared, fall back to the
        // system-level hi for sizing.
        if verify_block.stores.is_empty() {
            #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
            let hi = vs.hi.max(1) as usize;
            bound = bound.max(hi);
            if let Some(sys) = ir.systems.iter().find(|s| s.name == vs.name) {
                for ent_name in &sys.entities {
                    let existing = scope.get(ent_name).copied().unwrap_or(0);
                    scope.insert(ent_name.clone(), existing.max(hi));
                }
            }
        }
    }

    for assert_expr in &verify_block.asserts {
        collect_saw_systems_expr(assert_expr, &mut system_names);
    }

    // Cross-call expansion: walk transitively reachable systems and
    // size their entities at `bound`.
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
            for event in &sys.actions {
                collect_crosscall_systems(&event.body, &mut systems_to_scan);
            }
            // Follow let bindings: a program's let bindings define
            // which systems it composes, so the verifier must include
            // those systems in scope.
            for lb in &sys.let_bindings {
                if !systems_to_scan.contains(&lb.system_type) {
                    systems_to_scan.push(lb.system_type.clone());
                }
            }
            for ent_name in &sys.entities {
                let existing = scope.get(ent_name).copied().unwrap_or(0);
                scope.insert(ent_name.clone(), existing.max(bound));
            }
        }
    }

    (scope, system_names, bound, store_ranges)
}

/// Companion to `compute_verify_scope`: filter the IR's entities and
/// systems down to those that are in scope for a verify block. The
/// arguments come from `compute_verify_scope`'s return value.
pub(super) fn select_verify_relevant(
    ir: &IRProgram,
    scope: &HashMap<String, usize>,
    system_names: &[String],
) -> (Vec<IREntity>, Vec<IRSystem>) {
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
    (relevant_entities, relevant_systems)
}

/// Compute the canonical entity scope and reachable systems for a
/// theorem block. Theorems are unbounded — there is no `vs.hi` to
/// size from — so each entity is sized at `max(2, quantifier_depth + 1)`,
/// where the quantifier depth is computed from `quantifier_exprs`
/// (typically `theorem.shows`, optionally extended with
/// `theorem.invariants` when the caller will encode invariants too).
///
/// This is the theorem-side counterpart to
/// `compute_verify_scope`, replacing the open-coded scope walks in
/// `check_theorem_block` and `try_ic3_on_theorem`. The two call sites
/// previously duplicated the same `min_slots.max(2)` / `or_insert(2)`
/// recipe with subtle drift.
///
/// Returns:
/// - `scope`: entity name → slot count
/// - `system_names`: target systems plus cross-call-reachable systems
/// - `required_slots`: entity name → quantifier depth, exposed so the
///   caller can detect quantifiers over entities that are not in any
///   of the theorem's systems (an "out-of-scope quantifier" diagnostic).
pub(super) fn compute_theorem_scope(
    ir: &IRProgram,
    theorem: &IRTheorem,
    quantifier_exprs: &[&IRExpr],
    defs: &defenv::DefEnv,
) -> (HashMap<String, usize>, Vec<String>, HashMap<String, usize>) {
    // Compute quantifier depth per entity from the supplied expressions.
    // Expand through DefEnv first so pred/prop bodies with entity
    // quantifiers contribute their depth.
    let mut required_slots: HashMap<String, usize> = HashMap::new();
    for expr in quantifier_exprs {
        let expanded = super::expand_through_defs(expr, defs);
        let mut counts: HashMap<String, usize> = HashMap::new();
        super::count_entity_quantifiers(&expanded, &mut counts);
        for (entity, count) in &counts {
            let existing = required_slots.get(entity).copied().unwrap_or(0);
            required_slots.insert(entity.clone(), existing.max(*count));
        }
    }

    // Walk the theorem's systems with cross-call expansion. Size each
    // entity at max(2, quantifier_depth + 1): enough for the
    // simultaneously bound variables plus one slot for Create
    // transitions.
    let mut scope: HashMap<String, usize> = HashMap::new();
    let mut system_names: Vec<String> = theorem.systems.clone();
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
            for event in &sys.actions {
                collect_crosscall_systems(&event.body, &mut systems_to_scan);
            }
            // Follow let bindings: a program's let bindings define
            // which systems it composes, so the verifier must include
            // those systems in scope.
            for lb in &sys.let_bindings {
                if !systems_to_scan.contains(&lb.system_type) {
                    systems_to_scan.push(lb.system_type.clone());
                }
            }
            for ent_name in &sys.entities {
                let min_slots = required_slots.get(ent_name).copied().unwrap_or(0) + 1;
                scope.entry(ent_name.clone()).or_insert(min_slots.max(2));
            }
        }
    }

    (scope, system_names, required_slots)
}

// ── In-scope invariant collection ───────────────────────────────────

/// Collect every entity and system invariant in
/// scope for a verify or theorem block, returned as a list of
/// `Always`-wrapped property expressions ready to be merged into the
/// existing assert/show list.
///
/// Entity invariants are wrapped in `Always { Forall { var, domain:
/// Entity { name }, body: rewritten } }` so they apply per-instance to
/// every active entity slot at every step. The body's bare field
/// references are rewritten via the binder-aware
/// `DefEnv::rewrite_entity_invariant_body` so local
/// lets/lambdas/quantifiers inside the invariant body
/// are not clobbered.
///
/// System invariants are wrapped in `Always { body }` directly. They
/// reference system-scope state (pools, derived fields) and need no
/// per-instance wrapping.
///
/// Entity invariants travel with the entity type: every
/// entity in scope (`relevant_entities`, including those reached via
/// crosscall expansion) contributes its invariants regardless of which
/// system pools it. System invariants stay scoped to the declaring
/// system: `target_systems` is the literal verify/theorem target list,
/// not the crosscall-expanded `relevant_systems`. A callee system's
/// invariants do not leak into a caller's verify just because the
/// caller crosscalls into it.
pub(super) fn collect_in_scope_invariants(
    defs: &defenv::DefEnv,
    relevant_entities: &[IREntity],
    target_systems: &[IRSystem],
) -> Vec<IRExpr> {
    let mut wrapped: Vec<IRExpr> = Vec::new();

    // Entity invariants travel with the entity type.
    for ent in relevant_entities {
        for inv in &ent.invariants {
            // Build a fresh `__inv_self` Var of the entity type. The
            // name has a leading `__` so it cannot collide with any
            // user-written identifier.
            let receiver = IRExpr::Var {
                name: "__inv_self".to_owned(),
                ty: IRType::Entity {
                    name: ent.name.clone(),
                },
                span: None,
            };
            let rewritten =
                defs.rewrite_entity_invariant_body(inv.body.clone(), &receiver, &ent.name);
            let forall_body = IRExpr::Forall {
                var: "__inv_self".to_owned(),
                domain: IRType::Entity {
                    name: ent.name.clone(),
                },
                body: Box::new(rewritten),
                span: None,
            };
            wrapped.push(IRExpr::Always {
                body: Box::new(forall_body),
                span: None,
            });
        }
    }

    // System invariants: per they stay scoped to the declaring
    // system. Only the literal verify/theorem target systems contribute —
    // crosscall-reachable systems do not, because that would silently
    // import a callee's safety claims into the caller's verify.
    for sys in target_systems {
        for inv in &sys.invariants {
            wrapped.push(IRExpr::Always {
                body: Box::new(inv.body.clone()),
                span: None,
            });
        }
    }

    wrapped
}

// ── Symmetry reduction for quantified liveness () ────────────
//
// For `always all o: E | P(o) implies eventually Q(o)` with fair events:
// 1. All entities of type E have identical field types, defaults, and transitions
// 2. Fair events with `choose o: E where guard` are symmetric: which slot is
// chosen is nondeterministic, but fairness guarantees each enabled slot
// is eventually served
// 3. Therefore: if the property is PROVED for a system with 1 slot of type E,
// by symmetry it holds for any slot count
//
// Symmetry breaks when:
// - Events contain nested Choose/ForAll over the SAME entity type (inter-entity ref)
// - The property references multiple entities of the same type

/// Check whether a quantified liveness property is suitable for symmetry reduction.
///
/// The symmetry argument requires that all entities of the quantified type are
/// interchangeable: identical fields, identical transitions, no inter-entity
/// dependencies. This function checks three conditions:
///
/// 1. **Event bodies**: No event has multiple Choose/ForAll over the same entity
///    type (directly or via `CrossCall`), which would create inter-entity dependencies.
///
/// 2. **`CrossCall` composition**: If an event body calls into another system via
///    `CrossCall`, and that system also Choose/ForAll over the quantified entity type,
///    the combined event manipulates multiple slots (symmetry broken).
///
/// 3. **Property formulas**: The trigger/response expressions must not contain
///    additional quantifiers (Forall/Exists/One/Lone) over the same entity type,
///    which would reference multiple slots in the property itself.
///
/// Returns `true` if the system is symmetric for the given entity type.
pub(super) fn validate_symmetry(
    entity_name: &str,
    systems: &[IRSystem],
    all_systems: &[IRSystem],
    pattern: &LivenessPattern,
) -> bool {
    // ── Condition 1+2: Event bodies + CrossCall targets ──────────────
    // Count entity references per event, following CrossCall targets
    // transitively. If any event's combined action tree has 2+ references
    // to the quantified entity type, symmetry breaks.
    for sys in systems {
        for event in &sys.actions {
            let mut count = 0;
            count_entity_actions_with_crosscall(
                &event.body,
                entity_name,
                all_systems,
                &mut count,
                &mut HashSet::new(),
            );
            if count >= 2 {
                return false;
            }
        }
    }

    // ── Condition 3: Property formula quantifiers ────────────────────
    // The trigger/response must not quantify over the same entity type.
    // If they do, the property references multiple slots and the 1-slot
    // reduction would collapse that to a single slot — unsound.
    let (trigger, response) = match pattern {
        LivenessPattern::QuantifiedResponse {
            trigger, response, ..
        } => (Some(trigger), Some(response)),
        LivenessPattern::QuantifiedRecurrence { response, .. }
        | LivenessPattern::QuantifiedEventuality { response, .. } => (None, Some(response)),
        LivenessPattern::QuantifiedPersistence { condition, .. } => (None, Some(condition)),
        _ => (None, None),
    };
    if let Some(t) = trigger {
        if expr_quantifies_over_entity(t, entity_name) {
            return false;
        }
    }
    if let Some(r) = response {
        if expr_quantifies_over_entity(r, entity_name) {
            return false;
        }
    }

    true
}

/// Count Choose/ForAll references to `entity_name` in an action tree,
/// following `CrossCall` targets transitively into other systems.
fn count_entity_actions_with_crosscall(
    actions: &[IRAction],
    entity_name: &str,
    all_systems: &[IRSystem],
    count: &mut usize,
    visited_crosscalls: &mut HashSet<(String, String)>,
) {
    for action in actions {
        match action {
            IRAction::Choose { entity, ops, .. } => {
                if entity == entity_name {
                    *count += 1;
                }
                count_entity_actions_with_crosscall(
                    ops,
                    entity_name,
                    all_systems,
                    count,
                    visited_crosscalls,
                );
            }
            IRAction::ForAll { entity, ops, .. } => {
                if entity == entity_name {
                    *count += 1;
                }
                count_entity_actions_with_crosscall(
                    ops,
                    entity_name,
                    all_systems,
                    count,
                    visited_crosscalls,
                );
            }
            IRAction::CrossCall {
                system, command, ..
            }
            | IRAction::LetCrossCall {
                system, command, ..
            } => {
                let key = (system.clone(), command.clone());
                if visited_crosscalls.insert(key) {
                    // Follow into the CrossCall target's step body
                    if let Some(sys) = all_systems.iter().find(|s| s.name == *system) {
                        if let Some(step) = sys.actions.iter().find(|e| e.name == *command) {
                            count_entity_actions_with_crosscall(
                                &step.body,
                                entity_name,
                                all_systems,
                                count,
                                visited_crosscalls,
                            );
                        }
                    }
                }
            }
            IRAction::Match { scrutinee, arms } => {
                if let crate::ir::types::IRActionMatchScrutinee::CrossCall {
                    system, command, ..
                } = scrutinee
                {
                    let key = (system.clone(), command.clone());
                    if visited_crosscalls.insert(key) {
                        if let Some(sys) = all_systems.iter().find(|s| s.name == *system) {
                            if let Some(step) = sys.actions.iter().find(|e| e.name == *command) {
                                count_entity_actions_with_crosscall(
                                    &step.body,
                                    entity_name,
                                    all_systems,
                                    count,
                                    visited_crosscalls,
                                );
                            }
                        }
                    }
                }
                for arm in arms {
                    count_entity_actions_with_crosscall(
                        &arm.body,
                        entity_name,
                        all_systems,
                        count,
                        visited_crosscalls,
                    );
                }
            }
            _ => {}
        }
    }
}

/// Check whether an `IRExpr` contains any quantifier (Forall/Exists/One/Lone)
/// whose domain is the given entity type. This means the expression references
/// multiple slots of that entity, breaking the symmetry assumption.
fn expr_quantifies_over_entity(expr: &IRExpr, entity_name: &str) -> bool {
    match expr {
        IRExpr::Forall { domain, body, .. }
        | IRExpr::Exists { domain, body, .. }
        | IRExpr::One { domain, body, .. }
        | IRExpr::Lone { domain, body, .. } => {
            if matches!(domain, IRType::Entity { name } if name == entity_name) {
                return true;
            }
            expr_quantifies_over_entity(body, entity_name)
        }
        IRExpr::BinOp { left, right, .. } => {
            expr_quantifies_over_entity(left, entity_name)
                || expr_quantifies_over_entity(right, entity_name)
        }
        IRExpr::UnOp { operand, .. } | IRExpr::Field { expr: operand, .. } => {
            expr_quantifies_over_entity(operand, entity_name)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            expr_quantifies_over_entity(cond, entity_name)
                || expr_quantifies_over_entity(then_body, entity_name)
                || else_body
                    .as_ref()
                    .is_some_and(|e| expr_quantifies_over_entity(e, entity_name))
        }
        IRExpr::App { func, arg, .. } => {
            expr_quantifies_over_entity(func, entity_name)
                || expr_quantifies_over_entity(arg, entity_name)
        }
        IRExpr::Always { body, .. } | IRExpr::Eventually { body, .. } => {
            expr_quantifies_over_entity(body, entity_name)
        }
        IRExpr::SetComp {
            filter, projection, ..
        } => {
            expr_quantifies_over_entity(filter, entity_name)
                || projection
                    .as_ref()
                    .is_some_and(|p| expr_quantifies_over_entity(p, entity_name))
        }
        IRExpr::Until { left, right, .. } => {
            expr_quantifies_over_entity(left, entity_name)
                || expr_quantifies_over_entity(right, entity_name)
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            expr_quantifies_over_entity(scrutinee, entity_name)
                || arms
                    .iter()
                    .any(|a| expr_quantifies_over_entity(&a.body, entity_name))
        }
        IRExpr::Let { bindings, body, .. } => {
            bindings
                .iter()
                .any(|b| expr_quantifies_over_entity(&b.expr, entity_name))
                || expr_quantifies_over_entity(body, entity_name)
        }
        // Leaves: Lit, Var, Ctor, Lambda, SetLit, SeqLit, MapLit, etc.
        _ => false,
    }
}

/// Validate recursive `CrossCall` arities before encoding a scene.
///
/// This avoids panics in the harness and produces a user-facing `SceneFail`
/// reason pinpointing the mismatched call.
pub(super) fn validate_crosscall_arities(
    actions: &[IRAction],
    all_systems: &[crate::ir::types::IRSystem],
    depth: usize,
) -> Result<(), String> {
    if depth > 10 {
        return Ok(());
    }
    for action in actions {
        match action {
            IRAction::Choose { ops, .. } | IRAction::ForAll { ops, .. } => {
                validate_crosscall_arities(ops, all_systems, depth + 1)?;
            }
            IRAction::CrossCall {
                system,
                command,
                args,
            }
            | IRAction::LetCrossCall {
                system,
                command,
                args,
                ..
            } => {
                let Some(sys) = all_systems.iter().find(|s| s.name == *system) else {
                    return Err(format!("CrossCall target system not found: {system}"));
                };
                let matching_steps: Vec<_> =
                    sys.actions.iter().filter(|s| s.name == *command).collect();
                if matching_steps.is_empty() {
                    return Err(format!(
                        "CrossCall target command not found: {system}::{command}"
                    ));
                }
                for target_step in &matching_steps {
                    if target_step.params.len() != args.len() {
                        return Err(format!(
                            "CrossCall arity mismatch: {system}::{command} expects {} params but got {} args",
                            target_step.params.len(),
                            args.len()
                        ));
                    }
                    validate_crosscall_arities(&target_step.body, all_systems, depth + 1)?;
                }
            }
            IRAction::Match { scrutinee, arms } => {
                if let crate::ir::types::IRActionMatchScrutinee::CrossCall {
                    system,
                    command,
                    args,
                } = scrutinee
                {
                    let Some(sys) = all_systems.iter().find(|s| s.name == *system) else {
                        return Err(format!("CrossCall target system not found: {system}"));
                    };
                    let matching_steps: Vec<_> =
                        sys.actions.iter().filter(|s| s.name == *command).collect();
                    if matching_steps.is_empty() {
                        return Err(format!(
                            "CrossCall target command not found: {system}::{command}"
                        ));
                    }
                    for target_step in &matching_steps {
                        if target_step.params.len() != args.len() {
                            return Err(format!(
                                "CrossCall arity mismatch: {system}::{command} expects {} params but got {} args",
                                target_step.params.len(),
                                args.len()
                            ));
                        }
                        validate_crosscall_arities(&target_step.body, all_systems, depth + 1)?;
                    }
                }
                for arm in arms {
                    validate_crosscall_arities(&arm.body, all_systems, depth + 1)?;
                }
            }
            _ => {}
        }
    }
    Ok(())
}

pub(super) fn collect_crosscall_systems(actions: &[IRAction], targets: &mut Vec<String>) {
    for action in actions {
        match action {
            IRAction::CrossCall { system, .. } | IRAction::LetCrossCall { system, .. } => {
                if !targets.contains(system) {
                    targets.push(system.clone());
                }
            }
            IRAction::Apply { target, .. } => {
                if !targets.contains(target) {
                    targets.push(target.clone());
                }
            }
            IRAction::Choose { ops, .. } | IRAction::ForAll { ops, .. } => {
                collect_crosscall_systems(ops, targets);
            }
            IRAction::Match { scrutinee, arms } => {
                if let crate::ir::types::IRActionMatchScrutinee::CrossCall { system, .. } =
                    scrutinee
                {
                    if !targets.contains(system) {
                        targets.push(system.clone());
                    }
                }
                for arm in arms {
                    collect_crosscall_systems(&arm.body, targets);
                }
            }
            _ => {}
        }
    }
}

pub(super) fn collect_saw_systems_expr(expr: &IRExpr, targets: &mut Vec<String>) {
    match expr {
        IRExpr::Saw {
            system_name, args, ..
        } => {
            if !targets.contains(system_name) {
                targets.push(system_name.clone());
            }
            for arg in args.iter().flatten() {
                collect_saw_systems_expr(arg, targets);
            }
        }
        IRExpr::UnOp { operand, .. }
        | IRExpr::Always { body: operand, .. }
        | IRExpr::Eventually { body: operand, .. }
        | IRExpr::Historically { body: operand, .. }
        | IRExpr::Once { body: operand, .. }
        | IRExpr::Previously { body: operand, .. }
        | IRExpr::Prime { expr: operand, .. }
        | IRExpr::Field { expr: operand, .. }
        | IRExpr::Assert { expr: operand, .. }
        | IRExpr::Assume { expr: operand, .. }
        | IRExpr::Card { expr: operand, .. }
        | IRExpr::Lam { body: operand, .. } => collect_saw_systems_expr(operand, targets),
        IRExpr::BinOp { left, right, .. }
        | IRExpr::Until { left, right, .. }
        | IRExpr::Since { left, right, .. }
        | IRExpr::Index {
            map: left,
            key: right,
            ..
        } => {
            collect_saw_systems_expr(left, targets);
            collect_saw_systems_expr(right, targets);
        }
        IRExpr::Forall { body, .. }
        | IRExpr::Exists { body, .. }
        | IRExpr::One { body, .. }
        | IRExpr::Lone { body, .. } => collect_saw_systems_expr(body, targets),
        IRExpr::Choose { predicate, .. } => {
            if let Some(predicate) = predicate {
                collect_saw_systems_expr(predicate, targets);
            }
        }
        IRExpr::App { func, arg, .. } => {
            collect_saw_systems_expr(func, targets);
            collect_saw_systems_expr(arg, targets);
        }
        IRExpr::Let { bindings, body, .. } => {
            for binding in bindings {
                collect_saw_systems_expr(&binding.expr, targets);
            }
            collect_saw_systems_expr(body, targets);
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            collect_saw_systems_expr(scrutinee, targets);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_saw_systems_expr(guard, targets);
                }
                collect_saw_systems_expr(&arm.body, targets);
            }
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            collect_saw_systems_expr(map, targets);
            collect_saw_systems_expr(key, targets);
            collect_saw_systems_expr(value, targets);
        }
        IRExpr::SetComp {
            projection, filter, ..
        } => {
            if let Some(proj) = projection {
                collect_saw_systems_expr(proj, targets);
            }
            collect_saw_systems_expr(filter, targets);
        }
        IRExpr::RelComp {
            projection,
            bindings,
            filter,
            ..
        } => {
            collect_saw_systems_expr(projection, targets);
            for binding in bindings {
                if let Some(source) = &binding.source {
                    collect_saw_systems_expr(source, targets);
                }
            }
            collect_saw_systems_expr(filter, targets);
        }
        IRExpr::SetLit { elements, .. } | IRExpr::SeqLit { elements, .. } => {
            for element in elements {
                collect_saw_systems_expr(element, targets);
            }
        }
        IRExpr::MapLit { entries, .. } => {
            for (key, value) in entries {
                collect_saw_systems_expr(key, targets);
                collect_saw_systems_expr(value, targets);
            }
        }
        IRExpr::Ctor { args, .. } => {
            for (_, arg) in args {
                collect_saw_systems_expr(arg, targets);
            }
        }
        IRExpr::Aggregate {
            body, in_filter, ..
        } => {
            collect_saw_systems_expr(body, targets);
            if let Some(filter) = in_filter {
                collect_saw_systems_expr(filter, targets);
            }
        }
        IRExpr::Block { exprs, .. } => {
            for expr in exprs {
                collect_saw_systems_expr(expr, targets);
            }
        }
        IRExpr::VarDecl { init, rest, .. } => {
            collect_saw_systems_expr(init, targets);
            collect_saw_systems_expr(rest, targets);
        }
        IRExpr::While {
            cond,
            invariants,
            body,
            ..
        } => {
            collect_saw_systems_expr(cond, targets);
            for invariant in invariants {
                collect_saw_systems_expr(invariant, targets);
            }
            collect_saw_systems_expr(body, targets);
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            collect_saw_systems_expr(cond, targets);
            collect_saw_systems_expr(then_body, targets);
            if let Some(else_body) = else_body {
                collect_saw_systems_expr(else_body, targets);
            }
        }
        IRExpr::Var { .. } | IRExpr::Lit { .. } | IRExpr::Sorry { .. } | IRExpr::Todo { .. } => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::types::{
        IRActionMatchArm, IRAssumptionSet, IRField, IRInvariant, IRLetBinding, IRMatchArm,
        IRPattern, IRStoreDecl, IRTransParam, LetBinding, LitVal,
    };

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

    fn entity(name: &str) -> IREntity {
        IREntity {
            name: name.to_owned(),
            fields: vec![IRField {
                name: "ok".to_owned(),
                ty: IRType::Bool,
                default: Some(bool_lit(true)),
                initial_constraint: None,
            }],
            transitions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        }
    }

    fn step(name: &str, body: Vec<IRAction>) -> crate::ir::types::IRSystemAction {
        crate::ir::types::IRSystemAction {
            name: name.to_owned(),
            params: vec![],
            guard: bool_lit(true),
            body,
            return_expr: None,
        }
    }

    fn system(
        name: &str,
        entities: Vec<&str>,
        actions: Vec<crate::ir::types::IRSystemAction>,
    ) -> IRSystem {
        IRSystem {
            name: name.to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: entities.into_iter().map(str::to_owned).collect(),
            commands: vec![],
            actions,
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        }
    }

    fn program(entities: Vec<IREntity>, systems: Vec<IRSystem>) -> IRProgram {
        IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities,
            systems,
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        }
    }

    #[test]
    fn compute_verify_scope_tracks_store_ranges_depth_and_reachable_systems() {
        let callee = system("Audit", vec!["Log"], vec![]);
        let mut caller = system(
            "Orders",
            vec!["Order"],
            vec![step(
                "submit",
                vec![IRAction::CrossCall {
                    system: "Audit".to_owned(),
                    command: "record".to_owned(),
                    args: vec![],
                }],
            )],
        );
        caller.let_bindings.push(IRLetBinding {
            name: "audit".to_owned(),
            system_type: "Audit".to_owned(),
            store_bindings: vec![],
        });
        let ir = program(vec![entity("Order"), entity("Log")], vec![caller, callee]);
        let verify = IRVerify {
            name: "safety".to_owned(),
            depth: Some(5),
            systems: vec![crate::ir::types::IRVerifySystem {
                name: "Orders".to_owned(),
                lo: 0,
                hi: 2,
            }],
            stores: vec![
                IRStoreDecl {
                    name: "pending".to_owned(),
                    entity_type: "Order".to_owned(),
                    lo: 1,
                    hi: 2,
                },
                IRStoreDecl {
                    name: "archived".to_owned(),
                    entity_type: "Order".to_owned(),
                    lo: 0,
                    hi: 3,
                },
            ],
            assumption_set: IRAssumptionSet::default_for_verify(),
            asserts: vec![IRExpr::Saw {
                system_name: "Audit".to_owned(),
                event_name: "record".to_owned(),
                args: vec![],
                span: None,
            }],
            span: None,
            file: None,
        };

        let (scope, systems, bound, ranges) = compute_verify_scope(&ir, &verify);

        assert_eq!(scope.get("Order"), Some(&5));
        assert_eq!(scope.get("Log"), Some(&5));
        assert_eq!(bound, 5);
        assert!(systems.contains(&"Orders".to_owned()));
        assert!(systems.contains(&"Audit".to_owned()));
        assert_eq!(ranges["pending"].start_slot, 0);
        assert_eq!(ranges["pending"].slot_count, 2);
        assert_eq!(ranges["pending"].min_active, 1);
        assert_eq!(ranges["pending"].max_active, 2);
        assert_eq!(ranges["archived"].start_slot, 2);
        assert_eq!(ranges["archived"].slot_count, 3);
        assert_eq!(ranges["archived"].min_active, 0);
        assert_eq!(ranges["archived"].max_active, 3);
    }

    #[test]
    fn collect_in_scope_invariants_wraps_entity_and_target_system_invariants() {
        let mut ent = entity("Order");
        ent.invariants.push(IRInvariant {
            name: "ok".to_owned(),
            body: bool_var("ok"),
        });
        let mut target = system("Orders", vec!["Order"], vec![]);
        target.invariants.push(IRInvariant {
            name: "sys_ok".to_owned(),
            body: bool_lit(true),
        });
        let defs = defenv::DefEnv::from_ir(&program(vec![ent.clone()], vec![target.clone()]));

        let invariants = collect_in_scope_invariants(&defs, &[ent], &[target]);

        assert_eq!(invariants.len(), 2);
        assert!(matches!(invariants[0], IRExpr::Always { .. }));
        assert!(matches!(invariants[1], IRExpr::Always { .. }));
    }

    #[test]
    fn validate_symmetry_rejects_nested_actions_crosscalls_and_property_quantifiers() {
        let nested = system(
            "Orders",
            vec!["Order"],
            vec![step(
                "touch",
                vec![IRAction::Choose {
                    var: "a".to_owned(),
                    entity: "Order".to_owned(),
                    filter: Box::new(bool_lit(true)),
                    ops: vec![IRAction::ForAll {
                        var: "b".to_owned(),
                        entity: "Order".to_owned(),
                        ops: vec![],
                    }],
                }],
            )],
        );
        let pattern = LivenessPattern::QuantifiedRecurrence {
            var: "o".to_owned(),
            entity: "Order".to_owned(),
            response: bool_var("ok"),
        };
        assert!(!validate_symmetry(
            "Order",
            std::slice::from_ref(&nested),
            std::slice::from_ref(&nested),
            &pattern
        ));

        let caller = system(
            "Caller",
            vec!["Order"],
            vec![step(
                "call",
                vec![IRAction::Match {
                    scrutinee: crate::ir::types::IRActionMatchScrutinee::CrossCall {
                        system: "Callee".to_owned(),
                        command: "touch".to_owned(),
                        args: vec![],
                    },
                    arms: vec![IRActionMatchArm {
                        pattern: IRPattern::PWild,
                        guard: None,
                        body: vec![],
                    }],
                }],
            )],
        );
        let callee = system(
            "Callee",
            vec!["Order"],
            vec![step(
                "touch",
                vec![IRAction::Choose {
                    var: "o".to_owned(),
                    entity: "Order".to_owned(),
                    filter: Box::new(bool_lit(true)),
                    ops: vec![],
                }],
            )],
        );
        assert!(validate_symmetry(
            "Order",
            std::slice::from_ref(&caller),
            &[caller.clone(), callee],
            &pattern
        ));

        let quantified_pattern = LivenessPattern::QuantifiedResponse {
            var: "o".to_owned(),
            entity: "Order".to_owned(),
            trigger: IRExpr::Exists {
                var: "other".to_owned(),
                domain: IRType::Entity {
                    name: "Order".to_owned(),
                },
                body: Box::new(bool_lit(true)),
                span: None,
            },
            response: bool_lit(true),
        };
        assert!(!validate_symmetry(
            "Order",
            std::slice::from_ref(&caller),
            std::slice::from_ref(&caller),
            &quantified_pattern
        ));
    }

    #[test]
    fn validate_crosscall_arities_reports_missing_targets_and_nested_mismatch() {
        let target = crate::ir::types::IRSystemAction {
            name: "record".to_owned(),
            params: vec![IRTransParam {
                name: "id".to_owned(),
                ty: IRType::Int,
            }],
            guard: bool_lit(true),
            body: vec![],
            return_expr: None,
        };
        let audit = system("Audit", vec![], vec![target]);
        let err = validate_crosscall_arities(
            &[IRAction::CrossCall {
                system: "Audit".to_owned(),
                command: "record".to_owned(),
                args: vec![],
            }],
            std::slice::from_ref(&audit),
            0,
        )
        .expect_err("arity mismatch");
        assert!(err.contains("expects 1 params"));

        let missing = validate_crosscall_arities(
            &[IRAction::LetCrossCall {
                name: "x".to_owned(),
                system: "Missing".to_owned(),
                command: "record".to_owned(),
                args: vec![],
            }],
            &[audit],
            0,
        )
        .expect_err("missing target system");
        assert!(missing.contains("target system not found"));
    }

    #[test]
    fn collect_saw_systems_expr_walks_recursive_expression_shapes() {
        let saw = IRExpr::Saw {
            system_name: "Audit".to_owned(),
            event_name: "record".to_owned(),
            args: vec![Some(Box::new(IRExpr::Saw {
                system_name: "Nested".to_owned(),
                event_name: "seen".to_owned(),
                args: vec![],
                span: None,
            }))],
            span: None,
        };
        let expr = IRExpr::Match {
            scrutinee: Box::new(IRExpr::Let {
                bindings: vec![LetBinding {
                    name: "x".to_owned(),
                    ty: IRType::Bool,
                    expr: saw,
                }],
                body: Box::new(bool_var("x")),
                span: None,
            }),
            arms: vec![IRMatchArm {
                pattern: IRPattern::PWild,
                guard: Some(IRExpr::MapUpdate {
                    map: Box::new(IRExpr::MapLit {
                        entries: vec![],
                        ty: IRType::Map {
                            key: Box::new(IRType::Int),
                            value: Box::new(IRType::Bool),
                        },
                        span: None,
                    }),
                    key: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },
                        span: None,
                    }),
                    value: Box::new(IRExpr::Saw {
                        system_name: "Guard".to_owned(),
                        event_name: "hit".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    ty: IRType::Map {
                        key: Box::new(IRType::Int),
                        value: Box::new(IRType::Bool),
                    },
                    span: None,
                }),
                body: IRExpr::SetComp {
                    var: "v".to_owned(),
                    domain: IRType::Bool,
                    source: None,
                    filter: Box::new(IRExpr::Saw {
                        system_name: "Body".to_owned(),
                        event_name: "hit".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    projection: None,
                    ty: IRType::Set {
                        element: Box::new(IRType::Bool),
                    },
                    span: None,
                },
            }],
            span: None,
        };
        let mut targets = Vec::new();

        collect_saw_systems_expr(&expr, &mut targets);

        assert_eq!(targets, vec!["Audit", "Nested", "Guard", "Body"]);
    }
}
