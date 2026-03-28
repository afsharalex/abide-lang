//! Verification backend — connects Abide IR to Z3.
//!
//! Architecture:
//! - `smt`: Z3 value types and sort mapping
//! - `context`: `VerifyContext` (variant IDs, field metadata, entity pool info)
//! - `encode`: IR → Z3 term encoding (expressions)
//! - `harness`: Multi-slot entity pools, action/event encoding, constraint generation
//! - `mod`: Top-level BMC entry point (`verify_all`, `check_verify_block`)

pub mod context;
pub mod defenv;
pub mod encode;
pub mod harness;
pub mod smt;

use std::collections::{HashMap, HashSet};
use std::time::Instant;

use z3::ast::Bool;
use z3::Solver;

use crate::ir::types::{IRAction, IRExpr, IRProgram, IRScene, IRVerify};

use self::context::VerifyContext;
use self::harness::{
    create_slot_pool, domain_constraints, encode_event_with_params, initial_state_constraints,
    transition_constraints, SlotPool,
};
use self::smt::SmtValue;

// ── Verification results ────────────────────────────────────────────

/// Result of checking a single verification target.
#[derive(Debug)]
pub enum VerificationResult {
    /// Property proved inductively (unbounded, all sizes).
    Proved {
        name: String,
        method: String,
        time_ms: u64,
    },
    /// Property checked to a bounded depth (no counterexample found).
    Checked {
        name: String,
        depth: usize,
        time_ms: u64,
    },
    /// Counterexample found — a trace of events that violates the property.
    Counterexample { name: String, trace: Vec<TraceStep> },
    /// Scene passed — the scenario is satisfiable and assertions hold.
    ScenePass { name: String, time_ms: u64 },
    /// Scene failed — the scenario is unsatisfiable or assertions violated.
    SceneFail { name: String, reason: String },
    /// Could not prove automatically — needs manual proof.
    Unprovable { name: String, hint: String },
}

/// A single step in a counterexample trace.
#[derive(Debug)]
pub struct TraceStep {
    pub step: usize,
    pub event: Option<String>,
    pub assignments: Vec<(String, String, String)>, // (entity, field, value)
}

// ── Top-level verification entry point ──────────────────────────────

/// Verify all targets in an IR program.
///
/// Processes verify blocks (bounded model checking) and scene blocks (SAT).
/// Returns one result per target.
pub fn verify_all(ir: &IRProgram) -> Vec<VerificationResult> {
    let vctx = context::VerifyContext::from_ir(ir);
    let defs = defenv::DefEnv::from_ir(ir);
    let mut results = Vec::new();

    for verify_block in &ir.verifies {
        results.push(check_verify_block(ir, &vctx, &defs, verify_block));
    }

    for scene_block in &ir.scenes {
        results.push(check_scene_block(ir, &vctx, &defs, scene_block));
    }

    results
}

/// Elapsed time in milliseconds, saturating to `u64::MAX`.
#[allow(clippy::cast_possible_truncation)]
fn elapsed_ms(start: &Instant) -> u64 {
    start.elapsed().as_millis().min(u128::from(u64::MAX)) as u64
}

// ── BMC check for a single verify block ─────────────────────────────

/// Run bounded model checking on a single verify block.
///
/// 1. Build scope: `entity_name` → slot count from verify systems
/// 2. Create `SlotPool` with scope and bound
/// 3. Assert initial state, domain, and transition constraints
/// 4. Encode properties at every step
/// 5. Negate to search for counterexample
/// 6. UNSAT → CHECKED, SAT → COUNTEREXAMPLE
fn check_verify_block(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    verify_block: &IRVerify,
) -> VerificationResult {
    let start = Instant::now();

    // ── 1. Build scope: entity_name → max slot count ───────────────
    let mut scope: HashMap<String, usize> = HashMap::new();
    let mut bound: usize = 1; // default depth
    let mut system_names: Vec<String> = Vec::new();

    for vs in &verify_block.systems {
        system_names.push(vs.name.clone());
        #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
        let hi = vs.hi.max(1) as usize;
        bound = bound.max(hi);

        // Find the system's entities and add them to scope
        if let Some(sys) = ir.systems.iter().find(|s| s.name == vs.name) {
            for ent_name in &sys.entities {
                let existing = scope.get(ent_name).copied().unwrap_or(0);
                scope.insert(ent_name.clone(), existing.max(hi));
            }
        }
    }

    // If scope is empty (no systems found), return early
    if scope.is_empty() {
        let elapsed = elapsed_ms(&start);
        return VerificationResult::Checked {
            name: verify_block.name.clone(),
            depth: bound,
            time_ms: elapsed,
        };
    }

    // ── 1b. Expand scope to include CrossCall-reachable systems ────
    // Systems called via CrossCall must be included even if not in verify targets.
    // Walk all events in target systems and collect CrossCall targets transitively.
    let mut systems_to_scan = system_names.clone();
    let mut scanned: HashSet<String> = HashSet::new();
    while let Some(sys_name) = systems_to_scan.pop() {
        if !scanned.insert(sys_name.clone()) {
            continue;
        }
        if let Some(sys) = ir.systems.iter().find(|s| s.name == sys_name) {
            for event in &sys.events {
                collect_crosscall_systems(&event.body, &mut systems_to_scan);
            }
            // Add this system's entities to scope if not already present
            if !system_names.contains(&sys.name) {
                system_names.push(sys.name.clone());
            }
            for ent_name in &sys.entities {
                let existing = scope.get(ent_name).copied().unwrap_or(0);
                scope.insert(ent_name.clone(), existing.max(bound));
            }
        }
    }

    // ── 2. Collect relevant entities and systems ───────────────────
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

    // ── 3. Create slot pool ────────────────────────────────────────
    let pool = create_slot_pool(&relevant_entities, &scope, bound);

    // ── 4. Build solver and assert constraints ─────────────────────
    let solver = Solver::new();

    // Initial state: all slots inactive at step 0
    for c in initial_state_constraints(&pool) {
        solver.assert(&c);
    }

    // Domain constraints at every step
    for c in domain_constraints(&pool, vctx, &relevant_entities) {
        solver.assert(&c);
    }

    // Transition constraints at every step 0..bound-1
    for step in 0..bound {
        let trans =
            transition_constraints(&pool, vctx, &relevant_entities, &relevant_systems, step);
        solver.assert(&trans);
    }

    // ── 5. Encode properties and search for counterexample ─────────
    // For `always P`: check that P holds at every step 0..bound.
    // We negate: assert exists some step where P does NOT hold.
    // If UNSAT → property holds at all steps (CHECKED).
    // If SAT → counterexample found.
    let property_at_all_steps =
        encode_verify_properties(&pool, vctx, defs, &verify_block.asserts, bound);

    // Negate the conjunction of all properties across all steps
    solver.assert(property_at_all_steps.not());

    // ── 6. Check and return result ─────────────────────────────────
    let elapsed = elapsed_ms(&start);

    match solver.check() {
        z3::SatResult::Unsat => VerificationResult::Checked {
            name: verify_block.name.clone(),
            depth: bound,
            time_ms: elapsed,
        },
        z3::SatResult::Sat => {
            let trace = extract_counterexample(&solver, &pool, &relevant_entities, bound);
            VerificationResult::Counterexample {
                name: verify_block.name.clone(),
                trace,
            }
        }
        z3::SatResult::Unknown => VerificationResult::Unprovable {
            name: verify_block.name.clone(),
            hint: "Z3 returned unknown — try reducing bound or simplifying property".to_owned(),
        },
    }
}

// ── Scene checking (SAT) ────────────────────────────────────────────

/// Check a scene block by encoding given/when/then as a SAT problem.
///
/// Scenes are existential: "does there exist an execution matching
/// given+when that satisfies then?" This is the dual of verify blocks
/// (which are universal).
///
/// 1. Build scope and pool from scene systems
/// 2. Given: activate one slot per binding, constrain fields at step 0
/// 3. When: encode each event at its step (ordering from assume)
/// 4. Then: assert all then-expressions at the final step
/// 5. SAT → `ScenePass`, UNSAT → `SceneFail`
#[allow(clippy::too_many_lines)]
fn check_scene_block(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    scene: &IRScene,
) -> VerificationResult {
    let start = Instant::now();
    let n_events = scene.events.len();

    // ── 1. Build scope from scene systems ──────────────────────────
    // Each given binding needs one slot. Each entity type referenced
    // needs at least as many slots as given bindings of that type.
    let mut scope: HashMap<String, usize> = HashMap::new();
    let mut system_names: Vec<String> = scene.systems.clone();

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

    // Expand from systems — ensure all system entities are in scope.
    // Also follow CrossCalls transitively. Non-given entities need enough
    // slots for creates during the scenario (each event may create one instance).
    let default_slots = n_events.max(1);
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
            for event in &sys.events {
                collect_crosscall_systems(&event.body, &mut systems_to_scan);
            }
            for ent_name in &sys.entities {
                scope.entry(ent_name.clone()).or_insert(default_slots);
            }
        }
    }

    if scope.is_empty() {
        return VerificationResult::SceneFail {
            name: scene.name.clone(),
            reason: "no systems or entities found".to_owned(),
        };
    }

    // Bound = number of events (each event is one step)
    let bound = n_events;

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
    let pool = create_slot_pool(&relevant_entities, &scope, bound);
    let solver = Solver::new();

    // Domain constraints at every step
    for c in domain_constraints(&pool, vctx, &relevant_entities) {
        solver.assert(&c);
    }

    // ── 3. Encode given bindings ───────────────────────────────────
    // Each given binding activates one slot at step 0 and constrains its fields.
    // Track which slot each given variable is bound to.
    let mut given_bindings: HashMap<String, (String, usize)> = HashMap::new(); // var → (entity, slot)
    let mut next_slot: HashMap<String, usize> = HashMap::new(); // entity → next available slot

    for given in &scene.givens {
        if let Some(kind) = find_unsupported_scene_expr(&given.constraint) {
            return VerificationResult::SceneFail {
                name: scene.name.clone(),
                reason: format!(
                    "unsupported expression kind in scene given for {}: {kind}",
                    given.var
                ),
            };
        }
    }

    for given in &scene.givens {
        let slot = next_slot.entry(given.entity.clone()).or_insert(0);
        let current_slot = *slot;
        *slot += 1;

        // Activate this slot at step 0
        if let Some(SmtValue::Bool(active)) = pool.active_at(&given.entity, current_slot, 0) {
            solver.assert(active);
        }

        // Encode the given constraint on this slot's fields at step 0
        let given_ctx = PropertyCtx::new().with_binding(&given.var, &given.entity, current_slot);
        let constraint = encode_prop_expr(&pool, vctx, defs, &given_ctx, &given.constraint, 0);
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
                    let default_ctx = harness::SlotEncodeCtx {
                        pool: &pool,
                        vctx,
                        entity: &given.entity,
                        slot: current_slot,
                        params: HashMap::new(),
                        bindings: HashMap::new(),
                    };
                    let val = harness::encode_slot_expr(&default_ctx, default_expr, 0);
                    if let Some(field_var) =
                        pool.field_at(&given.entity, current_slot, &field.name, 0)
                    {
                        match (&val, field_var) {
                            (SmtValue::Int(v), SmtValue::Int(f)) => solver.assert(f.eq(v.clone())),
                            (SmtValue::Bool(v), SmtValue::Bool(f)) => {
                                solver.assert(f.eq(v.clone()));
                            }
                            (SmtValue::Real(v), SmtValue::Real(f)) => {
                                solver.assert(f.eq(v.clone()));
                            }
                            _ => {} // skip Dynamic
                        }
                    }
                }
            }
        }

        given_bindings.insert(given.var.clone(), (given.entity.clone(), current_slot));
    }

    // Deactivate all other slots at step 0
    for entity in &relevant_entities {
        let n_slots = pool.slots_for(&entity.name);
        let used = next_slot.get(&entity.name).copied().unwrap_or(0);
        for slot in used..n_slots {
            if let Some(SmtValue::Bool(active)) = pool.active_at(&entity.name, slot, 0) {
                solver.assert(active.not());
            }
        }
    }

    // ── 4a. Validate scene events and determine referenced vars ────
    // Reject unsupported cardinalities and validate arity up front.
    for scene_event in &scene.events {
        // Only {one} cardinality is supported for scenes
        match &scene_event.cardinality {
            crate::ir::types::Cardinality::Named(c) if c == "one" => {}
            crate::ir::types::Cardinality::Exact { exactly: 1 } => {}
            other => {
                return VerificationResult::SceneFail {
                    name: scene.name.clone(),
                    reason: format!(
                        "unsupported cardinality {other:?} for scene event {}::{}; \
                         only {{one}} is supported",
                        scene_event.system, scene_event.event
                    ),
                };
            }
        }
    }

    // Scene ordering (assume blocks) is implicit from event list position.
    // The assume expressions in scene.ordering are redundant for linear chains
    // (a -> b -> c matches event list order). Non-linear ordering is not yet
    // supported but the common linear case works correctly by construction.

    for assertion in &scene.assertions {
        if let Some(kind) = find_unsupported_scene_expr(assertion) {
            return VerificationResult::SceneFail {
                name: scene.name.clone(),
                reason: format!("unsupported expression kind in scene then assertion: {kind}"),
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

    // ── 4b. Encode when events ──────────────────────────────────────
    // Each event fires at its step index (0-based).
    for (step, scene_event) in scene.events.iter().enumerate() {
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
            };
        };
        let Some(event) = sys.events.iter().find(|e| e.name == scene_event.event) else {
            return VerificationResult::SceneFail {
                name: scene.name.clone(),
                reason: format!(
                    "event {} not found in system {}",
                    scene_event.event, scene_event.system
                ),
            };
        };

        // Validate arity: scene args must match event params
        if scene_event.args.len() != event.params.len() {
            return VerificationResult::SceneFail {
                name: scene.name.clone(),
                reason: format!(
                    "arity mismatch: scene provides {} args for {}::{} but event expects {} params",
                    scene_event.args.len(),
                    scene_event.system,
                    scene_event.event,
                    event.params.len()
                ),
            };
        }

        for arg in &scene_event.args {
            if let Some(kind) = find_unsupported_scene_expr(arg) {
                return VerificationResult::SceneFail {
                    name: scene.name.clone(),
                    reason: format!(
                        "unsupported expression kind in scene event arg for {}::{}: {kind}",
                        scene_event.system, scene_event.event
                    ),
                };
            }
        }

        if let Err(reason) = validate_crosscall_arities(&event.body, &relevant_systems, 0) {
            return VerificationResult::SceneFail {
                name: scene.name.clone(),
                reason,
            };
        }

        // Build override_params: resolve scene event args against current bindings.
        let mut override_params: HashMap<String, SmtValue> = HashMap::new();
        for (param, arg) in event.params.iter().zip(scene_event.args.iter()) {
            let arg_ctx = PropertyCtx::new();
            let arg_ctx = given_bindings
                .iter()
                .fold(arg_ctx, |ctx, (var, (ent, slot))| {
                    ctx.with_binding(var, ent, *slot)
                });
            let val = encode_prop_value(&pool, vctx, defs, &arg_ctx, arg, step);
            override_params.insert(param.name.clone(), val);
        }

        // Encode this specific event at this step with resolved params
        let event_formula = encode_event_with_params(
            &pool,
            vctx,
            &relevant_entities,
            &relevant_systems,
            event,
            step,
            override_params,
        );
        solver.assert(&event_formula);

        // If this var is referenced by subsequent events, determine the result
        // entity and bind it. Scan the event body (and CrossCalls) for Creates.
        if referenced_vars.contains(&scene_event.var) {
            let creates = scan_event_creates(&event.body, &relevant_systems);
            if let Some(result_entity) = creates.first() {
                // Pre-allocate next slot of this entity type
                let slot = next_slot.entry(result_entity.clone()).or_insert(0);
                let allocated_slot = *slot;
                *slot += 1;

                // Constrain: this slot was activated during this step
                // (inactive at step → active at step+1)
                if let Some(SmtValue::Bool(active_next)) =
                    pool.active_at(result_entity, allocated_slot, step + 1)
                {
                    solver.assert(active_next);
                }

                // Bind the scene var to this slot
                given_bindings.insert(
                    scene_event.var.clone(),
                    (result_entity.clone(), allocated_slot),
                );
            }
        }
    }

    // ── 5. Encode then assertions at final step ────────────────────
    let final_step = bound; // after all events
    let mut then_ctx = PropertyCtx::new();
    for (var, (entity, slot)) in &given_bindings {
        then_ctx = then_ctx.with_binding(var, entity, *slot);
    }

    for assertion in &scene.assertions {
        let prop = encode_prop_expr(&pool, vctx, defs, &then_ctx, assertion, final_step);
        solver.assert(&prop);
    }

    // ── 6. Check SAT ───────────────────────────────────────────────
    let elapsed = elapsed_ms(&start);

    match solver.check() {
        z3::SatResult::Sat => VerificationResult::ScenePass {
            name: scene.name.clone(),
            time_ms: elapsed,
        },
        z3::SatResult::Unsat => VerificationResult::SceneFail {
            name: scene.name.clone(),
            reason: "scenario is unsatisfiable — no execution matches given+when+then".to_owned(),
        },
        z3::SatResult::Unknown => VerificationResult::SceneFail {
            name: scene.name.clone(),
            reason: "Z3 returned unknown".to_owned(),
        },
    }
}

// ── Property encoding context ────────────────────────────────────────

/// Tracks quantifier-bound variables mapping `var_name` → (`entity_name`, `slot_index`).
///
/// When encoding nested multi-entity quantifiers like
/// `all s: Session | all u: User | u.status == @Locked and s.user_id == u.id`
/// the context accumulates bindings for each enclosing quantifier so that
/// field references from ANY bound entity can be resolved correctly.
struct PropertyCtx {
    /// Quantifier-bound variables: `var_name` → (`entity_name`, `slot_index`)
    bindings: HashMap<String, (String, usize)>,
}

impl PropertyCtx {
    fn new() -> Self {
        Self {
            bindings: HashMap::new(),
        }
    }

    /// Create a new context with an additional binding.
    fn with_binding(&self, var: &str, entity: &str, slot: usize) -> Self {
        let mut bindings = self.bindings.clone();
        bindings.insert(var.to_owned(), (entity.to_owned(), slot));
        Self { bindings }
    }
}

// ── Property encoding for BMC ───────────────────────────────────────

/// Encode all verify assertions across all BMC steps.
///
/// For `always P`: P must hold at every step 0..=bound.
/// For plain assertions: evaluated at every step.
/// Collect system names referenced by `CrossCall` actions, recursively.
fn collect_crosscall_systems(actions: &[IRAction], targets: &mut Vec<String>) {
    for action in actions {
        match action {
            IRAction::CrossCall { system, .. } => {
                if !targets.contains(system) {
                    targets.push(system.clone());
                }
            }
            IRAction::Choose { ops, .. } | IRAction::ForAll { ops, .. } => {
                collect_crosscall_systems(ops, targets);
            }
            _ => {}
        }
    }
}

/// Scan an event body (and `CrossCall` targets) for Create actions.
/// Returns the entity types created, in order of first appearance.
fn scan_event_creates(
    actions: &[IRAction],
    all_systems: &[crate::ir::types::IRSystem],
) -> Vec<String> {
    let mut creates = Vec::new();
    scan_event_creates_inner(actions, all_systems, &mut creates, 0);
    creates
}

fn scan_event_creates_inner(
    actions: &[IRAction],
    all_systems: &[crate::ir::types::IRSystem],
    creates: &mut Vec<String>,
    depth: usize,
) {
    if depth > 10 {
        return; // prevent infinite recursion on cyclic CrossCalls
    }
    for action in actions {
        match action {
            IRAction::Create { entity, .. } => {
                if !creates.contains(entity) {
                    creates.push(entity.clone());
                }
            }
            IRAction::Choose { ops, .. } | IRAction::ForAll { ops, .. } => {
                scan_event_creates_inner(ops, all_systems, creates, depth);
            }
            IRAction::CrossCall {
                system,
                event: event_name,
                ..
            } => {
                if let Some(sys) = all_systems.iter().find(|s| s.name == *system) {
                    if let Some(ev) = sys.events.iter().find(|e| e.name == *event_name) {
                        scan_event_creates_inner(&ev.body, all_systems, creates, depth + 1);
                    }
                }
            }
            _ => {}
        }
    }
}

/// Expand an IR expression through the `DefEnv` — replace Var refs matching
/// nullary defs with their bodies, and App chains matching parameterized defs
/// with their beta-reduced bodies. Used to resolve pred/prop references in
/// given constraints before scanning for field references.
fn expand_through_defs(expr: &IRExpr, defs: &defenv::DefEnv) -> IRExpr {
    if let IRExpr::Var { name, .. } = expr {
        if let Some(expanded) = defs.expand_var(name) {
            return expand_through_defs(&expanded, defs);
        }
    }
    if let IRExpr::App { .. } = expr {
        if let Some(expanded) = defs.expand_app(expr) {
            return expand_through_defs(&expanded, defs);
        }
    }
    match expr {
        IRExpr::BinOp {
            op,
            left,
            right,
            ty,
        } => IRExpr::BinOp {
            op: op.clone(),
            left: Box::new(expand_through_defs(left, defs)),
            right: Box::new(expand_through_defs(right, defs)),
            ty: ty.clone(),
        },
        IRExpr::UnOp { op, operand, ty } => IRExpr::UnOp {
            op: op.clone(),
            operand: Box::new(expand_through_defs(operand, defs)),
            ty: ty.clone(),
        },
        IRExpr::Forall { var, domain, body } => IRExpr::Forall {
            var: var.clone(),
            domain: domain.clone(),
            body: Box::new(expand_through_defs(body, defs)),
        },
        IRExpr::Exists { var, domain, body } => IRExpr::Exists {
            var: var.clone(),
            domain: domain.clone(),
            body: Box::new(expand_through_defs(body, defs)),
        },
        _ => expr.clone(),
    }
}

/// Collect field names referenced as `Field(Var(var_name), field)` in an expression.
/// Used to determine which entity fields are explicitly constrained by a given block
/// so that defaults are only applied to unconstrained fields.
fn collect_field_refs_in_expr(expr: &IRExpr, var_name: &str, fields: &mut HashSet<String>) {
    match expr {
        IRExpr::Field {
            expr: inner, field, ..
        } => {
            if let IRExpr::Var { name, .. } = inner.as_ref() {
                if name == var_name {
                    fields.insert(field.clone());
                }
            }
            collect_field_refs_in_expr(inner, var_name, fields);
        }
        IRExpr::BinOp { left, right, .. } => {
            collect_field_refs_in_expr(left, var_name, fields);
            collect_field_refs_in_expr(right, var_name, fields);
        }
        IRExpr::UnOp { operand, .. } => collect_field_refs_in_expr(operand, var_name, fields),
        IRExpr::Forall { body, .. } | IRExpr::Exists { body, .. } => {
            collect_field_refs_in_expr(body, var_name, fields);
        }
        _ => {}
    }
}

/// Collect variable names referenced in an IR expression (for scene var tracking).
/// Looks for `Field(Var(name), _)` patterns — `res.id` means `res` is referenced.
fn collect_var_refs_in_expr(expr: &IRExpr, refs: &mut HashSet<String>) {
    match expr {
        IRExpr::Field { expr: inner, .. } => {
            if let IRExpr::Var { name, .. } = inner.as_ref() {
                refs.insert(name.clone());
            }
            collect_var_refs_in_expr(inner, refs);
        }
        IRExpr::BinOp { left, right, .. } => {
            collect_var_refs_in_expr(left, refs);
            collect_var_refs_in_expr(right, refs);
        }
        IRExpr::UnOp { operand, .. } => collect_var_refs_in_expr(operand, refs),
        IRExpr::App { func, arg, .. } => {
            collect_var_refs_in_expr(func, refs);
            collect_var_refs_in_expr(arg, refs);
        }
        _ => {}
    }
}

/// Return the first expression kind that scene checking cannot encode safely.
///
/// Scene checks currently rely on `encode_prop_expr` / `encode_prop_value` for
/// given constraints, event arguments, and then assertions. Some expression
/// forms still panic there; reject those forms up front with `SceneFail`.
fn find_unsupported_scene_expr(expr: &IRExpr) -> Option<&'static str> {
    match expr {
        IRExpr::Let { .. } => Some("Let"),
        IRExpr::Lam { .. } => Some("Lam"),
        IRExpr::Match { .. } => Some("Match"),
        IRExpr::MapUpdate { .. } => Some("MapUpdate"),
        IRExpr::Index { .. } => Some("Index"),
        IRExpr::SetLit { .. } => Some("SetLit"),
        IRExpr::SeqLit { .. } => Some("SeqLit"),
        IRExpr::MapLit { .. } => Some("MapLit"),
        IRExpr::SetComp { .. } => Some("SetComp"),
        IRExpr::Sorry => Some("Sorry"),
        IRExpr::Todo => Some("Todo"),
        IRExpr::Field { expr, .. }
        | IRExpr::UnOp { operand: expr, .. }
        | IRExpr::Prime { expr }
        | IRExpr::Always { body: expr }
        | IRExpr::Eventually { body: expr } => find_unsupported_scene_expr(expr),
        IRExpr::BinOp { left, right, .. }
        | IRExpr::App {
            func: left,
            arg: right,
            ..
        } => find_unsupported_scene_expr(left).or_else(|| find_unsupported_scene_expr(right)),
        IRExpr::Forall { body, .. } | IRExpr::Exists { body, .. } => {
            find_unsupported_scene_expr(body)
        }
        IRExpr::Lit { .. } | IRExpr::Var { .. } | IRExpr::Ctor { .. } => None,
    }
}

/// Validate recursive `CrossCall` arities before encoding a scene.
///
/// This avoids panics in the harness and produces a user-facing `SceneFail`
/// reason pinpointing the mismatched call.
fn validate_crosscall_arities(
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
                event,
                args,
            } => {
                let Some(sys) = all_systems.iter().find(|s| s.name == *system) else {
                    return Err(format!("CrossCall target system not found: {system}"));
                };
                let Some(target_event) = sys.events.iter().find(|e| e.name == *event) else {
                    return Err(format!(
                        "CrossCall target event not found: {system}::{event}"
                    ));
                };
                if target_event.params.len() != args.len() {
                    return Err(format!(
                        "CrossCall arity mismatch: {system}::{event} expects {} params but got {} args",
                        target_event.params.len(),
                        args.len()
                    ));
                }
                validate_crosscall_arities(&target_event.body, all_systems, depth + 1)?;
            }
            _ => {}
        }
    }
    Ok(())
}

fn encode_verify_properties(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    asserts: &[IRExpr],
    bound: usize,
) -> Bool {
    let mut all_props = Vec::new();

    for assert_expr in asserts {
        match assert_expr {
            // `always P` — check P at every step
            IRExpr::Always { body } => {
                for step in 0..=bound {
                    let prop = encode_property_at_step(pool, vctx, defs, body, step);
                    all_props.push(prop);
                }
            }
            // `eventually P` — check P at some step (disjunction)
            IRExpr::Eventually { body } => {
                let mut step_props = Vec::new();
                for step in 0..=bound {
                    let prop = encode_property_at_step(pool, vctx, defs, body, step);
                    step_props.push(prop);
                }
                let refs: Vec<&Bool> = step_props.iter().collect();
                if !refs.is_empty() {
                    all_props.push(Bool::or(&refs));
                }
            }
            // Plain assertion — check at every step
            other => {
                for step in 0..=bound {
                    let prop = encode_property_at_step(pool, vctx, defs, other, step);
                    all_props.push(prop);
                }
            }
        }
    }

    if all_props.is_empty() {
        return Bool::from_bool(true);
    }

    let refs: Vec<&Bool> = all_props.iter().collect();
    Bool::and(&refs)
}

/// Encode a property expression at a specific BMC step.
///
/// Entry point that creates an empty `PropertyCtx` and delegates to
/// `encode_prop_expr`, which handles nested multi-entity quantifiers.
fn encode_property_at_step(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    expr: &IRExpr,
    step: usize,
) -> Bool {
    let ctx = PropertyCtx::new();
    encode_prop_expr(pool, vctx, defs, &ctx, expr, step)
}

/// Encode a property expression with quantifier context.
///
/// Handles entity quantifiers (`all o: Order | P(o)`) by expanding
/// over all active slots. The `PropertyCtx` tracks bindings from all
/// enclosing quantifiers so that nested multi-entity references like
/// `s.user_id` and `u.status` resolve to their correct entity slots.
fn encode_prop_expr(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    ctx: &PropertyCtx,
    expr: &IRExpr,
    step: usize,
) -> Bool {
    // Try def expansion — but only if the name is NOT shadowed by a local binding
    // (quantifier-bound variables take precedence over definitions).
    if let IRExpr::Var { name, .. } = expr {
        if !ctx.bindings.contains_key(name) {
            if let Some(expanded) = defs.expand_var(name) {
                return encode_prop_expr(pool, vctx, defs, ctx, &expanded, step);
            }
        }
    }
    if let IRExpr::App { .. } = expr {
        if let Some(expanded) = defs.expand_app(expr) {
            return encode_prop_expr(pool, vctx, defs, ctx, &expanded, step);
        }
    }

    match expr {
        // `all x: Entity | P(x)` — conjunction over all slots
        IRExpr::Forall {
            var,
            domain: crate::ir::types::IRType::Entity { name: entity_name },
            body,
        } => {
            let n_slots = pool.slots_for(entity_name);
            let mut conjuncts = Vec::new();
            for slot in 0..n_slots {
                let active = pool.active_at(entity_name, slot, step);
                let inner_ctx = ctx.with_binding(var, entity_name, slot);
                let body_val = encode_prop_expr(pool, vctx, defs, &inner_ctx, body, step);
                if let Some(SmtValue::Bool(act)) = active {
                    // active => P(slot)
                    conjuncts.push(act.implies(&body_val));
                }
            }
            if conjuncts.is_empty() {
                return Bool::from_bool(true);
            }
            let refs: Vec<&Bool> = conjuncts.iter().collect();
            Bool::and(&refs)
        }
        // `exists x: Entity | P(x)` — disjunction over active slots
        IRExpr::Exists {
            var,
            domain: crate::ir::types::IRType::Entity { name: entity_name },
            body,
        } => {
            let n_slots = pool.slots_for(entity_name);
            let mut disjuncts = Vec::new();
            for slot in 0..n_slots {
                let active = pool.active_at(entity_name, slot, step);
                let inner_ctx = ctx.with_binding(var, entity_name, slot);
                let body_val = encode_prop_expr(pool, vctx, defs, &inner_ctx, body, step);
                if let Some(SmtValue::Bool(act)) = active {
                    // active AND P(slot)
                    disjuncts.push(Bool::and(&[act, &body_val]));
                }
            }
            if disjuncts.is_empty() {
                return Bool::from_bool(false);
            }
            let refs: Vec<&Bool> = disjuncts.iter().collect();
            Bool::or(&refs)
        }
        // Boolean connectives — recurse
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpAnd" || op == "OpOr" || op == "OpImplies" || op == "OpXor" => {
            let l = encode_prop_expr(pool, vctx, defs, ctx, left, step);
            let r = encode_prop_expr(pool, vctx, defs, ctx, right, step);
            match op.as_str() {
                "OpAnd" => Bool::and(&[&l, &r]),
                "OpOr" => Bool::or(&[&l, &r]),
                "OpImplies" => l.implies(&r),
                "OpXor" => Bool::xor(&l, &r),
                _ => unreachable!(),
            }
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => {
            let inner = encode_prop_expr(pool, vctx, defs, ctx, operand, step);
            inner.not()
        }
        // Nested temporal operators — in BMC, `always P` at a single step
        // is just P (the outer loop iterates over steps), and `eventually P`
        // is also just P at this step (the outer loop handles the disjunction).
        IRExpr::Always { body } | IRExpr::Eventually { body } => {
            encode_prop_expr(pool, vctx, defs, ctx, body, step)
        }
        // Comparison and other BinOps that produce Bool (OpEq, OpNEq, OpLt, etc.)
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let l = encode_prop_value(pool, vctx, defs, ctx, left, step);
            let r = encode_prop_value(pool, vctx, defs, ctx, right, step);
            smt::binop(op, &l, &r).to_bool()
        }
        // Literals
        IRExpr::Lit {
            value: crate::ir::types::LitVal::Bool { value },
            ..
        } => Bool::from_bool(*value),
        // Everything else: encode as value and convert to Bool
        other => {
            let val = encode_prop_value(pool, vctx, defs, ctx, other, step);
            val.to_bool()
        }
    }
}

/// Encode a value expression using the multi-entity quantifier context.
///
/// Resolves field references like `s.user_id` by looking up `"s"` in the
/// `PropertyCtx` bindings to find the bound entity and slot index,
/// then resolves via `pool.field_at(entity, slot, field, step)`.
fn encode_prop_value(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    ctx: &PropertyCtx,
    expr: &IRExpr,
    step: usize,
) -> SmtValue {
    // Try def expansion — but only if the name is NOT shadowed by a local binding.
    if let IRExpr::Var { name, .. } = expr {
        if !ctx.bindings.contains_key(name) {
            if let Some(expanded) = defs.expand_var(name) {
                return encode_prop_value(pool, vctx, defs, ctx, &expanded, step);
            }
        }
    }
    if let IRExpr::App { .. } = expr {
        if let Some(expanded) = defs.expand_app(expr) {
            return encode_prop_value(pool, vctx, defs, ctx, &expanded, step);
        }
    }

    match expr {
        IRExpr::Lit { value, .. } => match value {
            crate::ir::types::LitVal::Int { value } => smt::int_val(*value),
            crate::ir::types::LitVal::Bool { value } => smt::bool_val(*value),
            crate::ir::types::LitVal::Real { value }
            | crate::ir::types::LitVal::Float { value } => {
                #[allow(clippy::cast_possible_truncation)]
                let scaled = (*value * 1_000_000.0) as i64;
                smt::real_val(scaled, 1_000_000)
            }
            crate::ir::types::LitVal::Str { .. } => smt::int_val(0),
        },
        // Field access: `var.field` — look up var in bindings, resolve field from bound entity
        IRExpr::Field {
            expr: recv, field, ..
        } => {
            // Try to resolve the receiver as a bound variable
            if let IRExpr::Var { name, .. } = recv.as_ref() {
                if let Some((entity, slot)) = ctx.bindings.get(name) {
                    if let Some(val) = pool.field_at(entity, *slot, field, step) {
                        return val.clone();
                    }
                    panic!(
                        "field not found: {entity}.{field} (var={name}, slot={slot}, step={step})"
                    );
                }
            }
            // No binding for receiver — try all bindings to find the field
            for (entity, slot) in ctx.bindings.values() {
                if let Some(val) = pool.field_at(entity, *slot, field, step) {
                    return val.clone();
                }
            }
            panic!("field not found in any bound entity: {field} (step={step})")
        }
        // Bare variable: check bindings first, then try as field in bound entities
        IRExpr::Var { name, .. } => {
            // Try as a field in each bound entity
            let mut matches = Vec::new();
            for (var, (entity, slot)) in &ctx.bindings {
                if let Some(val) = pool.field_at(entity, *slot, name, step) {
                    matches.push((var.clone(), entity.clone(), val.clone()));
                }
            }
            match matches.len() {
                0 => panic!(
                    "variable not found in any bound entity context: {name} (bindings: {:?}, step={step})",
                    ctx.bindings.keys().collect::<Vec<_>>()
                ),
                1 => matches.into_iter().next().unwrap().2,
                _ => panic!(
                    "ambiguous bare variable: {name} found in entities {:?} — use qualified access (e.g., var.{name})",
                    matches.iter().map(|(v, e, _)| format!("{v}:{e}")).collect::<Vec<_>>()
                ),
            }
        }
        IRExpr::Ctor {
            enum_name, ctor, ..
        } => {
            let id = vctx.variants.id_of(enum_name, ctor);
            smt::int_val(id)
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let l = encode_prop_value(pool, vctx, defs, ctx, left, step);
            let r = encode_prop_value(pool, vctx, defs, ctx, right, step);
            smt::binop(op, &l, &r)
        }
        IRExpr::UnOp { op, operand, .. } => {
            let v = encode_prop_value(pool, vctx, defs, ctx, operand, step);
            smt::unop(op, &v)
        }
        IRExpr::Prime { expr } => encode_prop_value(pool, vctx, defs, ctx, expr, step + 1),
        // Nested quantifiers in value position — encode as Bool, wrap as SmtValue
        IRExpr::Forall { .. } | IRExpr::Exists { .. } => {
            SmtValue::Bool(encode_prop_expr(pool, vctx, defs, ctx, expr, step))
        }
        IRExpr::Always { body } => {
            SmtValue::Bool(encode_prop_expr(pool, vctx, defs, ctx, body, step))
        }
        _ => panic!("unsupported expression in property value encoding: {expr:?}"),
    }
}

// ── Counterexample extraction ───────────────────────────────────────

/// Extract a counterexample trace from a SAT model.
///
/// For each step 0..=bound, reads active flags and field values from
/// the Z3 model and builds `TraceStep` entries.
fn extract_counterexample(
    solver: &Solver,
    pool: &SlotPool,
    entities: &[crate::ir::types::IREntity],
    bound: usize,
) -> Vec<TraceStep> {
    let Some(model) = solver.get_model() else {
        return Vec::new();
    };

    let mut trace = Vec::new();

    for step in 0..=bound {
        let mut assignments = Vec::new();

        for entity in entities {
            let n_slots = pool.slots_for(&entity.name);
            for slot in 0..n_slots {
                // Check if slot is active at this step
                let is_active =
                    if let Some(SmtValue::Bool(act)) = pool.active_at(&entity.name, slot, step) {
                        model
                            .eval(act, true)
                            .is_some_and(|v| format!("{v:?}").contains("true"))
                    } else {
                        false
                    };

                if !is_active {
                    continue;
                }

                // Read field values
                for field in &entity.fields {
                    if let Some(val) = pool.field_at(&entity.name, slot, &field.name, step) {
                        let val_str = match val {
                            SmtValue::Int(i) => model
                                .eval(i, true)
                                .map_or_else(|| "?".to_owned(), |v| format!("{v}")),
                            SmtValue::Bool(b) => model
                                .eval(b, true)
                                .map_or_else(|| "?".to_owned(), |v| format!("{v}")),
                            SmtValue::Real(r) => model
                                .eval(r, true)
                                .map_or_else(|| "?".to_owned(), |v| format!("{v}")),
                            SmtValue::Dynamic(d) => model
                                .eval(d, true)
                                .map_or_else(|| "?".to_owned(), |v| format!("{v}")),
                        };
                        let entity_label = if n_slots > 1 {
                            format!("{}[{}]", entity.name, slot)
                        } else {
                            entity.name.clone()
                        };
                        assignments.push((entity_label, field.name.clone(), val_str));
                    }
                }
            }
        }

        trace.push(TraceStep {
            step,
            // TODO: Determine which event fired by checking which event's guard+body
            // constraints are satisfied in the model. Events are encoded as a disjunction
            // in transition_constraints, so we would need to evaluate each event's formula
            // against the model to label the step.
            event: None,
            assignments,
        });
    }

    trace
}

// ── Display ─────────────────────────────────────────────────────────

impl std::fmt::Display for VerificationResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VerificationResult::Proved {
                name,
                method,
                time_ms,
            } => write!(f, "PROVED  {name} (method: {method}, {time_ms}ms)"),
            VerificationResult::Checked {
                name,
                depth,
                time_ms,
            } => write!(f, "CHECKED {name} (depth: {depth}, {time_ms}ms)"),
            VerificationResult::Counterexample { name, trace } => {
                writeln!(f, "COUNTEREXAMPLE {name}")?;
                for step in trace {
                    if let Some(event) = &step.event {
                        writeln!(f, "  step {}: event {event}", step.step)?;
                    } else {
                        writeln!(f, "  step {}:", step.step)?;
                    }
                    for (entity, field, value) in &step.assignments {
                        writeln!(f, "    {entity}.{field} = {value}")?;
                    }
                }
                Ok(())
            }
            VerificationResult::ScenePass { name, time_ms } => {
                write!(f, "PASS    {name} ({time_ms}ms)")
            }
            VerificationResult::SceneFail { name, reason } => {
                write!(f, "FAIL    {name}: {reason}")
            }
            VerificationResult::Unprovable { name, hint } => {
                write!(f, "UNKNOWN {name}: {hint}")
            }
        }
    }
}

// ── Tests ───────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::types::*;

    /// Helper: build a minimal IR program with an Order entity, OrderStatus enum,
    /// Commerce system, and a verify block.
    fn make_order_ir(assert_expr: IRExpr, bound: i64) -> IRProgram {
        let order_status = IRTypeEntry {
            name: "OrderStatus".to_owned(),
            ty: IRType::Enum {
                name: "OrderStatus".to_owned(),
                constructors: vec![
                    "Pending".to_owned(),
                    "Confirmed".to_owned(),
                    "Shipped".to_owned(),
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
                        name: "OrderStatus".to_owned(),
                        constructors: vec![
                            "Pending".to_owned(),
                            "Confirmed".to_owned(),
                            "Shipped".to_owned(),
                        ],
                    },
                    default: None,
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

        let commerce_system = IRSystem {
            name: "Commerce".to_owned(),
            entities: vec!["Order".to_owned()],
            events: vec![IREvent {
                name: "confirm_order".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                },
                postcondition: None,
                body: vec![IRAction::Choose {
                    var: "o".to_owned(),
                    entity: "Order".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
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

        let verify = IRVerify {
            name: "test_verify".to_owned(),
            systems: vec![IRVerifySystem {
                name: "Commerce".to_owned(),
                lo: 0,
                hi: bound,
            }],
            asserts: vec![assert_expr],
        };

        IRProgram {
            types: vec![order_status],
            constants: vec![],
            functions: vec![],
            entities: vec![order],
            systems: vec![commerce_system],
            verifies: vec![verify],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        }
    }

    #[test]
    fn bmc_checked_valid_property() {
        // Property: always (all o: Order | o.status != @Invalid)
        // Since @Invalid doesn't exist, status can only be Pending/Confirmed/Shipped.
        // The enum domain constraint ensures status is always in {0, 1, 2},
        // and we assert it's never -1, which should hold.
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
                        }),
                        field: "status".to_owned(),
                        ty: IRType::Int,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: -1 },
                    }),
                    ty: IRType::Bool,
                }),
            }),
        };

        let ir = make_order_ir(property, 3);
        let results = verify_all(&ir);

        assert_eq!(results.len(), 1);
        assert!(
            matches!(&results[0], VerificationResult::Checked { name, .. } if name == "test_verify"),
            "expected CHECKED, got: {:?}",
            results[0]
        );
    }

    #[test]
    fn bmc_counterexample_on_violation() {
        // Property: always (all o: Order | o.status == @Pending)
        // After confirm_order, status becomes Confirmed, so this should fail.
        // However, with all slots starting inactive, if no create event occurs,
        // no slot is ever active, so the universal quantifier is vacuously true.
        //
        // We need a system that creates orders AND confirms them.
        // Add a create_order event to the system.
        let mut ir = make_order_ir(
            IRExpr::Always {
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
                            enum_name: "OrderStatus".to_owned(),
                            ctor: "Pending".to_owned(),
                        }),
                        ty: IRType::Bool,
                    }),
                }),
            },
            3,
        );

        // Add a create_order event so orders can actually exist
        ir.systems[0].events.push(IREvent {
            name: "create_order".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
            },
            postcondition: None,
            body: vec![IRAction::Create {
                entity: "Order".to_owned(),
                fields: vec![
                    IRCreateField {
                        name: "id".to_owned(),
                        value: IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 1 },
                        },
                    },
                    IRCreateField {
                        name: "status".to_owned(),
                        value: IRExpr::Ctor {
                            enum_name: "OrderStatus".to_owned(),
                            ctor: "Pending".to_owned(),
                        },
                    },
                ],
            }],
        });

        let results = verify_all(&ir);

        assert_eq!(results.len(), 1);
        assert!(
            matches!(&results[0], VerificationResult::Counterexample { name, .. } if name == "test_verify"),
            "expected COUNTEREXAMPLE, got: {:?}",
            results[0]
        );
    }

    #[test]
    fn bmc_empty_program_no_results() {
        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        };
        let results = verify_all(&ir);
        assert!(results.is_empty());
    }

    fn make_dummy_entity() -> IREntity {
        IREntity {
            name: "Dummy".to_owned(),
            fields: vec![IRField {
                name: "id".to_owned(),
                ty: IRType::Id,
                default: None,
            }],
            transitions: vec![],
        }
    }

    fn make_noop_event(name: &str) -> IREvent {
        IREvent {
            name: name.to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
            },
            postcondition: None,
            body: vec![IRAction::ExprStmt {
                expr: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                },
            }],
        }
    }

    #[test]
    fn scene_rejects_let_in_given_constraint() {
        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![make_dummy_entity()],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![IRScene {
                name: "let_scene".to_owned(),
                systems: vec![],
                givens: vec![IRSceneGiven {
                    var: "d".to_owned(),
                    entity: "Dummy".to_owned(),
                    constraint: IRExpr::Let {
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
                    },
                }],
                events: vec![],
                ordering: vec![],
                assertions: vec![],
            }],
        };

        let results = verify_all(&ir);
        assert_eq!(results.len(), 1);
        match &results[0] {
            VerificationResult::SceneFail { reason, .. } => {
                assert!(reason.contains("unsupported expression kind in scene given"));
                assert!(reason.contains("Let"));
            }
            other => panic!("expected SceneFail, got {other:?}"),
        }
    }

    #[test]
    fn scene_reports_crosscall_arity_mismatch() {
        let caller = IRSystem {
            name: "Caller".to_owned(),
            entities: vec!["Dummy".to_owned()],
            events: vec![IREvent {
                name: "start".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                },
                postcondition: None,
                body: vec![IRAction::CrossCall {
                    system: "Callee".to_owned(),
                    event: "run".to_owned(),
                    args: vec![IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },
                    }],
                }],
            }],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
        };
        let callee = IRSystem {
            name: "Callee".to_owned(),
            entities: vec!["Dummy".to_owned()],
            events: vec![IREvent {
                name: "run".to_owned(),
                params: vec![
                    IRTransParam {
                        name: "a".to_owned(),
                        ty: IRType::Int,
                    },
                    IRTransParam {
                        name: "b".to_owned(),
                        ty: IRType::Int,
                    },
                ],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                },
                postcondition: None,
                body: vec![IRAction::ExprStmt {
                    expr: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                    },
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
            entities: vec![make_dummy_entity()],
            systems: vec![caller, callee],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![IRScene {
                name: "crosscall_arity".to_owned(),
                systems: vec!["Caller".to_owned()],
                givens: vec![],
                events: vec![IRSceneEvent {
                    var: "r".to_owned(),
                    system: "Caller".to_owned(),
                    event: "start".to_owned(),
                    args: vec![],
                    cardinality: Cardinality::Named("one".to_owned()),
                }],
                ordering: vec![],
                assertions: vec![],
            }],
        };

        let results = verify_all(&ir);
        assert_eq!(results.len(), 1);
        match &results[0] {
            VerificationResult::SceneFail { reason, .. } => {
                assert!(reason.contains("CrossCall arity mismatch"));
                assert!(reason.contains("Callee::run"));
            }
            other => panic!("expected SceneFail, got {other:?}"),
        }
    }

    /// Build a minimal IR with an entity that has a status field,
    /// a transition, and a system event — for scene testing.
    fn make_scene_test_ir(scene: IRScene) -> IRProgram {
        let status_enum = IRTypeEntry {
            name: "Status".to_owned(),
            ty: IRType::Enum {
                name: "Status".to_owned(),
                constructors: vec!["Active".to_owned(), "Locked".to_owned()],
            },
        };

        let account = IREntity {
            name: "Account".to_owned(),
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
                        constructors: vec!["Active".to_owned(), "Locked".to_owned()],
                    },
                    default: Some(IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Active".to_owned(),
                    }),
                },
            ],
            transitions: vec![IRTransition {
                name: "lock".to_owned(),
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
                        ctor: "Active".to_owned(),
                    }),
                    ty: IRType::Bool,
                },
                updates: vec![IRUpdate {
                    field: "status".to_owned(),
                    value: IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Locked".to_owned(),
                    },
                }],
                postcondition: None,
            }],
        };

        let system = IRSystem {
            name: "Auth".to_owned(),
            entities: vec!["Account".to_owned()],
            events: vec![IREvent {
                name: "lock_account".to_owned(),
                params: vec![IRTransParam {
                    name: "account_id".to_owned(),
                    ty: IRType::Id,
                }],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                },
                postcondition: None,
                body: vec![IRAction::Choose {
                    var: "a".to_owned(),
                    entity: "Account".to_owned(),
                    filter: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "a".to_owned(),
                                ty: IRType::Entity {
                                    name: "Account".to_owned(),
                                },
                            }),
                            field: "id".to_owned(),
                            ty: IRType::Id,
                        }),
                        right: Box::new(IRExpr::Var {
                            name: "account_id".to_owned(),
                            ty: IRType::Id,
                        }),
                        ty: IRType::Bool,
                    }),
                    ops: vec![IRAction::Apply {
                        target: "a".to_owned(),
                        transition: "lock".to_owned(),
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

        IRProgram {
            types: vec![status_enum],
            constants: vec![],
            functions: vec![],
            entities: vec![account],
            systems: vec![system],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![scene],
        }
    }

    #[test]
    fn scene_happy_path_passes() {
        // Scene: given an Active account, lock it, then assert it's Locked.
        let scene = IRScene {
            name: "lock_test".to_owned(),
            systems: vec!["Auth".to_owned()],
            givens: vec![IRSceneGiven {
                var: "a".to_owned(),
                entity: "Account".to_owned(),
                constraint: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "a".to_owned(),
                            ty: IRType::Entity {
                                name: "Account".to_owned(),
                            },
                        }),
                        field: "status".to_owned(),
                        ty: IRType::Int,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Active".to_owned(),
                    }),
                    ty: IRType::Bool,
                },
            }],
            events: vec![IRSceneEvent {
                var: "lk".to_owned(),
                system: "Auth".to_owned(),
                event: "lock_account".to_owned(),
                args: vec![IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "a".to_owned(),
                        ty: IRType::Entity {
                            name: "Account".to_owned(),
                        },
                    }),
                    field: "id".to_owned(),
                    ty: IRType::Id,
                }],
                cardinality: Cardinality::Named("one".to_owned()),
            }],
            ordering: vec![],
            assertions: vec![IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "a".to_owned(),
                        ty: IRType::Entity {
                            name: "Account".to_owned(),
                        },
                    }),
                    field: "status".to_owned(),
                    ty: IRType::Int,
                }),
                right: Box::new(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Locked".to_owned(),
                }),
                ty: IRType::Bool,
            }],
        };

        let ir = make_scene_test_ir(scene);
        let results = verify_all(&ir);
        assert_eq!(results.len(), 1);
        assert!(
            matches!(&results[0], VerificationResult::ScenePass { .. }),
            "expected ScenePass, got: {:?}",
            results[0]
        );
    }

    #[test]
    fn scene_impossible_assertion_fails() {
        // Scene: given an Active account, lock it, then assert it's STILL Active.
        // This is impossible — lock changes Active → Locked.
        let scene = IRScene {
            name: "impossible_test".to_owned(),
            systems: vec!["Auth".to_owned()],
            givens: vec![IRSceneGiven {
                var: "a".to_owned(),
                entity: "Account".to_owned(),
                constraint: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "a".to_owned(),
                            ty: IRType::Entity {
                                name: "Account".to_owned(),
                            },
                        }),
                        field: "status".to_owned(),
                        ty: IRType::Int,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Active".to_owned(),
                    }),
                    ty: IRType::Bool,
                },
            }],
            events: vec![IRSceneEvent {
                var: "lk".to_owned(),
                system: "Auth".to_owned(),
                event: "lock_account".to_owned(),
                args: vec![IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "a".to_owned(),
                        ty: IRType::Entity {
                            name: "Account".to_owned(),
                        },
                    }),
                    field: "id".to_owned(),
                    ty: IRType::Id,
                }],
                cardinality: Cardinality::Named("one".to_owned()),
            }],
            ordering: vec![],
            // Assert status is STILL Active — impossible after lock
            assertions: vec![IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "a".to_owned(),
                        ty: IRType::Entity {
                            name: "Account".to_owned(),
                        },
                    }),
                    field: "status".to_owned(),
                    ty: IRType::Int,
                }),
                right: Box::new(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Active".to_owned(),
                }),
                ty: IRType::Bool,
            }],
        };

        let ir = make_scene_test_ir(scene);
        let results = verify_all(&ir);
        assert_eq!(results.len(), 1);
        assert!(
            matches!(&results[0], VerificationResult::SceneFail { .. }),
            "expected SceneFail, got: {:?}",
            results[0]
        );
    }
}
