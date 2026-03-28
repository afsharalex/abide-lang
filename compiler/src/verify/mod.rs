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

use crate::ir::types::{IRAction, IRExpr, IRProgram, IRVerify};

use self::context::VerifyContext;
use self::harness::{
    create_slot_pool, domain_constraints, initial_state_constraints, transition_constraints,
    SlotPool,
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
/// Processes verify blocks (bounded model checking).
/// Returns one result per target.
pub fn verify_all(ir: &IRProgram) -> Vec<VerificationResult> {
    let vctx = context::VerifyContext::from_ir(ir);
    let defs = defenv::DefEnv::from_ir(ir);
    let mut results = Vec::new();

    for verify_block in &ir.verifies {
        results.push(check_verify_block(ir, &vctx, &defs, verify_block));
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
}
