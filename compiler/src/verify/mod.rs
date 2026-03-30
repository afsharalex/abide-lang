//! Verification backend — connects Abide IR to Z3.
//!
//! Architecture:
//! - `smt`: Z3 value types, sort mapping, collection array support
//! - `context`: `VerifyContext` (variant IDs, field metadata, entity pool info)
//! - `harness`: Multi-slot entity pools, action/event/collection encoding
//! - `ic3`: IC3/PDR via Z3 Spacer (CHC encoding, counterexample extraction)
//! - `defenv`: Definition environment for pred/prop/fn expansion
//! - `mod`: Tiered dispatch (`verify_all`), property encoding, counterexample extraction

pub mod context;
pub mod defenv;
pub mod harness;
pub mod ic3;
pub mod smt;

use std::collections::{HashMap, HashSet};
use std::time::Instant;

use z3::ast::Bool;
use z3::Solver;

use crate::ir::types::{IRAction, IRExpr, IRProgram, IRScene, IRTheorem, IRType, IRVerify};

use self::context::VerifyContext;
use self::harness::{
    create_slot_pool, domain_constraints, encode_event_with_params, initial_state_constraints,
    symmetry_breaking_constraints, transition_constraints, SlotPool,
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
        span: Option<crate::span::Span>,
        file: Option<String>,
    },
    /// Property checked to a bounded depth (no counterexample found).
    Checked {
        name: String,
        depth: usize,
        time_ms: u64,
        span: Option<crate::span::Span>,
        file: Option<String>,
    },
    /// Counterexample found — a trace of events that violates the property.
    Counterexample {
        name: String,
        trace: Vec<TraceStep>,
        span: Option<crate::span::Span>,
        file: Option<String>,
    },
    /// Scene passed — the scenario is satisfiable and assertions hold.
    ScenePass {
        name: String,
        time_ms: u64,
        span: Option<crate::span::Span>,
        file: Option<String>,
    },
    /// Scene failed — the scenario is unsatisfiable or assertions violated.
    SceneFail {
        name: String,
        reason: String,
        span: Option<crate::span::Span>,
        file: Option<String>,
    },
    /// Could not prove automatically — needs manual proof.
    Unprovable {
        name: String,
        hint: String,
        span: Option<crate::span::Span>,
        file: Option<String>,
    },
}

impl VerificationResult {
    /// Attach source location to this result (called by `verify_all` after dispatch).
    ///
    /// Only fills in span/file when the result doesn't already carry a more specific
    /// location (e.g., a per-assertion span set by the internal verification function).
    fn with_source(
        self,
        block_span: Option<crate::span::Span>,
        block_file: Option<String>,
    ) -> Self {
        match self {
            Self::Proved {
                name,
                method,
                time_ms,
                span,
                file,
            } => Self::Proved {
                name,
                method,
                time_ms,
                span: span.or(block_span),
                file: file.or(block_file),
            },
            Self::Checked {
                name,
                depth,
                time_ms,
                span,
                file,
            } => Self::Checked {
                name,
                depth,
                time_ms,
                span: span.or(block_span),
                file: file.or(block_file),
            },
            Self::Counterexample {
                name,
                trace,
                span,
                file,
            } => Self::Counterexample {
                name,
                trace,
                span: span.or(block_span),
                file: file.or(block_file),
            },
            Self::ScenePass {
                name,
                time_ms,
                span,
                file,
            } => Self::ScenePass {
                name,
                time_ms,
                span: span.or(block_span),
                file: file.or(block_file),
            },
            Self::SceneFail {
                name,
                reason,
                span,
                file,
            } => Self::SceneFail {
                name,
                reason,
                span: span.or(block_span),
                file: file.or(block_file),
            },
            Self::Unprovable {
                name,
                hint,
                span,
                file,
            } => Self::Unprovable {
                name,
                hint,
                span: span.or(block_span),
                file: file.or(block_file),
            },
        }
    }

    /// Is this a failure (counterexample, scene fail, or unprovable)?
    pub fn is_failure(&self) -> bool {
        matches!(
            self,
            Self::Counterexample { .. } | Self::SceneFail { .. } | Self::Unprovable { .. }
        )
    }

    /// Source span for diagnostic rendering.
    pub fn span(&self) -> Option<crate::span::Span> {
        match self {
            Self::Proved { span, .. }
            | Self::Checked { span, .. }
            | Self::Counterexample { span, .. }
            | Self::ScenePass { span, .. }
            | Self::SceneFail { span, .. }
            | Self::Unprovable { span, .. } => *span,
        }
    }

    /// Source file for diagnostic rendering.
    pub fn file(&self) -> Option<&str> {
        match self {
            Self::Proved { file, .. }
            | Self::Checked { file, .. }
            | Self::Counterexample { file, .. }
            | Self::ScenePass { file, .. }
            | Self::SceneFail { file, .. }
            | Self::Unprovable { file, .. } => file.as_deref(),
        }
    }
}

/// A single step in a counterexample trace.
#[derive(Debug)]
pub struct TraceStep {
    pub step: usize,
    pub event: Option<String>,
    pub assignments: Vec<(String, String, String)>, // (entity, field, value)
}

// ── Configuration ───────────────────────────────────────────────────

/// Configuration for the verification pipeline.
#[allow(clippy::struct_excessive_bools)]
pub struct VerifyConfig {
    /// Skip Tier 1 (induction), only run bounded model checking.
    pub bounded_only: bool,
    /// Skip Tier 2 (BMC), only try induction.
    pub unbounded_only: bool,
    /// Timeout for Tier 1 induction attempts, in milliseconds.
    pub induction_timeout_ms: u64,
    /// Timeout for Tier 2 BMC attempts, in milliseconds. 0 = no timeout.
    pub bmc_timeout_ms: u64,
    /// Default BMC depth for auto-verified props (which lack explicit `[0..N]`).
    pub prop_bmc_depth: usize,
    /// Timeout for IC3/PDR attempts, in milliseconds. 0 = no timeout.
    pub ic3_timeout_ms: u64,
    /// Skip IC3/PDR verification (for speed).
    pub no_ic3: bool,
    /// Skip automatic prop verification.
    pub no_prop_verify: bool,
    /// Print progress messages to stderr.
    pub progress: bool,
}

impl Default for VerifyConfig {
    fn default() -> Self {
        Self {
            bounded_only: false,
            unbounded_only: false,
            induction_timeout_ms: 5000,
            bmc_timeout_ms: 0,
            prop_bmc_depth: 10,
            ic3_timeout_ms: 10000,
            no_ic3: false,
            no_prop_verify: false,
            progress: false,
        }
    }
}

// ── Top-level verification entry point ──────────────────────────────

/// Verify all targets in an IR program.
///
/// Processes verify blocks (tiered: induction → IC3 → BMC), scene blocks (SAT),
/// and theorem blocks (IC3 → induction).
/// Returns one result per target, each carrying source location for diagnostic rendering.
#[allow(clippy::too_many_lines)]
pub fn verify_all(ir: &IRProgram, config: &VerifyConfig) -> Vec<VerificationResult> {
    let vctx = context::VerifyContext::from_ir(ir);
    let defs = defenv::DefEnv::from_ir(ir);
    let mut results = Vec::new();

    for verify_block in &ir.verifies {
        if config.progress {
            eprint!("Checking {}...", verify_block.name);
        }
        let result = check_verify_block_tiered(ir, &vctx, &defs, verify_block, config)
            .with_source(verify_block.span, verify_block.file.clone());
        if config.progress {
            eprintln!(" done");
        }
        results.push(result);
    }

    for scene_block in &ir.scenes {
        if config.progress {
            eprint!("Checking scene {}...", scene_block.name);
        }
        let result = check_scene_block(ir, &vctx, &defs, scene_block)
            .with_source(scene_block.span, scene_block.file.clone());
        if config.progress {
            eprintln!(" done");
        }
        results.push(result);
    }

    for theorem_block in &ir.theorems {
        if config.progress {
            eprint!("Proving {}...", theorem_block.name);
        }
        let result = check_theorem_block(ir, &vctx, &defs, theorem_block, config)
            .with_source(theorem_block.span, theorem_block.file.clone());
        if config.progress {
            eprintln!(" done");
        }
        results.push(result);
    }

    // ── Auto-verify props ───────────────────────────────────────────
    // Props with a target system are implicit theorems: declaring a prop
    // means asserting it must hold (Dafny model).
    if !config.no_prop_verify {
        // Collect prop names already covered by explicit theorems/verify blocks.
        // Collect from both unexpanded (direct name refs like `Var("prop_name")`)
        // AND expanded forms (transitive refs: if p2's body references p1,
        // a theorem proving p2 also covers p1).
        let mut covered: HashSet<String> = HashSet::new();
        for thm in &ir.theorems {
            // Direct references
            collect_def_refs_in_exprs(&thm.shows, &mut covered);
            collect_def_refs_in_exprs(&thm.invariants, &mut covered);
            // Transitive references (after def expansion)
            let expanded: Vec<IRExpr> = thm
                .shows
                .iter()
                .chain(thm.invariants.iter())
                .map(|e| expand_through_defs(e, &defs))
                .collect();
            collect_def_refs_in_exprs(&expanded, &mut covered);
        }
        for vb in &ir.verifies {
            collect_def_refs_in_exprs(&vb.asserts, &mut covered);
            let expanded: Vec<IRExpr> = vb
                .asserts
                .iter()
                .map(|e| expand_through_defs(e, &defs))
                .collect();
            collect_def_refs_in_exprs(&expanded, &mut covered);
        }

        for func in &ir.functions {
            // Props: have prop_target AND return Bool
            let Some(ref target_system) = func.prop_target else {
                continue;
            };
            if func.ty != IRType::Bool {
                results.push(
                    VerificationResult::Unprovable {
                        name: format!("prop_{}", func.name),
                        hint: format!(
                            "internal error: prop `{}` has non-Bool return type {:?}",
                            func.name, func.ty
                        ),
                        span: None,
                        file: None,
                    }
                    .with_source(func.span, func.file.clone()),
                );
                continue;
            }
            if covered.contains(&func.name) {
                continue; // already checked via an explicit theorem/verify
            }

            let synthetic_theorem = crate::ir::types::IRTheorem {
                name: format!("prop_{}", func.name),
                systems: vec![target_system.clone()],
                invariants: vec![],
                shows: vec![IRExpr::Always {
                    body: Box::new(func.body.clone()),
                    span: None,
                }],
                span: func.span,
                file: func.file.clone(),
            };

            if config.progress {
                eprint!("Verifying prop {}...", func.name);
            }
            let result = check_theorem_block(ir, &vctx, &defs, &synthetic_theorem, config)
                .with_source(func.span, func.file.clone());
            if config.progress {
                eprintln!(" done");
            }
            results.push(result);
        }
    }

    results
}

/// Elapsed time in milliseconds, saturating to `u64::MAX`.
#[allow(clippy::cast_possible_truncation)]
fn elapsed_ms(start: &Instant) -> u64 {
    start.elapsed().as_millis().min(u128::from(u64::MAX)) as u64
}

/// Extract the source span from an `IRExpr` (top-level only).
fn expr_span(e: &IRExpr) -> Option<crate::span::Span> {
    match e {
        IRExpr::Lit { span, .. }
        | IRExpr::Var { span, .. }
        | IRExpr::Ctor { span, .. }
        | IRExpr::BinOp { span, .. }
        | IRExpr::UnOp { span, .. }
        | IRExpr::App { span, .. }
        | IRExpr::Lam { span, .. }
        | IRExpr::Let { span, .. }
        | IRExpr::Forall { span, .. }
        | IRExpr::Exists { span, .. }
        | IRExpr::Field { span, .. }
        | IRExpr::Prime { span, .. }
        | IRExpr::Always { span, .. }
        | IRExpr::Eventually { span, .. }
        | IRExpr::Match { span, .. }
        | IRExpr::MapUpdate { span, .. }
        | IRExpr::Index { span, .. }
        | IRExpr::SetLit { span, .. }
        | IRExpr::SeqLit { span, .. }
        | IRExpr::MapLit { span, .. }
        | IRExpr::SetComp { span, .. }
        | IRExpr::Card { span, .. }
        | IRExpr::Sorry { span, .. }
        | IRExpr::Todo { span, .. }
        | IRExpr::Block { span, .. }
        | IRExpr::VarDecl { span, .. }
        | IRExpr::While { span, .. }
        | IRExpr::IfElse { span, .. } => *span,
    }
}

/// Collect top-level definition names referenced in expressions.
///
/// Finds `Var(name)` nodes that are NOT bound by enclosing quantifiers/lambdas
/// (i.e., free references to props/preds/fns). Used to detect which props are
/// already covered by explicit theorem/verify blocks.
fn collect_def_refs_in_exprs(exprs: &[IRExpr], refs: &mut HashSet<String>) {
    let bound = HashSet::new();
    for expr in exprs {
        collect_def_refs_inner(expr, &bound, refs);
    }
}

fn collect_def_refs_inner(expr: &IRExpr, bound: &HashSet<String>, refs: &mut HashSet<String>) {
    match expr {
        IRExpr::Var { name, .. } => {
            if !bound.contains(name) {
                refs.insert(name.clone());
            }
        }
        IRExpr::App { func, arg, .. } => {
            if let IRExpr::Var { name, .. } = func.as_ref() {
                if !bound.contains(name) {
                    refs.insert(name.clone());
                }
            }
            collect_def_refs_inner(func, bound, refs);
            collect_def_refs_inner(arg, bound, refs);
        }
        IRExpr::Forall { var, body, .. } | IRExpr::Exists { var, body, .. } => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.clone());
            collect_def_refs_inner(body, &inner_bound, refs);
        }
        IRExpr::Lam { param, body, .. } => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(param.clone());
            collect_def_refs_inner(body, &inner_bound, refs);
        }
        IRExpr::SetComp {
            var,
            filter,
            projection,
            ..
        } => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.clone());
            collect_def_refs_inner(filter, &inner_bound, refs);
            if let Some(proj) = projection {
                collect_def_refs_inner(proj, &inner_bound, refs);
            }
        }
        IRExpr::BinOp { left, right, .. } => {
            collect_def_refs_inner(left, bound, refs);
            collect_def_refs_inner(right, bound, refs);
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            collect_def_refs_inner(map, bound, refs);
            collect_def_refs_inner(key, bound, refs);
            collect_def_refs_inner(value, bound, refs);
        }
        IRExpr::Index { map, key, .. } => {
            collect_def_refs_inner(map, bound, refs);
            collect_def_refs_inner(key, bound, refs);
        }
        IRExpr::MapLit { entries, .. } => {
            for (k, v) in entries {
                collect_def_refs_inner(k, bound, refs);
                collect_def_refs_inner(v, bound, refs);
            }
        }
        IRExpr::SetLit { elements, .. } | IRExpr::SeqLit { elements, .. } => {
            for e in elements {
                collect_def_refs_inner(e, bound, refs);
            }
        }
        IRExpr::UnOp { operand, .. }
        | IRExpr::Field { expr: operand, .. }
        | IRExpr::Prime { expr: operand, .. }
        | IRExpr::Always { body: operand, .. }
        | IRExpr::Eventually { body: operand, .. }
        | IRExpr::Card { expr: operand, .. } => {
            collect_def_refs_inner(operand, bound, refs);
        }
        IRExpr::Let { bindings, body, .. } => {
            let mut inner_bound = bound.clone();
            for b in bindings {
                // Binding RHS is evaluated in the outer scope
                collect_def_refs_inner(&b.expr, &inner_bound, refs);
                inner_bound.insert(b.name.clone());
            }
            collect_def_refs_inner(body, &inner_bound, refs);
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            collect_def_refs_inner(scrutinee, bound, refs);
            for arm in arms {
                let mut arm_bound = bound.clone();
                collect_pattern_binders(&arm.pattern, &mut arm_bound);
                if let Some(ref guard) = arm.guard {
                    collect_def_refs_inner(guard, &arm_bound, refs);
                }
                collect_def_refs_inner(&arm.body, &arm_bound, refs);
            }
        }
        _ => {}
    }
}

/// Collect variable names bound by a pattern (for binder-aware traversal).
fn collect_pattern_binders(pat: &crate::ir::types::IRPattern, bound: &mut HashSet<String>) {
    match pat {
        crate::ir::types::IRPattern::PVar { name } => {
            bound.insert(name.clone());
        }
        crate::ir::types::IRPattern::PCtor { fields, .. } => {
            for f in fields {
                collect_pattern_binders(&f.pattern, bound);
            }
        }
        crate::ir::types::IRPattern::POr { left, right } => {
            collect_pattern_binders(left, bound);
            collect_pattern_binders(right, bound);
        }
        crate::ir::types::IRPattern::PWild => {}
    }
}

/// Convert IC3 trace steps to the shared `TraceStep` format.
fn ic3_trace_to_trace_steps(ic3_trace: &[ic3::Ic3TraceStep]) -> Vec<TraceStep> {
    ic3_trace
        .iter()
        .map(|s| TraceStep {
            step: s.step,
            event: None, // IC3 doesn't track which rule/event fired
            assignments: s.assignments.clone(),
        })
        .collect()
}

// ── Tiered dispatch for verify blocks ───────────────────────────────

/// Check a verify block using tiered dispatch (DDR-031):
///
/// 1. If asserts contain `eventually`, skip Tier 1 (liveness can't be proved by induction)
/// 2. **Tier 1a:** Try 1-induction with timeout — if PROVED, done
/// 3. **Tier 1b:** Try IC3/PDR — discovers strengthening invariants automatically
/// 4. **Tier 2:** Fall back to bounded model checking with `[0..N]` depth
///
/// The user writes the same `verify` block regardless of which tier succeeds.
fn check_verify_block_tiered(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    verify_block: &IRVerify,
    config: &VerifyConfig,
) -> VerificationResult {
    // Check if any assert contains `eventually` — skip induction for liveness
    let has_liveness = verify_block.asserts.iter().any(|a| {
        let expanded = expand_through_defs(a, defs);
        contains_eventually(&expanded)
    });

    // Tier 1a: Try induction (unless bounded-only or liveness)
    if !config.bounded_only && !has_liveness {
        if let Some(result) = try_induction_on_verify(ir, vctx, defs, verify_block, config) {
            return result;
        }
        // Induction failed or timed out — try IC3
    }

    // Tier 1b: Try IC3/PDR (unless bounded-only, no-ic3, or liveness)
    if !config.bounded_only && !config.no_ic3 && !has_liveness {
        if let Some(result) = try_ic3_on_verify(ir, vctx, defs, verify_block, config) {
            return result;
        }
        // IC3 failed — fall through to Tier 2
    }

    // Tier 2: Bounded model checking (unless unbounded-only)
    if config.unbounded_only {
        let techniques = if has_liveness {
            crate::messages::TIERED_LIVENESS_SKIP.to_owned()
        } else if config.no_ic3 {
            crate::messages::TIERED_NO_IC3.to_owned()
        } else {
            crate::messages::TIERED_BOTH_FAILED.to_owned()
        };
        return VerificationResult::Unprovable {
            name: verify_block.name.clone(),
            hint: format!("{techniques}, and --unbounded-only was specified"),
            span: None,
            file: None,
        };
    }

    check_verify_block(ir, vctx, defs, verify_block, config)
}

/// Attempt to prove a verify block's asserts by 1-induction.
///
/// Returns `Some(Proved)` if all asserts are inductive.
/// Returns `None` if induction fails, times out, or can't be applied.
#[allow(clippy::too_many_lines)]
fn try_induction_on_verify(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    verify_block: &IRVerify,
    config: &VerifyConfig,
) -> Option<VerificationResult> {
    let start = Instant::now();

    // Build scope (same as check_verify_block but reusable)
    let mut scope: HashMap<String, usize> = HashMap::new();
    let mut system_names: Vec<String> = Vec::new();

    for vs in &verify_block.systems {
        system_names.push(vs.name.clone());
        if let Some(sys) = ir.systems.iter().find(|s| s.name == vs.name) {
            for ent_name in &sys.entities {
                scope.entry(ent_name.clone()).or_insert(2);
            }
        }
    }

    // Expand scope via CrossCall
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
                scope.entry(ent_name.clone()).or_insert(2);
            }
        }
    }

    if scope.is_empty() {
        return None;
    }

    // Analyze quantifier depth for adaptive scope
    for assert_expr in &verify_block.asserts {
        let expanded = expand_through_defs(assert_expr, defs);
        let mut counts: HashMap<String, usize> = HashMap::new();
        count_entity_quantifiers(&expanded, &mut counts);
        for (entity, count) in counts {
            let min_slots = count + 1;
            if let Some(existing) = scope.get_mut(&entity) {
                *existing = (*existing).max(min_slots);
            }
        }
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

    // Strip `always` wrappers from asserts — induction proves always by construction
    let show_exprs: Vec<&IRExpr> = verify_block
        .asserts
        .iter()
        .map(|a| match a {
            IRExpr::Always { body, .. } => body.as_ref(),
            other => other,
        })
        .collect();

    // Pre-check: reject unsupported expressions in asserts AND transitions
    for expr in &show_exprs {
        let expanded = expand_through_defs(expr, defs);
        if find_unsupported_scene_expr(&expanded).is_some() {
            return None;
        }
    }
    for entity in &relevant_entities {
        for trans in &entity.transitions {
            if find_unsupported_scene_expr(&trans.guard).is_some() {
                return None;
            }
            for upd in &trans.updates {
                if find_unsupported_scene_expr(&upd.value).is_some() {
                    return None;
                }
            }
        }
    }
    for sys in &relevant_systems {
        for event in &sys.events {
            if find_unsupported_scene_expr(&event.guard).is_some() {
                return None;
            }
            if find_unsupported_in_actions(&event.body).is_some() {
                return None;
            }
        }
    }

    // ── Base case: P holds at step 0 ───────────────────────────────
    {
        let pool = create_slot_pool(&relevant_entities, &scope, 0);
        let solver = Solver::new();
        set_solver_timeout(&solver, config.induction_timeout_ms);

        for c in initial_state_constraints(&pool) {
            solver.assert(&c);
        }
        for c in domain_constraints(&pool, vctx, &relevant_entities) {
            solver.assert(&c);
        }

        let mut negated = Vec::new();
        for expr in &show_exprs {
            let Ok(prop) = encode_property_at_step(&pool, vctx, defs, expr, 0) else {
                return None;
            };
            negated.push(prop.not());
        }
        let neg_refs: Vec<&Bool> = negated.iter().collect();
        if !neg_refs.is_empty() {
            solver.assert(Bool::or(&neg_refs));
        }

        match solver.check() {
            z3::SatResult::Unsat => {} // base holds
            _ => return None,          // base fails or timeout — fall back
        }
    }

    // ── Step case: P(k) ∧ transition(k→k+1) → P(k+1) ─────────────
    {
        let pool = create_slot_pool(&relevant_entities, &scope, 1);
        let solver = Solver::new();
        set_solver_timeout(&solver, config.induction_timeout_ms);

        for c in domain_constraints(&pool, vctx, &relevant_entities) {
            solver.assert(&c);
        }

        // Assume P at step 0
        for expr in &show_exprs {
            let Ok(prop) = encode_property_at_step(&pool, vctx, defs, expr, 0) else {
                return None;
            };
            solver.assert(&prop);
        }

        // One transition
        let trans = transition_constraints(&pool, vctx, &relevant_entities, &relevant_systems, 0);
        solver.assert(&trans);

        // Assert NOT P at step 1
        let mut negated = Vec::new();
        for expr in &show_exprs {
            let Ok(prop) = encode_property_at_step(&pool, vctx, defs, expr, 1) else {
                return None;
            };
            negated.push(prop.not());
        }
        let neg_refs: Vec<&Bool> = negated.iter().collect();
        if !neg_refs.is_empty() {
            solver.assert(Bool::or(&neg_refs));
        }

        match solver.check() {
            z3::SatResult::Unsat => {} // step holds
            _ => return None,          // step fails or timeout — fall back
        }
    }

    // Both passed — PROVED
    let elapsed = elapsed_ms(&start);
    Some(VerificationResult::Proved {
        name: verify_block.name.clone(),
        method: "1-induction".to_owned(),
        time_ms: elapsed,
        span: None,
        file: None,
    })
}

/// Try to prove a verify block using IC3/PDR via Z3's Spacer engine.
///
/// IC3 is more powerful than 1-induction: it automatically discovers
/// strengthening invariants, proving properties that aren't directly
/// inductive. Returns `Some(Proved)` if all asserts are proved, `None`
/// if any assert fails or can't be encoded.
fn try_ic3_on_verify(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    verify_block: &IRVerify,
    config: &VerifyConfig,
) -> Option<VerificationResult> {
    let start = Instant::now();

    // Build scope (same as induction)
    let mut scope: HashMap<String, usize> = HashMap::new();
    let mut system_names: Vec<String> = Vec::new();

    for vs in &verify_block.systems {
        system_names.push(vs.name.clone());
        if let Some(sys) = ir.systems.iter().find(|s| s.name == vs.name) {
            for ent_name in &sys.entities {
                scope.entry(ent_name.clone()).or_insert(2);
            }
        }
    }

    // Expand scope via CrossCall
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
                scope.entry(ent_name.clone()).or_insert(2);
            }
        }
    }

    if scope.is_empty() {
        return None;
    }

    // Quantifier-based scope adjustment
    for assert_expr in &verify_block.asserts {
        let expanded = expand_through_defs(assert_expr, defs);
        let mut counts: HashMap<String, usize> = HashMap::new();
        count_entity_quantifiers(&expanded, &mut counts);
        for (entity, count) in counts {
            let min_slots = count + 1;
            if let Some(existing) = scope.get_mut(&entity) {
                *existing = (*existing).max(min_slots);
            }
        }
    }

    if config.progress {
        eprint!(" (trying IC3/PDR)");
    }

    // Try IC3 on each assert — all must pass for PROVED
    // Try IC3 on each assert — all must pass for PROVED.
    // IC3 Violated always falls to BMC for verify blocks: BMC produces
    // confirmed counterexamples from concrete solver models, while IC3
    // traces come from the over-approximated CHC encoding (ForAll
    // per-slot independence can produce spurious intermediate states).
    for assert_expr in &verify_block.asserts {
        let expanded = expand_through_defs(assert_expr, defs);
        let result = ic3::try_ic3_system(
            ir,
            vctx,
            &system_names,
            &expanded,
            &scope,
            config.ic3_timeout_ms,
        );
        match result {
            ic3::Ic3Result::Proved => {} // this assert proved, continue
            ic3::Ic3Result::Violated(_) | ic3::Ic3Result::Unknown(_) => {
                return None; // fall back to BMC for confirmed trace
            }
        }
    }

    let elapsed = elapsed_ms(&start);
    Some(VerificationResult::Proved {
        name: verify_block.name.clone(),
        method: "IC3/PDR".to_owned(),
        time_ms: elapsed,
        span: None,
        file: None,
    })
}

/// Set a timeout on a Z3 solver instance (milliseconds).
#[allow(clippy::cast_possible_truncation)]
fn set_solver_timeout(solver: &Solver, timeout_ms: u64) {
    let mut params = z3::Params::new();
    params.set_u32("timeout", timeout_ms.min(u64::from(u32::MAX)) as u32);
    solver.set_params(&params);
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
#[allow(clippy::too_many_lines)]
fn check_verify_block(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    verify_block: &IRVerify,
    config: &VerifyConfig,
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
            span: None,
            file: None,
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

    // ── 2c. Pre-validate: reject unsupported expression forms ─────
    // Catches forms like Card(field), SetComp with non-entity domain, etc.
    // that would panic during encoding. Scans both assert expressions AND
    // transition/event bodies (guards, updates, create fields).
    for assert_expr in &verify_block.asserts {
        let expanded = expand_through_defs(assert_expr, defs);
        if let Some(kind) = find_unsupported_scene_expr(&expanded) {
            return VerificationResult::Unprovable {
                name: verify_block.name.clone(),
                hint: format!("unsupported expression kind in verify assert: {kind}"),
                span: expr_span(assert_expr),
                file: None,
            };
        }
    }
    // Scan transition guards and update values for unsupported forms
    for entity in &relevant_entities {
        for trans in &entity.transitions {
            if let Some(kind) = find_unsupported_scene_expr(&trans.guard) {
                return VerificationResult::Unprovable {
                    name: verify_block.name.clone(),
                    hint: format!(
                        "unsupported expression in {}.{} guard: {kind}",
                        entity.name, trans.name
                    ),
                    span: None,
                    file: None,
                };
            }
            for upd in &trans.updates {
                if let Some(kind) = find_unsupported_scene_expr(&upd.value) {
                    return VerificationResult::Unprovable {
                        name: verify_block.name.clone(),
                        hint: format!(
                            "unsupported expression in {}.{} update of {}: {kind}",
                            entity.name, trans.name, upd.field
                        ),
                        span: None,
                        file: None,
                    };
                }
            }
        }
    }
    // Scan event guards and action bodies
    for sys in &relevant_systems {
        for event in &sys.events {
            if let Some(kind) = find_unsupported_scene_expr(&event.guard) {
                return VerificationResult::Unprovable {
                    name: verify_block.name.clone(),
                    hint: format!(
                        "unsupported expression in {}.{} event guard: {kind}",
                        sys.name, event.name
                    ),
                    span: None,
                    file: None,
                };
            }
            if let Some(kind) = find_unsupported_in_actions(&event.body) {
                return VerificationResult::Unprovable {
                    name: verify_block.name.clone(),
                    hint: format!(
                        "unsupported expression in {}.{} event body: {kind}",
                        sys.name, event.name
                    ),
                    span: None,
                    file: None,
                };
            }
        }
    }

    // ── 3. Create slot pool ────────────────────────────────────────
    let pool = create_slot_pool(&relevant_entities, &scope, bound);

    // ── 4. Build solver and assert constraints ─────────────────────
    let solver = Solver::new();
    if config.bmc_timeout_ms > 0 {
        set_solver_timeout(&solver, config.bmc_timeout_ms);
    }

    // Initial state: all slots inactive at step 0
    for c in initial_state_constraints(&pool) {
        solver.assert(&c);
    }

    // Symmetry breaking: slots activated in order to reduce search space
    for c in symmetry_breaking_constraints(&pool) {
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
        match encode_verify_properties(&pool, vctx, defs, &verify_block.asserts, bound) {
            Ok(prop) => prop,
            Err(msg) => {
                return VerificationResult::Unprovable {
                    name: verify_block.name.clone(),
                    hint: format!("encoding error: {msg}"),
                    span: None,
                    file: None,
                };
            }
        };

    // Negate the conjunction of all properties across all steps
    solver.assert(property_at_all_steps.not());

    // ── 6. Check and return result ─────────────────────────────────
    let elapsed = elapsed_ms(&start);

    match solver.check() {
        z3::SatResult::Unsat => VerificationResult::Checked {
            name: verify_block.name.clone(),
            depth: bound,
            time_ms: elapsed,
            span: None,
            file: None,
        },
        z3::SatResult::Sat => {
            let trace = extract_counterexample(&solver, &pool, &relevant_entities, bound);
            // Use the first assert's span when there's only one (common case).
            // For multi-assert blocks, with_source fills in the block span.
            let assert_span = if verify_block.asserts.len() == 1 {
                expr_span(&verify_block.asserts[0])
            } else {
                None
            };
            VerificationResult::Counterexample {
                name: verify_block.name.clone(),
                trace,
                span: assert_span,
                file: None,
            }
        }
        z3::SatResult::Unknown => {
            let hint = if config.bmc_timeout_ms > 0 {
                let timeout_display = if config.bmc_timeout_ms >= 1000 {
                    format!("{}s", config.bmc_timeout_ms / 1000)
                } else {
                    format!("{}ms", config.bmc_timeout_ms)
                };
                format!(
                    "Z3 timed out after {timeout_display} — try reducing bound, increasing --bmc-timeout, or simplifying property"
                )
            } else {
                crate::messages::BMC_UNKNOWN.to_owned()
            };
            VerificationResult::Unprovable {
                name: verify_block.name.clone(),
                hint,
                span: None,
                file: None,
            }
        }
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
            reason: crate::messages::SCENE_EMPTY_SCOPE.to_owned(),
            span: None,
            file: None,
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
                span: None,
                file: None,
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
        let constraint = match encode_prop_expr(&pool, vctx, defs, &given_ctx, &given.constraint, 0)
        {
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
                    span: None,
                    file: None,
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
                span: None,
                file: None,
            };
        };
        let Some(event) = sys.events.iter().find(|e| e.name == scene_event.event) else {
            return VerificationResult::SceneFail {
                name: scene.name.clone(),
                reason: format!(
                    "event {} not found in system {}",
                    scene_event.event, scene_event.system
                ),
                span: None,
                file: None,
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
                span: None,
                file: None,
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
                    span: None,
                    file: None,
                };
            }
        }

        if let Err(reason) = validate_crosscall_arities(&event.body, &relevant_systems, 0) {
            return VerificationResult::SceneFail {
                name: scene.name.clone(),
                reason,
                span: None,
                file: None,
            };
        }

        // Pre-validate event body for unsupported action forms
        if let Some(kind) = find_unsupported_in_actions(&event.body) {
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

        // Build override_params: resolve scene event args against current bindings.
        let mut override_params: HashMap<String, SmtValue> = HashMap::new();
        for (param, arg) in event.params.iter().zip(scene_event.args.iter()) {
            let arg_ctx = PropertyCtx::new();
            let arg_ctx = given_bindings
                .iter()
                .fold(arg_ctx, |ctx, (var, (ent, slot))| {
                    ctx.with_binding(var, ent, *slot)
                });
            let val = match encode_prop_value(&pool, vctx, defs, &arg_ctx, arg, step) {
                Ok(v) => v,
                Err(msg) => {
                    return VerificationResult::SceneFail {
                        name: scene.name.clone(),
                        reason: format!(
                            "encoding error in scene event arg for {}::{}: {msg}",
                            scene_event.system, scene_event.event
                        ),
                        span: None,
                        file: None,
                    };
                }
            };
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
        let prop = match encode_prop_expr(&pool, vctx, defs, &then_ctx, assertion, final_step) {
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
        z3::SatResult::Sat => VerificationResult::ScenePass {
            name: scene.name.clone(),
            time_ms: elapsed,
            span: None,
            file: None,
        },
        z3::SatResult::Unsat => VerificationResult::SceneFail {
            name: scene.name.clone(),
            reason: crate::messages::SCENE_UNSATISFIABLE.to_owned(),
            span: None,
            file: None,
        },
        z3::SatResult::Unknown => VerificationResult::SceneFail {
            name: scene.name.clone(),
            reason: crate::messages::SCENE_UNKNOWN.to_owned(),
            span: None,
            file: None,
        },
    }
}

// ── Theorem proving (IC3 → 1-induction) ─────────────────────────────

/// Check a theorem block using IC3/PDR, then 1-induction as fallback.
///
/// **IC3/PDR** is tried first — it automatically discovers strengthening
/// invariants, proving properties that aren't directly 1-inductive.
///
/// If IC3 fails or is skipped (`--no-ic3`), falls back to **4-phase
/// 1-induction** with user-provided invariants:
///
/// 0. Invariant base: I holds at step 0
/// 1. Invariant step: I(k) ∧ transition → I(k+1)
/// 2. Property base: P holds at step 0
/// 3. Property step: I(k) ∧ P(k) ∧ transition → P(k+1)
///
/// All phases pass → PROVED. Any fails → UNPROVABLE with hint.
#[allow(clippy::too_many_lines)]
fn check_theorem_block(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    theorem: &IRTheorem,
    config: &VerifyConfig,
) -> VerificationResult {
    let start = Instant::now();

    // ── Build scope from theorem systems ───────────────────────────
    let mut scope: HashMap<String, usize> = HashMap::new();
    let mut system_names: Vec<String> = theorem.systems.clone();

    // Analyze show expressions to determine required slots per entity type.
    // Count the quantifier nesting depth per entity type (e.g., `all a: X | all b: X | ...`
    // has depth 2 for entity X). Slots = max(2, depth + 1) — enough for all
    // simultaneously bound variables plus one for Create transitions.
    // Expand through DefEnv first so pred/prop bodies with entity quantifiers are counted.
    let mut required_slots: HashMap<String, usize> = HashMap::new();
    for show_expr in &theorem.shows {
        let expanded = expand_through_defs(show_expr, defs);
        let mut counts: HashMap<String, usize> = HashMap::new();
        count_entity_quantifiers(&expanded, &mut counts);
        for (entity, count) in &counts {
            let existing = required_slots.get(entity).copied().unwrap_or(0);
            required_slots.insert(entity.clone(), existing.max(*count));
        }
    }
    for inv_expr in &theorem.invariants {
        let expanded = expand_through_defs(inv_expr, defs);
        let mut counts: HashMap<String, usize> = HashMap::new();
        count_entity_quantifiers(&expanded, &mut counts);
        for (entity, count) in &counts {
            let existing = required_slots.get(entity).copied().unwrap_or(0);
            required_slots.insert(entity.clone(), existing.max(*count));
        }
    }

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
                // Slots = max(2, quantifier_depth + 1) — enough for the quantifier
                // structure plus one slot for Create transitions.
                let min_slots = required_slots.get(ent_name).copied().unwrap_or(0) + 1;
                scope.entry(ent_name.clone()).or_insert(min_slots.max(2));
            }
        }
    }

    if scope.is_empty() {
        return VerificationResult::Unprovable {
            name: theorem.name.clone(),
            hint: crate::messages::VERIFY_EMPTY_SCOPE.to_owned(),
            span: None,
            file: None,
        };
    }

    // Check for entity quantifiers over types not in scope — these would be vacuous.
    for entity_name in required_slots.keys() {
        if !scope.contains_key(entity_name) {
            return VerificationResult::Unprovable {
                name: theorem.name.clone(),
                hint: format!(
                    "theorem quantifies over entity {entity_name} which is not in scope \
                     of systems {:?} — quantifier would be vacuous",
                    theorem.systems
                ),
                span: None,
                file: None,
            };
        }
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

    // Strip `always` wrapper if present — induction proves always by construction.
    // Detect `eventually` which cannot be proved by induction.
    let mut show_exprs: Vec<&IRExpr> = Vec::new();
    for s in &theorem.shows {
        match s {
            IRExpr::Always { body, .. } => show_exprs.push(body.as_ref()),
            _ => show_exprs.push(s),
        }
    }

    // Check for `eventually` in show expressions — induction cannot prove liveness.
    // Expand through DefEnv first so pred/prop bodies with `eventually` are detected.
    for (i, show_expr) in show_exprs.iter().enumerate() {
        let expanded = expand_through_defs(show_expr, defs);
        if contains_eventually(&expanded) {
            return VerificationResult::Unprovable {
                name: theorem.name.clone(),
                hint: crate::messages::THEOREM_LIVENESS_UNSUPPORTED.to_owned(),
                span: expr_span(theorem.shows.get(i).unwrap_or(show_expr)),
                file: None,
            };
        }
    }

    // Pre-validate: reject unsupported expression forms that would panic during encoding.
    // Expand through DefEnv first — a pred body might contain unsupported forms.
    for (i, show_expr) in show_exprs.iter().enumerate() {
        let expanded = expand_through_defs(show_expr, defs);
        if let Some(kind) = find_unsupported_scene_expr(&expanded) {
            return VerificationResult::Unprovable {
                name: theorem.name.clone(),
                hint: format!("unsupported expression kind in theorem show: {kind}"),
                span: expr_span(theorem.shows.get(i).unwrap_or(show_expr)),
                file: None,
            };
        }
    }
    for inv_expr in &theorem.invariants {
        let expanded = expand_through_defs(inv_expr, defs);
        if let Some(kind) = find_unsupported_scene_expr(&expanded) {
            return VerificationResult::Unprovable {
                name: theorem.name.clone(),
                hint: format!("unsupported expression kind in theorem invariant: {kind}"),
                span: expr_span(inv_expr),
                file: None,
            };
        }
    }
    // Scan transition guards/updates and event bodies
    for entity in &relevant_entities {
        for trans in &entity.transitions {
            if let Some(kind) = find_unsupported_scene_expr(&trans.guard) {
                return VerificationResult::Unprovable {
                    name: theorem.name.clone(),
                    hint: format!(
                        "unsupported expression in {}.{} guard: {kind}",
                        entity.name, trans.name
                    ),
                    span: None,
                    file: None,
                };
            }
            for upd in &trans.updates {
                if let Some(kind) = find_unsupported_scene_expr(&upd.value) {
                    return VerificationResult::Unprovable {
                        name: theorem.name.clone(),
                        hint: format!(
                            "unsupported expression in {}.{} update of {}: {kind}",
                            entity.name, trans.name, upd.field
                        ),
                        span: None,
                        file: None,
                    };
                }
            }
        }
    }
    for sys in &relevant_systems {
        for event in &sys.events {
            if let Some(kind) = find_unsupported_scene_expr(&event.guard) {
                return VerificationResult::Unprovable {
                    name: theorem.name.clone(),
                    hint: format!(
                        "unsupported expression in {}.{} event guard: {kind}",
                        sys.name, event.name
                    ),
                    span: None,
                    file: None,
                };
            }
            if let Some(kind) = find_unsupported_in_actions(&event.body) {
                return VerificationResult::Unprovable {
                    name: theorem.name.clone(),
                    hint: format!(
                        "unsupported expression in {}.{} event body: {kind}",
                        sys.name, event.name
                    ),
                    span: None,
                    file: None,
                };
            }
        }
    }

    // ── bounded-only: theorems cannot be proved by BMC ────────────
    if config.bounded_only {
        return VerificationResult::Unprovable {
            name: theorem.name.clone(),
            hint: "--bounded-only was specified — theorems require unbounded proof \
                   (induction or IC3), not bounded model checking"
                .to_owned(),
            span: None,
            file: None,
        };
    }

    // ── Try IC3/PDR (more powerful than 1-induction) ───────────────
    // IC3 discovers strengthening invariants automatically. If it proves
    // the property, we're done. If not, fall through to 4-phase induction
    // which can leverage user-provided invariants.
    if let Some(result) = try_ic3_on_theorem(ir, vctx, defs, theorem, config) {
        return result;
    }

    // ── Phase 0: Verify invariants hold at step 0 ──────────────────
    // This prevents false invariants from making the step case vacuously true.
    if !theorem.invariants.is_empty() {
        let pool = create_slot_pool(&relevant_entities, &scope, 0);
        let solver = Solver::new();
        if config.induction_timeout_ms > 0 {
            set_solver_timeout(&solver, config.induction_timeout_ms);
        }

        for c in initial_state_constraints(&pool) {
            solver.assert(&c);
        }
        for c in domain_constraints(&pool, vctx, &relevant_entities) {
            solver.assert(&c);
        }

        // Assert NOT I at step 0 — if UNSAT, invariants hold initially
        let mut negated = Vec::new();
        for inv_expr in &theorem.invariants {
            let inv = match encode_property_at_step(&pool, vctx, defs, inv_expr, 0) {
                Ok(p) => p,
                Err(msg) => {
                    return VerificationResult::Unprovable {
                        name: theorem.name.clone(),
                        hint: format!("encoding error in invariant: {msg}"),
                        span: expr_span(inv_expr),
                        file: None,
                    };
                }
            };
            negated.push(inv.not());
        }
        let neg_refs: Vec<&Bool> = negated.iter().collect();
        if !neg_refs.is_empty() {
            solver.assert(Bool::or(&neg_refs));
        }

        match solver.check() {
            z3::SatResult::Unsat => {} // invariants hold initially
            z3::SatResult::Sat => {
                return VerificationResult::Unprovable {
                    name: theorem.name.clone(),
                    hint: "invariant does not hold at initial state — \
                           check that invariants are valid for the empty/initial configuration"
                        .to_owned(),
                    span: None,
                    file: None,
                };
            }
            z3::SatResult::Unknown => {
                return VerificationResult::Unprovable {
                    name: theorem.name.clone(),
                    hint: crate::messages::THEOREM_INV_BASE_UNKNOWN.to_owned(),
                    span: None,
                    file: None,
                };
            }
        }
    }

    // ── Phase 1: Verify invariants are preserved by transitions ────
    // I(k) ∧ transition(k→k+1) → I(k+1)
    if !theorem.invariants.is_empty() {
        let pool = create_slot_pool(&relevant_entities, &scope, 1);
        let solver = Solver::new();
        if config.induction_timeout_ms > 0 {
            set_solver_timeout(&solver, config.induction_timeout_ms);
        }

        for c in domain_constraints(&pool, vctx, &relevant_entities) {
            solver.assert(&c);
        }

        // Assume I at step 0
        for inv_expr in &theorem.invariants {
            let inv = match encode_property_at_step(&pool, vctx, defs, inv_expr, 0) {
                Ok(p) => p,
                Err(msg) => {
                    return VerificationResult::Unprovable {
                        name: theorem.name.clone(),
                        hint: format!("encoding error in invariant: {msg}"),
                        span: expr_span(inv_expr),
                        file: None,
                    };
                }
            };
            solver.assert(&inv);
        }

        let trans = transition_constraints(&pool, vctx, &relevant_entities, &relevant_systems, 0);
        solver.assert(&trans);

        // Assert NOT I at step 1
        let mut negated = Vec::new();
        for inv_expr in &theorem.invariants {
            let inv = match encode_property_at_step(&pool, vctx, defs, inv_expr, 1) {
                Ok(p) => p,
                Err(msg) => {
                    return VerificationResult::Unprovable {
                        name: theorem.name.clone(),
                        hint: format!("encoding error in invariant: {msg}"),
                        span: expr_span(inv_expr),
                        file: None,
                    };
                }
            };
            negated.push(inv.not());
        }
        let neg_refs: Vec<&Bool> = negated.iter().collect();
        if !neg_refs.is_empty() {
            solver.assert(Bool::or(&neg_refs));
        }

        match solver.check() {
            z3::SatResult::Unsat => {} // invariants are inductive
            z3::SatResult::Sat => {
                return VerificationResult::Unprovable {
                    name: theorem.name.clone(),
                    hint: "invariant is not preserved by transitions — \
                           the invariant itself is not inductive"
                        .to_owned(),
                    span: None,
                    file: None,
                };
            }
            z3::SatResult::Unknown => {
                return VerificationResult::Unprovable {
                    name: theorem.name.clone(),
                    hint: crate::messages::THEOREM_INV_STEP_UNKNOWN.to_owned(),
                    span: None,
                    file: None,
                };
            }
        }
    }

    // ── Phase 2: Base case — P holds at step 0 ─────────────────────
    {
        let pool = create_slot_pool(&relevant_entities, &scope, 0);
        let solver = Solver::new();
        if config.induction_timeout_ms > 0 {
            set_solver_timeout(&solver, config.induction_timeout_ms);
        }

        for c in initial_state_constraints(&pool) {
            solver.assert(&c);
        }
        for c in domain_constraints(&pool, vctx, &relevant_entities) {
            solver.assert(&c);
        }

        // Assert NOT P at step 0 — if UNSAT, P holds at initial state
        let mut negated = Vec::new();
        for show_expr in &show_exprs {
            let prop = match encode_property_at_step(&pool, vctx, defs, show_expr, 0) {
                Ok(p) => p,
                Err(msg) => {
                    return VerificationResult::Unprovable {
                        name: theorem.name.clone(),
                        hint: format!("encoding error in show expression: {msg}"),
                        span: None,
                        file: None,
                    };
                }
            };
            negated.push(prop.not());
        }
        let neg_refs: Vec<&Bool> = negated.iter().collect();
        if !neg_refs.is_empty() {
            solver.assert(Bool::or(&neg_refs));
        }

        match solver.check() {
            z3::SatResult::Unsat => {} // base case holds
            z3::SatResult::Sat => {
                return VerificationResult::Unprovable {
                    name: theorem.name.clone(),
                    hint: crate::messages::THEOREM_BASE_FAILED.to_owned(),
                    span: None,
                    file: None,
                };
            }
            z3::SatResult::Unknown => {
                return VerificationResult::Unprovable {
                    name: theorem.name.clone(),
                    hint: crate::messages::THEOREM_BASE_UNKNOWN.to_owned(),
                    span: None,
                    file: None,
                };
            }
        }
    }

    // ── Phase 3: Step case — I(k) ∧ P(k) ∧ transition → P(k+1) ───
    {
        let pool = create_slot_pool(&relevant_entities, &scope, 1);
        let solver = Solver::new();
        if config.induction_timeout_ms > 0 {
            set_solver_timeout(&solver, config.induction_timeout_ms);
        }

        for c in domain_constraints(&pool, vctx, &relevant_entities) {
            solver.assert(&c);
        }

        // Assume invariants at step 0
        for inv_expr in &theorem.invariants {
            let inv = match encode_property_at_step(&pool, vctx, defs, inv_expr, 0) {
                Ok(p) => p,
                Err(msg) => {
                    return VerificationResult::Unprovable {
                        name: theorem.name.clone(),
                        hint: format!("encoding error in invariant: {msg}"),
                        span: expr_span(inv_expr),
                        file: None,
                    };
                }
            };
            solver.assert(&inv);
        }

        // Assume P at step 0
        for show_expr in &show_exprs {
            let prop = match encode_property_at_step(&pool, vctx, defs, show_expr, 0) {
                Ok(p) => p,
                Err(msg) => {
                    return VerificationResult::Unprovable {
                        name: theorem.name.clone(),
                        hint: format!("encoding error in show expression: {msg}"),
                        span: None,
                        file: None,
                    };
                }
            };
            solver.assert(&prop);
        }

        // One transition step
        let trans = transition_constraints(&pool, vctx, &relevant_entities, &relevant_systems, 0);
        solver.assert(&trans);

        // Assert NOT P at step 1
        let mut negated = Vec::new();
        for show_expr in &show_exprs {
            let prop = match encode_property_at_step(&pool, vctx, defs, show_expr, 1) {
                Ok(p) => p,
                Err(msg) => {
                    return VerificationResult::Unprovable {
                        name: theorem.name.clone(),
                        hint: format!("encoding error in show expression: {msg}"),
                        span: None,
                        file: None,
                    };
                }
            };
            negated.push(prop.not());
        }
        let neg_refs: Vec<&Bool> = negated.iter().collect();
        if !neg_refs.is_empty() {
            solver.assert(Bool::or(&neg_refs));
        }

        match solver.check() {
            z3::SatResult::Unsat => {} // step case holds
            z3::SatResult::Sat => {
                return VerificationResult::Unprovable {
                    name: theorem.name.clone(),
                    hint: "inductive step failed — property is not preserved by transitions"
                        .to_owned(),
                    span: None,
                    file: None,
                };
            }
            z3::SatResult::Unknown => {
                return VerificationResult::Unprovable {
                    name: theorem.name.clone(),
                    hint: crate::messages::THEOREM_STEP_UNKNOWN.to_owned(),
                    span: None,
                    file: None,
                };
            }
        }
    }

    // Both base and step passed
    let elapsed = elapsed_ms(&start);

    // Report the method with scope details for inter-entity properties.
    let max_scope = scope.values().copied().max().unwrap_or(2);
    let method = if has_multi_entity_quantifier(&show_exprs) {
        format!("1-induction (scope: {max_scope} slots per entity type)")
    } else {
        "1-induction".to_owned()
    };

    VerificationResult::Proved {
        name: theorem.name.clone(),
        method,
        time_ms: elapsed,
        span: None,
        file: None,
    }
}

/// Try to prove a theorem's show expressions using IC3/PDR.
///
/// IC3 discovers strengthening invariants automatically, so user-provided
/// invariants are not needed. This is tried before 4-phase induction (since
/// IC3 is strictly more powerful for properties that need invariant discovery).
fn try_ic3_on_theorem(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    theorem: &IRTheorem,
    config: &VerifyConfig,
) -> Option<VerificationResult> {
    if config.no_ic3 {
        return None;
    }

    let start = Instant::now();

    // Build scope from theorem systems
    let mut scope: HashMap<String, usize> = HashMap::new();
    let mut system_names = theorem.systems.clone();

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
                scope.entry(ent_name.clone()).or_insert(2);
            }
        }
    }

    if scope.is_empty() {
        return None;
    }

    // Quantifier-based scope
    for show_expr in &theorem.shows {
        let expanded = expand_through_defs(show_expr, defs);
        let mut counts: HashMap<String, usize> = HashMap::new();
        count_entity_quantifiers(&expanded, &mut counts);
        for (entity, count) in counts {
            let min_slots = count + 1;
            if let Some(existing) = scope.get_mut(&entity) {
                *existing = (*existing).max(min_slots);
            }
        }
    }

    if config.progress {
        eprint!(" (trying IC3/PDR)");
    }

    // Try IC3 on each show expression
    for show_expr in &theorem.shows {
        let expanded = expand_through_defs(show_expr, defs);
        let result = ic3::try_ic3_system(
            ir,
            vctx,
            &system_names,
            &expanded,
            &scope,
            config.ic3_timeout_ms,
        );
        match result {
            ic3::Ic3Result::Proved => {}
            ic3::Ic3Result::Violated(trace) if !trace.is_empty() => {
                // Theorems have no BMC fallback, so IC3's trace is the best
                // counterexample available. The trace is extracted from the
                // CHC derivation tree, which may reflect the ForAll per-slot
                // over-approximation (see encode_event_chc doc). For confirmed
                // traces, users should write a verify block with BMC depth.
                return Some(VerificationResult::Counterexample {
                    name: theorem.name.clone(),
                    trace: ic3_trace_to_trace_steps(&trace),
                    span: None,
                    file: None,
                });
            }
            ic3::Ic3Result::Violated(_) | ic3::Ic3Result::Unknown(_) => return None,
        }
    }

    let elapsed = elapsed_ms(&start);
    Some(VerificationResult::Proved {
        name: theorem.name.clone(),
        method: "IC3/PDR".to_owned(),
        time_ms: elapsed,
        span: None,
        file: None,
    })
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
/// Check if an expression contains `Eventually` anywhere in its tree.
/// Induction cannot prove liveness — detect and reject early.
#[allow(clippy::match_same_arms)]
fn contains_eventually(expr: &IRExpr) -> bool {
    match expr {
        IRExpr::Eventually { .. } => true,
        IRExpr::Always { body, .. }
        | IRExpr::UnOp { operand: body, .. }
        | IRExpr::Field { expr: body, .. }
        | IRExpr::Prime { expr: body, .. } => contains_eventually(body),
        IRExpr::BinOp { left, right, .. }
        | IRExpr::App {
            func: left,
            arg: right,
            ..
        } => contains_eventually(left) || contains_eventually(right),
        IRExpr::Forall { body, .. } | IRExpr::Exists { body, .. } => contains_eventually(body),
        _ => false,
    }
}

/// Detect if show expressions have quantifier nesting depth > 1 for any entity type.
/// E.g., `all a: Account | all b: Account | P(a, b)` has depth 2 for Account.
/// Used to annotate PROVED output with scope info for inter-entity properties.
fn has_multi_entity_quantifier(show_exprs: &[&IRExpr]) -> bool {
    for expr in show_exprs {
        let mut entity_vars: HashMap<String, usize> = HashMap::new();
        count_entity_quantifiers(expr, &mut entity_vars);
        if entity_vars.values().any(|&count| count > 1) {
            return true;
        }
    }
    false
}

fn count_entity_quantifiers(expr: &IRExpr, counts: &mut HashMap<String, usize>) {
    match expr {
        IRExpr::Forall {
            domain: crate::ir::types::IRType::Entity { name },
            body,
            ..
        }
        | IRExpr::Exists {
            domain: crate::ir::types::IRType::Entity { name },
            body,
            ..
        } => {
            *counts.entry(name.clone()).or_insert(0) += 1;
            count_entity_quantifiers(body, counts);
        }
        IRExpr::BinOp { left, right, .. }
        | IRExpr::App {
            func: left,
            arg: right,
            ..
        } => {
            count_entity_quantifiers(left, counts);
            count_entity_quantifiers(right, counts);
        }
        IRExpr::UnOp { operand, .. }
        | IRExpr::Field { expr: operand, .. }
        | IRExpr::Prime { expr: operand, .. }
        | IRExpr::Card { expr: operand, .. }
        | IRExpr::Always { body: operand, .. }
        | IRExpr::Eventually { body: operand, .. } => {
            count_entity_quantifiers(operand, counts);
        }
        IRExpr::Forall { body, .. } | IRExpr::Exists { body, .. } => {
            count_entity_quantifiers(body, counts);
        }
        // SetComp introduces an entity binder — count it like Forall
        IRExpr::SetComp {
            domain: crate::ir::types::IRType::Entity { name },
            filter,
            projection,
            ..
        } => {
            *counts.entry(name.clone()).or_insert(0) += 1;
            count_entity_quantifiers(filter, counts);
            if let Some(proj) = projection {
                count_entity_quantifiers(proj, counts);
            }
        }
        IRExpr::SetComp {
            filter, projection, ..
        } => {
            count_entity_quantifiers(filter, counts);
            if let Some(proj) = projection {
                count_entity_quantifiers(proj, counts);
            }
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            count_entity_quantifiers(map, counts);
            count_entity_quantifiers(key, counts);
            count_entity_quantifiers(value, counts);
        }
        IRExpr::Index { map, key, .. } => {
            count_entity_quantifiers(map, counts);
            count_entity_quantifiers(key, counts);
        }
        _ => {}
    }
}

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
#[allow(clippy::too_many_lines)]
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
            ..
        } => IRExpr::BinOp {
            op: op.clone(),
            left: Box::new(expand_through_defs(left, defs)),
            right: Box::new(expand_through_defs(right, defs)),
            ty: ty.clone(),
            span: None,
        },
        IRExpr::UnOp {
            op, operand, ty, ..
        } => IRExpr::UnOp {
            op: op.clone(),
            operand: Box::new(expand_through_defs(operand, defs)),
            ty: ty.clone(),
            span: None,
        },
        IRExpr::Forall {
            var, domain, body, ..
        } => IRExpr::Forall {
            var: var.clone(),
            domain: domain.clone(),
            body: Box::new(expand_through_defs(body, defs)),
            span: None,
        },
        IRExpr::Exists {
            var, domain, body, ..
        } => IRExpr::Exists {
            var: var.clone(),
            domain: domain.clone(),
            body: Box::new(expand_through_defs(body, defs)),
            span: None,
        },
        IRExpr::Always { body, .. } => IRExpr::Always {
            body: Box::new(expand_through_defs(body, defs)),
            span: None,
        },
        IRExpr::Eventually { body, .. } => IRExpr::Eventually {
            body: Box::new(expand_through_defs(body, defs)),
            span: None,
        },
        IRExpr::Field {
            expr: inner,
            field,
            ty,
            ..
        } => IRExpr::Field {
            expr: Box::new(expand_through_defs(inner, defs)),
            field: field.clone(),
            ty: ty.clone(),
            span: None,
        },
        IRExpr::Prime { expr: inner, .. } => IRExpr::Prime {
            expr: Box::new(expand_through_defs(inner, defs)),
            span: None,
        },
        IRExpr::App { func, arg, ty, .. } => IRExpr::App {
            func: Box::new(expand_through_defs(func, defs)),
            arg: Box::new(expand_through_defs(arg, defs)),
            ty: ty.clone(),
            span: None,
        },
        IRExpr::Let { bindings, body, .. } => IRExpr::Let {
            bindings: bindings
                .iter()
                .map(|b| crate::ir::types::LetBinding {
                    name: b.name.clone(),
                    ty: b.ty.clone(),
                    expr: expand_through_defs(&b.expr, defs),
                })
                .collect(),
            body: Box::new(expand_through_defs(body, defs)),
            span: None,
        },
        IRExpr::Lam {
            param,
            param_type,
            body,
            ..
        } => IRExpr::Lam {
            param: param.clone(),
            param_type: param_type.clone(),
            body: Box::new(expand_through_defs(body, defs)),
            span: None,
        },
        IRExpr::Match {
            scrutinee, arms, ..
        } => IRExpr::Match {
            scrutinee: Box::new(expand_through_defs(scrutinee, defs)),
            arms: arms
                .iter()
                .map(|arm| crate::ir::types::IRMatchArm {
                    pattern: arm.pattern.clone(),
                    guard: arm.guard.as_ref().map(|g| expand_through_defs(g, defs)),
                    body: expand_through_defs(&arm.body, defs),
                })
                .collect(),
            span: None,
        },
        IRExpr::MapUpdate {
            map,
            key,
            value,
            ty,
            ..
        } => IRExpr::MapUpdate {
            map: Box::new(expand_through_defs(map, defs)),
            key: Box::new(expand_through_defs(key, defs)),
            value: Box::new(expand_through_defs(value, defs)),
            ty: ty.clone(),
            span: None,
        },
        IRExpr::Index { map, key, ty, .. } => IRExpr::Index {
            map: Box::new(expand_through_defs(map, defs)),
            key: Box::new(expand_through_defs(key, defs)),
            ty: ty.clone(),
            span: None,
        },
        IRExpr::Card { expr: inner, .. } => IRExpr::Card {
            expr: Box::new(expand_through_defs(inner, defs)),
            span: None,
        },
        IRExpr::SetComp {
            var,
            domain,
            filter,
            projection,
            ty,
            ..
        } => IRExpr::SetComp {
            var: var.clone(),
            domain: domain.clone(),
            filter: Box::new(expand_through_defs(filter, defs)),
            projection: projection
                .as_ref()
                .map(|p| Box::new(expand_through_defs(p, defs))),
            ty: ty.clone(),
            span: None,
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
        IRExpr::SetComp {
            domain: IRType::Entity { .. },
            filter,
            projection,
            ..
        } => {
            // Entity-domain comprehension is supported; check sub-expressions
            find_unsupported_scene_expr(filter).or_else(|| {
                projection
                    .as_ref()
                    .and_then(|p| find_unsupported_scene_expr(p))
            })
        }
        IRExpr::SetComp { .. } => Some("SetComp with non-entity domain"),
        IRExpr::Sorry { .. } => Some("Sorry"),
        IRExpr::Todo { .. } => Some("Todo"),
        IRExpr::Card { expr, .. } => match expr.as_ref() {
            // Compile-time literal cardinality — always supported
            IRExpr::SetLit { .. } | IRExpr::SeqLit { .. } | IRExpr::MapLit { .. } => None,
            // Entity-domain set comprehension — bounded sum over slots
            IRExpr::SetComp {
                domain: IRType::Entity { .. },
                filter,
                projection,
                ..
            } => find_unsupported_scene_expr(filter).or_else(|| {
                projection
                    .as_ref()
                    .and_then(|p| find_unsupported_scene_expr(p))
            }),
            // Anything else: unsupported (infinite domain, field expression, etc.)
            _ => Some("cardinality (#) of non-literal, non-comprehension expression"),
        },
        IRExpr::Field { expr, .. }
        | IRExpr::UnOp { operand: expr, .. }
        | IRExpr::Prime { expr, .. }
        | IRExpr::Always { body: expr, .. }
        | IRExpr::Eventually { body: expr, .. } => find_unsupported_scene_expr(expr),
        IRExpr::BinOp { left, right, .. } => {
            find_unsupported_scene_expr(left).or_else(|| find_unsupported_scene_expr(right))
        }
        IRExpr::App { func, arg, .. } => {
            // After def expansion, remaining App(Var(name), ...) means an
            // unresolvable function call that can't be encoded in Z3.
            if matches!(func.as_ref(), IRExpr::Var { .. }) {
                return Some(crate::messages::PRECHECK_UNRESOLVED_FN);
            }
            find_unsupported_scene_expr(func).or_else(|| find_unsupported_scene_expr(arg))
        }
        IRExpr::Forall { body, .. } | IRExpr::Exists { body, .. } => {
            find_unsupported_scene_expr(body)
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => find_unsupported_scene_expr(map)
            .or_else(|| find_unsupported_scene_expr(key))
            .or_else(|| find_unsupported_scene_expr(value)),
        IRExpr::Index { map, key, .. } => {
            find_unsupported_scene_expr(map).or_else(|| find_unsupported_scene_expr(key))
        }
        IRExpr::MapLit { entries, .. } => entries.iter().find_map(|(k, v)| {
            find_unsupported_scene_expr(k).or_else(|| find_unsupported_scene_expr(v))
        }),
        IRExpr::SetLit { elements, .. } | IRExpr::SeqLit { elements, .. } => {
            elements.iter().find_map(find_unsupported_scene_expr)
        }
        IRExpr::Lit { .. } | IRExpr::Var { .. } | IRExpr::Ctor { .. } => None,
        IRExpr::Block { .. } => Some("Block"),
        IRExpr::VarDecl { .. } => Some("VarDecl"),
        IRExpr::While { .. } => Some("While"),
        IRExpr::IfElse { .. } => Some("IfElse"),
    }
}

/// Scan action bodies for unsupported expression forms.
///
/// Walks Choose/ForAll/Apply/Create/CrossCall/ExprStmt and checks guards,
/// filters, create field values for unsupported expressions.
fn find_unsupported_in_actions(actions: &[IRAction]) -> Option<&'static str> {
    for action in actions {
        match action {
            IRAction::Choose { filter, ops, .. } => {
                if let Some(kind) = find_unsupported_scene_expr(filter) {
                    return Some(kind);
                }
                if let Some(kind) = find_unsupported_in_actions(ops) {
                    return Some(kind);
                }
            }
            IRAction::ForAll { var, ops, .. } => {
                let apply_count = ops
                    .iter()
                    .filter(|op| matches!(op, IRAction::Apply { target, .. } if target == var))
                    .count();
                if apply_count > 1 {
                    return Some(
                        "multiple Apply actions on the same entity in one ForAll block \
                         (sequential composition not yet supported — split into separate events)",
                    );
                }
                if let Some(kind) = find_unsupported_in_actions(ops) {
                    return Some(kind);
                }
            }
            IRAction::Create { fields, .. } => {
                for f in fields {
                    if let Some(kind) = find_unsupported_scene_expr(&f.value) {
                        return Some(kind);
                    }
                }
            }
            IRAction::ExprStmt { expr } => {
                if let Some(kind) = find_unsupported_scene_expr(expr) {
                    return Some(kind);
                }
            }
            IRAction::Apply { args, .. } | IRAction::CrossCall { args, .. } => {
                for arg in args {
                    if let Some(kind) = find_unsupported_scene_expr(arg) {
                        return Some(kind);
                    }
                }
            }
        }
    }
    None
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
) -> Result<Bool, String> {
    let mut all_props = Vec::new();

    for assert_expr in asserts {
        match assert_expr {
            // `always P` — check P at every step
            IRExpr::Always { body, .. } => {
                for step in 0..=bound {
                    let prop = encode_property_at_step(pool, vctx, defs, body, step)?;
                    all_props.push(prop);
                }
            }
            // `eventually P` — check P at some step (disjunction)
            IRExpr::Eventually { body, .. } => {
                let mut step_props = Vec::new();
                for step in 0..=bound {
                    let prop = encode_property_at_step(pool, vctx, defs, body, step)?;
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
                    let prop = encode_property_at_step(pool, vctx, defs, other, step)?;
                    all_props.push(prop);
                }
            }
        }
    }

    if all_props.is_empty() {
        return Ok(Bool::from_bool(true));
    }

    let refs: Vec<&Bool> = all_props.iter().collect();
    Ok(Bool::and(&refs))
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
) -> Result<Bool, String> {
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
) -> Result<Bool, String> {
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
            ..
        } => {
            let n_slots = pool.slots_for(entity_name);
            let mut conjuncts = Vec::new();
            for slot in 0..n_slots {
                let active = pool.active_at(entity_name, slot, step);
                let inner_ctx = ctx.with_binding(var, entity_name, slot);
                let body_val = encode_prop_expr(pool, vctx, defs, &inner_ctx, body, step)?;
                if let Some(SmtValue::Bool(act)) = active {
                    // active => P(slot)
                    conjuncts.push(act.implies(&body_val));
                }
            }
            if conjuncts.is_empty() {
                return Ok(Bool::from_bool(true));
            }
            let refs: Vec<&Bool> = conjuncts.iter().collect();
            Ok(Bool::and(&refs))
        }
        // `exists x: Entity | P(x)` — disjunction over active slots
        IRExpr::Exists {
            var,
            domain: crate::ir::types::IRType::Entity { name: entity_name },
            body,
            ..
        } => {
            let n_slots = pool.slots_for(entity_name);
            let mut disjuncts = Vec::new();
            for slot in 0..n_slots {
                let active = pool.active_at(entity_name, slot, step);
                let inner_ctx = ctx.with_binding(var, entity_name, slot);
                let body_val = encode_prop_expr(pool, vctx, defs, &inner_ctx, body, step)?;
                if let Some(SmtValue::Bool(act)) = active {
                    // active AND P(slot)
                    disjuncts.push(Bool::and(&[act, &body_val]));
                }
            }
            if disjuncts.is_empty() {
                return Ok(Bool::from_bool(false));
            }
            let refs: Vec<&Bool> = disjuncts.iter().collect();
            Ok(Bool::or(&refs))
        }
        // Boolean connectives — recurse
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpAnd" || op == "OpOr" || op == "OpImplies" || op == "OpXor" => {
            let l = encode_prop_expr(pool, vctx, defs, ctx, left, step)?;
            let r = encode_prop_expr(pool, vctx, defs, ctx, right, step)?;
            match op.as_str() {
                "OpAnd" => Ok(Bool::and(&[&l, &r])),
                "OpOr" => Ok(Bool::or(&[&l, &r])),
                "OpImplies" => Ok(l.implies(&r)),
                "OpXor" => Ok(Bool::xor(&l, &r)),
                _ => Err(format!("unsupported boolean operator: {op}")),
            }
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => {
            let inner = encode_prop_expr(pool, vctx, defs, ctx, operand, step)?;
            Ok(inner.not())
        }
        // Nested temporal operators — in BMC, `always P` at a single step
        // is just P (the outer loop iterates over steps), and `eventually P`
        // is also just P at this step (the outer loop handles the disjunction).
        IRExpr::Always { body, .. } | IRExpr::Eventually { body, .. } => {
            encode_prop_expr(pool, vctx, defs, ctx, body, step)
        }
        // Comparison and other BinOps that produce Bool (OpEq, OpNEq, OpLt, etc.)
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let l = encode_prop_value(pool, vctx, defs, ctx, left, step)?;
            let r = encode_prop_value(pool, vctx, defs, ctx, right, step)?;
            Ok(smt::binop(op, &l, &r)?.to_bool()?)
        }
        // Literals
        IRExpr::Lit {
            value: crate::ir::types::LitVal::Bool { value },
            ..
        } => Ok(Bool::from_bool(*value)),
        // Everything else: encode as value and convert to Bool
        other => {
            let val = encode_prop_value(pool, vctx, defs, ctx, other, step)?;
            Ok(val.to_bool()?)
        }
    }
}

/// Encode a value expression using the multi-entity quantifier context.
///
/// Resolves field references like `s.user_id` by looking up `"s"` in the
/// `PropertyCtx` bindings to find the bound entity and slot index,
/// then resolves via `pool.field_at(entity, slot, field, step)`.
#[allow(clippy::too_many_lines)]
fn encode_prop_value(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    ctx: &PropertyCtx,
    expr: &IRExpr,
    step: usize,
) -> Result<SmtValue, String> {
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
            crate::ir::types::LitVal::Int { value } => Ok(smt::int_val(*value)),
            crate::ir::types::LitVal::Bool { value } => Ok(smt::bool_val(*value)),
            crate::ir::types::LitVal::Real { value }
            | crate::ir::types::LitVal::Float { value } => {
                #[allow(clippy::cast_possible_truncation)]
                let scaled = (*value * 1_000_000.0) as i64;
                Ok(smt::real_val(scaled, 1_000_000))
            }
            crate::ir::types::LitVal::Str { .. } => Ok(smt::int_val(0)),
        },
        // Field access: `var.field` — look up var in bindings, resolve field from bound entity
        IRExpr::Field {
            expr: recv, field, ..
        } => {
            // Try to resolve the receiver as a bound variable
            if let IRExpr::Var { name, .. } = recv.as_ref() {
                if let Some((entity, slot)) = ctx.bindings.get(name) {
                    if let Some(val) = pool.field_at(entity, *slot, field, step) {
                        return Ok(val.clone());
                    }
                    return Err(format!(
                        "field not found: {entity}.{field} (var={name}, slot={slot}, step={step})"
                    ));
                }
            }
            // No binding for receiver — try all bindings to find the field
            for (entity, slot) in ctx.bindings.values() {
                if let Some(val) = pool.field_at(entity, *slot, field, step) {
                    return Ok(val.clone());
                }
            }
            Err(format!(
                "field not found in any bound entity: {field} (step={step})"
            ))
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
                0 => Err(format!(
                    "variable not found in any bound entity context: {name} (bindings: {:?}, step={step})",
                    ctx.bindings.keys().collect::<Vec<_>>()
                )),
                1 => match matches.into_iter().next() {
                    Some((_, _, val)) => Ok(val),
                    None => Err(format!("variable not found: {name} (step={step})")),
                },
                _ => Err(format!(
                    "ambiguous bare variable: {name} found in entities {:?} — use qualified access (e.g., var.{name})",
                    matches.iter().map(|(v, e, _)| format!("{v}:{e}")).collect::<Vec<_>>()
                )),
            }
        }
        IRExpr::Ctor {
            enum_name, ctor, ..
        } => {
            let id = vctx.variants.id_of(enum_name, ctor);
            Ok(smt::int_val(id))
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let l = encode_prop_value(pool, vctx, defs, ctx, left, step)?;
            let r = encode_prop_value(pool, vctx, defs, ctx, right, step)?;
            Ok(smt::binop(op, &l, &r)?)
        }
        IRExpr::UnOp { op, operand, .. } => {
            let v = encode_prop_value(pool, vctx, defs, ctx, operand, step)?;
            Ok(smt::unop(op, &v)?)
        }
        IRExpr::Prime { expr, .. } => encode_prop_value(pool, vctx, defs, ctx, expr, step + 1),
        // Nested quantifiers in value position — encode as Bool, wrap as SmtValue
        IRExpr::Forall { .. } | IRExpr::Exists { .. } => Ok(SmtValue::Bool(encode_prop_expr(
            pool, vctx, defs, ctx, expr, step,
        )?)),
        IRExpr::Always { body, .. } => Ok(SmtValue::Bool(encode_prop_expr(
            pool, vctx, defs, ctx, body, step,
        )?)),
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            let arr = encode_prop_value(pool, vctx, defs, ctx, map, step)?;
            let k = encode_prop_value(pool, vctx, defs, ctx, key, step)?;
            let v = encode_prop_value(pool, vctx, defs, ctx, value, step)?;
            Ok(SmtValue::Array(
                arr.as_array()?.store(&k.to_dynamic(), &v.to_dynamic()),
            ))
        }
        IRExpr::Index { map, key, .. } => {
            let arr = encode_prop_value(pool, vctx, defs, ctx, map, step)?;
            let k = encode_prop_value(pool, vctx, defs, ctx, key, step)?;
            Ok(SmtValue::Dynamic(arr.as_array()?.select(&k.to_dynamic())))
        }
        IRExpr::MapLit { entries, ty, .. } => {
            let (key_ty, val_ty) = match ty {
                IRType::Map { key, value } => (key.as_ref(), value.as_ref()),
                _ => return Err(format!("MapLit with non-Map type: {ty:?}")),
            };
            let key_sort = smt::ir_type_to_sort(key_ty);
            let default_val = smt::default_dynamic(val_ty);
            let mut arr = z3::ast::Array::const_array(&key_sort, &default_val);
            for (k_expr, v_expr) in entries {
                let k = encode_prop_value(pool, vctx, defs, ctx, k_expr, step)?;
                let v = encode_prop_value(pool, vctx, defs, ctx, v_expr, step)?;
                arr = arr.store(&k.to_dynamic(), &v.to_dynamic());
            }
            Ok(SmtValue::Array(arr))
        }
        IRExpr::SetLit { elements, ty, .. } => {
            let elem_ty = match ty {
                IRType::Set { element } => element.as_ref(),
                _ => return Err(format!("SetLit with non-Set type: {ty:?}")),
            };
            let elem_sort = smt::ir_type_to_sort(elem_ty);
            let false_val = smt::bool_val(false).to_dynamic();
            let true_val = smt::bool_val(true).to_dynamic();
            let mut arr = z3::ast::Array::const_array(&elem_sort, &false_val);
            for elem in elements {
                let e = encode_prop_value(pool, vctx, defs, ctx, elem, step)?;
                arr = arr.store(&e.to_dynamic(), &true_val);
            }
            Ok(SmtValue::Array(arr))
        }
        IRExpr::SeqLit { elements, ty, .. } => {
            let elem_ty = match ty {
                IRType::Seq { element } => element.as_ref(),
                _ => return Err(format!("SeqLit with non-Seq type: {ty:?}")),
            };
            let default_val = smt::default_dynamic(elem_ty);
            let mut arr = z3::ast::Array::const_array(&z3::Sort::int(), &default_val);
            for (i, elem) in elements.iter().enumerate() {
                let idx = smt::int_val(i64::try_from(i).unwrap_or(0)).to_dynamic();
                let v = encode_prop_value(pool, vctx, defs, ctx, elem, step)?;
                arr = arr.store(&idx, &v.to_dynamic());
            }
            Ok(SmtValue::Array(arr))
        }
        IRExpr::SetComp {
            var,
            domain: IRType::Entity { name: entity_name },
            filter,
            projection,
            ty,
            ..
        } => {
            // Set comprehension over entity slots.
            // Simple: { a: E where P(a) } → Array<Int, Bool> (slot index → member)
            // Projection: { f(a) | a: E where P(a) } → Array<T, Bool> (value → member)
            let n_slots = pool.slots_for(entity_name);
            let result_elem_sort = match (projection.as_ref(), ty) {
                (Some(_), IRType::Set { element }) => smt::ir_type_to_sort(element),
                (Some(_), _) => {
                    return Err(format!(
                        "projection SetComp with non-Set result type: {ty:?}"
                    ))
                }
                (None, _) => z3::Sort::int(), // simple form: slot indices are Int
            };
            let false_val = smt::bool_val(false).to_dynamic();
            let true_val = smt::bool_val(true).to_dynamic();
            let mut arr = z3::ast::Array::const_array(&result_elem_sort, &false_val);

            for slot in 0..n_slots {
                let active = pool.active_at(entity_name, slot, step);
                let is_active = match active {
                    Some(SmtValue::Bool(act)) => act.clone(),
                    _ => continue,
                };
                let inner_ctx = ctx.with_binding(var, entity_name, slot);
                let filter_val = encode_prop_expr(pool, vctx, defs, &inner_ctx, filter, step)?;
                // Condition: slot is active AND filter holds
                let cond = Bool::and(&[&is_active, &filter_val]);

                // Key: what to store true at
                let key = if let Some(proj_expr) = projection {
                    // Projection: store true at the projected value
                    encode_prop_value(pool, vctx, defs, &inner_ctx, proj_expr, step)?.to_dynamic()
                } else {
                    // Simple: store true at the slot index
                    smt::int_val(i64::try_from(slot).unwrap_or(0)).to_dynamic()
                };

                // Conditional store: ite(cond, store(arr, key, true), arr)
                let stored = arr.store(&key, &true_val);
                arr = cond.ite(&stored, &arr);
            }
            Ok(SmtValue::Array(arr))
        }
        IRExpr::SetComp { domain, .. } => {
            // Non-entity domain — should be caught by find_unsupported_scene_expr,
            // but if reached (e.g., manually constructed IR), return a fresh
            // unconstrained array rather than panicking.
            let sort = smt::ir_type_to_sort(domain);
            let false_val = smt::bool_val(false).to_dynamic();
            Ok(SmtValue::Array(z3::ast::Array::const_array(
                &sort, &false_val,
            )))
        }
        IRExpr::Card { expr: inner, .. } => encode_card(pool, vctx, defs, ctx, inner, step),
        IRExpr::App { func, .. } => {
            if let IRExpr::Var { name, .. } = func.as_ref() {
                return Err(format!(
                    "function `{name}` reached encoding without expansion \
                     (should have been caught by pre-validation)"
                ));
            }
            Err(format!(
                "unsupported App expression reached encoding: {expr:?}"
            ))
        }
        _ => Err(format!("unsupported expression reached encoding: {expr:?}")),
    }
}

/// Encode cardinality (`#expr`) as a Z3 Int.
///
/// - **Literals** (`SetLit`, `SeqLit`, `MapLit`): compile-time constant.
/// - **Entity set comprehension** `#{ x: E where P(x) }`: exact bounded sum
///   `Σ ite(active[i] ∧ P(i), 1, 0)` over entity slots. This is the primary
///   use case in Abide specs (e.g., `#{ o: Order where o.status == @Pending } > 0`).
/// - **Projection comprehension** `#{ f(x) | x: E where P(x) }`: bounded sum
///   that counts matching slots (may overcount if projection collapses duplicates —
///   sound as upper bound for `> 0` checks, not exact for `== N`).
/// - **Other**: panics (should be caught by `find_unsupported_scene_expr`).
fn encode_card(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    ctx: &PropertyCtx,
    inner: &IRExpr,
    step: usize,
) -> Result<SmtValue, String> {
    match inner {
        IRExpr::SetLit { elements, .. } => {
            let unique: std::collections::HashSet<String> =
                elements.iter().map(|e| format!("{e:?}")).collect();
            Ok(smt::int_val(i64::try_from(unique.len()).unwrap_or(0)))
        }
        IRExpr::SeqLit { elements, .. } => {
            Ok(smt::int_val(i64::try_from(elements.len()).unwrap_or(0)))
        }
        IRExpr::MapLit { entries, .. } => {
            let unique_keys: std::collections::HashSet<String> =
                entries.iter().map(|(k, _)| format!("{k:?}")).collect();
            Ok(smt::int_val(i64::try_from(unique_keys.len()).unwrap_or(0)))
        }
        // Entity-domain set comprehension: bounded sum over slots
        IRExpr::SetComp {
            var,
            domain: IRType::Entity { name: entity_name },
            filter,
            ..
        } => {
            let n_slots = pool.slots_for(entity_name);
            let mut sum_terms: Vec<z3::ast::Int> = Vec::new();
            let one = z3::ast::Int::from_i64(1);
            let zero = z3::ast::Int::from_i64(0);

            for slot in 0..n_slots {
                let is_active = match pool.active_at(entity_name, slot, step) {
                    Some(SmtValue::Bool(act)) => act.clone(),
                    _ => continue,
                };
                let inner_ctx = ctx.with_binding(var, entity_name, slot);
                let filter_val = encode_prop_expr(pool, vctx, defs, &inner_ctx, filter, step)?;
                let cond = Bool::and(&[&is_active, &filter_val]);
                sum_terms.push(cond.ite(&one, &zero));
            }

            if sum_terms.is_empty() {
                return Ok(smt::int_val(0));
            }
            let refs: Vec<&z3::ast::Int> = sum_terms.iter().collect();
            Ok(SmtValue::Int(z3::ast::Int::add(&refs)))
        }
        _ => Err(format!("unsupported cardinality expression: {inner:?}")),
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
                            SmtValue::Array(a) => model
                                .eval(a, true)
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
                ..
            } => write!(f, "PROVED  {name} (method: {method}, {time_ms}ms)"),
            VerificationResult::Checked {
                name,
                depth,
                time_ms,
                ..
            } => write!(f, "CHECKED {name} (depth: {depth}, {time_ms}ms)"),
            VerificationResult::Counterexample { name, trace, .. } => {
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
            VerificationResult::ScenePass { name, time_ms, .. } => {
                write!(f, "PASS    {name} ({time_ms}ms)")
            }
            VerificationResult::SceneFail { name, reason, .. } => {
                write!(f, "FAIL    {name}: {reason}")
            }
            VerificationResult::Unprovable { name, hint, .. } => {
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

                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "OrderStatus".to_owned(),
                        ctor: "Pending".to_owned(),

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

                        span: None,
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

        let verify = IRVerify {
            name: "test_verify".to_owned(),
            systems: vec![IRVerifySystem {
                name: "Commerce".to_owned(),
                lo: 0,
                hi: bound,
            }],
            asserts: vec![assert_expr],
            span: None,
            file: None,
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

                            span: None,
                        }),
                        field: "status".to_owned(),
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
                }),

                span: None,
            }),

            span: None,
        };

        let ir = make_order_ir(property, 3);
        let results = verify_all(&ir, &VerifyConfig::default());

        assert_eq!(results.len(), 1);
        assert!(
            matches!(&results[0], VerificationResult::Checked { name, .. } | VerificationResult::Proved { name, .. } if name == "test_verify"),
            "expected CHECKED or PROVED, got: {:?}",
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

                                span: None,
                            }),
                            field: "status".to_owned(),
                            ty: IRType::Int,

                            span: None,
                        }),
                        right: Box::new(IRExpr::Ctor {
                            enum_name: "OrderStatus".to_owned(),
                            ctor: "Pending".to_owned(),

                            span: None,
                        }),
                        ty: IRType::Bool,

                        span: None,
                    }),

                    span: None,
                }),

                span: None,
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

                span: None,
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

                            span: None,
                        },
                    },
                    IRCreateField {
                        name: "status".to_owned(),
                        value: IRExpr::Ctor {
                            enum_name: "OrderStatus".to_owned(),
                            ctor: "Pending".to_owned(),

                            span: None,
                        },
                    },
                ],
            }],
        });

        let results = verify_all(&ir, &VerifyConfig::default());

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
        let results = verify_all(&ir, &VerifyConfig::default());
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

                span: None,
            },
            postcondition: None,
            body: vec![IRAction::ExprStmt {
                expr: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
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

                                span: None,
                            },
                        }],
                        body: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },

                            span: None,
                        }),

                        span: None,
                    },
                }],
                events: vec![],
                ordering: vec![],
                assertions: vec![],
                span: None,
                file: None,
            }],
        };

        let results = verify_all(&ir, &VerifyConfig::default());
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

                    span: None,
                },
                postcondition: None,
                body: vec![IRAction::CrossCall {
                    system: "Callee".to_owned(),
                    event: "run".to_owned(),
                    args: vec![IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },

                        span: None,
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

                    span: None,
                },
                postcondition: None,
                body: vec![IRAction::ExprStmt {
                    expr: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
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
                span: None,
                file: None,
            }],
        };

        let results = verify_all(&ir, &VerifyConfig::default());
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

                        span: None,
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

                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Active".to_owned(),

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                },
                updates: vec![IRUpdate {
                    field: "status".to_owned(),
                    value: IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Locked".to_owned(),

                        span: None,
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

                    span: None,
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

                                span: None,
                            }),
                            field: "id".to_owned(),
                            ty: IRType::Id,

                            span: None,
                        }),
                        right: Box::new(IRExpr::Var {
                            name: "account_id".to_owned(),
                            ty: IRType::Id,

                            span: None,
                        }),
                        ty: IRType::Bool,

                        span: None,
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

                            span: None,
                        }),
                        field: "status".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Active".to_owned(),

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
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

                        span: None,
                    }),
                    field: "id".to_owned(),
                    ty: IRType::Id,

                    span: None,
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

                        span: None,
                    }),
                    field: "status".to_owned(),
                    ty: IRType::Int,

                    span: None,
                }),
                right: Box::new(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Locked".to_owned(),

                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            }],
            span: None,
            file: None,
        };

        let ir = make_scene_test_ir(scene);
        let results = verify_all(&ir, &VerifyConfig::default());
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

                            span: None,
                        }),
                        field: "status".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Active".to_owned(),

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
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

                        span: None,
                    }),
                    field: "id".to_owned(),
                    ty: IRType::Id,

                    span: None,
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

                        span: None,
                    }),
                    field: "status".to_owned(),
                    ty: IRType::Int,

                    span: None,
                }),
                right: Box::new(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Active".to_owned(),

                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            }],
            span: None,
            file: None,
        };

        let ir = make_scene_test_ir(scene);
        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 1);
        assert!(
            matches!(&results[0], VerificationResult::SceneFail { .. }),
            "expected SceneFail, got: {:?}",
            results[0]
        );
    }

    #[test]
    fn theorem_proved_by_induction() {
        // Theorem: status is always a valid enum variant (never -1).
        // This is trivially inductive — domain constraints enforce it at every step.
        let mut ir = make_order_ir(
            IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            3,
        );
        ir.verifies.clear(); // remove verify block
        ir.theorems.push(IRTheorem {
            name: "status_valid".to_owned(),
            systems: vec!["Commerce".to_owned()],
            invariants: vec![],
            shows: vec![IRExpr::Always {
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
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: -1 },

                            span: None,
                        }),
                        ty: IRType::Bool,

                        span: None,
                    }),

                    span: None,
                }),

                span: None,
            }],
            span: None,
            file: None,
        });

        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 1);
        assert!(
            matches!(&results[0], VerificationResult::Proved { .. }),
            "expected Proved, got: {:?}",
            results[0]
        );
    }

    #[test]
    fn theorem_unprovable_when_not_inductive() {
        // Theorem: all orders are always Pending.
        // This is NOT inductive — the confirm transition changes Pending → Confirmed.
        let mut ir = make_order_ir(
            IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            3,
        );
        // Add a create event so orders can exist
        ir.systems[0].events.push(IREvent {
            name: "create_order".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
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

                            span: None,
                        },
                    },
                    IRCreateField {
                        name: "status".to_owned(),
                        value: IRExpr::Ctor {
                            enum_name: "OrderStatus".to_owned(),
                            ctor: "Pending".to_owned(),

                            span: None,
                        },
                    },
                ],
            }],
        });
        ir.verifies.clear();
        ir.theorems.push(IRTheorem {
            name: "always_pending".to_owned(),
            systems: vec!["Commerce".to_owned()],
            invariants: vec![],
            shows: vec![IRExpr::Always {
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
                            enum_name: "OrderStatus".to_owned(),
                            ctor: "Pending".to_owned(),

                            span: None,
                        }),
                        ty: IRType::Bool,

                        span: None,
                    }),

                    span: None,
                }),

                span: None,
            }],
            span: None,
            file: None,
        });

        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 1);
        // IC3 finds the actual counterexample (Pending→Confirmed) with trace.
        assert!(
            matches!(&results[0], VerificationResult::Counterexample { trace, .. } if !trace.is_empty()),
            "expected Counterexample with non-empty trace, got: {:?}",
            results[0]
        );
    }

    #[test]
    fn tiered_bounded_only_skips_induction() {
        // With bounded_only, an inductive property should be CHECKED (not PROVED)
        let ir = make_order_ir(
            IRExpr::Always {
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
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: -1 },

                            span: None,
                        }),
                        ty: IRType::Bool,

                        span: None,
                    }),

                    span: None,
                }),

                span: None,
            },
            3,
        );
        let config = VerifyConfig {
            bounded_only: true,
            ..VerifyConfig::default()
        };
        let results = verify_all(&ir, &config);
        assert_eq!(results.len(), 1);
        assert!(
            matches!(&results[0], VerificationResult::Checked { .. }),
            "expected CHECKED with bounded_only, got: {:?}",
            results[0]
        );
    }

    #[test]
    fn tiered_unbounded_only_returns_unknown_on_failure() {
        // With unbounded_only, a non-inductive property should be UNKNOWN (not CHECKED)
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

                                span: None,
                            }),
                            field: "status".to_owned(),
                            ty: IRType::Int,

                            span: None,
                        }),
                        right: Box::new(IRExpr::Ctor {
                            enum_name: "OrderStatus".to_owned(),
                            ctor: "Pending".to_owned(),

                            span: None,
                        }),
                        ty: IRType::Bool,

                        span: None,
                    }),

                    span: None,
                }),

                span: None,
            },
            3,
        );
        // Add create so induction step fails (status changes via confirm)
        ir.systems[0].events.push(IREvent {
            name: "create_order".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
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

                            span: None,
                        },
                    },
                    IRCreateField {
                        name: "status".to_owned(),
                        value: IRExpr::Ctor {
                            enum_name: "OrderStatus".to_owned(),
                            ctor: "Pending".to_owned(),

                            span: None,
                        },
                    },
                ],
            }],
        });
        let config = VerifyConfig {
            unbounded_only: true,
            ..VerifyConfig::default()
        };
        let results = verify_all(&ir, &config);
        assert_eq!(results.len(), 1);
        // IC3 now finds the actual violation even in unbounded-only mode,
        // producing a Counterexample. If IC3 fails, falls back to Unprovable.
        assert!(
            matches!(
                &results[0],
                VerificationResult::Counterexample { .. } | VerificationResult::Unprovable { .. }
            ),
            "expected Counterexample or Unprovable with unbounded_only, got: {:?}",
            results[0]
        );
    }

    #[test]
    fn bmc_timeout_returns_unknown() {
        // With a 1ms BMC timeout, even a simple property should return UNKNOWN
        // because the solver can't finish in time.
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
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: -1 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
        };
        let ir = make_order_ir(property, 10);
        let config = VerifyConfig {
            bounded_only: true,
            bmc_timeout_ms: 1, // 1ms — too short to solve
            ..VerifyConfig::default()
        };
        let results = verify_all(&ir, &config);
        assert_eq!(results.len(), 1);
        // Should be either CHECKED (if solver is fast enough) or UNKNOWN (timeout)
        // On most systems, 1ms is too short for depth 10, but Z3 may be fast enough.
        // Accept either — the important thing is it doesn't panic.
        assert!(
            matches!(
                &results[0],
                VerificationResult::Checked { .. } | VerificationResult::Unprovable { .. }
            ),
            "expected CHECKED or UNKNOWN with 1ms timeout, got: {:?}",
            results[0]
        );
    }

    #[test]
    fn symmetry_breaking_does_not_regress_results() {
        // Symmetry breaking should not change correctness — valid properties should
        // still pass. The counterexample case is covered by bmc_counterexample_on_violation
        // which also runs with symmetry breaking active (it's always on).
        let valid_property = IRExpr::Always {
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
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: -1 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
        };
        let ir = make_order_ir(valid_property, 3);
        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 1);
        assert!(
            matches!(
                &results[0],
                VerificationResult::Checked { .. } | VerificationResult::Proved { .. }
            ),
            "valid property should be CHECKED or PROVED with symmetry breaking, got: {:?}",
            results[0]
        );
    }

    // ── IC3 integration tests ──────────────────────────────────────

    /// Test: property proved by IC3 that 1-induction can't prove.
    ///
    /// Entity has two fields (x, y) both starting at 0, with a transition
    /// that increments both. Property: `y <= 10`. This requires the
    /// strengthening invariant `y == x` (so the guard `x < 10` constrains y).
    /// 1-induction fails because from an arbitrary state with y=10, x could
    /// be anything, and y'=11 violates the property. IC3 discovers `y == x`.
    #[test]
    fn ic3_proves_property_induction_cannot() {
        let entity = IREntity {
            name: "Counter".to_owned(),
            fields: vec![
                IRField {
                    name: "x".to_owned(),
                    ty: IRType::Int,
                    default: Some(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },

                        span: None,
                    }),
                },
                IRField {
                    name: "y".to_owned(),
                    ty: IRType::Int,
                    default: Some(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },

                        span: None,
                    }),
                },
            ],
            transitions: vec![IRTransition {
                name: "step".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::BinOp {
                    op: "OpLt".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 10 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                },
                updates: vec![
                    IRUpdate {
                        field: "x".to_owned(),
                        value: IRExpr::BinOp {
                            op: "OpAdd".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "x".to_owned(),
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
                    },
                    IRUpdate {
                        field: "y".to_owned(),
                        value: IRExpr::BinOp {
                            op: "OpAdd".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "y".to_owned(),
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
                    },
                ],
                postcondition: None,
            }],
        };

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["Counter".to_owned()],
            events: vec![IREvent {
                name: "tick".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                postcondition: None,
                body: vec![IRAction::Choose {
                    var: "c".to_owned(),
                    entity: "Counter".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    }),
                    ops: vec![IRAction::Apply {
                        target: "c".to_owned(),
                        transition: "step".to_owned(),
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

        // Property: always all c: Counter | c.y <= 10
        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "c".to_owned(),
                domain: IRType::Entity {
                    name: "Counter".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpLe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "c".to_owned(),
                            ty: IRType::Entity {
                                name: "Counter".to_owned(),
                            },

                            span: None,
                        }),
                        field: "y".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 10 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
        };

        // Verify block with this property
        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![IRVerify {
                name: "counter_bounded".to_owned(),
                systems: vec![IRVerifySystem {
                    name: "S".to_owned(),
                    lo: 0,
                    hi: 20,
                }],
                asserts: vec![property.clone()],
                span: None,
                file: None,
            }],
            theorems: vec![IRTheorem {
                name: "counter_bounded_thm".to_owned(),
                systems: vec!["S".to_owned()],
                invariants: vec![],
                shows: vec![property],
                span: None,
                file: None,
            }],
            axioms: vec![],
            scenes: vec![],
        };

        let config = VerifyConfig::default();
        let results = verify_all(&ir, &config);

        // We expect:
        // - verify block: induction fails, IC3 proves → PROVED (method: IC3/PDR)
        //   OR: induction fails, IC3 fails, BMC checks → CHECKED
        // - theorem: IC3 proves → PROVED (method: IC3/PDR)
        //   OR: induction fails, IC3 fails → UNPROVABLE

        // At minimum, the verify block should succeed (BMC fallback if IC3 can't)
        assert!(results.len() >= 1, "expected at least 1 result");

        // Verify block: induction fails → IC3 proves
        let verify_result = &results[0];
        assert!(
            matches!(
                verify_result,
                VerificationResult::Proved { method, .. } if method == "IC3/PDR"
            ),
            "expected PROVED (method: IC3/PDR) for verify block, got: {verify_result}"
        );

        // Theorem: IC3 proves (tried before 4-phase induction)
        assert_eq!(results.len(), 2, "expected 2 results (verify + theorem)");
        let thm_result = &results[1];
        assert!(
            matches!(
                thm_result,
                VerificationResult::Proved { method, .. } if method == "IC3/PDR"
            ),
            "expected PROVED (method: IC3/PDR) for theorem, got: {thm_result}"
        );
    }

    #[test]
    fn no_ic3_flag_skips_ic3_verify_falls_to_bmc() {
        // Same IR as ic3_proves_property_induction_cannot, but with --no-ic3.
        // Verify block: induction fails, IC3 skipped, falls to BMC → CHECKED.
        let ir = make_two_counter_ir();
        let config = VerifyConfig {
            no_ic3: true,
            ..VerifyConfig::default()
        };
        let results = verify_all(&ir, &config);
        assert_eq!(results.len(), 2);

        // Verify block: BMC fallback (CHECKED)
        assert!(
            matches!(&results[0], VerificationResult::Checked { .. }),
            "expected CHECKED with --no-ic3, got: {}",
            results[0]
        );

        // Theorem: IC3 skipped, induction fails → UNPROVABLE
        assert!(
            matches!(&results[1], VerificationResult::Unprovable { .. }),
            "expected UNPROVABLE with --no-ic3, got: {}",
            results[1]
        );
    }

    #[test]
    fn bounded_only_skips_theorem_proving() {
        // With --bounded-only, theorems can't be proved (no BMC for theorems).
        let ir = make_two_counter_ir();
        let config = VerifyConfig {
            bounded_only: true,
            ..VerifyConfig::default()
        };
        let results = verify_all(&ir, &config);
        assert_eq!(results.len(), 2);

        // Verify block: BMC only → CHECKED
        assert!(
            matches!(&results[0], VerificationResult::Checked { .. }),
            "expected CHECKED with --bounded-only, got: {}",
            results[0]
        );

        // Theorem: --bounded-only → UNPROVABLE
        let thm = &results[1];
        assert!(
            matches!(thm, VerificationResult::Unprovable { hint, .. }
                if hint.contains("--bounded-only")),
            "expected UNPROVABLE with --bounded-only hint, got: {thm}"
        );
    }

    #[test]
    fn unbounded_only_no_ic3_gives_accurate_hint() {
        // --unbounded-only + --no-ic3: hint should say IC3 was skipped.
        let ir = make_two_counter_ir();
        let config = VerifyConfig {
            unbounded_only: true,
            no_ic3: true,
            ..VerifyConfig::default()
        };
        let results = verify_all(&ir, &config);

        // Verify block: induction fails, IC3 skipped, BMC skipped → UNPROVABLE
        let verify_result = &results[0];
        assert!(
            matches!(verify_result, VerificationResult::Unprovable { hint, .. }
                if hint.contains("--no-ic3")),
            "expected UNPROVABLE mentioning --no-ic3, got: {verify_result}"
        );
    }

    /// Helper: build the two-counter IR used by multiple IC3 flag tests.
    fn make_two_counter_ir() -> IRProgram {
        let entity = IREntity {
            name: "Counter".to_owned(),
            fields: vec![
                IRField {
                    name: "x".to_owned(),
                    ty: IRType::Int,
                    default: Some(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },

                        span: None,
                    }),
                },
                IRField {
                    name: "y".to_owned(),
                    ty: IRType::Int,
                    default: Some(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },

                        span: None,
                    }),
                },
            ],
            transitions: vec![IRTransition {
                name: "step".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::BinOp {
                    op: "OpLt".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 10 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                },
                updates: vec![
                    IRUpdate {
                        field: "x".to_owned(),
                        value: IRExpr::BinOp {
                            op: "OpAdd".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "x".to_owned(),
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
                    },
                    IRUpdate {
                        field: "y".to_owned(),
                        value: IRExpr::BinOp {
                            op: "OpAdd".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "y".to_owned(),
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
                    },
                ],
                postcondition: None,
            }],
        };

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["Counter".to_owned()],
            events: vec![IREvent {
                name: "tick".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                postcondition: None,
                body: vec![IRAction::Choose {
                    var: "c".to_owned(),
                    entity: "Counter".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    }),
                    ops: vec![IRAction::Apply {
                        target: "c".to_owned(),
                        transition: "step".to_owned(),
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

        // Property: always all c: Counter | c.y <= 10
        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "c".to_owned(),
                domain: IRType::Entity {
                    name: "Counter".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpLe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "c".to_owned(),
                            ty: IRType::Entity {
                                name: "Counter".to_owned(),
                            },

                            span: None,
                        }),
                        field: "y".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 10 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
        };

        IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![IRVerify {
                name: "counter_bounded".to_owned(),
                systems: vec![IRVerifySystem {
                    name: "S".to_owned(),
                    lo: 0,
                    hi: 20,
                }],
                asserts: vec![property.clone()],
                span: None,
                file: None,
            }],
            theorems: vec![IRTheorem {
                name: "counter_bounded_thm".to_owned(),
                systems: vec!["S".to_owned()],
                invariants: vec![],
                shows: vec![property],
                span: None,
                file: None,
            }],
            axioms: vec![],
            scenes: vec![],
        }
    }

    // ── Map encoding tests ──────────────────────────────────────────

    #[test]
    fn map_field_verify_index_after_update() {
        // Entity with a Map<Int, Int> field. Action does m[k := v].
        // Property: after update, m[k] == v. Tests MapUpdate + Index Z3 encoding.
        let entity = IREntity {
            name: "Store".to_owned(),
            fields: vec![IRField {
                name: "data".to_owned(),
                ty: IRType::Map {
                    key: Box::new(IRType::Int),
                    value: Box::new(IRType::Int),
                },
                default: None,
            }],
            transitions: vec![IRTransition {
                name: "put".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                updates: vec![IRUpdate {
                    field: "data".to_owned(),
                    value: IRExpr::MapUpdate {
                        map: Box::new(IRExpr::Var {
                            name: "data".to_owned(),
                            ty: IRType::Map {
                                key: Box::new(IRType::Int),
                                value: Box::new(IRType::Int),
                            },

                            span: None,
                        }),
                        key: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 42 },

                            span: None,
                        }),
                        value: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 100 },

                            span: None,
                        }),
                        ty: IRType::Map {
                            key: Box::new(IRType::Int),
                            value: Box::new(IRType::Int),
                        },

                        span: None,
                    },
                }],
                postcondition: None,
            }],
        };

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["Store".to_owned()],
            events: vec![
                IREvent {
                    name: "create_store".to_owned(),
                    params: vec![],
                    guard: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    },
                    postcondition: None,
                    body: vec![IRAction::Create {
                        entity: "Store".to_owned(),
                        fields: vec![], // data field unconstrained at creation
                    }],
                },
                IREvent {
                    name: "do_put".to_owned(),
                    params: vec![],
                    guard: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    },
                    postcondition: None,
                    body: vec![IRAction::Choose {
                        var: "s".to_owned(),
                        entity: "Store".to_owned(),
                        filter: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },

                            span: None,
                        }),
                        ops: vec![IRAction::Apply {
                            target: "s".to_owned(),
                            transition: "put".to_owned(),
                            refs: vec![],
                            args: vec![],
                        }],
                    }],
                },
            ],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
        };

        // Helper: build s.data[42] expression
        let data_at_42 = |var: &str| -> IRExpr {
            IRExpr::Index {
                map: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: var.to_owned(),
                        ty: IRType::Entity {
                            name: "Store".to_owned(),
                        },

                        span: None,
                    }),
                    field: "data".to_owned(),
                    ty: IRType::Map {
                        key: Box::new(IRType::Int),
                        value: Box::new(IRType::Int),
                    },

                    span: None,
                }),
                key: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 42 },

                    span: None,
                }),
                ty: IRType::Int,

                span: None,
            }
        };

        // Property: always all s: Store | s.data[42] == s.data[42]
        // Tautological — tests that Index encodes correctly in properties
        // without depending on initial/transition values. Z3 should prove
        // this by reflexivity of array select.
        let reflex_property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "s".to_owned(),
                domain: IRType::Entity {
                    name: "Store".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(data_at_42("s")),
                    right: Box::new(data_at_42("s")),
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
        };

        // Property: data[42] == 100 — false for newly created entities,
        // but CHECKED at depth 0 shows no violation with no active entities.
        // After create + put it holds. BMC validates the full encoding
        // path (MapUpdate in action → Index in property → comparison).
        let post_put_property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "s".to_owned(),
                domain: IRType::Entity {
                    name: "Store".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(data_at_42("s")),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 100 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
        };

        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![
                IRVerify {
                    name: "map_reflex".to_owned(),
                    systems: vec![IRVerifySystem {
                        name: "S".to_owned(),
                        lo: 0,
                        hi: 3,
                    }],
                    asserts: vec![reflex_property],
                    span: None,
                    file: None,
                },
                IRVerify {
                    name: "map_post_put".to_owned(),
                    systems: vec![IRVerifySystem {
                        name: "S".to_owned(),
                        lo: 0,
                        hi: 5,
                    }],
                    asserts: vec![post_put_property],
                    span: None,
                    file: None,
                },
            ],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        };

        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 2, "expected 2 verify results");

        // Reflexivity: data[42] == data[42] — PROVED by induction (trivially true)
        assert!(
            matches!(&results[0], VerificationResult::Proved { .. }),
            "reflexive map property should be PROVED: got {}",
            results[0]
        );

        // Post-put: data[42] == 100 — COUNTEREXAMPLE expected (create_store
        // event creates entities with unconstrained data, so data[42] != 100
        // before first put). Validates full MapUpdate→Index→comparison path.
        assert!(
            matches!(&results[1], VerificationResult::Counterexample { .. }),
            "post-put map property should find COUNTEREXAMPLE: got {}",
            results[1]
        );
    }

    #[test]
    fn map_literal_in_property_encoding() {
        // Tests MapLit encoding in the property encoder.
        // Entity with Map<Int, Int> field. Property compares field to a
        // MapLit constant: data == Map((42, 100)). BMC checks this.
        let entity = IREntity {
            name: "M".to_owned(),
            fields: vec![IRField {
                name: "data".to_owned(),
                ty: IRType::Map {
                    key: Box::new(IRType::Int),
                    value: Box::new(IRType::Int),
                },
                default: None,
            }],
            transitions: vec![],
        };

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["M".to_owned()],
            events: vec![IREvent {
                name: "create_m".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                postcondition: None,
                body: vec![IRAction::Create {
                    entity: "M".to_owned(),
                    fields: vec![],
                }],
            }],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
        };

        // Property: all m: M | m.data != Map((42, 100))
        // MapLit in the assertion — validates MapLit property encoding.
        // True: data is unconstrained at creation, extremely unlikely to
        // equal the specific map literal. BMC should PROVE or CHECK this.
        let map_ty = IRType::Map {
            key: Box::new(IRType::Int),
            value: Box::new(IRType::Int),
        };
        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "m".to_owned(),
                domain: IRType::Entity {
                    name: "M".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpNEq".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "m".to_owned(),
                            ty: IRType::Entity {
                                name: "M".to_owned(),
                            },

                            span: None,
                        }),
                        field: "data".to_owned(),
                        ty: map_ty.clone(),

                        span: None,
                    }),
                    right: Box::new(IRExpr::MapLit {
                        entries: vec![(
                            IRExpr::Lit {
                                ty: IRType::Int,
                                value: LitVal::Int { value: 42 },

                                span: None,
                            },
                            IRExpr::Lit {
                                ty: IRType::Int,
                                value: LitVal::Int { value: 100 },

                                span: None,
                            },
                        )],
                        ty: map_ty,

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
        };

        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![IRVerify {
                name: "map_lit_test".to_owned(),
                systems: vec![IRVerifySystem {
                    name: "S".to_owned(),
                    lo: 0,
                    hi: 3,
                }],
                asserts: vec![property],
                span: None,
                file: None,
            }],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        };

        // Should not panic — validates MapLit in property encoder path
        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 1);
        assert!(
            !matches!(&results[0], VerificationResult::Unprovable { .. }),
            "MapLit in property should encode without error: got {}",
            results[0]
        );
    }

    #[test]
    fn primed_map_update_sugar_encoding() {
        // Tests the primed-index sugar path: data' = data[key := value]
        // where the action body uses MapUpdate on the current field value.
        // This is the pattern used in workflow_engine: variables'[k] = v
        // which desugars to variables' = variables[k := v].
        //
        // Verifies that Prime(MapUpdate(Var, key, val)) encodes correctly
        // through the action → frame → property encoding chain.
        let entity = IREntity {
            name: "KV".to_owned(),
            fields: vec![
                IRField {
                    name: "store".to_owned(),
                    ty: IRType::Map {
                        key: Box::new(IRType::Int),
                        value: Box::new(IRType::Int),
                    },
                    default: None,
                },
                IRField {
                    name: "count".to_owned(),
                    ty: IRType::Int,
                    default: Some(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },

                        span: None,
                    }),
                },
            ],
            transitions: vec![IRTransition {
                name: "set_key".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                updates: vec![
                    // store' = store[1 := 42]
                    IRUpdate {
                        field: "store".to_owned(),
                        value: IRExpr::MapUpdate {
                            map: Box::new(IRExpr::Var {
                                name: "store".to_owned(),
                                ty: IRType::Map {
                                    key: Box::new(IRType::Int),
                                    value: Box::new(IRType::Int),
                                },

                                span: None,
                            }),
                            key: Box::new(IRExpr::Lit {
                                ty: IRType::Int,
                                value: LitVal::Int { value: 1 },

                                span: None,
                            }),
                            value: Box::new(IRExpr::Lit {
                                ty: IRType::Int,
                                value: LitVal::Int { value: 42 },

                                span: None,
                            }),
                            ty: IRType::Map {
                                key: Box::new(IRType::Int),
                                value: Box::new(IRType::Int),
                            },

                            span: None,
                        },
                    },
                    // count' = count + 1 (scalar frame test alongside map)
                    IRUpdate {
                        field: "count".to_owned(),
                        value: IRExpr::BinOp {
                            op: "OpAdd".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "count".to_owned(),
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
                    },
                ],
                postcondition: None,
            }],
        };

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["KV".to_owned()],
            events: vec![
                IREvent {
                    name: "create_kv".to_owned(),
                    params: vec![],
                    guard: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    },
                    postcondition: None,
                    body: vec![IRAction::Create {
                        entity: "KV".to_owned(),
                        fields: vec![],
                    }],
                },
                IREvent {
                    name: "do_set".to_owned(),
                    params: vec![],
                    guard: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    },
                    postcondition: None,
                    body: vec![IRAction::Choose {
                        var: "k".to_owned(),
                        entity: "KV".to_owned(),
                        filter: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },

                            span: None,
                        }),
                        ops: vec![IRAction::Apply {
                            target: "k".to_owned(),
                            transition: "set_key".to_owned(),
                            refs: vec![],
                            args: vec![],
                        }],
                    }],
                },
            ],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
        };

        // Property: count >= 0 (monotonically increasing from 0).
        // Tests that scalar fields are correctly framed alongside map updates.
        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "k".to_owned(),
                domain: IRType::Entity {
                    name: "KV".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "k".to_owned(),
                            ty: IRType::Entity {
                                name: "KV".to_owned(),
                            },

                            span: None,
                        }),
                        field: "count".to_owned(),
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

        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![IRVerify {
                name: "primed_map_update".to_owned(),
                systems: vec![IRVerifySystem {
                    name: "S".to_owned(),
                    lo: 0,
                    hi: 5,
                }],
                asserts: vec![property],
                span: None,
                file: None,
            }],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        };

        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 1);
        // count starts at 0, incremented by 1 each set_key → always >= 0.
        // Map update (store) encodes alongside scalar update without conflict.
        assert!(
            matches!(
                &results[0],
                VerificationResult::Proved { .. } | VerificationResult::Checked { .. }
            ),
            "primed map update with scalar should succeed: got {}",
            results[0]
        );
    }

    // ── Set encoding tests ──────────────────────────────────────────

    #[test]
    fn set_membership_via_index() {
        // Tests that `e in S` (lowered to Index(S, e)) works in properties.
        // Entity with Set<Int> field `tags`. Action `add_tag` does tags' = tags[5 := true]
        // (store 5 as member). Property: after add_tag, 5 is in tags.
        //
        // Since Set<T> = Array<T, Bool>, Index(tags, 5) returns Bool = true after store.
        let set_ty = IRType::Set {
            element: Box::new(IRType::Int),
        };

        let entity = IREntity {
            name: "Item".to_owned(),
            fields: vec![IRField {
                name: "tags".to_owned(),
                ty: set_ty.clone(),
                default: None,
            }],
            transitions: vec![IRTransition {
                name: "add_tag".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                // tags' = tags[5 := true] (add 5 to set)
                updates: vec![IRUpdate {
                    field: "tags".to_owned(),
                    value: IRExpr::MapUpdate {
                        map: Box::new(IRExpr::Var {
                            name: "tags".to_owned(),
                            ty: set_ty.clone(),

                            span: None,
                        }),
                        key: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 5 },

                            span: None,
                        }),
                        value: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },

                            span: None,
                        }),
                        ty: set_ty.clone(),

                        span: None,
                    },
                }],
                postcondition: None,
            }],
        };

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["Item".to_owned()],
            events: vec![
                IREvent {
                    name: "create_item".to_owned(),
                    params: vec![],
                    guard: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    },
                    postcondition: None,
                    body: vec![IRAction::Create {
                        entity: "Item".to_owned(),
                        fields: vec![],
                    }],
                },
                IREvent {
                    name: "do_add".to_owned(),
                    params: vec![],
                    guard: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    },
                    postcondition: None,
                    body: vec![IRAction::Choose {
                        var: "i".to_owned(),
                        entity: "Item".to_owned(),
                        filter: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },

                            span: None,
                        }),
                        ops: vec![IRAction::Apply {
                            target: "i".to_owned(),
                            transition: "add_tag".to_owned(),
                            refs: vec![],
                            args: vec![],
                        }],
                    }],
                },
            ],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
        };

        // Property: always (all i: Item | i.tags[5] == true)
        // i.e., "5 is always a member of tags"
        // This is NOT always true: newly created items have unconstrained tags,
        // so tags[5] can be false before add_tag fires.
        // BMC should find a COUNTEREXAMPLE — validates the full store→select
        // semantic chain for set membership.
        let tags_at_5 = IRExpr::Index {
            map: Box::new(IRExpr::Field {
                expr: Box::new(IRExpr::Var {
                    name: "i".to_owned(),
                    ty: IRType::Entity {
                        name: "Item".to_owned(),
                    },

                    span: None,
                }),
                field: "tags".to_owned(),
                ty: set_ty,

                span: None,
            }),
            key: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 5 },

                span: None,
            }),
            ty: IRType::Bool,

            span: None,
        };

        let membership_property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "i".to_owned(),
                domain: IRType::Entity {
                    name: "Item".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(tags_at_5),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
        };

        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![IRVerify {
                name: "set_membership".to_owned(),
                systems: vec![IRVerifySystem {
                    name: "S".to_owned(),
                    lo: 0,
                    hi: 3,
                }],
                asserts: vec![membership_property],
                span: None,
                file: None,
            }],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        };

        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 1);
        // Created items have unconstrained tags → tags[5] can be false → COUNTEREXAMPLE.
        // This validates: Set field as Array<Int,Bool>, store(5,true) in add_tag action,
        // select(5) in property assertion, Bool comparison — full semantic chain.
        assert!(
            matches!(&results[0], VerificationResult::Counterexample { .. }),
            "set membership should produce COUNTEREXAMPLE (unconstrained before add_tag): got {}",
            results[0]
        );
    }

    #[test]
    fn set_literal_in_property() {
        // Tests SetLit in property encoding.
        // Property: Set(1,2,3)[2] == true (2 is a member of {1,2,3}).
        // Uses SetLit directly in the assertion, validates property-side encoding.
        let set_ty = IRType::Set {
            element: Box::new(IRType::Int),
        };

        let entity = IREntity {
            name: "X".to_owned(),
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

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["X".to_owned()],
            events: vec![IREvent {
                name: "create_x".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                postcondition: None,
                body: vec![IRAction::Create {
                    entity: "X".to_owned(),
                    fields: vec![],
                }],
            }],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
        };

        // Property: Set(1,2,3)[2] == true — 2 is in {1,2,3}
        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "x".to_owned(),
                domain: IRType::Entity {
                    name: "X".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Index {
                        map: Box::new(IRExpr::SetLit {
                            elements: vec![
                                IRExpr::Lit {
                                    ty: IRType::Int,
                                    value: LitVal::Int { value: 1 },

                                    span: None,
                                },
                                IRExpr::Lit {
                                    ty: IRType::Int,
                                    value: LitVal::Int { value: 2 },

                                    span: None,
                                },
                                IRExpr::Lit {
                                    ty: IRType::Int,
                                    value: LitVal::Int { value: 3 },

                                    span: None,
                                },
                            ],
                            ty: set_ty,

                            span: None,
                        }),
                        key: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 2 },

                            span: None,
                        }),
                        ty: IRType::Bool,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
        };

        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![IRVerify {
                name: "set_lit_membership".to_owned(),
                systems: vec![IRVerifySystem {
                    name: "S".to_owned(),
                    lo: 0,
                    hi: 3,
                }],
                asserts: vec![property],
                span: None,
                file: None,
            }],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        };

        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 1);
        // Set(1,2,3)[2] is always true — should be PROVED
        assert!(
            matches!(&results[0], VerificationResult::Proved { .. }),
            "set literal membership should be PROVED: got {}",
            results[0]
        );
    }

    #[test]
    fn set_literal_cardinality() {
        // Tests #Set(1,2,3) == 3 in a property — cardinality of a set literal.
        let set_ty = IRType::Set {
            element: Box::new(IRType::Int),
        };

        let entity = IREntity {
            name: "X".to_owned(),
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

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["X".to_owned()],
            events: vec![IREvent {
                name: "create_x".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                postcondition: None,
                body: vec![IRAction::Create {
                    entity: "X".to_owned(),
                    fields: vec![],
                }],
            }],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
        };

        // Property: #Set(1,2,3) == 3
        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "x".to_owned(),
                domain: IRType::Entity {
                    name: "X".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Card {
                        expr: Box::new(IRExpr::SetLit {
                            elements: vec![
                                IRExpr::Lit {
                                    ty: IRType::Int,
                                    value: LitVal::Int { value: 1 },

                                    span: None,
                                },
                                IRExpr::Lit {
                                    ty: IRType::Int,
                                    value: LitVal::Int { value: 2 },

                                    span: None,
                                },
                                IRExpr::Lit {
                                    ty: IRType::Int,
                                    value: LitVal::Int { value: 3 },

                                    span: None,
                                },
                            ],
                            ty: set_ty,

                            span: None,
                        }),

                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 3 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
        };

        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![IRVerify {
                name: "card_set_lit".to_owned(),
                systems: vec![IRVerifySystem {
                    name: "S".to_owned(),
                    lo: 0,
                    hi: 3,
                }],
                asserts: vec![property],
                span: None,
                file: None,
            }],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        };

        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 1);
        // #Set(1,2,3) = 3 — compile-time constant, trivially PROVED
        assert!(
            matches!(&results[0], VerificationResult::Proved { .. }),
            "#Set(1,2,3) == 3 should be PROVED: got {}",
            results[0]
        );
    }

    #[test]
    fn set_literal_cardinality_deduplicates() {
        // #Set(1,1,2) should be 2 (not 3) — duplicates are collapsed.
        let set_ty = IRType::Set {
            element: Box::new(IRType::Int),
        };
        let entity = IREntity {
            name: "X".to_owned(),
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
        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["X".to_owned()],
            events: vec![IREvent {
                name: "create_x".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                postcondition: None,
                body: vec![IRAction::Create {
                    entity: "X".to_owned(),
                    fields: vec![],
                }],
            }],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
        };

        // #Set(1,1,2) == 2
        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "x".to_owned(),
                domain: IRType::Entity {
                    name: "X".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Card {
                        expr: Box::new(IRExpr::SetLit {
                            elements: vec![
                                IRExpr::Lit {
                                    ty: IRType::Int,
                                    value: LitVal::Int { value: 1 },

                                    span: None,
                                },
                                IRExpr::Lit {
                                    ty: IRType::Int,
                                    value: LitVal::Int { value: 1 }, // duplicate,
                                    span: None,
                                },
                                IRExpr::Lit {
                                    ty: IRType::Int,
                                    value: LitVal::Int { value: 2 },

                                    span: None,
                                },
                            ],
                            ty: set_ty,

                            span: None,
                        }),

                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 2 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
        };

        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![IRVerify {
                name: "card_dedup".to_owned(),
                systems: vec![IRVerifySystem {
                    name: "S".to_owned(),
                    lo: 0,
                    hi: 3,
                }],
                asserts: vec![property],
                span: None,
                file: None,
            }],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        };

        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 1);
        assert!(
            matches!(&results[0], VerificationResult::Proved { .. }),
            "#Set(1,1,2) == 2 should be PROVED (deduplicated): got {}",
            results[0]
        );
    }

    // ── Set comprehension tests ─────────────────────────────────────

    #[test]
    fn set_comprehension_simple_form() {
        // { o: Order where o.status == @Active } — simple set comprehension.
        // Entity with status enum, one transition that sets Active.
        // Property: #{ o: Order where true } >= 0 — always true (count is non-negative).
        // Tests that SetComp encodes without panic and produces a valid Array.
        let status_type = IRTypeEntry {
            name: "Status".to_owned(),
            ty: IRType::Enum {
                name: "Status".to_owned(),
                constructors: vec!["Idle".to_owned(), "Active".to_owned()],
            },
        };

        let entity = IREntity {
            name: "Obj".to_owned(),
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
                        constructors: vec!["Idle".to_owned(), "Active".to_owned()],
                    },
                    default: Some(IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Idle".to_owned(),

                        span: None,
                    }),
                },
            ],
            transitions: vec![IRTransition {
                name: "activate".to_owned(),
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
                        ctor: "Idle".to_owned(),

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                },
                updates: vec![IRUpdate {
                    field: "status".to_owned(),
                    value: IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Active".to_owned(),

                        span: None,
                    },
                }],
                postcondition: None,
            }],
        };

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["Obj".to_owned()],
            events: vec![
                IREvent {
                    name: "create_obj".to_owned(),
                    params: vec![],
                    guard: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    },
                    postcondition: None,
                    body: vec![IRAction::Create {
                        entity: "Obj".to_owned(),
                        fields: vec![],
                    }],
                },
                IREvent {
                    name: "do_activate".to_owned(),
                    params: vec![],
                    guard: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    },
                    postcondition: None,
                    body: vec![IRAction::Choose {
                        var: "o".to_owned(),
                        entity: "Obj".to_owned(),
                        filter: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },

                            span: None,
                        }),
                        ops: vec![IRAction::Apply {
                            target: "o".to_owned(),
                            transition: "activate".to_owned(),
                            refs: vec![],
                            args: vec![],
                        }],
                    }],
                },
            ],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
        };

        // Simple comprehension: { o: Obj where o.status == @Active }
        let active_set = IRExpr::SetComp {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Obj".to_owned(),
            },
            filter: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "o".to_owned(),
                        ty: IRType::Entity {
                            name: "Obj".to_owned(),
                        },

                        span: None,
                    }),
                    field: "status".to_owned(),
                    ty: IRType::Int,

                    span: None,
                }),
                right: Box::new(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Active".to_owned(),

                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            }),
            projection: None,
            ty: IRType::Set {
                element: Box::new(IRType::Int),
            },

            span: None,
        };

        // Property: { o: Obj where o.status == @Active } == { o: Obj where o.status == @Active }
        // Reflexive — validates SetComp encodes to Array without panic.
        // Wrapped in a Forall to get the right encoding context.
        let property = IRExpr::Always {
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(active_set.clone()),
                right: Box::new(active_set),
                ty: IRType::Bool,

                span: None,
            }),

            span: None,
        };

        let ir = IRProgram {
            types: vec![status_type],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![IRVerify {
                name: "set_comp_simple".to_owned(),
                systems: vec![IRVerifySystem {
                    name: "S".to_owned(),
                    lo: 0,
                    hi: 3,
                }],
                asserts: vec![property],
                span: None,
                file: None,
            }],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        };

        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 1);
        assert!(
            matches!(
                &results[0],
                VerificationResult::Proved { .. } | VerificationResult::Checked { .. }
            ),
            "set comprehension should encode without error: got {}",
            results[0]
        );
    }

    #[test]
    fn set_comprehension_membership_check() {
        // After activate: slot 0 should be in { o: Obj where o.status == @Active }.
        // Uses Index on the comprehension result to check membership.
        // This won't be provable (needs invariant linking slot index to active set),
        // but it validates the full SetComp→Index→Bool encoding chain.
        let status_type = IRTypeEntry {
            name: "Status".to_owned(),
            ty: IRType::Enum {
                name: "Status".to_owned(),
                constructors: vec!["Idle".to_owned(), "Active".to_owned()],
            },
        };

        let entity = IREntity {
            name: "Obj".to_owned(),
            fields: vec![IRField {
                name: "status".to_owned(),
                ty: IRType::Enum {
                    name: "Status".to_owned(),
                    constructors: vec!["Idle".to_owned(), "Active".to_owned()],
                },
                default: Some(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Idle".to_owned(),

                    span: None,
                }),
            }],
            transitions: vec![],
        };

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["Obj".to_owned()],
            events: vec![IREvent {
                name: "create_obj".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                postcondition: None,
                body: vec![IRAction::Create {
                    entity: "Obj".to_owned(),
                    fields: vec![],
                }],
            }],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
        };

        // { o: Obj where true }[0] — slot 0 membership in "all objects" set
        // This is true iff slot 0 is active. Since we can create objects, and
        // the set includes all active objects, Index(comprehension, 0) == active[0].
        // We check: Index(comprehension, 0) == Index(comprehension, 0) — reflexive,
        // but validates the SetComp→Index chain doesn't panic.
        let comp = IRExpr::SetComp {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Obj".to_owned(),
            },
            filter: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            }),
            projection: None,
            ty: IRType::Set {
                element: Box::new(IRType::Int),
            },

            span: None,
        };

        let comp_at_0 = IRExpr::Index {
            map: Box::new(comp),
            key: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },

                span: None,
            }),
            ty: IRType::Bool,

            span: None,
        };

        let property = IRExpr::Always {
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(comp_at_0.clone()),
                right: Box::new(comp_at_0),
                ty: IRType::Bool,

                span: None,
            }),

            span: None,
        };

        let ir = IRProgram {
            types: vec![status_type],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![IRVerify {
                name: "set_comp_index".to_owned(),
                systems: vec![IRVerifySystem {
                    name: "S".to_owned(),
                    lo: 0,
                    hi: 3,
                }],
                asserts: vec![property],
                span: None,
                file: None,
            }],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        };

        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 1);
        assert!(
            matches!(
                &results[0],
                VerificationResult::Proved { .. } | VerificationResult::Checked { .. }
            ),
            "SetComp→Index chain should encode without error: got {}",
            results[0]
        );
    }

    #[test]
    fn set_comprehension_projection_form() {
        // Projection comprehension: { o.status | o: Obj where true }
        // Collects status values of all active objects into a set.
        // Property: Set(1,2,3)[0] == true is independent of comprehension —
        // just validates projection encoding doesn't panic.
        let status_type = IRTypeEntry {
            name: "Status".to_owned(),
            ty: IRType::Enum {
                name: "Status".to_owned(),
                constructors: vec!["Idle".to_owned(), "Active".to_owned()],
            },
        };

        let entity = IREntity {
            name: "Obj".to_owned(),
            fields: vec![IRField {
                name: "status".to_owned(),
                ty: IRType::Enum {
                    name: "Status".to_owned(),
                    constructors: vec!["Idle".to_owned(), "Active".to_owned()],
                },
                default: Some(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Idle".to_owned(),

                    span: None,
                }),
            }],
            transitions: vec![],
        };

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["Obj".to_owned()],
            events: vec![IREvent {
                name: "create_obj".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                postcondition: None,
                body: vec![IRAction::Create {
                    entity: "Obj".to_owned(),
                    fields: vec![],
                }],
            }],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
        };

        // Projection: { o.status | o: Obj where true }
        let status_set = IRExpr::SetComp {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Obj".to_owned(),
            },
            filter: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            }),
            projection: Some(Box::new(IRExpr::Field {
                expr: Box::new(IRExpr::Var {
                    name: "o".to_owned(),
                    ty: IRType::Entity {
                        name: "Obj".to_owned(),
                    },

                    span: None,
                }),
                field: "status".to_owned(),
                ty: IRType::Int,

                span: None,
            })),
            ty: IRType::Set {
                element: Box::new(IRType::Int),
            },

            span: None,
        };

        // Property: Index(status_set, Idle_id) == Index(status_set, Idle_id)
        // Reflexive on the projection result — validates projection encoding chain.
        // Idle is constructor 0 in VerifyContext.
        let idle_id = IRExpr::Ctor {
            enum_name: "Status".to_owned(),
            ctor: "Idle".to_owned(),

            span: None,
        };
        let proj_at_idle = IRExpr::Index {
            map: Box::new(status_set),
            key: Box::new(idle_id),
            ty: IRType::Bool,

            span: None,
        };

        let property = IRExpr::Always {
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(proj_at_idle.clone()),
                right: Box::new(proj_at_idle),
                ty: IRType::Bool,

                span: None,
            }),

            span: None,
        };

        let ir = IRProgram {
            types: vec![status_type],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![IRVerify {
                name: "set_comp_proj".to_owned(),
                systems: vec![IRVerifySystem {
                    name: "S".to_owned(),
                    lo: 0,
                    hi: 3,
                }],
                asserts: vec![property],
                span: None,
                file: None,
            }],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        };

        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 1);
        assert!(
            matches!(
                &results[0],
                VerificationResult::Proved { .. } | VerificationResult::Checked { .. }
            ),
            "projection SetComp should encode without error: got {}",
            results[0]
        );
    }

    // ── Sequence encoding tests ─────────────────────────────────────

    #[test]
    fn seq_literal_index_and_cardinality() {
        // Tests SeqLit encoding in properties: Seq(10, 20, 30)[1] == 20 and #Seq(10,20,30) == 3.
        let seq_ty = IRType::Seq {
            element: Box::new(IRType::Int),
        };

        let entity = IREntity {
            name: "X".to_owned(),
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

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["X".to_owned()],
            events: vec![IREvent {
                name: "create_x".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                postcondition: None,
                body: vec![IRAction::Create {
                    entity: "X".to_owned(),
                    fields: vec![],
                }],
            }],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
        };

        let seq_lit = || IRExpr::SeqLit {
            elements: vec![
                IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 10 },

                    span: None,
                },
                IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 20 },

                    span: None,
                },
                IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 30 },

                    span: None,
                },
            ],
            ty: seq_ty.clone(),

            span: None,
        };

        // Property 1: Seq(10,20,30)[1] == 20
        let index_prop = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "x".to_owned(),
                domain: IRType::Entity {
                    name: "X".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Index {
                        map: Box::new(seq_lit()),
                        key: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 1 },

                            span: None,
                        }),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 20 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
        };

        // Property 2: #Seq(10,20,30) == 3
        let card_prop = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "x".to_owned(),
                domain: IRType::Entity {
                    name: "X".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Card {
                        expr: Box::new(seq_lit()),

                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 3 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
        };

        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![
                IRVerify {
                    name: "seq_index".to_owned(),
                    systems: vec![IRVerifySystem {
                        name: "S".to_owned(),
                        lo: 0,
                        hi: 3,
                    }],
                    asserts: vec![index_prop],
                    span: None,
                    file: None,
                },
                IRVerify {
                    name: "seq_card".to_owned(),
                    systems: vec![IRVerifySystem {
                        name: "S".to_owned(),
                        lo: 0,
                        hi: 3,
                    }],
                    asserts: vec![card_prop],
                    span: None,
                    file: None,
                },
            ],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        };

        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 2);

        // Seq(10,20,30)[1] == 20 — PROVED (store/select axiom)
        assert!(
            matches!(&results[0], VerificationResult::Proved { .. }),
            "Seq index should be PROVED: got {}",
            results[0]
        );

        // #Seq(10,20,30) == 3 — compile-time constant, PROVED or CHECKED
        assert!(
            matches!(
                &results[1],
                VerificationResult::Proved { .. } | VerificationResult::Checked { .. }
            ),
            "Seq cardinality should succeed: got {}",
            results[1]
        );
    }

    #[test]
    fn seq_field_frame_across_transition() {
        // Entity with Seq<Int> field + Int field. Transition updates Int only.
        // Seq field should be framed (preserved). Tests Array framing works for Seq.
        let seq_ty = IRType::Seq {
            element: Box::new(IRType::Int),
        };

        let entity = IREntity {
            name: "Q".to_owned(),
            fields: vec![
                IRField {
                    name: "items".to_owned(),
                    ty: seq_ty.clone(),
                    default: None,
                },
                IRField {
                    name: "count".to_owned(),
                    ty: IRType::Int,
                    default: Some(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },

                        span: None,
                    }),
                },
            ],
            transitions: vec![IRTransition {
                name: "inc".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                updates: vec![IRUpdate {
                    field: "count".to_owned(),
                    value: IRExpr::BinOp {
                        op: "OpAdd".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "count".to_owned(),
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
        };

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["Q".to_owned()],
            events: vec![
                IREvent {
                    name: "create_q".to_owned(),
                    params: vec![],
                    guard: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    },
                    postcondition: None,
                    body: vec![IRAction::Create {
                        entity: "Q".to_owned(),
                        fields: vec![],
                    }],
                },
                IREvent {
                    name: "do_inc".to_owned(),
                    params: vec![],
                    guard: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    },
                    postcondition: None,
                    body: vec![IRAction::Choose {
                        var: "q".to_owned(),
                        entity: "Q".to_owned(),
                        filter: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },

                            span: None,
                        }),
                        ops: vec![IRAction::Apply {
                            target: "q".to_owned(),
                            transition: "inc".to_owned(),
                            refs: vec![],
                            args: vec![],
                        }],
                    }],
                },
            ],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
        };

        // Property: items[0] == items[0] — reflexive on the Seq field.
        // This is trivially true but exercises the Array-typed field resolution
        // in the property encoder, proving the Seq field variable is correctly
        // created, accessed, and compared across time steps.
        let items_at_0 = IRExpr::Index {
            map: Box::new(IRExpr::Field {
                expr: Box::new(IRExpr::Var {
                    name: "q".to_owned(),
                    ty: IRType::Entity {
                        name: "Q".to_owned(),
                    },

                    span: None,
                }),
                field: "items".to_owned(),
                ty: seq_ty.clone(),

                span: None,
            }),
            key: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },

                span: None,
            }),
            ty: IRType::Int,

            span: None,
        };

        // Also check count >= 0 to validate scalar framing alongside Seq.
        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "q".to_owned(),
                domain: IRType::Entity {
                    name: "Q".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpAnd".to_owned(),
                    left: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(items_at_0.clone()),
                        right: Box::new(items_at_0),
                        ty: IRType::Bool,

                        span: None,
                    }),
                    right: Box::new(IRExpr::BinOp {
                        op: "OpGe".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "q".to_owned(),
                                ty: IRType::Entity {
                                    name: "Q".to_owned(),
                                },

                                span: None,
                            }),
                            field: "count".to_owned(),
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
        };

        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![IRVerify {
                name: "seq_frame".to_owned(),
                systems: vec![IRVerifySystem {
                    name: "S".to_owned(),
                    lo: 0,
                    hi: 5,
                }],
                asserts: vec![property],
                span: None,
                file: None,
            }],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        };

        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 1);
        assert!(
            matches!(
                &results[0],
                VerificationResult::Proved { .. } | VerificationResult::Checked { .. }
            ),
            "Seq frame alongside scalar should succeed: got {}",
            results[0]
        );
    }

    // ── Cardinality (bounded sum) tests ──────────────────────────────

    #[test]
    fn card_set_comp_bounded_sum() {
        // #{ o: Obj where o.status == @Active } — count of active objects.
        // With 2 slots and no transitions that create or activate, the count
        // is always 0. Property: #{ o | status == Active } == 0 should be PROVED.
        let status_type = IRTypeEntry {
            name: "Status".to_owned(),
            ty: IRType::Enum {
                name: "Status".to_owned(),
                constructors: vec!["Idle".to_owned(), "Active".to_owned()],
            },
        };

        let entity = IREntity {
            name: "Obj".to_owned(),
            fields: vec![IRField {
                name: "status".to_owned(),
                ty: IRType::Enum {
                    name: "Status".to_owned(),
                    constructors: vec!["Idle".to_owned(), "Active".to_owned()],
                },
                default: Some(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Idle".to_owned(),

                    span: None,
                }),
            }],
            transitions: vec![IRTransition {
                name: "activate".to_owned(),
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
                        ctor: "Idle".to_owned(),

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                },
                updates: vec![IRUpdate {
                    field: "status".to_owned(),
                    value: IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Active".to_owned(),

                        span: None,
                    },
                }],
                postcondition: None,
            }],
        };

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["Obj".to_owned()],
            events: vec![
                IREvent {
                    name: "create_obj".to_owned(),
                    params: vec![],
                    guard: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    },
                    postcondition: None,
                    body: vec![IRAction::Create {
                        entity: "Obj".to_owned(),
                        fields: vec![],
                    }],
                },
                IREvent {
                    name: "do_activate".to_owned(),
                    params: vec![],
                    guard: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    },
                    postcondition: None,
                    body: vec![IRAction::Choose {
                        var: "o".to_owned(),
                        entity: "Obj".to_owned(),
                        filter: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },

                            span: None,
                        }),
                        ops: vec![IRAction::Apply {
                            target: "o".to_owned(),
                            transition: "activate".to_owned(),
                            refs: vec![],
                            args: vec![],
                        }],
                    }],
                },
            ],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
        };

        // Comprehension: { o: Obj where o.status == @Active }
        let active_comp = IRExpr::SetComp {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Obj".to_owned(),
            },
            filter: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "o".to_owned(),
                        ty: IRType::Entity {
                            name: "Obj".to_owned(),
                        },

                        span: None,
                    }),
                    field: "status".to_owned(),
                    ty: IRType::Int,

                    span: None,
                }),
                right: Box::new(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Active".to_owned(),

                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            }),
            projection: None,
            ty: IRType::Set {
                element: Box::new(IRType::Int),
            },

            span: None,
        };

        // Property: #{ o | Active } >= 0 — always true (count is non-negative).
        // This is semantically meaningful: the bounded sum produces a real Int,
        // not a fresh unconstrained variable. Z3 can prove sum of ite(cond,1,0) >= 0.
        let non_neg_prop = IRExpr::Always {
            body: Box::new(IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Card {
                    expr: Box::new(active_comp.clone()),

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
        };

        // Property: #{ o | Active } <= 2 — true with scope size 2 (at most 2 slots).
        // The bounded sum can be at most n_slots = 2.
        let bounded_prop = IRExpr::Always {
            body: Box::new(IRExpr::BinOp {
                op: "OpLe".to_owned(),
                left: Box::new(IRExpr::Card {
                    expr: Box::new(active_comp),

                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 2 },

                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            }),

            span: None,
        };

        let ir = IRProgram {
            types: vec![status_type],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![
                IRVerify {
                    name: "card_non_neg".to_owned(),
                    systems: vec![IRVerifySystem {
                        name: "S".to_owned(),
                        lo: 0,
                        hi: 5,
                    }],
                    asserts: vec![non_neg_prop],
                    span: None,
                    file: None,
                },
                IRVerify {
                    name: "card_bounded".to_owned(),
                    systems: vec![IRVerifySystem {
                        name: "S".to_owned(),
                        lo: 0,
                        hi: 5,
                    }],
                    asserts: vec![bounded_prop],
                    span: None,
                    file: None,
                },
            ],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        };

        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 2);

        // #{ Active } >= 0 — PROVED (bounded sum of non-negative terms)
        assert!(
            matches!(
                &results[0],
                VerificationResult::Proved { .. } | VerificationResult::Checked { .. }
            ),
            "#{{ Active }} >= 0 should succeed: got {}",
            results[0]
        );

        // #{ Active } <= 2 — PROVED (at most 2 slots can be active)
        assert!(
            matches!(
                &results[1],
                VerificationResult::Proved { .. } | VerificationResult::Checked { .. }
            ),
            "#{{ Active }} <= 2 should succeed: got {}",
            results[1]
        );
    }

    // ── Prop auto-verification tests ────────────────────────────────

    #[test]
    fn prop_auto_verified_when_true() {
        // A prop targeting a system with a trivially true body should be auto-verified.
        let entity = IREntity {
            name: "X".to_owned(),
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
        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["X".to_owned()],
            events: vec![IREvent {
                name: "create_x".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                postcondition: None,
                body: vec![IRAction::Create {
                    entity: "X".to_owned(),
                    fields: vec![],
                }],
            }],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
        };

        // Prop: always all x: X | x.n >= 0 (true: default is 0, no transitions)
        let prop_body = IRExpr::Forall {
            var: "x".to_owned(),
            domain: IRType::Entity {
                name: "X".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Entity {
                            name: "X".to_owned(),
                        },

                        span: None,
                    }),
                    field: "n".to_owned(),
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
        };

        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![IRFunction {
                name: "n_non_neg".to_owned(),
                ty: IRType::Bool,
                body: prop_body,
                prop_target: Some("S".to_owned()),
                requires: vec![],
                ensures: vec![],
                decreases: None,
                span: None,
                file: None,
            }],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        };

        let results = verify_all(&ir, &VerifyConfig::default());
        // Should produce 1 result: the auto-verified prop
        assert_eq!(results.len(), 1, "expected 1 auto-verified prop result");
        assert!(
            matches!(
                &results[0],
                VerificationResult::Proved { name, .. } if name == "prop_n_non_neg"
            ),
            "prop should be auto-verified as PROVED: got {}",
            results[0]
        );
    }

    #[test]
    fn prop_skipped_when_covered_by_theorem() {
        // A prop already referenced in an explicit theorem should not be double-checked.
        let entity = IREntity {
            name: "X".to_owned(),
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
        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["X".to_owned()],
            events: vec![IREvent {
                name: "create_x".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                postcondition: None,
                body: vec![IRAction::Create {
                    entity: "X".to_owned(),
                    fields: vec![],
                }],
            }],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
        };

        let prop_ref = IRExpr::Var {
            name: "my_prop".to_owned(),
            ty: IRType::Bool,

            span: None,
        };

        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![IRFunction {
                name: "my_prop".to_owned(),
                ty: IRType::Bool,
                body: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                prop_target: Some("S".to_owned()),
                requires: vec![],
                ensures: vec![],
                decreases: None,
                span: None,
                file: None,
            }],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![],
            // Theorem already references my_prop
            theorems: vec![IRTheorem {
                name: "explicit_thm".to_owned(),
                systems: vec!["S".to_owned()],
                invariants: vec![],
                shows: vec![IRExpr::Always {
                    body: Box::new(prop_ref),

                    span: None,
                }],
                span: None,
                file: None,
            }],
            axioms: vec![],
            scenes: vec![],
        };

        let results = verify_all(&ir, &VerifyConfig::default());
        // Should only have 1 result (the explicit theorem), not 2
        assert_eq!(
            results.len(),
            1,
            "prop covered by theorem should not be double-checked: got {} results",
            results.len()
        );
        assert!(
            matches!(
                &results[0],
                VerificationResult::Proved { name, .. } if name == "explicit_thm"
            ),
            "only the explicit theorem should appear: got {}",
            results[0]
        );
    }

    #[test]
    fn no_prop_verify_flag_skips_props() {
        // --no-prop-verify should skip all prop auto-verification.
        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![IRFunction {
                name: "some_prop".to_owned(),
                ty: IRType::Bool,
                body: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                prop_target: Some("S".to_owned()),
                requires: vec![],
                ensures: vec![],
                decreases: None,
                span: None,
                file: None,
            }],
            entities: vec![],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        };

        let config = VerifyConfig {
            no_prop_verify: true,
            ..VerifyConfig::default()
        };
        let results = verify_all(&ir, &config);
        assert!(
            results.is_empty(),
            "--no-prop-verify should produce no results: got {} results",
            results.len()
        );
    }

    #[test]
    fn prop_auto_verified_when_false() {
        // A false prop should produce COUNTEREXAMPLE or UNPROVABLE.
        let status_type = IRTypeEntry {
            name: "Status".to_owned(),
            ty: IRType::Enum {
                name: "Status".to_owned(),
                constructors: vec!["On".to_owned(), "Off".to_owned()],
            },
        };
        let entity = IREntity {
            name: "Switch".to_owned(),
            fields: vec![IRField {
                name: "status".to_owned(),
                ty: IRType::Enum {
                    name: "Status".to_owned(),
                    constructors: vec!["On".to_owned(), "Off".to_owned()],
                },
                default: Some(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Off".to_owned(),

                    span: None,
                }),
            }],
            transitions: vec![IRTransition {
                name: "toggle".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                updates: vec![IRUpdate {
                    field: "status".to_owned(),
                    value: IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "On".to_owned(),

                        span: None,
                    },
                }],
                postcondition: None,
            }],
        };
        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["Switch".to_owned()],
            events: vec![
                IREvent {
                    name: "create_switch".to_owned(),
                    params: vec![],
                    guard: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    },
                    postcondition: None,
                    body: vec![IRAction::Create {
                        entity: "Switch".to_owned(),
                        fields: vec![],
                    }],
                },
                IREvent {
                    name: "do_toggle".to_owned(),
                    params: vec![],
                    guard: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    },
                    postcondition: None,
                    body: vec![IRAction::Choose {
                        var: "s".to_owned(),
                        entity: "Switch".to_owned(),
                        filter: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },

                            span: None,
                        }),
                        ops: vec![IRAction::Apply {
                            target: "s".to_owned(),
                            transition: "toggle".to_owned(),
                            refs: vec![],
                            args: vec![],
                        }],
                    }],
                },
            ],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
        };

        // False prop: "all switches are always Off" — toggle breaks this.
        let false_prop_body = IRExpr::Forall {
            var: "s".to_owned(),
            domain: IRType::Entity {
                name: "Switch".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "s".to_owned(),
                        ty: IRType::Entity {
                            name: "Switch".to_owned(),
                        },

                        span: None,
                    }),
                    field: "status".to_owned(),
                    ty: IRType::Int,

                    span: None,
                }),
                right: Box::new(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Off".to_owned(),

                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            }),

            span: None,
        };

        let ir = IRProgram {
            types: vec![status_type],
            constants: vec![],
            functions: vec![IRFunction {
                name: "always_off".to_owned(),
                ty: IRType::Bool,
                body: false_prop_body,
                prop_target: Some("S".to_owned()),
                requires: vec![],
                ensures: vec![],
                decreases: None,
                span: None,
                file: None,
            }],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        };

        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 1, "expected 1 auto-verified prop result");
        // The prop is false — IC3 should find a counterexample (toggle sets On),
        // or induction returns Unprovable.
        assert!(
            matches!(
                &results[0],
                VerificationResult::Counterexample { name, .. }
                    | VerificationResult::Unprovable { name, .. }
                    if name == "prop_always_off"
            ),
            "false prop should produce Counterexample or Unprovable: got {}",
            results[0]
        );
    }

    // ── Multi-apply sequential composition tests ──────────────────

    #[test]
    fn multi_apply_sequential_chaining() {
        // Two sequential Apply actions: pack (status 0→1) then ship (requires status==1, sets 2).
        // With intermediate variable chaining, ship's guard sees the result of pack.
        // Property: status is always 0 or 2 (never 1) at step boundaries — FALSE because
        // entities start at 0 and pack_and_ship takes them to 2 in one event step,
        // but status could be 0 (before pack_and_ship) or 2 (after). Status 1 only
        // exists in the intermediate state within the event.
        // Simpler property: status >= 0 (always true). Tests encoding doesn't panic.
        let entity = IREntity {
            name: "F".to_owned(),
            fields: vec![IRField {
                name: "status".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },

                    span: None,
                }),
            }],
            transitions: vec![
                IRTransition {
                    name: "pack".to_owned(),
                    refs: vec![],
                    params: vec![],
                    guard: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "status".to_owned(),
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
                    updates: vec![IRUpdate {
                        field: "status".to_owned(),
                        value: IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 1 },

                            span: None,
                        },
                    }],
                    postcondition: None,
                },
                IRTransition {
                    name: "ship".to_owned(),
                    refs: vec![],
                    params: vec![],
                    // Guard: requires status == 1 (result of pack)
                    guard: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "status".to_owned(),
                            ty: IRType::Int,

                            span: None,
                        }),
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 1 },

                            span: None,
                        }),
                        ty: IRType::Bool,

                        span: None,
                    },
                    updates: vec![IRUpdate {
                        field: "status".to_owned(),
                        value: IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 2 },

                            span: None,
                        },
                    }],
                    postcondition: None,
                },
            ],
        };

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["F".to_owned()],
            events: vec![
                IREvent {
                    name: "create_f".to_owned(),
                    params: vec![],
                    guard: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    },
                    postcondition: None,
                    body: vec![IRAction::Create {
                        entity: "F".to_owned(),
                        fields: vec![],
                    }],
                },
                IREvent {
                    name: "pack_and_ship".to_owned(),
                    params: vec![],
                    guard: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    },
                    postcondition: None,
                    body: vec![IRAction::Choose {
                        var: "f".to_owned(),
                        entity: "F".to_owned(),
                        filter: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },

                            span: None,
                        }),
                        ops: vec![
                            IRAction::Apply {
                                target: "f".to_owned(),
                                transition: "pack".to_owned(),
                                refs: vec![],
                                args: vec![],
                            },
                            IRAction::Apply {
                                target: "f".to_owned(),
                                transition: "ship".to_owned(),
                                refs: vec![],
                                args: vec![],
                            },
                        ],
                    }],
                },
            ],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
        };

        // Property: status >= 0 (always true — 0, 1, or 2)
        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "f".to_owned(),
                domain: IRType::Entity {
                    name: "F".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "f".to_owned(),
                            ty: IRType::Entity {
                                name: "F".to_owned(),
                            },

                            span: None,
                        }),
                        field: "status".to_owned(),
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

        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![IRVerify {
                name: "multi_apply_test".to_owned(),
                systems: vec![IRVerifySystem {
                    name: "S".to_owned(),
                    lo: 0,
                    hi: 5,
                }],
                asserts: vec![property],
                span: None,
                file: None,
            }],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        };

        let config = VerifyConfig {
            bounded_only: true, // BMC only — test the chaining encoding
            ..VerifyConfig::default()
        };
        let results = verify_all(&ir, &config);
        assert_eq!(results.len(), 1);
        // Should succeed — status is always 0 or 2 at step boundaries, both >= 0.
        // The key test: this doesn't panic and the guard chain works (ship sees pack's result).
        assert!(
            matches!(
                &results[0],
                VerificationResult::Proved { .. } | VerificationResult::Checked { .. }
            ),
            "multi-apply sequential chaining should succeed: got {}",
            results[0]
        );
    }

    #[test]
    fn multi_apply_scene_checks_final_state() {
        // Scene: given entity with status==0, when pack_and_ship fires,
        // then status == 2 (pack sets 1, ship reads 1 and sets 2).
        // This validates intermediate chaining in the scene encoding path.
        use crate::ir::types::{Cardinality, IRScene, IRSceneEvent, IRSceneGiven};

        let entity = IREntity {
            name: "F".to_owned(),
            fields: vec![IRField {
                name: "status".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },

                    span: None,
                }),
            }],
            transitions: vec![
                IRTransition {
                    name: "pack".to_owned(),
                    refs: vec![],
                    params: vec![],
                    guard: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "status".to_owned(),
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
                    updates: vec![IRUpdate {
                        field: "status".to_owned(),
                        value: IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 1 },

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
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 1 },

                            span: None,
                        }),
                        ty: IRType::Bool,

                        span: None,
                    },
                    updates: vec![IRUpdate {
                        field: "status".to_owned(),
                        value: IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 2 },

                            span: None,
                        },
                    }],
                    postcondition: None,
                },
            ],
        };

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["F".to_owned()],
            events: vec![IREvent {
                name: "pack_and_ship".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                postcondition: None,
                body: vec![IRAction::Choose {
                    var: "f".to_owned(),
                    entity: "F".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    }),
                    ops: vec![
                        IRAction::Apply {
                            target: "f".to_owned(),
                            transition: "pack".to_owned(),
                            refs: vec![],
                            args: vec![],
                        },
                        IRAction::Apply {
                            target: "f".to_owned(),
                            transition: "ship".to_owned(),
                            refs: vec![],
                            args: vec![],
                        },
                    ],
                }],
            }],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
        };

        // Scene: given f with status==0, when pack_and_ship, then f.status==2
        let scene = IRScene {
            name: "pack_then_ship".to_owned(),
            systems: vec!["S".to_owned()],
            givens: vec![IRSceneGiven {
                var: "f".to_owned(),
                entity: "F".to_owned(),
                constraint: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "f".to_owned(),
                            ty: IRType::Entity {
                                name: "F".to_owned(),
                            },

                            span: None,
                        }),
                        field: "status".to_owned(),
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
            }],
            events: vec![IRSceneEvent {
                var: "ps".to_owned(),
                system: "S".to_owned(),
                event: "pack_and_ship".to_owned(),
                args: vec![],
                cardinality: Cardinality::Named("one".to_owned()),
            }],
            ordering: vec![],
            assertions: vec![IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "f".to_owned(),
                        ty: IRType::Entity {
                            name: "F".to_owned(),
                        },

                        span: None,
                    }),
                    field: "status".to_owned(),
                    ty: IRType::Int,

                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 2 },

                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            }],
            span: None,
            file: None,
        };

        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![scene],
        };

        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 1);
        // Scene should PASS: pack (0→1) then ship (1→2) = final status 2.
        // Without intermediate chaining, ship's guard fails (sees 0, not 1).
        assert!(
            matches!(&results[0], VerificationResult::ScenePass { .. }),
            "scene with multi-apply should PASS: got {}",
            results[0]
        );
    }

    #[test]
    fn multi_apply_ic3_proves_property() {
        // IC3 rejects same-entity multi-apply (CHC per-Apply rules model
        // multi-step, not atomic intra-event composition). Falls through to
        // 4-phase induction which uses BMC-style intermediate variable chaining.
        // Property: status >= 0 (1-inductive: default 0, transitions set 1 or 2).
        let entity = IREntity {
            name: "F".to_owned(),
            fields: vec![IRField {
                name: "status".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },

                    span: None,
                }),
            }],
            transitions: vec![
                IRTransition {
                    name: "pack".to_owned(),
                    refs: vec![],
                    params: vec![],
                    guard: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "status".to_owned(),
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
                    updates: vec![IRUpdate {
                        field: "status".to_owned(),
                        value: IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 1 },

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
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 1 },

                            span: None,
                        }),
                        ty: IRType::Bool,

                        span: None,
                    },
                    updates: vec![IRUpdate {
                        field: "status".to_owned(),
                        value: IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 2 },

                            span: None,
                        },
                    }],
                    postcondition: None,
                },
            ],
        };

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["F".to_owned()],
            events: vec![
                IREvent {
                    name: "create_f".to_owned(),
                    params: vec![],
                    guard: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    },
                    postcondition: None,
                    body: vec![IRAction::Create {
                        entity: "F".to_owned(),
                        fields: vec![],
                    }],
                },
                IREvent {
                    name: "pack_and_ship".to_owned(),
                    params: vec![],
                    guard: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    },
                    postcondition: None,
                    body: vec![IRAction::Choose {
                        var: "f".to_owned(),
                        entity: "F".to_owned(),
                        filter: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },

                            span: None,
                        }),
                        ops: vec![
                            IRAction::Apply {
                                target: "f".to_owned(),
                                transition: "pack".to_owned(),
                                refs: vec![],
                                args: vec![],
                            },
                            IRAction::Apply {
                                target: "f".to_owned(),
                                transition: "ship".to_owned(),
                                refs: vec![],
                                args: vec![],
                            },
                        ],
                    }],
                },
            ],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
        };

        // Property: status >= 0 (always true: 0, 1, or 2)
        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "f".to_owned(),
                domain: IRType::Entity {
                    name: "F".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "f".to_owned(),
                            ty: IRType::Entity {
                                name: "F".to_owned(),
                            },

                            span: None,
                        }),
                        field: "status".to_owned(),
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

        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![],
            theorems: vec![IRTheorem {
                name: "multi_apply_ic3".to_owned(),
                systems: vec!["S".to_owned()],
                invariants: vec![],
                shows: vec![property],
                span: None,
                file: None,
            }],
            axioms: vec![],
            scenes: vec![],
        };

        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 1);
        // IC3 rejects multi-apply (Unknown), falls to 4-phase induction.
        // status >= 0 is 1-inductive (default 0, transitions set 1 or 2).
        assert!(
            matches!(
                &results[0],
                VerificationResult::Proved { method, .. } if method == "1-induction"
            ),
            "multi-apply theorem should be PROVED by 1-induction (IC3 rejects, falls through): got {}",
            results[0]
        );
    }

    #[test]
    fn multi_apply_step_scoping_no_intermediate_collision() {
        // Regression: two events with multi-apply chains in the same system.
        // Intermediate variables must be scoped by step and chain_id so that
        // chains at step 0 and step 1 don't alias each other.
        // Entity has three transitions: a (0→1), b (1→2), c (2→3).
        // Event "ab" does a+b (0→2), event "bc" does b+c (but can only fire
        // if status==1, which never happens via ab). We verify status <= 2
        // after create+ab — if intermediates aliased across events, the solver
        // could produce spurious states.
        let entity = IREntity {
            name: "F".to_owned(),
            fields: vec![IRField {
                name: "status".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },

                    span: None,
                }),
            }],
            transitions: vec![
                IRTransition {
                    name: "a".to_owned(),
                    refs: vec![],
                    params: vec![],
                    guard: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "status".to_owned(),
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
                    updates: vec![IRUpdate {
                        field: "status".to_owned(),
                        value: IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 1 },

                            span: None,
                        },
                    }],
                    postcondition: None,
                },
                IRTransition {
                    name: "b".to_owned(),
                    refs: vec![],
                    params: vec![],
                    guard: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "status".to_owned(),
                            ty: IRType::Int,

                            span: None,
                        }),
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 1 },

                            span: None,
                        }),
                        ty: IRType::Bool,

                        span: None,
                    },
                    updates: vec![IRUpdate {
                        field: "status".to_owned(),
                        value: IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 2 },

                            span: None,
                        },
                    }],
                    postcondition: None,
                },
                IRTransition {
                    name: "c".to_owned(),
                    refs: vec![],
                    params: vec![],
                    guard: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "status".to_owned(),
                            ty: IRType::Int,

                            span: None,
                        }),
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 2 },

                            span: None,
                        }),
                        ty: IRType::Bool,

                        span: None,
                    },
                    updates: vec![IRUpdate {
                        field: "status".to_owned(),
                        value: IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 3 },

                            span: None,
                        },
                    }],
                    postcondition: None,
                },
            ],
        };

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["F".to_owned()],
            events: vec![
                IREvent {
                    name: "create_f".to_owned(),
                    params: vec![],
                    guard: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    },
                    postcondition: None,
                    body: vec![IRAction::Create {
                        entity: "F".to_owned(),
                        fields: vec![],
                    }],
                },
                // Event ab: a (0→1) then b (1→2) — multi-apply chain
                IREvent {
                    name: "ab".to_owned(),
                    params: vec![],
                    guard: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    },
                    postcondition: None,
                    body: vec![IRAction::Choose {
                        var: "f".to_owned(),
                        entity: "F".to_owned(),
                        filter: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },

                            span: None,
                        }),
                        ops: vec![
                            IRAction::Apply {
                                target: "f".to_owned(),
                                transition: "a".to_owned(),
                                refs: vec![],
                                args: vec![],
                            },
                            IRAction::Apply {
                                target: "f".to_owned(),
                                transition: "b".to_owned(),
                                refs: vec![],
                                args: vec![],
                            },
                        ],
                    }],
                },
                // Event bc: b (1→2) then c (2→3) — second multi-apply chain
                IREvent {
                    name: "bc".to_owned(),
                    params: vec![],
                    guard: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    },
                    postcondition: None,
                    body: vec![IRAction::Choose {
                        var: "f".to_owned(),
                        entity: "F".to_owned(),
                        filter: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },

                            span: None,
                        }),
                        ops: vec![
                            IRAction::Apply {
                                target: "f".to_owned(),
                                transition: "b".to_owned(),
                                refs: vec![],
                                args: vec![],
                            },
                            IRAction::Apply {
                                target: "f".to_owned(),
                                transition: "c".to_owned(),
                                refs: vec![],
                                args: vec![],
                            },
                        ],
                    }],
                },
            ],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
        };

        // Property: status <= 3 (always true: 0 via default, 2 via ab, 3 via ab then bc)
        // If intermediates aliased across events, solver could produce spurious values.
        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "f".to_owned(),
                domain: IRType::Entity {
                    name: "F".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpLe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "f".to_owned(),
                            ty: IRType::Entity {
                                name: "F".to_owned(),
                            },

                            span: None,
                        }),
                        field: "status".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 3 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
        };

        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![IRVerify {
                name: "step_scope_test".to_owned(),
                systems: vec![IRVerifySystem {
                    name: "S".to_owned(),
                    lo: 0,
                    hi: 5,
                }],
                asserts: vec![property],
                span: None,
                file: None,
            }],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        };

        let config = VerifyConfig {
            bounded_only: true,
            ..VerifyConfig::default()
        };
        let results = verify_all(&ir, &config);
        assert_eq!(results.len(), 1);
        assert!(
            matches!(
                &results[0],
                VerificationResult::Proved { .. } | VerificationResult::Checked { .. }
            ),
            "two multi-apply events with distinct chains should not alias intermediates: got {}",
            results[0]
        );
    }

    #[test]
    fn multi_apply_active_flag_preserved_in_chain() {
        // Regression: multi-apply chain must assert active flag at step k AND k+1.
        // If active constraints were missing, an inactive entity slot could get
        // spurious intermediate state written through it.
        // Test: entity defaults to status=0, pack_and_ship chains pack(0→1)+ship(1→2).
        // Property: status is exactly 0 or 2 (never anything else at step boundaries).
        // This is tighter than >= 0 — validates that only active entities transition.
        let entity = IREntity {
            name: "F".to_owned(),
            fields: vec![IRField {
                name: "status".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },

                    span: None,
                }),
            }],
            transitions: vec![
                IRTransition {
                    name: "pack".to_owned(),
                    refs: vec![],
                    params: vec![],
                    guard: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "status".to_owned(),
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
                    updates: vec![IRUpdate {
                        field: "status".to_owned(),
                        value: IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 1 },

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
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 1 },

                            span: None,
                        }),
                        ty: IRType::Bool,

                        span: None,
                    },
                    updates: vec![IRUpdate {
                        field: "status".to_owned(),
                        value: IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 2 },

                            span: None,
                        },
                    }],
                    postcondition: None,
                },
            ],
        };

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["F".to_owned()],
            events: vec![
                IREvent {
                    name: "create_f".to_owned(),
                    params: vec![],
                    guard: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    },
                    postcondition: None,
                    body: vec![IRAction::Create {
                        entity: "F".to_owned(),
                        fields: vec![],
                    }],
                },
                IREvent {
                    name: "pack_and_ship".to_owned(),
                    params: vec![],
                    guard: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    },
                    postcondition: None,
                    body: vec![IRAction::Choose {
                        var: "f".to_owned(),
                        entity: "F".to_owned(),
                        filter: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },

                            span: None,
                        }),
                        ops: vec![
                            IRAction::Apply {
                                target: "f".to_owned(),
                                transition: "pack".to_owned(),
                                refs: vec![],
                                args: vec![],
                            },
                            IRAction::Apply {
                                target: "f".to_owned(),
                                transition: "ship".to_owned(),
                                refs: vec![],
                                args: vec![],
                            },
                        ],
                    }],
                },
            ],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
        };

        // Tighter property: status == 0 OR status == 2
        // Status 1 only exists in intermediate state within the event chain.
        // If active flag constraints were missing, inactive slots could leak
        // intermediate values (1) into step-boundary observations.
        let property = IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "f".to_owned(),
                domain: IRType::Entity {
                    name: "F".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpOr".to_owned(),
                    left: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "f".to_owned(),
                                ty: IRType::Entity {
                                    name: "F".to_owned(),
                                },

                                span: None,
                            }),
                            field: "status".to_owned(),
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
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "f".to_owned(),
                                ty: IRType::Entity {
                                    name: "F".to_owned(),
                                },

                                span: None,
                            }),
                            field: "status".to_owned(),
                            ty: IRType::Int,

                            span: None,
                        }),
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 2 },

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
        };

        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![IRVerify {
                name: "active_flag_test".to_owned(),
                systems: vec![IRVerifySystem {
                    name: "S".to_owned(),
                    lo: 0,
                    hi: 5,
                }],
                asserts: vec![property],
                span: None,
                file: None,
            }],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        };

        let config = VerifyConfig {
            bounded_only: true,
            ..VerifyConfig::default()
        };
        let results = verify_all(&ir, &config);
        assert_eq!(results.len(), 1);
        // Status should only be 0 (default/uncreated) or 2 (after pack_and_ship).
        // The intermediate value 1 must never appear at step boundaries.
        assert!(
            matches!(
                &results[0],
                VerificationResult::Proved { .. } | VerificationResult::Checked { .. }
            ),
            "status should be exactly 0 or 2 at step boundaries (active flag preserves chain integrity): got {}",
            results[0]
        );
    }

    #[test]
    fn multi_apply_second_apply_args_depend_on_first_update() {
        // Regression: when the second Apply's transition takes a parameter whose
        // value is computed from a field updated by the first Apply, the parameter
        // must be evaluated against the intermediate state, not the pre-state.
        //
        // Entity "F" has two fields: status (int) and amount (int, default 0).
        // Transition "prepare": guard status==0, sets status=1, sets amount=10.
        // Transition "finalize(expected: int)": guard status==1 AND amount==expected,
        //   sets status=2.
        // Event "prep_and_finalize": Choose f, f.prepare(), f.finalize(f.amount).
        // The arg `f.amount` must resolve to 10 (prepare's update), not 0 (pre-state).
        // Property: if status==2 then amount==10 (validates correct arg resolution).
        let entity = IREntity {
            name: "F".to_owned(),
            fields: vec![
                IRField {
                    name: "status".to_owned(),
                    ty: IRType::Int,
                    default: Some(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },

                        span: None,
                    }),
                },
                IRField {
                    name: "amount".to_owned(),
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
                    name: "prepare".to_owned(),
                    refs: vec![],
                    params: vec![],
                    guard: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "status".to_owned(),
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
                    updates: vec![
                        IRUpdate {
                            field: "status".to_owned(),
                            value: IRExpr::Lit {
                                ty: IRType::Int,
                                value: LitVal::Int { value: 1 },

                                span: None,
                            },
                        },
                        IRUpdate {
                            field: "amount".to_owned(),
                            value: IRExpr::Lit {
                                ty: IRType::Int,
                                value: LitVal::Int { value: 10 },

                                span: None,
                            },
                        },
                    ],
                    postcondition: None,
                },
                IRTransition {
                    name: "finalize".to_owned(),
                    refs: vec![],
                    params: vec![IRTransParam {
                        name: "expected".to_owned(),
                        ty: IRType::Int,
                    }],
                    // Guard: status==1 AND amount==expected
                    guard: IRExpr::BinOp {
                        op: "OpAnd".to_owned(),
                        left: Box::new(IRExpr::BinOp {
                            op: "OpEq".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "status".to_owned(),
                                ty: IRType::Int,

                                span: None,
                            }),
                            right: Box::new(IRExpr::Lit {
                                ty: IRType::Int,
                                value: LitVal::Int { value: 1 },

                                span: None,
                            }),
                            ty: IRType::Bool,

                            span: None,
                        }),
                        right: Box::new(IRExpr::BinOp {
                            op: "OpEq".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "amount".to_owned(),
                                ty: IRType::Int,

                                span: None,
                            }),
                            right: Box::new(IRExpr::Var {
                                name: "expected".to_owned(),
                                ty: IRType::Int,

                                span: None,
                            }),
                            ty: IRType::Bool,

                            span: None,
                        }),
                        ty: IRType::Bool,

                        span: None,
                    },
                    updates: vec![IRUpdate {
                        field: "status".to_owned(),
                        value: IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 2 },

                            span: None,
                        },
                    }],
                    postcondition: None,
                },
            ],
        };

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["F".to_owned()],
            events: vec![
                IREvent {
                    name: "create_f".to_owned(),
                    params: vec![],
                    guard: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    },
                    postcondition: None,
                    body: vec![IRAction::Create {
                        entity: "F".to_owned(),
                        fields: vec![],
                    }],
                },
                IREvent {
                    name: "prep_and_finalize".to_owned(),
                    params: vec![],
                    guard: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    },
                    postcondition: None,
                    body: vec![IRAction::Choose {
                        var: "f".to_owned(),
                        entity: "F".to_owned(),
                        filter: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },

                            span: None,
                        }),
                        ops: vec![
                            IRAction::Apply {
                                target: "f".to_owned(),
                                transition: "prepare".to_owned(),
                                refs: vec![],
                                args: vec![],
                            },
                            IRAction::Apply {
                                target: "f".to_owned(),
                                transition: "finalize".to_owned(),
                                refs: vec![],
                                // Arg: f.amount — must resolve from intermediate state (10),
                                // not pre-state (0)
                                args: vec![IRExpr::Var {
                                    name: "amount".to_owned(),
                                    ty: IRType::Int,

                                    span: None,
                                }],
                            },
                        ],
                    }],
                },
            ],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
        };

        // Property: if status == 2 then amount == 10.
        // If the second Apply's arg was evaluated against pre-state,
        // finalize's guard (amount==expected) would use expected=0 (pre-state amount),
        // which wouldn't match the intermediate amount=10, making finalize's guard UNSAT.
        // The event wouldn't fire, so status would stay at 0 — the property holds vacuously.
        //
        // With correct intermediate evaluation, expected=10 (from intermediate amount),
        // finalize fires (amount==10==expected), status goes to 2, and status==2 → amount==10
        // holds concretely.
        //
        // To distinguish: use a scene to verify the event CAN fire and produces status==2.
        use crate::ir::types::{Cardinality, IRScene, IRSceneEvent, IRSceneGiven};
        let scene = IRScene {
            name: "prep_finalize_fires".to_owned(),
            systems: vec!["S".to_owned()],
            givens: vec![IRSceneGiven {
                var: "f".to_owned(),
                entity: "F".to_owned(),
                constraint: IRExpr::BinOp {
                    op: "OpAnd".to_owned(),
                    left: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "f".to_owned(),
                                ty: IRType::Entity {
                                    name: "F".to_owned(),
                                },

                                span: None,
                            }),
                            field: "status".to_owned(),
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
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "f".to_owned(),
                                ty: IRType::Entity {
                                    name: "F".to_owned(),
                                },

                                span: None,
                            }),
                            field: "amount".to_owned(),
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
                },
            }],
            events: vec![IRSceneEvent {
                var: "pf".to_owned(),
                system: "S".to_owned(),
                event: "prep_and_finalize".to_owned(),
                args: vec![],
                cardinality: Cardinality::Named("one".to_owned()),
            }],
            ordering: vec![],
            // Assert: status reaches 2 AND amount is 10 (prepare's update)
            assertions: vec![
                IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "f".to_owned(),
                            ty: IRType::Entity {
                                name: "F".to_owned(),
                            },

                            span: None,
                        }),
                        field: "status".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 2 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                },
                IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "f".to_owned(),
                            ty: IRType::Entity {
                                name: "F".to_owned(),
                            },

                            span: None,
                        }),
                        field: "amount".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 10 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                },
            ],
            span: None,
            file: None,
        };

        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![scene],
        };

        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 1);
        // Scene must PASS: prepare sets amount=10, finalize's arg (f.amount)
        // reads from intermediate state and gets 10, guard is satisfied, status→2.
        assert!(
            matches!(&results[0], VerificationResult::ScenePass { .. }),
            "second Apply's args must resolve from intermediate state (amount=10, not 0): got {}",
            results[0]
        );
    }

    #[test]
    fn multi_apply_forall_rejected_in_scene() {
        // Regression: a scene whose event uses ForAll with multiple Apply actions
        // on the same entity must be rejected via find_unsupported_in_actions,
        // not silently encoded incorrectly.
        use crate::ir::types::{Cardinality, IRScene, IRSceneEvent, IRSceneGiven};

        let entity = IREntity {
            name: "F".to_owned(),
            fields: vec![IRField {
                name: "status".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },

                    span: None,
                }),
            }],
            transitions: vec![
                IRTransition {
                    name: "pack".to_owned(),
                    refs: vec![],
                    params: vec![],
                    guard: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "status".to_owned(),
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
                    updates: vec![IRUpdate {
                        field: "status".to_owned(),
                        value: IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 1 },

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
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 1 },

                            span: None,
                        }),
                        ty: IRType::Bool,

                        span: None,
                    },
                    updates: vec![IRUpdate {
                        field: "status".to_owned(),
                        value: IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 2 },

                            span: None,
                        },
                    }],
                    postcondition: None,
                },
            ],
        };

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["F".to_owned()],
            events: vec![IREvent {
                name: "pack_all_and_ship".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                postcondition: None,
                // ForAll with two Applies on same entity — NOT supported
                body: vec![IRAction::ForAll {
                    var: "f".to_owned(),
                    entity: "F".to_owned(),
                    ops: vec![
                        IRAction::Apply {
                            target: "f".to_owned(),
                            transition: "pack".to_owned(),
                            refs: vec![],
                            args: vec![],
                        },
                        IRAction::Apply {
                            target: "f".to_owned(),
                            transition: "ship".to_owned(),
                            refs: vec![],
                            args: vec![],
                        },
                    ],
                }],
            }],
            schedule: IRSchedule {
                when: vec![],
                idle: true,
            },
        };

        let scene = IRScene {
            name: "forall_multi_apply".to_owned(),
            systems: vec!["S".to_owned()],
            givens: vec![IRSceneGiven {
                var: "f".to_owned(),
                entity: "F".to_owned(),
                constraint: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "f".to_owned(),
                            ty: IRType::Entity {
                                name: "F".to_owned(),
                            },

                            span: None,
                        }),
                        field: "status".to_owned(),
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
            }],
            events: vec![IRSceneEvent {
                var: "ps".to_owned(),
                system: "S".to_owned(),
                event: "pack_all_and_ship".to_owned(),
                args: vec![],
                cardinality: Cardinality::Named("one".to_owned()),
            }],
            ordering: vec![],
            assertions: vec![IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "f".to_owned(),
                        ty: IRType::Entity {
                            name: "F".to_owned(),
                        },

                        span: None,
                    }),
                    field: "status".to_owned(),
                    ty: IRType::Int,

                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 2 },

                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            }],
            span: None,
            file: None,
        };

        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![scene],
        };

        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 1);
        // Must be rejected as SceneFail with "multiple Apply" message,
        // NOT silently encoded incorrectly.
        match &results[0] {
            VerificationResult::SceneFail { reason, .. } => {
                assert!(
                    reason.contains("multiple Apply"),
                    "ForAll multi-apply rejection should mention 'multiple Apply': got {reason}"
                );
            }
            other => panic!("ForAll multi-apply in scene should produce SceneFail, got: {other}"),
        }
    }
}
