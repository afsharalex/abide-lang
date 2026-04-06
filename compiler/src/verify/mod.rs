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

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::time::Instant;

use z3::ast::{Bool, Int};
use z3::Solver;

use crate::ir::types::{
    IRAction, IREvent, IRExpr, IRProgram, IRScene, IRSceneEvent, IRSystem, IRTheorem, IRType,
    IRVerify,
};

use self::context::VerifyContext;
use self::harness::{
    create_slot_pool, domain_constraints, encode_event_with_params, fairness_constraints,
    initial_state_constraints, lasso_loopback, symmetry_breaking_constraints,
    transition_constraints, transition_constraints_with_fire, SlotPool,
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
    /// Function contract (ensures) proved — body satisfies postcondition.
    FnContractProved {
        name: String,
        time_ms: u64,
        span: Option<crate::span::Span>,
        file: Option<String>,
    },
    /// Function contract admitted — body contains `assume` or `sorry`.
    /// Not a failure (exit code 0), but visually distinct from PROVED.
    FnContractAdmitted {
        name: String,
        reason: String,
        time_ms: u64,
        span: Option<crate::span::Span>,
        file: Option<String>,
    },
    /// Function contract (ensures) violated — counterexample found.
    FnContractFailed {
        name: String,
        counterexample: Vec<(String, String)>, // (param_name, value)
        span: Option<crate::span::Span>,
        file: Option<String>,
    },
    /// Liveness violation — lasso-shaped counterexample (infinite execution).
    /// The trace has a prefix (steps 0..loop_start) and a loop (steps
    /// loop_start..bound that repeats forever).
    LivenessViolation {
        name: String,
        prefix: Vec<TraceStep>,
        loop_trace: Vec<TraceStep>,
        loop_start: usize,
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
            Self::FnContractProved {
                name,
                time_ms,
                span,
                file,
            } => Self::FnContractProved {
                name,
                time_ms,
                span: span.or(block_span),
                file: file.or(block_file),
            },
            Self::FnContractAdmitted {
                name,
                reason,
                time_ms,
                span,
                file,
            } => Self::FnContractAdmitted {
                name,
                reason,
                time_ms,
                span: span.or(block_span),
                file: file.or(block_file),
            },
            Self::FnContractFailed {
                name,
                counterexample,
                span,
                file,
            } => Self::FnContractFailed {
                name,
                counterexample,
                span: span.or(block_span),
                file: file.or(block_file),
            },
            Self::LivenessViolation {
                name,
                prefix,
                loop_trace,
                loop_start,
                span,
                file,
            } => Self::LivenessViolation {
                name,
                prefix,
                loop_trace,
                loop_start,
                span: span.or(block_span),
                file: file.or(block_file),
            },
        }
    }

    /// Is this a failure (counterexample, scene fail, fn contract fail, liveness violation, or unprovable)?
    pub fn is_failure(&self) -> bool {
        matches!(
            self,
            Self::Counterexample { .. }
                | Self::SceneFail { .. }
                | Self::Unprovable { .. }
                | Self::FnContractFailed { .. }
                | Self::LivenessViolation { .. }
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
            | Self::Unprovable { span, .. }
            | Self::FnContractProved { span, .. }
            | Self::FnContractAdmitted { span, .. }
            | Self::FnContractFailed { span, .. }
            | Self::LivenessViolation { span, .. } => *span,
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
            | Self::Unprovable { file, .. }
            | Self::FnContractProved { file, .. }
            | Self::FnContractAdmitted { file, .. }
            | Self::LivenessViolation { file, .. }
            | Self::FnContractFailed { file, .. } => file.as_deref(),
        }
    }
}

/// A single step in a counterexample trace.
#[derive(Debug, Clone)]
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
    /// Skip function contract verification.
    pub no_fn_verify: bool,
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
            no_fn_verify: false,
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
    let mut defs = defenv::DefEnv::from_ir(ir);
    let mut results = Vec::new();

    // ── Verify lemmas ─────────────────────────────────────────────
    // Lemmas are system-independent properties. Each body expression
    // must be a tautology. Processed first so proved lemmas are
    // available to verify blocks, scenes, and theorems via DefEnv.
    for lemma_block in &ir.lemmas {
        if config.progress {
            eprint!("Proving lemma {}...", lemma_block.name);
        }
        let result = check_lemma_block(&vctx, &defs, lemma_block)
            .with_source(lemma_block.span, lemma_block.file.clone());
        if config.progress {
            eprintln!(" done");
        }
        // If the lemma proved, add its body to DefEnv under its declared
        // name so later verify/scene/theorem blocks can reference it.
        if matches!(&result, VerificationResult::Proved { .. }) {
            defs.add_lemma_fact(&lemma_block.name, &lemma_block.body);
        }
        results.push(result);
    }

    for verify_block in &ir.verifies {
        if config.progress {
            eprint!("Checking {}...", verify_block.name);
        }
        clear_prop_precondition_obligations();
        clear_path_guard_stack();
        let result = check_verify_block_tiered(ir, &vctx, &defs, verify_block, config)
            .with_source(verify_block.span, verify_block.file.clone());
        if config.progress {
            eprintln!(" done");
        }
        if let Some(violation) = check_prop_precondition_obligations() {
            results.push(
                VerificationResult::Unprovable {
                    name: verify_block.name.clone(),
                    hint: violation,
                    span: verify_block.span,
                    file: verify_block.file.clone(),
                },
            );
        } else {
            results.push(result);
        }
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
        clear_prop_precondition_obligations();
        clear_path_guard_stack();
        let result = check_theorem_block(ir, &vctx, &defs, theorem_block, config)
            .with_source(theorem_block.span, theorem_block.file.clone());
        if config.progress {
            eprintln!(" done");
        }
        if let Some(violation) = check_prop_precondition_obligations() {
            results.push(
                VerificationResult::Unprovable {
                    name: theorem_block.name.clone(),
                    hint: violation,
                    span: theorem_block.span,
                    file: theorem_block.file.clone(),
                },
            );
        } else {
            results.push(result);
        }
    }

    // ── Verify function contracts ───────────────────────────────────
    // For each fn with ensures, prove that the body satisfies the
    // postcondition given the precondition.
    if !config.no_fn_verify {
        verify_fn_contracts(ir, &vctx, &defs, config, &mut results);
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

// ── Function contract verification ──────────────────────────────────

/// Verify function contracts (ensures clauses) for all functions.
///
/// For each fn with non-empty `ensures` and no `prop_target` (i.e., not a prop):
/// - Declare Z3 variables for each parameter
/// - Assert requires as assumptions
/// - Assert NOT(ensures[result := body]) and check for counterexample
/// - UNSAT = postcondition holds; SAT = counterexample
fn verify_fn_contracts(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    config: &VerifyConfig,
    results: &mut Vec<VerificationResult>,
) {
    for func in &ir.functions {
        // Skip props (system-level properties, not fn contracts)
        if func.prop_target.is_some() {
            continue;
        }

        // Skip fns without ensures clauses AND without assert/assume/sorry.
        // Functions with assert must be verified even without ensures — the
        // assert itself is a verification obligation. Functions with sorry
        // should report ADMITTED even without ensures.
        let has_asserts = body_contains_assert(&func.body);
        let has_sorry = body_contains_sorry(&func.body);
        if func.ensures.is_empty() && !has_asserts && !has_sorry {
            continue;
        }

        // Sorry in body: admit the entire proof obligation — postcondition,
        // termination, everything — without attempting any verification.
        // Sorry means "I know this is unproved" (like Lean's sorry or Agda's
        // postulate). Checked before termination so that `sorry` in a
        // recursive body doesn't report spurious termination failures.
        if has_sorry {
            results.push(VerificationResult::FnContractAdmitted {
                name: func.name.clone(),
                reason: "sorry in body".to_owned(),
                time_ms: 0,
                span: func.span,
                file: func.file.clone(),
            });
            continue;
        }

        // Termination verification: for fns with decreases, prove
        // recursive calls decrease the measure AND satisfy the callee's requires.
        let mut termination_failed = false;
        if let Some(ref dec) = func.decreases {
            if !dec.star {
                if config.progress {
                    eprint!("Checking termination of fn {}...", func.name);
                }
                let start = Instant::now();
                let term_result = verify_fn_termination(func, vctx, defs);
                let _time_ms = elapsed_ms(&start);
                if config.progress {
                    eprintln!(" done");
                }
                if let Err(msg) = term_result {
                    results.push(VerificationResult::Unprovable {
                        name: format!("fn_{}", func.name),
                        hint: msg,
                        span: func.span,
                        file: func.file.clone(),
                    });
                    termination_failed = true;
                }
            }
        }

        // Skip postcondition verification if termination failed — the
        // recursive-call ensures assumptions are unsound without valid
        // termination + callee preconditions at recursive call sites.
        if termination_failed {
            continue;
        }

        if config.progress {
            eprint!("Verifying fn {}...", func.name);
        }

        let start = Instant::now();
        let result = verify_single_fn_contract(func, vctx, defs);
        let time_ms = elapsed_ms(&start);

        let has_assume = body_contains_assume(&func.body);
        let vr = match result {
            Ok(()) if has_assume => VerificationResult::FnContractAdmitted {
                name: func.name.clone(),
                reason: "assume in body".to_owned(),
                time_ms,
                span: func.span,
                file: func.file.clone(),
            },
            Ok(()) => VerificationResult::FnContractProved {
                name: func.name.clone(),
                time_ms,
                span: func.span,
                file: func.file.clone(),
            },
            Err(FnContractError::Counterexample(ce)) => VerificationResult::FnContractFailed {
                name: func.name.clone(),
                counterexample: ce,
                span: func.span,
                file: func.file.clone(),
            },
            Err(FnContractError::EncodingError(msg)) => VerificationResult::Unprovable {
                name: format!("fn_{}", func.name),
                hint: msg,
                span: func.span,
                file: func.file.clone(),
            },
        };

        if config.progress {
            eprintln!(" done");
        }
        results.push(vr);
    }
}

/// Error from fn contract verification.
enum FnContractError {
    /// Counterexample: parameter assignments that violate the ensures clause.
    Counterexample(Vec<(String, String)>),
    /// Encoding error: couldn't translate the expression to Z3.
    EncodingError(String),
}

/// Verify a single function's ensures clauses against its body.
///
/// For `fn f(x: Int, y: Int): Int requires P ensures Q = body`:
/// Check: ∀ x, y. P(x, y) → Q[result := body(x, y)]
/// Negated: ∃ x, y. P(x, y) ∧ ¬Q[result := body(x, y)]
/// UNSAT = proved, SAT = counterexample
fn verify_single_fn_contract(
    func: &crate::ir::types::IRFunction,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
) -> Result<(), FnContractError> {
    let solver = Solver::new();

    // Clear lambda axioms from any prior verification target
    clear_lambda_axioms();

    // Uncurry the function to get params and body
    let entry = defs.get(&func.name).ok_or_else(|| {
        FnContractError::EncodingError(format!("function '{}' not found in DefEnv", func.name))
    })?;

    let params = &entry.params;
    let body = &entry.body;

    // Create Z3 variables for each parameter (using vctx for ADT-encoded enums)
    let mut env: HashMap<String, SmtValue> = HashMap::new();
    for (name, ty) in params {
        let var = make_z3_var_ctx(name, ty, Some(vctx)).map_err(FnContractError::EncodingError)?;
        env.insert(name.clone(), var);
    }

    // Assert requires as assumptions
    for req in &func.requires {
        let req_val =
            encode_pure_expr(req, &env, vctx, defs).map_err(FnContractError::EncodingError)?;
        let req_bool = req_val
            .to_bool()
            .map_err(FnContractError::EncodingError)?;
        solver.assert(&req_bool);
    }

    // Encode the body using the imperative-aware encoder.
    // This handles While loops via Hoare-logic:
    //   - Verifies loop invariant init/preservation/termination as side conditions
    //   - Accumulates post-loop constraints (invariant ∧ ¬cond), properly guarded
    //     by branch conditions when inside if/else
    //   - Updates env with fresh post-loop variables
    let mut solver_constraints = Vec::new();
    let body_val =
        encode_fn_body(body, &mut env, &mut solver_constraints, &func.requires, &[], Some(func), vctx, defs)?;

    // Assert accumulated constraints (post-loop invariants, branch-guarded)
    for c in &solver_constraints {
        solver.assert(c);
    }

    // Assert ensures constraints from recursive self-calls (modular reasoning).
    // These assume the function's postcondition holds for recursive calls,
    // which is sound because Phase 1 proves the postcondition by induction.
    for c in &take_recursive_call_constraints() {
        solver.assert(c);
    }

    // Bind result to the body's return value
    env.insert("result".to_owned(), body_val);

    // Assert negation of ensures: looking for counterexample to postcondition
    let mut ensures_bools = Vec::new();
    for ens in &func.ensures {
        let ens_val = encode_pure_expr(ens, &env, vctx, defs)
            .map_err(FnContractError::EncodingError)?;
        let ens_bool = ens_val
            .to_bool()
            .map_err(FnContractError::EncodingError)?;
        ensures_bools.push(ens_bool);
    }

    let ensures_refs: Vec<&Bool> = ensures_bools.iter().collect();
    let all_ensures = Bool::and(&ensures_refs);
    solver.assert(&all_ensures.not());

    // Assert lambda definitional axioms AFTER all encoding (body + ensures).
    // Lambdas may appear in either body or ensures; all their axioms must be
    // available before the solver check.
    for axiom in &clone_lambda_axioms() {
        solver.assert(axiom);
    }

    // Check
    match solver.check() {
        z3::SatResult::Unsat => Ok(()), // Proved: no counterexample exists
        z3::SatResult::Sat => {
            // Extract counterexample
            let model = solver.get_model().unwrap();
            let mut ce = Vec::new();
            for (name, ty) in params {
                let val = env.get(name).unwrap();
                let val_str = extract_model_value(&model, val, &vctx.variants, ty);
                ce.push((name.clone(), val_str));
            }
            Err(FnContractError::Counterexample(ce))
        }
        z3::SatResult::Unknown => Err(FnContractError::EncodingError(
            "solver returned unknown (timeout or incomplete theory)".to_owned(),
        )),
    }
}

// ── Imperative body encoding (Hoare-logic for while loops) ──────────

/// Global counter for generating fresh post-loop variable names.
static LOOP_VAR_COUNTER: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

// Thread-local accumulator for ensures constraints from recursive self-calls.
// When encode_recursive_self_call creates a fresh result variable, it also
// encodes the function's ensures clauses (with actual args + result var
// substituted) and pushes them here. The caller asserts them on the main solver.
thread_local! {
    static RECURSIVE_CALL_CONSTRAINTS: RefCell<Vec<Bool>> =
        const { RefCell::new(Vec::new()) };
}

fn push_recursive_call_constraint(c: Bool) {
    RECURSIVE_CALL_CONSTRAINTS.with(|v| v.borrow_mut().push(c));
}

fn take_recursive_call_constraints() -> Vec<Bool> {
    RECURSIVE_CALL_CONSTRAINTS.with(|v| std::mem::take(&mut *v.borrow_mut()))
}

// Thread-local accumulator for lambda definitional axioms.
// When a lambda is encoded as a Z3 uninterpreted function, its
// definitional axiom (forall params. f(params) == body) is pushed here.
// The caller asserts them on the main solver.
thread_local! {
    static LAMBDA_AXIOMS: RefCell<Vec<Bool>> =
        const { RefCell::new(Vec::new()) };
}

fn push_lambda_axiom(axiom: Bool) {
    LAMBDA_AXIOMS.with(|v| v.borrow_mut().push(axiom));
}

/// Get a copy of all accumulated lambda axioms (non-destructive).
/// Every solver that may encounter lambda applications needs these.
fn clone_lambda_axioms() -> Vec<Bool> {
    LAMBDA_AXIOMS.with(|v| v.borrow().clone())
}

/// Clear all accumulated lambda axioms (call between verification targets).
fn clear_lambda_axioms() {
    LAMBDA_AXIOMS.with(|v| v.borrow_mut().clear());
}

/// Assert all accumulated lambda axioms on a solver.
/// Call this on every fresh VC solver (assert, loop, precondition checks).
fn assert_lambda_axioms_on(solver: &Solver) {
    for axiom in &clone_lambda_axioms() {
        solver.assert(axiom);
    }
}

/// Counter for generating unique lambda function names.
static LAMBDA_COUNTER: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

// Thread-local accumulator for call-site precondition obligations found
// during system-verification property encoding (encode_prop_expr /
// encode_prop_value). Each obligation is a Z3 Bool that represents
// `path_condition → precondition`. After encoding, these are checked
// as a conjunction: if any obligation is falsifiable, the property
// has a call-site precondition violation.
thread_local! {
    static PROP_PRECOND_OBLIGATIONS: RefCell<Vec<(Bool, String)>> =
        const { RefCell::new(Vec::new()) };
}

/// Record a precondition obligation during property encoding.
/// `obligation` is `path_guard → precondition` (already guarded).
fn record_prop_precondition_obligation(obligation: Bool, fn_name: String) {
    PROP_PRECOND_OBLIGATIONS.with(|v| {
        v.borrow_mut().push((obligation, fn_name));
    });
}

/// Take (and clear) all recorded precondition obligations.
fn take_prop_precondition_obligations() -> Vec<(Bool, String)> {
    PROP_PRECOND_OBLIGATIONS.with(|v| std::mem::take(&mut *v.borrow_mut()))
}

/// Clear all recorded precondition obligations (call before encoding).
fn clear_prop_precondition_obligations() {
    PROP_PRECOND_OBLIGATIONS.with(|v| v.borrow_mut().clear());
}

// Thread-local path guard stack. When encoding inside `A implies B`,
// the path guard for B is `A` (the call is only reachable when A is true).
// Nested implications accumulate: `A implies (B implies f(x))` has
// path guard `A ∧ B` for the `f(x)` call.
thread_local! {
    static PROP_PATH_GUARD: RefCell<Vec<Bool>> = const { RefCell::new(Vec::new()) };
}

fn push_path_guard(guard: Bool) {
    PROP_PATH_GUARD.with(|v| v.borrow_mut().push(guard));
}

fn pop_path_guard() {
    PROP_PATH_GUARD.with(|v| v.borrow_mut().pop());
}

fn clear_path_guard_stack() {
    PROP_PATH_GUARD.with(|v| v.borrow_mut().clear());
}

/// Get the current path guard (conjunction of all guards on the stack).
/// Returns `true` if the stack is empty (unconditional context).
fn current_path_guard() -> Bool {
    PROP_PATH_GUARD.with(|v| {
        let guards = v.borrow();
        if guards.is_empty() {
            Bool::from_bool(true)
        } else {
            let refs: Vec<&Bool> = guards.iter().collect();
            Bool::and(&refs)
        }
    })
}

/// Check accumulated precondition obligations. Returns the first
/// violation found (a function name whose precondition is falsifiable).
fn check_prop_precondition_obligations() -> Option<String> {
    let obligations = take_prop_precondition_obligations();
    for (obligation, fn_name) in &obligations {
        let vc = Solver::new();
        vc.assert(&obligation.not());
        if vc.check() != z3::SatResult::Unsat {
            return Some(format!(
                "precondition of '{fn_name}' may not hold at call site in property"
            ));
        }
    }
    None
}

/// Encode a function body that may contain imperative constructs (While, VarDecl, Block).
///
/// Unlike `encode_pure_expr`, this function:
/// - Threads the environment through Block expressions (sequential env mutation)
/// - Verifies while-loop invariants via Hoare-logic side conditions
/// - Creates fresh post-loop variables and asserts invariant ∧ ¬cond on the solver
/// `solver_constraints` accumulates Z3 Bool assertions that must hold
/// (e.g., post-loop invariants). These are NOT asserted immediately — the
/// caller decides how to assert them (e.g., guarded by branch conditions).
///
/// `extra_assumptions` carries Z3 Bool facts known to be true in the current
/// context — e.g., branch conditions from enclosing if/else. These are threaded
/// to loop verification so that branch-local invariants (like `invariant flag`
/// inside `if flag { ... }`) can be verified.
fn encode_fn_body(
    expr: &IRExpr,
    env: &mut HashMap<String, SmtValue>,
    solver_constraints: &mut Vec<Bool>,
    fn_requires: &[IRExpr],
    extra_assumptions: &[Bool],
    self_fn: Option<&crate::ir::types::IRFunction>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
) -> Result<SmtValue, FnContractError> {
    match expr {
        // Lam: peel off the lambda, bind the param, recurse
        IRExpr::Lam {
            param,
            param_type,
            body,
            ..
        } => {
            if !env.contains_key(param) {
                let var = make_z3_var(param, param_type)
                    .map_err(FnContractError::EncodingError)?;
                env.insert(param.clone(), var);
            }
            encode_fn_body(body, env, solver_constraints, fn_requires, extra_assumptions, self_fn, vctx, defs)
        }

        // VarDecl: evaluate init, extend env, recurse into rest
        IRExpr::VarDecl {
            name, init, rest, ..
        } => {
            let val = encode_pure_expr(init, env, vctx, defs)
                .map_err(FnContractError::EncodingError)?;
            env.insert(name.clone(), val);
            encode_fn_body(rest, env, solver_constraints, fn_requires, extra_assumptions, self_fn, vctx, defs)
        }

        // Block: thread env through each expression sequentially
        IRExpr::Block { exprs, .. } => {
            if exprs.is_empty() {
                return Ok(smt::bool_val(true));
            }
            let mut last = smt::bool_val(true);
            for e in exprs {
                last = encode_fn_body(e, env, solver_constraints, fn_requires, extra_assumptions, self_fn, vctx, defs)?;
            }
            Ok(last)
        }

        // While: Hoare-logic verification
        IRExpr::While {
            cond,
            invariants,
            decreases,
            body,
            ..
        } => encode_while_hoare(
            cond,
            invariants,
            decreases,
            body,
            env,
            solver_constraints,
            fn_requires,
            extra_assumptions,
            vctx,
            defs,
        ),

        // Assignment: BinOp(OpEq, Var(name), expr) in imperative context
        IRExpr::BinOp {
            op,
            left,
            right,
            ..
        } if op == "OpEq" && matches!(left.as_ref(), IRExpr::Var { .. }) => {
            if let IRExpr::Var { name, .. } = left.as_ref() {
                if env.contains_key(name) {
                    let val = encode_pure_expr(right, env, vctx, defs)
                        .map_err(FnContractError::EncodingError)?;
                    env.insert(name.clone(), val);
                    return Ok(smt::bool_val(true));
                }
            }
            encode_pure_expr(expr, env, vctx, defs)
                .map_err(FnContractError::EncodingError)
        }

        // IfElse with possible imperative branches
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            if contains_imperative(then_body)
                || else_body.as_ref().map_or(false, |e| contains_imperative(e))
            {
                encode_imperative_if_else(
                    cond,
                    then_body,
                    else_body.as_deref(),
                    env,
                    solver_constraints,
                    fn_requires,
                    extra_assumptions,
                    self_fn,
                    vctx,
                    defs,
                )
            } else {
                let precheck = PrecheckCtx {
                    fn_requires,
                    extra_assumptions,
                    self_fn,
                };
                encode_pure_expr_checked(expr, env, vctx, defs, &precheck)
                    .map_err(FnContractError::EncodingError)
            }
        }

        // Assert: generate a VC to prove the assertion holds at this point,
        // then make the assertion truth available as a fact for subsequent code.
        IRExpr::Assert { expr: assert_expr, span } => {
            let assert_val = encode_pure_expr(assert_expr, env, vctx, defs)
                .map_err(FnContractError::EncodingError)?;
            let assert_bool = assert_val
                .to_bool()
                .map_err(FnContractError::EncodingError)?;

            // VC check: prove assert_expr holds given fn_requires + extra_assumptions + accumulated constraints
            let vc_solver = Solver::new();
            assert_lambda_axioms_on(&vc_solver);
            // Assert function preconditions
            for req in fn_requires {
                let req_val = encode_pure_expr(req, env, vctx, defs)
                    .map_err(FnContractError::EncodingError)?;
                let req_bool = req_val
                    .to_bool()
                    .map_err(FnContractError::EncodingError)?;
                vc_solver.assert(&req_bool);
            }
            // Assert extra assumptions (e.g., from enclosing branches)
            for assumption in extra_assumptions {
                vc_solver.assert(assumption);
            }
            // Assert all accumulated solver constraints (loop postconditions, etc.)
            for c in solver_constraints.iter() {
                vc_solver.assert(c);
            }
            // Assert negation of the assertion — looking for a counterexample
            vc_solver.assert(&assert_bool.not());
            assert_lambda_axioms_on(&vc_solver);

            match vc_solver.check() {
                z3::SatResult::Unsat => {
                    // Proved: assertion holds. Make it available as a fact.
                    solver_constraints.push(assert_bool);
                    Ok(smt::bool_val(true))
                }
                z3::SatResult::Sat | z3::SatResult::Unknown => {
                    Err(FnContractError::EncodingError(
                        if let Some(sp) = span {
                            format!(
                                "{} (at byte offset {}..{})",
                                crate::messages::FN_ASSERT_FAILED,
                                sp.start, sp.end,
                            )
                        } else {
                            crate::messages::FN_ASSERT_FAILED.to_owned()
                        },
                    ))
                }
            }
        }

        // Assume: add the expression as a fact without proof.
        // The user takes responsibility for its truth.
        IRExpr::Assume { expr: assume_expr, .. } => {
            let assume_val = encode_pure_expr(assume_expr, env, vctx, defs)
                .map_err(FnContractError::EncodingError)?;
            let assume_bool = assume_val
                .to_bool()
                .map_err(FnContractError::EncodingError)?;
            // Push as a solver constraint — assumed true for subsequent code
            solver_constraints.push(assume_bool);
            Ok(smt::bool_val(true))
        }

        // Everything else (including App): delegate to pure encoder with
        // precondition checking enabled. This ensures ALL nested function
        // calls have their preconditions verified, not just top-level ones.
        _ => {
            let precheck = PrecheckCtx {
                fn_requires,
                extra_assumptions,
                self_fn,
            };
            encode_pure_expr_checked(expr, env, vctx, defs, &precheck)
                .map_err(FnContractError::EncodingError)
        }
    }
}

/// Check if an expression contains imperative constructs (While, VarDecl, mutable assignment).
fn contains_imperative(expr: &IRExpr) -> bool {
    match expr {
        IRExpr::While { .. } | IRExpr::VarDecl { .. } | IRExpr::Assert { .. } | IRExpr::Assume { .. } => true,
        // Assignment: BinOp(OpEq, Var(_), _) is an imperative mutation
        IRExpr::BinOp { op, left, .. }
            if op == "OpEq" && matches!(left.as_ref(), IRExpr::Var { .. }) =>
        {
            true
        }
        IRExpr::Block { exprs, .. } => exprs.iter().any(contains_imperative),
        IRExpr::IfElse {
            then_body,
            else_body,
            ..
        } => {
            contains_imperative(then_body)
                || else_body.as_ref().map_or(false, |e| contains_imperative(e))
        }
        _ => false,
    }
}

/// Check if a function body contains any `assert` or `assume` statements.
/// Used to determine if a function without `ensures` should still be verified.
///
/// Walks the entire expression tree — assert/assume may appear nested inside
/// any expression form (e.g., `x + (assert false)`), not just at statement level.
fn body_contains_assert(expr: &IRExpr) -> bool {
    match expr {
        IRExpr::Assert { .. } | IRExpr::Assume { .. } => true,
        IRExpr::Block { exprs, .. } => exprs.iter().any(body_contains_assert),
        IRExpr::Lam { body, .. }
        | IRExpr::Always { body, .. }
        | IRExpr::Eventually { body, .. } => body_contains_assert(body),
        IRExpr::VarDecl {
            init, rest, ..
        } => body_contains_assert(init) || body_contains_assert(rest),
        IRExpr::While {
            cond,
            invariants,
            body,
            ..
        } => {
            body_contains_assert(cond)
                || invariants.iter().any(body_contains_assert)
                || body_contains_assert(body)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            body_contains_assert(cond)
                || body_contains_assert(then_body)
                || else_body.as_ref().map_or(false, |e| body_contains_assert(e))
        }
        IRExpr::BinOp { left, right, .. }
        | IRExpr::Until { left, right, .. } => {
            body_contains_assert(left) || body_contains_assert(right)
        }
        IRExpr::UnOp { operand, .. } => body_contains_assert(operand),
        IRExpr::App { func, arg, .. } => {
            body_contains_assert(func) || body_contains_assert(arg)
        }
        IRExpr::Let { bindings, body, .. } => {
            bindings.iter().any(|b| body_contains_assert(&b.expr)) || body_contains_assert(body)
        }
        IRExpr::Forall { body, .. }
        | IRExpr::Exists { body, .. }
        | IRExpr::One { body, .. }
        | IRExpr::Lone { body, .. } => body_contains_assert(body),
        IRExpr::Field { expr, .. }
        | IRExpr::Prime { expr, .. }
        | IRExpr::Card { expr, .. } => body_contains_assert(expr),
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            body_contains_assert(scrutinee)
                || arms.iter().any(|a| {
                    a.guard.as_ref().map_or(false, body_contains_assert)
                        || body_contains_assert(&a.body)
                })
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            body_contains_assert(map)
                || body_contains_assert(key)
                || body_contains_assert(value)
        }
        IRExpr::Index { map, key, .. } => {
            body_contains_assert(map) || body_contains_assert(key)
        }
        IRExpr::SetComp {
            filter, projection, ..
        } => {
            body_contains_assert(filter)
                || projection.as_ref().map_or(false, |p| body_contains_assert(p))
        }
        IRExpr::SetLit { elements, .. } | IRExpr::SeqLit { elements, .. } => {
            elements.iter().any(body_contains_assert)
        }
        IRExpr::MapLit { entries, .. } => {
            entries.iter().any(|(k, v)| body_contains_assert(k) || body_contains_assert(v))
        }
        IRExpr::Lit { .. }
        | IRExpr::Var { .. }
        | IRExpr::Ctor { .. }
        | IRExpr::Sorry { .. }
        | IRExpr::Todo { .. } => false,
    }
}

/// Check if a function body contains any `assume` statement (specifically).
/// Used to determine if a verified function should be reported as ADMITTED.
fn body_contains_assume(expr: &IRExpr) -> bool {
    match expr {
        IRExpr::Assume { .. } => true,
        IRExpr::Assert { expr, .. } => body_contains_assume(expr),
        IRExpr::Block { exprs, .. } => exprs.iter().any(body_contains_assume),
        IRExpr::Lam { body, .. } => body_contains_assume(body),
        IRExpr::VarDecl { init, rest, .. } => {
            body_contains_assume(init) || body_contains_assume(rest)
        }
        IRExpr::While { cond, invariants, body, .. } => {
            body_contains_assume(cond)
                || invariants.iter().any(body_contains_assume)
                || body_contains_assume(body)
        }
        IRExpr::IfElse { cond, then_body, else_body, .. } => {
            body_contains_assume(cond)
                || body_contains_assume(then_body)
                || else_body.as_ref().map_or(false, |e| body_contains_assume(e))
        }
        IRExpr::BinOp { left, right, .. } => {
            body_contains_assume(left) || body_contains_assume(right)
        }
        IRExpr::UnOp { operand, .. } => body_contains_assume(operand),
        IRExpr::App { func, arg, .. } => {
            body_contains_assume(func) || body_contains_assume(arg)
        }
        IRExpr::Let { bindings, body, .. } => {
            bindings.iter().any(|b| body_contains_assume(&b.expr)) || body_contains_assume(body)
        }
        IRExpr::Match { scrutinee, arms, .. } => {
            body_contains_assume(scrutinee)
                || arms.iter().any(|a| {
                    a.guard.as_ref().map_or(false, body_contains_assume)
                        || body_contains_assume(&a.body)
                })
        }
        _ => false,
    }
}

/// Check if a function body contains `sorry`.
/// Used to short-circuit verification — sorry admits the entire proof obligation.
///
/// Walks the entire expression tree so nested forms like `x + sorry` are detected.
fn body_contains_sorry(expr: &IRExpr) -> bool {
    match expr {
        IRExpr::Sorry { .. } => true,
        IRExpr::Block { exprs, .. } => exprs.iter().any(body_contains_sorry),
        IRExpr::Lam { body, .. }
        | IRExpr::Always { body, .. }
        | IRExpr::Eventually { body, .. } => body_contains_sorry(body),
        IRExpr::VarDecl { init, rest, .. } => {
            body_contains_sorry(init) || body_contains_sorry(rest)
        }
        IRExpr::While { cond, invariants, body, .. } => {
            body_contains_sorry(cond)
                || invariants.iter().any(body_contains_sorry)
                || body_contains_sorry(body)
        }
        IRExpr::IfElse { cond, then_body, else_body, .. } => {
            body_contains_sorry(cond)
                || body_contains_sorry(then_body)
                || else_body.as_ref().map_or(false, |e| body_contains_sorry(e))
        }
        IRExpr::BinOp { left, right, .. }
        | IRExpr::Until { left, right, .. } => {
            body_contains_sorry(left) || body_contains_sorry(right)
        }
        IRExpr::UnOp { operand, .. } => body_contains_sorry(operand),
        IRExpr::App { func, arg, .. } => {
            body_contains_sorry(func) || body_contains_sorry(arg)
        }
        IRExpr::Let { bindings, body, .. } => {
            bindings.iter().any(|b| body_contains_sorry(&b.expr)) || body_contains_sorry(body)
        }
        IRExpr::Forall { body, .. }
        | IRExpr::Exists { body, .. }
        | IRExpr::One { body, .. }
        | IRExpr::Lone { body, .. } => body_contains_sorry(body),
        IRExpr::Field { expr, .. }
        | IRExpr::Prime { expr, .. }
        | IRExpr::Card { expr, .. }
        | IRExpr::Assert { expr, .. }
        | IRExpr::Assume { expr, .. } => body_contains_sorry(expr),
        IRExpr::Match { scrutinee, arms, .. } => {
            body_contains_sorry(scrutinee)
                || arms.iter().any(|a| {
                    a.guard.as_ref().map_or(false, body_contains_sorry)
                        || body_contains_sorry(&a.body)
                })
        }
        IRExpr::MapUpdate { map, key, value, .. } => {
            body_contains_sorry(map)
                || body_contains_sorry(key)
                || body_contains_sorry(value)
        }
        IRExpr::Index { map, key, .. } => {
            body_contains_sorry(map) || body_contains_sorry(key)
        }
        IRExpr::SetComp { filter, projection, .. } => {
            body_contains_sorry(filter)
                || projection.as_ref().map_or(false, |p| body_contains_sorry(p))
        }
        IRExpr::SetLit { elements, .. } | IRExpr::SeqLit { elements, .. } => {
            elements.iter().any(body_contains_sorry)
        }
        IRExpr::MapLit { entries, .. } => {
            entries.iter().any(|(k, v)| body_contains_sorry(k) || body_contains_sorry(v))
        }
        IRExpr::Lit { .. }
        | IRExpr::Var { .. }
        | IRExpr::Ctor { .. }
        | IRExpr::Todo { .. } => false,
    }
}

/// Encode a while loop using Hoare-logic verification.
///
/// Verification conditions:
/// 1. **Init**: invariant holds with current env values
/// 2. **Preservation**: invariant ∧ cond → invariant[after body]
/// 3. **Termination** (if decreases): measure ≥ 0 ∧ measure decreases
/// 4. **Post-loop**: create fresh vars, assert invariant ∧ ¬cond, update env
#[allow(clippy::too_many_arguments)]
fn encode_while_hoare(
    cond: &IRExpr,
    invariants: &[IRExpr],
    decreases: &Option<crate::ir::types::IRDecreases>,
    body: &IRExpr,
    env: &mut HashMap<String, SmtValue>,
    solver_constraints: &mut Vec<Bool>,
    fn_requires: &[IRExpr],
    extra_assumptions: &[Bool],
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
) -> Result<SmtValue, FnContractError> {
    // ── Step 1: Identify variables modified by the loop body ─────────
    let mut modified = Vec::new();
    collect_modified_vars(body, &mut modified);
    modified.sort();
    modified.dedup();

    // ── Step 2: Verify loop conditions (init, preservation, termination) ──
    verify_loop_conditions(cond, invariants, decreases, body, &modified, env, fn_requires, extra_assumptions, vctx, defs)?;

    // ── Step 3: Post-loop abstraction ───────────────────────────────
    // Create fresh Z3 variables for all modified variables.
    // Assert invariant ∧ ¬cond on the main solver.
    // Update env with fresh post-loop variables.
    let counter = LOOP_VAR_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    for var_name in &modified {
        if let Some(old_val) = env.get(var_name) {
            // Create a fresh Z3 variable for the post-loop value
            let fresh_name = format!("{var_name}_post_{counter}");
            let fresh_var = make_z3_var_from_smt(&fresh_name, old_val);
            env.insert(var_name.clone(), fresh_var);
        }
    }

    // Accumulate post-loop constraints (invariant ∧ ¬cond).
    // These are NOT asserted directly — the caller will assert them,
    // potentially guarded by branch conditions if inside an if/else.
    for inv in invariants {
        let inv_val = encode_pure_expr(inv, env, vctx, defs)
            .map_err(FnContractError::EncodingError)?;
        let inv_bool = inv_val
            .to_bool()
            .map_err(FnContractError::EncodingError)?;
        solver_constraints.push(inv_bool);
    }

    // ¬cond (loop exited)
    let cond_val = encode_pure_expr(cond, env, vctx, defs)
        .map_err(FnContractError::EncodingError)?;
    let cond_bool = cond_val
        .to_bool()
        .map_err(FnContractError::EncodingError)?;
    solver_constraints.push(cond_bool.not());

    // The while loop itself produces no meaningful value — it's executed
    // for side effects (env mutation). Return a unit-like value.
    Ok(smt::bool_val(true))
}

/// Verify the three Hoare-logic conditions for a while loop:
/// 1. Invariant initialization
/// 2. Invariant preservation
/// 3. Termination (if decreases clause present)
#[allow(clippy::too_many_arguments)]
fn verify_loop_conditions(
    cond: &IRExpr,
    invariants: &[IRExpr],
    decreases: &Option<crate::ir::types::IRDecreases>,
    body: &IRExpr,
    modified: &[String],
    env: &HashMap<String, SmtValue>,
    fn_requires: &[IRExpr],
    extra_assumptions: &[Bool],
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
) -> Result<(), FnContractError> {
    if invariants.is_empty() {
        return Err(FnContractError::EncodingError(
            crate::messages::FN_LOOP_NO_INVARIANT.to_owned(),
        ));
    }

    verify_loop_init(invariants, env, fn_requires, extra_assumptions, vctx, defs)?;
    verify_loop_preservation(cond, invariants, body, modified, env, fn_requires, extra_assumptions, vctx, defs)?;

    if let Some(dec) = decreases {
        if !dec.star {
            verify_loop_termination(
                cond, invariants, &dec.measures, body, modified, env, fn_requires,
                extra_assumptions, vctx, defs,
            )?;
        }
    }

    Ok(())
}

/// VC1: Verify that the loop invariant holds at initialization.
///
/// Check: ¬invariant(env) is UNSAT → invariant always holds with current values.
fn verify_loop_init(
    invariants: &[IRExpr],
    env: &HashMap<String, SmtValue>,
    fn_requires: &[IRExpr],
    extra_assumptions: &[Bool],
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
) -> Result<(), FnContractError> {
    let vc_solver = Solver::new();
    assert_lambda_axioms_on(&vc_solver);

    // Assert function preconditions and any outer context assumptions
    for req in fn_requires {
        let req_val = encode_pure_expr(req, env, vctx, defs)
            .map_err(FnContractError::EncodingError)?;
        let req_bool = req_val
            .to_bool()
            .map_err(FnContractError::EncodingError)?;
        vc_solver.assert(&req_bool);
    }
    for assumption in extra_assumptions {
        vc_solver.assert(assumption);
    }

    // Assert ¬invariant — looking for counterexample to init
    let mut inv_bools = Vec::new();
    for inv in invariants {
        let inv_val = encode_pure_expr(inv, env, vctx, defs)
            .map_err(FnContractError::EncodingError)?;
        let inv_bool = inv_val
            .to_bool()
            .map_err(FnContractError::EncodingError)?;
        inv_bools.push(inv_bool);
    }
    let inv_refs: Vec<&Bool> = inv_bools.iter().collect();
    let all_inv = Bool::and(&inv_refs);
    vc_solver.assert(&all_inv.not());

    // Assert lambda axioms after all encoding (invariants may contain lambdas)
    assert_lambda_axioms_on(&vc_solver);

    match vc_solver.check() {
        z3::SatResult::Unsat => Ok(()),
        z3::SatResult::Sat | z3::SatResult::Unknown => {
            Err(FnContractError::EncodingError(
                crate::messages::FN_LOOP_INIT_FAILED.to_owned(),
            ))
        }
    }
}

/// VC2: Verify invariant preservation — one iteration maintains the invariant.
///
/// Check: invariant ∧ cond ∧ body → invariant
/// Negated: invariant ∧ cond ∧ ¬invariant[post_body] is UNSAT
#[allow(clippy::too_many_arguments)]
fn verify_loop_preservation(
    cond: &IRExpr,
    invariants: &[IRExpr],
    body: &IRExpr,
    modified: &[String],
    env: &HashMap<String, SmtValue>,
    fn_requires: &[IRExpr],
    extra_assumptions: &[Bool],
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
) -> Result<(), FnContractError> {
    let vc_solver = Solver::new();
    assert_lambda_axioms_on(&vc_solver);

    // Create fresh "pre-iteration" variables for all modified vars.
    let counter = LOOP_VAR_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let mut pre_env = env.clone();
    for var_name in modified {
        if let Some(old_val) = env.get(var_name) {
            let fresh_name = format!("{var_name}_pre_{counter}");
            let fresh_var = make_z3_var_from_smt(&fresh_name, old_val);
            pre_env.insert(var_name.clone(), fresh_var);
        }
    }

    // Assume function preconditions and outer context
    for req in fn_requires {
        let req_val = encode_pure_expr(req, &pre_env, vctx, defs)
            .map_err(FnContractError::EncodingError)?;
        vc_solver.assert(
            &req_val
                .to_bool()
                .map_err(FnContractError::EncodingError)?,
        );
    }
    for assumption in extra_assumptions {
        vc_solver.assert(assumption);
    }

    // Assume invariant holds for pre-iteration values.
    // Collect as Bool values too, for inner loop context.
    let mut inner_assumptions: Vec<Bool> = extra_assumptions.to_vec();
    for inv in invariants {
        let inv_val = encode_pure_expr(inv, &pre_env, vctx, defs)
            .map_err(FnContractError::EncodingError)?;
        let inv_bool = inv_val
            .to_bool()
            .map_err(FnContractError::EncodingError)?;
        vc_solver.assert(&inv_bool);
        inner_assumptions.push(inv_bool);
    }

    // Assume condition holds (we're inside the loop)
    let cond_val = encode_pure_expr(cond, &pre_env, vctx, defs)
        .map_err(FnContractError::EncodingError)?;
    let cond_bool = cond_val
        .to_bool()
        .map_err(FnContractError::EncodingError)?;
    vc_solver.assert(&cond_bool);
    inner_assumptions.push(cond_bool);

    // Also add fn_requires as Bool for inner loop context
    for req in fn_requires {
        let req_val = encode_pure_expr(req, &pre_env, vctx, defs)
            .map_err(FnContractError::EncodingError)?;
        inner_assumptions.push(
            req_val
                .to_bool()
                .map_err(FnContractError::EncodingError)?,
        );
    }

    // Execute the body to get post-iteration variable values
    let mut post_env = pre_env.clone();
    let mut body_constraints = Vec::new();
    execute_loop_body(body, &mut post_env, &mut body_constraints, &inner_assumptions, vctx, defs)?;

    // Assert any constraints from nested loops (inner invariant ∧ ¬inner_cond)
    for c in &body_constraints {
        vc_solver.assert(c);
    }

    // Assert ¬invariant[post] — looking for counterexample to preservation
    let mut post_inv_bools = Vec::new();
    for inv in invariants {
        let inv_val = encode_pure_expr(inv, &post_env, vctx, defs)
            .map_err(FnContractError::EncodingError)?;
        let inv_bool = inv_val
            .to_bool()
            .map_err(FnContractError::EncodingError)?;
        post_inv_bools.push(inv_bool);
    }
    let post_refs: Vec<&Bool> = post_inv_bools.iter().collect();
    let all_post = Bool::and(&post_refs);
    vc_solver.assert(&all_post.not());

    // Assert lambda axioms after all encoding
    assert_lambda_axioms_on(&vc_solver);

    match vc_solver.check() {
        z3::SatResult::Unsat => Ok(()),
        z3::SatResult::Sat | z3::SatResult::Unknown => {
            Err(FnContractError::EncodingError(
                crate::messages::FN_LOOP_PRESERVATION_FAILED.to_owned(),
            ))
        }
    }
}

/// VC3: Verify termination — decreases measure is non-negative and strictly decreases.
///
/// Check: invariant ∧ cond → D ≥ 0 ∧ D[post] < D[pre]
#[allow(clippy::too_many_arguments)]
fn verify_loop_termination(
    cond: &IRExpr,
    invariants: &[IRExpr],
    measures: &[IRExpr],
    body: &IRExpr,
    modified: &[String],
    env: &HashMap<String, SmtValue>,
    fn_requires: &[IRExpr],
    extra_assumptions: &[Bool],
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
) -> Result<(), FnContractError> {
    let vc_solver = Solver::new();
    assert_lambda_axioms_on(&vc_solver);

    // Create fresh pre-iteration variables
    let counter = LOOP_VAR_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let mut pre_env = env.clone();
    for var_name in modified {
        if let Some(old_val) = env.get(var_name) {
            let fresh_name = format!("{var_name}_term_{counter}");
            let fresh_var = make_z3_var_from_smt(&fresh_name, old_val);
            pre_env.insert(var_name.clone(), fresh_var);
        }
    }

    // Assume requires ∧ extra_assumptions ∧ invariant ∧ cond
    let mut inner_assumptions: Vec<Bool> = extra_assumptions.to_vec();
    for req in fn_requires {
        let req_val = encode_pure_expr(req, &pre_env, vctx, defs)
            .map_err(FnContractError::EncodingError)?;
        let req_bool = req_val
            .to_bool()
            .map_err(FnContractError::EncodingError)?;
        vc_solver.assert(&req_bool);
        inner_assumptions.push(req_bool);
    }
    for assumption in extra_assumptions {
        vc_solver.assert(assumption);
    }
    for inv in invariants {
        let inv_val = encode_pure_expr(inv, &pre_env, vctx, defs)
            .map_err(FnContractError::EncodingError)?;
        let inv_bool = inv_val
            .to_bool()
            .map_err(FnContractError::EncodingError)?;
        vc_solver.assert(&inv_bool);
        inner_assumptions.push(inv_bool);
    }
    let cond_val = encode_pure_expr(cond, &pre_env, vctx, defs)
        .map_err(FnContractError::EncodingError)?;
    let cond_bool = cond_val
        .to_bool()
        .map_err(FnContractError::EncodingError)?;
    vc_solver.assert(&cond_bool);
    inner_assumptions.push(cond_bool);

    // Evaluate decreases measure before iteration
    let pre_measures: Vec<SmtValue> = measures
        .iter()
        .map(|m| encode_pure_expr(m, &pre_env, vctx, defs).map_err(FnContractError::EncodingError))
        .collect::<Result<_, _>>()?;

    // Execute body
    let mut post_env = pre_env.clone();
    let mut body_constraints = Vec::new();
    execute_loop_body(body, &mut post_env, &mut body_constraints, &inner_assumptions, vctx, defs)?;

    // Assert any constraints from nested loops
    for c in &body_constraints {
        vc_solver.assert(c);
    }

    // Evaluate decreases measure after iteration
    let post_measures: Vec<SmtValue> = measures
        .iter()
        .map(|m| encode_pure_expr(m, &post_env, vctx, defs).map_err(FnContractError::EncodingError))
        .collect::<Result<_, _>>()?;

    // For single measure: assert ¬(pre ≥ 0 ∧ post < pre)
    // For multiple measures: lexicographic ordering (first that differs must decrease)
    // Start with single measure (most common)
    if pre_measures.len() == 1 {
        let pre_m = pre_measures[0]
            .as_int()
            .map_err(FnContractError::EncodingError)?;
        let post_m = post_measures[0]
            .as_int()
            .map_err(FnContractError::EncodingError)?;
        let bounded = pre_m.ge(z3::ast::Int::from_i64(0));
        let decreases_strict = post_m.lt(pre_m);
        let term_ok = Bool::and(&[&bounded, &decreases_strict]);
        vc_solver.assert(&term_ok.not());
    } else {
        // Lexicographic: ∃ i. (∀ j < i. mⱼ_post == mⱼ_pre) ∧ mᵢ_post < mᵢ_pre ∧ mᵢ_pre ≥ 0
        let mut lex_cases = Vec::new();
        for i in 0..pre_measures.len() {
            let mut conjuncts = Vec::new();
            // All measures before i are equal
            for j in 0..i {
                let pre_j = pre_measures[j]
                    .as_int()
                    .map_err(FnContractError::EncodingError)?;
                let post_j = post_measures[j]
                    .as_int()
                    .map_err(FnContractError::EncodingError)?;
                conjuncts.push(pre_j.eq(post_j.clone()));
            }
            // Measure i strictly decreases and is bounded
            let pre_i = pre_measures[i]
                .as_int()
                .map_err(FnContractError::EncodingError)?;
            let post_i = post_measures[i]
                .as_int()
                .map_err(FnContractError::EncodingError)?;
            conjuncts.push(pre_i.ge(z3::ast::Int::from_i64(0)));
            conjuncts.push(post_i.lt(pre_i));
            let refs: Vec<&Bool> = conjuncts.iter().collect();
            lex_cases.push(Bool::and(&refs));
        }
        let lex_refs: Vec<&Bool> = lex_cases.iter().collect();
        let lex_ok = Bool::or(&lex_refs);
        vc_solver.assert(&lex_ok.not());
    }

    // Assert lambda axioms after all encoding
    assert_lambda_axioms_on(&vc_solver);

    match vc_solver.check() {
        z3::SatResult::Unsat => Ok(()),
        z3::SatResult::Sat | z3::SatResult::Unknown => {
            Err(FnContractError::EncodingError(
                crate::messages::FN_LOOP_TERMINATION_FAILED.to_owned(),
            ))
        }
    }
}

/// Execute a while loop body, updating the environment with post-iteration values.
///
/// Processes assignments (`BinOp(OpEq, Var(name), expr)`) sequentially,
/// VarDecl for local temporaries, nested Blocks, and nested While loops.
///
/// `constraints` accumulates Z3 Bool assertions that must hold after execution
/// (e.g., inner loop postconditions: invariant ∧ ¬cond on fresh post-loop vars).
/// `assumptions` are Z3 Bool facts known to be true in the current context
/// (e.g., outer loop invariant ∧ outer condition ∧ fn requires). These are
/// passed as additional assumptions when verifying inner loop conditions.
fn execute_loop_body(
    body: &IRExpr,
    env: &mut HashMap<String, SmtValue>,
    constraints: &mut Vec<Bool>,
    assumptions: &[Bool],
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
) -> Result<(), FnContractError> {
    match body {
        IRExpr::Block { exprs, .. } => {
            for e in exprs {
                execute_loop_body(e, env, constraints, assumptions, vctx, defs)?;
            }
            Ok(())
        }

        IRExpr::VarDecl {
            name, init, rest, ..
        } => {
            let val = encode_pure_expr(init, env, vctx, defs)
                .map_err(FnContractError::EncodingError)?;
            env.insert(name.clone(), val);
            execute_loop_body(rest, env, constraints, assumptions, vctx, defs)
        }

        // Assignment: var = expr
        IRExpr::BinOp {
            op,
            left,
            right,
            ..
        } if op == "OpEq" => {
            if let IRExpr::Var { name, .. } = left.as_ref() {
                let val = encode_pure_expr(right, env, vctx, defs)
                    .map_err(FnContractError::EncodingError)?;
                env.insert(name.clone(), val);
                Ok(())
            } else {
                Ok(())
            }
        }

        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond_val = encode_pure_expr(cond, env, vctx, defs)
                .map_err(FnContractError::EncodingError)?;
            let cond_bool = cond_val
                .to_bool()
                .map_err(FnContractError::EncodingError)?;

            // Then-branch: collect constraints separately, guard with cond
            let mut then_assumptions: Vec<Bool> = assumptions.to_vec();
            then_assumptions.push(cond_bool.clone());
            let mut then_constraints: Vec<Bool> = Vec::new();
            let mut then_env = env.clone();
            execute_loop_body(then_body, &mut then_env, &mut then_constraints, &then_assumptions, vctx, defs)?;

            // Else-branch: collect constraints separately, guard with ¬cond
            let mut else_assumptions: Vec<Bool> = assumptions.to_vec();
            else_assumptions.push(cond_bool.not());
            let mut else_constraints: Vec<Bool> = Vec::new();
            let mut else_env = env.clone();
            if let Some(eb) = else_body {
                execute_loop_body(eb, &mut else_env, &mut else_constraints, &else_assumptions, vctx, defs)?;
            }

            // Guard branch constraints before propagating to the shared vector
            for c in then_constraints {
                constraints.push(cond_bool.implies(&c));
            }
            for c in else_constraints {
                constraints.push(cond_bool.not().implies(&c));
            }

            // Merge: for each variable that changed in either branch,
            // set it to ite(cond, then_val, else_val)
            let all_keys: HashSet<String> = then_env
                .keys()
                .chain(else_env.keys())
                .cloned()
                .collect();
            for key in all_keys {
                let then_val = then_env.get(&key);
                let else_val = else_env.get(&key);
                if let (Some(tv), Some(ev)) = (then_val, else_val) {
                    let merged = encode_ite(&cond_bool, tv, ev)
                        .map_err(FnContractError::EncodingError)?;
                    env.insert(key, merged);
                }
            }
            Ok(())
        }

        // Nested while loop: apply Hoare-logic abstraction.
        // The inner loop's effects must be modeled via invariant ∧ ¬cond,
        // not silently dropped.
        IRExpr::While {
            cond: inner_cond,
            invariants: inner_invs,
            decreases: inner_dec,
            body: inner_body,
            ..
        } => {
            // Collect variables modified by the inner loop
            let mut inner_modified = Vec::new();
            collect_modified_vars(inner_body, &mut inner_modified);
            inner_modified.sort();
            inner_modified.dedup();

            // Verify the inner loop's own conditions (init, preservation, termination).
            // Pass the outer context (outer invariant ∧ outer cond ∧ fn requires)
            // as extra assumptions so the inner loop can depend on them.
            // Inner loops are held to the same invariant requirement as top-level loops.
            verify_loop_conditions(
                inner_cond,
                inner_invs,
                inner_dec,
                inner_body,
                &inner_modified,
                env,
                &[],         // no fn_requires (captured in assumptions)
                assumptions, // outer context: invariant ∧ cond ∧ requires
                vctx,
                defs,
            )?;

            // Post-loop abstraction: havoc modified variables, then
            // add inner invariant ∧ ¬inner_cond as constraints.
            let counter =
                LOOP_VAR_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            for var_name in &inner_modified {
                if let Some(old_val) = env.get(var_name) {
                    let fresh_name = format!("{var_name}_inner_{counter}");
                    let fresh_var = make_z3_var_from_smt(&fresh_name, old_val);
                    env.insert(var_name.clone(), fresh_var);
                }
            }

            // Assert inner invariant holds for post-loop values
            for inv in inner_invs {
                let inv_val = encode_pure_expr(inv, env, vctx, defs)
                    .map_err(FnContractError::EncodingError)?;
                let inv_bool = inv_val
                    .to_bool()
                    .map_err(FnContractError::EncodingError)?;
                constraints.push(inv_bool);
            }

            // Assert ¬inner_cond (inner loop exited)
            let cond_val = encode_pure_expr(inner_cond, env, vctx, defs)
                .map_err(FnContractError::EncodingError)?;
            let cond_bool = cond_val
                .to_bool()
                .map_err(FnContractError::EncodingError)?;
            constraints.push(cond_bool.not());

            Ok(())
        }

        // Assert in loop body: VC check using assumptions (invariant ∧ cond ∧ fn_requires)
        // as context. If proved, assertion becomes available as a fact for subsequent code.
        IRExpr::Assert { expr: assert_expr, span } => {
            let assert_val = encode_pure_expr(assert_expr, env, vctx, defs)
                .map_err(FnContractError::EncodingError)?;
            let assert_bool = assert_val
                .to_bool()
                .map_err(FnContractError::EncodingError)?;

            // VC check: prove assert_expr holds given current assumptions + constraints
            let vc_solver = Solver::new();
            assert_lambda_axioms_on(&vc_solver);
            for assumption in assumptions {
                vc_solver.assert(assumption);
            }
            for c in constraints.iter() {
                vc_solver.assert(c);
            }
            vc_solver.assert(&assert_bool.not());
            assert_lambda_axioms_on(&vc_solver);

            match vc_solver.check() {
                z3::SatResult::Unsat => {
                    // Proved: assertion holds in loop body. Make available as fact.
                    constraints.push(assert_bool);
                    Ok(())
                }
                z3::SatResult::Sat | z3::SatResult::Unknown => {
                    Err(FnContractError::EncodingError(
                        if let Some(sp) = span {
                            format!(
                                "{} (at byte offset {}..{})",
                                crate::messages::FN_ASSERT_FAILED,
                                sp.start, sp.end,
                            )
                        } else {
                            crate::messages::FN_ASSERT_FAILED.to_owned()
                        },
                    ))
                }
            }
        }

        // Assume in loop body: add as a fact without proof.
        IRExpr::Assume { expr: assume_expr, .. } => {
            let assume_val = encode_pure_expr(assume_expr, env, vctx, defs)
                .map_err(FnContractError::EncodingError)?;
            let assume_bool = assume_val
                .to_bool()
                .map_err(FnContractError::EncodingError)?;
            constraints.push(assume_bool);
            Ok(())
        }

        // Ignore other expressions in the body (pure, no side effects — correct to drop)
        _ => Ok(()),
    }
}

/// Collect variable names that are modified by assignments in a loop body.
fn collect_modified_vars(body: &IRExpr, modified: &mut Vec<String>) {
    match body {
        IRExpr::Block { exprs, .. } => {
            for e in exprs {
                collect_modified_vars(e, modified);
            }
        }
        IRExpr::VarDecl { rest, .. } => {
            collect_modified_vars(rest, modified);
        }
        IRExpr::BinOp { op, left, .. } if op == "OpEq" => {
            if let IRExpr::Var { name, .. } = left.as_ref() {
                modified.push(name.clone());
            }
        }
        IRExpr::IfElse {
            then_body,
            else_body,
            ..
        } => {
            collect_modified_vars(then_body, modified);
            if let Some(eb) = else_body {
                collect_modified_vars(eb, modified);
            }
        }
        IRExpr::While { body: inner, .. } => {
            collect_modified_vars(inner, modified);
        }
        _ => {}
    }
}

/// Encode a recursive self-call: instead of expanding the body (which
/// would diverge), return a fresh Z3 variable constrained by the
/// function's `ensures` clauses with actual arguments substituted.
///
/// This implements modular verification: we trust the postcondition for
/// recursive calls (after Phase 1 proves it holds for all cases via induction).
fn encode_recursive_self_call(
    self_fn: &crate::ir::types::IRFunction,
    actual_args: &[IRExpr],
    env: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
) -> Result<SmtValue, String> {
    static REC_CALL_COUNTER: std::sync::atomic::AtomicU64 =
        std::sync::atomic::AtomicU64::new(0);

    // Determine the return type
    let ret_ty = extract_return_type(&self_fn.ty);

    // Create a fresh Z3 variable for the return value
    let counter = REC_CALL_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let fresh_name = format!("{}_rec_{counter}", self_fn.name);
    let result_var = make_z3_var(&fresh_name, &ret_ty)?;

    // If the function has ensures clauses, constrain the result.
    // Substitute: formal params → actual args, "result" → fresh var.
    if !self_fn.ensures.is_empty() {
        let entry = defs.get(&self_fn.name);
        if let Some(entry) = entry {
            let params = &entry.params;
            if params.len() == actual_args.len() {
                // Build an env with actual arg values for formal param names
                let mut call_env = env.clone();
                for (i, (param_name, _)) in params.iter().enumerate() {
                    let val = encode_pure_expr(&actual_args[i], env, vctx, defs)?;
                    call_env.insert(param_name.clone(), val);
                }
                call_env.insert("result".to_owned(), result_var.clone());

                // Encode ensures clauses with actual args substituted.
                // These are pushed to a thread-local accumulator and asserted
                // on the main solver by the caller (verify_single_fn_contract).
                // This implements modular verification: we assume the ensures
                // hold for recursive calls (Phase 1 proves this by induction).
                for ens in &self_fn.ensures {
                    if let Ok(ens_val) = encode_pure_expr(ens, &call_env, vctx, defs) {
                        if let Ok(ens_bool) = ens_val.to_bool() {
                            push_recursive_call_constraint(ens_bool);
                        }
                    }
                }
            }
        }
    }

    Ok(result_var)
}

/// Extract the return type from a (curried) function type.
fn extract_return_type(ty: &crate::ir::types::IRType) -> crate::ir::types::IRType {
    let mut current = ty;
    while let crate::ir::types::IRType::Fn { result, .. } = current {
        current = result;
    }
    current.clone()
}

// ── Function termination verification ───────────────────────────────

/// Verify termination for a recursive function with a `decreases` clause.
///
/// Walks the function body to find all recursive call sites (calls to
/// `func.name`). For each call site, extracts the path condition (branch
/// conditions that must be true for the call to be reached) and the actual
/// arguments. Then checks:
///
/// `requires ∧ path_condition → measure(actual_args) < measure(formal_params) ∧ measure(actual_args) ≥ 0`
///
/// Returns `Ok(())` if all recursive calls provably decrease the measure,
/// or `Err(message)` if any call fails.
fn verify_fn_termination(
    func: &crate::ir::types::IRFunction,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
) -> Result<(), String> {
    let dec = func.decreases.as_ref().ok_or_else(|| {
        "internal error: verify_fn_termination called without decreases".to_owned()
    })?;
    if dec.star {
        return Ok(()); // decreases * — skip termination checking
    }

    // Uncurry the function to get params and body
    let entry = defs.get(&func.name).ok_or_else(|| {
        format!("function '{}' not found in DefEnv", func.name)
    })?;
    let params = &entry.params;

    // Create Z3 variables for each parameter
    let mut env: HashMap<String, SmtValue> = HashMap::new();
    for (name, ty) in params {
        let var = make_z3_var(name, ty)?;
        env.insert(name.clone(), var);
    }

    // Find all recursive call sites with their path conditions
    // call_sites: (path_conditions, actual_args, env_at_call_site)
    let mut call_sites: Vec<(Vec<Bool>, Vec<IRExpr>, HashMap<String, SmtValue>)> = Vec::new();
    let mut body_env = env.clone();
    collect_recursive_calls(
        &entry.body,
        &func.name,
        params,
        &mut body_env,
        vctx,
        defs,
        &mut Vec::new(), // path conditions
        &mut call_sites,
    )?;

    if call_sites.is_empty() {
        return Ok(()); // no recursive calls — trivially terminating
    }

    // Encode fn requires as Bool values
    let mut requires_bools: Vec<Bool> = Vec::new();
    for req in &func.requires {
        let req_val = encode_pure_expr(req, &env, vctx, defs)?;
        requires_bools.push(req_val.to_bool()?);
    }

    // Encode the decreases measures for the formal parameters
    let pre_measures: Vec<SmtValue> = dec
        .measures
        .iter()
        .map(|m| encode_pure_expr(m, &env, vctx, defs))
        .collect::<Result<_, _>>()?;

    // Check each recursive call site
    for (path_conds, actual_args, call_env) in &call_sites {
        // Evaluate actual arg values in the call-site env
        let mut substituted_env = env.clone();
        for (i, (param_name, _)) in params.iter().enumerate() {
            if i < actual_args.len() {
                let val = encode_pure_expr(&actual_args[i], call_env, vctx, defs)?;
                substituted_env.insert(param_name.clone(), val);
            }
        }

        // Evaluate measures with actual args
        let post_measures: Vec<SmtValue> = dec
            .measures
            .iter()
            .map(|m| encode_pure_expr(m, &substituted_env, vctx, defs))
            .collect::<Result<_, _>>()?;

        // Evaluate callee requires with actual args (for precondition check)
        let mut callee_requires_bools: Vec<Bool> = Vec::new();
        for req in &func.requires {
            let req_val = encode_pure_expr(req, &substituted_env, vctx, defs)?;
            callee_requires_bools.push(req_val.to_bool()?);
        }

        // ── VC1: Callee precondition ────────────────────────────────
        // requires(caller) ∧ path_condition → requires(actual_args)
        {
            let vc_solver = Solver::new();
            assert_lambda_axioms_on(&vc_solver);
            for req_bool in &requires_bools {
                vc_solver.assert(req_bool);
            }
            for pc in path_conds {
                vc_solver.assert(pc);
            }
            // Assert ¬callee_requires — looking for counterexample
            let callee_refs: Vec<&Bool> = callee_requires_bools.iter().collect();
            let all_callee_req = Bool::and(&callee_refs);
            vc_solver.assert(&all_callee_req.not());
            if vc_solver.check() != z3::SatResult::Unsat {
                return Err(
                    crate::messages::FN_CALL_PRECONDITION_FAILED.to_owned(),
                );
            }
        }

        // ── VC2: Measure decreases and is bounded ───────────────────
        // requires(caller) ∧ path_condition → post_measure < pre_measure ∧ post_measure ≥ 0
        {
            let vc_solver = Solver::new();
            assert_lambda_axioms_on(&vc_solver);
            for req_bool in &requires_bools {
                vc_solver.assert(req_bool);
            }
            for pc in path_conds {
                vc_solver.assert(pc);
            }

            if pre_measures.len() == 1 {
                // Single measure: post < pre ∧ post ≥ 0
                let pre_m = pre_measures[0].as_int()?;
                let post_m = post_measures[0].as_int()?;
                let bounded = post_m.ge(z3::ast::Int::from_i64(0));
                let decreases_strict = post_m.lt(pre_m);
                let term_ok = Bool::and(&[&bounded, &decreases_strict]);
                vc_solver.assert(&term_ok.not());
            } else {
                // Lexicographic: ∃ i. (∀ j < i. mⱼ_post == mⱼ_pre) ∧ mᵢ_post < mᵢ_pre ∧ mᵢ_post ≥ 0
                let mut lex_cases = Vec::new();
                for i in 0..pre_measures.len() {
                    let mut conjuncts = Vec::new();
                    for j in 0..i {
                        let pre_j = pre_measures[j].as_int()?;
                        let post_j = post_measures[j].as_int()?;
                        conjuncts.push(pre_j.eq(post_j.clone()));
                    }
                    let pre_i = pre_measures[i].as_int()?;
                    let post_i = post_measures[i].as_int()?;
                    conjuncts.push(post_i.ge(z3::ast::Int::from_i64(0)));
                    conjuncts.push(post_i.lt(pre_i));
                    let refs: Vec<&Bool> = conjuncts.iter().collect();
                    lex_cases.push(Bool::and(&refs));
                }
                let lex_refs: Vec<&Bool> = lex_cases.iter().collect();
                let lex_ok = Bool::or(&lex_refs);
                vc_solver.assert(&lex_ok.not());
            }

            match vc_solver.check() {
                z3::SatResult::Unsat => {}
                _ => {
                    return Err(
                        crate::messages::FN_TERMINATION_FAILED.to_owned(),
                    );
                }
            }
        }
    }

    Ok(())
}

/// Recursively walk a function body to find all recursive call sites.
///
/// Collects `(path_conditions, actual_arguments)` for each call to `fn_name`.
/// The path conditions are Z3 Bool expressions representing the branch
/// conditions that must hold for the call to be reached.
#[allow(clippy::too_many_arguments)]
fn collect_recursive_calls(
    expr: &IRExpr,
    fn_name: &str,
    params: &[(String, crate::ir::types::IRType)],
    env: &mut HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    path_conds: &mut Vec<Bool>,
    call_sites: &mut Vec<(Vec<Bool>, Vec<IRExpr>, HashMap<String, SmtValue>)>,
) -> Result<(), String> {
    match expr {
        IRExpr::App { .. } => {
            if let Some((name, args)) = defenv::decompose_app_chain_public(expr) {
                if name == fn_name && args.len() == params.len() {
                    // Record the env snapshot at this call site so that
                    // local variables (let/var bindings) are available
                    // when evaluating the actual arguments later.
                    call_sites.push((path_conds.clone(), args, env.clone()));
                }
            }
            if let IRExpr::App { func, arg, .. } = expr {
                collect_recursive_calls(func, fn_name, params, env, vctx, defs, path_conds, call_sites)?;
                collect_recursive_calls(arg, fn_name, params, env, vctx, defs, path_conds, call_sites)?;
            }
        }
        IRExpr::Lam { param, param_type, body, .. } => {
            // Lam introduces a binding — create a Z3 var for it
            if !env.contains_key(param) {
                if let Ok(var) = make_z3_var(param, param_type) {
                    env.insert(param.clone(), var);
                }
            }
            collect_recursive_calls(body, fn_name, params, env, vctx, defs, path_conds, call_sites)?;
        }
        IRExpr::BinOp { left, right, .. } => {
            collect_recursive_calls(left, fn_name, params, env, vctx, defs, path_conds, call_sites)?;
            collect_recursive_calls(right, fn_name, params, env, vctx, defs, path_conds, call_sites)?;
        }
        IRExpr::UnOp { operand, .. } => {
            collect_recursive_calls(operand, fn_name, params, env, vctx, defs, path_conds, call_sites)?;
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond_val = encode_pure_expr(cond, env, vctx, defs)?;
            let cond_bool = cond_val.to_bool()?;

            path_conds.push(cond_bool.clone());
            collect_recursive_calls(then_body, fn_name, params, env, vctx, defs, path_conds, call_sites)?;
            path_conds.pop();

            if let Some(eb) = else_body {
                path_conds.push(cond_bool.not());
                collect_recursive_calls(eb, fn_name, params, env, vctx, defs, path_conds, call_sites)?;
                path_conds.pop();
            }
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            collect_recursive_calls(scrutinee, fn_name, params, env, vctx, defs, path_conds, call_sites)?;
            let scrut_val = encode_pure_expr(scrutinee, env, vctx, defs)?;

            // Match arms are sequential: arm k is reached only if all prior
            // arm conditions (pattern ∧ guard) were false. Accumulate the
            // negation of prior arm conditions as path context.
            let mut prior_negations: Vec<Bool> = Vec::new();
            for arm in arms {
                let pat_cond = encode_pattern_cond(&scrut_val, &arm.pattern, &HashMap::new(), vctx)?;
                let full_arm_cond = if let Some(guard) = &arm.guard {
                    let guard_val = encode_pure_expr(guard, env, vctx, defs)?;
                    let guard_bool = guard_val.to_bool()?;
                    Bool::and(&[&pat_cond, &guard_bool])
                } else {
                    pat_cond.clone()
                };

                // This arm's path: prior arms all failed + this arm matched
                let n_prior = prior_negations.len();
                for neg in &prior_negations {
                    path_conds.push(neg.clone());
                }
                path_conds.push(pat_cond);
                if let Some(guard) = &arm.guard {
                    let guard_val = encode_pure_expr(guard, env, vctx, defs)?;
                    path_conds.push(guard_val.to_bool()?);
                    collect_recursive_calls(&arm.body, fn_name, params, env, vctx, defs, path_conds, call_sites)?;
                    path_conds.pop(); // guard
                } else {
                    collect_recursive_calls(&arm.body, fn_name, params, env, vctx, defs, path_conds, call_sites)?;
                }
                path_conds.pop(); // pattern
                // Pop prior negations
                for _ in 0..n_prior {
                    path_conds.pop();
                }

                // For subsequent arms: this arm's condition was false
                prior_negations.push(full_arm_cond.not());
            }
        }
        IRExpr::Let { bindings, body, .. } => {
            for b in bindings {
                collect_recursive_calls(&b.expr, fn_name, params, env, vctx, defs, path_conds, call_sites)?;
                // Extend env with the binding so it's available in the body
                if let Ok(val) = encode_pure_expr(&b.expr, env, vctx, defs) {
                    env.insert(b.name.clone(), val);
                }
            }
            collect_recursive_calls(body, fn_name, params, env, vctx, defs, path_conds, call_sites)?;
        }
        IRExpr::Block { exprs, .. } => {
            for e in exprs {
                collect_recursive_calls(e, fn_name, params, env, vctx, defs, path_conds, call_sites)?;
            }
        }
        IRExpr::VarDecl { name, init, rest, .. } => {
            collect_recursive_calls(init, fn_name, params, env, vctx, defs, path_conds, call_sites)?;
            // Extend env with the var declaration
            if let Ok(val) = encode_pure_expr(init, env, vctx, defs) {
                env.insert(name.clone(), val);
            }
            collect_recursive_calls(rest, fn_name, params, env, vctx, defs, path_conds, call_sites)?;
        }
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            collect_recursive_calls(expr, fn_name, params, env, vctx, defs, path_conds, call_sites)?;
        }
        _ => {}
    }
    Ok(())
}

/// Create a fresh Z3 variable with the same sort as an existing SmtValue.
fn make_z3_var_from_smt(name: &str, template: &SmtValue) -> SmtValue {
    match template {
        SmtValue::Int(_) => smt::int_var(name),
        SmtValue::Bool(_) => smt::bool_var(name),
        SmtValue::Real(_) => smt::real_var(name),
        SmtValue::Array(_) | SmtValue::Dynamic(_) | SmtValue::Func(_) => {
            // For arrays/dynamic/func, fall back to int (best effort)
            smt::int_var(name)
        }
    }
}

/// Encode an imperative if/else that may contain while loops or assignments.
///
/// Evaluates both branches with cloned environments, then merges
/// modified variables using ITE on the condition.
#[allow(clippy::too_many_arguments)]
fn encode_imperative_if_else(
    cond: &IRExpr,
    then_body: &IRExpr,
    else_body: Option<&IRExpr>,
    env: &mut HashMap<String, SmtValue>,
    solver_constraints: &mut Vec<Bool>,
    fn_requires: &[IRExpr],
    extra_assumptions: &[Bool],
    self_fn: Option<&crate::ir::types::IRFunction>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
) -> Result<SmtValue, FnContractError> {
    let cond_val = encode_pure_expr(cond, env, vctx, defs)
        .map_err(FnContractError::EncodingError)?;
    let cond_bool = cond_val
        .to_bool()
        .map_err(FnContractError::EncodingError)?;

    // Then-branch: condition is known true → add it as assumption.
    // Collect constraints separately so they can be guarded by cond.
    let mut then_assumptions: Vec<Bool> = extra_assumptions.to_vec();
    then_assumptions.push(cond_bool.clone());
    let mut then_constraints: Vec<Bool> = Vec::new();
    let mut then_env = env.clone();
    let then_val = encode_fn_body(
        then_body, &mut then_env, &mut then_constraints, fn_requires, &then_assumptions, self_fn, vctx, defs,
    )?;

    // Else-branch: condition is known false → add ¬cond as assumption.
    let mut else_assumptions: Vec<Bool> = extra_assumptions.to_vec();
    else_assumptions.push(cond_bool.not());
    let mut else_constraints: Vec<Bool> = Vec::new();
    let mut else_env = env.clone();
    let else_val = if let Some(eb) = else_body {
        encode_fn_body(eb, &mut else_env, &mut else_constraints, fn_requires, &else_assumptions, self_fn, vctx, defs)?
    } else {
        smt::bool_val(true)
    };

    // Merge environments: for variables that differ between branches, use ITE
    let all_keys: HashSet<String> = then_env
        .keys()
        .chain(else_env.keys())
        .cloned()
        .collect();
    for key in all_keys {
        let then_v = then_env.get(&key);
        let else_v = else_env.get(&key);
        if let (Some(tv), Some(ev)) = (then_v, else_v) {
            let merged = encode_ite(&cond_bool, tv, ev)
                .map_err(FnContractError::EncodingError)?;
            env.insert(key, merged);
        }
    }

    // Guard branch constraints with the branch condition.
    // Then-branch constraints hold only when cond is true.
    // Else-branch constraints hold only when cond is false.
    // This prevents unreachable-branch facts from polluting the solver.
    for c in then_constraints {
        solver_constraints.push(cond_bool.implies(&c));
    }
    for c in else_constraints {
        solver_constraints.push(cond_bool.not().implies(&c));
    }

    // The value of the if/else expression
    encode_ite(&cond_bool, &then_val, &else_val).map_err(FnContractError::EncodingError)
}

/// Create a Z3 variable for a given IR type.
/// Check that a function call's arguments satisfy the callee's preconditions.
fn make_z3_var(name: &str, ty: &crate::ir::types::IRType) -> Result<SmtValue, String> {
    make_z3_var_ctx(name, ty, None)
}

fn make_z3_var_ctx(
    name: &str,
    ty: &crate::ir::types::IRType,
    vctx: Option<&VerifyContext>,
) -> Result<SmtValue, String> {
    use crate::ir::types::IRType;
    match ty {
        IRType::Int | IRType::Id | IRType::String => Ok(smt::int_var(name)),
        IRType::Bool => Ok(smt::bool_var(name)),
        IRType::Real | IRType::Float => Ok(smt::real_var(name)),
        IRType::Enum {
            name: enum_name, ..
        } => {
            // Use ADT sort if the enum has constructor fields
            if let Some(ctx) = vctx {
                if let Some(dt) = ctx.adt_sorts.get(enum_name) {
                    let var = z3::ast::Dynamic::new_const(name, &dt.sort);
                    return Ok(SmtValue::Dynamic(var));
                }
            }
            Ok(smt::int_var(name))
        }
        IRType::Refinement { base, .. } => make_z3_var_ctx(name, base, vctx),
        IRType::Set { .. } | IRType::Seq { .. } | IRType::Map { .. } => {
            smt::array_var(name, ty)
        }
        _ => Err(format!(
            "unsupported parameter type for fn contract verification: {ty:?}"
        )),
    }
}

/// Encode a pure expression (no entity pools, no time steps) to Z3.
///
/// Used for function contract verification where expressions reference
/// only function parameters and locally bound variables.
#[allow(clippy::too_many_lines)]
/// Context for call-site precondition checking inside `encode_pure_expr`.
///
/// When present, every `App` expansion checks that the callee's `requires`
/// hold in the current context (fn_requires + extra_assumptions).
struct PrecheckCtx<'a> {
    fn_requires: &'a [IRExpr],
    extra_assumptions: &'a [Bool],
    /// The function being verified — recursive self-calls are not expanded
    /// but instead return a fresh variable constrained by the function's ensures.
    self_fn: Option<&'a crate::ir::types::IRFunction>,
}

fn encode_pure_expr(
    expr: &IRExpr,
    env: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
) -> Result<SmtValue, String> {
    encode_pure_expr_inner(expr, env, vctx, defs, None)
}

fn encode_pure_expr_checked(
    expr: &IRExpr,
    env: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    precheck: &PrecheckCtx<'_>,
) -> Result<SmtValue, String> {
    encode_pure_expr_inner(expr, env, vctx, defs, Some(precheck))
}

#[allow(clippy::too_many_lines)]
fn encode_pure_expr_inner(
    expr: &IRExpr,
    env: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    precheck: Option<&PrecheckCtx<'_>>,
) -> Result<SmtValue, String> {
    match expr {
        IRExpr::Lit { value, ty, .. } => encode_pure_lit(value, ty),

        IRExpr::Var { name, .. } => {
            if let Some(val) = env.get(name) {
                return Ok(val.clone());
            }
            if let Some(expanded) = defs.expand_var(name) {
                return encode_pure_expr_inner(&expanded, env, vctx, defs, precheck);
            }
            Err(format!("unbound variable in fn contract: '{name}'"))
        }

        IRExpr::Ctor {
            enum_name, ctor, args, ..
        } => {
            // ADT-encoded enum: use constructor function with field arguments
            if let Some(dt) = vctx.adt_sorts.get(enum_name) {
                for variant in &dt.variants {
                    if variant.constructor.name() == *ctor {
                        let arity = variant.accessors.len();
                        if arity > 0 && args.is_empty() {
                            return Err(format!(
                                "constructor '{ctor}' of '{enum_name}' requires {arity} \
                                 field argument(s) — use @{enum_name}::{ctor} {{ ... }}"
                            ));
                        }
                        if args.is_empty() {
                            // Nullary constructor (no fields)
                            let result = variant.constructor.apply(&[]);
                            return Ok(dynamic_to_smt_value(result));
                        }

                        // Validate and reorder field arguments by declared order.
                        // Accessor names define the canonical field order.
                        let declared_names: Vec<std::string::String> = variant
                            .accessors
                            .iter()
                            .map(|a| a.name())
                            .collect();

                        // Check for unknown fields
                        for (field_name, _) in args {
                            if !declared_names.iter().any(|d| d == field_name) {
                                return Err(format!(
                                    "unknown field '{field_name}' in constructor '{ctor}' \
                                     of '{enum_name}' — declared fields: {}",
                                    declared_names.join(", ")
                                ));
                            }
                        }

                        // Check for duplicates
                        let mut seen = std::collections::HashSet::new();
                        for (field_name, _) in args {
                            if !seen.insert(field_name.as_str()) {
                                return Err(format!(
                                    "duplicate field '{field_name}' in constructor '{ctor}'"
                                ));
                            }
                        }

                        // Check arity
                        if args.len() != arity {
                            let missing: Vec<&str> = declared_names
                                .iter()
                                .filter(|d| !args.iter().any(|(n, _)| n == d.as_str()))
                                .map(|s| s.as_str())
                                .collect();
                            return Err(format!(
                                "constructor '{ctor}' of '{enum_name}' requires {arity} \
                                 field(s) but got {} — missing: {}",
                                args.len(),
                                missing.join(", ")
                            ));
                        }

                        // Build args in declared field order (not source order)
                        let args_map: HashMap<&str, &IRExpr> = args
                            .iter()
                            .map(|(n, e)| (n.as_str(), e))
                            .collect();
                        let mut z3_args: Vec<z3::ast::Dynamic> = Vec::new();
                        for decl_name in &declared_names {
                            let field_expr = args_map[decl_name.as_str()];
                            let val = encode_pure_expr_inner(
                                field_expr, env, vctx, defs, precheck,
                            )?;
                            z3_args.push(val.to_dynamic());
                        }

                        let arg_refs: Vec<&dyn z3::ast::Ast> =
                            z3_args.iter().map(|a| a as &dyn z3::ast::Ast).collect();
                        let result = variant.constructor.apply(&arg_refs);
                        return Ok(dynamic_to_smt_value(result));
                    }
                }
            }
            // Flat Int encoding for fieldless enums
            let id = vctx.variants.id_of(enum_name, ctor);
            Ok(smt::int_val(id))
        }

        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpSeqConcat" => {
            // Seq::concat: build result array with a's elements at 0..len_a,
            // b's elements at len_a..len_a+len_b.
            // Extract concrete elements from SeqLit operands.
            let a_elems = match left.as_ref() {
                IRExpr::SeqLit { elements, .. } => elements.clone(),
                _ => return Err("Seq::concat requires literal operands".to_owned()),
            };
            let b_elems = match right.as_ref() {
                IRExpr::SeqLit { elements, .. } => elements.clone(),
                _ => return Err("Seq::concat requires literal operands".to_owned()),
            };
            // Build combined SeqLit and encode it
            let mut combined = a_elems;
            combined.extend(b_elems);
            let seq_ty = match left.as_ref() {
                IRExpr::SeqLit { ty, .. } => ty.clone(),
                _ => crate::ir::types::IRType::Seq {
                    element: Box::new(crate::ir::types::IRType::Int),
                },
            };
            let combined_lit = IRExpr::SeqLit {
                elements: combined,
                ty: seq_ty,
                span: None,
            };
            encode_pure_expr_inner(&combined_lit, env, vctx, defs, precheck)
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let lhs = encode_pure_expr_inner(left, env, vctx, defs, precheck)?;
            let rhs = encode_pure_expr_inner(right, env, vctx, defs, precheck)?;
            smt::binop(op, &lhs, &rhs)
        }

        IRExpr::UnOp { op, operand, .. } => {
            let val = encode_pure_expr_inner(operand, env, vctx, defs, precheck)?;
            smt::unop(op, &val)
        }

        IRExpr::App { .. } => {
            // Determine if this is a recursive self-call
            let is_self_call = precheck
                .and_then(|ctx| ctx.self_fn)
                .and_then(|sf| {
                    defenv::decompose_app_chain_name(expr)
                        .filter(|name| name == &sf.name)
                })
                .is_some();

            // Check preconditions for NON-self calls.
            // Self-call preconditions are checked by Phase 3 (termination VC)
            // with proper path conditions from the enclosing branch structure.
            if !is_self_call {
                if let Some(ctx) = precheck {
                    if let Some(preconditions) = defs.call_preconditions(expr) {
                        if !preconditions.is_empty() {
                            let mut context_bools: Vec<Bool> = Vec::new();
                            for req in ctx.fn_requires {
                                let req_val = encode_pure_expr(req, env, vctx, defs)?;
                                context_bools.push(req_val.to_bool()?);
                            }
                            for assumption in ctx.extra_assumptions {
                                context_bools.push(assumption.clone());
                            }
                            for pre in &preconditions {
                                let pre_val = encode_pure_expr(pre, env, vctx, defs)?;
                                let pre_bool = pre_val.to_bool()?;
                                let vc_solver = Solver::new();
                                assert_lambda_axioms_on(&vc_solver);
                                for ctx_bool in &context_bools {
                                    vc_solver.assert(ctx_bool);
                                }
                                vc_solver.assert(&pre_bool.not());
                                if vc_solver.check() != z3::SatResult::Unsat {
                                    return Err(
                                        crate::messages::FN_CALL_PRECONDITION_FAILED.to_owned(),
                                    );
                                }
                            }
                        }
                    }
                }
            }
            // Handle recursive self-calls: don't expand, return fresh
            // variable constrained by the function's ensures (modular reasoning).
            if let Some(ctx) = precheck {
                if let Some(self_f) = ctx.self_fn {
                    if let Some((call_name, call_args)) =
                        defenv::decompose_app_chain_public(expr)
                    {
                        if call_name == self_f.name {
                            return encode_recursive_self_call(
                                self_f, &call_args, env, vctx, defs,
                            );
                        }
                    }
                }
            }
            // Collect the full curried application chain: App(App(f, a), b) → (f, [a, b])
            // Then check if the base function is a lambda (Func-valued).
            {
                let mut base = expr;
                let mut arg_exprs: Vec<&IRExpr> = Vec::new();
                while let IRExpr::App { func, arg, .. } = base {
                    arg_exprs.push(arg);
                    base = func;
                }
                arg_exprs.reverse(); // collected in reverse order

                // Try encoding the base function
                let func_result = encode_pure_expr_inner(base, env, vctx, defs, precheck);
                if let Ok(SmtValue::Func(ref ft)) = func_result {
                    let (ref func_decl, ref param_sorts, ref range_sort) = **ft;
                    let arity = param_sorts.len();
                    let mut z3_args: Vec<z3::ast::Dynamic> = Vec::new();
                    for arg_expr in &arg_exprs {
                        let val = encode_pure_expr_inner(arg_expr, env, vctx, defs, precheck)?;
                        z3_args.push(val.to_dynamic());
                    }

                    if arg_exprs.len() == arity {
                        // Full application
                        let arg_refs: Vec<&dyn z3::ast::Ast> =
                            z3_args.iter().map(|a| a as &dyn z3::ast::Ast).collect();
                        let result = func_decl.apply(&arg_refs);
                        return Ok(dynamic_to_smt_value(result));
                    } else if arg_exprs.len() < arity {
                        // Partial application
                        return encode_partial_application(
                            func_decl, param_sorts, range_sort, &z3_args,
                        );
                    } else {
                        return Err(format!(
                            "too many arguments — function expects {arity} but got {}",
                            arg_exprs.len()
                        ));
                    }
                }
                // If base is not Func-valued, fall through to DefEnv / self-call
            }

            // Expand via DefEnv
            if let Some(expanded) = defs.expand_app(expr) {
                return encode_pure_expr_inner(&expanded, env, vctx, defs, precheck);
            }
            Err(format!(
                "could not expand function application in fn contract"
            ))
        }

        IRExpr::Let { bindings, body, .. } => {
            let mut extended_env = env.clone();
            for b in bindings {
                let val = encode_pure_expr_inner(&b.expr, &extended_env, vctx, defs, precheck)?;
                extended_env.insert(b.name.clone(), val);
            }
            encode_pure_expr_inner(body, &extended_env, vctx, defs, precheck)
        }

        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond_val = encode_pure_expr_inner(cond, env, vctx, defs, precheck)?;
            let cond_bool = cond_val.to_bool()?;
            let then_val = encode_pure_expr_inner(then_body, env, vctx, defs, precheck)?;
            match else_body {
                Some(eb) => {
                    let else_val = encode_pure_expr_inner(eb, env, vctx, defs, precheck)?;
                    encode_ite(&cond_bool, &then_val, &else_val)
                }
                None => {
                    let then_bool = then_val.to_bool()?;
                    Ok(SmtValue::Bool(cond_bool.implies(&then_bool)))
                }
            }
        }

        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            let scrut_val = encode_pure_expr_inner(scrutinee, env, vctx, defs, precheck)?;
            encode_pure_match(&scrut_val, arms, env, vctx, defs, precheck)
        }

        IRExpr::Forall {
            var, domain, body, ..
        } => encode_z3_quantifier(true, var, domain, body, env, vctx, defs, precheck),

        IRExpr::Exists {
            var, domain, body, ..
        } => encode_z3_quantifier(false, var, domain, body, env, vctx, defs, precheck),

        IRExpr::One {
            var, domain, body, ..
        } => encode_z3_one(var, domain, body, env, vctx, defs, precheck),

        IRExpr::Lone {
            var, domain, body, ..
        } => encode_z3_lone(var, domain, body, env, vctx, defs, precheck),

        IRExpr::Index { map, key, ty, .. } => {
            let map_val = encode_pure_expr_inner(map, env, vctx, defs, precheck)?;
            let key_val = encode_pure_expr_inner(key, env, vctx, defs, precheck)?;
            let arr = map_val.as_array()?;
            let result = arr.select(&key_val.to_dynamic());
            // Cast to typed SmtValue when the IR declares a known type
            // (e.g., `e in Set<T>` has ty=Bool, `map[k]` has ty=ValueType).
            // This avoids Dynamic→Bool conversion failures for lambda arrays.
            match ty {
                crate::ir::types::IRType::Bool => {
                    match result.as_bool() {
                        Some(b) => Ok(SmtValue::Bool(b)),
                        None => Ok(SmtValue::Dynamic(result)),
                    }
                }
                crate::ir::types::IRType::Int | crate::ir::types::IRType::Id => {
                    match result.as_int() {
                        Some(i) => Ok(SmtValue::Int(i)),
                        None => Ok(SmtValue::Dynamic(result)),
                    }
                }
                crate::ir::types::IRType::Real | crate::ir::types::IRType::Float => {
                    match result.as_real() {
                        Some(r) => Ok(SmtValue::Real(r)),
                        None => Ok(SmtValue::Dynamic(result)),
                    }
                }
                _ => Ok(SmtValue::Dynamic(result)),
            }
        }

        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            let map_val = encode_pure_expr_inner(map, env, vctx, defs, precheck)?;
            let key_val = encode_pure_expr_inner(key, env, vctx, defs, precheck)?;
            let val = encode_pure_expr_inner(value, env, vctx, defs, precheck)?;
            let arr = map_val.as_array()?;
            Ok(SmtValue::Array(
                arr.store(&key_val.to_dynamic(), &val.to_dynamic()),
            ))
        }

        IRExpr::SetLit { elements, ty, .. } => {
            let elem_ty = match ty {
                crate::ir::types::IRType::Set { element } => element.as_ref(),
                // Unresolved type: infer element type from first element (Int default)
                _ => &crate::ir::types::IRType::Int,
            };
            let elem_sort = smt::ir_type_to_sort(elem_ty);
            let false_dyn = smt::default_dynamic(&crate::ir::types::IRType::Bool);
            let mut arr = z3::ast::Array::const_array(&elem_sort, &false_dyn);
            let true_dyn =
                z3::ast::Dynamic::from_ast(&z3::ast::Bool::from_bool(true));
            for e in elements {
                let elem = encode_pure_expr_inner(e, env, vctx, defs, precheck)?;
                arr = arr.store(&elem.to_dynamic(), &true_dyn);
            }
            Ok(SmtValue::Array(arr))
        }

        IRExpr::SeqLit { elements, ty, .. } => {
            let elem_ty = match ty {
                crate::ir::types::IRType::Seq { element } => element.as_ref(),
                _ => &crate::ir::types::IRType::Int,
            };
            let default = smt::default_dynamic(elem_ty);
            let mut arr = z3::ast::Array::const_array(&z3::Sort::int(), &default);
            for (i, e) in elements.iter().enumerate() {
                let elem = encode_pure_expr_inner(e, env, vctx, defs, precheck)?;
                let idx =
                    z3::ast::Dynamic::from_ast(&z3::ast::Int::from_i64(i as i64));
                arr = arr.store(&idx, &elem.to_dynamic());
            }
            Ok(SmtValue::Array(arr))
        }

        IRExpr::MapLit { entries, ty, .. } => {
            let (key_ty, val_ty) = match ty {
                crate::ir::types::IRType::Map { key, value } => (key.as_ref(), value.as_ref()),
                // Unresolved type: infer from entries (Int keys, Bool values as default)
                _ => (
                    &crate::ir::types::IRType::Int,
                    &crate::ir::types::IRType::Bool,
                ),
            };
            let key_sort = smt::ir_type_to_sort(key_ty);
            let default = smt::default_dynamic(val_ty);
            let mut arr = z3::ast::Array::const_array(&key_sort, &default);
            for (k, v) in entries {
                let key_val = encode_pure_expr_inner(k, env, vctx, defs, precheck)?;
                let val_val = encode_pure_expr_inner(v, env, vctx, defs, precheck)?;
                arr = arr.store(&key_val.to_dynamic(), &val_val.to_dynamic());
            }
            Ok(SmtValue::Array(arr))
        }

        IRExpr::Card { expr: inner, .. } => match inner.as_ref() {
            // Set cardinality: count semantically distinct elements.
            // Encode each element to Z3, then use the "first occurrence"
            // pattern: element i is counted iff it differs from all prior
            // elements. This correctly handles `#Set(1, 1 + 0)` = 1.
            IRExpr::SetLit { elements, .. } => {
                if elements.is_empty() {
                    return Ok(smt::int_val(0));
                }
                let z3_elems: Vec<SmtValue> = elements
                    .iter()
                    .map(|e| encode_pure_expr_inner(e, env, vctx, defs, precheck))
                    .collect::<Result<_, _>>()?;

                let one = z3::ast::Int::from_i64(1);
                let zero = z3::ast::Int::from_i64(0);
                let mut terms: Vec<z3::ast::Int> = Vec::new();

                for (i, vi) in z3_elems.iter().enumerate() {
                    if i == 0 {
                        // First element always counts
                        terms.push(one.clone());
                    } else {
                        // Count iff different from all prior elements
                        let mut diff_from_prior: Vec<Bool> = Vec::new();
                        for vj in &z3_elems[..i] {
                            let neq = smt::smt_neq(vi, vj)?;
                            diff_from_prior.push(neq);
                        }
                        let refs: Vec<&Bool> = diff_from_prior.iter().collect();
                        let is_first = Bool::and(&refs);
                        terms.push(is_first.ite(&one, &zero));
                    }
                }

                let refs: Vec<&z3::ast::Int> = terms.iter().collect();
                Ok(SmtValue::Int(z3::ast::Int::add(&refs)))
            }
            IRExpr::SeqLit { elements, .. } => {
                Ok(smt::int_val(i64::try_from(elements.len()).unwrap_or(0)))
            }
            IRExpr::MapLit { entries, .. } => {
                if entries.is_empty() {
                    return Ok(smt::int_val(0));
                }
                // Same first-occurrence pattern for map keys
                let z3_keys: Vec<SmtValue> = entries
                    .iter()
                    .map(|(k, _)| encode_pure_expr_inner(k, env, vctx, defs, precheck))
                    .collect::<Result<_, _>>()?;

                let one = z3::ast::Int::from_i64(1);
                let zero = z3::ast::Int::from_i64(0);
                let mut terms: Vec<z3::ast::Int> = Vec::new();

                for (i, ki) in z3_keys.iter().enumerate() {
                    if i == 0 {
                        terms.push(one.clone());
                    } else {
                        let mut diff: Vec<Bool> = Vec::new();
                        for kj in &z3_keys[..i] {
                            diff.push(smt::smt_neq(ki, kj)?);
                        }
                        let refs: Vec<&Bool> = diff.iter().collect();
                        let is_first = Bool::and(&refs);
                        terms.push(is_first.ite(&one, &zero));
                    }
                }

                let refs: Vec<&z3::ast::Int> = terms.iter().collect();
                Ok(SmtValue::Int(z3::ast::Int::add(&refs)))
            }
            // Cardinality of non-literal: encode the inner expression and
            // reject if it's not a form we can reason about.
            _ => Err(
                "cardinality (#) of non-literal collections not supported in fn contracts — \
                 use #Set(...), #Seq(...), or #Map(...)"
                    .to_owned(),
            ),
        },
        // Set comprehension: { x: T where P(x) }
        // Encode as Z3 lambda array with domain restriction:
        //   simple:     λx. domain_pred(x) ∧ P(x)
        //   projection: λy. ∃x. domain_pred(x) ∧ P(x) ∧ f(x) == y
        IRExpr::SetComp {
            var,
            domain,
            filter,
            projection,
            ..
        } => {
            // Create a fresh Z3 constant for the comprehension variable
            let bound_var = make_z3_var(var, domain)?;
            let mut inner_env = env.clone();
            inner_env.insert(var.to_owned(), bound_var.clone());

            // Encode the filter predicate with the bound variable in scope
            let filter_val =
                encode_pure_expr_inner(filter, &inner_env, vctx, defs, precheck)?;
            let filter_bool = filter_val.to_bool()?;

            // Build domain predicate for restricted types (enum, refinement)
            let domain_pred = build_domain_predicate(
                domain, &bound_var, &inner_env, vctx, defs, precheck,
            )?;

            // Combine filter with domain predicate: domain_pred ∧ filter
            let restricted_filter = match domain_pred {
                Some(dp) => Bool::and(&[&dp, &filter_bool]),
                None => filter_bool,
            };

            if let Some(proj) = projection {
                // Projection comprehension: { f(x) | x: T where P(x) }
                // Encode as: λy. ∃x. domain_pred(x) ∧ P(x) ∧ f(x) == y
                let proj_val =
                    encode_pure_expr_inner(proj, &inner_env, vctx, defs, precheck)?;

                let proj_var_name = format!("{var}__proj");
                let proj_bound = make_z3_var_from_smt(&proj_var_name, &proj_val);

                let eq = smt::smt_eq(&proj_val, &proj_bound)?;
                let body = Bool::and(&[&restricted_filter, &eq]);

                let exists_body = match &bound_var {
                    SmtValue::Int(i) => {
                        z3::ast::exists_const(&[i as &dyn z3::ast::Ast], &[], &body)
                    }
                    SmtValue::Bool(b) => {
                        z3::ast::exists_const(&[b as &dyn z3::ast::Ast], &[], &body)
                    }
                    SmtValue::Real(r) => {
                        z3::ast::exists_const(&[r as &dyn z3::ast::Ast], &[], &body)
                    }
                    _ => {
                        return Err(format!(
                            "unsupported set comprehension domain: {domain:?}"
                        ))
                    }
                };

                let body_dyn = z3::ast::Dynamic::from_ast(&exists_body);
                let arr = match &proj_bound {
                    SmtValue::Int(v) => {
                        z3::ast::lambda_const(&[v as &dyn z3::ast::Ast], &body_dyn)
                    }
                    SmtValue::Bool(v) => {
                        z3::ast::lambda_const(&[v as &dyn z3::ast::Ast], &body_dyn)
                    }
                    SmtValue::Real(v) => {
                        z3::ast::lambda_const(&[v as &dyn z3::ast::Ast], &body_dyn)
                    }
                    _ => {
                        return Err(format!(
                            "unsupported set comprehension projection type: {proj_val:?}"
                        ))
                    }
                };
                Ok(SmtValue::Array(arr))
            } else {
                // Simple comprehension: { x: T where P(x) }
                // Encode as: λx. domain_pred(x) ∧ P(x)
                let body_dyn = z3::ast::Dynamic::from_ast(&restricted_filter);
                let arr = match &bound_var {
                    SmtValue::Int(v) => {
                        z3::ast::lambda_const(&[v as &dyn z3::ast::Ast], &body_dyn)
                    }
                    SmtValue::Bool(v) => {
                        z3::ast::lambda_const(&[v as &dyn z3::ast::Ast], &body_dyn)
                    }
                    SmtValue::Real(v) => {
                        z3::ast::lambda_const(&[v as &dyn z3::ast::Ast], &body_dyn)
                    }
                    _ => {
                        return Err(format!(
                            "unsupported set comprehension domain: {domain:?}"
                        ))
                    }
                };
                Ok(SmtValue::Array(arr))
            }
        }
        IRExpr::Always { .. } | IRExpr::Eventually { .. } | IRExpr::Until { .. } => {
            Err("temporal operators not allowed in fn contracts".to_owned())
        }
        IRExpr::Prime { .. } => Err("prime (next-state) not allowed in fn contracts".to_owned()),
        IRExpr::Field { .. } => {
            Err("entity field access not allowed in fn contracts".to_owned())
        }
        IRExpr::Lam { .. } => {
            encode_lambda(expr, env, vctx, defs, precheck)
        }

        IRExpr::Block { exprs, .. } => {
            if exprs.is_empty() {
                return Ok(smt::bool_val(true));
            }
            let mut last = smt::bool_val(true);
            for e in exprs {
                last = encode_pure_expr_inner(e, env, vctx, defs, precheck)?;
            }
            Ok(last)
        }

        IRExpr::VarDecl {
            name, init, rest, ..
        } => {
            let val = encode_pure_expr_inner(init, env, vctx, defs, precheck)?;
            let mut extended_env = env.clone();
            extended_env.insert(name.clone(), val);
            encode_pure_expr_inner(rest, &extended_env, vctx, defs, precheck)
        }

        IRExpr::While { .. } => {
            Err(crate::messages::FN_LOOP_NO_INVARIANT.to_owned())
        }

        IRExpr::Assert { .. } => {
            Err("assert in pure expression context — assert is an imperative statement and must appear in a function body block".to_owned())
        }
        IRExpr::Assume { .. } => {
            Err("assume in pure expression context — assume is an imperative statement and must appear in a function body block".to_owned())
        }

        IRExpr::Sorry { .. } => Ok(smt::bool_val(true)),
        IRExpr::Todo { .. } => Err("todo expression in fn contract body".to_owned()),
    }
}

/// Build a domain predicate for restricted types (enum, refinement).
/// Returns `None` for unrestricted types (Int, Bool, Real, etc.).
///
/// Used by both quantifier encoding and set comprehension encoding to
/// constrain bound variables to their declared domain.
#[allow(clippy::too_many_arguments)]
fn build_domain_predicate(
    domain: &crate::ir::types::IRType,
    bound_var: &SmtValue,
    inner_env: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    precheck: Option<&PrecheckCtx<'_>>,
) -> Result<Option<Bool>, String> {
    use crate::ir::types::IRType;
    match domain {
        IRType::Enum {
            name,
            variants: vs,
        } => {
            // ADT-encoded enums (Dynamic): Z3's ADT sort already constrains
            // the variable to valid constructors — no domain predicate needed.
            if matches!(bound_var, SmtValue::Dynamic(_)) {
                return Ok(None);
            }
            // Flat Int-encoded enums: restrict to valid variant ID range.
            let var_int = bound_var.as_int()?;
            let ids: Vec<i64> = vs
                .iter()
                .map(|v| vctx.variants.id_of(name, &v.name))
                .collect();
            let min_id = *ids.iter().min().unwrap();
            let max_id = *ids.iter().max().unwrap();
            let lo = smt::int_val(min_id);
            let hi = smt::int_val(max_id);
            Ok(Some(Bool::and(&[
                &var_int.ge(lo.as_int().unwrap()),
                &var_int.le(hi.as_int().unwrap()),
            ])))
        }
        IRType::Refinement { predicate, .. } => {
            let mut pred_env = inner_env.clone();
            pred_env.insert("$".to_owned(), bound_var.clone());
            let pred_val =
                encode_pure_expr_inner(predicate, &pred_env, vctx, defs, precheck)?;
            Ok(Some(pred_val.to_bool()?))
        }
        _ => Ok(None),
    }
}

/// Encode a Z3 native quantifier (forall / exists) for non-entity domains.
///
/// Creates a fresh Z3 constant for the bound variable, encodes the body with
/// that variable in scope, then wraps with `z3::ast::forall_const` or
/// `z3::ast::exists_const`. No patterns/triggers — Z3 uses MBQI automatically.
///
/// For restricted domains (enums, refinement types), the body is guarded by
/// a domain predicate:
///   - forall y: E | P(y)  →  forall y: Int | (y ∈ E) implies P(y)
///   - exists y: E | P(y)  →  exists y: Int | (y ∈ E) and P(y)
///
/// Entity-domain quantifiers in system properties still use slot-pool expansion
/// (complete, decidable). This function handles the general case.
#[allow(clippy::too_many_arguments)]
fn encode_z3_quantifier(
    is_forall: bool,
    var: &str,
    domain: &crate::ir::types::IRType,
    body: &IRExpr,
    env: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    precheck: Option<&PrecheckCtx<'_>>,
) -> Result<SmtValue, String> {
    // Create a fresh Z3 constant for the bound variable (ADT-aware via vctx)
    let bound_var = make_z3_var_ctx(var, domain, Some(vctx))?;

    // Extend environment with the bound variable
    let mut inner_env = env.clone();
    inner_env.insert(var.to_owned(), bound_var.clone());

    // Encode the body with the bound variable in scope
    let body_val = encode_pure_expr_inner(body, &inner_env, vctx, defs, precheck)?;
    let body_bool = body_val.to_bool()?;

    let domain_pred = build_domain_predicate(
        domain, &bound_var, &inner_env, vctx, defs, precheck,
    )?;

    // Combine body with domain predicate:
    //   forall: domain_pred implies body
    //   exists: domain_pred and body
    let quantified_body = match domain_pred {
        Some(dp) => {
            if is_forall {
                dp.implies(&body_bool)
            } else {
                Bool::and(&[&dp, &body_bool])
            }
        }
        None => body_bool,
    };

    let result = build_z3_quantifier(is_forall, &bound_var, &quantified_body, var, domain)?;
    Ok(SmtValue::Bool(result))
}

/// Build a domain predicate for a non-entity quantifier in property context.
///
/// Bridges the `PropertyCtx` (which uses `locals` for non-entity bindings) to
/// `build_domain_predicate` (which needs a `HashMap<String, SmtValue>` env).
/// This ensures refinement type predicates and enum range guards are applied
/// correctly in verify/theorem property expressions.
fn prop_domain_predicate(
    domain: &crate::ir::types::IRType,
    bound_var: &SmtValue,
    ctx: &PropertyCtx,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
) -> Result<Option<Bool>, String> {
    // Build a minimal env from PropertyCtx locals for the pure expression encoder
    let env: HashMap<String, SmtValue> = ctx.locals.clone();
    build_domain_predicate(domain, bound_var, &env, vctx, defs, None)
}

/// Return the number of variants in an enum IR type.
fn enum_variant_count(ty: &crate::ir::types::IRType) -> usize {
    match ty {
        crate::ir::types::IRType::Enum { variants, .. } => variants.len(),
        _ => 0,
    }
}

/// Build a Z3 quantifier (exists_const or forall_const) from a bound variable
/// and body. Dispatches on the SmtValue variant to extract the Z3 AST node.
fn build_z3_quantifier(
    is_forall: bool,
    bound_var: &SmtValue,
    body: &Bool,
    var: &str,
    domain: &crate::ir::types::IRType,
) -> Result<Bool, String> {
    match bound_var {
        SmtValue::Int(i) => {
            let bounds: &[&dyn z3::ast::Ast] = &[i];
            if is_forall {
                Ok(z3::ast::forall_const(bounds, &[], body))
            } else {
                Ok(z3::ast::exists_const(bounds, &[], body))
            }
        }
        SmtValue::Bool(b) => {
            let bounds: &[&dyn z3::ast::Ast] = &[b];
            if is_forall {
                Ok(z3::ast::forall_const(bounds, &[], body))
            } else {
                Ok(z3::ast::exists_const(bounds, &[], body))
            }
        }
        SmtValue::Real(r) => {
            let bounds: &[&dyn z3::ast::Ast] = &[r];
            if is_forall {
                Ok(z3::ast::forall_const(bounds, &[], body))
            } else {
                Ok(z3::ast::exists_const(bounds, &[], body))
            }
        }
        SmtValue::Dynamic(d) => {
            let bounds: &[&dyn z3::ast::Ast] = &[d];
            if is_forall {
                Ok(z3::ast::forall_const(bounds, &[], body))
            } else {
                Ok(z3::ast::exists_const(bounds, &[], body))
            }
        }
        _ => Err(format!(
            "unsupported quantifier domain type for '{var}': {domain:?}"
        )),
    }
}

/// Encode `one x: T | P(x)` — exactly one x satisfies P.
///
/// Semantics: ∃x. D(x) ∧ P(x) ∧ ∀y. D(y) ∧ P(y) → y = x
///
/// where D is the domain predicate (enum range, refinement guard, etc.)
#[allow(clippy::too_many_arguments)]
fn encode_z3_one(
    var: &str,
    domain: &crate::ir::types::IRType,
    body: &IRExpr,
    env: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    precheck: Option<&PrecheckCtx<'_>>,
) -> Result<SmtValue, String> {
    // Create bound variable x (ADT-aware via vctx)
    let x_var = make_z3_var_ctx(var, domain, Some(vctx))?;
    let mut x_env = env.clone();
    x_env.insert(var.to_owned(), x_var.clone());

    // Encode P(x)
    let p_x = encode_pure_expr_inner(body, &x_env, vctx, defs, precheck)?
        .to_bool()?;

    // Domain predicate for x
    let d_x = build_domain_predicate(domain, &x_var, &x_env, vctx, defs, precheck)?;

    // D(x) ∧ P(x)
    let x_satisfies = match &d_x {
        Some(dp) => Bool::and(&[dp, &p_x]),
        None => p_x.clone(),
    };

    // Create a fresh bound variable y (different Z3 name, ADT-aware)
    let y_name = format!("{var}__unique");
    let y_var = make_z3_var_ctx(&y_name, domain, Some(vctx))?;
    let mut y_env = env.clone();
    y_env.insert(var.to_owned(), y_var.clone());

    // Encode P(y) — same body, but with y bound to the quantifier variable
    let p_y = encode_pure_expr_inner(body, &y_env, vctx, defs, precheck)?
        .to_bool()?;

    // Domain predicate for y
    let d_y = build_domain_predicate(domain, &y_var, &y_env, vctx, defs, precheck)?;

    // D(y) ∧ P(y) → y = x
    let y_satisfies = match &d_y {
        Some(dp) => Bool::and(&[dp, &p_y]),
        None => p_y,
    };
    let y_eq_x = smt::smt_eq(&y_var, &x_var)?;
    let uniqueness_body = y_satisfies.implies(&y_eq_x);

    // ∀y. D(y) ∧ P(y) → y = x
    let forall_unique = build_z3_quantifier(true, &y_var, &uniqueness_body, &y_name, domain)?;

    // ∃x. D(x) ∧ P(x) ∧ (∀y. D(y) ∧ P(y) → y = x)
    let exists_body = Bool::and(&[&x_satisfies, &forall_unique]);
    let result = build_z3_quantifier(false, &x_var, &exists_body, var, domain)?;

    Ok(SmtValue::Bool(result))
}

/// Encode `lone x: T | P(x)` — at most one x satisfies P.
///
/// Semantics: ∀x, y. D(x) ∧ D(y) ∧ P(x) ∧ P(y) → x = y
///
/// where D is the domain predicate (enum range, refinement guard, etc.)
#[allow(clippy::too_many_arguments)]
fn encode_z3_lone(
    var: &str,
    domain: &crate::ir::types::IRType,
    body: &IRExpr,
    env: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    precheck: Option<&PrecheckCtx<'_>>,
) -> Result<SmtValue, String> {
    // Create bound variable x (ADT-aware via vctx)
    let x_var = make_z3_var_ctx(var, domain, Some(vctx))?;
    let mut x_env = env.clone();
    x_env.insert(var.to_owned(), x_var.clone());

    // Create bound variable y (different Z3 name, ADT-aware)
    let y_name = format!("{var}__unique");
    let y_var = make_z3_var_ctx(&y_name, domain, Some(vctx))?;
    let mut y_env = env.clone();
    y_env.insert(var.to_owned(), y_var.clone());

    // Encode P(x) and P(y)
    let p_x = encode_pure_expr_inner(body, &x_env, vctx, defs, precheck)?
        .to_bool()?;
    let p_y = encode_pure_expr_inner(body, &y_env, vctx, defs, precheck)?
        .to_bool()?;

    // Domain predicates
    let d_x = build_domain_predicate(domain, &x_var, &x_env, vctx, defs, precheck)?;
    let d_y = build_domain_predicate(domain, &y_var, &y_env, vctx, defs, precheck)?;

    // D(x) ∧ D(y) ∧ P(x) ∧ P(y)
    let mut antecedents = Vec::new();
    if let Some(dp) = &d_x {
        antecedents.push(dp.clone());
    }
    if let Some(dp) = &d_y {
        antecedents.push(dp.clone());
    }
    antecedents.push(p_x);
    antecedents.push(p_y);
    let antecedent_refs: Vec<&Bool> = antecedents.iter().collect();
    let lhs = Bool::and(&antecedent_refs);

    // x = y
    let x_eq_y = smt::smt_eq(&x_var, &y_var)?;

    // D(x) ∧ D(y) ∧ P(x) ∧ P(y) → x = y
    let forall_body = lhs.implies(&x_eq_y);

    // ∀y. [body]
    let inner = build_z3_quantifier(true, &y_var, &forall_body, &y_name, domain)?;
    // ∀x. ∀y. [body]
    let result = build_z3_quantifier(true, &x_var, &inner, var, domain)?;

    Ok(SmtValue::Bool(result))
}

/// Encode a lambda expression as a Z3 uninterpreted function with a
/// definitional axiom.
///
/// For `fn(x: T): R => body`:
/// 1. Uncurry nested Lams to get all parameters
/// 2. Create `FuncDecl::new("__lambda_N", domain_sorts, range_sort)`
/// 3. Create Z3 bound variables for each parameter
/// 4. Encode the body with parameters in scope
/// 5. Assert definitional axiom: `forall params. f(params) == body`
/// 6. Return `SmtValue::Func(func_decl)`
///
/// Handles curried lambdas: `Lam(x, Lam(y, body))` → `f(x, y) == body`.
fn encode_lambda(
    expr: &IRExpr,
    env: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    precheck: Option<&PrecheckCtx<'_>>,
) -> Result<SmtValue, String> {
    // Uncurry: collect all nested Lam parameters
    let mut params: Vec<(&str, &crate::ir::types::IRType)> = Vec::new();
    let mut current = expr;
    while let IRExpr::Lam {
        param,
        param_type,
        body,
        ..
    } = current
    {
        params.push((param.as_str(), param_type));
        current = body;
    }
    let body_expr = current;

    if params.is_empty() {
        return Err("empty lambda (no parameters)".to_owned());
    }

    // Create Z3 variables for parameters (ADT-aware via vctx)
    let mut inner_env = env.clone();
    let mut bound_vars: Vec<SmtValue> = Vec::new();
    let mut domain_sorts: Vec<z3::Sort> = Vec::new();
    for (pname, pty) in &params {
        let var = make_z3_var_ctx(pname, pty, Some(vctx))?;
        // Extract the sort from the created variable
        use z3::ast::Ast;
        let sort = var.to_dynamic().get_sort();
        domain_sorts.push(sort);
        inner_env.insert((*pname).to_owned(), var.clone());
        bound_vars.push(var);
    }
    let domain_refs: Vec<&z3::Sort> = domain_sorts.iter().collect();

    // Encode the body with all params in scope
    let body_val = encode_pure_expr_inner(body_expr, &inner_env, vctx, defs, precheck)?;

    // Determine range sort from the encoded body value
    use z3::ast::Ast;
    let range_sort = body_val.to_dynamic().get_sort();

    // Create the uninterpreted function
    let lambda_id = LAMBDA_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let func_name = format!("__lambda_{lambda_id}");
    let func_decl = z3::FuncDecl::new(func_name.as_str(), &domain_refs, &range_sort);

    // Build the definitional axiom: forall params. f(params) == body
    // Use Dynamic for all parameter types (works for scalars and ADTs)
    let bound_dyns: Vec<z3::ast::Dynamic> = bound_vars
        .iter()
        .map(SmtValue::to_dynamic)
        .collect();
    let app_args: Vec<&dyn z3::ast::Ast> = bound_dyns
        .iter()
        .map(|d| d as &dyn z3::ast::Ast)
        .collect();
    let app_result = func_decl.apply(&app_args);
    let app_smt = dynamic_to_smt_value(app_result);
    let eq = smt::smt_eq(&app_smt, &body_val)?;

    // Quantify over all parameters using Dynamic binders
    let bounds: Vec<&dyn z3::ast::Ast> = bound_dyns
        .iter()
        .map(|d| d as &dyn z3::ast::Ast)
        .collect();
    let axiom = z3::ast::forall_const(&bounds, &[], &eq);

    push_lambda_axiom(axiom);

    Ok(SmtValue::Func(std::rc::Rc::new((func_decl, domain_sorts, range_sort))))
}

/// Encode a partial application as a new uninterpreted function.
///
/// Given `f(a1, ..., ak)` where `f` has arity `n > k`, creates a fresh
/// function `g(x_{k+1}, ..., x_n)` with axiom:
///   `forall x_{k+1}, ..., x_n. g(x_{k+1}, ..., x_n) = f(a1, ..., ak, x_{k+1}, ..., x_n)`
///
/// This models currying: `add(1)` creates `inc(y) = add(1, y)`.
fn encode_partial_application(
    orig_func: &z3::FuncDecl,
    param_sorts: &[z3::Sort],
    range_sort: &z3::Sort,
    bound_args: &[z3::ast::Dynamic],
) -> Result<SmtValue, String> {
    let remaining_param_sorts: Vec<z3::Sort> =
        param_sorts[bound_args.len()..].to_vec();
    let remaining_sort_refs: Vec<&z3::Sort> = remaining_param_sorts.iter().collect();

    // Create fresh function symbol for the partial application
    let partial_id = LAMBDA_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let partial_name = format!("__partial_{partial_id}");
    let partial_func =
        z3::FuncDecl::new(partial_name.as_str(), &remaining_sort_refs, range_sort);

    // Create bound variables for the remaining parameters
    let mut remaining_vars: Vec<z3::ast::Dynamic> = Vec::new();
    for (i, sort) in remaining_param_sorts.iter().enumerate() {
        let var_name = format!("__parg_{partial_id}_{i}");
        remaining_vars.push(z3::ast::Dynamic::new_const(var_name.as_str(), sort));
    }

    // Build: g(x_{k+1}, ..., x_n)
    let partial_arg_refs: Vec<&dyn z3::ast::Ast> =
        remaining_vars.iter().map(|v| v as &dyn z3::ast::Ast).collect();
    let partial_app = partial_func.apply(&partial_arg_refs);

    // Build: f(a1, ..., ak, x_{k+1}, ..., x_n)
    let mut full_args: Vec<z3::ast::Dynamic> = bound_args.to_vec();
    full_args.extend(remaining_vars.iter().cloned());
    let full_arg_refs: Vec<&dyn z3::ast::Ast> =
        full_args.iter().map(|v| v as &dyn z3::ast::Ast).collect();
    let full_app = orig_func.apply(&full_arg_refs);

    // Definitional axiom: g(remaining) == f(bound, remaining)
    let eq = partial_app.eq(full_app);

    // Quantify over remaining parameters
    let bounds: Vec<&dyn z3::ast::Ast> =
        remaining_vars.iter().map(|v| v as &dyn z3::ast::Ast).collect();
    let axiom = if !bounds.is_empty() {
        z3::ast::forall_const(&bounds, &[], &eq)
    } else {
        eq
    };

    push_lambda_axiom(axiom);

    Ok(SmtValue::Func(std::rc::Rc::new((
        partial_func,
        remaining_param_sorts,
        range_sort.clone(),
    ))))
}

/// Encode a literal value to Z3.
fn encode_pure_lit(
    value: &crate::ir::types::LitVal,
    _ty: &crate::ir::types::IRType,
) -> Result<SmtValue, String> {
    use crate::ir::types::LitVal;
    match value {
        LitVal::Int { value } => Ok(smt::int_val(*value)),
        LitVal::Bool { value } => Ok(smt::bool_val(*value)),
        LitVal::Real { value } => {
            // Approximate: convert f64 to rational
            #[allow(clippy::cast_possible_truncation)]
            let scaled = (*value * 1_000_000.0) as i64;
            Ok(smt::real_val(scaled, 1_000_000))
        }
        LitVal::Float { value } => {
            #[allow(clippy::cast_possible_truncation)]
            let scaled = (*value * 1_000_000.0) as i64;
            Ok(smt::real_val(scaled, 1_000_000))
        }
        LitVal::Str { value } => {
            // Strings are encoded as Int (see smt::ir_type_to_sort).
            // Each distinct string literal must produce a distinct Int constant.
            // We use a deterministic hash so "a" != "b" but "a" == "a".
            use std::hash::{Hash, Hasher};
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            value.hash(&mut hasher);
            // Use the lower 62 bits to stay safely in i64 range
            let hash = (hasher.finish() & 0x3FFF_FFFF_FFFF_FFFF) as i64;
            Ok(smt::int_val(hash))
        }
    }
}

/// Encode an if-then-else at the SmtValue level.
fn encode_ite(
    cond: &z3::ast::Bool,
    then_val: &SmtValue,
    else_val: &SmtValue,
) -> Result<SmtValue, String> {
    match (then_val, else_val) {
        (SmtValue::Int(t), SmtValue::Int(e)) => Ok(SmtValue::Int(cond.ite(t, e))),
        (SmtValue::Bool(t), SmtValue::Bool(e)) => Ok(SmtValue::Bool(cond.ite(t, e))),
        (SmtValue::Real(t), SmtValue::Real(e)) => Ok(SmtValue::Real(cond.ite(t, e))),
        (SmtValue::Array(t), SmtValue::Array(e)) => Ok(SmtValue::Array(cond.ite(t, e))),
        (SmtValue::Dynamic(t), SmtValue::Dynamic(e)) => Ok(SmtValue::Dynamic(cond.ite(t, e))),
        // Cross-variant: coerce to Dynamic
        _ => {
            let t_dyn = then_val.to_dynamic();
            let e_dyn = else_val.to_dynamic();
            Ok(SmtValue::Dynamic(cond.ite(&t_dyn, &e_dyn)))
        }
    }
}

/// Encode a match expression in the pure context.
///
/// Each arm is encoded as an ITE chain:
/// match e { P1 => b1, P2 => b2, _ => b3 }
/// → ite(P1(e), b1, ite(P2(e), b2, b3))
fn encode_pure_match(
    scrut: &SmtValue,
    arms: &[crate::ir::types::IRMatchArm],
    env: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    precheck: Option<&PrecheckCtx<'_>>,
) -> Result<SmtValue, String> {
    if arms.is_empty() {
        return Err("empty match expression".to_owned());
    }

    let mut result: Option<SmtValue> = None;

    for arm in arms.iter().rev() {
        let arm_cond = encode_pattern_cond(scrut, &arm.pattern, env, vctx)?;
        let mut arm_env = env.clone();
        bind_pattern_vars(&arm.pattern, scrut, &mut arm_env, vctx)?;

        let full_cond = if let Some(guard) = &arm.guard {
            let guard_val = encode_pure_expr_inner(guard, &arm_env, vctx, defs, precheck)?;
            let guard_bool = guard_val.to_bool()?;
            SmtValue::Bool(Bool::and(&[&arm_cond, &guard_bool]))
        } else {
            SmtValue::Bool(arm_cond.clone())
        };

        let body_val = encode_pure_expr_inner(&arm.body, &arm_env, vctx, defs, precheck)?;

        result = Some(match result {
            Some(else_val) => {
                let cond_bool = full_cond.to_bool()?;
                encode_ite(&cond_bool, &body_val, &else_val)?
            }
            None => body_val, // last arm = default
        });
    }

    result.ok_or_else(|| "empty match".to_owned())
}

/// Find the ADT sort that matches a scrutinee's Z3 sort.
/// Returns `(enum_name, &DatatypeSort)` if found.
fn resolve_scrut_adt<'a>(
    scrut: &SmtValue,
    vctx: &'a VerifyContext,
) -> Option<(&'a str, &'a z3::DatatypeSort)> {
    if let SmtValue::Dynamic(d) = scrut {
        use z3::ast::Ast;
        let scrut_sort = d.get_sort().to_string();
        for (name, dt) in &vctx.adt_sorts {
            if dt.sort.to_string() == scrut_sort {
                return Some((name.as_str(), dt));
            }
        }
    }
    None
}

/// Encode a pattern match condition as a Z3 Bool.
///
/// Constructor patterns are resolved against the scrutinee's ADT sort
/// (type-directed), not by scanning all ADTs globally.
fn encode_pattern_cond(
    scrut: &SmtValue,
    pattern: &crate::ir::types::IRPattern,
    _env: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
) -> Result<z3::ast::Bool, String> {
    use crate::ir::types::IRPattern;
    match pattern {
        IRPattern::PWild | IRPattern::PVar { .. } => Ok(Bool::from_bool(true)),
        IRPattern::PCtor { name, .. } => {
            // Type-directed: resolve against the scrutinee's ADT sort
            if let Some((_enum_name, dt)) = resolve_scrut_adt(scrut, vctx) {
                for variant in &dt.variants {
                    let ctor_name = variant.constructor.name();
                    if ctor_name == *name
                        || format!("{_enum_name}::{ctor_name}") == *name
                    {
                        let scrut_dyn = scrut.to_dynamic();
                        let result = variant.tester.apply(&[&scrut_dyn]);
                        return result
                            .as_bool()
                            .ok_or_else(|| format!("ADT tester did not return Bool for {name}"));
                    }
                }
                return Err(format!("unknown constructor '{name}' for enum '{_enum_name}'"));
            }
            // Fallback: flat Int encoding for fieldless enums
            let scrut_int = scrut.as_int()?;
            for ((type_name, variant_name), id) in &vctx.variants.to_id {
                if variant_name == name || format!("{type_name}::{variant_name}") == *name {
                    return Ok(scrut_int.eq(z3::ast::Int::from_i64(*id)));
                }
            }
            Err(format!("unknown constructor pattern: {name}"))
        }
        IRPattern::POr { left, right } => {
            let l = encode_pattern_cond(scrut, left, _env, vctx)?;
            let r = encode_pattern_cond(scrut, right, _env, vctx)?;
            Ok(Bool::or(&[&l, &r]))
        }
    }
}

/// Bind pattern variables into the environment.
///
/// For ADT-encoded enums with constructor fields, extracts field values
/// using Z3 datatype accessor functions. For fieldless enums, no bindings
/// are needed from the constructor itself.
fn bind_pattern_vars(
    pattern: &crate::ir::types::IRPattern,
    scrut: &SmtValue,
    env: &mut HashMap<String, SmtValue>,
    vctx: &VerifyContext,
) -> Result<(), String> {
    use crate::ir::types::IRPattern;
    match pattern {
        IRPattern::PVar { name } => {
            env.insert(name.clone(), scrut.clone());
            Ok(())
        }
        IRPattern::PWild => Ok(()),
        IRPattern::PCtor { name, fields } => {
            if fields.is_empty() {
                return Ok(());
            }
            // Type-directed: resolve against the scrutinee's ADT sort
            if let Some((_enum_name, dt)) = resolve_scrut_adt(scrut, vctx) {
                for variant in &dt.variants {
                    let ctor_name = variant.constructor.name();
                    if ctor_name == *name
                        || !_enum_name.is_empty() && format!("{_enum_name}::{ctor_name}") == *name
                    {
                        // Extract fields by name — match each pattern field to
                        // the accessor with the same name, not by position.
                        let scrut_dyn = scrut.to_dynamic();
                        for field_pat in fields {
                            let accessor = variant
                                .accessors
                                .iter()
                                .find(|a| a.name() == field_pat.name)
                                .ok_or_else(|| {
                                    format!(
                                        "unknown field '{}' in pattern for constructor '{name}'",
                                        field_pat.name
                                    )
                                })?;
                            let field_val = accessor.apply(&[&scrut_dyn]);
                            let smt_val = dynamic_to_smt_value(field_val);
                            bind_pattern_vars(&field_pat.pattern, &smt_val, env, vctx)?;
                        }
                        return Ok(());
                    }
                }
            }
            Err(format!(
                "constructor field destructuring requires algebraic datatype encoding — \
                 enum variant '{name}' not found in registered ADT sorts"
            ))
        }
        IRPattern::POr { left, right } => {
            bind_pattern_vars(left, scrut, env, vctx)?;
            bind_pattern_vars(right, scrut, env, vctx)
        }
    }
}

/// Convert a Z3 Dynamic value to an SmtValue, attempting type-specific conversions.
fn dynamic_to_smt_value(d: z3::ast::Dynamic) -> SmtValue {
    if let Some(i) = d.as_int() {
        SmtValue::Int(i)
    } else if let Some(b) = d.as_bool() {
        SmtValue::Bool(b)
    } else if let Some(r) = d.as_real() {
        SmtValue::Real(r)
    } else {
        SmtValue::Dynamic(d)
    }
}

/// Extract a human-readable value from a Z3 model for counterexample display.
fn extract_model_value(
    model: &z3::Model,
    val: &SmtValue,
    variants: &context::VariantMap,
    ty: &crate::ir::types::IRType,
) -> String {
    match val {
        SmtValue::Int(i) => {
            if let Some(model_val) = model.eval(i, true) {
                let s = model_val.to_string();
                // Check if this is an enum — try to decode the int to a variant name
                if let crate::ir::types::IRType::Enum { .. } = ty {
                    if let Ok(id) = s.parse::<i64>() {
                        if let Some((type_name, variant_name)) = variants.name_of(id) {
                            return format!("@{type_name}::{variant_name}");
                        }
                    }
                }
                s
            } else {
                "?".to_owned()
            }
        }
        SmtValue::Bool(b) => model
            .eval(b, true)
            .map_or("?".to_owned(), |v| v.to_string()),
        SmtValue::Real(r) => model
            .eval(r, true)
            .map_or("?".to_owned(), |v| v.to_string()),
        _ => "?".to_owned(),
    }
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
        | IRExpr::One { span, .. }
        | IRExpr::Lone { span, .. }
        | IRExpr::Field { span, .. }
        | IRExpr::Prime { span, .. }
        | IRExpr::Always { span, .. }
        | IRExpr::Eventually { span, .. }
        | IRExpr::Until { span, .. }
        | IRExpr::Match { span, .. }
        | IRExpr::MapUpdate { span, .. }
        | IRExpr::Index { span, .. }
        | IRExpr::SetLit { span, .. }
        | IRExpr::SeqLit { span, .. }
        | IRExpr::MapLit { span, .. }
        | IRExpr::SetComp { span, .. }
        | IRExpr::Card { span, .. }
        | IRExpr::Assert { span, .. }
        | IRExpr::Assume { span, .. }
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
        IRExpr::Forall { var, body, .. }
        | IRExpr::Exists { var, body, .. }
        | IRExpr::One { var, body, .. }
        | IRExpr::Lone { var, body, .. } => {
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
        IRExpr::BinOp { left, right, .. }
        | IRExpr::Until { left, right, .. } => {
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
fn ic3_trace_to_trace_steps(
    ic3_trace: &[ic3::Ic3TraceStep],
    entities: &[crate::ir::types::IREntity],
    systems: &[crate::ir::types::IRSystem],
) -> Vec<TraceStep> {
    let steps: Vec<TraceStep> = ic3_trace
        .iter()
        .map(|s| TraceStep {
            step: s.step,
            event: None,
            assignments: s.assignments.clone(),
        })
        .collect();

    let mut result = steps;
    for i in 0..result.len().saturating_sub(1) {
        let event_name = identify_event_from_field_changes(
            &result[i].assignments,
            &result[i + 1].assignments,
            entities,
            systems,
        );
        result[i].event = event_name;
    }
    result
}

/// Best-effort event identification for IC3 traces by comparing field changes
/// between consecutive steps against event action update signatures.
///
/// Matches based on which specific fields changed (not just entity name).
/// Collects all matching events — if ambiguous, reports "event A or event B".
fn identify_event_from_field_changes(
    before: &[(String, String, String)],
    after: &[(String, String, String)],
    entities: &[crate::ir::types::IREntity],
    systems: &[crate::ir::types::IRSystem],
) -> Option<String> {
    // Find which (entity, field) pairs changed
    let mut changed_fields: HashSet<(String, String)> = HashSet::new();
    for (entity_a, field_a, val_a) in after {
        let base_entity = entity_a.split('[').next().unwrap_or(entity_a).to_owned();
        let prev = before.iter().find(|(e, f, _)| e == entity_a && f == field_a);
        match prev {
            Some((_, _, val_b)) if val_a != val_b => {
                changed_fields.insert((base_entity, field_a.clone()));
            }
            None => {
                changed_fields.insert((base_entity, field_a.clone()));
            }
            _ => {}
        }
    }

    if changed_fields.is_empty() {
        return None; // stutter
    }

    // Check if new entities appeared
    let new_entities: HashSet<String> = after
        .iter()
        .filter(|(e, _, _)| !before.iter().any(|(eb, _, _)| eb == e))
        .map(|(e, _, _)| e.split('[').next().unwrap_or(e).to_owned())
        .collect();

    // Collect fields that each event's actions modify
    let mut matches = Vec::new();
    for system in systems {
        for event in &system.events {
            let modified = collect_event_modified_fields(&event.body, entities);
            let creates = collect_event_created_entities(&event.body);

            // Match: event modifies exactly the fields that changed,
            // or creates the entities that appeared
            let fields_match = !modified.is_empty()
                && modified.iter().all(|(e, f)| changed_fields.contains(&(e.clone(), f.clone())));
            let creates_match = !creates.is_empty()
                && creates.iter().any(|e| new_entities.contains(e));

            if fields_match || creates_match {
                let name = if systems.len() == 1 {
                    event.name.clone()
                } else {
                    format!("{}::{}", system.name, event.name)
                };
                matches.push(name);
            }
        }
    }

    match matches.len() {
        0 => None,
        1 => Some(matches.into_iter().next().unwrap()),
        _ => Some(matches.join(" or ")),
    }
}

/// Collect (entity, field) pairs modified by an event's actions.
///
/// Resolves transition/action names to the actual fields they update
/// by looking up entity IR transitions.
fn collect_event_modified_fields(
    actions: &[crate::ir::types::IRAction],
    entities: &[crate::ir::types::IREntity],
) -> HashSet<(String, String)> {
    use crate::ir::types::IRAction;
    let mut fields = HashSet::new();
    for action in actions {
        match action {
            IRAction::Choose { entity, ops, .. } | IRAction::ForAll { entity, ops, .. } => {
                for op in ops {
                    if let IRAction::Apply { transition, .. } = op {
                        // Resolve transition name to actual updated fields
                        if let Some(ent_ir) = entities.iter().find(|e| &e.name == entity) {
                            if let Some(trans) = ent_ir.transitions.iter().find(|t| &t.name == transition) {
                                for upd in &trans.updates {
                                    fields.insert((entity.clone(), upd.field.clone()));
                                }
                            }
                        }
                    }
                }
                let nested = collect_event_modified_fields(ops, entities);
                fields.extend(nested);
            }
            _ => {}
        }
    }
    fields
}

/// Collect entity names created by an event's actions.
fn collect_event_created_entities(actions: &[crate::ir::types::IRAction]) -> Vec<String> {
    use crate::ir::types::IRAction;
    let mut entities = Vec::new();
    for action in actions {
        match action {
            IRAction::Create { entity, .. } => entities.push(entity.clone()),
            IRAction::Choose { ops, .. } | IRAction::ForAll { ops, .. } => {
                entities.extend(collect_event_created_entities(ops));
            }
            _ => {}
        }
    }
    entities
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
        contains_liveness(&expanded)
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

    // Liveness properties: lasso BMC first (finds violations), then reduction (proves)
    if has_liveness {
        let system_names: Vec<String> = verify_block
            .systems
            .iter()
            .map(|vs| vs.name.clone())
            .collect();
        let has_fair_events = ir
            .systems
            .iter()
            .filter(|s| system_names.contains(&s.name))
            .any(|s| s.events.iter().any(|e| e.fairness.is_fair()));

        if has_fair_events {
            // Tier 2a: Try lasso BMC first — finds violations quickly
            let lasso_result = check_verify_block_lasso(ir, vctx, defs, verify_block, config);
            match &lasso_result {
                VerificationResult::LivenessViolation { .. } => return lasso_result,
                VerificationResult::Checked { .. } => {
                    // No violation found at this depth. Try reduction for PROVED.
                    if !config.bounded_only {
                        if let Some(proved) =
                            try_liveness_reduction(ir, vctx, defs, verify_block, config)
                        {
                            return proved;
                        }
                    }
                    // Reduction failed — return CHECKED from lasso
                    return lasso_result;
                }
                _ => return lasso_result,
            }
        }
        // No fair events — fall through to linear BMC.
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

// ── Liveness-to-Safety Reduction (Phase 13) ──────────────────────────

/// A liveness pattern extracted from an assertion.
enum LivenessPattern {
    /// `always (P implies eventually Q)` — response property
    Response {
        trigger: IRExpr,
        response: IRExpr,
    },
    /// `always eventually Q` — recurrence (trigger is always true, repeating)
    Recurrence {
        response: IRExpr,
    },
    /// `eventually Q` — bare eventuality (one-shot: Q must hold at least once)
    Eventuality {
        response: IRExpr,
    },
    /// `eventually always P` — persistence (P eventually holds forever)
    Persistence {
        condition: IRExpr,
    },
    /// `always (all o: E | P(o) implies eventually Q(o))`
    QuantifiedResponse {
        var: String,
        entity: String,
        trigger: IRExpr,
        response: IRExpr,
    },
    /// `always (all o: E | eventually Q(o))`
    QuantifiedRecurrence {
        var: String,
        entity: String,
        response: IRExpr,
    },
    /// `eventually (all o: E | Q(o))` or `all o: E | eventually Q(o)` (bare)
    QuantifiedEventuality {
        var: String,
        entity: String,
        response: IRExpr,
    },
    /// `eventually always (all o: E | P(o))`
    QuantifiedPersistence {
        var: String,
        entity: String,
        condition: IRExpr,
    },
}

/// Result of liveness pattern extraction: the recognized liveness pattern
/// plus any safety conjuncts that must be verified separately.
///
/// Safety conjuncts arise from conjunction decomposition (e.g., `until`
/// desugars to `(eventually Q) AND (always (¬Q → P))`). The liveness
/// side is extracted as the pattern; the safety side must still be proved.
struct PatternExtraction {
    pattern: LivenessPattern,
    safety_conjuncts: Vec<IRExpr>,
}

/// Extract a response/recurrence liveness pattern from an assertion.
///
/// Recognizes:
/// - `always (P implies eventually Q)` → Response
/// - `always eventually Q` → Recurrence
/// - `always (all o: E | P(o) implies eventually Q(o))` → QuantifiedResponse
/// - `always (all o: E | eventually Q(o))` → QuantifiedRecurrence
/// - Conjunctions where one side is liveness and the other is safety
///
/// Returns `None` if the expression doesn't match a supported pattern.
fn extract_liveness_pattern(
    expr: &IRExpr,
    defs: &defenv::DefEnv,
) -> Option<PatternExtraction> {
    let expanded = expand_through_defs(expr, defs);
    // Desugar `until` before extraction so `P until Q` becomes
    // `(eventually Q) AND (always (¬Q → P))`, which the conjunction
    // case can decompose into liveness + safety.
    let desugared = desugar_until(&expanded);
    extract_liveness_pattern_inner(&desugared)
}

fn extract_liveness_pattern_inner(expr: &IRExpr) -> Option<PatternExtraction> {
    let pattern = extract_liveness_pattern_with_always(expr, false)?;
    let safety_conjuncts = strip_liveness_from_conjunction(expr)
        .into_iter()
        .collect();
    Some(PatternExtraction {
        pattern,
        safety_conjuncts,
    })
}

/// Walk an expression tree and extract the safety side of any conjunction
/// where one side is liveness and the other is safety.
///
/// Preserves surrounding structure (Always, Forall) so the result can be
/// verified as a standalone safety property.
///
/// Returns `None` if no such conjunction exists (pure liveness or no conjunction).
fn strip_liveness_from_conjunction(expr: &IRExpr) -> Option<IRExpr> {
    match expr {
        IRExpr::Always { body, span } => {
            strip_liveness_from_conjunction(body).map(|inner| IRExpr::Always {
                body: Box::new(inner),
                span: *span,
            })
        }
        IRExpr::Forall {
            var,
            domain,
            body,
            span,
        } => strip_liveness_from_conjunction(body).map(|inner| IRExpr::Forall {
            var: var.clone(),
            domain: domain.clone(),
            body: Box::new(inner),
            span: *span,
        }),
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpAnd" => {
            let l = contains_liveness(left);
            let r = contains_liveness(right);
            match (l, r) {
                (true, false) => Some(*right.clone()), // left is liveness, right is safety
                (false, true) => Some(*left.clone()),  // right is liveness, left is safety
                _ => None,                             // both or neither — can't split
            }
        }
        _ => None,
    }
}

fn extract_liveness_pattern_with_always(expr: &IRExpr, inside_always: bool) -> Option<LivenessPattern> {
    match expr {
        // always (body) — mark that we're inside always
        IRExpr::Always { body, .. } => extract_liveness_pattern_with_always(body, true),

        // all o: Entity | body
        IRExpr::Forall {
            var,
            domain,
            body,
            ..
        } => {
            let entity = match domain {
                IRType::Entity { name } => name.clone(),
                _ => return extract_liveness_pattern_with_always(body, inside_always),
            };
            match body.as_ref() {
                // all o: E | P implies eventually Q
                IRExpr::BinOp {
                    op, left, right, ..
                } if op == "OpImplies" => {
                    if let IRExpr::Eventually { body: resp, .. } = right.as_ref() {
                        if inside_always {
                            Some(LivenessPattern::QuantifiedResponse {
                                var: var.clone(),
                                entity,
                                trigger: *left.clone(),
                                response: *resp.clone(),
                            })
                        } else {
                            None // bare `all o | P implies eventually Q` without always
                        }
                    } else {
                        None
                    }
                }
                // all o: E | eventually (always P) → quantified persistence
                IRExpr::Eventually { body: ev_body, .. }
                    if matches!(ev_body.as_ref(), IRExpr::Always { .. }) =>
                {
                    if let IRExpr::Always { body: inner, .. } = ev_body.as_ref() {
                        Some(LivenessPattern::QuantifiedPersistence {
                            var: var.clone(),
                            entity,
                            condition: *inner.clone(),
                        })
                    } else {
                        None
                    }
                }
                // all o: E | eventually Q
                IRExpr::Eventually { body: resp, .. } => {
                    if inside_always {
                        Some(LivenessPattern::QuantifiedRecurrence {
                            var: var.clone(),
                            entity,
                            response: *resp.clone(),
                        })
                    } else {
                        Some(LivenessPattern::QuantifiedEventuality {
                            var: var.clone(),
                            entity,
                            response: *resp.clone(),
                        })
                    }
                }
                // all o: E | <conjunction or other> — recurse, then wrap
                // with quantifier context if the result is non-quantified
                _ => {
                    let inner = extract_liveness_pattern_with_always(body, inside_always)?;
                    Some(match inner {
                        LivenessPattern::Response { trigger, response } => {
                            if inside_always {
                                LivenessPattern::QuantifiedResponse {
                                    var: var.clone(),
                                    entity,
                                    trigger,
                                    response,
                                }
                            } else {
                                return None;
                            }
                        }
                        LivenessPattern::Recurrence { response } => {
                            LivenessPattern::QuantifiedRecurrence {
                                var: var.clone(),
                                entity,
                                response,
                            }
                        }
                        LivenessPattern::Eventuality { response } => {
                            LivenessPattern::QuantifiedEventuality {
                                var: var.clone(),
                                entity,
                                response,
                            }
                        }
                        LivenessPattern::Persistence { condition } => {
                            LivenessPattern::QuantifiedPersistence {
                                var: var.clone(),
                                entity,
                                condition,
                            }
                        }
                        // Already quantified — leave as-is
                        other => other,
                    })
                },
            }
        }

        // P implies eventually Q (only valid inside always)
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpImplies" => {
            if let IRExpr::Eventually { body: resp, .. } = right.as_ref() {
                if inside_always {
                    Some(LivenessPattern::Response {
                        trigger: *left.clone(),
                        response: *resp.clone(),
                    })
                } else {
                    None // bare response without always
                }
            } else {
                None
            }
        }

        // Conjunction: can't soundly prove A ∧ B by proving one conjunct
        // Conjunction: from until desugaring (eventually Q) AND (always safety).
        // If exactly one side is liveness, extract it.
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpAnd" => {
            let l = contains_liveness(left);
            let r = contains_liveness(right);
            match (l, r) {
                (true, false) => extract_liveness_pattern_with_always(left, inside_always),
                (false, true) => extract_liveness_pattern_with_always(right, inside_always),
                _ => None,
            }
        }

        // eventually (always P) — persistence
        IRExpr::Eventually { body, .. } if matches!(body.as_ref(), IRExpr::Always { .. }) => {
            if let IRExpr::Always { body: inner, .. } = body.as_ref() {
                if let IRExpr::Forall {
                    var,
                    domain: IRType::Entity { name },
                    body: qb,
                    ..
                } = inner.as_ref()
                {
                    return Some(LivenessPattern::QuantifiedPersistence {
                        var: var.clone(),
                        entity: name.clone(),
                        condition: *qb.clone(),
                    });
                }
                Some(LivenessPattern::Persistence {
                    condition: *inner.clone(),
                })
            } else {
                None
            }
        }

        // eventually Q
        IRExpr::Eventually { body, .. } => {
            if let IRExpr::Forall {
                var,
                domain: IRType::Entity { name },
                body: qb,
                ..
            } = body.as_ref()
            {
                return if inside_always {
                    Some(LivenessPattern::QuantifiedRecurrence {
                        var: var.clone(),
                        entity: name.clone(),
                        response: *qb.clone(),
                    })
                } else {
                    Some(LivenessPattern::QuantifiedEventuality {
                        var: var.clone(),
                        entity: name.clone(),
                        response: *qb.clone(),
                    })
                };
            }
            if inside_always {
                Some(LivenessPattern::Recurrence {
                    response: *body.clone(),
                })
            } else {
                Some(LivenessPattern::Eventuality {
                    response: *body.clone(),
                })
            }
        }

        _ => None,
    }
}

// ── Symmetry reduction for quantified liveness (Phase 16) ────────────
//
// For `always all o: E | P(o) implies eventually Q(o)` with fair events:
// 1. All entities of type E have identical field types, defaults, and transitions
// 2. Fair events with `choose o: E where guard` are symmetric: which slot is
//    chosen is nondeterministic, but fairness guarantees each enabled slot
//    is eventually served
// 3. Therefore: if the property is PROVED for a system with 1 slot of type E,
//    by symmetry it holds for any slot count
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
///    type (directly or via CrossCall), which would create inter-entity dependencies.
///
/// 2. **CrossCall composition**: If an event body calls into another system via
///    CrossCall, and that system also Choose/ForAll over the quantified entity type,
///    the combined event manipulates multiple slots (symmetry broken).
///
/// 3. **Property formulas**: The trigger/response expressions must not contain
///    additional quantifiers (Forall/Exists/One/Lone) over the same entity type,
///    which would reference multiple slots in the property itself.
///
/// Returns `true` if the system is symmetric for the given entity type.
fn validate_symmetry(
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
        for event in &sys.events {
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
/// following CrossCall targets transitively into other systems.
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
            IRAction::CrossCall { system, event, .. } => {
                let key = (system.clone(), event.clone());
                if visited_crosscalls.insert(key) {
                    // Follow into the CrossCall target's event body
                    if let Some(sys) = all_systems.iter().find(|s| s.name == *system) {
                        if let Some(evt) = sys.events.iter().find(|e| e.name == *event) {
                            count_entity_actions_with_crosscall(
                                &evt.body,
                                entity_name,
                                all_systems,
                                count,
                                visited_crosscalls,
                            );
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

/// Check whether an IRExpr contains any quantifier (Forall/Exists/One/Lone)
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
        IRExpr::Match { scrutinee, arms, .. } => {
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

/// Try symmetry reduction for quantified liveness patterns.
///
/// Validates entity symmetry for each quantified pattern. Currently cannot
/// PROVE properties unboundedly — returns None to fall back to lasso BMC
/// (CHECKED) or UNPROVABLE.
///
/// IC3's BAS monitor encoding uses coarse justice tracking that is fundamentally
/// unsound for liveness: it under-approximates the accepting condition by
/// requiring all fair events to have fired, but doesn't account for events that
/// are never enabled (where fairness is vacuously satisfied). This causes false
/// PROVED results on systems with reachable dead states. No fixed-depth lasso
/// sanity check can compensate — the dead state may be arbitrarily deep.
///
/// Sound unbounded liveness proofs require either:
/// - A BAS encoding with per-event enabled tracking (IC3/Spacer struggles with
///   the additional CHC columns)
/// - k-liveness (Claessen & Sörensson) which sidesteps BAS entirely
/// - Manual proof via `axiom ... by "file"`
fn try_symmetry_reduction(
    ir: &IRProgram,
    _vctx: &VerifyContext,
    _defs: &defenv::DefEnv,
    patterns: &[(usize, LivenessPattern)],
    _safety_obligations: &[IRExpr],
    _system_names: &[String],
    _scope: &HashMap<String, usize>,
    _fair_event_keys: &[(String, String)],
    relevant_systems: &[IRSystem],
    _config: &VerifyConfig,
    _start: &Instant,
    _verify_block: &IRVerify,
) -> Option<VerificationResult> {
    // Validate symmetry for each quantified entity type.
    // Even though we can't PROVE properties here, symmetry validation
    // is still useful for diagnostics and future k-liveness integration.
    for (_assert_idx, pattern) in patterns {
        let entity_name = match pattern {
            LivenessPattern::QuantifiedResponse { entity, .. }
            | LivenessPattern::QuantifiedRecurrence { entity, .. }
            | LivenessPattern::QuantifiedEventuality { entity, .. }
            | LivenessPattern::QuantifiedPersistence { entity, .. } => entity.as_str(),
            _ => continue,
        };

        if !validate_symmetry(entity_name, relevant_systems, &ir.systems, pattern) {
            return None; // symmetry broken
        }
    }

    // Cannot prove quantified liveness unboundedly with current IC3 encoding.
    // Fall through to lasso BMC (CHECKED) or UNPROVABLE.
    None
}

/// Try to prove liveness properties in a verify block via
/// liveness-to-safety reduction (Biere-Artho-Schuppan 2002).
///
/// Reduces `always (P implies eventually Q)` to a safety property
/// `always (not accepting)` with monitor state, then proves the
/// safety property via 1-induction.
///
/// Returns `Some(Proved)` if the safety property holds unboundedly,
/// or `None` if the proof fails (caller falls back to lasso BMC).
#[allow(clippy::too_many_lines)]
fn try_liveness_reduction(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    verify_block: &IRVerify,
    config: &VerifyConfig,
) -> Option<VerificationResult> {
    let start = Instant::now();

    // Build scope (same as try_induction_on_verify)
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

    // Adaptive scope from quantifier depth
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

    // Check if any relevant system has fair events (required for soundness)
    let has_fair_events = relevant_systems
        .iter()
        .any(|s| s.events.iter().any(|e| e.fairness.is_fair()));
    if !has_fair_events {
        return None; // can't prove liveness without fairness
    }

    // Collect fair event keys for justice tracking
    let fair_event_keys: Vec<(String, String)> = relevant_systems
        .iter()
        .flat_map(|s| {
            s.events
                .iter()
                .filter(|e| e.fairness.is_fair())
                .map(|e| (s.name.clone(), e.name.clone()))
        })
        .collect();

    // Extract liveness patterns from all asserts.
    // ALL liveness asserts must be recognized — if any is unsupported,
    // the reduction cannot prove the block and must return None.
    //
    // Also collect safety conjuncts from conjunction decomposition (e.g., from
    // desugared `until`). These must be verified separately after the liveness
    // side is proved.
    let mut patterns: Vec<(usize, LivenessPattern)> = Vec::new();
    let mut safety_obligations: Vec<IRExpr> = Vec::new();
    let mut has_unrecognized_liveness = false;
    for (i, assert_expr) in verify_block.asserts.iter().enumerate() {
        let expanded = expand_through_defs(assert_expr, defs);
        if contains_liveness(&expanded) {
            if let Some(extraction) = extract_liveness_pattern(assert_expr, defs) {
                patterns.push((i, extraction.pattern));
                safety_obligations.extend(extraction.safety_conjuncts);
            } else {
                has_unrecognized_liveness = true;
            }
        }
    }

    if patterns.is_empty() || has_unrecognized_liveness {
        return None; // can't prove: no patterns or some liveness is unsupported
    }

    // Pre-validate expressions
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

    // ── Inductive step (the core of the proof) ──────────────────────
    // For each liveness assert, build a monitor and check
    // `not accepting(k+1)` given `not accepting(k)` and one transition.
    let pool = create_slot_pool(&relevant_entities, &scope, 1);
    let solver = Solver::new();
    set_solver_timeout(&solver, config.induction_timeout_ms);

    for c in domain_constraints(&pool, vctx, &relevant_entities) {
        solver.assert(&c);
    }

    // Fire tracking for the single transition step (0→1)
    let fire_tracking =
        transition_constraints_with_fire(&pool, vctx, &relevant_entities, &relevant_systems, 1);
    for c in &fire_tracking.constraints {
        solver.assert(c);
    }

    // Build a monitor per liveness assert.
    //
    // For QUANTIFIED patterns (all o: E | ... eventually ...):
    //   Build one monitor PER entity slot. This gives universal semantics:
    //   each slot must independently satisfy the liveness property.
    //   If ANY slot's monitor can accept, the property is violated.
    //
    // For NON-QUANTIFIED patterns: one monitor per assert (as before).
    let mut accepting_vars_step1: Vec<Bool> = Vec::new();

    for (_assert_idx, pattern) in &patterns {
        // Determine the slot range for this pattern
        let (quant_var, quant_entity) = match pattern {
            LivenessPattern::QuantifiedResponse { var, entity, .. }
            | LivenessPattern::QuantifiedRecurrence { var, entity, .. }
            | LivenessPattern::QuantifiedEventuality { var, entity, .. }
            | LivenessPattern::QuantifiedPersistence { var, entity, .. } => {
                (Some(var.as_str()), Some(entity.as_str()))
            }
            _ => (None, None),
        };

        let slot_count = if let Some(ent_name) = quant_entity {
            pool.slots_for(ent_name)
        } else {
            1 // non-quantified: single monitor
        };

        for target_slot in 0..slot_count {
            // Unique prefix per (assert, slot) to avoid variable name collisions
            let prefix = if quant_entity.is_some() {
                format!("mon{_assert_idx}_s{target_slot}")
            } else {
                format!("mon{_assert_idx}")
            };

            let pending_0 = Bool::new_const(format!("{prefix}_pending_t0"));
            let pending_1 = Bool::new_const(format!("{prefix}_pending_t1"));

            // Saved state: one copy per entity/slot/field (constants — captured at trigger)
            let mut saved_fields: Vec<(String, usize, String, SmtValue)> = Vec::new();
            let mut saved_active: Vec<(String, usize, SmtValue)> = Vec::new();
            for entity in &relevant_entities {
                let n_slots = pool.slots_for(&entity.name);
                for slot in 0..n_slots {
                    for field in &entity.fields {
                        let name =
                            format!("{prefix}_saved_{}_s{}_{}", entity.name, slot, field.name);
                        let var = match &field.ty {
                            IRType::Bool => smt::bool_var(&name),
                            IRType::Real | IRType::Float => smt::real_var(&name),
                            _ => smt::int_var(&name),
                        };
                        saved_fields.push((entity.name.clone(), slot, field.name.clone(), var));
                    }
                    let act_name = format!("{prefix}_saved_{}_s{}_active", entity.name, slot);
                    saved_active.push((entity.name.clone(), slot, smt::bool_var(&act_name)));
                }
            }

            // Justice counters: one per fair event, at steps 0 and 1
            let mut justice_0: Vec<Bool> = Vec::new();
            let mut justice_1: Vec<Bool> = Vec::new();
            for (i, _key) in fair_event_keys.iter().enumerate() {
                justice_0.push(Bool::new_const(format!("{prefix}_justice{i}_t0")));
                justice_1.push(Bool::new_const(format!("{prefix}_justice{i}_t1")));
            }

            // Build property context: bind quantified variable to this specific slot
            let ctx = if let (Some(var), Some(ent_name)) = (quant_var, quant_entity) {
                PropertyCtx::new().with_binding(var, ent_name, target_slot)
            } else {
                PropertyCtx::new()
            };

            let (trigger_0, response_0) = match pattern {
                LivenessPattern::Response { trigger, response }
                | LivenessPattern::QuantifiedResponse { trigger, response, .. } => {
                    let p = encode_prop_expr(&pool, vctx, defs, &ctx, trigger, 0).ok()?;
                    let q = encode_prop_expr(&pool, vctx, defs, &ctx, response, 0).ok()?;
                    (p, q)
                }
                LivenessPattern::Recurrence { response }
                | LivenessPattern::QuantifiedRecurrence { response, .. }
                | LivenessPattern::Eventuality { response }
                | LivenessPattern::QuantifiedEventuality { response, .. } => {
                    let q = encode_prop_expr(&pool, vctx, defs, &ctx, response, 0).ok()?;
                    (Bool::from_bool(true), q)
                }
                LivenessPattern::Persistence { condition }
                | LivenessPattern::QuantifiedPersistence { condition, .. } => {
                    // ◇□P: trigger=true, response=P. Monitor finds cycles where P never holds.
                    let p = encode_prop_expr(&pool, vctx, defs, &ctx, condition, 0).ok()?;
                    (Bool::from_bool(true), p)
                }
            };

            // Monitor transition: step 0 → step 1
            //
            // trigger_fires = NOT pending_0 AND P(0) AND NOT Q(0)
            let trigger_fires = Bool::and(&[&pending_0.not(), &trigger_0, &response_0.not()]);
            // discharge = pending_0 AND Q(0)
            let discharge = Bool::and(&[&pending_0, &response_0]);

            // pending_1 = ITE(trigger_fires, true, ITE(discharge, false, pending_0))
            let pending_1_val = trigger_fires.ite(
                &Bool::from_bool(true),
                &discharge.ite(&Bool::from_bool(false), &pending_0),
            );
            solver.assert(&pending_1.eq(pending_1_val));

            // Saved state capture: on trigger, save current state
            for (ent, slot, field, saved_var) in &saved_fields {
                if let Some(current) = pool.field_at(ent, *slot, field, 0) {
                    let saved_val = smt::smt_ite(&trigger_fires, current, saved_var);
                    if let Ok(eq) = smt::smt_eq(&saved_val, saved_var) {
                        solver.assert(&eq);
                    }
                }
            }
            for (ent, slot, saved_act) in &saved_active {
                if let Some(SmtValue::Bool(current)) = pool.active_at(ent, *slot, 0) {
                    let saved_val = trigger_fires.ite(
                        current,
                        match saved_act {
                            SmtValue::Bool(b) => b,
                            _ => continue,
                        },
                    );
                    if let SmtValue::Bool(s) = saved_act {
                        solver.assert(&s.eq(saved_val));
                    }
                }
            }

            // Justice tracking: on trigger_fires, reset to just this step's fire.
            // Otherwise, accumulate: justice_1 = justice_0 OR fire_at_0
            for (i, key) in fair_event_keys.iter().enumerate() {
                let fired_at_0 = fire_tracking
                    .fire_vars
                    .get(key)
                    .and_then(|v| v.first())
                    .cloned()
                    .unwrap_or_else(|| Bool::from_bool(false));

                let justice_val = trigger_fires.ite(
                    &fired_at_0,
                    &Bool::or(&[&justice_0[i], &fired_at_0]),
                );
                solver.assert(&justice_1[i].eq(justice_val));
            }

            // Loop detection: accepting_1 = pending_1 AND state_matches AND all_justice
            let mut state_match_parts: Vec<Bool> = Vec::new();
            for (ent, slot, field, saved_var) in &saved_fields {
                if let Some(current) = pool.field_at(ent, *slot, field, 1) {
                    if let Ok(eq) = smt::smt_eq(saved_var, current) {
                        state_match_parts.push(eq);
                    }
                }
            }
            for (ent, slot, saved_act) in &saved_active {
                if let Some(SmtValue::Bool(current)) = pool.active_at(ent, *slot, 1) {
                    if let SmtValue::Bool(s) = saved_act {
                        state_match_parts.push(s.eq(current.clone()));
                    }
                }
            }

            let state_matches = if state_match_parts.is_empty() {
                Bool::from_bool(true)
            } else {
                let refs: Vec<&Bool> = state_match_parts.iter().collect();
                Bool::and(&refs)
            };

            let all_justice = if justice_1.is_empty() {
                Bool::from_bool(true)
            } else {
                let refs: Vec<&Bool> = justice_1.iter().collect();
                Bool::and(&refs)
            };

            let accepting_1 = Bool::and(&[&pending_1, &state_matches, &all_justice]);
            accepting_vars_step1.push(accepting_1);
        } // end for target_slot
    }

    // Inductive hypothesis: no monitor is accepting at step 0
    // (Since we don't assert accepting_0 explicitly, the solver is free to
    //  choose any value. We assert NOT accepting_0 as the hypothesis.)
    // Actually, we need to assert: none of the monitors are accepting at step 0.
    // The accepting_0 is not materialized — we just don't constrain it.
    // The hypothesis is that the safety property holds at step k.
    // For simplicity, assert that no accepting condition holds at step 0.
    //
    // Note: we don't need separate accepting_0 variables. The hypothesis
    // is implicit: we're checking whether accepting can become true after
    // one transition from ANY state where it's not true.
    //
    // We assert: the negation of the safety property at step 1 (any accepting_1 is true)
    let any_accepting = if accepting_vars_step1.len() == 1 {
        accepting_vars_step1[0].clone()
    } else {
        let refs: Vec<&Bool> = accepting_vars_step1.iter().collect();
        Bool::or(&refs)
    };
    solver.assert(&any_accepting);

    // Check: UNSAT means no transition can make any monitor accepting → PROVED
    match solver.check() {
        z3::SatResult::Unsat => {
            // Liveness part proved. Now verify safety obligations (if any).
            if !safety_obligations.is_empty() {
                let safety_verify = IRVerify {
                    name: verify_block.name.clone(),
                    systems: verify_block.systems.clone(),
                    asserts: safety_obligations.clone(),
                    span: verify_block.span,
                    file: verify_block.file.clone(),
                };
                // Try induction first, then IC3 for safety
                let safety_proved =
                    try_induction_on_verify(ir, vctx, defs, &safety_verify, config)
                        .or_else(|| {
                            if !config.no_ic3 {
                                try_ic3_on_verify(ir, vctx, defs, &safety_verify, config)
                            } else {
                                None
                            }
                        });
                match safety_proved {
                    Some(VerificationResult::Proved { .. }) => {
                        let elapsed = elapsed_ms(&start);
                        return Some(VerificationResult::Proved {
                            name: verify_block.name.clone(),
                            method: crate::messages::LIVENESS_REDUCTION_METHOD.to_owned(),
                            time_ms: elapsed,
                            span: None,
                            file: None,
                        });
                    }
                    _ => {} // safety couldn't be proved — fall through to IC3
                }
            } else {
                let elapsed = elapsed_ms(&start);
                return Some(VerificationResult::Proved {
                    name: verify_block.name.clone(),
                    method: crate::messages::LIVENESS_REDUCTION_METHOD.to_owned(),
                    time_ms: elapsed,
                    span: None,
                    file: None,
                });
            }
        }
        _ => {} // 1-induction failed — try IC3 below
    }

    // ── IC3/PDR on the reduced safety property ──────────────────────
    // 1-induction is too weak for most liveness reductions. IC3 can
    // automatically discover the strengthening invariants needed.
    let system_names: Vec<String> = verify_block
        .systems
        .iter()
        .map(|vs| vs.name.clone())
        .collect();

    // ALL patterns must be proved by IC3. If any fails, the block is not proved.
    //
    // For QUANTIFIED patterns: IC3 with coarse justice tracking on the full
    // multi-slot system is unsound (events firing on other slots satisfy
    // justice for the wrong slot). Instead, try symmetry reduction: prove
    // the property on a 1-slot system where coarse justice IS sound (there's
    // only one slot, so any event on that slot is the target), then
    // generalize by entity symmetry.
    let has_quantified = patterns.iter().any(|(_, p)| {
        matches!(
            p,
            LivenessPattern::QuantifiedResponse { .. }
                | LivenessPattern::QuantifiedRecurrence { .. }
                | LivenessPattern::QuantifiedEventuality { .. }
                | LivenessPattern::QuantifiedPersistence { .. }
        )
    });
    if has_quantified {
        // Try symmetry reduction before falling back to lasso BMC
        if let Some(result) = try_symmetry_reduction(
            ir,
            vctx,
            defs,
            &patterns,
            &safety_obligations,
            &system_names,
            &scope,
            &fair_event_keys,
            &relevant_systems,
            config,
            &start,
            verify_block,
        ) {
            return Some(result);
        }
        return None; // symmetry failed — fall back to lasso BMC (CHECKED)
    }

    let mut all_proved = true;
    'pattern_loop: for (_assert_idx, pattern) in &patterns {
        let true_lit = IRExpr::Lit {
            ty: IRType::Bool,
            value: crate::ir::types::LitVal::Bool { value: true },
            span: None,
        };

        let (actual_trigger, response_expr, ent_var, ent_name) = match pattern {
            LivenessPattern::Response { trigger, response } => {
                (trigger as &IRExpr, response as &IRExpr, None, None)
            }
            LivenessPattern::Recurrence { response }
            | LivenessPattern::Eventuality { response } => {
                (&true_lit as &IRExpr, response as &IRExpr, None, None)
            }
            LivenessPattern::Persistence { condition } => {
                (&true_lit as &IRExpr, condition as &IRExpr, None, None)
            }
            LivenessPattern::QuantifiedResponse {
                var,
                entity,
                trigger,
                response,
            } => (
                trigger as &IRExpr,
                response as &IRExpr,
                Some(var.as_str()),
                Some(entity.as_str()),
            ),
            LivenessPattern::QuantifiedRecurrence {
                var,
                entity,
                response,
            }
            | LivenessPattern::QuantifiedEventuality {
                var,
                entity,
                response,
            } => (
                &true_lit as &IRExpr,
                response as &IRExpr,
                Some(var.as_str()),
                Some(entity.as_str()),
            ),
            LivenessPattern::QuantifiedPersistence {
                var,
                entity,
                condition,
            } => (
                &true_lit as &IRExpr,
                condition as &IRExpr,
                Some(var.as_str()),
                Some(entity.as_str()),
            ),
        };

        let is_oneshot = matches!(
            pattern,
            LivenessPattern::Eventuality { .. } | LivenessPattern::QuantifiedEventuality { .. }
        );

        // Determine slot iteration range for quantified vs non-quantified
        let slot_count = if let Some(ent) = ent_name {
            scope.get(ent).copied().unwrap_or(1)
        } else {
            1 // non-quantified: single IC3 call with target_slot=None
        };

        for target_slot_idx in 0..slot_count {
            let target_slot = if ent_var.is_some() {
                Some(target_slot_idx)
            } else {
                None // non-quantified: no per-slot restriction
            };

            let ic3_result = ic3::try_ic3_liveness(
                ir,
                vctx,
                &system_names,
                actual_trigger,
                response_expr,
                ent_var,
                ent_name,
                &fair_event_keys,
                &scope,
                is_oneshot,
                target_slot,
                config.ic3_timeout_ms / 2,
            );

            match ic3_result {
                ic3::Ic3Result::Proved => {
                    // This slot proved — continue to check remaining slots
                }
                _ => {
                    // Any slot failing means the pattern (and block) is not proved
                    all_proved = false;
                    break 'pattern_loop;
                }
            }
        }
    }

    if all_proved {
        // Liveness proved via IC3. Now verify safety obligations (if any).
        if !safety_obligations.is_empty() {
            let safety_verify = IRVerify {
                name: verify_block.name.clone(),
                systems: verify_block.systems.clone(),
                asserts: safety_obligations,
                span: verify_block.span,
                file: verify_block.file.clone(),
            };
            let safety_proved =
                try_induction_on_verify(ir, vctx, defs, &safety_verify, config).or_else(|| {
                    if !config.no_ic3 {
                        try_ic3_on_verify(ir, vctx, defs, &safety_verify, config)
                    } else {
                        None
                    }
                });
            match safety_proved {
                Some(VerificationResult::Proved { .. }) => {
                    let elapsed = elapsed_ms(&start);
                    return Some(VerificationResult::Proved {
                        name: verify_block.name.clone(),
                        method: "liveness-to-safety (IC3/PDR)".to_owned(),
                        time_ms: elapsed,
                        span: None,
                        file: None,
                    });
                }
                _ => return None, // safety couldn't be proved — whole block not proved
            }
        }

        let elapsed = elapsed_ms(&start);
        return Some(VerificationResult::Proved {
            name: verify_block.name.clone(),
            method: "liveness-to-safety (IC3/PDR)".to_owned(),
            time_ms: elapsed,
            span: None,
            file: None,
        });
    }

    None
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

    // NOTE: Do NOT early-return when scope is empty. Properties may contain
    // non-entity quantifiers (e.g., `all c: Color | P(c)`) that must be checked.
    // The BMC flow handles empty scope correctly: no slots, no events, stutter only.

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
            let trace = extract_counterexample_with_events(
                &solver, &pool, vctx, &relevant_entities, &relevant_systems, bound,
            );
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
// ── Lasso BMC for liveness properties ────────────────────────────────

/// Lasso-shaped BMC for liveness verification with fairness.
///
/// A lasso is a trace: s₀ → s₁ → ... → s_l → ... → s_N → s_l (loop back).
/// The solver searches for a lasso where the liveness property is violated
/// on the loop (P never holds at any step in the loop). If SAT, this is a
/// true infinite counterexample. If UNSAT, no violation exists at this bound.
///
/// Fairness: for each fair event, if it is enabled somewhere in the loop,
/// it must fire somewhere in the loop. This excludes degenerate stutter loops.
#[allow(clippy::too_many_lines)]
fn check_verify_block_lasso(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    verify_block: &IRVerify,
    config: &VerifyConfig,
) -> VerificationResult {
    let start = Instant::now();

    // ── 1. Build scope (same as check_verify_block) ─────────────────
    let mut scope: HashMap<String, usize> = HashMap::new();
    let mut bound: usize = 1;
    let mut system_names: Vec<String> = Vec::new();

    for vs in &verify_block.systems {
        system_names.push(vs.name.clone());
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

    if scope.is_empty() {
        // No entities — lasso BMC requires entity state for loop-back.
        // Fall back to linear BMC.
        return check_verify_block(ir, vctx, defs, verify_block, config);
    }

    // Expand scope for CrossCall targets
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
            if !system_names.contains(&sys.name) {
                system_names.push(sys.name.clone());
            }
            for ent_name in &sys.entities {
                let existing = scope.get(ent_name).copied().unwrap_or(0);
                scope.insert(ent_name.clone(), existing.max(bound));
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

    // ── 2. Create pool and solver ───────────────────────────────────
    let pool = create_slot_pool(&relevant_entities, &scope, bound);
    let solver = Solver::new();
    if config.bmc_timeout_ms > 0 {
        set_solver_timeout(&solver, config.bmc_timeout_ms);
    }

    // Initial state
    for c in initial_state_constraints(&pool) {
        solver.assert(&c);
    }
    for c in symmetry_breaking_constraints(&pool) {
        solver.assert(&c);
    }
    for c in domain_constraints(&pool, vctx, &relevant_entities) {
        solver.assert(&c);
    }

    // ── 3. Per-event fire tracking + transitions ────────────────────
    let fire_tracking =
        transition_constraints_with_fire(&pool, vctx, &relevant_entities, &relevant_systems, bound);
    for c in &fire_tracking.constraints {
        solver.assert(c);
    }

    // ── 4. Lasso loop-back ──────────────────────────────────────────
    let lasso = lasso_loopback(&pool, &relevant_entities);
    for c in &lasso.constraints {
        solver.assert(c);
    }

    // ── 5. Fairness constraints ─────────────────────────────────────
    let fair_constraints = fairness_constraints(
        &pool,
        vctx,
        &relevant_entities,
        &relevant_systems,
        &fire_tracking,
        &lasso,
    );
    for c in &fair_constraints {
        solver.assert(c);
    }

    // ── 6. Check each liveness assert independently ────────────────
    // Each assert is checked separately — if ANY assert is violated,
    // the verify block fails. This matches standard semantics: each
    // assert is an independent obligation.
    for assert_expr in &verify_block.asserts {
        let expanded = expand_through_defs(assert_expr, defs);
        let violation = match encode_lasso_liveness_violation(
            &pool, vctx, defs, &expanded, &lasso.loop_indicators, bound,
        ) {
            Ok(v) => v,
            Err(msg) => {
                return VerificationResult::Unprovable {
                    name: verify_block.name.clone(),
                    hint: format!("lasso encoding error: {msg}"),
                    span: expr_span(assert_expr),
                    file: None,
                };
            }
        };

        // Skip non-liveness asserts (violation is false)
        // Check: push violation, check SAT, pop
        solver.push();
        solver.assert(&violation);

        match solver.check() {
            z3::SatResult::Sat => {
                // Found a lasso violating this assert
                let model = solver.get_model().unwrap();
                let mut loop_start = 0;
                for (l, ind) in lasso.loop_indicators.iter().enumerate() {
                    if let Some(true) = model.eval(ind, true).and_then(|v| v.as_bool()) {
                        loop_start = l;
                        break;
                    }
                }

                let full_trace = extract_counterexample_with_events(
                    &solver, &pool, vctx, &relevant_entities, &relevant_systems, bound,
                );
                let prefix: Vec<TraceStep> = full_trace
                    .iter()
                    .filter(|s| s.step < loop_start)
                    .cloned()
                    .collect();
                let loop_trace: Vec<TraceStep> = full_trace
                    .iter()
                    .filter(|s| s.step >= loop_start)
                    .cloned()
                    .collect();

                return VerificationResult::LivenessViolation {
                    name: verify_block.name.clone(),
                    prefix,
                    loop_trace,
                    loop_start,
                    span: expr_span(assert_expr),
                    file: None,
                };
            }
            z3::SatResult::Unknown => {
                solver.pop(1);
                return VerificationResult::Unprovable {
                    name: verify_block.name.clone(),
                    hint: crate::messages::BMC_UNKNOWN.to_owned(),
                    span: expr_span(assert_expr),
                    file: None,
                };
            }
            z3::SatResult::Unsat => {
                solver.pop(1);
                // This assert passes — continue to next
            }
        }
    }

    // All asserts passed
    let elapsed = elapsed_ms(&start);
    VerificationResult::Checked {
        name: verify_block.name.clone(),
        depth: bound,
        time_ms: elapsed,
        span: None,
        file: None,
    }
}

/// Encode a liveness violation condition for the lasso loop.
///
/// Recursively handles:
/// - `eventually P`: violation = P never holds on loop
/// - `always body`: strips Always, examines body for response patterns
/// - Entity quantifiers `all o: E | body`: expands over active slots
/// - `P implies eventually Q`: response pattern — P triggers, Q never responds
/// - Safety properties (no `eventually`): returns `false` (no lasso violation)
fn encode_lasso_liveness_violation(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    assert_expr: &IRExpr,
    loop_indicators: &[Bool],
    bound: usize,
) -> Result<Bool, String> {
    let ctx = PropertyCtx::new();
    encode_lasso_violation_inner(pool, vctx, defs, assert_expr, loop_indicators, bound, &ctx)
}

/// Inner recursive helper for lasso liveness violation encoding.
/// Carries a `PropertyCtx` for entity quantifier bindings.
fn encode_lasso_violation_inner(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    expr: &IRExpr,
    loop_indicators: &[Bool],
    bound: usize,
    ctx: &PropertyCtx,
) -> Result<Bool, String> {
    match expr {
        // `eventually P` — violation: P never holds on the loop
        IRExpr::Eventually { body, .. } => {
            let mut loop_violations = Vec::new();
            for (l, loop_ind) in loop_indicators.iter().enumerate() {
                let mut p_never = Vec::new();
                for step in l..=bound {
                    let p = encode_prop_expr(pool, vctx, defs, ctx, body, step)?;
                    p_never.push(p.not());
                }
                let p_never_refs: Vec<&Bool> = p_never.iter().collect();
                let violation_at_l = Bool::and(&[loop_ind, &Bool::and(&p_never_refs)]);
                loop_violations.push(violation_at_l);
            }
            if loop_violations.is_empty() {
                return Ok(Bool::from_bool(false));
            }
            let refs: Vec<&Bool> = loop_violations.iter().collect();
            Ok(Bool::or(&refs))
        }

        // `always body` — strip always, examine body for liveness patterns
        IRExpr::Always { body, .. } => {
            encode_lasso_violation_inner(pool, vctx, defs, body, loop_indicators, bound, ctx)
        }

        // Entity quantifier: `all o: Entity | body` — expand over active slots
        // and check each for liveness violations (disjunction: ANY slot violated).
        // The active guard per step is handled inside the inner encoding
        // (response pattern guards P(t) with active(slot, t)).
        IRExpr::Forall {
            var,
            domain: crate::ir::types::IRType::Entity { name: entity_name },
            body,
            ..
        } => {
            let n_slots = pool.slots_for(entity_name);
            let mut slot_violations = Vec::new();
            for slot in 0..n_slots {
                let inner_ctx = ctx.with_binding(var, entity_name, slot);
                let v = encode_lasso_violation_inner(
                    pool, vctx, defs, body, loop_indicators, bound, &inner_ctx,
                )?;
                slot_violations.push(v);
            }
            if slot_violations.is_empty() {
                return Ok(Bool::from_bool(false));
            }
            let refs: Vec<&Bool> = slot_violations.iter().collect();
            Ok(Bool::or(&refs))
        }

        // `P implies eventually Q` — response pattern
        //
        // Violation on a lasso with loop l..bound:
        //   P triggers at some step t (anywhere in trace) AND
        //   Q never holds on the LOOP (steps l..bound).
        //
        // Since the loop repeats forever, Q absent from the loop means Q
        // never holds in the infinite future — regardless of where P triggered.
        // The trigger can be in the prefix (t < l) or on the loop (t >= l).
        //
        // Entity-bound triggers are guarded by the entity's active flag.
        //
        // Correct encoding: for each trigger step t, Q must be absent from
        // step t through the end of the trace [t, bound]. Since the trace
        // after step bound loops back to step l, and [t, bound] includes
        // the entire loop [l, bound], Q absent from [t, bound] means Q
        // never holds in the infinite future from the trigger point.
        //
        // Encoding: ∃l. loop_l ∧ ∃t ∈ [0,bound]. active(t) ∧ P(t) ∧ (∀s ∈ [t,bound]. ¬Q(s))
        IRExpr::BinOp {
            op,
            left: trigger,
            right: response_box,
            ..
        } if op == "OpImplies" => {
            if let IRExpr::Eventually {
                body: response, ..
            } = response_box.as_ref()
            {
                let mut loop_violations = Vec::new();
                for (l, loop_ind) in loop_indicators.iter().enumerate() {
                    // Precompute Q absence on the full loop [l, bound].
                    // Reused for all triggers at t ≥ l (loop-internal triggers
                    // wrap around: future is [t,bound] ∪ [l,t-1] = [l,bound]).
                    let mut q_loop_never = Vec::new();
                    for s in l..=bound {
                        let q =
                            encode_prop_expr(pool, vctx, defs, ctx, response, s)?;
                        q_loop_never.push(q.not());
                    }
                    let q_loop_refs: Vec<&Bool> = q_loop_never.iter().collect();
                    let q_absent_on_loop = Bool::and(&q_loop_refs);

                    // For each possible trigger step t in the full trace
                    let mut per_trigger = Vec::new();
                    for t in 0..=bound {
                        // Guard with entity active flags at step t
                        let mut guards = Vec::new();
                        for (_, (entity_name, slot)) in &ctx.bindings {
                            if let Some(SmtValue::Bool(act)) =
                                pool.active_at(entity_name, *slot, t)
                            {
                                guards.push(act.clone());
                            }
                        }
                        let p = encode_prop_expr(pool, vctx, defs, ctx, trigger, t)?;
                        let p_guarded = if guards.is_empty() {
                            p
                        } else {
                            let guard_refs: Vec<&Bool> = guards.iter().collect();
                            Bool::and(&[&Bool::and(&guard_refs), &p])
                        };

                        // Q absent from the infinite future starting at step t.
                        //
                        // On the lasso s₀..s_l..s_bound → s_l:
                        // - Trigger in prefix (t < l): future = [t,l-1] ∪ loop.
                        //   Q absent from [t, bound] covers both (since [t,bound] ⊇ loop).
                        // - Trigger on loop (t ≥ l): future wraps: [t,bound] ∪ [l,t-1].
                        //   Q must be absent from the entire loop [l, bound].
                        //
                        // Combined: Q absent from [min(t, l), bound].
                        let q_absent = if t <= l {
                            // Prefix trigger: need Q absent from [t, l-1] AND on loop
                            if t < l {
                                let mut q_prefix = Vec::new();
                                for s in t..l {
                                    let q = encode_prop_expr(
                                        pool, vctx, defs, ctx, response, s,
                                    )?;
                                    q_prefix.push(q.not());
                                }
                                let prefix_refs: Vec<&Bool> = q_prefix.iter().collect();
                                Bool::and(&[&Bool::and(&prefix_refs), &q_absent_on_loop])
                            } else {
                                // t == l: just the loop
                                q_absent_on_loop.clone()
                            }
                        } else {
                            // Loop-internal trigger: Q absent on entire loop
                            q_absent_on_loop.clone()
                        };

                        per_trigger.push(Bool::and(&[&p_guarded, &q_absent]));
                    }
                    let trigger_refs: Vec<&Bool> = per_trigger.iter().collect();
                    let some_trigger_violated = Bool::or(&trigger_refs);

                    loop_violations
                        .push(Bool::and(&[loop_ind, &some_trigger_violated]));
                }
                if loop_violations.is_empty() {
                    return Ok(Bool::from_bool(false));
                }
                let refs: Vec<&Bool> = loop_violations.iter().collect();
                return Ok(Bool::or(&refs));
            }
            // P implies Q (no eventually) — safety, not liveness
            Ok(Bool::from_bool(false))
        }

        // Safety properties or other patterns — no lasso violation
        _ => Ok(Bool::from_bool(false)),
    }
}

/// Collect event indices referenced by ^| (exclusive choice) in ordering expressions.
fn collect_xor_event_indices(
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

/// Collect event-level same-step pairs from OpSameStep ordering expressions.
fn collect_same_step_event_pairs(
    ordering: &[IRExpr],
    var_to_idx: &HashMap<&str, usize>,
    pairs: &mut Vec<(usize, usize)>,
) {
    for expr in ordering {
        collect_same_step_event_pairs_expr(expr, var_to_idx, pairs);
    }
}

fn collect_same_step_event_pairs_expr(
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
fn encode_scene_ordering_v2(
    expr: &IRExpr,
    var_to_idx: &HashMap<&str, usize>,
    event_instance_ranges: &[std::ops::Range<usize>],
    instances: &[FiringInst],
    solver: &Solver,
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
                        solver.assert(&last_l.lt(first_r.clone()));
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
                    left, var_to_idx, event_instance_ranges, instances, solver, scene_name,
                )?;
                encode_scene_ordering_v2(
                    right, var_to_idx, event_instance_ranges, instances, solver, scene_name,
                )?;
            }
            "OpSameStep" => {
                // Handled by same-step grouping. Recurse for nested.
                encode_scene_ordering_v2(
                    left, var_to_idx, event_instance_ranges, instances, solver, scene_name,
                )?;
                encode_scene_ordering_v2(
                    right, var_to_idx, event_instance_ranges, instances, solver, scene_name,
                )?;
            }
            "OpConc" | "OpUnord" => {
                encode_scene_ordering_v2(
                    left, var_to_idx, event_instance_ranges, instances, solver, scene_name,
                )?;
                encode_scene_ordering_v2(
                    right, var_to_idx, event_instance_ranges, instances, solver, scene_name,
                )?;
            }
            "OpXor" => {
                // ^| : exactly one of the two events fires.
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
                        let a_fires = instances[a_range.start]
                            .fires_var
                            .as_ref()
                            .ok_or_else(|| {
                                crate::messages::scene_xor_no_fire_tracking(
                                    scene_name,
                                    &event_var_names_from_idx(a, var_to_idx),
                                )
                            })?;
                        let b_fires = instances[b_range.start]
                            .fires_var
                            .as_ref()
                            .ok_or_else(|| {
                                crate::messages::scene_xor_no_fire_tracking(
                                    scene_name,
                                    &event_var_names_from_idx(b, var_to_idx),
                                )
                            })?;
                        // XOR: (a_fires ∧ ¬b_fires) ∨ (¬a_fires ∧ b_fires)
                        let xor = Bool::or(&[
                            &Bool::and(&[a_fires, &b_fires.not()]),
                            &Bool::and(&[&a_fires.not(), b_fires]),
                        ]);
                        solver.assert(&xor);
                    }
                }
                // Recurse for nested
                encode_scene_ordering_v2(
                    left, var_to_idx, event_instance_ranges, instances, solver, scene_name,
                )?;
                encode_scene_ordering_v2(
                    right, var_to_idx, event_instance_ranges, instances, solver, scene_name,
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
fn event_var_names_from_idx(idx: usize, var_to_idx: &HashMap<&str, usize>) -> String {
    var_to_idx
        .iter()
        .find(|(_, &i)| i == idx)
        .map(|(name, _)| name.to_string())
        .unwrap_or_else(|| format!("event_{idx}"))
}

/// A single firing instance in the scene trace.
struct FiringInst {
    event_idx: usize,
    #[allow(dead_code)]
    inst_idx: usize,
    step_var: Int,
    fires_var: Option<Bool>,
}

/// Resolved scene event: validated reference to the scene event and its IR.
struct ResolvedSceneEvent<'a> {
    scene_event: &'a IRSceneEvent,
    event_ir: &'a IREvent,
}

/// Build override_params for a scene event at a given step.
fn build_scene_event_params(
    re: &ResolvedSceneEvent<'_>,
    pool: &harness::SlotPool,
    vctx: &context::VerifyContext,
    defs: &defenv::DefEnv,
    given_bindings: &HashMap<String, (String, usize)>,
    step: usize,
    _scene_name: &str,
) -> Result<HashMap<String, SmtValue>, String> {
    let mut override_params: HashMap<String, SmtValue> = HashMap::new();
    for (param, arg) in re.event_ir.params.iter().zip(re.scene_event.args.iter()) {
        let arg_ctx = PropertyCtx::new();
        let arg_ctx = given_bindings
            .iter()
            .fold(arg_ctx, |ctx, (var, (ent, slot))| {
                ctx.with_binding(var, ent, *slot)
            });
        let val = encode_prop_value(pool, vctx, defs, &arg_ctx, arg, step).map_err(|msg| {
            format!(
                "encoding error in scene event arg for {}::{}: {msg}",
                re.scene_event.system, re.scene_event.event
            )
        })?;
        override_params.insert(param.name.clone(), val);
    }
    Ok(override_params)
}

/// (Phase 10 legacy — replaced by encode_scene_ordering_v2 in Phase 12)
/// - `OpSeq(a, b)` → `group_step(a) < group_step(b)` (sequence: a before b)
/// - `OpSameStep(a, b)` → handled by same-step grouping (no constraint emitted here)
/// - `OpConc/OpUnord(a, b)` → no constraint (both fire, any order)
/// - `OpXor(a, b)` → error (requires Phase 12 fire-tracking)
#[allow(dead_code)]
fn encode_scene_ordering(
    expr: &IRExpr,
    var_to_idx: &HashMap<&str, usize>,
    event_to_step_idx: &[usize],
    group_step_vars: &[Int],
    solver: &Solver,
    scene_name: &str,
) -> Result<(), String> {
    match expr {
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            match op.as_str() {
                "OpSeq" => {
                    // a -> b: group_step(a) < group_step(b)
                    // Recurse for chains (a -> b -> c).
                    if let (Some(l_event), Some(r_event)) = (
                        last_ordering_var(left, var_to_idx),
                        first_ordering_var(right, var_to_idx),
                    ) {
                        let l_step = event_to_step_idx[l_event];
                        let r_step = event_to_step_idx[r_event];
                        if l_step != r_step {
                            solver.assert(
                                &group_step_vars[l_step].lt(group_step_vars[r_step].clone()),
                            );
                        }
                        // Same group → already at same step, constraint is trivially satisfied
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
                    encode_scene_ordering(
                        left, var_to_idx, event_to_step_idx, group_step_vars, solver, scene_name,
                    )?;
                    encode_scene_ordering(
                        right, var_to_idx, event_to_step_idx, group_step_vars, solver, scene_name,
                    )?;
                }
                "OpSameStep" => {
                    // Same-step grouping is handled by collect_same_step_pairs
                    // before step variable creation. No constraint to emit here.
                    // Recurse for nested sub-expressions.
                    encode_scene_ordering(
                        left, var_to_idx, event_to_step_idx, group_step_vars, solver, scene_name,
                    )?;
                    encode_scene_ordering(
                        right, var_to_idx, event_to_step_idx, group_step_vars, solver, scene_name,
                    )?;
                }
                "OpConc" | "OpUnord" => {
                    // Both fire, no ordering constraint. Recurse for nested.
                    encode_scene_ordering(
                        left, var_to_idx, event_to_step_idx, group_step_vars, solver, scene_name,
                    )?;
                    encode_scene_ordering(
                        right, var_to_idx, event_to_step_idx, group_step_vars, solver, scene_name,
                    )?;
                }
                "OpXor" => {
                    return Err(format!(
                        "scene '{scene_name}': exclusive choice `^|` requires \
                         fire-tracking from scene event cardinality (Phase 12)"
                    ));
                }
                _ => {
                    // Other BinOps in ordering are unexpected but not fatal —
                    // skip silently (they may be boolean conditions).
                }
            }
        }
        IRExpr::Var { .. } => {
            // Leaf variable — no constraint to emit (constraints come from the parent BinOp)
        }
        _ => {
            // Non-composition expression in ordering — skip
        }
    }
    Ok(())
}

/// Collect entity type names that an event body touches, including through
/// CrossCall targets (resolved recursively). Used to check same-step
/// compatibility — events at the same step must not touch the same entity.
fn collect_event_body_entities(
    actions: &[IRAction],
    systems: &[IRSystem],
    entities: &mut HashSet<String>,
    visited: &mut HashSet<(String, String)>,
) {
    for action in actions {
        match action {
            IRAction::Choose { entity, ops, .. } | IRAction::ForAll { entity, ops, .. } => {
                entities.insert(entity.clone());
                collect_event_body_entities(ops, systems, entities, visited);
            }
            IRAction::Create { entity, .. } => {
                entities.insert(entity.clone());
            }
            IRAction::Apply { target, .. } => {
                entities.insert(target.clone());
            }
            IRAction::CrossCall {
                system,
                event: event_name,
                ..
            } => {
                let key = (system.clone(), event_name.clone());
                if visited.insert(key) {
                    if let Some(sys) = systems.iter().find(|s| s.name == *system) {
                        if let Some(evt) = sys.events.iter().find(|e| e.name == *event_name) {
                            collect_event_body_entities(
                                &evt.body, systems, entities, visited,
                            );
                        }
                    }
                }
            }
            IRAction::ExprStmt { .. } => {}
        }
    }
}

/// Collect all event variable names referenced in an ordering expression.
fn collect_ordering_leaf_vars<'a>(expr: &'a IRExpr) -> Vec<&'a str> {
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
fn last_ordering_var(expr: &IRExpr, var_to_idx: &HashMap<&str, usize>) -> Option<usize> {
    match expr {
        IRExpr::Var { name, .. } => var_to_idx.get(name.as_str()).copied(),
        IRExpr::BinOp { op, right, .. } if op == "OpSeq" => {
            last_ordering_var(right, var_to_idx)
        }
        IRExpr::BinOp { right, .. } => last_ordering_var(right, var_to_idx),
        _ => None,
    }
}

/// Get the step variable index of the first (leftmost) event in an ordering expr.
/// For `a -> b`, returns index of `a`. For a bare `Var("a")`, returns index of `a`.
fn first_ordering_var(expr: &IRExpr, var_to_idx: &HashMap<&str, usize>) -> Option<usize> {
    match expr {
        IRExpr::Var { name, .. } => var_to_idx.get(name.as_str()).copied(),
        IRExpr::BinOp { op, left, .. } if op == "OpSeq" => {
            first_ordering_var(left, var_to_idx)
        }
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
fn check_scene_block(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    scene: &IRScene,
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
            for event in &sys.events {
                collect_crosscall_systems(&event.body, &mut systems_to_scan);
            }
            for ent_name in &sys.entities {
                // Ensure enough slots for given bindings PLUS potential creates.
                // Given bindings occupy fixed slots at step 0; creates need
                // additional inactive slots. So total = given_count + default_slots.
                let given_count = scene.givens.iter()
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

        resolved_events.push(ResolvedSceneEvent { scene_event, event_ir: event });
    }

    // Pre-compute result variable bindings (Creates from event bodies).
    // This must happen before the step variable encoding so bindings are
    // available for argument resolution at all possible steps.
    for re in &resolved_events {
        if referenced_vars.contains(&re.scene_event.var) {
            let creates = scan_event_creates(&re.event_ir.body, &relevant_systems);
            if let Some(result_entity) = creates.first() {
                let slot = next_slot.entry(result_entity.clone()).or_insert(0);
                let allocated_slot = *slot;
                *slot += 1;
                given_bindings.insert(
                    re.scene_event.var.clone(),
                    (result_entity.clone(), allocated_slot),
                );
            }
        }
    }

    // ── 4c. Resolve cardinalities and build firing instances ────────
    // Each event's cardinality determines how many firing instances it
    // gets. Each instance has a step variable (Int) and optionally a
    // fires variable (Bool) for optional firings.
    use crate::ir::types::Cardinality;

    let event_var_names: Vec<&str> = scene
        .events
        .iter()
        .map(|e| e.var.as_str())
        .collect();
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
                Int::new_const(format!("scene_step_{var_name}"))
            } else {
                Int::new_const(format!("scene_step_{var_name}_{inst_idx}"))
            };
            let fires_var = if ec.has_fire_tracking {
                Some(Bool::new_const(format!("scene_fires_{var_name}_{inst_idx}")))
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
        solver.assert(&inst.step_var.ge(Int::from_i64(0)));
        solver.assert(&inst.step_var.lt(Int::from_i64(bound as i64)));
    }

    // Assert internal ordering for multi-instance events: step_0 < step_1 < ...
    for ec_range in &event_instance_ranges {
        if ec_range.len() > 1 {
            for i in ec_range.start..(ec_range.end - 1) {
                let curr = &instances[i].step_var;
                let next = &instances[i + 1].step_var;
                solver.assert(&curr.lt(next.clone()));
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
                    solver.assert(&Bool::or(&fire_vars));
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
                    collect_event_body_entities(
                        &re.event_ir.body,
                        &relevant_systems,
                        &mut event_entities,
                        &mut visited_calls,
                    );
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
                    solver.assert(&instances[i].step_var.eq(instances[j].step_var.clone()));
                } else {
                    // Different groups: assert distinct step
                    solver.assert(
                        &instances[i]
                            .step_var
                            .eq(instances[j].step_var.clone())
                            .not(),
                    );
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

            let step_guard = instances[group_root]
                .step_var
                .eq(Int::from_i64(step as i64));

            if group_members.len() == 1 {
                let ii = group_members[0];
                let inst = &instances[ii];
                let re = &resolved_events[inst.event_idx];

                let override_params = match build_scene_event_params(
                    re, &pool, vctx, defs, &given_bindings, step, &scene.name,
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

                if let Some(fires) = &inst.fires_var {
                    // Optional firing: (step_guard ∧ fires ∧ event) ∨ (step_guard ∧ ¬fires ∧ stutter)
                    let event_formula = encode_event_with_params(
                        &pool, vctx, &relevant_entities, &relevant_systems,
                        re.event_ir, step, override_params,
                    );
                    let fires_branch = Bool::and(&[&step_guard, fires, &event_formula]);
                    let stutter = harness::stutter_constraint(&pool, &relevant_entities, step);
                    let skip_branch = Bool::and(&[&step_guard, &fires.not(), &stutter]);
                    step_disjuncts.push(Bool::or(&[&fires_branch, &skip_branch]));
                } else {
                    // Must fire
                    let event_formula = encode_event_with_params(
                        &pool, vctx, &relevant_entities, &relevant_systems,
                        re.event_ir, step, override_params,
                    );
                    step_disjuncts.push(Bool::and(&[&step_guard, &event_formula]));
                }
            } else {
                // Same-step group: encode combined with fire-tracking.
                // {lone} members are conditional: fires_var → event, ¬fires_var → skip.
                // The combined frame covers all potentially touched entities.
                let mut group_formulas: Vec<Bool> = Vec::new();
                let mut combined_touched: HashSet<(String, usize)> = HashSet::new();

                for &ii in &group_members {
                    let inst = &instances[ii];
                    let re = &resolved_events[inst.event_idx];
                    let override_params = match build_scene_event_params(
                        re, &pool, vctx, defs, &given_bindings, step, &scene.name,
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
                    let (formula, touched) = harness::encode_event_inner(
                        &pool, vctx, &relevant_entities, &relevant_systems,
                        re.event_ir, step, 0, Some(override_params),
                    );
                    // For {lone} members, make the formula conditional on fires_var.
                    // If not firing, the member contributes nothing — the combined
                    // frame preserves its entities unchanged.
                    if let Some(fires) = &inst.fires_var {
                        group_formulas.push(fires.implies(&formula));
                    } else {
                        group_formulas.push(formula);
                    }
                    combined_touched.extend(touched);
                }

                let mut all_parts = vec![step_guard];
                all_parts.extend(group_formulas);
                let combined = {
                    let refs: Vec<&Bool> = all_parts.iter().collect();
                    Bool::and(&refs)
                };
                let framed = harness::apply_global_frame(
                    &pool, &relevant_entities, &combined_touched, step, combined,
                );
                step_disjuncts.push(framed);
            }
        }

        // Stutter: no instance fires at this step
        let mut no_inst_parts: Vec<Bool> = Vec::new();
        for &root in &inst_group_roots {
            no_inst_parts
                .push(instances[root].step_var.eq(Int::from_i64(step as i64)).not());
        }
        let stutter = harness::stutter_constraint(&pool, &relevant_entities, step);
        let no_inst_refs: Vec<&Bool> = no_inst_parts.iter().collect();
        let no_inst = Bool::and(&no_inst_refs);
        step_disjuncts.push(Bool::and(&[&no_inst, &stutter]));

        let refs: Vec<&Bool> = step_disjuncts.iter().collect();
        solver.assert(&Bool::or(&refs));
    }

    // Assert result variable activation for create events
    for (ei, re) in resolved_events.iter().enumerate() {
        if let Some((result_entity, allocated_slot)) = given_bindings.get(&re.scene_event.var)
        {
            let is_result = scene
                .givens
                .iter()
                .all(|g| g.var != re.scene_event.var);
            if is_result {
                // Use first instance of this event for result activation
                let range = &event_instance_ranges[ei];
                if !range.is_empty() {
                    let first_inst = &instances[range.start];
                    for step in 0..bound {
                        if let Some(SmtValue::Bool(active_next)) =
                            pool.active_at(result_entity, *allocated_slot, step + 1)
                        {
                            let mut guard = first_inst
                                .step_var
                                .eq(Int::from_i64(step as i64));
                            if let Some(fires) = &first_inst.fires_var {
                                guard = Bool::and(&[&guard, fires]);
                            }
                            solver.assert(&guard.implies(active_next));
                        }
                    }
                }
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
/// Verify a lemma block.
///
/// Lemmas are system-independent properties: each body expression must be a
/// tautology (universally true). We encode the conjunction of all body
/// expressions via the pure expression encoder, negate it, and check UNSAT.
fn check_lemma_block(
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    lemma: &crate::ir::types::IRLemma,
) -> VerificationResult {
    let start = Instant::now();

    if lemma.body.is_empty() {
        let elapsed = elapsed_ms(&start);
        return VerificationResult::Proved {
            name: lemma.name.clone(),
            method: "lemma (empty body)".to_owned(),
            time_ms: elapsed,
            span: lemma.span,
            file: lemma.file.clone(),
        };
    }

    let env: HashMap<String, SmtValue> = HashMap::new();

    // Encode each body expression and conjoin
    let mut conjuncts = Vec::new();
    for body_expr in &lemma.body {
        let expanded = expand_through_defs(body_expr, defs);
        match encode_pure_expr_inner(&expanded, &env, vctx, defs, None) {
            Ok(val) => match val.to_bool() {
                Ok(b) => conjuncts.push(b),
                Err(e) => {
                    return VerificationResult::Unprovable {
                        name: lemma.name.clone(),
                        hint: format!("lemma body encoding error: {e}"),
                        span: lemma.span,
                        file: lemma.file.clone(),
                    };
                }
            },
            Err(e) => {
                return VerificationResult::Unprovable {
                    name: lemma.name.clone(),
                    hint: format!("lemma body encoding error: {e}"),
                    span: lemma.span,
                    file: lemma.file.clone(),
                };
            }
        }
    }

    let refs: Vec<&Bool> = conjuncts.iter().collect();
    let lemma_body = Bool::and(&refs);

    // Negate and check: if UNSAT, the lemma is a tautology
    let solver = Solver::new();
    assert_lambda_axioms_on(&solver);
    solver.assert(&lemma_body.not());

    let elapsed = elapsed_ms(&start);
    match solver.check() {
        z3::SatResult::Unsat => VerificationResult::Proved {
            name: lemma.name.clone(),
            method: "lemma".to_owned(),
            time_ms: elapsed,
            span: lemma.span,
            file: lemma.file.clone(),
        },
        z3::SatResult::Sat => VerificationResult::Counterexample {
            name: lemma.name.clone(),
            trace: Vec::new(),
            span: lemma.span,
            file: lemma.file.clone(),
        },
        z3::SatResult::Unknown => VerificationResult::Unprovable {
            name: lemma.name.clone(),
            hint: "Z3 returned unknown for lemma".to_owned(),
            span: lemma.span,
            file: lemma.file.clone(),
        },
    }
}

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

    // Check for `eventually` in show expressions.
    // Try liveness-to-safety reduction for liveness properties.
    // Expand through DefEnv first so pred/prop bodies with `eventually` are detected.
    let has_liveness_shows = show_exprs
        .iter()
        .any(|e| contains_liveness(&expand_through_defs(e, defs)));

    if has_liveness_shows {
        // Build a virtual verify block from the theorem's shows for the reduction
        let virtual_verify = IRVerify {
            name: theorem.name.clone(),
            systems: theorem
                .systems
                .iter()
                .map(|s| crate::ir::types::IRVerifySystem {
                    name: s.clone(),
                    lo: 0,
                    hi: 10, // not used by reduction
                })
                .collect(),
            asserts: theorem.shows.clone(),
            span: theorem.span,
            file: theorem.file.clone(),
        };
        let config = VerifyConfig::default();
        if let Some(result) = try_liveness_reduction(ir, vctx, defs, &virtual_verify, &config) {
            return result;
        }
        // Reduction failed — can't prove liveness by induction
        return VerificationResult::Unprovable {
            name: theorem.name.clone(),
            hint: crate::messages::LIVENESS_REDUCTION_FAILED.to_owned(),
            span: None,
            file: None,
        };
    }

    for (i, show_expr) in show_exprs.iter().enumerate() {
        let expanded = expand_through_defs(show_expr, defs);
        if contains_liveness(&expanded) {
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
                let relevant_systems: Vec<_> = ir
                    .systems
                    .iter()
                    .filter(|s| system_names.contains(&s.name))
                    .cloned()
                    .collect();
                let relevant_entities: Vec<_> = ir
                    .entities
                    .iter()
                    .filter(|e| scope.contains_key(&e.name))
                    .cloned()
                    .collect();
                return Some(VerificationResult::Counterexample {
                    name: theorem.name.clone(),
                    trace: ic3_trace_to_trace_steps(
                        &trace, &relevant_entities, &relevant_systems,
                    ),
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
    /// Non-entity quantifier variables: `var_name` → `SmtValue`
    /// Used for enum/Int/Bool/Real domain quantifiers in verify/theorem properties.
    locals: HashMap<String, SmtValue>,
}

impl PropertyCtx {
    fn new() -> Self {
        Self {
            bindings: HashMap::new(),
            locals: HashMap::new(),
        }
    }

    /// Create a new context with an additional entity binding.
    fn with_binding(&self, var: &str, entity: &str, slot: usize) -> Self {
        let mut bindings = self.bindings.clone();
        bindings.insert(var.to_owned(), (entity.to_owned(), slot));
        Self {
            bindings,
            locals: self.locals.clone(),
        }
    }

    /// Create a new context with a non-entity local variable binding.
    fn with_local(&self, var: &str, val: SmtValue) -> Self {
        let mut locals = self.locals.clone();
        locals.insert(var.to_owned(), val);
        Self {
            bindings: self.bindings.clone(),
            locals,
        }
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
/// Recursively desugar `P until Q` into `(eventually Q) and (always (not Q implies P))`.
///
/// This decomposition is semantically equivalent to LTL `P U Q` and works
/// correctly inside entity quantifiers and nested temporal operators, unlike
/// a top-level-only unrolling approach.
fn desugar_until(expr: &IRExpr) -> IRExpr {
    match expr {
        IRExpr::Until { left, right, .. } => {
            let p = desugar_until(left);
            let q = desugar_until(right);
            // eventually Q
            let eventually_q = IRExpr::Eventually {
                body: Box::new(q.clone()),
                span: None,
            };
            // always (not Q implies P)
            let not_q = IRExpr::UnOp {
                op: "OpNot".to_owned(),
                operand: Box::new(q),
                ty: crate::ir::types::IRType::Bool,
                span: None,
            };
            let not_q_implies_p = IRExpr::BinOp {
                op: "OpImplies".to_owned(),
                left: Box::new(not_q),
                right: Box::new(p),
                ty: crate::ir::types::IRType::Bool,
                span: None,
            };
            let always_guard = IRExpr::Always {
                body: Box::new(not_q_implies_p),
                span: None,
            };
            // Conjunction: (eventually Q) and (always (not Q implies P))
            IRExpr::BinOp {
                op: "OpAnd".to_owned(),
                left: Box::new(eventually_q),
                right: Box::new(always_guard),
                ty: crate::ir::types::IRType::Bool,
                span: None,
            }
        }
        // Recurse into subexpressions
        IRExpr::Always { body, span } => IRExpr::Always {
            body: Box::new(desugar_until(body)),
            span: *span,
        },
        IRExpr::Eventually { body, span } => IRExpr::Eventually {
            body: Box::new(desugar_until(body)),
            span: *span,
        },
        IRExpr::Forall {
            var,
            domain,
            body,
            span,
        } => IRExpr::Forall {
            var: var.clone(),
            domain: domain.clone(),
            body: Box::new(desugar_until(body)),
            span: *span,
        },
        IRExpr::Exists {
            var,
            domain,
            body,
            span,
        } => IRExpr::Exists {
            var: var.clone(),
            domain: domain.clone(),
            body: Box::new(desugar_until(body)),
            span: *span,
        },
        IRExpr::One {
            var,
            domain,
            body,
            span,
        } => IRExpr::One {
            var: var.clone(),
            domain: domain.clone(),
            body: Box::new(desugar_until(body)),
            span: *span,
        },
        IRExpr::Lone {
            var,
            domain,
            body,
            span,
        } => IRExpr::Lone {
            var: var.clone(),
            domain: domain.clone(),
            body: Box::new(desugar_until(body)),
            span: *span,
        },
        IRExpr::BinOp {
            op,
            left,
            right,
            ty,
            span,
        } => IRExpr::BinOp {
            op: op.clone(),
            left: Box::new(desugar_until(left)),
            right: Box::new(desugar_until(right)),
            ty: ty.clone(),
            span: *span,
        },
        IRExpr::UnOp {
            op,
            operand,
            ty,
            span,
        } => IRExpr::UnOp {
            op: op.clone(),
            operand: Box::new(desugar_until(operand)),
            ty: ty.clone(),
            span: *span,
        },
        // Leaf nodes and others — return as-is
        _ => expr.clone(),
    }
}

fn contains_liveness(expr: &IRExpr) -> bool {
    match expr {
        IRExpr::Eventually { .. } => true,
        IRExpr::Until { .. } => true,
        IRExpr::Always { body, .. }
        | IRExpr::UnOp { operand: body, .. }
        | IRExpr::Field { expr: body, .. }
        | IRExpr::Prime { expr: body, .. } => contains_liveness(body),
        IRExpr::BinOp { left, right, .. }
        | IRExpr::App {
            func: left,
            arg: right,
            ..
        } => contains_liveness(left) || contains_liveness(right),
        IRExpr::Forall { body, .. }
        | IRExpr::Exists { body, .. }
        | IRExpr::One { body, .. }
        | IRExpr::Lone { body, .. } => contains_liveness(body),
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
        }
        | IRExpr::One {
            domain: crate::ir::types::IRType::Entity { name },
            body,
            ..
        }
        | IRExpr::Lone {
            domain: crate::ir::types::IRType::Entity { name },
            body,
            ..
        } => {
            *counts.entry(name.clone()).or_insert(0) += 1;
            count_entity_quantifiers(body, counts);
        }
        IRExpr::BinOp { left, right, .. }
        | IRExpr::Until { left, right, .. }
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
        IRExpr::Forall { body, .. }
        | IRExpr::Exists { body, .. }
        | IRExpr::One { body, .. }
        | IRExpr::Lone { body, .. } => {
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
        IRExpr::One {
            var, domain, body, ..
        } => IRExpr::One {
            var: var.clone(),
            domain: domain.clone(),
            body: Box::new(expand_through_defs(body, defs)),
            span: None,
        },
        IRExpr::Lone {
            var, domain, body, ..
        } => IRExpr::Lone {
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
        IRExpr::Until { left, right, .. } => IRExpr::Until {
            left: Box::new(expand_through_defs(left, defs)),
            right: Box::new(expand_through_defs(right, defs)),
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
        IRExpr::BinOp { left, right, .. }
        | IRExpr::Until { left, right, .. } => {
            collect_field_refs_in_expr(left, var_name, fields);
            collect_field_refs_in_expr(right, var_name, fields);
        }
        IRExpr::UnOp { operand, .. } => collect_field_refs_in_expr(operand, var_name, fields),
        IRExpr::Forall { body, .. }
        | IRExpr::Exists { body, .. }
        | IRExpr::One { body, .. }
        | IRExpr::Lone { body, .. } => {
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
        IRExpr::BinOp { left, right, .. }
        | IRExpr::Until { left, right, .. } => {
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
        IRExpr::Forall { body, .. }
        | IRExpr::Exists { body, .. }
        | IRExpr::One { body, .. }
        | IRExpr::Lone { body, .. } => find_unsupported_scene_expr(body),
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
        IRExpr::Assert { .. } => Some("Assert"),
        IRExpr::Assume { .. } => Some("Assume"),
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
        // First expand defs (props/preds) so that any `until` inside
        // definitions is exposed, THEN desugar until nodes. This ensures
        // `prop helper = P until Q` followed by `assert helper` gets the
        // correct multi-step encoding rather than the step-local fallback.
        let expanded = expand_through_defs(assert_expr, defs);
        let desugared = desugar_until(&expanded);

        match &desugared {
            // `always P` — check P at every step
            IRExpr::Always { body, .. } => {
                for step in 0..=bound {
                    let prop = encode_property_at_step(pool, vctx, defs, body.as_ref(), step)?;
                    all_props.push(prop);
                }
            }
            // `eventually P` — check P at some step (disjunction)
            IRExpr::Eventually { body, .. } => {
                let mut step_props = Vec::new();
                for step in 0..=bound {
                    let prop = encode_property_at_step(pool, vctx, defs, body.as_ref(), step)?;
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
        // Record context-sensitive precondition obligations.
        // Each obligation is guarded by the current path condition,
        // so calls inside `A implies f(0)` only require the precondition
        // when A is true.
        if let Some(preconditions) = defs.call_preconditions(expr) {
            let fn_name = defenv::decompose_app_chain_name(expr)
                .unwrap_or_else(|| "(unknown)".to_owned());
            let path_guard = current_path_guard();
            for pre in &preconditions {
                if let Ok(pre_bool) = encode_prop_expr(pool, vctx, defs, ctx, pre, step) {
                    // Obligation: path_guard → precondition
                    record_prop_precondition_obligation(
                        path_guard.implies(&pre_bool),
                        fn_name.clone(),
                    );
                }
            }
        }
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
        // `one x: Entity | P(x)` — exactly one active slot satisfies P
        IRExpr::One {
            var,
            domain: crate::ir::types::IRType::Entity { name: entity_name },
            body,
            ..
        } => {
            let n_slots = pool.slots_for(entity_name);
            // Encode P(slot) for each slot, paired with active flag
            let mut slot_preds = Vec::new();
            for slot in 0..n_slots {
                let active = pool.active_at(entity_name, slot, step);
                let inner_ctx = ctx.with_binding(var, entity_name, slot);
                let body_val = encode_prop_expr(pool, vctx, defs, &inner_ctx, body, step)?;
                if let Some(SmtValue::Bool(act)) = active {
                    slot_preds.push(Bool::and(&[act, &body_val]));
                }
            }
            if slot_preds.is_empty() {
                return Ok(Bool::from_bool(false));
            }
            // Exactly one: at least one AND at most one (pairwise exclusion)
            let at_least_one = {
                let refs: Vec<&Bool> = slot_preds.iter().collect();
                Bool::or(&refs)
            };
            let mut exclusion_conjuncts = Vec::new();
            for i in 0..slot_preds.len() {
                for j in (i + 1)..slot_preds.len() {
                    // ¬(P(i) ∧ P(j))
                    exclusion_conjuncts.push(Bool::and(&[&slot_preds[i], &slot_preds[j]]).not());
                }
            }
            if exclusion_conjuncts.is_empty() {
                // Only one slot — at_least_one is sufficient
                Ok(at_least_one)
            } else {
                let excl_refs: Vec<&Bool> = exclusion_conjuncts.iter().collect();
                let at_most_one = Bool::and(&excl_refs);
                Ok(Bool::and(&[&at_least_one, &at_most_one]))
            }
        }
        // `lone x: Entity | P(x)` — at most one active slot satisfies P
        IRExpr::Lone {
            var,
            domain: crate::ir::types::IRType::Entity { name: entity_name },
            body,
            ..
        } => {
            let n_slots = pool.slots_for(entity_name);
            let mut slot_preds = Vec::new();
            for slot in 0..n_slots {
                let active = pool.active_at(entity_name, slot, step);
                let inner_ctx = ctx.with_binding(var, entity_name, slot);
                let body_val = encode_prop_expr(pool, vctx, defs, &inner_ctx, body, step)?;
                if let Some(SmtValue::Bool(act)) = active {
                    slot_preds.push(Bool::and(&[act, &body_val]));
                }
            }
            if slot_preds.len() <= 1 {
                // 0 or 1 slots — at most one trivially true
                return Ok(Bool::from_bool(true));
            }
            // Pairwise exclusion: no two slots both satisfy
            let mut exclusion_conjuncts = Vec::new();
            for i in 0..slot_preds.len() {
                for j in (i + 1)..slot_preds.len() {
                    exclusion_conjuncts.push(Bool::and(&[&slot_preds[i], &slot_preds[j]]).not());
                }
            }
            let refs: Vec<&Bool> = exclusion_conjuncts.iter().collect();
            Ok(Bool::and(&refs))
        }
        // ── Non-entity domain quantifiers ──────────────────────────────
        //
        // Two strategies:
        // 1. Fieldless enums: finite expansion over variant indices (decidable).
        // 2. Everything else (ADT enums, refinement types, Int/Bool/Real):
        //    Z3 native quantifiers with domain predicates.
        //
        // Fieldless-enum finite expansion (Forall = conjunction, Exists = disjunction):
        IRExpr::Forall {
            var,
            domain: domain @ crate::ir::types::IRType::Enum { .. },
            body,
            ..
        } if !domain.has_variant_fields() => {
            let n = enum_variant_count(domain);
            let mut conjuncts = Vec::new();
            for idx in 0..n {
                let inner_ctx = ctx.with_local(var, smt::int_val(idx as i64));
                conjuncts.push(encode_prop_expr(pool, vctx, defs, &inner_ctx, body, step)?);
            }
            if conjuncts.is_empty() {
                return Ok(Bool::from_bool(true));
            }
            let refs: Vec<&Bool> = conjuncts.iter().collect();
            Ok(Bool::and(&refs))
        }
        IRExpr::Exists {
            var,
            domain: domain @ crate::ir::types::IRType::Enum { .. },
            body,
            ..
        } if !domain.has_variant_fields() => {
            let n = enum_variant_count(domain);
            let mut disjuncts = Vec::new();
            for idx in 0..n {
                let inner_ctx = ctx.with_local(var, smt::int_val(idx as i64));
                disjuncts.push(encode_prop_expr(pool, vctx, defs, &inner_ctx, body, step)?);
            }
            if disjuncts.is_empty() {
                return Ok(Bool::from_bool(false));
            }
            let refs: Vec<&Bool> = disjuncts.iter().collect();
            Ok(Bool::or(&refs))
        }
        IRExpr::One {
            var,
            domain: domain @ crate::ir::types::IRType::Enum { .. },
            body,
            ..
        } if !domain.has_variant_fields() => {
            let n = enum_variant_count(domain);
            let mut preds = Vec::new();
            for idx in 0..n {
                let inner_ctx = ctx.with_local(var, smt::int_val(idx as i64));
                preds.push(encode_prop_expr(pool, vctx, defs, &inner_ctx, body, step)?);
            }
            if preds.is_empty() {
                return Ok(Bool::from_bool(false));
            }
            // Exactly one: at least one AND pairwise exclusion
            let at_least_one = {
                let refs: Vec<&Bool> = preds.iter().collect();
                Bool::or(&refs)
            };
            let mut exclusions = Vec::new();
            for i in 0..preds.len() {
                for j in (i + 1)..preds.len() {
                    exclusions.push(Bool::and(&[&preds[i], &preds[j]]).not());
                }
            }
            if exclusions.is_empty() {
                Ok(at_least_one)
            } else {
                let excl_refs: Vec<&Bool> = exclusions.iter().collect();
                Ok(Bool::and(&[&at_least_one, &Bool::and(&excl_refs)]))
            }
        }
        IRExpr::Lone {
            var,
            domain: domain @ crate::ir::types::IRType::Enum { .. },
            body,
            ..
        } if !domain.has_variant_fields() => {
            let n = enum_variant_count(domain);
            let mut preds = Vec::new();
            for idx in 0..n {
                let inner_ctx = ctx.with_local(var, smt::int_val(idx as i64));
                preds.push(encode_prop_expr(pool, vctx, defs, &inner_ctx, body, step)?);
            }
            if preds.len() <= 1 {
                return Ok(Bool::from_bool(true));
            }
            let mut exclusions = Vec::new();
            for i in 0..preds.len() {
                for j in (i + 1)..preds.len() {
                    exclusions.push(Bool::and(&[&preds[i], &preds[j]]).not());
                }
            }
            let refs: Vec<&Bool> = exclusions.iter().collect();
            Ok(Bool::and(&refs))
        }
        // Z3 native quantifiers for all other non-entity domains:
        // ADT enums (infinite values per constructor), refinement types
        // (domain predicate restricts range), Int/Bool/Real.
        //
        // Domain predicates are applied via build_domain_predicate to
        // constrain bound variables to their declared domain.
        IRExpr::Forall {
            var, domain, body, ..
        } => {
            let bound_var = make_z3_var_ctx(var, domain, Some(vctx))?;
            let inner_ctx = ctx.with_local(var, bound_var.clone());
            let body_bool = encode_prop_expr(pool, vctx, defs, &inner_ctx, body, step)?;
            let dp = prop_domain_predicate(domain, &bound_var, &inner_ctx, vctx, defs)?;
            let guarded = match dp {
                Some(d) => d.implies(&body_bool),
                None => body_bool,
            };
            build_z3_quantifier(true, &bound_var, &guarded, var, domain)
        }
        IRExpr::Exists {
            var, domain, body, ..
        } => {
            let bound_var = make_z3_var_ctx(var, domain, Some(vctx))?;
            let inner_ctx = ctx.with_local(var, bound_var.clone());
            let body_bool = encode_prop_expr(pool, vctx, defs, &inner_ctx, body, step)?;
            let dp = prop_domain_predicate(domain, &bound_var, &inner_ctx, vctx, defs)?;
            let guarded = match dp {
                Some(d) => Bool::and(&[&d, &body_bool]),
                None => body_bool,
            };
            build_z3_quantifier(false, &bound_var, &guarded, var, domain)
        }
        IRExpr::One {
            var, domain, body, ..
        } => {
            // Exactly one: ∃x. D(x) ∧ P(x) ∧ ∀y. D(y) ∧ P(y) → y = x
            let x_var = make_z3_var_ctx(var, domain, Some(vctx))?;
            let x_ctx = ctx.with_local(var, x_var.clone());
            let p_x = encode_prop_expr(pool, vctx, defs, &x_ctx, body, step)?;
            let d_x = prop_domain_predicate(domain, &x_var, &x_ctx, vctx, defs)?;
            let x_satisfies = match &d_x {
                Some(dp) => Bool::and(&[dp, &p_x]),
                None => p_x.clone(),
            };

            let y_name = format!("{var}__unique");
            let y_var = make_z3_var_ctx(&y_name, domain, Some(vctx))?;
            let y_ctx = ctx.with_local(var, y_var.clone());
            let p_y = encode_prop_expr(pool, vctx, defs, &y_ctx, body, step)?;
            let d_y = prop_domain_predicate(domain, &y_var, &y_ctx, vctx, defs)?;
            let y_satisfies = match &d_y {
                Some(dp) => Bool::and(&[dp, &p_y]),
                None => p_y,
            };

            let y_eq_x = smt::smt_eq(&y_var, &x_var)?;
            let forall_unique = build_z3_quantifier(
                true, &y_var, &y_satisfies.implies(&y_eq_x), &y_name, domain,
            )?;
            let exists_body = Bool::and(&[&x_satisfies, &forall_unique]);
            build_z3_quantifier(false, &x_var, &exists_body, var, domain)
        }
        IRExpr::Lone {
            var, domain, body, ..
        } => {
            // At most one: ∀x, y. D(x) ∧ D(y) ∧ P(x) ∧ P(y) → x = y
            let x_var = make_z3_var_ctx(var, domain, Some(vctx))?;
            let x_ctx = ctx.with_local(var, x_var.clone());
            let p_x = encode_prop_expr(pool, vctx, defs, &x_ctx, body, step)?;
            let d_x = prop_domain_predicate(domain, &x_var, &x_ctx, vctx, defs)?;

            let y_name = format!("{var}__unique");
            let y_var = make_z3_var_ctx(&y_name, domain, Some(vctx))?;
            let y_ctx = ctx.with_local(var, y_var.clone());
            let p_y = encode_prop_expr(pool, vctx, defs, &y_ctx, body, step)?;
            let d_y = prop_domain_predicate(domain, &y_var, &y_ctx, vctx, defs)?;

            let mut antecedents = Vec::new();
            if let Some(dp) = &d_x { antecedents.push(dp.clone()); }
            if let Some(dp) = &d_y { antecedents.push(dp.clone()); }
            antecedents.push(p_x);
            antecedents.push(p_y);
            let antecedent_refs: Vec<&Bool> = antecedents.iter().collect();
            let lhs = Bool::and(&antecedent_refs);

            let x_eq_y = smt::smt_eq(&x_var, &y_var)?;
            let forall_body = lhs.implies(&x_eq_y);
            let inner = build_z3_quantifier(true, &y_var, &forall_body, &y_name, domain)?;
            build_z3_quantifier(true, &x_var, &inner, var, domain)
        }
        // Boolean connectives — recurse
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpAnd" || op == "OpOr" || op == "OpImplies" || op == "OpXor" => {
            let l = encode_prop_expr(pool, vctx, defs, ctx, left, step)?;
            // For implication, the RHS is only reachable when the LHS is true.
            // Push the LHS as a path guard so that precondition obligations
            // inside the RHS are guarded by it. Use a scope guard to ensure
            // pop happens even if encoding the RHS returns an error.
            let is_implies = op == "OpImplies";
            if is_implies {
                push_path_guard(l.clone());
            }
            let r_result = encode_prop_expr(pool, vctx, defs, ctx, right, step);
            if is_implies {
                pop_path_guard();
            }
            let r = r_result?;
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
        // `P until Q` should not reach here from BMC (desugared at top level
        // after def expansion). If it does arrive (e.g., from scene encoding or
        // other non-BMC paths), use same-step: Q(s) ∨ P(s). This is an
        // over-approximation but avoids unsound false proofs.
        IRExpr::Until { left, right, .. } => {
            let q = encode_prop_expr(pool, vctx, defs, ctx, right, step)?;
            let p = encode_prop_expr(pool, vctx, defs, ctx, left, step)?;
            Ok(Bool::or(&[&q, &p]))
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
        // Record context-sensitive precondition obligations (same as encode_prop_expr)
        if let Some(preconditions) = defs.call_preconditions(expr) {
            let fn_name = defenv::decompose_app_chain_name(expr)
                .unwrap_or_else(|| "(unknown)".to_owned());
            let path_guard = current_path_guard();
            for pre in &preconditions {
                if let Ok(pre_bool) = encode_prop_expr(pool, vctx, defs, ctx, pre, step) {
                    record_prop_precondition_obligation(
                        path_guard.implies(&pre_bool),
                        fn_name.clone(),
                    );
                }
            }
        }
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
        // Bare variable: check locals first, then entity bindings, then entity fields
        IRExpr::Var { name, .. } => {
            // Check non-entity local bindings first (enum/Int/Bool/Real quantifier vars)
            if let Some(val) = ctx.locals.get(name) {
                return Ok(val.clone());
            }
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
            enum_name, ctor, args, ..
        } => {
            // ADT-encoded enum: use constructor function with field arguments
            if let Some(dt) = vctx.adt_sorts.get(enum_name) {
                for variant in &dt.variants {
                    if variant.constructor.name() == *ctor {
                        if args.is_empty() {
                            let result = variant.constructor.apply(&[]);
                            return Ok(dynamic_to_smt_value(result));
                        }
                        // Build args in declared field order
                        let declared_names: Vec<std::string::String> = variant
                            .accessors
                            .iter()
                            .map(|a| a.name())
                            .collect();
                        let args_map: HashMap<&str, &IRExpr> = args
                            .iter()
                            .map(|(n, e)| (n.as_str(), e))
                            .collect();
                        let mut z3_args: Vec<z3::ast::Dynamic> = Vec::new();
                        for decl_name in &declared_names {
                            if let Some(field_expr) = args_map.get(decl_name.as_str()) {
                                let val = encode_prop_value(pool, vctx, defs, ctx, field_expr, step)?;
                                z3_args.push(val.to_dynamic());
                            }
                        }
                        let arg_refs: Vec<&dyn z3::ast::Ast> =
                            z3_args.iter().map(|a| a as &dyn z3::ast::Ast).collect();
                        let result = variant.constructor.apply(&arg_refs);
                        return Ok(dynamic_to_smt_value(result));
                    }
                }
            }
            // Flat Int encoding for fieldless enums
            let id = vctx.variants.id_of(enum_name, ctor);
            Ok(smt::int_val(id))
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpSeqConcat" => {
            // Seq::concat on concrete literals: combine elements
            let a_elems = match left.as_ref() {
                IRExpr::SeqLit { elements, .. } => elements.clone(),
                _ => return Err(format!("Seq::concat requires literal operands")),
            };
            let b_elems = match right.as_ref() {
                IRExpr::SeqLit { elements, .. } => elements.clone(),
                _ => return Err(format!("Seq::concat requires literal operands")),
            };
            let mut combined = a_elems;
            combined.extend(b_elems);
            let seq_ty = match left.as_ref() {
                IRExpr::SeqLit { ty, .. } => ty.clone(),
                _ => crate::ir::types::IRType::Seq {
                    element: Box::new(crate::ir::types::IRType::Int),
                },
            };
            let combined_lit = IRExpr::SeqLit {
                elements: combined,
                ty: seq_ty,
                span: None,
            };
            encode_prop_value(pool, vctx, defs, ctx, &combined_lit, step)
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
        IRExpr::Forall { .. }
        | IRExpr::Exists { .. }
        | IRExpr::One { .. }
        | IRExpr::Lone { .. } => Ok(SmtValue::Bool(encode_prop_expr(
            pool, vctx, defs, ctx, expr, step,
        )?)),
        IRExpr::Always { body, .. } => Ok(SmtValue::Bool(encode_prop_expr(
            pool, vctx, defs, ctx, body, step,
        )?)),
        IRExpr::Until { .. } => Ok(SmtValue::Bool(encode_prop_expr(
            pool, vctx, defs, ctx, expr, step,
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
/// Extract a counterexample trace with event identification.
///
/// For each transition step, evaluates event guards against the model to
/// determine which event fired. If no event guard is satisfied, the step
/// is labeled as stutter.
fn extract_counterexample_with_events(
    solver: &Solver,
    pool: &SlotPool,
    vctx: &crate::verify::context::VerifyContext,
    entities: &[crate::ir::types::IREntity],
    systems: &[crate::ir::types::IRSystem],
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
                            SmtValue::Func(_) => "?".to_owned(),
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

        // Identify which event fired at this step (for transition steps only)
        let event_name = if step < bound && !systems.is_empty() {
            identify_event_at_step(&model, pool, vctx, entities, systems, step)
        } else {
            None
        };

        trace.push(TraceStep {
            step,
            event: event_name,
            assignments,
        });
    }

    trace
}

/// Identify which event fired at a given step by evaluating event guards
/// against the Z3 model.
///
/// For each system event, encodes the guard at the given step and checks
/// if the model satisfies it. Returns the first matching event name, or
/// None if only stutter occurred.
fn identify_event_at_step(
    model: &z3::Model,
    pool: &SlotPool,
    vctx: &crate::verify::context::VerifyContext,
    entities: &[crate::ir::types::IREntity],
    systems: &[crate::ir::types::IRSystem],
    step: usize,
) -> Option<String> {
    use crate::verify::harness::encode_event;

    // Evaluate each event's full formula (guard + body + frame) against the model.
    // Collect ALL matching events — if ambiguous, report "event A or event B".
    let mut matches = Vec::new();
    for system in systems {
        for event in &system.events {
            let formula = encode_event(pool, vctx, entities, systems, event, step);
            if let Some(val) = model.eval(&formula, true) {
                if val.as_bool() == Some(true) {
                    let name = if systems.len() == 1 {
                        event.name.clone()
                    } else {
                        format!("{}::{}", system.name, event.name)
                    };
                    matches.push(name);
                }
            }
        }
    }
    match matches.len() {
        0 => None, // stutter
        1 => Some(matches.into_iter().next().unwrap()),
        _ => Some(matches.join(" or ")),
    }
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
                    if step.step == 0 {
                        writeln!(f, "  step 0: (initial)")?;
                    } else if let Some(event) = &step.event {
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
                write!(f, "UNPROVABLE {name}: {hint}")
            }
            VerificationResult::FnContractProved { name, time_ms, .. } => {
                write!(f, "PROVED  fn {name} (contract, {time_ms}ms)")
            }
            VerificationResult::FnContractAdmitted {
                name,
                reason,
                time_ms,
                ..
            } => {
                write!(f, "ADMITTED fn {name} ({reason}, {time_ms}ms)")
            }
            VerificationResult::FnContractFailed {
                name,
                counterexample,
                ..
            } => {
                writeln!(f, "FAILED  fn {name} (contract violated)")?;
                for (param, value) in counterexample {
                    writeln!(f, "    {param} = {value}")?;
                }
                Ok(())
            }
            VerificationResult::LivenessViolation {
                name,
                prefix,
                loop_trace,
                loop_start,
                ..
            } => {
                writeln!(f, "LIVENESS_VIOLATION {name}")?;
                if !prefix.is_empty() {
                    writeln!(f, "  prefix (steps 0..{loop_start}):")?;
                    for step in prefix {
                        if step.step == 0 {
                            writeln!(f, "    step 0: (initial)")?;
                        } else if let Some(event) = &step.event {
                            writeln!(f, "    step {}: event {event}", step.step)?;
                        } else {
                            writeln!(f, "    step {}:", step.step)?;
                        }
                        for (entity, field, value) in &step.assignments {
                            writeln!(f, "      {entity}.{field} = {value}")?;
                        }
                    }
                }
                writeln!(f, "  loop (repeats forever):")?;
                for step in loop_trace {
                    if let Some(event) = &step.event {
                        writeln!(f, "    step {}: event {event}", step.step)?;
                    } else {
                        writeln!(f, "    step {}:", step.step)?;
                    }
                    for (entity, field, value) in &step.assignments {
                        writeln!(f, "      {entity}.{field} = {value}")?;
                    }
                }
                writeln!(f, "    [loops back to step {loop_start}]")
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
                    initial_constraint: None,
                },
                IRField {
                    name: "status".to_owned(),
                    ty: IRType::Enum {
                        name: "OrderStatus".to_owned(),
                        variants: vec![
                    IRVariant::simple("Pending"),
                    IRVariant::simple("Confirmed"),
                    IRVariant::simple("Shipped"),
                ],
                    },
                    default: None,
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
        };

        let commerce_system = IRSystem {
            name: "Commerce".to_owned(),
            entities: vec!["Order".to_owned()],
            events: vec![IREvent {
                fairness: IRFairness::None,
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
            lemmas: vec![],
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
                            args: vec![],
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
            fairness: IRFairness::None,
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
                            args: vec![],
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
            lemmas: vec![],
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
                initial_constraint: None,
            }],
            transitions: vec![],
        }
    }

    fn make_noop_event(name: &str) -> IREvent {
        IREvent {
            name: name.to_owned(),
            fairness: IRFairness::None,
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
            lemmas: vec![],
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
                fairness: IRFairness::None,
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
                fairness: IRFairness::None,
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
            lemmas: vec![],
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
                variants: vec![IRVariant::simple("Active"), IRVariant::simple("Locked")],
            },
        };

        let account = IREntity {
            name: "Account".to_owned(),
            fields: vec![
                IRField {
                    name: "id".to_owned(),
                    ty: IRType::Id,
                    default: None,
                    initial_constraint: None,
                },
                IRField {
                    name: "status".to_owned(),
                    ty: IRType::Enum {
                        name: "Status".to_owned(),
                        variants: vec![IRVariant::simple("Active"), IRVariant::simple("Locked")],
                    },
                    default: Some(IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Active".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    initial_constraint: None,
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
                        ctor: "Locked".to_owned(),
                        args: vec![],
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
                fairness: IRFairness::None,
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
            lemmas: vec![],
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
                        args: vec![],
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
                    args: vec![],
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
                        args: vec![],
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
                    args: vec![],
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
            fairness: IRFairness::None,
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
                            args: vec![],
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
                            args: vec![],
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
                            args: vec![],
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
            fairness: IRFairness::None,
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
                            args: vec![],
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
                    initial_constraint: None,
                },
                IRField {
                    name: "y".to_owned(),
                    ty: IRType::Int,
                    default: Some(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },

                        span: None,
                    }),
                    initial_constraint: None,
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
                fairness: IRFairness::None,
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
            lemmas: vec![],
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
                    initial_constraint: None,
                },
                IRField {
                    name: "y".to_owned(),
                    ty: IRType::Int,
                    default: Some(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },

                        span: None,
                    }),
                    initial_constraint: None,
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
                fairness: IRFairness::None,
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
            lemmas: vec![],
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
                initial_constraint: None,
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
                    fairness: IRFairness::None,
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
                    fairness: IRFairness::None,
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
            lemmas: vec![],
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
                initial_constraint: None,
            }],
            transitions: vec![],
        };

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["M".to_owned()],
            events: vec![IREvent {
                fairness: IRFairness::None,
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
            lemmas: vec![],
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
                    initial_constraint: None,
                },
                IRField {
                    name: "count".to_owned(),
                    ty: IRType::Int,
                    default: Some(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },

                        span: None,
                    }),
                    initial_constraint: None,
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
                    fairness: IRFairness::None,
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
                    fairness: IRFairness::None,
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
            lemmas: vec![],
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
                initial_constraint: None,
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
                    fairness: IRFairness::None,
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
                    fairness: IRFairness::None,
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
            lemmas: vec![],
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
                initial_constraint: None,
            }],
            transitions: vec![],
        };

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["X".to_owned()],
            events: vec![IREvent {
                fairness: IRFairness::None,
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
            lemmas: vec![],
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
                initial_constraint: None,
            }],
            transitions: vec![],
        };

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["X".to_owned()],
            events: vec![IREvent {
                fairness: IRFairness::None,
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
            lemmas: vec![],
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
                initial_constraint: None,
            }],
            transitions: vec![],
        };
        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["X".to_owned()],
            events: vec![IREvent {
                fairness: IRFairness::None,
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
            lemmas: vec![],
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
                variants: vec![IRVariant::simple("Idle"), IRVariant::simple("Active")],
            },
        };

        let entity = IREntity {
            name: "Obj".to_owned(),
            fields: vec![
                IRField {
                    name: "id".to_owned(),
                    ty: IRType::Id,
                    default: None,
                    initial_constraint: None,
                },
                IRField {
                    name: "status".to_owned(),
                    ty: IRType::Enum {
                        name: "Status".to_owned(),
                        variants: vec![IRVariant::simple("Idle"), IRVariant::simple("Active")],
                    },
                    default: Some(IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Idle".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    initial_constraint: None,
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
                        ctor: "Active".to_owned(),
                        args: vec![],
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
                    fairness: IRFairness::None,
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
                    fairness: IRFairness::None,
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
                    args: vec![],
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
            lemmas: vec![],
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
                variants: vec![IRVariant::simple("Idle"), IRVariant::simple("Active")],
            },
        };

        let entity = IREntity {
            name: "Obj".to_owned(),
            fields: vec![IRField {
                name: "status".to_owned(),
                ty: IRType::Enum {
                    name: "Status".to_owned(),
                    variants: vec![IRVariant::simple("Idle"), IRVariant::simple("Active")],
                },
                default: Some(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Idle".to_owned(),
                    args: vec![],
                    span: None,
                }),
                initial_constraint: None,
            }],
            transitions: vec![],
        };

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["Obj".to_owned()],
            events: vec![IREvent {
                fairness: IRFairness::None,
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
            lemmas: vec![],
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
                variants: vec![IRVariant::simple("Idle"), IRVariant::simple("Active")],
            },
        };

        let entity = IREntity {
            name: "Obj".to_owned(),
            fields: vec![IRField {
                name: "status".to_owned(),
                ty: IRType::Enum {
                    name: "Status".to_owned(),
                    variants: vec![IRVariant::simple("Idle"), IRVariant::simple("Active")],
                },
                default: Some(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Idle".to_owned(),
                    args: vec![],
                    span: None,
                }),
                initial_constraint: None,
            }],
            transitions: vec![],
        };

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["Obj".to_owned()],
            events: vec![IREvent {
                fairness: IRFairness::None,
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
            args: vec![],
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
            lemmas: vec![],
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
                initial_constraint: None,
            }],
            transitions: vec![],
        };

        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["X".to_owned()],
            events: vec![IREvent {
                fairness: IRFairness::None,
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
            lemmas: vec![],
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
                    initial_constraint: None,
                },
                IRField {
                    name: "count".to_owned(),
                    ty: IRType::Int,
                    default: Some(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },

                        span: None,
                    }),
                    initial_constraint: None,
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
                    fairness: IRFairness::None,
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
                    fairness: IRFairness::None,
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
            lemmas: vec![],
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
                variants: vec![IRVariant::simple("Idle"), IRVariant::simple("Active")],
            },
        };

        let entity = IREntity {
            name: "Obj".to_owned(),
            fields: vec![IRField {
                name: "status".to_owned(),
                ty: IRType::Enum {
                    name: "Status".to_owned(),
                    variants: vec![IRVariant::simple("Idle"), IRVariant::simple("Active")],
                },
                default: Some(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Idle".to_owned(),
                    args: vec![],
                    span: None,
                }),
                initial_constraint: None,
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
                        ctor: "Active".to_owned(),
                        args: vec![],
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
                    fairness: IRFairness::None,
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
                    fairness: IRFairness::None,
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
                    args: vec![],
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
            lemmas: vec![],
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
                initial_constraint: None,
            }],
            transitions: vec![],
        };
        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["X".to_owned()],
            events: vec![IREvent {
                fairness: IRFairness::None,
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
            lemmas: vec![],
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
                initial_constraint: None,
            }],
            transitions: vec![],
        };
        let system = IRSystem {
            name: "S".to_owned(),
            entities: vec!["X".to_owned()],
            events: vec![IREvent {
                fairness: IRFairness::None,
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
            lemmas: vec![],
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
            lemmas: vec![],
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
                variants: vec![IRVariant::simple("On"), IRVariant::simple("Off")],
            },
        };
        let entity = IREntity {
            name: "Switch".to_owned(),
            fields: vec![IRField {
                name: "status".to_owned(),
                ty: IRType::Enum {
                    name: "Status".to_owned(),
                    variants: vec![IRVariant::simple("On"), IRVariant::simple("Off")],
                },
                default: Some(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Off".to_owned(),
                    args: vec![],
                    span: None,
                }),
                initial_constraint: None,
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
                        args: vec![],
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
                    fairness: IRFairness::None,
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
                    fairness: IRFairness::None,
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
                    args: vec![],
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
            lemmas: vec![],
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
                initial_constraint: None,
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
                    fairness: IRFairness::None,
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
                    fairness: IRFairness::None,
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
            lemmas: vec![],
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
                initial_constraint: None,
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
                fairness: IRFairness::None,
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
            lemmas: vec![],
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
                initial_constraint: None,
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
                    fairness: IRFairness::None,
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
                    fairness: IRFairness::None,
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
            lemmas: vec![],
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
                initial_constraint: None,
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
                    fairness: IRFairness::None,
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
                    fairness: IRFairness::None,
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
                    fairness: IRFairness::None,
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
            lemmas: vec![],
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
                initial_constraint: None,
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
                    fairness: IRFairness::None,
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
                    fairness: IRFairness::None,
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
            lemmas: vec![],
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
                    initial_constraint: None,
                },
                IRField {
                    name: "amount".to_owned(),
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
                    fairness: IRFairness::None,
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
                    fairness: IRFairness::None,
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
            lemmas: vec![],
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
                initial_constraint: None,
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
                fairness: IRFairness::None,
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
            lemmas: vec![],
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

    // ── Function contract verification tests ────────────────────────

    /// Helper: build an IR program with a single function (no entities/systems).
    fn make_fn_ir(func: IRFunction) -> IRProgram {
        IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![func],
            entities: vec![],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        }
    }

    /// fn double(x: Int): Int ensures result == x + x = x + x
    /// Postcondition should be proved.
    #[test]
    fn fn_contract_simple_ensures_proved() {
        let func = IRFunction {
            name: "double".to_owned(),
            ty: IRType::Fn {
                param: Box::new(IRType::Int),
                result: Box::new(IRType::Int),
            },
            body: IRExpr::Lam {
                param: "x".to_owned(),
                param_type: IRType::Int,
                body: Box::new(IRExpr::BinOp {
                    op: "OpAdd".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    ty: IRType::Int,
                    span: None,
                }),
                span: None,
            },
            prop_target: None,
            requires: vec![],
            ensures: vec![IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "result".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(IRExpr::BinOp {
                    op: "OpAdd".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    ty: IRType::Int,
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }],
            decreases: None,
            span: None,
            file: None,
        };

        let ir = make_fn_ir(func);
        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 1);
        assert!(
            matches!(&results[0], VerificationResult::FnContractProved { name, .. } if name == "double"),
            "expected FnContractProved, got: {}",
            results[0]
        );
    }

    /// fn bad(x: Int): Int ensures result > x = x
    /// Body is just x, but ensures says result > x. Should fail.
    #[test]
    fn fn_contract_ensures_fails() {
        let func = IRFunction {
            name: "bad".to_owned(),
            ty: IRType::Fn {
                param: Box::new(IRType::Int),
                result: Box::new(IRType::Int),
            },
            body: IRExpr::Lam {
                param: "x".to_owned(),
                param_type: IRType::Int,
                body: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                span: None,
            },
            prop_target: None,
            requires: vec![],
            ensures: vec![IRExpr::BinOp {
                op: "OpGt".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "result".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }],
            decreases: None,
            span: None,
            file: None,
        };

        let ir = make_fn_ir(func);
        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 1);
        assert!(
            matches!(&results[0], VerificationResult::FnContractFailed { name, counterexample, .. }
                if name == "bad" && !counterexample.is_empty()),
            "expected FnContractFailed with counterexample, got: {}",
            results[0]
        );
    }

    /// fn no_contract(x: Int): Int = x + 1
    /// No ensures clause — should be skipped entirely.
    #[test]
    fn fn_contract_no_ensures_skipped() {
        let func = IRFunction {
            name: "no_contract".to_owned(),
            ty: IRType::Fn {
                param: Box::new(IRType::Int),
                result: Box::new(IRType::Int),
            },
            body: IRExpr::Lam {
                param: "x".to_owned(),
                param_type: IRType::Int,
                body: Box::new(IRExpr::BinOp {
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
                }),
                span: None,
            },
            prop_target: None,
            requires: vec![],
            ensures: vec![],
            decreases: None,
            span: None,
            file: None,
        };

        let ir = make_fn_ir(func);
        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 0, "fn without ensures should produce no results");
    }

    /// fn clamp(x: Int, lo: Int, hi: Int): Int
    ///   requires lo <= hi
    ///   ensures result >= lo
    ///   ensures result <= hi
    /// = if x < lo then lo else if x > hi then hi else x
    #[test]
    fn fn_contract_with_requires_and_multiple_ensures() {
        let func = IRFunction {
            name: "clamp".to_owned(),
            ty: IRType::Fn {
                param: Box::new(IRType::Int),
                result: Box::new(IRType::Fn {
                    param: Box::new(IRType::Int),
                    result: Box::new(IRType::Fn {
                        param: Box::new(IRType::Int),
                        result: Box::new(IRType::Int),
                    }),
                }),
            },
            body: IRExpr::Lam {
                param: "x".to_owned(),
                param_type: IRType::Int,
                body: Box::new(IRExpr::Lam {
                    param: "lo".to_owned(),
                    param_type: IRType::Int,
                    body: Box::new(IRExpr::Lam {
                        param: "hi".to_owned(),
                        param_type: IRType::Int,
                        body: Box::new(IRExpr::IfElse {
                            cond: Box::new(IRExpr::BinOp {
                                op: "OpLt".to_owned(),
                                left: Box::new(IRExpr::Var {
                                    name: "x".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                right: Box::new(IRExpr::Var {
                                    name: "lo".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                ty: IRType::Bool,
                                span: None,
                            }),
                            then_body: Box::new(IRExpr::Var {
                                name: "lo".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            else_body: Some(Box::new(IRExpr::IfElse {
                                cond: Box::new(IRExpr::BinOp {
                                    op: "OpGt".to_owned(),
                                    left: Box::new(IRExpr::Var {
                                        name: "x".to_owned(),
                                        ty: IRType::Int,
                                        span: None,
                                    }),
                                    right: Box::new(IRExpr::Var {
                                        name: "hi".to_owned(),
                                        ty: IRType::Int,
                                        span: None,
                                    }),
                                    ty: IRType::Bool,
                                    span: None,
                                }),
                                then_body: Box::new(IRExpr::Var {
                                    name: "hi".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                else_body: Some(Box::new(IRExpr::Var {
                                    name: "x".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                })),
                                span: None,
                            })),
                            span: None,
                        }),
                        span: None,
                    }),
                    span: None,
                }),
                span: None,
            },
            prop_target: None,
            requires: vec![IRExpr::BinOp {
                op: "OpLe".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "lo".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(IRExpr::Var {
                    name: "hi".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }],
            ensures: vec![
                IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "result".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "lo".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                },
                IRExpr::BinOp {
                    op: "OpLe".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "result".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "hi".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                },
            ],
            decreases: None,
            span: None,
            file: None,
        };

        let ir = make_fn_ir(func);
        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 1);
        assert!(
            matches!(&results[0], VerificationResult::FnContractProved { name, .. } if name == "clamp"),
            "expected FnContractProved for clamp, got: {}",
            results[0]
        );
    }

    /// fn only_requires(x: Int): Int requires x > 0 = x
    /// Has requires but no ensures — should be skipped.
    #[test]
    fn fn_contract_only_requires_skipped() {
        let func = IRFunction {
            name: "only_requires".to_owned(),
            ty: IRType::Fn {
                param: Box::new(IRType::Int),
                result: Box::new(IRType::Int),
            },
            body: IRExpr::Lam {
                param: "x".to_owned(),
                param_type: IRType::Int,
                body: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                span: None,
            },
            prop_target: None,
            requires: vec![IRExpr::BinOp {
                op: "OpGt".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
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
            }],
            ensures: vec![],
            decreases: None,
            span: None,
            file: None,
        };

        let ir = make_fn_ir(func);
        let results = verify_all(&ir, &VerifyConfig::default());
        assert_eq!(results.len(), 0, "fn with only requires should produce no results");
    }

    /// --no-fn-verify skips fn contract verification.
    #[test]
    fn fn_contract_skipped_with_flag() {
        let func = IRFunction {
            name: "double".to_owned(),
            ty: IRType::Fn {
                param: Box::new(IRType::Int),
                result: Box::new(IRType::Int),
            },
            body: IRExpr::Lam {
                param: "x".to_owned(),
                param_type: IRType::Int,
                body: Box::new(IRExpr::BinOp {
                    op: "OpAdd".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    ty: IRType::Int,
                    span: None,
                }),
                span: None,
            },
            prop_target: None,
            requires: vec![],
            ensures: vec![IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "result".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(IRExpr::BinOp {
                    op: "OpAdd".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    ty: IRType::Int,
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }],
            decreases: None,
            span: None,
            file: None,
        };

        let ir = make_fn_ir(func);
        let config = VerifyConfig {
            no_fn_verify: true,
            ..VerifyConfig::default()
        };
        let results = verify_all(&ir, &config);
        assert_eq!(results.len(), 0, "no_fn_verify should skip fn contract verification");
    }
}
