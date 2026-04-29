//! Function contract verification — ensures/requires, Hoare-logic loops,
//! termination, recursive call encoding.

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::panic::{self, AssertUnwindSafe};
use std::time::Instant;

use crate::ir::types::{IRExpr, IRProgram};

use super::context::VerifyContext;
use super::defenv;
#[allow(clippy::wildcard_imports)]
use super::encode::*;
use super::smt::{self, AbideSolver, Bool, SatResult, SmtValue};
#[allow(clippy::wildcard_imports)]
use super::walkers::*;
use super::{remaining_budget_ms, verification_timeout_hint, VerificationResult, VerifyConfig};

// ── Thread-local accumulators ───────────────────────────────────────

/// Global counter for generating fresh post-loop variable names.
static LOOP_VAR_COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

// Thread-local accumulator for ensures constraints from recursive self-calls.
// When encode_recursive_self_call creates a fresh result variable, it also
// encodes the function's ensures clauses (with actual args + result var
// substituted) and pushes them here. The caller asserts them on the main solver.
thread_local! {
    static RECURSIVE_CALL_CONSTRAINTS: RefCell<Vec<Bool>> =
        const { RefCell::new(Vec::new()) };
    static FN_SOLVER_TIMEOUT_MS: Cell<u64> = const { Cell::new(0) };
}

pub(super) fn push_recursive_call_constraint(c: Bool) {
    RECURSIVE_CALL_CONSTRAINTS.with(|v| v.borrow_mut().push(c));
}

pub(super) fn take_recursive_call_constraints() -> Vec<Bool> {
    RECURSIVE_CALL_CONSTRAINTS.with(|v| std::mem::take(&mut *v.borrow_mut()))
}

fn set_fn_solver_timeout_ms(timeout_ms: u64) {
    FN_SOLVER_TIMEOUT_MS.with(|cell| cell.set(timeout_ms));
}

fn new_timed_solver() -> AbideSolver {
    let solver = AbideSolver::new();
    let timeout_ms = FN_SOLVER_TIMEOUT_MS.with(Cell::get);
    if timeout_ms > 0 {
        solver.set_timeout(timeout_ms);
    }
    solver
}

type RecursiveCallSite = (Vec<Bool>, Vec<IRExpr>, HashMap<String, SmtValue>);

// Thread-local accumulator for lambda definitional axioms.
// When a lambda is encoded as a Z3 uninterpreted function, its
// definitional axiom (forall params. f(params) == body) is pushed here.
// The caller asserts them on the main solver.
thread_local! {
    static LAMBDA_AXIOMS: RefCell<Vec<Bool>> =
        const { RefCell::new(Vec::new()) };
}

pub(super) fn push_lambda_axiom(axiom: Bool) {
    LAMBDA_AXIOMS.with(|v| v.borrow_mut().push(axiom));
}

/// Get a copy of all accumulated lambda axioms (non-destructive).
/// Every solver that may encounter lambda applications needs these.
pub(super) fn clone_lambda_axioms() -> Vec<Bool> {
    LAMBDA_AXIOMS.with(|v| v.borrow().clone())
}

/// Clear all accumulated lambda axioms (call between verification targets).
pub(super) fn clear_lambda_axioms() {
    LAMBDA_AXIOMS.with(|v| v.borrow_mut().clear());
}

/// Assert all accumulated lambda axioms on a solver.
/// Call this on every fresh VC solver (assert, loop, precondition checks).
pub(super) fn assert_lambda_axioms_on(solver: &AbideSolver) {
    for axiom in &clone_lambda_axioms() {
        solver.assert(axiom);
    }
}

// ── Top-level fn contract verification ──────────────────────────────

///
/// For each fn with non-empty `ensures` and no `prop_target` (i.e., not a prop):
/// - Declare Z3 variables for each parameter
/// - Assert requires as assumptions
/// - Assert NOT(ensures[result:= body]) and check for counterexample
/// - UNSAT = postcondition holds; SAT = counterexample
pub(super) fn verify_fn_contracts(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    config: &VerifyConfig,
    deadline: Option<Instant>,
    results: &mut Vec<VerificationResult>,
) {
    for func in &ir.functions {
        if !super::should_run_target(config, super::VerifyTargetKind::Fn, &func.name) {
            continue;
        }
        if matches!(remaining_budget_ms(deadline), Some(0)) {
            results.push(VerificationResult::Unprovable {
                name: format!("fn_{}", func.name),
                hint: verification_timeout_hint(config),
                span: func.span,
                file: func.file.clone(),
            });
            continue;
        }
        let effective_timeout_ms = remaining_budget_ms(deadline)
            .map(|remaining| {
                if config.induction_timeout_ms == 0 {
                    remaining
                } else {
                    config.induction_timeout_ms.min(remaining)
                }
            })
            .unwrap_or(config.induction_timeout_ms);
        set_fn_solver_timeout_ms(effective_timeout_ms);
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
                let term_result = panic::catch_unwind(AssertUnwindSafe(|| {
                    verify_fn_termination(func, vctx, defs)
                }))
                .unwrap_or_else(|payload| {
                    Err(super::internal_verifier_hint(
                        "checking function termination",
                        &super::panic_message(payload),
                    ))
                });
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
        let result = panic::catch_unwind(AssertUnwindSafe(|| {
            verify_single_fn_contract(func, vctx, defs)
        }))
        .unwrap_or_else(|payload| {
            Err(FnContractError::EncodingError(
                super::internal_verifier_hint(
                    "verifying function contract",
                    &super::panic_message(payload),
                ),
            ))
        });
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
pub(super) enum FnContractError {
    /// Counterexample: parameter assignments that violate the ensures clause.
    Counterexample(Vec<(String, String)>),
    /// Encoding error: couldn't translate the expression to Z3.
    EncodingError(String),
}

/// Verify a single function's ensures clauses against its body.
///
/// For `fn f(x: Int, y: Int): Int requires P ensures Q = body`:
/// Check: ∀ x, y. P(x, y) → Q[result:= body(x, y)]
/// Negated: ∃ x, y. P(x, y) ∧ ¬Q[result:= body(x, y)]
/// UNSAT = proved, SAT = counterexample
pub(super) fn verify_single_fn_contract(
    func: &crate::ir::types::IRFunction,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
) -> Result<(), FnContractError> {
    let solver = new_timed_solver();

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
        let req_bool = req_val.to_bool().map_err(FnContractError::EncodingError)?;
        solver.assert(&req_bool);
    }

    // Encode the body using the imperative-aware encoder.
    // This handles While loops via Hoare-logic:
    // - Verifies loop invariant init/preservation/termination as side conditions
    // - Accumulates post-loop constraints (invariant ∧ ¬cond), properly guarded
    // by branch conditions when inside if/else
    // - Updates env with fresh post-loop variables
    let mut solver_constraints = Vec::new();
    let body_val = encode_fn_body(
        body,
        &mut env,
        &mut solver_constraints,
        &func.requires,
        &[],
        Some(func),
        vctx,
        defs,
    )?;

    // Assert accumulated constraints (post-loop invariants, branch-guarded)
    for c in &solver_constraints {
        solver.assert(c);
    }

    // Assert ensures constraints from recursive self-calls (modular reasoning).
    // These assume the function's postcondition holds for recursive calls,
    // which is sound because proves the postcondition by induction.
    for c in &take_recursive_call_constraints() {
        solver.assert(c);
    }

    // Bind result to the body's return value
    env.insert("result".to_owned(), body_val);

    // Assert negation of ensures: looking for counterexample to postcondition
    let mut ensures_bools = Vec::new();
    for ens in &func.ensures {
        let ens_val =
            encode_pure_expr(ens, &env, vctx, defs).map_err(FnContractError::EncodingError)?;
        let ens_bool = ens_val.to_bool().map_err(FnContractError::EncodingError)?;
        ensures_bools.push(ens_bool);
    }

    let ensures_refs: Vec<&Bool> = ensures_bools.iter().collect();
    let all_ensures = smt::bool_and(&ensures_refs);
    solver.assert(smt::bool_not(&all_ensures));

    // Assert lambda definitional axioms AFTER all encoding (body + ensures).
    // Lambdas may appear in either body or ensures; all their axioms must be
    // available before the solver check.
    for axiom in &clone_lambda_axioms() {
        solver.assert(axiom);
    }

    // Check
    match solver.check() {
        SatResult::Unsat => Ok(()), // Proved: no counterexample exists
        SatResult::Sat => {
            // Extract counterexample
            let model = solver.get_model().ok_or_else(|| {
                FnContractError::EncodingError(
                    "solver reported sat but did not provide a model".to_owned(),
                )
            })?;
            let mut ce = Vec::new();
            for (name, ty) in params {
                let val = env.get(name).ok_or_else(|| {
                    FnContractError::EncodingError(format!(
                        "missing parameter `{name}` in function contract environment"
                    ))
                })?;
                let val_str = extract_model_value(&model, val, &vctx.variants, ty);
                ce.push((name.clone(), val_str));
            }
            Err(FnContractError::Counterexample(ce))
        }
        SatResult::Unknown(_) => Err(FnContractError::EncodingError(
            "solver returned unknown (timeout or incomplete theory)".to_owned(),
        )),
    }
}

// ── Imperative body encoding (Hoare-logic for while loops) ──────────

/// Encode a function body that may contain imperative constructs (While, `VarDecl`, Block).
///
/// Unlike `encode_pure_expr`, this function:
/// - Threads the environment through Block expressions (sequential env mutation)
/// - Verifies while-loop invariants via Hoare-logic side conditions
/// - Creates fresh post-loop variables and asserts invariant ∧ ¬cond on the solver
///   `solver_constraints` accumulates Z3 Bool assertions that must hold
///   (e.g., post-loop invariants). These are NOT asserted immediately — the
///   caller decides how to assert them (e.g., guarded by branch conditions).
///
/// `extra_assumptions` carries Z3 Bool facts known to be true in the current
/// context — e.g., branch conditions from enclosing if/else. These are threaded
/// to loop verification so that branch-local invariants (like `invariant flag`
/// inside `if flag {... }`) can be verified.
#[allow(clippy::too_many_arguments)]
pub(super) fn encode_fn_body(
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
                let var = make_z3_var(param, param_type).map_err(FnContractError::EncodingError)?;
                env.insert(param.clone(), var);
            }
            encode_fn_body(
                body,
                env,
                solver_constraints,
                fn_requires,
                extra_assumptions,
                self_fn,
                vctx,
                defs,
            )
        }

        // VarDecl: evaluate init, extend env, recurse into rest
        IRExpr::VarDecl {
            name, init, rest, ..
        } => {
            let val =
                encode_pure_expr(init, env, vctx, defs).map_err(FnContractError::EncodingError)?;
            env.insert(name.clone(), val);
            encode_fn_body(
                rest,
                env,
                solver_constraints,
                fn_requires,
                extra_assumptions,
                self_fn,
                vctx,
                defs,
            )
        }

        // Block: thread env through each expression sequentially
        IRExpr::Block { exprs, .. } => {
            if exprs.is_empty() {
                return Ok(smt::bool_val(true));
            }
            let mut last = smt::bool_val(true);
            for e in exprs {
                last = encode_fn_body(
                    e,
                    env,
                    solver_constraints,
                    fn_requires,
                    extra_assumptions,
                    self_fn,
                    vctx,
                    defs,
                )?;
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
            op, left, right, ..
        } if op == "OpEq" && matches!(left.as_ref(), IRExpr::Var { .. }) => {
            if let IRExpr::Var { name, .. } = left.as_ref() {
                if env.contains_key(name) {
                    let val = encode_pure_expr(right, env, vctx, defs)
                        .map_err(FnContractError::EncodingError)?;
                    env.insert(name.clone(), val);
                    return Ok(smt::bool_val(true));
                }
            }
            encode_pure_expr(expr, env, vctx, defs).map_err(FnContractError::EncodingError)
        }

        // IfElse with possible imperative branches
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            if contains_imperative(then_body)
                || else_body.as_ref().is_some_and(|e| contains_imperative(e))
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
        IRExpr::Assert {
            expr: assert_expr,
            span,
        } => {
            let assert_val = encode_pure_expr(assert_expr, env, vctx, defs)
                .map_err(FnContractError::EncodingError)?;
            let assert_bool = assert_val
                .to_bool()
                .map_err(FnContractError::EncodingError)?;

            // VC check: prove assert_expr holds given fn_requires + extra_assumptions + accumulated constraints
            let vc_solver = new_timed_solver();
            assert_lambda_axioms_on(&vc_solver);
            // Assert function preconditions
            for req in fn_requires {
                let req_val = encode_pure_expr(req, env, vctx, defs)
                    .map_err(FnContractError::EncodingError)?;
                let req_bool = req_val.to_bool().map_err(FnContractError::EncodingError)?;
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
            vc_solver.assert(smt::bool_not(&assert_bool));
            assert_lambda_axioms_on(&vc_solver);

            match vc_solver.check() {
                SatResult::Unsat => {
                    // Proved: assertion holds. Make it available as a fact.
                    solver_constraints.push(assert_bool);
                    Ok(smt::bool_val(true))
                }
                SatResult::Sat | SatResult::Unknown(_) => {
                    Err(FnContractError::EncodingError(if let Some(sp) = span {
                        format!(
                            "{} (at byte offset {}..{})",
                            crate::messages::FN_ASSERT_FAILED,
                            sp.start,
                            sp.end,
                        )
                    } else {
                        crate::messages::FN_ASSERT_FAILED.to_owned()
                    }))
                }
            }
        }

        // Assume: add the expression as a fact without proof.
        // The user takes responsibility for its truth.
        IRExpr::Assume {
            expr: assume_expr, ..
        } => {
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

// ── While-loop Hoare-logic verification ─────────────────────────────

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
    verify_loop_conditions(
        cond,
        invariants,
        decreases,
        body,
        &modified,
        env,
        fn_requires,
        extra_assumptions,
        vctx,
        defs,
    )?;

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
        let inv_val =
            encode_pure_expr(inv, env, vctx, defs).map_err(FnContractError::EncodingError)?;
        let inv_bool = inv_val.to_bool().map_err(FnContractError::EncodingError)?;
        solver_constraints.push(inv_bool);
    }

    // ¬cond (loop exited)
    let cond_val =
        encode_pure_expr(cond, env, vctx, defs).map_err(FnContractError::EncodingError)?;
    let cond_bool = cond_val.to_bool().map_err(FnContractError::EncodingError)?;
    solver_constraints.push(smt::bool_not(&cond_bool));

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
    verify_loop_preservation(
        cond,
        invariants,
        body,
        modified,
        env,
        fn_requires,
        extra_assumptions,
        vctx,
        defs,
    )?;

    if let Some(dec) = decreases {
        if !dec.star {
            verify_loop_termination(
                cond,
                invariants,
                &dec.measures,
                body,
                modified,
                env,
                fn_requires,
                extra_assumptions,
                vctx,
                defs,
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
    let vc_solver = new_timed_solver();
    assert_lambda_axioms_on(&vc_solver);

    // Assert function preconditions and any outer context assumptions
    for req in fn_requires {
        let req_val =
            encode_pure_expr(req, env, vctx, defs).map_err(FnContractError::EncodingError)?;
        let req_bool = req_val.to_bool().map_err(FnContractError::EncodingError)?;
        vc_solver.assert(&req_bool);
    }
    for assumption in extra_assumptions {
        vc_solver.assert(assumption);
    }

    // Assert ¬invariant — looking for counterexample to init
    let mut inv_bools = Vec::new();
    for inv in invariants {
        let inv_val =
            encode_pure_expr(inv, env, vctx, defs).map_err(FnContractError::EncodingError)?;
        let inv_bool = inv_val.to_bool().map_err(FnContractError::EncodingError)?;
        inv_bools.push(inv_bool);
    }
    let inv_refs: Vec<&Bool> = inv_bools.iter().collect();
    let all_inv = smt::bool_and(&inv_refs);
    vc_solver.assert(smt::bool_not(&all_inv));

    // Assert lambda axioms after all encoding (invariants may contain lambdas)
    assert_lambda_axioms_on(&vc_solver);

    match vc_solver.check() {
        SatResult::Unsat => Ok(()),
        SatResult::Sat | SatResult::Unknown(_) => Err(FnContractError::EncodingError(
            crate::messages::FN_LOOP_INIT_FAILED.to_owned(),
        )),
    }
}

/// VC2: Verify invariant preservation — one iteration maintains the invariant.
///
/// Check: invariant ∧ cond ∧ body → invariant
/// Negated: invariant ∧ cond ∧ ¬invariant[`post_body`] is UNSAT
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
    let vc_solver = new_timed_solver();
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
        let req_val =
            encode_pure_expr(req, &pre_env, vctx, defs).map_err(FnContractError::EncodingError)?;
        vc_solver.assert(&req_val.to_bool().map_err(FnContractError::EncodingError)?);
    }
    for assumption in extra_assumptions {
        vc_solver.assert(assumption);
    }

    // Assume invariant holds for pre-iteration values.
    // Collect as Bool values too, for inner loop context.
    let mut inner_assumptions: Vec<Bool> = extra_assumptions.to_vec();
    for inv in invariants {
        let inv_val =
            encode_pure_expr(inv, &pre_env, vctx, defs).map_err(FnContractError::EncodingError)?;
        let inv_bool = inv_val.to_bool().map_err(FnContractError::EncodingError)?;
        vc_solver.assert(&inv_bool);
        inner_assumptions.push(inv_bool);
    }

    // Assume condition holds (we're inside the loop)
    let cond_val =
        encode_pure_expr(cond, &pre_env, vctx, defs).map_err(FnContractError::EncodingError)?;
    let cond_bool = cond_val.to_bool().map_err(FnContractError::EncodingError)?;
    vc_solver.assert(&cond_bool);
    inner_assumptions.push(cond_bool);

    // Also add fn_requires as Bool for inner loop context
    for req in fn_requires {
        let req_val =
            encode_pure_expr(req, &pre_env, vctx, defs).map_err(FnContractError::EncodingError)?;
        inner_assumptions.push(req_val.to_bool().map_err(FnContractError::EncodingError)?);
    }

    // Execute the body to get post-iteration variable values
    let mut post_env = pre_env.clone();
    let mut body_constraints = Vec::new();
    execute_loop_body(
        body,
        &mut post_env,
        &mut body_constraints,
        &inner_assumptions,
        vctx,
        defs,
    )?;

    // Assert any constraints from nested loops (inner invariant ∧ ¬inner_cond)
    for c in &body_constraints {
        vc_solver.assert(c);
    }

    // Assert ¬invariant[post] — looking for counterexample to preservation
    let mut post_inv_bools = Vec::new();
    for inv in invariants {
        let inv_val =
            encode_pure_expr(inv, &post_env, vctx, defs).map_err(FnContractError::EncodingError)?;
        let inv_bool = inv_val.to_bool().map_err(FnContractError::EncodingError)?;
        post_inv_bools.push(inv_bool);
    }
    let post_refs: Vec<&Bool> = post_inv_bools.iter().collect();
    let all_post = smt::bool_and(&post_refs);
    vc_solver.assert(smt::bool_not(&all_post));

    // Assert lambda axioms after all encoding
    assert_lambda_axioms_on(&vc_solver);

    match vc_solver.check() {
        SatResult::Unsat => Ok(()),
        SatResult::Sat | SatResult::Unknown(_) => Err(FnContractError::EncodingError(
            crate::messages::FN_LOOP_PRESERVATION_FAILED.to_owned(),
        )),
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
    let vc_solver = new_timed_solver();
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
        let req_val =
            encode_pure_expr(req, &pre_env, vctx, defs).map_err(FnContractError::EncodingError)?;
        let req_bool = req_val.to_bool().map_err(FnContractError::EncodingError)?;
        vc_solver.assert(&req_bool);
        inner_assumptions.push(req_bool);
    }
    for assumption in extra_assumptions {
        vc_solver.assert(assumption);
    }
    for inv in invariants {
        let inv_val =
            encode_pure_expr(inv, &pre_env, vctx, defs).map_err(FnContractError::EncodingError)?;
        let inv_bool = inv_val.to_bool().map_err(FnContractError::EncodingError)?;
        vc_solver.assert(&inv_bool);
        inner_assumptions.push(inv_bool);
    }
    let cond_val =
        encode_pure_expr(cond, &pre_env, vctx, defs).map_err(FnContractError::EncodingError)?;
    let cond_bool = cond_val.to_bool().map_err(FnContractError::EncodingError)?;
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
    execute_loop_body(
        body,
        &mut post_env,
        &mut body_constraints,
        &inner_assumptions,
        vctx,
        defs,
    )?;

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
        let bounded = smt::int_ge(pre_m, &smt::int_lit(0));
        let decreases_strict = smt::int_lt(post_m, pre_m);
        let term_ok = smt::bool_and(&[&bounded, &decreases_strict]);
        vc_solver.assert(smt::bool_not(&term_ok));
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
                conjuncts.push(smt::int_eq(pre_j, post_j));
            }
            // Measure i strictly decreases and is bounded
            let pre_i = pre_measures[i]
                .as_int()
                .map_err(FnContractError::EncodingError)?;
            let post_i = post_measures[i]
                .as_int()
                .map_err(FnContractError::EncodingError)?;
            conjuncts.push(smt::int_ge(pre_i, &smt::int_lit(0)));
            conjuncts.push(smt::int_lt(post_i, pre_i));
            let refs: Vec<&Bool> = conjuncts.iter().collect();
            lex_cases.push(smt::bool_and(&refs));
        }
        let lex_refs: Vec<&Bool> = lex_cases.iter().collect();
        let lex_ok = smt::bool_or(&lex_refs);
        vc_solver.assert(smt::bool_not(&lex_ok));
    }

    // Assert lambda axioms after all encoding
    assert_lambda_axioms_on(&vc_solver);

    match vc_solver.check() {
        SatResult::Unsat => Ok(()),
        SatResult::Sat | SatResult::Unknown(_) => Err(FnContractError::EncodingError(
            crate::messages::FN_LOOP_TERMINATION_FAILED.to_owned(),
        )),
    }
}

/// Execute a while loop body, updating the environment with post-iteration values.
///
/// Processes assignments (`BinOp(OpEq, Var(name), expr)`) sequentially,
/// `VarDecl` for local temporaries, nested Blocks, and nested While loops.
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
            let val =
                encode_pure_expr(init, env, vctx, defs).map_err(FnContractError::EncodingError)?;
            env.insert(name.clone(), val);
            execute_loop_body(rest, env, constraints, assumptions, vctx, defs)
        }

        // Assignment: var = expr
        IRExpr::BinOp {
            op, left, right, ..
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
            let cond_val =
                encode_pure_expr(cond, env, vctx, defs).map_err(FnContractError::EncodingError)?;
            let cond_bool = cond_val.to_bool().map_err(FnContractError::EncodingError)?;

            // Then-branch: collect constraints separately, guard with cond
            let mut then_assumptions: Vec<Bool> = assumptions.to_vec();
            then_assumptions.push(cond_bool.clone());
            let mut then_constraints: Vec<Bool> = Vec::new();
            let mut then_env = env.clone();
            execute_loop_body(
                then_body,
                &mut then_env,
                &mut then_constraints,
                &then_assumptions,
                vctx,
                defs,
            )?;

            // Else-branch: collect constraints separately, guard with ¬cond
            let mut else_assumptions: Vec<Bool> = assumptions.to_vec();
            else_assumptions.push(smt::bool_not(&cond_bool));
            let mut else_constraints: Vec<Bool> = Vec::new();
            let mut else_env = env.clone();
            if let Some(eb) = else_body {
                execute_loop_body(
                    eb,
                    &mut else_env,
                    &mut else_constraints,
                    &else_assumptions,
                    vctx,
                    defs,
                )?;
            }

            // Guard branch constraints before propagating to the shared vector
            for c in then_constraints {
                constraints.push(smt::bool_implies(&cond_bool, &c));
            }
            for c in else_constraints {
                constraints.push(smt::bool_implies(&smt::bool_not(&cond_bool), &c));
            }

            // Merge: for each variable that changed in either branch,
            // set it to ite(cond, then_val, else_val)
            let all_keys: HashSet<String> =
                then_env.keys().chain(else_env.keys()).cloned().collect();
            for key in all_keys {
                let then_val = then_env.get(&key);
                let else_val = else_env.get(&key);
                if let (Some(tv), Some(ev)) = (then_val, else_val) {
                    let merged =
                        encode_ite(&cond_bool, tv, ev).map_err(FnContractError::EncodingError)?;
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
            let counter = LOOP_VAR_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
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
                let inv_bool = inv_val.to_bool().map_err(FnContractError::EncodingError)?;
                constraints.push(inv_bool);
            }

            // Assert ¬inner_cond (inner loop exited)
            let cond_val = encode_pure_expr(inner_cond, env, vctx, defs)
                .map_err(FnContractError::EncodingError)?;
            let cond_bool = cond_val.to_bool().map_err(FnContractError::EncodingError)?;
            constraints.push(smt::bool_not(&cond_bool));

            Ok(())
        }

        // Assert in loop body: VC check using assumptions (invariant ∧ cond ∧ fn_requires)
        // as context. If proved, assertion becomes available as a fact for subsequent code.
        IRExpr::Assert {
            expr: assert_expr,
            span,
        } => {
            let assert_val = encode_pure_expr(assert_expr, env, vctx, defs)
                .map_err(FnContractError::EncodingError)?;
            let assert_bool = assert_val
                .to_bool()
                .map_err(FnContractError::EncodingError)?;

            // VC check: prove assert_expr holds given current assumptions + constraints
            let vc_solver = new_timed_solver();
            assert_lambda_axioms_on(&vc_solver);
            for assumption in assumptions {
                vc_solver.assert(assumption);
            }
            for c in constraints.iter() {
                vc_solver.assert(c);
            }
            vc_solver.assert(smt::bool_not(&assert_bool));
            assert_lambda_axioms_on(&vc_solver);

            match vc_solver.check() {
                SatResult::Unsat => {
                    // Proved: assertion holds in loop body. Make available as fact.
                    constraints.push(assert_bool);
                    Ok(())
                }
                SatResult::Sat | SatResult::Unknown(_) => {
                    Err(FnContractError::EncodingError(if let Some(sp) = span {
                        format!(
                            "{} (at byte offset {}..{})",
                            crate::messages::FN_ASSERT_FAILED,
                            sp.start,
                            sp.end,
                        )
                    } else {
                        crate::messages::FN_ASSERT_FAILED.to_owned()
                    }))
                }
            }
        }

        // Assume in loop body: add as a fact without proof.
        IRExpr::Assume {
            expr: assume_expr, ..
        } => {
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

// ── Recursive call encoding ─────────────────────────────────────────

/// Encode a recursive self-call: instead of expanding the body (which
/// would diverge), return a fresh Z3 variable constrained by the
/// function's `ensures` clauses with actual arguments substituted.
///
/// This implements modular verification: we trust the postcondition for
/// recursive calls (after proves it holds for all cases via induction).
pub(super) fn encode_recursive_self_call(
    self_fn: &crate::ir::types::IRFunction,
    actual_args: &[IRExpr],
    env: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
) -> Result<SmtValue, String> {
    static REC_CALL_COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

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
                // hold for recursive calls ( proves this by induction).
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
pub(super) fn extract_return_type(ty: &crate::ir::types::IRType) -> crate::ir::types::IRType {
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
    let entry = defs
        .get(&func.name)
        .ok_or_else(|| format!("function '{}' not found in DefEnv", func.name))?;
    let params = &entry.params;

    // Create Z3 variables for each parameter
    let mut env: HashMap<String, SmtValue> = HashMap::new();
    for (name, ty) in params {
        let var = make_z3_var(name, ty)?;
        env.insert(name.clone(), var);
    }

    // Find all recursive call sites with their path conditions
    // call_sites: (path_conditions, actual_args, env_at_call_site)
    let mut call_sites: Vec<RecursiveCallSite> = Vec::new();
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
            let vc_solver = new_timed_solver();
            assert_lambda_axioms_on(&vc_solver);
            for req_bool in &requires_bools {
                vc_solver.assert(req_bool);
            }
            for pc in path_conds {
                vc_solver.assert(pc);
            }
            // Assert ¬callee_requires — looking for counterexample
            let callee_refs: Vec<&Bool> = callee_requires_bools.iter().collect();
            let all_callee_req = smt::bool_and(&callee_refs);
            vc_solver.assert(smt::bool_not(&all_callee_req));
            if vc_solver.check() != SatResult::Unsat {
                return Err(crate::messages::FN_CALL_PRECONDITION_FAILED.to_owned());
            }
        }

        // ── VC2: Measure decreases and is bounded ───────────────────
        // requires(caller) ∧ path_condition → post_measure < pre_measure ∧ post_measure ≥ 0
        {
            let vc_solver = new_timed_solver();
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
                let bounded = smt::int_ge(post_m, &smt::int_lit(0));
                let decreases_strict = smt::int_lt(post_m, pre_m);
                let term_ok = smt::bool_and(&[&bounded, &decreases_strict]);
                vc_solver.assert(smt::bool_not(&term_ok));
            } else {
                // Lexicographic: ∃ i. (∀ j < i. mⱼ_post == mⱼ_pre) ∧ mᵢ_post < mᵢ_pre ∧ mᵢ_post ≥ 0
                let mut lex_cases = Vec::new();
                for i in 0..pre_measures.len() {
                    let mut conjuncts = Vec::new();
                    for j in 0..i {
                        let pre_j = pre_measures[j].as_int()?;
                        let post_j = post_measures[j].as_int()?;
                        conjuncts.push(smt::int_eq(pre_j, post_j));
                    }
                    let pre_i = pre_measures[i].as_int()?;
                    let post_i = post_measures[i].as_int()?;
                    conjuncts.push(smt::int_ge(post_i, &smt::int_lit(0)));
                    conjuncts.push(smt::int_lt(post_i, pre_i));
                    let refs: Vec<&Bool> = conjuncts.iter().collect();
                    lex_cases.push(smt::bool_and(&refs));
                }
                let lex_refs: Vec<&Bool> = lex_cases.iter().collect();
                let lex_ok = smt::bool_or(&lex_refs);
                vc_solver.assert(smt::bool_not(&lex_ok));
            }

            match vc_solver.check() {
                SatResult::Unsat => {}
                _ => {
                    return Err(crate::messages::FN_TERMINATION_FAILED.to_owned());
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
    call_sites: &mut Vec<RecursiveCallSite>,
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
                collect_recursive_calls(
                    func, fn_name, params, env, vctx, defs, path_conds, call_sites,
                )?;
                collect_recursive_calls(
                    arg, fn_name, params, env, vctx, defs, path_conds, call_sites,
                )?;
            }
        }
        IRExpr::Lam {
            param,
            param_type,
            body,
            ..
        } => {
            // Lam introduces a binding — create a Z3 var for it
            if !env.contains_key(param) {
                if let Ok(var) = make_z3_var(param, param_type) {
                    env.insert(param.clone(), var);
                }
            }
            collect_recursive_calls(
                body, fn_name, params, env, vctx, defs, path_conds, call_sites,
            )?;
        }
        IRExpr::BinOp { left, right, .. } => {
            collect_recursive_calls(
                left, fn_name, params, env, vctx, defs, path_conds, call_sites,
            )?;
            collect_recursive_calls(
                right, fn_name, params, env, vctx, defs, path_conds, call_sites,
            )?;
        }
        IRExpr::UnOp { operand, .. } => {
            collect_recursive_calls(
                operand, fn_name, params, env, vctx, defs, path_conds, call_sites,
            )?;
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
            collect_recursive_calls(
                then_body, fn_name, params, env, vctx, defs, path_conds, call_sites,
            )?;
            path_conds.pop();

            if let Some(eb) = else_body {
                path_conds.push(smt::bool_not(&cond_bool));
                collect_recursive_calls(
                    eb, fn_name, params, env, vctx, defs, path_conds, call_sites,
                )?;
                path_conds.pop();
            }
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            collect_recursive_calls(
                scrutinee, fn_name, params, env, vctx, defs, path_conds, call_sites,
            )?;
            let scrut_val = encode_pure_expr(scrutinee, env, vctx, defs)?;

            // Match arms are sequential: arm k is reached only if all prior
            // arm conditions (pattern ∧ guard) were false. Accumulate the
            // negation of prior arm conditions as path context.
            let mut prior_negations: Vec<Bool> = Vec::new();
            for arm in arms {
                let pat_cond =
                    encode_pattern_cond(&scrut_val, &arm.pattern, &HashMap::new(), vctx)?;
                let full_arm_cond = if let Some(guard) = &arm.guard {
                    let guard_val = encode_pure_expr(guard, env, vctx, defs)?;
                    let guard_bool = guard_val.to_bool()?;
                    smt::bool_and(&[&pat_cond, &guard_bool])
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
                    collect_recursive_calls(
                        &arm.body, fn_name, params, env, vctx, defs, path_conds, call_sites,
                    )?;
                    path_conds.pop(); // guard
                } else {
                    collect_recursive_calls(
                        &arm.body, fn_name, params, env, vctx, defs, path_conds, call_sites,
                    )?;
                }
                path_conds.pop(); // pattern
                                  // Pop prior negations
                for _ in 0..n_prior {
                    path_conds.pop();
                }

                // For subsequent arms: this arm's condition was false
                prior_negations.push(smt::bool_not(&full_arm_cond));
            }
        }
        IRExpr::Let { bindings, body, .. } => {
            for b in bindings {
                collect_recursive_calls(
                    &b.expr, fn_name, params, env, vctx, defs, path_conds, call_sites,
                )?;
                // Extend env with the binding so it's available in the body
                if let Ok(val) = encode_pure_expr(&b.expr, env, vctx, defs) {
                    env.insert(b.name.clone(), val);
                }
            }
            collect_recursive_calls(
                body, fn_name, params, env, vctx, defs, path_conds, call_sites,
            )?;
        }
        IRExpr::Block { exprs, .. } => {
            for e in exprs {
                collect_recursive_calls(
                    e, fn_name, params, env, vctx, defs, path_conds, call_sites,
                )?;
            }
        }
        IRExpr::VarDecl {
            name, init, rest, ..
        } => {
            collect_recursive_calls(
                init, fn_name, params, env, vctx, defs, path_conds, call_sites,
            )?;
            // Extend env with the var declaration
            if let Ok(val) = encode_pure_expr(init, env, vctx, defs) {
                env.insert(name.clone(), val);
            }
            collect_recursive_calls(
                rest, fn_name, params, env, vctx, defs, path_conds, call_sites,
            )?;
        }
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            collect_recursive_calls(
                expr, fn_name, params, env, vctx, defs, path_conds, call_sites,
            )?;
        }
        _ => {}
    }
    Ok(())
}

/// Encode an imperative if/else that may contain while loops or assignments.
///
/// Evaluates both branches with cloned environments, then merges
/// modified variables using ITE on the condition.
#[allow(clippy::too_many_arguments)]
pub(super) fn encode_imperative_if_else(
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
    let cond_val =
        encode_pure_expr(cond, env, vctx, defs).map_err(FnContractError::EncodingError)?;
    let cond_bool = cond_val.to_bool().map_err(FnContractError::EncodingError)?;

    // Then-branch: condition is known true → add it as assumption.
    // Collect constraints separately so they can be guarded by cond.
    let mut then_assumptions: Vec<Bool> = extra_assumptions.to_vec();
    then_assumptions.push(cond_bool.clone());
    let mut then_constraints: Vec<Bool> = Vec::new();
    let mut then_env = env.clone();
    let then_val = encode_fn_body(
        then_body,
        &mut then_env,
        &mut then_constraints,
        fn_requires,
        &then_assumptions,
        self_fn,
        vctx,
        defs,
    )?;

    // Else-branch: condition is known false → add ¬cond as assumption.
    let mut else_assumptions: Vec<Bool> = extra_assumptions.to_vec();
    else_assumptions.push(smt::bool_not(&cond_bool));
    let mut else_constraints: Vec<Bool> = Vec::new();
    let mut else_env = env.clone();
    let else_val = if let Some(eb) = else_body {
        encode_fn_body(
            eb,
            &mut else_env,
            &mut else_constraints,
            fn_requires,
            &else_assumptions,
            self_fn,
            vctx,
            defs,
        )?
    } else {
        smt::bool_val(true)
    };

    // Merge environments: for variables that differ between branches, use ITE
    let all_keys: HashSet<String> = then_env.keys().chain(else_env.keys()).cloned().collect();
    for key in all_keys {
        let then_v = then_env.get(&key);
        let else_v = else_env.get(&key);
        if let (Some(tv), Some(ev)) = (then_v, else_v) {
            let merged = encode_ite(&cond_bool, tv, ev).map_err(FnContractError::EncodingError)?;
            env.insert(key, merged);
        }
    }

    // Guard branch constraints with the branch condition.
    // Then-branch constraints hold only when cond is true.
    // Else-branch constraints hold only when cond is false.
    // This prevents unreachable-branch facts from polluting the solver.
    for c in then_constraints {
        solver_constraints.push(smt::bool_implies(&cond_bool, &c));
    }
    for c in else_constraints {
        solver_constraints.push(smt::bool_implies(&smt::bool_not(&cond_bool), &c));
    }

    // The value of the if/else expression
    encode_ite(&cond_bool, &then_val, &else_val).map_err(FnContractError::EncodingError)
}
