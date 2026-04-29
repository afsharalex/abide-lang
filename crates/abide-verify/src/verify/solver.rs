//! Solver backend trait and Z3 implementation.
//!
//! This is the ONLY file in verify/ that imports from `z3::` directly.
//! All other files use type aliases and helper functions from `smt.rs`,
//! which dispatches to the active backend defined here.
//!
//! To add a second solver (e.g., CVC5):
//! 1. Implement `SolverBackend` for a `CVC5Backend` struct
//! 2. Change the type aliases in this file to point to CVC5Backend
//! 3. All verify/ code automatically uses the new backend

use std::borrow::Borrow;
use std::cell::{Cell, RefCell};
use std::fmt;

use std::collections::BTreeMap;
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc;
use std::time::Duration;

// ── Z3 imports (the ONLY place in verify/ that touches z3::) ─────────
use z3::ast::{
    Array as Z3Array, Ast as Z3Ast, Bool as Z3Bool, Dynamic as Z3Dynamic, Int as Z3Int,
    Real as Z3Real,
};
use z3::{
    DatatypeAccessor as Z3DatatypeAccessor, DatatypeBuilder as Z3DatatypeBuilder,
    Fixedpoint as Z3Fixedpoint, FuncDecl as Z3FuncDecl, Model as Z3Model, Params as Z3Params,
    SatResult as Z3SatResult, Solver as Z3Solver, Sort as Z3Sort,
};

// ── Public re-exports for downstream consumers ──────────────────────
// These allow files that import from smt.rs (or directly from solver)
// to access z3 trait/type names without their own `use z3::` imports.
pub use z3::ast::Ast;

use cvc5_rs::{
    unknown_explanation_to_string as cvc5_unknown_to_string, Kind as Cvc5Kind,
    Solver as Cvc5Solver, Sort as Cvc5Sort, Term as Cvc5Term, TermManager as Cvc5TermManager,
};

// ── Solver-independent result type ──────────────────────────────────

/// Solver-independent satisfiability result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SatResult {
    Sat,
    Unsat,
    Unknown(String),
}

/// Result of a CHC (Constrained Horn Clause) satisfiability check.
/// Used by IC3/PDR and any other CHC-based verification strategy.
#[derive(Debug, Clone)]
pub enum ChcResult {
    /// Property holds — error state is unreachable.
    Proved,
    /// Property violated — error state is reachable.
    /// The answer string is the solver's derivation/counterexample in
    /// S-expression format (parseable for trace extraction).
    Counterexample(String),
    /// Solver could not determine result.
    Unknown(String),
}

/// Solver call limits applied at the actual backend check/query boundary.
///
/// A zero timeout means "no explicit limit". Callers should prefer passing a
/// clamped verifier budget here over setting a solver option separately.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SolverLimits {
    timeout_ms: u64,
}

impl SolverLimits {
    pub const NONE: Self = Self { timeout_ms: 0 };

    pub const fn from_timeout_ms(timeout_ms: u64) -> Self {
        Self { timeout_ms }
    }

    pub const fn timeout_ms(self) -> Option<u64> {
        if self.timeout_ms == 0 {
            None
        } else {
            Some(self.timeout_ms)
        }
    }

    fn timeout_duration(self) -> Option<Duration> {
        self.timeout_ms().map(Duration::from_millis)
    }
}

/// Backend-neutral view of a datatype constructor branch.
#[derive(Clone, Debug)]
pub struct DatatypeVariant<F> {
    pub name: String,
    pub constructor: F,
    pub tester: F,
    pub accessors: Vec<F>,
}

/// Backend-neutral datatype sort metadata consumed by the verifier.
#[derive(Debug)]
pub struct SolverDatatypeSort<S, F> {
    pub sort: S,
    pub variants: Vec<DatatypeVariant<F>>,
}

#[derive(Clone)]
pub struct Cvc5Context {
    tm: Cvc5TermManager,
}

impl fmt::Debug for Cvc5Context {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Cvc5Context").finish_non_exhaustive()
    }
}

#[derive(Clone)]
pub struct Cvc5Model {
    solver: Rc<RefCell<Cvc5Solver>>,
}

impl fmt::Debug for Cvc5Model {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Cvc5Model").finish_non_exhaustive()
    }
}

#[derive(Clone, Default)]
pub struct Cvc5Params {
    values: BTreeMap<String, String>,
}

impl fmt::Debug for Cvc5Params {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Cvc5Params")
            .field("values", &self.values)
            .finish()
    }
}

#[derive(Clone)]
pub struct Cvc5DatatypeBuilder {
    tm: Cvc5TermManager,
    name: String,
    variants: Vec<(String, Vec<(String, Cvc5Sort)>)>,
}

impl fmt::Debug for Cvc5DatatypeBuilder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Cvc5DatatypeBuilder")
            .field("name", &self.name)
            .field("variants", &self.variants)
            .finish()
    }
}

/// Concrete solver backend families supported by the verifier.
///
/// This stays separate from CLI-facing selection because the runtime
/// dispatcher will eventually support modes like `auto` and `both`
/// that are not themselves backend implementations.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SolverFamily {
    Z3,
    Cvc5,
}

thread_local! {
    static ACTIVE_SOLVER_FAMILY: RefCell<SolverFamily> = const { RefCell::new(SolverFamily::Z3) };
}

pub fn active_solver_family() -> SolverFamily {
    ACTIVE_SOLVER_FAMILY.with(|family| *family.borrow())
}

pub fn is_solver_family_available(family: SolverFamily) -> bool {
    match family {
        SolverFamily::Z3 => true,
        SolverFamily::Cvc5 => true,
    }
}

pub fn set_active_solver_family(family: SolverFamily) -> Result<(), String> {
    if !is_solver_family_available(family) {
        return Err(match family {
            SolverFamily::Z3 => "z3 backend is not available".to_owned(),
            SolverFamily::Cvc5 => "cvc5 backend is not available".to_owned(),
        });
    }
    ACTIVE_SOLVER_FAMILY.with(|active| *active.borrow_mut() = family);
    Ok(())
}

/// High-level verifier task classes used for backend routing.
///
/// The goal is not to mirror every call site one-to-one. This is a
/// coarse classification the router can use to prefer a solver with
/// the right theory support or proof engine for a given request.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VerificationTask {
    Satisfiability,
    BoundedModelCheck,
    Property,
    Scene,
    FunctionVc,
    Theorem,
    Liveness,
    Chc,
}

/// Backend capability profile used by the future multi-solver router.
///
/// This is intentionally descriptive rather than prescriptive: a
/// backend may support a feature natively, via a shim, or not at all.
/// The router can then prefer the strongest native backend while
/// still allowing a fallback encoding when appropriate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SolverCapabilities {
    pub arrays: bool,
    pub datatypes: bool,
    pub quantifiers: bool,
    pub models: bool,
    pub incremental: bool,
    pub chc: bool,
    pub native_sequences: bool,
    pub native_bags: bool,
    pub unsat_cores: bool,
}

impl SolverCapabilities {
    pub const fn supports(self, task: VerificationTask) -> bool {
        match task {
            VerificationTask::Satisfiability
            | VerificationTask::BoundedModelCheck
            | VerificationTask::Property
            | VerificationTask::Scene
            | VerificationTask::FunctionVc
            | VerificationTask::Theorem
            | VerificationTask::Liveness => {
                self.arrays && self.quantifiers && self.models && self.incremental
            }
            VerificationTask::Chc => self.chc,
        }
    }
}

/// Fine-grained theory/features requested by an encoding path.
///
/// The current Z3 backend satisfies the baseline profile. CVC5 can
/// later advertise stronger native support for sequences and bags
/// without forcing the front-end encoding to guess blindly.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct BackendRequirements {
    pub sequences: bool,
    pub bags: bool,
    pub unsat_cores: bool,
    pub chc: bool,
}

impl BackendRequirements {
    pub const fn for_task(task: VerificationTask) -> Self {
        Self {
            sequences: false,
            bags: false,
            unsat_cores: false,
            chc: matches!(task, VerificationTask::Chc),
        }
    }
}

/// Routing score used to prefer one backend over another for a task.
///
/// Higher is better. Negative values mean "do not select".
pub fn backend_score(
    family: SolverFamily,
    capabilities: SolverCapabilities,
    task: VerificationTask,
    requirements: BackendRequirements,
) -> i32 {
    if !capabilities.supports(task) {
        return -1;
    }
    if requirements.chc && !capabilities.chc {
        return -1;
    }
    if requirements.unsat_cores && !capabilities.unsat_cores {
        return -1;
    }

    let mut score = 0;

    if requirements.bags {
        score += if capabilities.native_bags { 100 } else { -20 };
    }
    if requirements.sequences {
        score += if capabilities.native_sequences {
            40
        } else {
            -10
        };
    }

    // Z3 remains the preferred CHC backend until a second CHC path is
    // implemented and validated to the same standard.
    if task == VerificationTask::Chc && family == SolverFamily::Z3 {
        score += 50;
    }

    score
}

fn with_z3_interrupt_after<R>(limits: SolverLimits, f: impl FnOnce() -> R) -> R {
    let Some(timeout) = limits.timeout_duration() else {
        return f();
    };

    let ctx = z3::Context::thread_local();
    std::thread::scope(|scope| {
        let handle = ctx.handle();
        let (done_tx, done_rx) = mpsc::channel();
        scope.spawn(move || {
            if done_rx.recv_timeout(timeout).is_err() {
                handle.interrupt();
            }
        });
        let result = f();
        let _ = done_tx.send(());
        result
    })
}

// ── SolverBackend trait ─────────────────────────────────────────────

/// Abstraction over an SMT solver backend.
///
/// Associated types represent the concrete AST node kinds, sorts,
/// function declarations, models, and ADT construction types.
///
/// This trait does NOT need to be object-safe (`dyn SolverBackend`).
/// All dispatch is compile-time via type aliases.
#[allow(clippy::too_many_arguments)]
pub trait SolverBackend {
    /// Which concrete backend family this implementation belongs to.
    fn family() -> SolverFamily;

    /// Native capabilities available on this backend.
    fn capabilities() -> SolverCapabilities;

    /// Backend-owned term construction context.
    ///
    /// Z3 does not require one, so it uses `()`. CVC5 will use this for
    /// its `TermManager`-style API.
    type Context: Clone + fmt::Debug;

    /// Create or obtain a backend context suitable for term construction.
    fn context_new() -> Self::Context;

    // ── Associated AST types ────────────────────────────────────────
    /// Boolean AST node.
    type Bool: Clone + fmt::Debug;
    /// Integer AST node.
    type Int: Clone + fmt::Debug;
    /// Real AST node.
    type Real: Clone + fmt::Debug;
    /// Dynamically-typed AST node (uninterpreted / generic).
    type Dynamic: Clone + fmt::Debug;
    /// Array AST node.
    type Array: Clone + fmt::Debug;

    // ── Sort / type ─────────────────────────────────────────────────
    type Sort: Clone + fmt::Debug;

    // ── Function declarations ───────────────────────────────────────
    type FuncDecl: fmt::Debug;

    // ── Model (counterexample extraction) ───────────────────────────
    type Model: fmt::Debug;

    // ── ADT construction ────────────────────────────────────────────
    type DatatypeSort: fmt::Debug;
    type DatatypeAccessor: fmt::Debug;
    type DatatypeBuilder: fmt::Debug;

    // ── CHC solving (IC3/PDR) ──────────────────────────────────────
    // No Fixedpoint associated type — CHC solving is exposed as a
    // single high-level method. Z3 uses Spacer internally; CVC5 would
    // use its own CHC solver.

    // ── Params ──────────────────────────────────────────────────────
    type Params: fmt::Debug;

    // ── Solver lifecycle ────────────────────────────────────────────
    fn solver_new(ctx: &Self::Context) -> Self;
    fn solver_assert(&self, c: &Self::Bool);
    fn solver_check(&self) -> SatResult;
    fn solver_check_with_limits(&self, limits: SolverLimits) -> SatResult {
        if let Some(timeout_ms) = limits.timeout_ms() {
            self.solver_set_timeout(timeout_ms);
        }
        self.solver_check()
    }
    fn solver_push(&self);
    fn solver_pop(&self);
    fn solver_set_timeout(&self, ms: u64);
    fn solver_get_model(&self) -> Option<Self::Model>;

    // ── Bool operations ─────────────────────────────────────────────
    fn bool_const(ctx: &Self::Context, val: bool) -> Self::Bool;
    fn bool_var(ctx: &Self::Context, name: &str) -> Self::Bool;
    fn bool_and(ctx: &Self::Context, args: &[&Self::Bool]) -> Self::Bool;
    fn bool_or(ctx: &Self::Context, args: &[&Self::Bool]) -> Self::Bool;
    fn bool_not(ctx: &Self::Context, b: &Self::Bool) -> Self::Bool;
    fn bool_implies(ctx: &Self::Context, a: &Self::Bool, b: &Self::Bool) -> Self::Bool;
    fn bool_xor(ctx: &Self::Context, a: &Self::Bool, b: &Self::Bool) -> Self::Bool;
    fn bool_eq(ctx: &Self::Context, a: &Self::Bool, b: &Self::Bool) -> Self::Bool;
    fn bool_ite(
        ctx: &Self::Context,
        cond: &Self::Bool,
        t: &Self::Bool,
        e: &Self::Bool,
    ) -> Self::Bool;

    // ── Int operations ──────────────────────────────────────────────
    fn int_lit(ctx: &Self::Context, n: i64) -> Self::Int;
    fn int_var(ctx: &Self::Context, name: &str) -> Self::Int;
    fn int_add(ctx: &Self::Context, args: &[&Self::Int]) -> Self::Int;
    fn int_sub(ctx: &Self::Context, args: &[&Self::Int]) -> Self::Int;
    fn int_mul(ctx: &Self::Context, args: &[&Self::Int]) -> Self::Int;
    fn int_div(ctx: &Self::Context, a: &Self::Int, b: &Self::Int) -> Self::Int;
    fn int_modulo(ctx: &Self::Context, a: &Self::Int, b: &Self::Int) -> Self::Int;
    fn int_neg(ctx: &Self::Context, a: &Self::Int) -> Self::Int;
    fn int_eq(ctx: &Self::Context, a: &Self::Int, b: &Self::Int) -> Self::Bool;
    fn int_lt(ctx: &Self::Context, a: &Self::Int, b: &Self::Int) -> Self::Bool;
    fn int_le(ctx: &Self::Context, a: &Self::Int, b: &Self::Int) -> Self::Bool;
    fn int_gt(ctx: &Self::Context, a: &Self::Int, b: &Self::Int) -> Self::Bool;
    fn int_ge(ctx: &Self::Context, a: &Self::Int, b: &Self::Int) -> Self::Bool;
    fn int_ite(ctx: &Self::Context, cond: &Self::Bool, t: &Self::Int, e: &Self::Int) -> Self::Int;

    // ── Real operations ─────────────────────────────────────────────
    fn real_val(ctx: &Self::Context, num: i64, den: i64) -> Self::Real;
    fn real_var(ctx: &Self::Context, name: &str) -> Self::Real;
    fn real_add(ctx: &Self::Context, args: &[&Self::Real]) -> Self::Real;
    fn real_sub(ctx: &Self::Context, args: &[&Self::Real]) -> Self::Real;
    fn real_mul(ctx: &Self::Context, args: &[&Self::Real]) -> Self::Real;
    fn real_div(ctx: &Self::Context, a: &Self::Real, b: &Self::Real) -> Self::Real;
    fn real_eq(ctx: &Self::Context, a: &Self::Real, b: &Self::Real) -> Self::Bool;
    fn real_lt(ctx: &Self::Context, a: &Self::Real, b: &Self::Real) -> Self::Bool;
    fn real_le(ctx: &Self::Context, a: &Self::Real, b: &Self::Real) -> Self::Bool;
    fn real_gt(ctx: &Self::Context, a: &Self::Real, b: &Self::Real) -> Self::Bool;
    fn real_ge(ctx: &Self::Context, a: &Self::Real, b: &Self::Real) -> Self::Bool;
    fn real_ite(
        ctx: &Self::Context,
        cond: &Self::Bool,
        t: &Self::Real,
        e: &Self::Real,
    ) -> Self::Real;

    // ── Sort operations ─────────────────────────────────────────────
    fn int_sort(ctx: &Self::Context) -> Self::Sort;
    fn bool_sort(ctx: &Self::Context) -> Self::Sort;
    fn real_sort(ctx: &Self::Context) -> Self::Sort;
    fn array_sort(ctx: &Self::Context, domain: &Self::Sort, range: &Self::Sort) -> Self::Sort;
    fn sort_array_domain(ctx: &Self::Context, s: &Self::Sort) -> Option<Self::Sort>;
    fn sort_array_range(ctx: &Self::Context, s: &Self::Sort) -> Option<Self::Sort>;
    fn sort_to_string(ctx: &Self::Context, s: &Self::Sort) -> String;

    // ── Dynamic operations ──────────────────────────────────────────
    fn dynamic_fresh(ctx: &Self::Context, prefix: &str, sort: &Self::Sort) -> Self::Dynamic;
    fn dynamic_const(ctx: &Self::Context, name: &str, sort: &Self::Sort) -> Self::Dynamic;
    fn dynamic_from_bool(ctx: &Self::Context, b: &Self::Bool) -> Self::Dynamic;
    fn dynamic_from_int(ctx: &Self::Context, i: &Self::Int) -> Self::Dynamic;
    fn dynamic_from_real(ctx: &Self::Context, r: &Self::Real) -> Self::Dynamic;
    fn dynamic_from_array(ctx: &Self::Context, a: &Self::Array) -> Self::Dynamic;
    fn dynamic_as_bool(ctx: &Self::Context, d: &Self::Dynamic) -> Option<Self::Bool>;
    fn dynamic_as_int(ctx: &Self::Context, d: &Self::Dynamic) -> Option<Self::Int>;
    fn dynamic_as_real(ctx: &Self::Context, d: &Self::Dynamic) -> Option<Self::Real>;
    fn dynamic_as_array(ctx: &Self::Context, d: &Self::Dynamic) -> Option<Self::Array>;
    fn dynamic_eq(ctx: &Self::Context, a: &Self::Dynamic, b: &Self::Dynamic) -> Self::Bool;
    fn dynamic_ite(
        ctx: &Self::Context,
        cond: &Self::Bool,
        t: &Self::Dynamic,
        e: &Self::Dynamic,
    ) -> Self::Dynamic;
    fn dynamic_get_sort(ctx: &Self::Context, d: &Self::Dynamic) -> Self::Sort;

    // ── Array operations ────────────────────────────────────────────
    fn array_new_const(
        ctx: &Self::Context,
        name: &str,
        domain: &Self::Sort,
        range: &Self::Sort,
    ) -> Self::Array;
    fn array_const_array(
        ctx: &Self::Context,
        domain: &Self::Sort,
        default: &Self::Dynamic,
    ) -> Self::Array;
    fn array_select(ctx: &Self::Context, a: &Self::Array, index: &Self::Dynamic) -> Self::Dynamic;
    fn array_store(
        ctx: &Self::Context,
        a: &Self::Array,
        index: &Self::Dynamic,
        value: &Self::Dynamic,
    ) -> Self::Array;
    fn array_eq(ctx: &Self::Context, a: &Self::Array, b: Self::Array) -> Self::Bool;
    fn array_ite(
        ctx: &Self::Context,
        cond: &Self::Bool,
        t: &Self::Array,
        e: &Self::Array,
    ) -> Self::Array;
    fn array_get_sort(ctx: &Self::Context, a: &Self::Array) -> Self::Sort;

    // ── Quantifiers ─────────────────────────────────────────────────
    fn forall(ctx: &Self::Context, bound: &[&Self::Dynamic], body: &Self::Bool) -> Self::Bool;
    fn exists(ctx: &Self::Context, bound: &[&Self::Dynamic], body: &Self::Bool) -> Self::Bool;
    fn lambda(ctx: &Self::Context, bound: &[&Self::Dynamic], body: &Self::Dynamic) -> Self::Array;

    // ── Function declarations ───────────────────────────────────────
    fn func_decl_new(
        ctx: &Self::Context,
        name: &str,
        domain: &[&Self::Sort],
        range: &Self::Sort,
    ) -> Self::FuncDecl;
    fn func_decl_apply(
        ctx: &Self::Context,
        f: &Self::FuncDecl,
        args: &[&Self::Dynamic],
    ) -> Self::Dynamic;
    fn func_decl_name(ctx: &Self::Context, f: &Self::FuncDecl) -> String;

    // ── ADT construction ────────────────────────────────────────────
    fn datatype_builder_new(ctx: &Self::Context, name: &str) -> Self::DatatypeBuilder;
    fn datatype_builder_variant(
        ctx: &Self::Context,
        builder: Self::DatatypeBuilder,
        name: &str,
        fields: Vec<(&str, Self::DatatypeAccessor)>,
    ) -> Self::DatatypeBuilder;
    fn datatype_builder_finish(
        ctx: &Self::Context,
        builder: Self::DatatypeBuilder,
    ) -> Self::DatatypeSort;
    fn datatype_accessor_sort(ctx: &Self::Context, sort: Self::Sort) -> Self::DatatypeAccessor;

    // ── Params ──────────────────────────────────────────────────────
    fn params_new() -> Self::Params;
    fn params_set_bool(params: &mut Self::Params, key: &str, val: bool);
    fn params_set_u32(params: &mut Self::Params, key: &str, val: u32);
    fn params_set_symbol(params: &mut Self::Params, key: &str, val: &str);

    // ── Model operations ────────────────────────────────────────────
    fn model_eval_bool(model: &Self::Model, b: &Self::Bool) -> Option<bool>;
    fn model_eval_int(model: &Self::Model, i: &Self::Int) -> Option<i64>;
    fn model_eval_dynamic(model: &Self::Model, d: &Self::Dynamic) -> Option<String>;
}

// ── Z3 backend ──────────────────────────────────────────────────────

/// Z3 backend implementing the `SolverBackend` trait.
///
/// Wraps a `z3::Solver` and delegates all operations to the z3 crate.
pub struct Z3Backend {
    solver: Z3Solver,
    timeout_ms: Cell<u64>,
}

impl fmt::Debug for Z3Backend {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Z3Backend").finish_non_exhaustive()
    }
}

impl SolverBackend for Z3Backend {
    fn family() -> SolverFamily {
        SolverFamily::Z3
    }

    fn capabilities() -> SolverCapabilities {
        SolverCapabilities {
            arrays: true,
            datatypes: true,
            quantifiers: true,
            models: true,
            incremental: true,
            chc: true,
            native_sequences: false,
            native_bags: false,
            unsat_cores: false,
        }
    }

    type Context = ();

    fn context_new() -> Self::Context {}

    type Bool = Z3Bool;
    type Int = Z3Int;
    type Real = Z3Real;
    type Dynamic = Z3Dynamic;
    type Array = Z3Array;
    type Sort = Z3Sort;
    type FuncDecl = Z3FuncDecl;
    type Model = Z3Model;
    type DatatypeSort = SolverDatatypeSort<Z3Sort, Z3FuncDecl>;
    type DatatypeAccessor = Z3DatatypeAccessor;
    type DatatypeBuilder = Z3DatatypeBuilder;
    type Params = Z3Params;

    // ── Solver lifecycle ────────────────────────────────────────────

    fn solver_new(_ctx: &Self::Context) -> Self {
        Self {
            solver: Z3Solver::new(),
            timeout_ms: Cell::new(0),
        }
    }

    fn solver_assert(&self, c: &Z3Bool) {
        self.solver.assert(c);
    }

    fn solver_check(&self) -> SatResult {
        self.solver_check_with_limits(SolverLimits::from_timeout_ms(self.timeout_ms.get()))
    }

    fn solver_check_with_limits(&self, limits: SolverLimits) -> SatResult {
        if let Some(timeout_ms) = limits.timeout_ms() {
            self.solver_set_timeout(timeout_ms);
        }
        with_z3_interrupt_after(limits, || match self.solver.check() {
            Z3SatResult::Sat => SatResult::Sat,
            Z3SatResult::Unsat => SatResult::Unsat,
            Z3SatResult::Unknown => {
                SatResult::Unknown(self.solver.get_reason_unknown().unwrap_or_default())
            }
        })
    }

    fn solver_push(&self) {
        self.solver.push();
    }

    fn solver_pop(&self) {
        self.solver.pop(1);
    }

    fn solver_set_timeout(&self, ms: u64) {
        self.timeout_ms.set(ms);
        let mut params = Z3Params::new();
        params.set_u32("timeout", ms.min(u64::from(u32::MAX)) as u32);
        self.solver.set_params(&params);
    }

    fn solver_get_model(&self) -> Option<Z3Model> {
        self.solver.get_model()
    }

    // ── Bool operations ─────────────────────────────────────────────

    fn bool_const(_ctx: &Self::Context, val: bool) -> Z3Bool {
        Z3Bool::from_bool(val)
    }

    fn bool_var(_ctx: &Self::Context, name: &str) -> Z3Bool {
        Z3Bool::new_const(name)
    }

    fn bool_and(_ctx: &Self::Context, args: &[&Z3Bool]) -> Z3Bool {
        Z3Bool::and(args)
    }

    fn bool_or(_ctx: &Self::Context, args: &[&Z3Bool]) -> Z3Bool {
        Z3Bool::or(args)
    }

    fn bool_not(_ctx: &Self::Context, b: &Z3Bool) -> Z3Bool {
        b.not()
    }

    fn bool_implies(_ctx: &Self::Context, a: &Z3Bool, b: &Z3Bool) -> Z3Bool {
        a.implies(b)
    }

    fn bool_xor(_ctx: &Self::Context, a: &Z3Bool, b: &Z3Bool) -> Z3Bool {
        Z3Bool::xor(a, b)
    }

    fn bool_eq(_ctx: &Self::Context, a: &Z3Bool, b: &Z3Bool) -> Z3Bool {
        a.eq(b.clone())
    }

    fn bool_ite(_ctx: &Self::Context, cond: &Z3Bool, t: &Z3Bool, e: &Z3Bool) -> Z3Bool {
        cond.ite(t, e)
    }

    // ── Int operations ──────────────────────────────────────────────

    fn int_lit(_ctx: &Self::Context, n: i64) -> Z3Int {
        Z3Int::from_i64(n)
    }

    fn int_var(_ctx: &Self::Context, name: &str) -> Z3Int {
        Z3Int::new_const(name)
    }

    fn int_add(_ctx: &Self::Context, args: &[&Z3Int]) -> Z3Int {
        Z3Int::add(args)
    }

    fn int_sub(_ctx: &Self::Context, args: &[&Z3Int]) -> Z3Int {
        Z3Int::sub(args)
    }

    fn int_mul(_ctx: &Self::Context, args: &[&Z3Int]) -> Z3Int {
        Z3Int::mul(args)
    }

    fn int_div(_ctx: &Self::Context, a: &Z3Int, b: &Z3Int) -> Z3Int {
        a.div(b)
    }

    fn int_modulo(_ctx: &Self::Context, a: &Z3Int, b: &Z3Int) -> Z3Int {
        a.modulo(b)
    }

    fn int_neg(_ctx: &Self::Context, a: &Z3Int) -> Z3Int {
        Z3Int::unary_minus(a)
    }

    fn int_eq(_ctx: &Self::Context, a: &Z3Int, b: &Z3Int) -> Z3Bool {
        a.eq(b)
    }

    fn int_lt(_ctx: &Self::Context, a: &Z3Int, b: &Z3Int) -> Z3Bool {
        a.lt(b)
    }

    fn int_le(_ctx: &Self::Context, a: &Z3Int, b: &Z3Int) -> Z3Bool {
        a.le(b)
    }

    fn int_gt(_ctx: &Self::Context, a: &Z3Int, b: &Z3Int) -> Z3Bool {
        a.gt(b)
    }

    fn int_ge(_ctx: &Self::Context, a: &Z3Int, b: &Z3Int) -> Z3Bool {
        a.ge(b)
    }

    fn int_ite(_ctx: &Self::Context, cond: &Z3Bool, t: &Z3Int, e: &Z3Int) -> Z3Int {
        cond.ite(t, e)
    }

    // ── Real operations ─────────────────────────────────────────────

    fn real_val(_ctx: &Self::Context, num: i64, den: i64) -> Z3Real {
        Z3Real::from_rational(num, den)
    }

    fn real_var(_ctx: &Self::Context, name: &str) -> Z3Real {
        Z3Real::new_const(name)
    }

    fn real_add(_ctx: &Self::Context, args: &[&Z3Real]) -> Z3Real {
        Z3Real::add(args)
    }

    fn real_sub(_ctx: &Self::Context, args: &[&Z3Real]) -> Z3Real {
        Z3Real::sub(args)
    }

    fn real_mul(_ctx: &Self::Context, args: &[&Z3Real]) -> Z3Real {
        Z3Real::mul(args)
    }

    fn real_div(_ctx: &Self::Context, a: &Z3Real, b: &Z3Real) -> Z3Real {
        Z3Real::div(a, b)
    }

    fn real_eq(_ctx: &Self::Context, a: &Z3Real, b: &Z3Real) -> Z3Bool {
        a.eq(b.clone())
    }

    fn real_lt(_ctx: &Self::Context, a: &Z3Real, b: &Z3Real) -> Z3Bool {
        Z3Real::lt(a, b)
    }

    fn real_le(_ctx: &Self::Context, a: &Z3Real, b: &Z3Real) -> Z3Bool {
        Z3Real::le(a, b)
    }

    fn real_gt(_ctx: &Self::Context, a: &Z3Real, b: &Z3Real) -> Z3Bool {
        Z3Real::gt(a, b)
    }

    fn real_ge(_ctx: &Self::Context, a: &Z3Real, b: &Z3Real) -> Z3Bool {
        Z3Real::ge(a, b)
    }

    fn real_ite(_ctx: &Self::Context, cond: &Z3Bool, t: &Z3Real, e: &Z3Real) -> Z3Real {
        cond.ite(t, e)
    }

    // ── Sort operations ─────────────────────────────────────────────

    fn int_sort(_ctx: &Self::Context) -> Z3Sort {
        Z3Sort::int()
    }

    fn bool_sort(_ctx: &Self::Context) -> Z3Sort {
        Z3Sort::bool()
    }

    fn real_sort(_ctx: &Self::Context) -> Z3Sort {
        Z3Sort::real()
    }

    fn array_sort(_ctx: &Self::Context, domain: &Z3Sort, range: &Z3Sort) -> Z3Sort {
        Z3Sort::array(domain, range)
    }

    fn sort_array_domain(_ctx: &Self::Context, s: &Z3Sort) -> Option<Z3Sort> {
        s.array_domain()
    }

    fn sort_array_range(_ctx: &Self::Context, s: &Z3Sort) -> Option<Z3Sort> {
        s.array_range()
    }

    fn sort_to_string(_ctx: &Self::Context, s: &Z3Sort) -> String {
        s.to_string()
    }

    // ── Dynamic operations ──────────────────────────────────────────

    fn dynamic_fresh(_ctx: &Self::Context, prefix: &str, sort: &Z3Sort) -> Z3Dynamic {
        Z3Dynamic::fresh_const(prefix, sort)
    }

    fn dynamic_const(_ctx: &Self::Context, name: &str, sort: &Z3Sort) -> Z3Dynamic {
        Z3Dynamic::new_const(name, sort)
    }

    fn dynamic_from_bool(_ctx: &Self::Context, b: &Z3Bool) -> Z3Dynamic {
        Z3Dynamic::from_ast(b)
    }

    fn dynamic_from_int(_ctx: &Self::Context, i: &Z3Int) -> Z3Dynamic {
        Z3Dynamic::from_ast(i)
    }

    fn dynamic_from_real(_ctx: &Self::Context, r: &Z3Real) -> Z3Dynamic {
        Z3Dynamic::from_ast(r)
    }

    fn dynamic_from_array(_ctx: &Self::Context, a: &Z3Array) -> Z3Dynamic {
        Z3Dynamic::from_ast(a)
    }

    fn dynamic_as_bool(_ctx: &Self::Context, d: &Z3Dynamic) -> Option<Z3Bool> {
        d.as_bool()
    }

    fn dynamic_as_int(_ctx: &Self::Context, d: &Z3Dynamic) -> Option<Z3Int> {
        d.as_int()
    }

    fn dynamic_as_real(_ctx: &Self::Context, d: &Z3Dynamic) -> Option<Z3Real> {
        d.as_real()
    }

    fn dynamic_as_array(_ctx: &Self::Context, d: &Z3Dynamic) -> Option<Z3Array> {
        d.as_array()
    }

    fn dynamic_eq(_ctx: &Self::Context, a: &Z3Dynamic, b: &Z3Dynamic) -> Z3Bool {
        a.eq(b.clone())
    }

    fn dynamic_ite(_ctx: &Self::Context, cond: &Z3Bool, t: &Z3Dynamic, e: &Z3Dynamic) -> Z3Dynamic {
        cond.ite(t, e)
    }

    fn dynamic_get_sort(_ctx: &Self::Context, d: &Z3Dynamic) -> Z3Sort {
        Z3Ast::get_sort(d)
    }

    // ── Array operations ────────────────────────────────────────────

    fn array_new_const(
        _ctx: &Self::Context,
        name: &str,
        domain: &Z3Sort,
        range: &Z3Sort,
    ) -> Z3Array {
        Z3Array::new_const(name, domain, range)
    }

    fn array_const_array(_ctx: &Self::Context, domain: &Z3Sort, default: &Z3Dynamic) -> Z3Array {
        Z3Array::const_array(domain, default)
    }

    fn array_select(_ctx: &Self::Context, a: &Z3Array, index: &Z3Dynamic) -> Z3Dynamic {
        a.select(index)
    }

    fn array_store(
        _ctx: &Self::Context,
        a: &Z3Array,
        index: &Z3Dynamic,
        value: &Z3Dynamic,
    ) -> Z3Array {
        a.store(index, value)
    }

    fn array_eq(_ctx: &Self::Context, a: &Z3Array, b: Z3Array) -> Z3Bool {
        a.eq(b)
    }

    fn array_ite(_ctx: &Self::Context, cond: &Z3Bool, t: &Z3Array, e: &Z3Array) -> Z3Array {
        cond.ite(t, e)
    }

    fn array_get_sort(_ctx: &Self::Context, a: &Z3Array) -> Z3Sort {
        Z3Ast::get_sort(a)
    }

    // ── Quantifiers ─────────────────────────────────────────────────

    fn forall(_ctx: &Self::Context, bound: &[&Z3Dynamic], body: &Z3Bool) -> Z3Bool {
        let ast_refs: Vec<&dyn Z3Ast> = bound.iter().map(|d| *d as &dyn Z3Ast).collect();
        z3::ast::forall_const(&ast_refs, &[], body)
    }

    fn exists(_ctx: &Self::Context, bound: &[&Z3Dynamic], body: &Z3Bool) -> Z3Bool {
        let ast_refs: Vec<&dyn Z3Ast> = bound.iter().map(|d| *d as &dyn Z3Ast).collect();
        z3::ast::exists_const(&ast_refs, &[], body)
    }

    fn lambda(_ctx: &Self::Context, bound: &[&Z3Dynamic], body: &Z3Dynamic) -> Z3Array {
        let ast_refs: Vec<&dyn Z3Ast> = bound.iter().map(|d| *d as &dyn Z3Ast).collect();
        z3::ast::lambda_const(&ast_refs, body)
    }

    // ── Function declarations ───────────────────────────────────────

    fn func_decl_new(
        _ctx: &Self::Context,
        name: &str,
        domain: &[&Z3Sort],
        range: &Z3Sort,
    ) -> Z3FuncDecl {
        Z3FuncDecl::new(name, domain, range)
    }

    fn func_decl_apply(_ctx: &Self::Context, f: &Z3FuncDecl, args: &[&Z3Dynamic]) -> Z3Dynamic {
        let ast_refs: Vec<&dyn Z3Ast> = args.iter().map(|d| *d as &dyn Z3Ast).collect();
        f.apply(&ast_refs)
    }

    fn func_decl_name(_ctx: &Self::Context, f: &Z3FuncDecl) -> String {
        f.name()
    }

    // ── ADT construction ────────────────────────────────────────────

    fn datatype_builder_new(_ctx: &Self::Context, name: &str) -> Z3DatatypeBuilder {
        Z3DatatypeBuilder::new(name)
    }

    fn datatype_builder_variant(
        _ctx: &Self::Context,
        builder: Z3DatatypeBuilder,
        name: &str,
        fields: Vec<(&str, Z3DatatypeAccessor)>,
    ) -> Z3DatatypeBuilder {
        builder.variant(name, fields)
    }

    fn datatype_builder_finish(
        _ctx: &Self::Context,
        builder: Z3DatatypeBuilder,
    ) -> SolverDatatypeSort<Z3Sort, Z3FuncDecl> {
        let dt = builder.finish();
        let variants = dt
            .variants
            .into_iter()
            .map(|variant| DatatypeVariant {
                name: variant.constructor.name(),
                constructor: variant.constructor,
                tester: variant.tester,
                accessors: variant.accessors,
            })
            .collect();
        SolverDatatypeSort {
            sort: dt.sort,
            variants,
        }
    }

    fn datatype_accessor_sort(_ctx: &Self::Context, sort: Z3Sort) -> Z3DatatypeAccessor {
        Z3DatatypeAccessor::Sort(sort)
    }

    // ── Params ──────────────────────────────────────────────────────

    fn params_new() -> Z3Params {
        Z3Params::new()
    }

    fn params_set_bool(params: &mut Z3Params, key: &str, val: bool) {
        params.set_bool(key, val);
    }

    fn params_set_u32(params: &mut Z3Params, key: &str, val: u32) {
        params.set_u32(key, val);
    }

    fn params_set_symbol(params: &mut Z3Params, key: &str, val: &str) {
        params.set_symbol(key, val);
    }

    // ── Model operations ────────────────────────────────────────────

    fn model_eval_bool(model: &Z3Model, b: &Z3Bool) -> Option<bool> {
        model.eval(b, true).and_then(|v| v.as_bool())
    }

    fn model_eval_int(model: &Z3Model, i: &Z3Int) -> Option<i64> {
        model.eval(i, true).and_then(|v| v.as_i64())
    }

    fn model_eval_dynamic(model: &Z3Model, d: &Z3Dynamic) -> Option<String> {
        model.eval(d, true).map(|v| format!("{v}"))
    }
}

// ── CVC5 backend ────────────────────────────────────────────────────

thread_local! {
    static CVC5_TERM_MANAGER: RefCell<Option<Cvc5TermManager>> = const { RefCell::new(None) };
}

static CVC5_FRESH_COUNTER: AtomicU64 = AtomicU64::new(0);

fn cvc5_context() -> Cvc5Context {
    CVC5_TERM_MANAGER.with(|cell| {
        let tm = cell
            .borrow_mut()
            .get_or_insert_with(Cvc5TermManager::new)
            .clone();
        Cvc5Context { tm }
    })
}

fn cvc5_apply_kind(term: &Cvc5Term) -> Cvc5Kind {
    let sort = term.sort();
    if sort.is_dt_constructor() {
        Cvc5Kind::CVC5_KIND_APPLY_CONSTRUCTOR
    } else if sort.is_dt_selector() {
        Cvc5Kind::CVC5_KIND_APPLY_SELECTOR
    } else if sort.is_dt_tester() {
        Cvc5Kind::CVC5_KIND_APPLY_TESTER
    } else {
        Cvc5Kind::CVC5_KIND_APPLY_UF
    }
}

fn cvc5_apply_term(ctx: &Cvc5Context, func: &Cvc5Term, args: &[&Cvc5Term]) -> Cvc5Term {
    let mut children = Vec::with_capacity(args.len() + 1);
    children.push(func.clone());
    children.extend(args.iter().map(|arg| (*arg).clone()));
    ctx.tm.mk_term(cvc5_apply_kind(func), &children)
}

fn cvc5_bool_term(ctx: &Cvc5Context, kind: Cvc5Kind, args: &[Cvc5Term]) -> Cvc5Term {
    match (kind, args) {
        (Cvc5Kind::CVC5_KIND_AND, []) => return ctx.tm.mk_boolean(true),
        (Cvc5Kind::CVC5_KIND_OR, []) => return ctx.tm.mk_boolean(false),
        (Cvc5Kind::CVC5_KIND_AND | Cvc5Kind::CVC5_KIND_OR, [only]) => return only.clone(),
        _ => {}
    }
    ctx.tm.mk_term(kind, args)
}

fn cvc5_int_value(term: &Cvc5Term) -> Option<i64> {
    if term.is_int64_value() {
        Some(term.int64_value())
    } else if term.is_int32_value() {
        Some(i64::from(term.int32_value()))
    } else if term.is_integer_value() {
        term.integer_value().parse().ok()
    } else {
        None
    }
}

/// CVC5 backend implementing the `SolverBackend` trait.
///
/// This is currently feature-gated and not yet the active backend.
pub struct Cvc5Backend {
    solver: Rc<RefCell<Cvc5Solver>>,
    timeout_ms: Cell<u64>,
}

impl fmt::Debug for Cvc5Backend {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Cvc5Backend").finish_non_exhaustive()
    }
}

impl SolverBackend for Cvc5Backend {
    fn family() -> SolverFamily {
        SolverFamily::Cvc5
    }

    fn capabilities() -> SolverCapabilities {
        SolverCapabilities {
            arrays: true,
            datatypes: true,
            quantifiers: true,
            models: true,
            incremental: true,
            chc: false,
            native_sequences: true,
            native_bags: true,
            unsat_cores: true,
        }
    }

    type Context = Cvc5Context;
    fn context_new() -> Self::Context {
        cvc5_context()
    }

    type Bool = Cvc5Term;
    type Int = Cvc5Term;
    type Real = Cvc5Term;
    type Dynamic = Cvc5Term;
    type Array = Cvc5Term;
    type Sort = Cvc5Sort;
    type FuncDecl = Cvc5Term;
    type Model = Cvc5Model;
    type DatatypeSort = SolverDatatypeSort<Cvc5Sort, Cvc5Term>;
    type DatatypeAccessor = Cvc5Sort;
    type DatatypeBuilder = Cvc5DatatypeBuilder;
    type Params = Cvc5Params;

    fn solver_new(ctx: &Self::Context) -> Self {
        let mut solver = Cvc5Solver::new(&ctx.tm);
        solver.set_logic("ALL");
        solver.set_option("produce-models", "true");
        solver.set_option("incremental", "true");
        Self {
            solver: Rc::new(RefCell::new(solver)),
            timeout_ms: Cell::new(0),
        }
    }

    fn solver_assert(&self, c: &Self::Bool) {
        self.solver.borrow_mut().assert_formula(c.clone());
    }

    fn solver_check(&self) -> SatResult {
        self.solver_check_with_limits(SolverLimits::from_timeout_ms(self.timeout_ms.get()))
    }

    fn solver_check_with_limits(&self, limits: SolverLimits) -> SatResult {
        if let Some(timeout_ms) = limits.timeout_ms() {
            self.solver_set_timeout(timeout_ms);
        }
        let result = self.solver.borrow_mut().check_sat();
        if result.is_sat() {
            SatResult::Sat
        } else if result.is_unsat() {
            SatResult::Unsat
        } else {
            SatResult::Unknown(cvc5_unknown_to_string(result.unknown_explanation()))
        }
    }

    fn solver_push(&self) {
        self.solver.borrow_mut().push(1);
    }

    fn solver_pop(&self) {
        self.solver.borrow_mut().pop(1);
    }

    fn solver_set_timeout(&self, ms: u64) {
        self.timeout_ms.set(ms);
        self.solver
            .borrow_mut()
            .set_option("tlimit-per", &ms.to_string());
    }

    fn solver_get_model(&self) -> Option<Self::Model> {
        Some(Cvc5Model {
            solver: self.solver.clone(),
        })
    }

    fn bool_const(ctx: &Self::Context, val: bool) -> Self::Bool {
        ctx.tm.mk_boolean(val)
    }

    fn bool_var(ctx: &Self::Context, name: &str) -> Self::Bool {
        ctx.tm.mk_const(ctx.tm.boolean_sort(), name)
    }

    fn bool_and(ctx: &Self::Context, args: &[&Self::Bool]) -> Self::Bool {
        cvc5_bool_term(
            ctx,
            Cvc5Kind::CVC5_KIND_AND,
            &args.iter().map(|a| (*a).clone()).collect::<Vec<_>>(),
        )
    }

    fn bool_or(ctx: &Self::Context, args: &[&Self::Bool]) -> Self::Bool {
        cvc5_bool_term(
            ctx,
            Cvc5Kind::CVC5_KIND_OR,
            &args.iter().map(|a| (*a).clone()).collect::<Vec<_>>(),
        )
    }

    fn bool_not(ctx: &Self::Context, b: &Self::Bool) -> Self::Bool {
        ctx.tm
            .mk_term(Cvc5Kind::CVC5_KIND_NOT, std::slice::from_ref(b))
    }

    fn bool_implies(ctx: &Self::Context, a: &Self::Bool, b: &Self::Bool) -> Self::Bool {
        ctx.tm
            .mk_term(Cvc5Kind::CVC5_KIND_IMPLIES, &[a.clone(), b.clone()])
    }

    fn bool_xor(ctx: &Self::Context, a: &Self::Bool, b: &Self::Bool) -> Self::Bool {
        ctx.tm
            .mk_term(Cvc5Kind::CVC5_KIND_XOR, &[a.clone(), b.clone()])
    }

    fn bool_eq(ctx: &Self::Context, a: &Self::Bool, b: &Self::Bool) -> Self::Bool {
        ctx.tm
            .mk_term(Cvc5Kind::CVC5_KIND_EQUAL, &[a.clone(), b.clone()])
    }

    fn bool_ite(
        ctx: &Self::Context,
        cond: &Self::Bool,
        t: &Self::Bool,
        e: &Self::Bool,
    ) -> Self::Bool {
        ctx.tm.mk_term(
            Cvc5Kind::CVC5_KIND_ITE,
            &[cond.clone(), t.clone(), e.clone()],
        )
    }

    fn int_lit(ctx: &Self::Context, n: i64) -> Self::Int {
        ctx.tm.mk_integer(n)
    }

    fn int_var(ctx: &Self::Context, name: &str) -> Self::Int {
        ctx.tm.mk_const(ctx.tm.integer_sort(), name)
    }

    fn int_add(ctx: &Self::Context, args: &[&Self::Int]) -> Self::Int {
        ctx.tm.mk_term(
            Cvc5Kind::CVC5_KIND_ADD,
            &args.iter().map(|a| (*a).clone()).collect::<Vec<_>>(),
        )
    }

    fn int_sub(ctx: &Self::Context, args: &[&Self::Int]) -> Self::Int {
        ctx.tm.mk_term(
            Cvc5Kind::CVC5_KIND_SUB,
            &args.iter().map(|a| (*a).clone()).collect::<Vec<_>>(),
        )
    }

    fn int_mul(ctx: &Self::Context, args: &[&Self::Int]) -> Self::Int {
        ctx.tm.mk_term(
            Cvc5Kind::CVC5_KIND_MULT,
            &args.iter().map(|a| (*a).clone()).collect::<Vec<_>>(),
        )
    }

    fn int_div(ctx: &Self::Context, a: &Self::Int, b: &Self::Int) -> Self::Int {
        ctx.tm
            .mk_term(Cvc5Kind::CVC5_KIND_INTS_DIVISION, &[a.clone(), b.clone()])
    }

    fn int_modulo(ctx: &Self::Context, a: &Self::Int, b: &Self::Int) -> Self::Int {
        ctx.tm
            .mk_term(Cvc5Kind::CVC5_KIND_INTS_MODULUS, &[a.clone(), b.clone()])
    }

    fn int_neg(ctx: &Self::Context, a: &Self::Int) -> Self::Int {
        ctx.tm
            .mk_term(Cvc5Kind::CVC5_KIND_NEG, std::slice::from_ref(a))
    }

    fn int_eq(ctx: &Self::Context, a: &Self::Int, b: &Self::Int) -> Self::Bool {
        ctx.tm
            .mk_term(Cvc5Kind::CVC5_KIND_EQUAL, &[a.clone(), b.clone()])
    }

    fn int_lt(ctx: &Self::Context, a: &Self::Int, b: &Self::Int) -> Self::Bool {
        ctx.tm
            .mk_term(Cvc5Kind::CVC5_KIND_LT, &[a.clone(), b.clone()])
    }

    fn int_le(ctx: &Self::Context, a: &Self::Int, b: &Self::Int) -> Self::Bool {
        ctx.tm
            .mk_term(Cvc5Kind::CVC5_KIND_LEQ, &[a.clone(), b.clone()])
    }

    fn int_gt(ctx: &Self::Context, a: &Self::Int, b: &Self::Int) -> Self::Bool {
        ctx.tm
            .mk_term(Cvc5Kind::CVC5_KIND_GT, &[a.clone(), b.clone()])
    }

    fn int_ge(ctx: &Self::Context, a: &Self::Int, b: &Self::Int) -> Self::Bool {
        ctx.tm
            .mk_term(Cvc5Kind::CVC5_KIND_GEQ, &[a.clone(), b.clone()])
    }

    fn int_ite(ctx: &Self::Context, cond: &Self::Bool, t: &Self::Int, e: &Self::Int) -> Self::Int {
        ctx.tm.mk_term(
            Cvc5Kind::CVC5_KIND_ITE,
            &[cond.clone(), t.clone(), e.clone()],
        )
    }

    fn real_val(ctx: &Self::Context, num: i64, den: i64) -> Self::Real {
        ctx.tm.mk_real_from_rational(num, den)
    }

    fn real_var(ctx: &Self::Context, name: &str) -> Self::Real {
        ctx.tm.mk_const(ctx.tm.real_sort(), name)
    }

    fn real_add(ctx: &Self::Context, args: &[&Self::Real]) -> Self::Real {
        ctx.tm.mk_term(
            Cvc5Kind::CVC5_KIND_ADD,
            &args.iter().map(|a| (*a).clone()).collect::<Vec<_>>(),
        )
    }

    fn real_sub(ctx: &Self::Context, args: &[&Self::Real]) -> Self::Real {
        ctx.tm.mk_term(
            Cvc5Kind::CVC5_KIND_SUB,
            &args.iter().map(|a| (*a).clone()).collect::<Vec<_>>(),
        )
    }

    fn real_mul(ctx: &Self::Context, args: &[&Self::Real]) -> Self::Real {
        ctx.tm.mk_term(
            Cvc5Kind::CVC5_KIND_MULT,
            &args.iter().map(|a| (*a).clone()).collect::<Vec<_>>(),
        )
    }

    fn real_div(ctx: &Self::Context, a: &Self::Real, b: &Self::Real) -> Self::Real {
        ctx.tm
            .mk_term(Cvc5Kind::CVC5_KIND_DIVISION, &[a.clone(), b.clone()])
    }

    fn real_eq(ctx: &Self::Context, a: &Self::Real, b: &Self::Real) -> Self::Bool {
        ctx.tm
            .mk_term(Cvc5Kind::CVC5_KIND_EQUAL, &[a.clone(), b.clone()])
    }

    fn real_lt(ctx: &Self::Context, a: &Self::Real, b: &Self::Real) -> Self::Bool {
        ctx.tm
            .mk_term(Cvc5Kind::CVC5_KIND_LT, &[a.clone(), b.clone()])
    }

    fn real_le(ctx: &Self::Context, a: &Self::Real, b: &Self::Real) -> Self::Bool {
        ctx.tm
            .mk_term(Cvc5Kind::CVC5_KIND_LEQ, &[a.clone(), b.clone()])
    }

    fn real_gt(ctx: &Self::Context, a: &Self::Real, b: &Self::Real) -> Self::Bool {
        ctx.tm
            .mk_term(Cvc5Kind::CVC5_KIND_GT, &[a.clone(), b.clone()])
    }

    fn real_ge(ctx: &Self::Context, a: &Self::Real, b: &Self::Real) -> Self::Bool {
        ctx.tm
            .mk_term(Cvc5Kind::CVC5_KIND_GEQ, &[a.clone(), b.clone()])
    }

    fn real_ite(
        ctx: &Self::Context,
        cond: &Self::Bool,
        t: &Self::Real,
        e: &Self::Real,
    ) -> Self::Real {
        ctx.tm.mk_term(
            Cvc5Kind::CVC5_KIND_ITE,
            &[cond.clone(), t.clone(), e.clone()],
        )
    }

    fn int_sort(ctx: &Self::Context) -> Self::Sort {
        ctx.tm.integer_sort()
    }

    fn bool_sort(ctx: &Self::Context) -> Self::Sort {
        ctx.tm.boolean_sort()
    }

    fn real_sort(ctx: &Self::Context) -> Self::Sort {
        ctx.tm.real_sort()
    }

    fn array_sort(ctx: &Self::Context, domain: &Self::Sort, range: &Self::Sort) -> Self::Sort {
        ctx.tm.mk_array_sort(domain.clone(), range.clone())
    }

    fn sort_array_domain(_ctx: &Self::Context, s: &Self::Sort) -> Option<Self::Sort> {
        s.is_array().then(|| s.array_index_sort())
    }

    fn sort_array_range(_ctx: &Self::Context, s: &Self::Sort) -> Option<Self::Sort> {
        s.is_array().then(|| s.array_element_sort())
    }

    fn sort_to_string(_ctx: &Self::Context, s: &Self::Sort) -> String {
        s.to_string()
    }

    fn dynamic_fresh(ctx: &Self::Context, prefix: &str, sort: &Self::Sort) -> Self::Dynamic {
        let id = CVC5_FRESH_COUNTER.fetch_add(1, Ordering::Relaxed);
        ctx.tm.mk_const(sort.clone(), &format!("{prefix}!{id}"))
    }

    fn dynamic_const(ctx: &Self::Context, name: &str, sort: &Self::Sort) -> Self::Dynamic {
        ctx.tm.mk_const(sort.clone(), name)
    }

    fn dynamic_from_bool(_ctx: &Self::Context, b: &Self::Bool) -> Self::Dynamic {
        b.clone()
    }

    fn dynamic_from_int(_ctx: &Self::Context, i: &Self::Int) -> Self::Dynamic {
        i.clone()
    }

    fn dynamic_from_real(_ctx: &Self::Context, r: &Self::Real) -> Self::Dynamic {
        r.clone()
    }

    fn dynamic_from_array(_ctx: &Self::Context, a: &Self::Array) -> Self::Dynamic {
        a.clone()
    }

    fn dynamic_as_bool(_ctx: &Self::Context, d: &Self::Dynamic) -> Option<Self::Bool> {
        d.sort().is_boolean().then(|| d.clone())
    }

    fn dynamic_as_int(_ctx: &Self::Context, d: &Self::Dynamic) -> Option<Self::Int> {
        d.sort().is_integer().then(|| d.clone())
    }

    fn dynamic_as_real(_ctx: &Self::Context, d: &Self::Dynamic) -> Option<Self::Real> {
        d.sort().is_real().then(|| d.clone())
    }

    fn dynamic_as_array(_ctx: &Self::Context, d: &Self::Dynamic) -> Option<Self::Array> {
        d.sort().is_array().then(|| d.clone())
    }

    fn dynamic_eq(ctx: &Self::Context, a: &Self::Dynamic, b: &Self::Dynamic) -> Self::Bool {
        ctx.tm
            .mk_term(Cvc5Kind::CVC5_KIND_EQUAL, &[a.clone(), b.clone()])
    }

    fn dynamic_ite(
        ctx: &Self::Context,
        cond: &Self::Bool,
        t: &Self::Dynamic,
        e: &Self::Dynamic,
    ) -> Self::Dynamic {
        ctx.tm.mk_term(
            Cvc5Kind::CVC5_KIND_ITE,
            &[cond.clone(), t.clone(), e.clone()],
        )
    }

    fn dynamic_get_sort(_ctx: &Self::Context, d: &Self::Dynamic) -> Self::Sort {
        d.sort()
    }

    fn array_new_const(
        ctx: &Self::Context,
        name: &str,
        domain: &Self::Sort,
        range: &Self::Sort,
    ) -> Self::Array {
        let sort = ctx.tm.mk_array_sort(domain.clone(), range.clone());
        ctx.tm.mk_const(sort, name)
    }

    fn array_const_array(
        ctx: &Self::Context,
        domain: &Self::Sort,
        default: &Self::Dynamic,
    ) -> Self::Array {
        let range = default.sort();
        let array_sort = ctx.tm.mk_array_sort(domain.clone(), range);
        ctx.tm.mk_const_array(array_sort, default.clone())
    }

    fn array_select(ctx: &Self::Context, a: &Self::Array, index: &Self::Dynamic) -> Self::Dynamic {
        ctx.tm
            .mk_term(Cvc5Kind::CVC5_KIND_SELECT, &[a.clone(), index.clone()])
    }

    fn array_store(
        ctx: &Self::Context,
        a: &Self::Array,
        index: &Self::Dynamic,
        value: &Self::Dynamic,
    ) -> Self::Array {
        ctx.tm.mk_term(
            Cvc5Kind::CVC5_KIND_STORE,
            &[a.clone(), index.clone(), value.clone()],
        )
    }

    fn array_eq(ctx: &Self::Context, a: &Self::Array, b: Self::Array) -> Self::Bool {
        ctx.tm.mk_term(Cvc5Kind::CVC5_KIND_EQUAL, &[a.clone(), b])
    }

    fn array_ite(
        ctx: &Self::Context,
        cond: &Self::Bool,
        t: &Self::Array,
        e: &Self::Array,
    ) -> Self::Array {
        ctx.tm.mk_term(
            Cvc5Kind::CVC5_KIND_ITE,
            &[cond.clone(), t.clone(), e.clone()],
        )
    }

    fn array_get_sort(_ctx: &Self::Context, a: &Self::Array) -> Self::Sort {
        a.sort()
    }

    fn forall(ctx: &Self::Context, bound: &[&Self::Dynamic], body: &Self::Bool) -> Self::Bool {
        let vars = ctx.tm.mk_term(
            Cvc5Kind::CVC5_KIND_VARIABLE_LIST,
            &bound.iter().map(|b| (*b).clone()).collect::<Vec<_>>(),
        );
        ctx.tm
            .mk_term(Cvc5Kind::CVC5_KIND_FORALL, &[vars, body.clone()])
    }

    fn exists(ctx: &Self::Context, bound: &[&Self::Dynamic], body: &Self::Bool) -> Self::Bool {
        let vars = ctx.tm.mk_term(
            Cvc5Kind::CVC5_KIND_VARIABLE_LIST,
            &bound.iter().map(|b| (*b).clone()).collect::<Vec<_>>(),
        );
        ctx.tm
            .mk_term(Cvc5Kind::CVC5_KIND_EXISTS, &[vars, body.clone()])
    }

    fn lambda(ctx: &Self::Context, bound: &[&Self::Dynamic], body: &Self::Dynamic) -> Self::Array {
        let vars = ctx.tm.mk_term(
            Cvc5Kind::CVC5_KIND_VARIABLE_LIST,
            &bound.iter().map(|b| (*b).clone()).collect::<Vec<_>>(),
        );
        ctx.tm
            .mk_term(Cvc5Kind::CVC5_KIND_LAMBDA, &[vars, body.clone()])
    }

    fn func_decl_new(
        ctx: &Self::Context,
        name: &str,
        domain: &[&Self::Sort],
        range: &Self::Sort,
    ) -> Self::FuncDecl {
        let sort = ctx.tm.mk_fun_sort(
            &domain.iter().map(|s| (*s).clone()).collect::<Vec<_>>(),
            range.clone(),
        );
        ctx.tm.mk_const(sort, name)
    }

    fn func_decl_apply(
        ctx: &Self::Context,
        f: &Self::FuncDecl,
        args: &[&Self::Dynamic],
    ) -> Self::Dynamic {
        cvc5_apply_term(ctx, f, args)
    }

    fn func_decl_name(_ctx: &Self::Context, f: &Self::FuncDecl) -> String {
        if f.has_symbol() {
            f.symbol().to_owned()
        } else {
            format!("{f}")
        }
    }

    fn datatype_builder_new(ctx: &Self::Context, name: &str) -> Self::DatatypeBuilder {
        Cvc5DatatypeBuilder {
            tm: ctx.tm.clone(),
            name: name.to_owned(),
            variants: Vec::new(),
        }
    }

    fn datatype_builder_variant(
        _ctx: &Self::Context,
        mut builder: Self::DatatypeBuilder,
        name: &str,
        fields: Vec<(&str, Self::DatatypeAccessor)>,
    ) -> Self::DatatypeBuilder {
        builder.variants.push((
            name.to_owned(),
            fields
                .into_iter()
                .map(|(field_name, sort)| (field_name.to_owned(), sort))
                .collect(),
        ));
        builder
    }

    fn datatype_builder_finish(
        _ctx: &Self::Context,
        builder: Self::DatatypeBuilder,
    ) -> Self::DatatypeSort {
        let mut decl = builder.tm.mk_dt_decl(&builder.name, false);
        for (ctor_name, fields) in &builder.variants {
            let mut ctor = builder.tm.mk_dt_cons_decl(ctor_name);
            for (field_name, sort) in fields {
                ctor.add_selector(field_name, sort.clone());
            }
            decl.add_constructor(&ctor);
        }
        let sort = builder.tm.mk_dt_sort(&decl);
        let dt = sort.datatype();
        let mut variants = Vec::with_capacity(dt.num_constructors());
        for idx in 0..dt.num_constructors() {
            let ctor = dt.constructor(idx);
            let accessors = (0..ctor.num_selectors())
                .map(|i| ctor.selector(i).term())
                .collect();
            variants.push(DatatypeVariant {
                name: ctor.name().to_owned(),
                constructor: ctor.term(),
                tester: ctor.tester_term(),
                accessors,
            });
        }
        SolverDatatypeSort { sort, variants }
    }

    fn datatype_accessor_sort(_ctx: &Self::Context, sort: Self::Sort) -> Self::DatatypeAccessor {
        sort
    }

    fn params_new() -> Self::Params {
        Cvc5Params::default()
    }

    fn params_set_bool(params: &mut Self::Params, key: &str, val: bool) {
        params.values.insert(key.to_owned(), val.to_string());
    }

    fn params_set_u32(params: &mut Self::Params, key: &str, val: u32) {
        params.values.insert(key.to_owned(), val.to_string());
    }

    fn params_set_symbol(params: &mut Self::Params, key: &str, val: &str) {
        params.values.insert(key.to_owned(), val.to_owned());
    }

    fn model_eval_bool(model: &Self::Model, b: &Self::Bool) -> Option<bool> {
        let value = model.solver.as_ref().borrow().get_value(b.clone());
        value.is_boolean_value().then(|| value.boolean_value())
    }

    fn model_eval_int(model: &Self::Model, i: &Self::Int) -> Option<i64> {
        let value = model.solver.as_ref().borrow().get_value(i.clone());
        cvc5_int_value(&value)
    }

    fn model_eval_dynamic(model: &Self::Model, d: &Self::Dynamic) -> Option<String> {
        Some(format!(
            "{}",
            model.solver.as_ref().borrow().get_value(d.clone())
        ))
    }
}

// ── Runtime backend wrapper ────────────────────────────────────────

#[derive(Clone, Debug)]
pub enum RuntimeContext {
    Z3(()),
    Cvc5(Cvc5Context),
}

#[derive(Clone, Debug)]
pub enum RuntimeBool {
    Z3(Z3Bool),
    Cvc5(Cvc5Term),
}

#[derive(Clone, Debug)]
pub enum RuntimeInt {
    Z3(Z3Int),
    Cvc5(Cvc5Term),
}

#[derive(Clone, Debug)]
pub enum RuntimeReal {
    Z3(Z3Real),
    Cvc5(Cvc5Term),
}

#[derive(Clone, Debug)]
pub enum RuntimeDynamic {
    Z3(Z3Dynamic),
    Cvc5(Cvc5Term),
}

#[derive(Clone, Debug)]
pub enum RuntimeArray {
    Z3(Z3Array),
    Cvc5(Cvc5Term),
}

#[derive(Clone, Debug)]
pub enum RuntimeSort {
    Z3(Z3Sort),
    Cvc5(Cvc5Sort),
}

#[derive(Debug)]
pub enum RuntimeFuncDecl {
    Z3(Z3FuncDecl),
    Cvc5(Cvc5Term),
}

#[derive(Debug)]
pub enum RuntimeModel {
    Z3(Z3Model),
    Cvc5(Cvc5Model),
}

#[derive(Debug)]
pub struct RuntimeDatatypeSort {
    pub sort: RuntimeSort,
    pub variants: Vec<DatatypeVariant<RuntimeFuncDecl>>,
}

#[derive(Debug)]
pub enum RuntimeDatatypeAccessor {
    Z3(Z3DatatypeAccessor),
    Cvc5(Cvc5Sort),
}

#[derive(Debug)]
pub enum RuntimeDatatypeBuilder {
    Z3(Z3DatatypeBuilder),
    Cvc5(Cvc5DatatypeBuilder),
}

#[derive(Debug)]
pub enum RuntimeParams {
    Z3(Z3Params),
    Cvc5(Cvc5Params),
}

#[derive(Debug)]
pub enum RuntimeBackend {
    Z3(Z3Backend),
    Cvc5(Cvc5Backend),
}

pub trait RuntimeModelEval: Sized {
    fn runtime_eval(model: &RuntimeModel, ast: &Self, model_completion: bool) -> Option<Self>;
}

impl RuntimeArray {
    pub fn store(&self, index: &RuntimeDynamic, value: &RuntimeDynamic) -> Self {
        let ctx = match self {
            RuntimeArray::Z3(_) => RuntimeContext::Z3(()),
            RuntimeArray::Cvc5(_) => RuntimeContext::Cvc5(Cvc5Backend::context_new()),
        };
        RuntimeBackend::array_store(&ctx, self, index, value)
    }

    pub fn select(&self, index: &RuntimeDynamic) -> RuntimeDynamic {
        let ctx = match self {
            RuntimeArray::Z3(_) => RuntimeContext::Z3(()),
            RuntimeArray::Cvc5(_) => RuntimeContext::Cvc5(Cvc5Backend::context_new()),
        };
        RuntimeBackend::array_select(&ctx, self, index)
    }
}

impl RuntimeDynamic {
    pub fn as_bool(&self) -> Option<RuntimeBool> {
        let ctx = match self {
            RuntimeDynamic::Z3(_) => RuntimeContext::Z3(()),
            RuntimeDynamic::Cvc5(_) => RuntimeContext::Cvc5(Cvc5Backend::context_new()),
        };
        RuntimeBackend::dynamic_as_bool(&ctx, self)
    }

    pub fn as_int(&self) -> Option<RuntimeInt> {
        let ctx = match self {
            RuntimeDynamic::Z3(_) => RuntimeContext::Z3(()),
            RuntimeDynamic::Cvc5(_) => RuntimeContext::Cvc5(Cvc5Backend::context_new()),
        };
        RuntimeBackend::dynamic_as_int(&ctx, self)
    }

    pub fn as_real(&self) -> Option<RuntimeReal> {
        let ctx = match self {
            RuntimeDynamic::Z3(_) => RuntimeContext::Z3(()),
            RuntimeDynamic::Cvc5(_) => RuntimeContext::Cvc5(Cvc5Backend::context_new()),
        };
        RuntimeBackend::dynamic_as_real(&ctx, self)
    }
}

impl RuntimeBool {
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            RuntimeBool::Z3(b) => b.as_bool(),
            RuntimeBool::Cvc5(b) => b.is_boolean_value().then(|| b.boolean_value()),
        }
    }
}

impl RuntimeInt {
    pub fn as_i64(&self) -> Option<i64> {
        match self {
            RuntimeInt::Z3(i) => i.as_i64(),
            RuntimeInt::Cvc5(i) => cvc5_int_value(i),
        }
    }
}

impl RuntimeDatatypeSort {
    pub fn sort(&self) -> RuntimeSort {
        self.sort.clone()
    }
}

impl RuntimeModel {
    pub fn eval<T: RuntimeModelEval>(&self, ast: &T, _model_completion: bool) -> Option<T> {
        T::runtime_eval(self, ast, _model_completion)
    }
}

#[allow(unreachable_patterns)]
impl RuntimeModelEval for RuntimeBool {
    fn runtime_eval(model: &RuntimeModel, ast: &Self, _model_completion: bool) -> Option<Self> {
        match (model, ast) {
            (RuntimeModel::Z3(model), RuntimeBool::Z3(ast)) => {
                model.eval(ast, true).map(RuntimeBool::Z3)
            }
            (RuntimeModel::Cvc5(model), RuntimeBool::Cvc5(ast)) => Some(RuntimeBool::Cvc5(
                model.solver.as_ref().borrow().get_value(ast.clone()),
            )),
            _ => None,
        }
    }
}

#[allow(unreachable_patterns)]
impl RuntimeModelEval for RuntimeInt {
    fn runtime_eval(model: &RuntimeModel, ast: &Self, _model_completion: bool) -> Option<Self> {
        match (model, ast) {
            (RuntimeModel::Z3(model), RuntimeInt::Z3(ast)) => {
                model.eval(ast, true).map(RuntimeInt::Z3)
            }
            (RuntimeModel::Cvc5(model), RuntimeInt::Cvc5(ast)) => Some(RuntimeInt::Cvc5(
                model.solver.as_ref().borrow().get_value(ast.clone()),
            )),
            _ => None,
        }
    }
}

#[allow(unreachable_patterns)]
impl RuntimeModelEval for RuntimeReal {
    fn runtime_eval(model: &RuntimeModel, ast: &Self, _model_completion: bool) -> Option<Self> {
        match (model, ast) {
            (RuntimeModel::Z3(model), RuntimeReal::Z3(ast)) => {
                model.eval(ast, true).map(RuntimeReal::Z3)
            }
            (RuntimeModel::Cvc5(model), RuntimeReal::Cvc5(ast)) => Some(RuntimeReal::Cvc5(
                model.solver.as_ref().borrow().get_value(ast.clone()),
            )),
            _ => None,
        }
    }
}

#[allow(unreachable_patterns)]
impl RuntimeModelEval for RuntimeDynamic {
    fn runtime_eval(model: &RuntimeModel, ast: &Self, _model_completion: bool) -> Option<Self> {
        match (model, ast) {
            (RuntimeModel::Z3(model), RuntimeDynamic::Z3(ast)) => {
                model.eval(ast, true).map(RuntimeDynamic::Z3)
            }
            (RuntimeModel::Cvc5(model), RuntimeDynamic::Cvc5(ast)) => Some(RuntimeDynamic::Cvc5(
                model.solver.as_ref().borrow().get_value(ast.clone()),
            )),
            _ => None,
        }
    }
}

#[allow(unreachable_patterns)]
impl RuntimeModelEval for RuntimeArray {
    fn runtime_eval(model: &RuntimeModel, ast: &Self, _model_completion: bool) -> Option<Self> {
        match (model, ast) {
            (RuntimeModel::Z3(model), RuntimeArray::Z3(ast)) => {
                model.eval(ast, true).map(RuntimeArray::Z3)
            }
            (RuntimeModel::Cvc5(model), RuntimeArray::Cvc5(ast)) => Some(RuntimeArray::Cvc5(
                model.solver.as_ref().borrow().get_value(ast.clone()),
            )),
            _ => None,
        }
    }
}

impl fmt::Display for RuntimeBool {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimeBool::Z3(v) => write!(f, "{v}"),
            RuntimeBool::Cvc5(v) => write!(f, "{v}"),
        }
    }
}

impl fmt::Display for RuntimeInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimeInt::Z3(v) => write!(f, "{v}"),
            RuntimeInt::Cvc5(v) => write!(f, "{v}"),
        }
    }
}

impl fmt::Display for RuntimeReal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimeReal::Z3(v) => write!(f, "{v}"),
            RuntimeReal::Cvc5(v) => write!(f, "{v}"),
        }
    }
}

impl fmt::Display for RuntimeDynamic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimeDynamic::Z3(v) => write!(f, "{v}"),
            RuntimeDynamic::Cvc5(v) => write!(f, "{v}"),
        }
    }
}

impl fmt::Display for RuntimeArray {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimeArray::Z3(v) => write!(f, "{v}"),
            RuntimeArray::Cvc5(v) => write!(f, "{v}"),
        }
    }
}

fn panic_mixed_solver_terms(expected: SolverFamily) -> ! {
    panic!(
        "mixed solver terms encountered while using {:?} backend",
        expected
    )
}

#[allow(unreachable_patterns)]
impl SolverBackend for RuntimeBackend {
    fn family() -> SolverFamily {
        active_solver_family()
    }

    fn capabilities() -> SolverCapabilities {
        match active_solver_family() {
            SolverFamily::Z3 => Z3Backend::capabilities(),
            SolverFamily::Cvc5 => Cvc5Backend::capabilities(),
        }
    }

    type Context = RuntimeContext;
    type Bool = RuntimeBool;
    type Int = RuntimeInt;
    type Real = RuntimeReal;
    type Dynamic = RuntimeDynamic;
    type Array = RuntimeArray;
    type Sort = RuntimeSort;
    type FuncDecl = RuntimeFuncDecl;
    type Model = RuntimeModel;
    type DatatypeSort = RuntimeDatatypeSort;
    type DatatypeAccessor = RuntimeDatatypeAccessor;
    type DatatypeBuilder = RuntimeDatatypeBuilder;
    type Params = RuntimeParams;

    fn context_new() -> Self::Context {
        match active_solver_family() {
            SolverFamily::Z3 => {
                Z3Backend::context_new();
                RuntimeContext::Z3(())
            }
            SolverFamily::Cvc5 => RuntimeContext::Cvc5(Cvc5Backend::context_new()),
        }
    }

    fn solver_new(ctx: &Self::Context) -> Self {
        match ctx {
            RuntimeContext::Z3(ctx) => RuntimeBackend::Z3(Z3Backend::solver_new(ctx)),
            RuntimeContext::Cvc5(ctx) => RuntimeBackend::Cvc5(Cvc5Backend::solver_new(ctx)),
        }
    }

    fn solver_assert(&self, c: &Self::Bool) {
        match (self, c) {
            (RuntimeBackend::Z3(solver), RuntimeBool::Z3(c)) => solver.solver_assert(c),
            (RuntimeBackend::Cvc5(solver), RuntimeBool::Cvc5(c)) => solver.solver_assert(c),
            (RuntimeBackend::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeBackend::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn solver_check(&self) -> SatResult {
        match self {
            RuntimeBackend::Z3(solver) => solver.solver_check(),
            RuntimeBackend::Cvc5(solver) => solver.solver_check(),
        }
    }

    fn solver_check_with_limits(&self, limits: SolverLimits) -> SatResult {
        match self {
            RuntimeBackend::Z3(solver) => solver.solver_check_with_limits(limits),
            RuntimeBackend::Cvc5(solver) => solver.solver_check_with_limits(limits),
        }
    }

    fn solver_push(&self) {
        match self {
            RuntimeBackend::Z3(solver) => solver.solver_push(),
            RuntimeBackend::Cvc5(solver) => solver.solver_push(),
        }
    }

    fn solver_pop(&self) {
        match self {
            RuntimeBackend::Z3(solver) => solver.solver_pop(),
            RuntimeBackend::Cvc5(solver) => solver.solver_pop(),
        }
    }

    fn solver_set_timeout(&self, ms: u64) {
        match self {
            RuntimeBackend::Z3(solver) => solver.solver_set_timeout(ms),
            RuntimeBackend::Cvc5(solver) => solver.solver_set_timeout(ms),
        }
    }

    fn solver_get_model(&self) -> Option<Self::Model> {
        match self {
            RuntimeBackend::Z3(solver) => solver.solver_get_model().map(RuntimeModel::Z3),
            RuntimeBackend::Cvc5(solver) => solver.solver_get_model().map(RuntimeModel::Cvc5),
        }
    }

    fn bool_const(ctx: &Self::Context, val: bool) -> Self::Bool {
        match ctx {
            RuntimeContext::Z3(ctx) => RuntimeBool::Z3(Z3Backend::bool_const(ctx, val)),
            RuntimeContext::Cvc5(ctx) => RuntimeBool::Cvc5(Cvc5Backend::bool_const(ctx, val)),
        }
    }

    fn bool_var(ctx: &Self::Context, name: &str) -> Self::Bool {
        match ctx {
            RuntimeContext::Z3(ctx) => RuntimeBool::Z3(Z3Backend::bool_var(ctx, name)),
            RuntimeContext::Cvc5(ctx) => RuntimeBool::Cvc5(Cvc5Backend::bool_var(ctx, name)),
        }
    }

    fn bool_and(ctx: &Self::Context, args: &[&Self::Bool]) -> Self::Bool {
        match ctx {
            RuntimeContext::Z3(ctx) => RuntimeBool::Z3(Z3Backend::bool_and(
                ctx,
                &args
                    .iter()
                    .map(|arg| match arg {
                        RuntimeBool::Z3(arg) => arg,
                        _ => panic_mixed_solver_terms(SolverFamily::Z3),
                    })
                    .collect::<Vec<_>>(),
            )),
            RuntimeContext::Cvc5(ctx) => RuntimeBool::Cvc5(Cvc5Backend::bool_and(
                ctx,
                &args
                    .iter()
                    .map(|arg| match arg {
                        RuntimeBool::Cvc5(arg) => arg,
                        _ => panic_mixed_solver_terms(SolverFamily::Cvc5),
                    })
                    .collect::<Vec<_>>(),
            )),
        }
    }

    fn bool_or(ctx: &Self::Context, args: &[&Self::Bool]) -> Self::Bool {
        match ctx {
            RuntimeContext::Z3(ctx) => RuntimeBool::Z3(Z3Backend::bool_or(
                ctx,
                &args
                    .iter()
                    .map(|arg| match arg {
                        RuntimeBool::Z3(arg) => arg,
                        _ => panic_mixed_solver_terms(SolverFamily::Z3),
                    })
                    .collect::<Vec<_>>(),
            )),
            RuntimeContext::Cvc5(ctx) => RuntimeBool::Cvc5(Cvc5Backend::bool_or(
                ctx,
                &args
                    .iter()
                    .map(|arg| match arg {
                        RuntimeBool::Cvc5(arg) => arg,
                        _ => panic_mixed_solver_terms(SolverFamily::Cvc5),
                    })
                    .collect::<Vec<_>>(),
            )),
        }
    }

    fn bool_not(ctx: &Self::Context, b: &Self::Bool) -> Self::Bool {
        match (ctx, b) {
            (RuntimeContext::Z3(ctx), RuntimeBool::Z3(b)) => {
                RuntimeBool::Z3(Z3Backend::bool_not(ctx, b))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeBool::Cvc5(b)) => {
                RuntimeBool::Cvc5(Cvc5Backend::bool_not(ctx, b))
            }
            (RuntimeContext::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn bool_implies(ctx: &Self::Context, a: &Self::Bool, b: &Self::Bool) -> Self::Bool {
        match (ctx, a, b) {
            (RuntimeContext::Z3(ctx), RuntimeBool::Z3(a), RuntimeBool::Z3(b)) => {
                RuntimeBool::Z3(Z3Backend::bool_implies(ctx, a, b))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeBool::Cvc5(a), RuntimeBool::Cvc5(b)) => {
                RuntimeBool::Cvc5(Cvc5Backend::bool_implies(ctx, a, b))
            }
            (RuntimeContext::Z3(_), _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn bool_xor(ctx: &Self::Context, a: &Self::Bool, b: &Self::Bool) -> Self::Bool {
        match (ctx, a, b) {
            (RuntimeContext::Z3(ctx), RuntimeBool::Z3(a), RuntimeBool::Z3(b)) => {
                RuntimeBool::Z3(Z3Backend::bool_xor(ctx, a, b))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeBool::Cvc5(a), RuntimeBool::Cvc5(b)) => {
                RuntimeBool::Cvc5(Cvc5Backend::bool_xor(ctx, a, b))
            }
            (RuntimeContext::Z3(_), _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn bool_eq(ctx: &Self::Context, a: &Self::Bool, b: &Self::Bool) -> Self::Bool {
        match (ctx, a, b) {
            (RuntimeContext::Z3(ctx), RuntimeBool::Z3(a), RuntimeBool::Z3(b)) => {
                RuntimeBool::Z3(Z3Backend::bool_eq(ctx, a, b))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeBool::Cvc5(a), RuntimeBool::Cvc5(b)) => {
                RuntimeBool::Cvc5(Cvc5Backend::bool_eq(ctx, a, b))
            }
            (RuntimeContext::Z3(_), _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn bool_ite(
        ctx: &Self::Context,
        cond: &Self::Bool,
        t: &Self::Bool,
        e: &Self::Bool,
    ) -> Self::Bool {
        match (ctx, cond, t, e) {
            (
                RuntimeContext::Z3(ctx),
                RuntimeBool::Z3(cond),
                RuntimeBool::Z3(t),
                RuntimeBool::Z3(e),
            ) => RuntimeBool::Z3(Z3Backend::bool_ite(ctx, cond, t, e)),
            (
                RuntimeContext::Cvc5(ctx),
                RuntimeBool::Cvc5(cond),
                RuntimeBool::Cvc5(t),
                RuntimeBool::Cvc5(e),
            ) => RuntimeBool::Cvc5(Cvc5Backend::bool_ite(ctx, cond, t, e)),
            (RuntimeContext::Z3(_), _, _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn int_lit(ctx: &Self::Context, n: i64) -> Self::Int {
        match ctx {
            RuntimeContext::Z3(ctx) => RuntimeInt::Z3(Z3Backend::int_lit(ctx, n)),
            RuntimeContext::Cvc5(ctx) => RuntimeInt::Cvc5(Cvc5Backend::int_lit(ctx, n)),
        }
    }

    fn int_var(ctx: &Self::Context, name: &str) -> Self::Int {
        match ctx {
            RuntimeContext::Z3(ctx) => RuntimeInt::Z3(Z3Backend::int_var(ctx, name)),
            RuntimeContext::Cvc5(ctx) => RuntimeInt::Cvc5(Cvc5Backend::int_var(ctx, name)),
        }
    }

    fn int_add(ctx: &Self::Context, args: &[&Self::Int]) -> Self::Int {
        match ctx {
            RuntimeContext::Z3(ctx) => RuntimeInt::Z3(Z3Backend::int_add(
                ctx,
                &args
                    .iter()
                    .map(|arg| match arg {
                        RuntimeInt::Z3(arg) => arg,
                        _ => panic_mixed_solver_terms(SolverFamily::Z3),
                    })
                    .collect::<Vec<_>>(),
            )),
            RuntimeContext::Cvc5(ctx) => RuntimeInt::Cvc5(Cvc5Backend::int_add(
                ctx,
                &args
                    .iter()
                    .map(|arg| match arg {
                        RuntimeInt::Cvc5(arg) => arg,
                        _ => panic_mixed_solver_terms(SolverFamily::Cvc5),
                    })
                    .collect::<Vec<_>>(),
            )),
        }
    }

    fn int_sub(ctx: &Self::Context, args: &[&Self::Int]) -> Self::Int {
        match ctx {
            RuntimeContext::Z3(ctx) => RuntimeInt::Z3(Z3Backend::int_sub(
                ctx,
                &args
                    .iter()
                    .map(|arg| match arg {
                        RuntimeInt::Z3(arg) => arg,
                        _ => panic_mixed_solver_terms(SolverFamily::Z3),
                    })
                    .collect::<Vec<_>>(),
            )),
            RuntimeContext::Cvc5(ctx) => RuntimeInt::Cvc5(Cvc5Backend::int_sub(
                ctx,
                &args
                    .iter()
                    .map(|arg| match arg {
                        RuntimeInt::Cvc5(arg) => arg,
                        _ => panic_mixed_solver_terms(SolverFamily::Cvc5),
                    })
                    .collect::<Vec<_>>(),
            )),
        }
    }

    fn int_mul(ctx: &Self::Context, args: &[&Self::Int]) -> Self::Int {
        match ctx {
            RuntimeContext::Z3(ctx) => RuntimeInt::Z3(Z3Backend::int_mul(
                ctx,
                &args
                    .iter()
                    .map(|arg| match arg {
                        RuntimeInt::Z3(arg) => arg,
                        _ => panic_mixed_solver_terms(SolverFamily::Z3),
                    })
                    .collect::<Vec<_>>(),
            )),
            RuntimeContext::Cvc5(ctx) => RuntimeInt::Cvc5(Cvc5Backend::int_mul(
                ctx,
                &args
                    .iter()
                    .map(|arg| match arg {
                        RuntimeInt::Cvc5(arg) => arg,
                        _ => panic_mixed_solver_terms(SolverFamily::Cvc5),
                    })
                    .collect::<Vec<_>>(),
            )),
        }
    }

    fn int_div(ctx: &Self::Context, a: &Self::Int, b: &Self::Int) -> Self::Int {
        match (ctx, a, b) {
            (RuntimeContext::Z3(ctx), RuntimeInt::Z3(a), RuntimeInt::Z3(b)) => {
                RuntimeInt::Z3(Z3Backend::int_div(ctx, a, b))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeInt::Cvc5(a), RuntimeInt::Cvc5(b)) => {
                RuntimeInt::Cvc5(Cvc5Backend::int_div(ctx, a, b))
            }
            (RuntimeContext::Z3(_), _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn int_modulo(ctx: &Self::Context, a: &Self::Int, b: &Self::Int) -> Self::Int {
        match (ctx, a, b) {
            (RuntimeContext::Z3(ctx), RuntimeInt::Z3(a), RuntimeInt::Z3(b)) => {
                RuntimeInt::Z3(Z3Backend::int_modulo(ctx, a, b))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeInt::Cvc5(a), RuntimeInt::Cvc5(b)) => {
                RuntimeInt::Cvc5(Cvc5Backend::int_modulo(ctx, a, b))
            }
            (RuntimeContext::Z3(_), _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn int_neg(ctx: &Self::Context, a: &Self::Int) -> Self::Int {
        match (ctx, a) {
            (RuntimeContext::Z3(ctx), RuntimeInt::Z3(a)) => {
                RuntimeInt::Z3(Z3Backend::int_neg(ctx, a))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeInt::Cvc5(a)) => {
                RuntimeInt::Cvc5(Cvc5Backend::int_neg(ctx, a))
            }
            (RuntimeContext::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn int_eq(ctx: &Self::Context, a: &Self::Int, b: &Self::Int) -> Self::Bool {
        match (ctx, a, b) {
            (RuntimeContext::Z3(ctx), RuntimeInt::Z3(a), RuntimeInt::Z3(b)) => {
                RuntimeBool::Z3(Z3Backend::int_eq(ctx, a, b))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeInt::Cvc5(a), RuntimeInt::Cvc5(b)) => {
                RuntimeBool::Cvc5(Cvc5Backend::int_eq(ctx, a, b))
            }
            (RuntimeContext::Z3(_), _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn int_lt(ctx: &Self::Context, a: &Self::Int, b: &Self::Int) -> Self::Bool {
        match (ctx, a, b) {
            (RuntimeContext::Z3(ctx), RuntimeInt::Z3(a), RuntimeInt::Z3(b)) => {
                RuntimeBool::Z3(Z3Backend::int_lt(ctx, a, b))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeInt::Cvc5(a), RuntimeInt::Cvc5(b)) => {
                RuntimeBool::Cvc5(Cvc5Backend::int_lt(ctx, a, b))
            }
            (RuntimeContext::Z3(_), _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn int_le(ctx: &Self::Context, a: &Self::Int, b: &Self::Int) -> Self::Bool {
        match (ctx, a, b) {
            (RuntimeContext::Z3(ctx), RuntimeInt::Z3(a), RuntimeInt::Z3(b)) => {
                RuntimeBool::Z3(Z3Backend::int_le(ctx, a, b))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeInt::Cvc5(a), RuntimeInt::Cvc5(b)) => {
                RuntimeBool::Cvc5(Cvc5Backend::int_le(ctx, a, b))
            }
            (RuntimeContext::Z3(_), _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn int_gt(ctx: &Self::Context, a: &Self::Int, b: &Self::Int) -> Self::Bool {
        match (ctx, a, b) {
            (RuntimeContext::Z3(ctx), RuntimeInt::Z3(a), RuntimeInt::Z3(b)) => {
                RuntimeBool::Z3(Z3Backend::int_gt(ctx, a, b))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeInt::Cvc5(a), RuntimeInt::Cvc5(b)) => {
                RuntimeBool::Cvc5(Cvc5Backend::int_gt(ctx, a, b))
            }
            (RuntimeContext::Z3(_), _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn int_ge(ctx: &Self::Context, a: &Self::Int, b: &Self::Int) -> Self::Bool {
        match (ctx, a, b) {
            (RuntimeContext::Z3(ctx), RuntimeInt::Z3(a), RuntimeInt::Z3(b)) => {
                RuntimeBool::Z3(Z3Backend::int_ge(ctx, a, b))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeInt::Cvc5(a), RuntimeInt::Cvc5(b)) => {
                RuntimeBool::Cvc5(Cvc5Backend::int_ge(ctx, a, b))
            }
            (RuntimeContext::Z3(_), _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn int_ite(ctx: &Self::Context, cond: &Self::Bool, t: &Self::Int, e: &Self::Int) -> Self::Int {
        match (ctx, cond, t, e) {
            (
                RuntimeContext::Z3(ctx),
                RuntimeBool::Z3(cond),
                RuntimeInt::Z3(t),
                RuntimeInt::Z3(e),
            ) => RuntimeInt::Z3(Z3Backend::int_ite(ctx, cond, t, e)),
            (
                RuntimeContext::Cvc5(ctx),
                RuntimeBool::Cvc5(cond),
                RuntimeInt::Cvc5(t),
                RuntimeInt::Cvc5(e),
            ) => RuntimeInt::Cvc5(Cvc5Backend::int_ite(ctx, cond, t, e)),
            (RuntimeContext::Z3(_), _, _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn real_val(ctx: &Self::Context, num: i64, den: i64) -> Self::Real {
        match ctx {
            RuntimeContext::Z3(ctx) => RuntimeReal::Z3(Z3Backend::real_val(ctx, num, den)),
            RuntimeContext::Cvc5(ctx) => RuntimeReal::Cvc5(Cvc5Backend::real_val(ctx, num, den)),
        }
    }

    fn real_var(ctx: &Self::Context, name: &str) -> Self::Real {
        match ctx {
            RuntimeContext::Z3(ctx) => RuntimeReal::Z3(Z3Backend::real_var(ctx, name)),
            RuntimeContext::Cvc5(ctx) => RuntimeReal::Cvc5(Cvc5Backend::real_var(ctx, name)),
        }
    }

    fn real_add(ctx: &Self::Context, args: &[&Self::Real]) -> Self::Real {
        match ctx {
            RuntimeContext::Z3(ctx) => RuntimeReal::Z3(Z3Backend::real_add(
                ctx,
                &args
                    .iter()
                    .map(|arg| match arg {
                        RuntimeReal::Z3(arg) => arg,
                        _ => panic_mixed_solver_terms(SolverFamily::Z3),
                    })
                    .collect::<Vec<_>>(),
            )),
            RuntimeContext::Cvc5(ctx) => RuntimeReal::Cvc5(Cvc5Backend::real_add(
                ctx,
                &args
                    .iter()
                    .map(|arg| match arg {
                        RuntimeReal::Cvc5(arg) => arg,
                        _ => panic_mixed_solver_terms(SolverFamily::Cvc5),
                    })
                    .collect::<Vec<_>>(),
            )),
        }
    }

    fn real_sub(ctx: &Self::Context, args: &[&Self::Real]) -> Self::Real {
        match ctx {
            RuntimeContext::Z3(ctx) => RuntimeReal::Z3(Z3Backend::real_sub(
                ctx,
                &args
                    .iter()
                    .map(|arg| match arg {
                        RuntimeReal::Z3(arg) => arg,
                        _ => panic_mixed_solver_terms(SolverFamily::Z3),
                    })
                    .collect::<Vec<_>>(),
            )),
            RuntimeContext::Cvc5(ctx) => RuntimeReal::Cvc5(Cvc5Backend::real_sub(
                ctx,
                &args
                    .iter()
                    .map(|arg| match arg {
                        RuntimeReal::Cvc5(arg) => arg,
                        _ => panic_mixed_solver_terms(SolverFamily::Cvc5),
                    })
                    .collect::<Vec<_>>(),
            )),
        }
    }

    fn real_mul(ctx: &Self::Context, args: &[&Self::Real]) -> Self::Real {
        match ctx {
            RuntimeContext::Z3(ctx) => RuntimeReal::Z3(Z3Backend::real_mul(
                ctx,
                &args
                    .iter()
                    .map(|arg| match arg {
                        RuntimeReal::Z3(arg) => arg,
                        _ => panic_mixed_solver_terms(SolverFamily::Z3),
                    })
                    .collect::<Vec<_>>(),
            )),
            RuntimeContext::Cvc5(ctx) => RuntimeReal::Cvc5(Cvc5Backend::real_mul(
                ctx,
                &args
                    .iter()
                    .map(|arg| match arg {
                        RuntimeReal::Cvc5(arg) => arg,
                        _ => panic_mixed_solver_terms(SolverFamily::Cvc5),
                    })
                    .collect::<Vec<_>>(),
            )),
        }
    }

    fn real_div(ctx: &Self::Context, a: &Self::Real, b: &Self::Real) -> Self::Real {
        match (ctx, a, b) {
            (RuntimeContext::Z3(ctx), RuntimeReal::Z3(a), RuntimeReal::Z3(b)) => {
                RuntimeReal::Z3(Z3Backend::real_div(ctx, a, b))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeReal::Cvc5(a), RuntimeReal::Cvc5(b)) => {
                RuntimeReal::Cvc5(Cvc5Backend::real_div(ctx, a, b))
            }
            (RuntimeContext::Z3(_), _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn real_eq(ctx: &Self::Context, a: &Self::Real, b: &Self::Real) -> Self::Bool {
        match (ctx, a, b) {
            (RuntimeContext::Z3(ctx), RuntimeReal::Z3(a), RuntimeReal::Z3(b)) => {
                RuntimeBool::Z3(Z3Backend::real_eq(ctx, a, b))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeReal::Cvc5(a), RuntimeReal::Cvc5(b)) => {
                RuntimeBool::Cvc5(Cvc5Backend::real_eq(ctx, a, b))
            }
            (RuntimeContext::Z3(_), _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn real_lt(ctx: &Self::Context, a: &Self::Real, b: &Self::Real) -> Self::Bool {
        match (ctx, a, b) {
            (RuntimeContext::Z3(ctx), RuntimeReal::Z3(a), RuntimeReal::Z3(b)) => {
                RuntimeBool::Z3(Z3Backend::real_lt(ctx, a, b))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeReal::Cvc5(a), RuntimeReal::Cvc5(b)) => {
                RuntimeBool::Cvc5(Cvc5Backend::real_lt(ctx, a, b))
            }
            (RuntimeContext::Z3(_), _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn real_le(ctx: &Self::Context, a: &Self::Real, b: &Self::Real) -> Self::Bool {
        match (ctx, a, b) {
            (RuntimeContext::Z3(ctx), RuntimeReal::Z3(a), RuntimeReal::Z3(b)) => {
                RuntimeBool::Z3(Z3Backend::real_le(ctx, a, b))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeReal::Cvc5(a), RuntimeReal::Cvc5(b)) => {
                RuntimeBool::Cvc5(Cvc5Backend::real_le(ctx, a, b))
            }
            (RuntimeContext::Z3(_), _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn real_gt(ctx: &Self::Context, a: &Self::Real, b: &Self::Real) -> Self::Bool {
        match (ctx, a, b) {
            (RuntimeContext::Z3(ctx), RuntimeReal::Z3(a), RuntimeReal::Z3(b)) => {
                RuntimeBool::Z3(Z3Backend::real_gt(ctx, a, b))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeReal::Cvc5(a), RuntimeReal::Cvc5(b)) => {
                RuntimeBool::Cvc5(Cvc5Backend::real_gt(ctx, a, b))
            }
            (RuntimeContext::Z3(_), _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn real_ge(ctx: &Self::Context, a: &Self::Real, b: &Self::Real) -> Self::Bool {
        match (ctx, a, b) {
            (RuntimeContext::Z3(ctx), RuntimeReal::Z3(a), RuntimeReal::Z3(b)) => {
                RuntimeBool::Z3(Z3Backend::real_ge(ctx, a, b))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeReal::Cvc5(a), RuntimeReal::Cvc5(b)) => {
                RuntimeBool::Cvc5(Cvc5Backend::real_ge(ctx, a, b))
            }
            (RuntimeContext::Z3(_), _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn real_ite(
        ctx: &Self::Context,
        cond: &Self::Bool,
        t: &Self::Real,
        e: &Self::Real,
    ) -> Self::Real {
        match (ctx, cond, t, e) {
            (
                RuntimeContext::Z3(ctx),
                RuntimeBool::Z3(cond),
                RuntimeReal::Z3(t),
                RuntimeReal::Z3(e),
            ) => RuntimeReal::Z3(Z3Backend::real_ite(ctx, cond, t, e)),
            (
                RuntimeContext::Cvc5(ctx),
                RuntimeBool::Cvc5(cond),
                RuntimeReal::Cvc5(t),
                RuntimeReal::Cvc5(e),
            ) => RuntimeReal::Cvc5(Cvc5Backend::real_ite(ctx, cond, t, e)),
            (RuntimeContext::Z3(_), _, _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn int_sort(ctx: &Self::Context) -> Self::Sort {
        match ctx {
            RuntimeContext::Z3(ctx) => RuntimeSort::Z3(Z3Backend::int_sort(ctx)),
            RuntimeContext::Cvc5(ctx) => RuntimeSort::Cvc5(Cvc5Backend::int_sort(ctx)),
        }
    }

    fn bool_sort(ctx: &Self::Context) -> Self::Sort {
        match ctx {
            RuntimeContext::Z3(ctx) => RuntimeSort::Z3(Z3Backend::bool_sort(ctx)),
            RuntimeContext::Cvc5(ctx) => RuntimeSort::Cvc5(Cvc5Backend::bool_sort(ctx)),
        }
    }

    fn real_sort(ctx: &Self::Context) -> Self::Sort {
        match ctx {
            RuntimeContext::Z3(ctx) => RuntimeSort::Z3(Z3Backend::real_sort(ctx)),
            RuntimeContext::Cvc5(ctx) => RuntimeSort::Cvc5(Cvc5Backend::real_sort(ctx)),
        }
    }

    fn array_sort(ctx: &Self::Context, domain: &Self::Sort, range: &Self::Sort) -> Self::Sort {
        match (ctx, domain, range) {
            (RuntimeContext::Z3(ctx), RuntimeSort::Z3(domain), RuntimeSort::Z3(range)) => {
                RuntimeSort::Z3(Z3Backend::array_sort(ctx, domain, range))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeSort::Cvc5(domain), RuntimeSort::Cvc5(range)) => {
                RuntimeSort::Cvc5(Cvc5Backend::array_sort(ctx, domain, range))
            }
            (RuntimeContext::Z3(_), _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn sort_array_domain(ctx: &Self::Context, s: &Self::Sort) -> Option<Self::Sort> {
        match (ctx, s) {
            (RuntimeContext::Z3(ctx), RuntimeSort::Z3(s)) => {
                Z3Backend::sort_array_domain(ctx, s).map(RuntimeSort::Z3)
            }
            (RuntimeContext::Cvc5(ctx), RuntimeSort::Cvc5(s)) => {
                Cvc5Backend::sort_array_domain(ctx, s).map(RuntimeSort::Cvc5)
            }
            (RuntimeContext::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn sort_array_range(ctx: &Self::Context, s: &Self::Sort) -> Option<Self::Sort> {
        match (ctx, s) {
            (RuntimeContext::Z3(ctx), RuntimeSort::Z3(s)) => {
                Z3Backend::sort_array_range(ctx, s).map(RuntimeSort::Z3)
            }
            (RuntimeContext::Cvc5(ctx), RuntimeSort::Cvc5(s)) => {
                Cvc5Backend::sort_array_range(ctx, s).map(RuntimeSort::Cvc5)
            }
            (RuntimeContext::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn sort_to_string(ctx: &Self::Context, s: &Self::Sort) -> String {
        match (ctx, s) {
            (RuntimeContext::Z3(ctx), RuntimeSort::Z3(s)) => Z3Backend::sort_to_string(ctx, s),
            (RuntimeContext::Cvc5(ctx), RuntimeSort::Cvc5(s)) => {
                Cvc5Backend::sort_to_string(ctx, s)
            }
            (RuntimeContext::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn dynamic_fresh(ctx: &Self::Context, prefix: &str, sort: &Self::Sort) -> Self::Dynamic {
        match (ctx, sort) {
            (RuntimeContext::Z3(ctx), RuntimeSort::Z3(sort)) => {
                RuntimeDynamic::Z3(Z3Backend::dynamic_fresh(ctx, prefix, sort))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeSort::Cvc5(sort)) => {
                RuntimeDynamic::Cvc5(Cvc5Backend::dynamic_fresh(ctx, prefix, sort))
            }
            (RuntimeContext::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn dynamic_const(ctx: &Self::Context, name: &str, sort: &Self::Sort) -> Self::Dynamic {
        match (ctx, sort) {
            (RuntimeContext::Z3(ctx), RuntimeSort::Z3(sort)) => {
                RuntimeDynamic::Z3(Z3Backend::dynamic_const(ctx, name, sort))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeSort::Cvc5(sort)) => {
                RuntimeDynamic::Cvc5(Cvc5Backend::dynamic_const(ctx, name, sort))
            }
            (RuntimeContext::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn dynamic_from_bool(ctx: &Self::Context, b: &Self::Bool) -> Self::Dynamic {
        match (ctx, b) {
            (RuntimeContext::Z3(ctx), RuntimeBool::Z3(b)) => {
                RuntimeDynamic::Z3(Z3Backend::dynamic_from_bool(ctx, b))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeBool::Cvc5(b)) => {
                RuntimeDynamic::Cvc5(Cvc5Backend::dynamic_from_bool(ctx, b))
            }
            (RuntimeContext::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn dynamic_from_int(ctx: &Self::Context, i: &Self::Int) -> Self::Dynamic {
        match (ctx, i) {
            (RuntimeContext::Z3(ctx), RuntimeInt::Z3(i)) => {
                RuntimeDynamic::Z3(Z3Backend::dynamic_from_int(ctx, i))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeInt::Cvc5(i)) => {
                RuntimeDynamic::Cvc5(Cvc5Backend::dynamic_from_int(ctx, i))
            }
            (RuntimeContext::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn dynamic_from_real(ctx: &Self::Context, r: &Self::Real) -> Self::Dynamic {
        match (ctx, r) {
            (RuntimeContext::Z3(ctx), RuntimeReal::Z3(r)) => {
                RuntimeDynamic::Z3(Z3Backend::dynamic_from_real(ctx, r))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeReal::Cvc5(r)) => {
                RuntimeDynamic::Cvc5(Cvc5Backend::dynamic_from_real(ctx, r))
            }
            (RuntimeContext::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn dynamic_from_array(ctx: &Self::Context, a: &Self::Array) -> Self::Dynamic {
        match (ctx, a) {
            (RuntimeContext::Z3(ctx), RuntimeArray::Z3(a)) => {
                RuntimeDynamic::Z3(Z3Backend::dynamic_from_array(ctx, a))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeArray::Cvc5(a)) => {
                RuntimeDynamic::Cvc5(Cvc5Backend::dynamic_from_array(ctx, a))
            }
            (RuntimeContext::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn dynamic_as_bool(ctx: &Self::Context, d: &Self::Dynamic) -> Option<Self::Bool> {
        match (ctx, d) {
            (RuntimeContext::Z3(ctx), RuntimeDynamic::Z3(d)) => {
                Z3Backend::dynamic_as_bool(ctx, d).map(RuntimeBool::Z3)
            }
            (RuntimeContext::Cvc5(ctx), RuntimeDynamic::Cvc5(d)) => {
                Cvc5Backend::dynamic_as_bool(ctx, d).map(RuntimeBool::Cvc5)
            }
            (RuntimeContext::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn dynamic_as_int(ctx: &Self::Context, d: &Self::Dynamic) -> Option<Self::Int> {
        match (ctx, d) {
            (RuntimeContext::Z3(ctx), RuntimeDynamic::Z3(d)) => {
                Z3Backend::dynamic_as_int(ctx, d).map(RuntimeInt::Z3)
            }
            (RuntimeContext::Cvc5(ctx), RuntimeDynamic::Cvc5(d)) => {
                Cvc5Backend::dynamic_as_int(ctx, d).map(RuntimeInt::Cvc5)
            }
            (RuntimeContext::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn dynamic_as_real(ctx: &Self::Context, d: &Self::Dynamic) -> Option<Self::Real> {
        match (ctx, d) {
            (RuntimeContext::Z3(ctx), RuntimeDynamic::Z3(d)) => {
                Z3Backend::dynamic_as_real(ctx, d).map(RuntimeReal::Z3)
            }
            (RuntimeContext::Cvc5(ctx), RuntimeDynamic::Cvc5(d)) => {
                Cvc5Backend::dynamic_as_real(ctx, d).map(RuntimeReal::Cvc5)
            }
            (RuntimeContext::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn dynamic_as_array(ctx: &Self::Context, d: &Self::Dynamic) -> Option<Self::Array> {
        match (ctx, d) {
            (RuntimeContext::Z3(ctx), RuntimeDynamic::Z3(d)) => {
                Z3Backend::dynamic_as_array(ctx, d).map(RuntimeArray::Z3)
            }
            (RuntimeContext::Cvc5(ctx), RuntimeDynamic::Cvc5(d)) => {
                Cvc5Backend::dynamic_as_array(ctx, d).map(RuntimeArray::Cvc5)
            }
            (RuntimeContext::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn dynamic_eq(ctx: &Self::Context, a: &Self::Dynamic, b: &Self::Dynamic) -> Self::Bool {
        match (ctx, a, b) {
            (RuntimeContext::Z3(ctx), RuntimeDynamic::Z3(a), RuntimeDynamic::Z3(b)) => {
                RuntimeBool::Z3(Z3Backend::dynamic_eq(ctx, a, b))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeDynamic::Cvc5(a), RuntimeDynamic::Cvc5(b)) => {
                RuntimeBool::Cvc5(Cvc5Backend::dynamic_eq(ctx, a, b))
            }
            (RuntimeContext::Z3(_), _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn dynamic_ite(
        ctx: &Self::Context,
        cond: &Self::Bool,
        t: &Self::Dynamic,
        e: &Self::Dynamic,
    ) -> Self::Dynamic {
        match (ctx, cond, t, e) {
            (
                RuntimeContext::Z3(ctx),
                RuntimeBool::Z3(cond),
                RuntimeDynamic::Z3(t),
                RuntimeDynamic::Z3(e),
            ) => RuntimeDynamic::Z3(Z3Backend::dynamic_ite(ctx, cond, t, e)),
            (
                RuntimeContext::Cvc5(ctx),
                RuntimeBool::Cvc5(cond),
                RuntimeDynamic::Cvc5(t),
                RuntimeDynamic::Cvc5(e),
            ) => RuntimeDynamic::Cvc5(Cvc5Backend::dynamic_ite(ctx, cond, t, e)),
            (RuntimeContext::Z3(_), _, _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn dynamic_get_sort(ctx: &Self::Context, d: &Self::Dynamic) -> Self::Sort {
        match (ctx, d) {
            (RuntimeContext::Z3(ctx), RuntimeDynamic::Z3(d)) => {
                RuntimeSort::Z3(Z3Backend::dynamic_get_sort(ctx, d))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeDynamic::Cvc5(d)) => {
                RuntimeSort::Cvc5(Cvc5Backend::dynamic_get_sort(ctx, d))
            }
            (RuntimeContext::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn array_new_const(
        ctx: &Self::Context,
        name: &str,
        domain: &Self::Sort,
        range: &Self::Sort,
    ) -> Self::Array {
        match (ctx, domain, range) {
            (RuntimeContext::Z3(ctx), RuntimeSort::Z3(domain), RuntimeSort::Z3(range)) => {
                RuntimeArray::Z3(Z3Backend::array_new_const(ctx, name, domain, range))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeSort::Cvc5(domain), RuntimeSort::Cvc5(range)) => {
                RuntimeArray::Cvc5(Cvc5Backend::array_new_const(ctx, name, domain, range))
            }
            (RuntimeContext::Z3(_), _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn array_const_array(
        ctx: &Self::Context,
        domain: &Self::Sort,
        default: &Self::Dynamic,
    ) -> Self::Array {
        match (ctx, domain, default) {
            (RuntimeContext::Z3(ctx), RuntimeSort::Z3(domain), RuntimeDynamic::Z3(default)) => {
                RuntimeArray::Z3(Z3Backend::array_const_array(ctx, domain, default))
            }
            (
                RuntimeContext::Cvc5(ctx),
                RuntimeSort::Cvc5(domain),
                RuntimeDynamic::Cvc5(default),
            ) => RuntimeArray::Cvc5(Cvc5Backend::array_const_array(ctx, domain, default)),
            (RuntimeContext::Z3(_), _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn array_select(ctx: &Self::Context, a: &Self::Array, index: &Self::Dynamic) -> Self::Dynamic {
        match (ctx, a, index) {
            (RuntimeContext::Z3(ctx), RuntimeArray::Z3(a), RuntimeDynamic::Z3(index)) => {
                RuntimeDynamic::Z3(Z3Backend::array_select(ctx, a, index))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeArray::Cvc5(a), RuntimeDynamic::Cvc5(index)) => {
                RuntimeDynamic::Cvc5(Cvc5Backend::array_select(ctx, a, index))
            }
            (RuntimeContext::Z3(_), _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn array_store(
        ctx: &Self::Context,
        a: &Self::Array,
        index: &Self::Dynamic,
        value: &Self::Dynamic,
    ) -> Self::Array {
        match (ctx, a, index, value) {
            (
                RuntimeContext::Z3(ctx),
                RuntimeArray::Z3(a),
                RuntimeDynamic::Z3(index),
                RuntimeDynamic::Z3(value),
            ) => RuntimeArray::Z3(Z3Backend::array_store(ctx, a, index, value)),
            (
                RuntimeContext::Cvc5(ctx),
                RuntimeArray::Cvc5(a),
                RuntimeDynamic::Cvc5(index),
                RuntimeDynamic::Cvc5(value),
            ) => RuntimeArray::Cvc5(Cvc5Backend::array_store(ctx, a, index, value)),
            (RuntimeContext::Z3(_), _, _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn array_eq(ctx: &Self::Context, a: &Self::Array, b: Self::Array) -> Self::Bool {
        match (ctx, a, b) {
            (RuntimeContext::Z3(ctx), RuntimeArray::Z3(a), RuntimeArray::Z3(b)) => {
                RuntimeBool::Z3(Z3Backend::array_eq(ctx, a, b))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeArray::Cvc5(a), RuntimeArray::Cvc5(b)) => {
                RuntimeBool::Cvc5(Cvc5Backend::array_eq(ctx, a, b))
            }
            (RuntimeContext::Z3(_), _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn array_ite(
        ctx: &Self::Context,
        cond: &Self::Bool,
        t: &Self::Array,
        e: &Self::Array,
    ) -> Self::Array {
        match (ctx, cond, t, e) {
            (
                RuntimeContext::Z3(ctx),
                RuntimeBool::Z3(cond),
                RuntimeArray::Z3(t),
                RuntimeArray::Z3(e),
            ) => RuntimeArray::Z3(Z3Backend::array_ite(ctx, cond, t, e)),
            (
                RuntimeContext::Cvc5(ctx),
                RuntimeBool::Cvc5(cond),
                RuntimeArray::Cvc5(t),
                RuntimeArray::Cvc5(e),
            ) => RuntimeArray::Cvc5(Cvc5Backend::array_ite(ctx, cond, t, e)),
            (RuntimeContext::Z3(_), _, _, _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _, _, _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn array_get_sort(ctx: &Self::Context, a: &Self::Array) -> Self::Sort {
        match (ctx, a) {
            (RuntimeContext::Z3(ctx), RuntimeArray::Z3(a)) => {
                RuntimeSort::Z3(Z3Backend::array_get_sort(ctx, a))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeArray::Cvc5(a)) => {
                RuntimeSort::Cvc5(Cvc5Backend::array_get_sort(ctx, a))
            }
            (RuntimeContext::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn forall(ctx: &Self::Context, bound: &[&Self::Dynamic], body: &Self::Bool) -> Self::Bool {
        match (ctx, body) {
            (RuntimeContext::Z3(ctx), RuntimeBool::Z3(body)) => RuntimeBool::Z3(Z3Backend::forall(
                ctx,
                &bound
                    .iter()
                    .map(|arg| match arg {
                        RuntimeDynamic::Z3(arg) => arg,
                        _ => panic_mixed_solver_terms(SolverFamily::Z3),
                    })
                    .collect::<Vec<_>>(),
                body,
            )),
            (RuntimeContext::Cvc5(ctx), RuntimeBool::Cvc5(body)) => {
                RuntimeBool::Cvc5(Cvc5Backend::forall(
                    ctx,
                    &bound
                        .iter()
                        .map(|arg| match arg {
                            RuntimeDynamic::Cvc5(arg) => arg,
                            _ => panic_mixed_solver_terms(SolverFamily::Cvc5),
                        })
                        .collect::<Vec<_>>(),
                    body,
                ))
            }
            (RuntimeContext::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn exists(ctx: &Self::Context, bound: &[&Self::Dynamic], body: &Self::Bool) -> Self::Bool {
        match (ctx, body) {
            (RuntimeContext::Z3(ctx), RuntimeBool::Z3(body)) => RuntimeBool::Z3(Z3Backend::exists(
                ctx,
                &bound
                    .iter()
                    .map(|arg| match arg {
                        RuntimeDynamic::Z3(arg) => arg,
                        _ => panic_mixed_solver_terms(SolverFamily::Z3),
                    })
                    .collect::<Vec<_>>(),
                body,
            )),
            (RuntimeContext::Cvc5(ctx), RuntimeBool::Cvc5(body)) => {
                RuntimeBool::Cvc5(Cvc5Backend::exists(
                    ctx,
                    &bound
                        .iter()
                        .map(|arg| match arg {
                            RuntimeDynamic::Cvc5(arg) => arg,
                            _ => panic_mixed_solver_terms(SolverFamily::Cvc5),
                        })
                        .collect::<Vec<_>>(),
                    body,
                ))
            }
            (RuntimeContext::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn lambda(ctx: &Self::Context, bound: &[&Self::Dynamic], body: &Self::Dynamic) -> Self::Array {
        match (ctx, body) {
            (RuntimeContext::Z3(ctx), RuntimeDynamic::Z3(body)) => {
                RuntimeArray::Z3(Z3Backend::lambda(
                    ctx,
                    &bound
                        .iter()
                        .map(|arg| match arg {
                            RuntimeDynamic::Z3(arg) => arg,
                            _ => panic_mixed_solver_terms(SolverFamily::Z3),
                        })
                        .collect::<Vec<_>>(),
                    body,
                ))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeDynamic::Cvc5(body)) => {
                RuntimeArray::Cvc5(Cvc5Backend::lambda(
                    ctx,
                    &bound
                        .iter()
                        .map(|arg| match arg {
                            RuntimeDynamic::Cvc5(arg) => arg,
                            _ => panic_mixed_solver_terms(SolverFamily::Cvc5),
                        })
                        .collect::<Vec<_>>(),
                    body,
                ))
            }
            (RuntimeContext::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn func_decl_new(
        ctx: &Self::Context,
        name: &str,
        domain: &[&Self::Sort],
        range: &Self::Sort,
    ) -> Self::FuncDecl {
        match (ctx, range) {
            (RuntimeContext::Z3(ctx), RuntimeSort::Z3(range)) => {
                RuntimeFuncDecl::Z3(Z3Backend::func_decl_new(
                    ctx,
                    name,
                    &domain
                        .iter()
                        .map(|arg| match arg {
                            RuntimeSort::Z3(arg) => arg,
                            _ => panic_mixed_solver_terms(SolverFamily::Z3),
                        })
                        .collect::<Vec<_>>(),
                    range,
                ))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeSort::Cvc5(range)) => {
                RuntimeFuncDecl::Cvc5(Cvc5Backend::func_decl_new(
                    ctx,
                    name,
                    &domain
                        .iter()
                        .map(|arg| match arg {
                            RuntimeSort::Cvc5(arg) => arg,
                            _ => panic_mixed_solver_terms(SolverFamily::Cvc5),
                        })
                        .collect::<Vec<_>>(),
                    range,
                ))
            }
            (RuntimeContext::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn func_decl_apply(
        ctx: &Self::Context,
        f: &Self::FuncDecl,
        args: &[&Self::Dynamic],
    ) -> Self::Dynamic {
        match (ctx, f) {
            (RuntimeContext::Z3(ctx), RuntimeFuncDecl::Z3(f)) => {
                RuntimeDynamic::Z3(Z3Backend::func_decl_apply(
                    ctx,
                    f,
                    &args
                        .iter()
                        .map(|arg| match arg {
                            RuntimeDynamic::Z3(arg) => arg,
                            _ => panic_mixed_solver_terms(SolverFamily::Z3),
                        })
                        .collect::<Vec<_>>(),
                ))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeFuncDecl::Cvc5(f)) => {
                RuntimeDynamic::Cvc5(Cvc5Backend::func_decl_apply(
                    ctx,
                    f,
                    &args
                        .iter()
                        .map(|arg| match arg {
                            RuntimeDynamic::Cvc5(arg) => arg,
                            _ => panic_mixed_solver_terms(SolverFamily::Cvc5),
                        })
                        .collect::<Vec<_>>(),
                ))
            }
            (RuntimeContext::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn func_decl_name(ctx: &Self::Context, f: &Self::FuncDecl) -> String {
        match (ctx, f) {
            (RuntimeContext::Z3(ctx), RuntimeFuncDecl::Z3(f)) => Z3Backend::func_decl_name(ctx, f),
            (RuntimeContext::Cvc5(ctx), RuntimeFuncDecl::Cvc5(f)) => {
                Cvc5Backend::func_decl_name(ctx, f)
            }
            (RuntimeContext::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn datatype_builder_new(ctx: &Self::Context, name: &str) -> Self::DatatypeBuilder {
        match ctx {
            RuntimeContext::Z3(ctx) => {
                RuntimeDatatypeBuilder::Z3(Z3Backend::datatype_builder_new(ctx, name))
            }
            RuntimeContext::Cvc5(ctx) => {
                RuntimeDatatypeBuilder::Cvc5(Cvc5Backend::datatype_builder_new(ctx, name))
            }
        }
    }

    fn datatype_builder_variant(
        ctx: &Self::Context,
        builder: Self::DatatypeBuilder,
        name: &str,
        fields: Vec<(&str, Self::DatatypeAccessor)>,
    ) -> Self::DatatypeBuilder {
        match (ctx, builder) {
            (RuntimeContext::Z3(ctx), RuntimeDatatypeBuilder::Z3(builder)) => {
                RuntimeDatatypeBuilder::Z3(Z3Backend::datatype_builder_variant(
                    ctx,
                    builder,
                    name,
                    fields
                        .into_iter()
                        .map(|(field, accessor)| match accessor {
                            RuntimeDatatypeAccessor::Z3(accessor) => (field, accessor),
                            _ => panic_mixed_solver_terms(SolverFamily::Z3),
                        })
                        .collect(),
                ))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeDatatypeBuilder::Cvc5(builder)) => {
                RuntimeDatatypeBuilder::Cvc5(Cvc5Backend::datatype_builder_variant(
                    ctx,
                    builder,
                    name,
                    fields
                        .into_iter()
                        .map(|(field, accessor)| match accessor {
                            RuntimeDatatypeAccessor::Cvc5(accessor) => (field, accessor),
                            _ => panic_mixed_solver_terms(SolverFamily::Cvc5),
                        })
                        .collect(),
                ))
            }
            (RuntimeContext::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn datatype_builder_finish(
        ctx: &Self::Context,
        builder: Self::DatatypeBuilder,
    ) -> Self::DatatypeSort {
        match (ctx, builder) {
            (RuntimeContext::Z3(ctx), RuntimeDatatypeBuilder::Z3(builder)) => {
                let dt = Z3Backend::datatype_builder_finish(ctx, builder);
                RuntimeDatatypeSort {
                    sort: RuntimeSort::Z3(dt.sort),
                    variants: dt
                        .variants
                        .into_iter()
                        .map(|variant| DatatypeVariant {
                            name: variant.name,
                            constructor: RuntimeFuncDecl::Z3(variant.constructor),
                            tester: RuntimeFuncDecl::Z3(variant.tester),
                            accessors: variant
                                .accessors
                                .into_iter()
                                .map(RuntimeFuncDecl::Z3)
                                .collect(),
                        })
                        .collect(),
                }
            }
            (RuntimeContext::Cvc5(ctx), RuntimeDatatypeBuilder::Cvc5(builder)) => {
                let dt = Cvc5Backend::datatype_builder_finish(ctx, builder);
                RuntimeDatatypeSort {
                    sort: RuntimeSort::Cvc5(dt.sort),
                    variants: dt
                        .variants
                        .into_iter()
                        .map(|variant| DatatypeVariant {
                            name: variant.name,
                            constructor: RuntimeFuncDecl::Cvc5(variant.constructor),
                            tester: RuntimeFuncDecl::Cvc5(variant.tester),
                            accessors: variant
                                .accessors
                                .into_iter()
                                .map(RuntimeFuncDecl::Cvc5)
                                .collect(),
                        })
                        .collect(),
                }
            }
            (RuntimeContext::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn datatype_accessor_sort(ctx: &Self::Context, sort: Self::Sort) -> Self::DatatypeAccessor {
        match (ctx, sort) {
            (RuntimeContext::Z3(ctx), RuntimeSort::Z3(sort)) => {
                RuntimeDatatypeAccessor::Z3(Z3Backend::datatype_accessor_sort(ctx, sort))
            }
            (RuntimeContext::Cvc5(ctx), RuntimeSort::Cvc5(sort)) => {
                RuntimeDatatypeAccessor::Cvc5(Cvc5Backend::datatype_accessor_sort(ctx, sort))
            }
            (RuntimeContext::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeContext::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn params_new() -> Self::Params {
        match active_solver_family() {
            SolverFamily::Z3 => RuntimeParams::Z3(Z3Backend::params_new()),
            SolverFamily::Cvc5 => RuntimeParams::Cvc5(Cvc5Backend::params_new()),
        }
    }

    fn params_set_bool(params: &mut Self::Params, key: &str, val: bool) {
        match params {
            RuntimeParams::Z3(params) => Z3Backend::params_set_bool(params, key, val),
            RuntimeParams::Cvc5(params) => Cvc5Backend::params_set_bool(params, key, val),
        }
    }

    fn params_set_u32(params: &mut Self::Params, key: &str, val: u32) {
        match params {
            RuntimeParams::Z3(params) => Z3Backend::params_set_u32(params, key, val),
            RuntimeParams::Cvc5(params) => Cvc5Backend::params_set_u32(params, key, val),
        }
    }

    fn params_set_symbol(params: &mut Self::Params, key: &str, val: &str) {
        match params {
            RuntimeParams::Z3(params) => Z3Backend::params_set_symbol(params, key, val),
            RuntimeParams::Cvc5(params) => Cvc5Backend::params_set_symbol(params, key, val),
        }
    }

    fn model_eval_bool(model: &Self::Model, b: &Self::Bool) -> Option<bool> {
        match (model, b) {
            (RuntimeModel::Z3(model), RuntimeBool::Z3(b)) => Z3Backend::model_eval_bool(model, b),
            (RuntimeModel::Cvc5(model), RuntimeBool::Cvc5(b)) => {
                Cvc5Backend::model_eval_bool(model, b)
            }
            (RuntimeModel::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeModel::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn model_eval_int(model: &Self::Model, i: &Self::Int) -> Option<i64> {
        match (model, i) {
            (RuntimeModel::Z3(model), RuntimeInt::Z3(i)) => Z3Backend::model_eval_int(model, i),
            (RuntimeModel::Cvc5(model), RuntimeInt::Cvc5(i)) => {
                Cvc5Backend::model_eval_int(model, i)
            }
            (RuntimeModel::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeModel::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }

    fn model_eval_dynamic(model: &Self::Model, d: &Self::Dynamic) -> Option<String> {
        match (model, d) {
            (RuntimeModel::Z3(model), RuntimeDynamic::Z3(d)) => {
                Z3Backend::model_eval_dynamic(model, d)
            }
            (RuntimeModel::Cvc5(model), RuntimeDynamic::Cvc5(d)) => {
                Cvc5Backend::model_eval_dynamic(model, d)
            }
            (RuntimeModel::Z3(_), _) => panic_mixed_solver_terms(SolverFamily::Z3),
            (RuntimeModel::Cvc5(_), _) => panic_mixed_solver_terms(SolverFamily::Cvc5),
        }
    }
}

pub(crate) fn z3_check_chc(chc_text: &str, error_relation: &str, timeout_ms: u64) -> ChcResult {
    let limits = SolverLimits::from_timeout_ms(timeout_ms);
    let fp = Z3Fixedpoint::new();

    let mut params = Z3Params::new();
    params.set_symbol("engine", "spacer");
    params.set_bool("xform.slice", false);
    if timeout_ms > 0 {
        #[allow(clippy::cast_possible_truncation)]
        params.set_u32("timeout", timeout_ms.min(u64::from(u32::MAX)) as u32);
    }
    fp.set_params(&params);

    if let Err(e) = fp.from_string(chc_text) {
        return ChcResult::Unknown(format!("CHC parse error: {e}"));
    }

    let error_rel = Z3FuncDecl::new(error_relation, &[], &Z3Sort::bool());
    fp.register_relation(&error_rel);

    let error_query = error_rel.apply(&[]);
    match with_z3_interrupt_after(limits, || fp.query(&error_query)) {
        Z3SatResult::Unsat => ChcResult::Proved,
        Z3SatResult::Sat => {
            let answer = fp.get_answer().map_or_else(String::new, |a| format!("{a}"));
            ChcResult::Counterexample(answer)
        }
        Z3SatResult::Unknown => ChcResult::Unknown(fp.get_reason_unknown()),
    }
}

pub(crate) fn cvc5_check_chc(chc_text: &str, _error_relation: &str, _timeout_ms: u64) -> ChcResult {
    ChcResult::Unknown(format!(
        "CVC5 does not support Abide's current Z3-style fixedpoint CHC text (`declare-var`, `rule`, `query`) yet; use `--chc-solver z3` for IC3/PDR (input size: {} bytes)",
        chc_text.len()
    ))
}

// ── AbideSolver wrapper ─────────────────────────────────────────────

/// Thin wrapper around a concrete backend solver.
pub struct AbideSolver<B: SolverBackend = Z3Backend> {
    _ctx: B::Context,
    backend: B,
}

impl<B: SolverBackend> AbideSolver<B> {
    pub fn new() -> Self {
        let ctx = B::context_new();
        Self {
            backend: B::solver_new(&ctx),
            _ctx: ctx,
        }
    }

    pub fn assert<T: Borrow<B::Bool>>(&self, c: T) {
        self.backend.solver_assert(c.borrow());
    }

    pub fn check(&self) -> SatResult {
        self.backend.solver_check()
    }

    pub fn check_with_limits(&self, limits: SolverLimits) -> SatResult {
        self.backend.solver_check_with_limits(limits)
    }

    pub fn push(&self) {
        self.backend.solver_push();
    }

    pub fn pop(&self) {
        self.backend.solver_pop();
    }

    pub fn set_timeout(&self, ms: u64) {
        self.backend.solver_set_timeout(ms);
    }

    pub fn get_model(&self) -> Option<B::Model> {
        self.backend.solver_get_model()
    }

    pub fn family(&self) -> SolverFamily {
        B::family()
    }

    pub fn capabilities(&self) -> SolverCapabilities {
        B::capabilities()
    }
}

impl<B: SolverBackend> Default for AbideSolver<B> {
    fn default() -> Self {
        Self::new()
    }
}

// ── Type aliases (active backend = runtime-selected) ────────────────

/// The active solver backend used by the verifier SMT facade.
pub type ActiveBackend = RuntimeBackend;

pub type Bool = <ActiveBackend as SolverBackend>::Bool;
pub type Int = <ActiveBackend as SolverBackend>::Int;
pub type Real = <ActiveBackend as SolverBackend>::Real;
pub type Dynamic = <ActiveBackend as SolverBackend>::Dynamic;
pub type Array = <ActiveBackend as SolverBackend>::Array;
pub type Sort = <ActiveBackend as SolverBackend>::Sort;
pub type FuncDecl = <ActiveBackend as SolverBackend>::FuncDecl;
pub type Model = <ActiveBackend as SolverBackend>::Model;
pub type DatatypeSort = <ActiveBackend as SolverBackend>::DatatypeSort;
pub type DatatypeAccessor = <ActiveBackend as SolverBackend>::DatatypeAccessor;
pub type DatatypeBuilder = <ActiveBackend as SolverBackend>::DatatypeBuilder;
pub type Params = <ActiveBackend as SolverBackend>::Params;

#[cfg(test)]
#[allow(clippy::let_unit_value)]
mod tests {
    use super::*;

    fn exercise_backend_surface<B: SolverBackend>() {
        let ctx = B::context_new();
        let solver = AbideSolver::<B>::new();
        solver.set_timeout(1_000);

        let t = B::bool_const(&ctx, true);
        let f = B::bool_const(&ctx, false);
        let b = B::bool_var(&ctx, "backend_surface_b");
        let not_b = B::bool_not(&ctx, &b);
        let bool_ite = B::bool_ite(&ctx, &b, &t, &f);
        let bool_formula = B::bool_and(
            &ctx,
            &[
                &B::bool_or(&ctx, &[&b, &not_b]),
                &B::bool_implies(&ctx, &bool_ite, &b),
                &B::bool_xor(&ctx, &t, &f),
                &B::bool_eq(&ctx, &t, &t),
            ],
        );

        let one = B::int_lit(&ctx, 1);
        let two = B::int_lit(&ctx, 2);
        let three = B::int_lit(&ctx, 3);
        let x = B::int_var(&ctx, "backend_surface_x");
        let int_expr = B::int_sub(
            &ctx,
            &[
                &B::int_add(&ctx, &[&one, &two, &three]),
                &B::int_lit(&ctx, 1),
            ],
        );
        let int_expr = B::int_mul(&ctx, &[&int_expr, &B::int_lit(&ctx, 1)]);
        let int_expr = B::int_div(&ctx, &int_expr, &B::int_lit(&ctx, 1));
        let int_expr = B::int_sub(
            &ctx,
            &[&int_expr, &B::int_modulo(&ctx, &B::int_lit(&ctx, 5), &two)],
        );
        let int_expr = B::int_add(&ctx, &[&int_expr, &B::int_neg(&ctx, &B::int_lit(&ctx, -1))]);
        let int_ite = B::int_ite(&ctx, &t, &int_expr, &one);
        let int_formula = B::bool_and(
            &ctx,
            &[
                &B::int_eq(&ctx, &x, &B::int_lit(&ctx, 6)),
                &B::int_lt(&ctx, &one, &two),
                &B::int_le(&ctx, &two, &two),
                &B::int_gt(&ctx, &three, &two),
                &B::int_ge(&ctx, &three, &three),
                &B::int_eq(&ctx, &int_ite, &B::int_lit(&ctx, 6)),
            ],
        );

        let r1 = B::real_val(&ctx, 1, 2);
        let r2 = B::real_val(&ctx, 3, 2);
        let r3 = B::real_var(&ctx, "backend_surface_r");
        let real_expr = B::real_div(
            &ctx,
            &B::real_mul(
                &ctx,
                &[&B::real_add(&ctx, &[&r1, &r2]), &B::real_val(&ctx, 2, 1)],
            ),
            &B::real_val(&ctx, 2, 1),
        );
        let real_expr = B::real_sub(&ctx, &[&real_expr, &B::real_val(&ctx, 1, 1)]);
        let real_ite = B::real_ite(&ctx, &t, &real_expr, &r1);
        let real_formula = B::bool_and(
            &ctx,
            &[
                &B::real_eq(&ctx, &r3, &B::real_val(&ctx, 1, 1)),
                &B::real_lt(&ctx, &r1, &r2),
                &B::real_le(&ctx, &r1, &r1),
                &B::real_gt(&ctx, &r2, &r1),
                &B::real_ge(&ctx, &r2, &r2),
                &B::real_eq(&ctx, &real_ite, &B::real_val(&ctx, 1, 1)),
            ],
        );

        let int_sort = B::int_sort(&ctx);
        let bool_sort = B::bool_sort(&ctx);
        let real_sort = B::real_sort(&ctx);
        let array_sort = B::array_sort(&ctx, &int_sort, &bool_sort);
        assert_eq!(B::sort_array_domain(&ctx, &array_sort).is_some(), true);
        assert_eq!(B::sort_array_range(&ctx, &array_sort).is_some(), true);
        assert!(!B::sort_to_string(&ctx, &real_sort).is_empty());

        let dx = B::dynamic_from_int(&ctx, &x);
        let db = B::dynamic_from_bool(&ctx, &b);
        let dr = B::dynamic_from_real(&ctx, &r3);
        let fresh = B::dynamic_fresh(&ctx, "backend_surface_fresh", &int_sort);
        let named = B::dynamic_const(&ctx, "backend_surface_named", &int_sort);
        assert!(B::dynamic_as_int(&ctx, &dx).is_some());
        assert!(B::dynamic_as_bool(&ctx, &db).is_some());
        assert!(B::dynamic_as_real(&ctx, &dr).is_some());
        let _ = B::dynamic_get_sort(&ctx, &fresh);
        let dyn_ite = B::dynamic_ite(&ctx, &t, &dx, &named);
        let dyn_formula = B::dynamic_eq(&ctx, &dyn_ite, &dx);

        let array = B::array_new_const(&ctx, "backend_surface_array", &int_sort, &bool_sort);
        let default_array = B::array_const_array(&ctx, &int_sort, &B::dynamic_from_bool(&ctx, &f));
        let stored = B::array_store(
            &ctx,
            &default_array,
            &B::dynamic_from_int(&ctx, &one),
            &B::dynamic_from_bool(&ctx, &t),
        );
        let selected = B::array_select(&ctx, &stored, &B::dynamic_from_int(&ctx, &one));
        let arr_dyn = B::dynamic_from_array(&ctx, &array);
        assert!(B::dynamic_as_array(&ctx, &arr_dyn).is_some());
        let _ = B::array_get_sort(&ctx, &stored);
        let array_formula = B::bool_and(
            &ctx,
            &[
                &B::dynamic_eq(&ctx, &selected, &B::dynamic_from_bool(&ctx, &t)),
                &B::array_eq(
                    &ctx,
                    &B::array_ite(&ctx, &t, &stored, &default_array),
                    stored.clone(),
                ),
            ],
        );

        let quantifier_formula = if B::family() == SolverFamily::Z3 {
            let q_var = B::dynamic_const(&ctx, "backend_surface_q", &int_sort);
            let q_int = B::dynamic_as_int(&ctx, &q_var).expect("int dynamic");
            let q_body = B::int_eq(&ctx, &q_int, &q_int);
            let forall = B::forall(&ctx, &[&q_var], &q_body);
            let exists = B::exists(&ctx, &[&q_var], &q_body);
            let lambda = B::lambda(&ctx, &[&q_var], &B::dynamic_from_int(&ctx, &q_int));
            let _ = B::array_get_sort(&ctx, &lambda);
            B::bool_and(&ctx, &[&forall, &exists])
        } else {
            B::bool_const(&ctx, true)
        };

        let func = B::func_decl_new(&ctx, "backend_surface_func", &[&int_sort], &bool_sort);
        let applied = B::func_decl_apply(&ctx, &func, &[&B::dynamic_from_int(&ctx, &one)]);
        assert_eq!(B::func_decl_name(&ctx, &func), "backend_surface_func");
        let _ = B::dynamic_as_bool(&ctx, &applied);

        let dt = B::datatype_builder_finish(
            &ctx,
            B::datatype_builder_variant(
                &ctx,
                B::datatype_builder_new(&ctx, "BackendSurfaceOption"),
                "None",
                vec![],
            ),
        );
        let _ = format!("{dt:?}");

        let mut params = B::params_new();
        B::params_set_bool(&mut params, "model", true);
        B::params_set_u32(&mut params, "timeout", 10);
        B::params_set_symbol(&mut params, "engine", "default");
        let _ = format!("{params:?}");

        let _ = (
            bool_formula,
            int_formula,
            real_formula,
            dyn_formula,
            array_formula,
            quantifier_formula,
        );

        solver.assert(B::bool_and(
            &ctx,
            &[
                &B::bool_eq(&ctx, &b, &t),
                &B::int_eq(&ctx, &x, &B::int_lit(&ctx, 6)),
            ],
        ));
        assert_eq!(solver.check(), SatResult::Sat);
        let model = solver.get_model().expect("sat model");
        assert_eq!(B::model_eval_bool(&model, &b), Some(true));
        assert_eq!(B::model_eval_int(&model, &x), Some(6));
        assert!(B::model_eval_dynamic(&model, &dx).is_some());
    }

    #[test]
    fn sat_result_eq() {
        assert_eq!(SatResult::Sat, SatResult::Sat);
        assert_eq!(SatResult::Unsat, SatResult::Unsat);
        assert_ne!(SatResult::Sat, SatResult::Unsat);
    }

    #[test]
    fn backend_surface_exercises_z3_and_cvc5_paths() {
        assert_eq!(Z3Backend::family(), SolverFamily::Z3);
        assert_eq!(Cvc5Backend::family(), SolverFamily::Cvc5);
        assert!(Cvc5Backend::capabilities().native_sequences);
        assert!(format!("{:?}", Z3Backend::solver_new(&())).contains("Z3Backend"));
        let cvc5_ctx = Cvc5Backend::context_new();
        assert!(format!("{cvc5_ctx:?}").contains("Cvc5Context"));
        assert!(format!("{:?}", Cvc5Backend::solver_new(&cvc5_ctx)).contains("Cvc5Backend"));

        exercise_backend_surface::<Z3Backend>();
        exercise_backend_surface::<Cvc5Backend>();
    }

    #[test]
    fn z3_check_with_limits_accepts_explicit_timeout() {
        let solver = AbideSolver::<Z3Backend>::new();
        solver.assert(Z3Backend::bool_const(&(), true));

        assert_eq!(
            solver.check_with_limits(SolverLimits::from_timeout_ms(1_000)),
            SatResult::Sat
        );
    }

    #[test]
    fn z3_chc_timeout_limit_returns_typed_result() {
        let chc = r#"
            (declare-rel Reach (Int))
            (declare-rel Error ())
            (declare-var x Int)
            (rule (Reach 0) base)
            (rule (=> (and (Reach x) (< x 5)) (Reach (+ x 1))) step)
            (rule (=> (and (Reach x) (< x 0)) Error) err)
        "#;

        let result = z3_check_chc(chc, "Error", 1_000);
        assert!(matches!(result, ChcResult::Proved), "got: {result:?}");
    }

    #[test]
    fn z3_backend_bool_const() {
        let ctx = Z3Backend::context_new();
        let t = Z3Backend::bool_const(&ctx, true);
        let f = Z3Backend::bool_const(&ctx, false);
        let solver = AbideSolver::<Z3Backend>::new();
        // true is satisfiable
        solver.assert(&t);
        assert_eq!(solver.check(), SatResult::Sat);
        // true AND false is unsatisfiable
        solver.assert(&f);
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn z3_capabilities_match_current_backend_shape() {
        let caps = Z3Backend::capabilities();
        assert!(caps.arrays);
        assert!(caps.datatypes);
        assert!(caps.quantifiers);
        assert!(caps.models);
        assert!(caps.incremental);
        assert!(caps.chc);
        assert!(!caps.native_sequences);
        assert!(!caps.native_bags);
    }

    #[test]
    fn backend_score_prefers_native_bags_when_requested() {
        let z3 = Z3Backend::capabilities();
        let cvc5_like = SolverCapabilities {
            native_bags: true,
            native_sequences: true,
            unsat_cores: true,
            chc: false,
            ..z3
        };

        let req = BackendRequirements {
            bags: true,
            ..BackendRequirements::default()
        };

        assert!(
            backend_score(
                SolverFamily::Cvc5,
                cvc5_like,
                VerificationTask::Property,
                req
            ) > backend_score(SolverFamily::Z3, z3, VerificationTask::Property, req)
        );
    }

    #[test]
    fn backend_score_keeps_chc_on_z3_by_default() {
        let z3 = Z3Backend::capabilities();
        let cvc5_like = SolverCapabilities { chc: true, ..z3 };

        let req = BackendRequirements::for_task(VerificationTask::Chc);

        assert!(
            backend_score(SolverFamily::Z3, z3, VerificationTask::Chc, req)
                > backend_score(SolverFamily::Cvc5, cvc5_like, VerificationTask::Chc, req)
        );
    }

    #[test]
    fn cvc5_backend_context_reuses_term_manager() {
        let a = Cvc5Backend::context_new();
        let b = Cvc5Backend::context_new();
        let x = Cvc5Backend::int_var(&a, "x");
        let y = Cvc5Backend::int_var(&b, "y");
        let sum = Cvc5Backend::int_add(&a, &[&x, &y]);
        assert!(sum.sort().is_integer());
    }

    #[test]
    fn cvc5_backend_basic_sat() {
        let ctx = Cvc5Backend::context_new();
        let x = Cvc5Backend::int_var(&ctx, "x");
        let zero = Cvc5Backend::int_lit(&ctx, 0);
        let gt = Cvc5Backend::int_gt(&ctx, &x, &zero);
        let solver = AbideSolver::<Cvc5Backend>::new();
        solver.assert(&gt);
        assert_eq!(solver.check(), SatResult::Sat);
    }

    #[test]
    fn z3_backend_int_lit() {
        let ctx = Z3Backend::context_new();
        let five = Z3Backend::int_lit(&ctx, 5);
        let three = Z3Backend::int_lit(&ctx, 3);
        let sum = Z3Backend::int_add(&ctx, &[&five, &three]);
        let eight = Z3Backend::int_lit(&ctx, 8);
        let eq = Z3Backend::int_eq(&ctx, &sum, &eight);
        let solver = AbideSolver::<Z3Backend>::new();
        solver.assert(&eq);
        assert_eq!(solver.check(), SatResult::Sat);
    }

    #[test]
    fn z3_backend_push_pop() {
        let ctx = Z3Backend::context_new();
        let solver = AbideSolver::<Z3Backend>::new();
        let x = Z3Backend::bool_var(&ctx, "x");
        solver.assert(&x);
        assert_eq!(solver.check(), SatResult::Sat);

        solver.push();
        solver.assert(Z3Backend::bool_not(&ctx, &x));
        assert_eq!(solver.check(), SatResult::Unsat);
        solver.pop();

        // After pop, only x is asserted — should be SAT again
        assert_eq!(solver.check(), SatResult::Sat);
    }

    #[test]
    fn runtime_backend_defaults_to_z3() {
        set_active_solver_family(SolverFamily::Z3).unwrap();
        let solver = AbideSolver::<RuntimeBackend>::new();
        assert_eq!(solver.family(), SolverFamily::Z3);
    }

    #[test]
    fn runtime_backend_can_switch_to_cvc5() {
        set_active_solver_family(SolverFamily::Cvc5).unwrap();
        let ctx = RuntimeBackend::context_new();
        let gt = RuntimeBackend::int_gt(
            &ctx,
            &RuntimeBackend::int_lit(&ctx, 4),
            &RuntimeBackend::int_lit(&ctx, 3),
        );
        let solver = AbideSolver::<RuntimeBackend>::new();
        assert_eq!(solver.family(), SolverFamily::Cvc5);
        solver.assert(&gt);
        assert_eq!(solver.check(), SatResult::Sat);
        set_active_solver_family(SolverFamily::Z3).unwrap();
    }

    #[test]
    fn z3_backend_quantifier() {
        // forall x: Int. x >= 0 OR x < 0 (tautology)
        let ctx = Z3Backend::context_new();
        let x = Z3Backend::dynamic_from_int(&ctx, &Z3Backend::int_var(&ctx, "x"));
        let x_int = Z3Backend::dynamic_as_int(&ctx, &x).unwrap();
        let zero = Z3Backend::int_lit(&ctx, 0);
        let ge = Z3Backend::int_ge(&ctx, &x_int, &zero);
        let lt = Z3Backend::int_lt(&ctx, &x_int, &zero);
        let body = Z3Backend::bool_or(&ctx, &[&ge, &lt]);
        let q = Z3Backend::forall(&ctx, &[&x], &body);

        let solver = AbideSolver::<Z3Backend>::new();
        // Assert the negation — should be UNSAT (the forall is a tautology)
        solver.assert(Z3Backend::bool_not(&ctx, &q));
        assert_eq!(solver.check(), SatResult::Unsat);
    }
}
