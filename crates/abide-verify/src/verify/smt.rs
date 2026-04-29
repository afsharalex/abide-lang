//! SMT solver facade — the single point of backend contact for the verify module.
//!
//! Every other file in verify/ imports solver types from here, never from `z3::`
//! directly. All operations dispatch through the `SolverBackend` trait
//! (implemented by `Z3Backend` in `solver.rs`), ensuring a future backend swap
//! only touches solver.rs.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use super::solver::{self, ActiveBackend, SolverBackend, SolverFamily};

// ── Type re-exports from solver ─────────────────────────────────────
// All solver types used by verify/ are re-exported here so no other file
// needs `use z3::` or `use super::solver::` directly.

// AST types used pervasively as value types throughout verify/
pub use super::solver::{Array, Bool, Dynamic, Int, Real};

// Sort, function declarations, solver parameters
pub use super::solver::{FuncDecl, Params, Sort};

// Model for counterexample extraction
pub use super::solver::Model;

// ADT construction (used by context.rs)
pub use super::solver::{DatatypeAccessor, DatatypeBuilder, DatatypeSort};

// CHC solving result type (used by ic3.rs)
pub use super::solver::ChcResult;

// Ast trait (needed by downstream files for trait method access)
pub use super::solver::Ast;

// Solver-independent result type and solver wrapper
pub use super::solver::{SatResult, SolverLimits};

/// Concrete solver wrapper (always uses the active backend from solver.rs).
pub type AbideSolver = solver::AbideSolver<ActiveBackend>;

use crate::ir::types::IRType;

/// Shorthand for the active backend to reduce verbosity.
type AB = ActiveBackend;

thread_local! {
    static ACTIVE_BACKEND_CONTEXT: RefCell<Option<(SolverFamily, <AB as SolverBackend>::Context)>> =
        const { RefCell::new(None) };
    static MAP_OPTION_SORT_CACHE: RefCell<HashMap<(SolverFamily, String), Rc<DatatypeSort>>> =
        RefCell::new(HashMap::new());
    static SEQ_SORT_CACHE: RefCell<HashMap<(SolverFamily, String), Rc<DatatypeSort>>> =
        RefCell::new(HashMap::new());
}

fn with_backend_context<R>(f: impl FnOnce(&<AB as SolverBackend>::Context) -> R) -> R {
    ACTIVE_BACKEND_CONTEXT.with(|cell| {
        let family = AB::family();
        let needs_refresh = {
            let borrow = cell.borrow();
            !matches!(borrow.as_ref(), Some((current, _)) if *current == family)
        };
        if needs_refresh {
            *cell.borrow_mut() = Some((family, AB::context_new()));
        }
        let borrow = cell.borrow();
        let (_, ctx) = borrow.as_ref().expect("backend context initialized");
        f(ctx)
    })
}

macro_rules! backend {
    ($method:ident $(, $arg:expr )* $(,)?) => {
        with_backend_context(|ctx| AB::$method(ctx $(, $arg )*))
    };
}

// ── Backend-neutral AST helper traits ───────────────────────────────

/// Backend-neutral boolean AST operations.
///
/// Verify/ code previously relied on Z3 inherent methods like
/// `Bool::from_bool`, `Bool::new_const`, `b.not()`, and `b.implies(c)`.
/// These traits keep the call-site ergonomics while routing through
/// the active backend instead of assuming Z3-specific APIs.
pub trait BoolAstExt: Sized {
    fn from_bool(val: bool) -> Self;
    fn new_const<S: AsRef<str>>(name: S) -> Self;
    fn and(args: &[&Self]) -> Self;
    fn or(args: &[&Self]) -> Self;
    fn xor(a: &Self, b: &Self) -> Self;
    fn not(&self) -> Self;
    fn implies(&self, rhs: &Self) -> Self;
    fn eq(&self, rhs: Self) -> Self;
}

impl BoolAstExt for Bool {
    fn from_bool(val: bool) -> Self {
        backend!(bool_const, val)
    }

    fn new_const<S: AsRef<str>>(name: S) -> Self {
        backend!(bool_var, name.as_ref())
    }

    fn and(args: &[&Self]) -> Self {
        backend!(bool_and, args)
    }

    fn or(args: &[&Self]) -> Self {
        backend!(bool_or, args)
    }

    fn xor(a: &Self, b: &Self) -> Self {
        backend!(bool_xor, a, b)
    }

    fn not(&self) -> Self {
        backend!(bool_not, self)
    }

    fn implies(&self, rhs: &Self) -> Self {
        backend!(bool_implies, self, rhs)
    }

    fn eq(&self, rhs: Self) -> Self {
        backend!(bool_eq, self, &rhs)
    }
}

/// Backend-neutral integer AST operations.
pub trait IntAstExt: Sized {
    fn from_i64(val: i64) -> Self;
    fn new_const<S: AsRef<str>>(name: S) -> Self;
    fn eq(&self, rhs: Self) -> Bool;
    fn lt(&self, rhs: Self) -> Bool;
    fn le(&self, rhs: Self) -> Bool;
    fn gt(&self, rhs: Self) -> Bool;
    fn ge(&self, rhs: Self) -> Bool;
}

impl IntAstExt for Int {
    fn from_i64(val: i64) -> Self {
        backend!(int_lit, val)
    }

    fn new_const<S: AsRef<str>>(name: S) -> Self {
        backend!(int_var, name.as_ref())
    }

    fn eq(&self, rhs: Self) -> Bool {
        backend!(int_eq, self, &rhs)
    }

    fn lt(&self, rhs: Self) -> Bool {
        backend!(int_lt, self, &rhs)
    }

    fn le(&self, rhs: Self) -> Bool {
        backend!(int_le, self, &rhs)
    }

    fn gt(&self, rhs: Self) -> Bool {
        backend!(int_gt, self, &rhs)
    }

    fn ge(&self, rhs: Self) -> Bool {
        backend!(int_ge, self, &rhs)
    }
}

/// Backend-neutral real AST comparison operations.
pub trait RealAstExt: Sized {
    fn eq(&self, rhs: Self) -> Bool;
    fn lt(&self, rhs: Self) -> Bool;
    fn le(&self, rhs: Self) -> Bool;
    fn gt(&self, rhs: Self) -> Bool;
    fn ge(&self, rhs: Self) -> Bool;
}

impl RealAstExt for Real {
    fn eq(&self, rhs: Self) -> Bool {
        backend!(real_eq, self, &rhs)
    }

    fn lt(&self, rhs: Self) -> Bool {
        backend!(real_lt, self, &rhs)
    }

    fn le(&self, rhs: Self) -> Bool {
        backend!(real_le, self, &rhs)
    }

    fn gt(&self, rhs: Self) -> Bool {
        backend!(real_gt, self, &rhs)
    }

    fn ge(&self, rhs: Self) -> Bool {
        backend!(real_ge, self, &rhs)
    }
}

/// Backend-neutral sort constructors.
pub trait SortExt: Sized {
    fn int() -> Self;
    fn bool() -> Self;
    fn real() -> Self;
}

impl SortExt for Sort {
    fn int() -> Self {
        backend!(int_sort)
    }

    fn bool() -> Self {
        backend!(bool_sort)
    }

    fn real() -> Self {
        backend!(real_sort)
    }
}

/// Backend-neutral function declaration helpers.
pub trait FuncDeclExt {
    fn name(&self) -> String;
}

impl FuncDeclExt for FuncDecl {
    fn name(&self) -> String {
        backend!(func_decl_name, self)
    }
}

// ── Boolean combinators ─────────────────────────────────────────────

/// Conjunction of boolean expressions.
pub fn bool_and(args: &[&Bool]) -> Bool {
    backend!(bool_and, args)
}

/// Disjunction of boolean expressions.
pub fn bool_or(args: &[&Bool]) -> Bool {
    backend!(bool_or, args)
}

/// Negation.
pub fn bool_not(b: &Bool) -> Bool {
    backend!(bool_not, b)
}

/// Implication: a => b.
pub fn bool_implies(a: &Bool, b: &Bool) -> Bool {
    backend!(bool_implies, a, b)
}

/// Boolean constant (true/false).
pub fn bool_const(val: bool) -> Bool {
    backend!(bool_const, val)
}

/// Named boolean variable.
pub fn bool_named(name: &str) -> Bool {
    backend!(bool_var, name)
}

/// Exclusive or.
pub fn bool_xor(a: &Bool, b: &Bool) -> Bool {
    backend!(bool_xor, a, b)
}

/// Backend-neutral boolean if-then-else.
pub fn bool_ite(cond: &Bool, then_val: &Bool, else_val: &Bool) -> Bool {
    backend!(bool_ite, cond, then_val, else_val)
}

/// Backend-neutral boolean equality.
pub fn bool_eq(a: &Bool, b: &Bool) -> Bool {
    backend!(bool_eq, a, b)
}

// ── Integer helpers ─────────────────────────────────────────────────

/// Integer literal.
pub fn int_lit(n: i64) -> Int {
    backend!(int_lit, n)
}

/// Named integer variable.
pub fn int_const(name: &str) -> Int {
    backend!(int_var, name)
}

/// Named integer variable (AST-level helper).
pub fn int_named(name: &str) -> Int {
    backend!(int_var, name)
}

/// Sum of integer expressions.
pub fn int_add(args: &[&Int]) -> Int {
    backend!(int_add, args)
}

/// Difference of integer expressions.
pub fn int_sub(args: &[&Int]) -> Int {
    backend!(int_sub, args)
}

/// Backend-neutral integer if-then-else.
pub fn int_ite(cond: &Bool, then_val: &Int, else_val: &Int) -> Int {
    backend!(int_ite, cond, then_val, else_val)
}

/// Backend-neutral integer equality.
pub fn int_eq(a: &Int, b: &Int) -> Bool {
    backend!(int_eq, a, b)
}

/// Backend-neutral integer less-than.
pub fn int_lt(a: &Int, b: &Int) -> Bool {
    backend!(int_lt, a, b)
}

/// Backend-neutral integer less-than-or-equal.
pub fn int_le(a: &Int, b: &Int) -> Bool {
    backend!(int_le, a, b)
}

/// Backend-neutral integer greater-than.
pub fn int_gt(a: &Int, b: &Int) -> Bool {
    backend!(int_gt, a, b)
}

/// Backend-neutral integer greater-than-or-equal.
pub fn int_ge(a: &Int, b: &Int) -> Bool {
    backend!(int_ge, a, b)
}

/// Backend-neutral real if-then-else.
pub fn real_ite(cond: &Bool, then_val: &Real, else_val: &Real) -> Real {
    backend!(real_ite, cond, then_val, else_val)
}

/// Backend-neutral real equality.
pub fn real_eq(a: &Real, b: &Real) -> Bool {
    backend!(real_eq, a, b)
}

/// Backend-neutral real less-than.
pub fn real_lt(a: &Real, b: &Real) -> Bool {
    backend!(real_lt, a, b)
}

/// Backend-neutral real less-than-or-equal.
pub fn real_le(a: &Real, b: &Real) -> Bool {
    backend!(real_le, a, b)
}

/// Backend-neutral real greater-than.
pub fn real_gt(a: &Real, b: &Real) -> Bool {
    backend!(real_gt, a, b)
}

/// Backend-neutral real greater-than-or-equal.
pub fn real_ge(a: &Real, b: &Real) -> Bool {
    backend!(real_ge, a, b)
}

// ── Quantifiers ─────────────────────────────────────────────────────

/// Universal quantifier: forall bound. body.
pub fn forall(bound: &[&Dynamic], body: &Bool) -> Bool {
    backend!(forall, bound, body)
}

/// Existential quantifier: exists bound. body.
pub fn exists(bound: &[&Dynamic], body: &Bool) -> Bool {
    backend!(exists, bound, body)
}

/// Lambda array: lambda bound. body.
pub fn lambda(bound: &[&Dynamic], body: &Dynamic) -> Array {
    backend!(lambda, bound, body)
}

// ── Dynamic/ADT helpers ─────────────────────────────────────────────

/// Create a fresh Dynamic constant with a unique name.
pub fn dynamic_fresh(prefix: &str, sort: &Sort) -> Dynamic {
    backend!(dynamic_fresh, prefix, sort)
}

/// Integer sort helper.
pub fn sort_int() -> Sort {
    backend!(int_sort)
}

/// Boolean sort helper.
pub fn sort_bool() -> Sort {
    backend!(bool_sort)
}

/// Real sort helper.
pub fn sort_real() -> Sort {
    backend!(real_sort)
}

/// Create a named Dynamic constant.
pub fn dynamic_const(name: &str, sort: &Sort) -> Dynamic {
    backend!(dynamic_const, name, sort)
}

/// Wrap a Bool as Dynamic.
pub fn bool_to_dynamic(b: &Bool) -> Dynamic {
    backend!(dynamic_from_bool, b)
}

/// Wrap an Int as Dynamic.
pub fn int_to_dynamic(i: &Int) -> Dynamic {
    backend!(dynamic_from_int, i)
}

/// Wrap a Real as Dynamic.
pub fn real_to_dynamic(r: &Real) -> Dynamic {
    backend!(dynamic_from_real, r)
}

/// Wrap an Array as Dynamic.
pub fn array_to_dynamic(a: &Array) -> Dynamic {
    backend!(dynamic_from_array, a)
}

/// Create a constant array (all elements have the same value).
pub fn const_array(domain: &Sort, default: &Dynamic) -> Array {
    backend!(array_const_array, domain, default)
}

/// Backend-neutral array if-then-else.
pub fn array_ite(cond: &Bool, then_val: &Array, else_val: &Array) -> Array {
    backend!(array_ite, cond, then_val, else_val)
}

/// Backend-neutral dynamic if-then-else.
pub fn dynamic_ite(cond: &Bool, then_val: &Dynamic, else_val: &Dynamic) -> Dynamic {
    backend!(dynamic_ite, cond, then_val, else_val)
}

/// Backend-neutral dynamic equality.
pub fn dynamic_eq(a: &Dynamic, b: &Dynamic) -> Bool {
    backend!(dynamic_eq, a, b)
}

/// Attempt to view a dynamic term as Bool.
pub fn dynamic_as_bool(d: &Dynamic) -> Option<Bool> {
    backend!(dynamic_as_bool, d)
}

/// Attempt to view a dynamic term as Int.
pub fn dynamic_as_int(d: &Dynamic) -> Option<Int> {
    backend!(dynamic_as_int, d)
}

/// Attempt to view a dynamic term as Real.
pub fn dynamic_as_real(d: &Dynamic) -> Option<Real> {
    backend!(dynamic_as_real, d)
}

/// Attempt to view a dynamic term as Array.
pub fn dynamic_as_array(d: &Dynamic) -> Option<Array> {
    backend!(dynamic_as_array, d)
}

/// Return the sort of a dynamic term.
pub fn dynamic_sort(d: &Dynamic) -> Sort {
    backend!(dynamic_get_sort, d)
}

/// Return a backend-neutral string name for a sort.
pub fn sort_name(s: &Sort) -> String {
    backend!(sort_to_string, s)
}

/// Backend-neutral array equality.
pub fn array_eq(a: &Array, b: &Array) -> Bool {
    backend!(array_eq, a, b.clone())
}

/// Create a new function declaration.
pub fn func_decl(name: &str, domain: &[&Sort], range: &Sort) -> FuncDecl {
    backend!(func_decl_new, name, domain, range)
}

/// Return the backend-neutral display name for a function declaration.
pub fn func_decl_name(f: &FuncDecl) -> String {
    backend!(func_decl_name, f)
}

/// Apply a function declaration to dynamic arguments.
pub fn func_decl_apply(f: &FuncDecl, args: &[&Dynamic]) -> Dynamic {
    backend!(func_decl_apply, f, args)
}

/// Create a datatype builder.
pub fn datatype_builder(name: &str) -> DatatypeBuilder {
    backend!(datatype_builder_new, name)
}

/// Add a variant to a datatype builder.
pub fn datatype_builder_variant(
    builder: DatatypeBuilder,
    name: &str,
    fields: Vec<(&str, DatatypeAccessor)>,
) -> DatatypeBuilder {
    backend!(datatype_builder_variant, builder, name, fields)
}

/// Finish a datatype builder.
pub fn datatype_builder_finish(builder: DatatypeBuilder) -> DatatypeSort {
    backend!(datatype_builder_finish, builder)
}

/// Construct a datatype field accessor from a sort.
pub fn datatype_accessor_sort(sort: Sort) -> DatatypeAccessor {
    backend!(datatype_accessor_sort, sort)
}

fn stable_hash_hex(s: &str) -> String {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    s.hash(&mut hasher);
    format!("{:016x}", hasher.finish())
}

pub fn map_option_sort(value_ty: &IRType) -> Rc<DatatypeSort> {
    let family = AB::family();
    let key = format!("{value_ty:?}");
    MAP_OPTION_SORT_CACHE.with(|cache| {
        if let Some(found) = cache.borrow().get(&(family, key.clone())) {
            return Rc::clone(found);
        }

        let name = format!("MapValOption_{}", stable_hash_hex(&key));
        let builder = datatype_builder_variant(datatype_builder(&name), "None", vec![]);
        let builder = datatype_builder_variant(
            builder,
            "Some",
            vec![("value", datatype_accessor_sort(ir_type_to_sort(value_ty)))],
        );
        let sort = Rc::new(datatype_builder_finish(builder));
        cache.borrow_mut().insert((family, key), Rc::clone(&sort));
        sort
    })
}

pub fn seq_sort(element_ty: &IRType) -> Rc<DatatypeSort> {
    let family = AB::family();
    let key = format!("{element_ty:?}");
    SEQ_SORT_CACHE.with(|cache| {
        if let Some(found) = cache.borrow().get(&(family, key.clone())) {
            return Rc::clone(found);
        }

        let name = format!("SeqVal_{}", stable_hash_hex(&key));
        let builder = datatype_builder_variant(
            datatype_builder(&name),
            "Seq",
            vec![
                ("len", datatype_accessor_sort(sort_int())),
                (
                    "data",
                    datatype_accessor_sort(backend!(
                        array_sort,
                        &sort_int(),
                        &ir_type_to_sort(element_ty)
                    )),
                ),
            ],
        );
        let sort = Rc::new(datatype_builder_finish(builder));
        cache.borrow_mut().insert((family, key), Rc::clone(&sort));
        sort
    })
}

// ── Z3 value wrapper ────────────────────────────────────────────────

/// An SMT AST value — wraps the concrete sort variants.
///
/// All Abide expressions compile down to one of these.
#[derive(Debug, Clone)]
pub enum SmtValue {
    /// Int sort — used for int, identity, enum variants (encoded as sequential IDs).
    Int(Int),
    /// Bool sort — direct mapping from Abide Bool.
    Bool(Bool),
    /// Real sort — used for Abide Real type (exact rational).
    Real(Real),
    /// Array sort — used for `Map<K,V>` (store/select), `Set<T>` (characteristic function).
    Array(Array),
    /// Uninterpreted/dynamic sort — used for complex types and array select results.
    Dynamic(Dynamic),
    /// Uninterpreted function — used for lambda encodings.
    /// The function has a definitional axiom asserted on the solver.
    /// Carries (`FuncDecl`, `param_sorts`, `range_sort`) for partial application.
    /// Wrapped in Rc because `FuncDecl` does not implement Clone.
    Func(std::rc::Rc<(FuncDecl, Vec<Sort>, Sort)>),
}

impl SmtValue {
    /// Extract as Bool. Returns error if wrong variant.
    pub fn as_bool(&self) -> Result<&Bool, String> {
        match self {
            SmtValue::Bool(b) => Ok(b),
            other => Err(format!("type error: expected Bool, got {other:?}")),
        }
    }

    /// Extract as Int. Returns error if wrong variant.
    pub fn as_int(&self) -> Result<&Int, String> {
        match self {
            SmtValue::Int(i) => Ok(i),
            other => Err(format!("type error: expected Int, got {other:?}")),
        }
    }

    /// Extract as Real. Returns error if wrong variant.
    pub fn as_real(&self) -> Result<&Real, String> {
        match self {
            SmtValue::Real(r) => Ok(r),
            other => Err(format!("type error: expected Real, got {other:?}")),
        }
    }

    /// Extract as Array. Returns error if wrong variant.
    pub fn as_array(&self) -> Result<&Array, String> {
        match self {
            SmtValue::Array(a) => Ok(a),
            other => Err(format!("type error: expected Array, got {other:?}")),
        }
    }

    /// Extract the underlying AST as Dynamic (works for any variant).
    pub fn to_dynamic(&self) -> Dynamic {
        match self {
            SmtValue::Int(i) => backend!(dynamic_from_int, i),
            SmtValue::Bool(b) => backend!(dynamic_from_bool, b),
            SmtValue::Real(r) => backend!(dynamic_from_real, r),
            SmtValue::Array(a) => backend!(dynamic_from_array, a),
            SmtValue::Dynamic(d) => d.clone(),
            SmtValue::Func(f) => {
                // A function value as Dynamic: create a nullary application
                // (this is a fallback — Func values are normally applied, not coerced)
                backend!(func_decl_apply, &f.0, &[])
            }
        }
    }

    /// Convert to a Bool (for use in assertions).
    /// Int -> Bool via (int != 0), Bool -> Bool, Dynamic -> Bool (sort cast).
    pub fn to_bool(&self) -> Result<Bool, String> {
        match self {
            SmtValue::Bool(b) => Ok(b.clone()),
            SmtValue::Int(i) => {
                let zero = backend!(int_lit, 0);
                Ok(backend!(bool_not, &backend!(int_eq, i, &zero)))
            }
            SmtValue::Dynamic(d) => backend!(dynamic_as_bool, d)
                .ok_or_else(|| format!("type error: cannot convert Dynamic to Bool: {d:?}")),
            other => Err(format!("type error: cannot convert {other:?} to Bool")),
        }
    }
}

fn int_like_dynamic_to_smt_value(d: Dynamic) -> SmtValue {
    if let Some(i) = dynamic_as_int(&d) {
        SmtValue::Int(i)
    } else {
        SmtValue::Dynamic(d)
    }
}

pub fn dynamic_to_typed_value(d: Dynamic, ty: &IRType) -> SmtValue {
    match ty {
        IRType::Bool => dynamic_as_bool(&d).map_or(SmtValue::Dynamic(d), SmtValue::Bool),
        IRType::Int
        | IRType::Identity
        | IRType::String
        | IRType::Enum { .. }
        | IRType::Entity { .. }
        | IRType::Fn { .. }
        | IRType::Record { .. }
        | IRType::Tuple { .. } => int_like_dynamic_to_smt_value(d),
        IRType::Real | IRType::Float => {
            dynamic_as_real(&d).map_or(SmtValue::Dynamic(d), SmtValue::Real)
        }
        IRType::Set { .. } | IRType::Map { .. } => {
            dynamic_as_array(&d).map_or(SmtValue::Dynamic(d), SmtValue::Array)
        }
        IRType::Seq { .. } => SmtValue::Dynamic(d),
        IRType::Refinement { base, .. } => dynamic_to_typed_value(d, base),
    }
}

pub fn map_none_dynamic(value_ty: &IRType) -> Dynamic {
    let option = map_option_sort(value_ty);
    func_decl_apply(&option.variants[0].constructor, &[])
}

pub fn map_some_dynamic(value_ty: &IRType, value: &SmtValue) -> Dynamic {
    let option = map_option_sort(value_ty);
    let payload = value.to_dynamic();
    func_decl_apply(&option.variants[1].constructor, &[&payload])
}

pub fn map_is_some(value_ty: &IRType, opt: &Dynamic) -> Bool {
    let option = map_option_sort(value_ty);
    dynamic_as_bool(&func_decl_apply(&option.variants[1].tester, &[opt]))
        .expect("map option tester must return Bool")
}

pub fn map_unwrap_or_default(value_ty: &IRType, opt: &Dynamic) -> SmtValue {
    let option = map_option_sort(value_ty);
    let some_guard = map_is_some(value_ty, opt);
    let payload = func_decl_apply(&option.variants[1].accessors[0], &[opt]);
    let then_val = dynamic_to_typed_value(payload, value_ty);
    let else_val = dynamic_to_typed_value(default_dynamic(value_ty), value_ty);
    smt_ite(&some_guard, &then_val, &else_val)
}

pub fn map_lookup(map: &SmtValue, key: &SmtValue, value_ty: &IRType) -> Result<SmtValue, String> {
    let opt = map.as_array()?.select(&key.to_dynamic());
    Ok(map_unwrap_or_default(value_ty, &opt))
}

pub fn map_store(
    map: &SmtValue,
    key: &SmtValue,
    value: &SmtValue,
    value_ty: &IRType,
) -> Result<SmtValue, String> {
    let stored = map
        .as_array()?
        .store(&key.to_dynamic(), &map_some_dynamic(value_ty, value));
    Ok(SmtValue::Array(stored))
}

pub fn map_has(map: &SmtValue, key: &SmtValue, value_ty: &IRType) -> Result<SmtValue, String> {
    let opt = map.as_array()?.select(&key.to_dynamic());
    Ok(SmtValue::Bool(map_is_some(value_ty, &opt)))
}

pub fn map_domain(map: &SmtValue, key_ty: &IRType, value_ty: &IRType) -> Result<SmtValue, String> {
    let arr = map.as_array()?;
    let key_sort = ir_type_to_sort(key_ty);
    let key = dynamic_fresh("md", &key_sort);
    let body = bool_to_dynamic(&map_is_some(value_ty, &arr.select(&key)));
    Ok(SmtValue::Array(lambda(&[&key], &body)))
}

pub fn map_merge(
    left: &SmtValue,
    right: &SmtValue,
    key_ty: &IRType,
    value_ty: &IRType,
) -> Result<SmtValue, String> {
    let left_arr = left.as_array()?;
    let right_arr = right.as_array()?;
    let key_sort = ir_type_to_sort(key_ty);
    let key = dynamic_fresh("mm", &key_sort);
    let left_opt = left_arr.select(&key);
    let right_opt = right_arr.select(&key);
    let body = dynamic_ite(&map_is_some(value_ty, &right_opt), &right_opt, &left_opt);
    Ok(SmtValue::Array(lambda(&[&key], &body)))
}

pub fn map_range(map: &SmtValue, key_ty: &IRType, value_ty: &IRType) -> Result<SmtValue, String> {
    let arr = map.as_array()?;
    let key_sort = ir_type_to_sort(key_ty);
    let value_sort = ir_type_to_sort(value_ty);
    let value = dynamic_fresh("mr", &value_sort);
    let key = dynamic_fresh("mk", &key_sort);
    let opt = arr.select(&key);
    let present = map_is_some(value_ty, &opt);
    let candidate = map_unwrap_or_default(value_ty, &opt);
    let value_expr = dynamic_to_typed_value(value.clone(), value_ty);
    let matches = smt_eq(&candidate, &value_expr)?;
    let witness = exists(&[&key], &bool_and(&[&present, &matches]));
    Ok(SmtValue::Array(lambda(
        &[&value],
        &bool_to_dynamic(&witness),
    )))
}

fn seq_dynamic(value: &SmtValue) -> Result<Dynamic, String> {
    match value {
        SmtValue::Dynamic(d) => Ok(d.clone()),
        other => Err(format!(
            "type error: expected Seq dynamic value, got {other:?}"
        )),
    }
}

pub fn seq_make(element_ty: &IRType, len: &Int, data: &Array) -> SmtValue {
    let sort = seq_sort(element_ty);
    let len_dyn = int_to_dynamic(len);
    let data_dyn = array_to_dynamic(data);
    SmtValue::Dynamic(func_decl_apply(
        &sort.variants[0].constructor,
        &[&len_dyn, &data_dyn],
    ))
}

pub fn seq_length(value: &SmtValue, element_ty: &IRType) -> Result<SmtValue, String> {
    let seq = seq_dynamic(value)?;
    let sort = seq_sort(element_ty);
    Ok(SmtValue::Int(
        dynamic_as_int(&func_decl_apply(&sort.variants[0].accessors[0], &[&seq]))
            .expect("Seq len accessor must return Int"),
    ))
}

pub fn seq_data(value: &SmtValue, element_ty: &IRType) -> Result<Array, String> {
    let seq = seq_dynamic(value)?;
    let sort = seq_sort(element_ty);
    dynamic_as_array(&func_decl_apply(&sort.variants[0].accessors[1], &[&seq]))
        .ok_or_else(|| "Seq data accessor must return array".to_owned())
}

pub fn seq_literal(element_ty: &IRType, elements: &[SmtValue]) -> SmtValue {
    let default = default_dynamic(element_ty);
    let mut arr = const_array(&sort_int(), &default);
    for (i, elem) in elements.iter().enumerate() {
        let idx = int_to_dynamic(&int_lit(i as i64));
        arr = arr.store(&idx, &elem.to_dynamic());
    }
    seq_make(element_ty, &int_lit(elements.len() as i64), &arr)
}

pub fn seq_index(
    value: &SmtValue,
    key: &SmtValue,
    element_ty: &IRType,
) -> Result<SmtValue, String> {
    let data = seq_data(value, element_ty)?;
    Ok(dynamic_to_typed_value(
        data.select(&key.to_dynamic()),
        element_ty,
    ))
}

pub fn seq_head(value: &SmtValue, element_ty: &IRType) -> Result<SmtValue, String> {
    seq_index(value, &int_val(0), element_ty)
}

pub fn seq_tail(value: &SmtValue, element_ty: &IRType) -> Result<SmtValue, String> {
    let data = seq_data(value, element_ty)?;
    let len = seq_length(value, element_ty)?.as_int()?.clone();
    let idx = dynamic_fresh("st", &sort_int());
    let idx_int = dynamic_as_int(&idx).ok_or_else(|| "Seq::tail expected Int index".to_owned())?;
    let one = int_lit(1);
    let shifted = int_add(&[&idx_int, &one]);
    let body = data.select(&int_to_dynamic(&shifted));
    let tail_data = lambda(&[&idx], &body);
    let zero = int_lit(0);
    let new_len = int_ite(&int_gt(&len, &zero), &int_sub(&[&len, &one]), &zero);
    Ok(seq_make(element_ty, &new_len, &tail_data))
}

pub fn seq_concat(
    left: &SmtValue,
    right: &SmtValue,
    element_ty: &IRType,
) -> Result<SmtValue, String> {
    let left_data = seq_data(left, element_ty)?;
    let right_data = seq_data(right, element_ty)?;
    let left_len = seq_length(left, element_ty)?.as_int()?.clone();
    let right_len = seq_length(right, element_ty)?.as_int()?.clone();
    let idx = dynamic_fresh("sc", &sort_int());
    let idx_int =
        dynamic_as_int(&idx).ok_or_else(|| "Seq::concat expected Int index".to_owned())?;
    let in_left = int_lt(&idx_int, &left_len);
    let left_val = dynamic_to_typed_value(left_data.select(&idx), element_ty);
    let shifted = int_sub(&[&idx_int, &left_len]);
    let right_val =
        dynamic_to_typed_value(right_data.select(&int_to_dynamic(&shifted)), element_ty);
    let body = smt_ite(&in_left, &left_val, &right_val).to_dynamic();
    let concat_data = lambda(&[&idx], &body);
    let concat_len = int_add(&[&left_len, &right_len]);
    Ok(seq_make(element_ty, &concat_len, &concat_data))
}

// ── Sort mapping ────────────────────────────────────────────────────

/// Map an Abide IR type to a solver sort.
///
/// Enums are encoded as Int (variant IDs).
/// Records and entities are handled structurally (not as datatypes for now).
#[allow(clippy::match_same_arms)] // arms will diverge as encoding matures
pub fn ir_type_to_sort(ty: &IRType) -> Sort {
    match ty {
        IRType::Int | IRType::Identity => backend!(int_sort),
        IRType::Bool => backend!(bool_sort),
        IRType::Real | IRType::Float => backend!(real_sort),
        IRType::String => backend!(int_sort), // strings as uninterpreted ints for now
        IRType::Enum { .. } => backend!(int_sort), // enums encoded as sequential int IDs
        IRType::Entity { .. } => backend!(int_sort), // entity refs as slot indices
        IRType::Fn { .. } => backend!(int_sort), // functions as uninterpreted for now
        IRType::Record { .. } => backend!(int_sort), // records as uninterpreted for now
        IRType::Set { element } => {
            backend!(array_sort, &ir_type_to_sort(element), &backend!(bool_sort))
        }
        IRType::Seq { element } => seq_sort(element).sort(),
        IRType::Map { key, value } => {
            let option_sort = map_option_sort(value);
            backend!(array_sort, &ir_type_to_sort(key), &option_sort.sort)
        }
        IRType::Tuple { .. } => backend!(int_sort), // tuples as uninterpreted for now
        IRType::Refinement { base, .. } => ir_type_to_sort(base), // use base type sort
    }
}

// ── Literal construction ────────────────────────────────────────────

/// Create an Int constant from an i64 value.
pub fn int_val(v: i64) -> SmtValue {
    SmtValue::Int(backend!(int_lit, v))
}

/// Create a Bool constant.
pub fn bool_val(v: bool) -> SmtValue {
    SmtValue::Bool(backend!(bool_const, v))
}

/// Create a Real constant from numerator/denominator.
pub fn real_val(num: i64, den: i64) -> SmtValue {
    SmtValue::Real(backend!(real_val, num, den))
}

/// Create a named Int variable.
pub fn int_var(name: &str) -> SmtValue {
    SmtValue::Int(backend!(int_var, name))
}

/// Create a named Bool variable.
pub fn bool_var(name: &str) -> SmtValue {
    SmtValue::Bool(backend!(bool_var, name))
}

/// Create a named Real variable.
pub fn real_var(name: &str) -> SmtValue {
    SmtValue::Real(backend!(real_var, name))
}

/// Default value for a given IR type, returned as Dynamic.
/// Used for constant-array initialization in collection literal encoding.
/// Recurses for nested collections: `Map<K, Set<T>>` gets a const-array default.
pub fn default_dynamic(ty: &IRType) -> Dynamic {
    match ty {
        IRType::Bool => backend!(dynamic_from_bool, &backend!(bool_const, false)),
        IRType::Real | IRType::Float => backend!(dynamic_from_real, &backend!(real_val, 0, 1)),
        IRType::Map { key, value } => {
            let key_sort = ir_type_to_sort(key);
            let val_default = map_none_dynamic(value);
            backend!(
                dynamic_from_array,
                &backend!(array_const_array, &key_sort, &val_default)
            )
        }
        IRType::Set { element } => {
            let elem_sort = ir_type_to_sort(element);
            let false_val = backend!(dynamic_from_bool, &backend!(bool_const, false));
            backend!(
                dynamic_from_array,
                &backend!(array_const_array, &elem_sort, &false_val)
            )
        }
        IRType::Seq { element } => {
            let default = default_dynamic(element);
            let data = backend!(array_const_array, &backend!(int_sort), &default);
            seq_make(element, &backend!(int_lit, 0), &data).to_dynamic()
        }
        _ => backend!(dynamic_from_int, &backend!(int_lit, 0)),
    }
}

/// Create a named Array variable for a Map/Set/Seq field.
pub fn array_var(name: &str, ty: &IRType) -> Result<SmtValue, String> {
    let sort = ir_type_to_sort(ty);
    let domain = backend!(sort_array_domain, &sort)
        .ok_or_else(|| format!("type error: expected array sort for '{name}', got {ty:?}"))?;
    let range = backend!(sort_array_range, &sort)
        .ok_or_else(|| format!("type error: expected array sort for '{name}', got {ty:?}"))?;
    Ok(SmtValue::Array(backend!(
        array_new_const,
        name,
        &domain,
        &range
    )))
}

/// Assert that two `SmtValue`s are equal, returning a Bool constraint.
///
/// Handles same-variant pairs directly. For cross-variant pairs involving
/// Dynamic (e.g., `Array::select` result vs Int field), coerces the typed
/// operand to Dynamic and uses generic equality.
pub fn smt_eq(a: &SmtValue, b: &SmtValue) -> Result<Bool, String> {
    match (a, b) {
        (SmtValue::Int(x), SmtValue::Int(y)) => Ok(backend!(int_eq, x, y)),
        (SmtValue::Bool(x), SmtValue::Bool(y)) => Ok(backend!(bool_eq, x, y)),
        (SmtValue::Real(x), SmtValue::Real(y)) => Ok(backend!(real_eq, x, y)),
        (SmtValue::Array(x), SmtValue::Array(y)) => Ok(backend!(array_eq, x, y.clone())),
        (SmtValue::Dynamic(x), SmtValue::Dynamic(y)) => Ok(backend!(dynamic_eq, x, y)),
        // Cross-variant: coerce both to Dynamic for generic equality
        (SmtValue::Dynamic(d), other) | (other, SmtValue::Dynamic(d)) => {
            Ok(backend!(dynamic_eq, d, &other.to_dynamic()))
        }
        _ => Err(format!("sort mismatch in equality: {a:?} vs {b:?}")),
    }
}

/// Compare two `SmtValue`s for inequality: `a != b`.
pub fn smt_neq(a: &SmtValue, b: &SmtValue) -> Result<Bool, String> {
    let eq = smt_eq(a, b)?;
    Ok(backend!(bool_not, &eq))
}

/// Conditional select: `if cond then then_val else else_val`.
/// Both branches must have the same sort.
pub fn smt_ite(cond: &Bool, then_val: &SmtValue, else_val: &SmtValue) -> SmtValue {
    match (then_val, else_val) {
        (SmtValue::Int(t), SmtValue::Int(e)) => SmtValue::Int(backend!(int_ite, cond, t, e)),
        (SmtValue::Bool(t), SmtValue::Bool(e)) => SmtValue::Bool(backend!(bool_ite, cond, t, e)),
        (SmtValue::Real(t), SmtValue::Real(e)) => SmtValue::Real(backend!(real_ite, cond, t, e)),
        (SmtValue::Array(t), SmtValue::Array(e)) => {
            SmtValue::Array(backend!(array_ite, cond, t, e))
        }
        (SmtValue::Dynamic(t), SmtValue::Dynamic(e)) => {
            SmtValue::Dynamic(backend!(dynamic_ite, cond, t, e))
        }
        // Cross-variant: coerce to Dynamic
        _ => SmtValue::Dynamic(backend!(
            dynamic_ite,
            cond,
            &then_val.to_dynamic(),
            &else_val.to_dynamic(),
        )),
    }
}

// ── Binary operations ───────────────────────────────────────────────

/// Apply a binary operation to two `SmtValue`s.
///
/// Returns the result as an `SmtValue`. Operand types must match.
#[allow(clippy::too_many_lines, clippy::match_same_arms)]
pub fn binop(op: &str, lhs: &SmtValue, rhs: &SmtValue) -> Result<SmtValue, String> {
    match (op, lhs, rhs) {
        // Arithmetic (Int)
        ("OpAdd", SmtValue::Int(a), SmtValue::Int(b)) => {
            Ok(SmtValue::Int(backend!(int_add, &[a, b])))
        }
        ("OpSub", SmtValue::Int(a), SmtValue::Int(b)) => {
            Ok(SmtValue::Int(backend!(int_sub, &[a, b])))
        }
        ("OpMul", SmtValue::Int(a), SmtValue::Int(b)) => {
            Ok(SmtValue::Int(backend!(int_mul, &[a, b])))
        }
        ("OpDiv", SmtValue::Int(a), SmtValue::Int(b)) => Ok(SmtValue::Int(backend!(int_div, a, b))),
        ("OpMod", SmtValue::Int(a), SmtValue::Int(b)) => {
            Ok(SmtValue::Int(backend!(int_modulo, a, b)))
        }

        // Arithmetic (Real)
        ("OpAdd", SmtValue::Real(a), SmtValue::Real(b)) => {
            Ok(SmtValue::Real(backend!(real_add, &[a, b])))
        }
        ("OpSub", SmtValue::Real(a), SmtValue::Real(b)) => {
            Ok(SmtValue::Real(backend!(real_sub, &[a, b])))
        }
        ("OpMul", SmtValue::Real(a), SmtValue::Real(b)) => {
            Ok(SmtValue::Real(backend!(real_mul, &[a, b])))
        }
        ("OpDiv", SmtValue::Real(a), SmtValue::Real(b)) => {
            Ok(SmtValue::Real(backend!(real_div, a, b)))
        }

        // Comparison (Int)
        ("OpEq", SmtValue::Int(a), SmtValue::Int(b)) => Ok(SmtValue::Bool(backend!(int_eq, a, b))),
        ("OpNEq", SmtValue::Int(a), SmtValue::Int(b)) => {
            Ok(SmtValue::Bool(backend!(bool_not, &backend!(int_eq, a, b))))
        }
        ("OpLt", SmtValue::Int(a), SmtValue::Int(b)) => Ok(SmtValue::Bool(backend!(int_lt, a, b))),
        ("OpGt", SmtValue::Int(a), SmtValue::Int(b)) => Ok(SmtValue::Bool(backend!(int_gt, a, b))),
        ("OpLe", SmtValue::Int(a), SmtValue::Int(b)) => Ok(SmtValue::Bool(backend!(int_le, a, b))),
        ("OpGe", SmtValue::Int(a), SmtValue::Int(b)) => Ok(SmtValue::Bool(backend!(int_ge, a, b))),

        // Comparison (Real)
        ("OpEq", SmtValue::Real(a), SmtValue::Real(b)) => {
            Ok(SmtValue::Bool(backend!(real_eq, a, b)))
        }
        ("OpNEq", SmtValue::Real(a), SmtValue::Real(b)) => {
            Ok(SmtValue::Bool(backend!(bool_not, &backend!(real_eq, a, b))))
        }
        ("OpLt", SmtValue::Real(a), SmtValue::Real(b)) => {
            Ok(SmtValue::Bool(backend!(real_lt, a, b)))
        }
        ("OpGt", SmtValue::Real(a), SmtValue::Real(b)) => {
            Ok(SmtValue::Bool(backend!(real_gt, a, b)))
        }
        ("OpLe", SmtValue::Real(a), SmtValue::Real(b)) => {
            Ok(SmtValue::Bool(backend!(real_le, a, b)))
        }
        ("OpGe", SmtValue::Real(a), SmtValue::Real(b)) => {
            Ok(SmtValue::Bool(backend!(real_ge, a, b)))
        }

        // Boolean (Bool)
        ("OpEq", SmtValue::Bool(a), SmtValue::Bool(b)) => {
            Ok(SmtValue::Bool(backend!(bool_eq, a, b)))
        }
        ("OpNEq", SmtValue::Bool(a), SmtValue::Bool(b)) => {
            Ok(SmtValue::Bool(backend!(bool_not, &backend!(bool_eq, a, b))))
        }
        ("OpAnd", SmtValue::Bool(a), SmtValue::Bool(b)) => {
            Ok(SmtValue::Bool(backend!(bool_and, &[a, b])))
        }
        ("OpOr", SmtValue::Bool(a), SmtValue::Bool(b)) => {
            Ok(SmtValue::Bool(backend!(bool_or, &[a, b])))
        }
        ("OpImplies", SmtValue::Bool(a), SmtValue::Bool(b)) => {
            Ok(SmtValue::Bool(backend!(bool_implies, a, b)))
        }

        // Array equality (Map/Set/Seq)
        ("OpEq", SmtValue::Array(a), SmtValue::Array(b)) => {
            Ok(SmtValue::Bool(backend!(array_eq, a, b.clone())))
        }
        ("OpNEq", SmtValue::Array(a), SmtValue::Array(b)) => Ok(SmtValue::Bool(backend!(
            bool_not,
            &backend!(array_eq, a, b.clone())
        ))),

        // ── Collection operations (Set/Seq/Map) ───────────────────────
        // Sets are Array<T, Bool> (characteristic functions).
        // Operations use lambda arrays and quantifiers.

        // ── Set operations (polymorphic over element sort) ────────────
        // Type-directed overloading (*, -, <=, + on sets) is done at IR
        // lowering time by checking the EExpr type, NOT here at SMT level.
        // This avoids confusing Set<T> with Map<K,Bool> or Seq<Bool>.
        //
        // Helper: create a fresh quantifier variable matching the array's
        // domain sort. Uses array_get_sort() to extract the element type.
        //
        // Set union (<> or Set::union): lambda x. a[x] OR b[x]
        ("OpDiamond" | "OpSetUnion", SmtValue::Array(a), SmtValue::Array(b)) => {
            let sort = backend!(array_get_sort, a);
            let domain = backend!(sort_array_domain, &sort).unwrap();
            let x = backend!(dynamic_fresh, "su", &domain);
            let a_x = backend!(dynamic_as_bool, &backend!(array_select, a, &x)).unwrap();
            let b_x = backend!(dynamic_as_bool, &backend!(array_select, b, &x)).unwrap();
            let body = backend!(bool_or, &[&a_x, &b_x]);
            let arr = backend!(lambda, &[&x], &backend!(dynamic_from_bool, &body));
            Ok(SmtValue::Array(arr))
        }
        // Set intersection (* or Set::intersect)
        ("OpSetIntersect", SmtValue::Array(a), SmtValue::Array(b)) => {
            let sort = backend!(array_get_sort, a);
            let domain = backend!(sort_array_domain, &sort).unwrap();
            let x = backend!(dynamic_fresh, "si", &domain);
            let a_x = backend!(dynamic_as_bool, &backend!(array_select, a, &x)).unwrap();
            let b_x = backend!(dynamic_as_bool, &backend!(array_select, b, &x)).unwrap();
            let body = backend!(bool_and, &[&a_x, &b_x]);
            let arr = backend!(lambda, &[&x], &backend!(dynamic_from_bool, &body));
            Ok(SmtValue::Array(arr))
        }
        // Set difference (- or Set::diff)
        ("OpSetDiff", SmtValue::Array(a), SmtValue::Array(b)) => {
            let sort = backend!(array_get_sort, a);
            let domain = backend!(sort_array_domain, &sort).unwrap();
            let x = backend!(dynamic_fresh, "sd", &domain);
            let a_x = backend!(dynamic_as_bool, &backend!(array_select, a, &x)).unwrap();
            let b_x = backend!(dynamic_as_bool, &backend!(array_select, b, &x)).unwrap();
            let body = backend!(bool_and, &[&a_x, &backend!(bool_not, &b_x)]);
            let arr = backend!(lambda, &[&x], &backend!(dynamic_from_bool, &body));
            Ok(SmtValue::Array(arr))
        }
        // Set subset (<= or Set::subset): forall x. a[x] -> b[x]
        ("OpSetSubset", SmtValue::Array(a), SmtValue::Array(b)) => {
            let sort = backend!(array_get_sort, a);
            let domain = backend!(sort_array_domain, &sort).unwrap();
            let x = backend!(dynamic_fresh, "ss", &domain);
            let a_x = backend!(dynamic_as_bool, &backend!(array_select, a, &x)).unwrap();
            let b_x = backend!(dynamic_as_bool, &backend!(array_select, b, &x)).unwrap();
            let body = backend!(bool_implies, &a_x, &b_x);
            let q = backend!(forall, &[&x], &body);
            Ok(SmtValue::Bool(q))
        }
        // Set disjointness (!* or Set::disjoint): forall x. not(a[x] and b[x])
        ("OpDisjoint" | "OpSetDisjoint", SmtValue::Array(a), SmtValue::Array(b)) => {
            let sort = backend!(array_get_sort, a);
            let domain = backend!(sort_array_domain, &sort).unwrap();
            let x = backend!(dynamic_fresh, "sj", &domain);
            let a_x = backend!(dynamic_as_bool, &backend!(array_select, a, &x)).unwrap();
            let b_x = backend!(dynamic_as_bool, &backend!(array_select, b, &x)).unwrap();
            let body = backend!(bool_not, &backend!(bool_and, &[&a_x, &b_x]));
            let q = backend!(forall, &[&x], &body);
            Ok(SmtValue::Bool(q))
        }
        // Seq concat (<> on Seq or Seq::concat): result[i] = if i < #a then a[i] else b[i - #a]
        // Since we don't track lengths explicitly in the SMT encoding, we use
        // array equality semantics: two concatenated arrays agree on all indices.
        // For finite literal concatenation, this works via store chains.
        // For symbolic concat, we return the merged array (best-effort).
        ("OpSeqConcat" | "OpSeqCons", SmtValue::Array(_a), SmtValue::Array(_b)) => {
            // For now: treat <> on sequences the same as on sets (element-wise OR).
            // This is correct for set-like usage but not for ordered sequences.
            // Full ordered concat needs length tracking (deferred to ).
            Err(
                "Seq::concat on symbolic sequences requires length tracking; \
                 use Seq literals directly for concrete concatenation"
                    .to_owned(),
            )
        }
        // Set member (Set::member(elem, set)): select from characteristic function
        // Argument order: (elem, set) from surface syntax
        ("OpSetMember", SmtValue::Int(x), SmtValue::Array(s)) => Ok(SmtValue::Bool(
            backend!(
                dynamic_as_bool,
                &backend!(array_select, s, &backend!(dynamic_from_int, x))
            )
            .unwrap(),
        )),
        ("OpSetMember", SmtValue::Dynamic(x), SmtValue::Array(s)) => Ok(SmtValue::Bool(
            backend!(dynamic_as_bool, &backend!(array_select, s, x)).unwrap(),
        )),
        ("OpSetMember", SmtValue::Bool(x), SmtValue::Array(s)) => Ok(SmtValue::Bool(
            backend!(
                dynamic_as_bool,
                &backend!(array_select, s, &backend!(dynamic_from_bool, x))
            )
            .unwrap(),
        )),
        ("OpSetMember", SmtValue::Real(x), SmtValue::Array(s)) => Ok(SmtValue::Bool(
            backend!(
                dynamic_as_bool,
                &backend!(array_select, s, &backend!(dynamic_from_real, x))
            )
            .unwrap(),
        )),
        // Map merge/has/domain/range: require domain tracking (a companion
        // boolean array recording which keys are present). Without it, merge
        // discards left-only keys, domain misses default-valued keys, and has
        // is unsound for non-Bool maps. Deferred — see.

        // Composition operators
        ("OpSeq", SmtValue::Bool(a), SmtValue::Bool(b)) => {
            Ok(SmtValue::Bool(backend!(bool_implies, a, b)))
        }
        ("OpSameStep", SmtValue::Bool(a), SmtValue::Bool(b)) => {
            Ok(SmtValue::Bool(backend!(bool_and, &[a, b])))
        }
        ("OpUnord", SmtValue::Bool(a), SmtValue::Bool(b)) => {
            Ok(SmtValue::Bool(backend!(bool_and, &[a, b])))
        }
        ("OpConc", SmtValue::Bool(a), SmtValue::Bool(b)) => {
            Ok(SmtValue::Bool(backend!(bool_and, &[a, b])))
        }
        ("OpXor", SmtValue::Bool(a), SmtValue::Bool(b)) => {
            Ok(SmtValue::Bool(backend!(bool_xor, a, b)))
        }

        // Dynamic operands — from array select, cast to matching type
        (op, SmtValue::Dynamic(d), other) | (op, other, SmtValue::Dynamic(d)) => {
            let coerced = match other {
                SmtValue::Int(_) => SmtValue::Int(
                    backend!(dynamic_as_int, d)
                        .ok_or_else(|| format!("type error: Dynamic->Int cast failed in {op}"))?,
                ),
                SmtValue::Bool(_) => SmtValue::Bool(
                    backend!(dynamic_as_bool, d)
                        .ok_or_else(|| format!("type error: Dynamic->Bool cast failed in {op}"))?,
                ),
                SmtValue::Real(_) => SmtValue::Real(
                    backend!(dynamic_as_real, d)
                        .ok_or_else(|| format!("type error: Dynamic->Real cast failed in {op}"))?,
                ),
                SmtValue::Dynamic(d2) => {
                    if let Some(i) = backend!(dynamic_as_int, d) {
                        SmtValue::Int(i)
                    } else if let Some(b) = backend!(dynamic_as_bool, d) {
                        SmtValue::Bool(b)
                    } else {
                        // Both operands are genuine Dynamic (e.g., ADT sorts) —
                        // use generic equality/inequality directly.
                        return match op {
                            "OpEq" => Ok(SmtValue::Bool(backend!(dynamic_eq, d, d2))),
                            "OpNEq" => Ok(SmtValue::Bool(backend!(
                                bool_not,
                                &backend!(dynamic_eq, d, d2)
                            ))),
                            _ => Err(format!(
                                "type error: cannot apply {op} to ADT/Dynamic operands"
                            )),
                        };
                    }
                }
                SmtValue::Array(_) => {
                    return Err(format!("type error: cannot apply {op} to Array operand"));
                }
                SmtValue::Func(_) => {
                    return Err(format!("type error: cannot apply {op} to function value"));
                }
            };
            if matches!(lhs, SmtValue::Dynamic(_)) {
                binop(op, &coerced, rhs)
            } else {
                binop(op, lhs, &coerced)
            }
        }

        _ => Err(format!("unsupported binop: {op} on {lhs:?}, {rhs:?}")),
    }
}

/// Negate a boolean or apply unary minus to an int.
/// Accepts IR op names: `"OpNot"`, `"OpNeg"`.
pub fn unop(op: &str, val: &SmtValue) -> Result<SmtValue, String> {
    match op {
        "OpNot" | "not" => {
            let b = val.as_bool()?;
            Ok(SmtValue::Bool(backend!(bool_not, b)))
        }
        "OpNeg" | "-" => {
            let i = val.as_int()?;
            Ok(SmtValue::Int(backend!(int_neg, i)))
        }

        // Collection unary operations
        "OpSetEmpty" => {
            let arr = val.as_array()?;
            let sort = backend!(array_get_sort, arr);
            let empty = backend!(
                array_const_array,
                &backend!(sort_array_domain, &sort).unwrap(),
                &backend!(dynamic_from_bool, &backend!(bool_const, false)),
            );
            Ok(SmtValue::Bool(backend!(array_eq, arr, empty)))
        }
        "OpSetSize" => {
            // Set size via cardinality — reuse existing Card encoding path
            Err("Set::size should use # (cardinality) operator".to_owned())
        }
        "OpSeqHead" => {
            let arr = val.as_array()?;
            let zero = backend!(int_lit, 0);
            Ok(SmtValue::Dynamic(backend!(
                array_select,
                arr,
                &backend!(dynamic_from_int, &zero),
            )))
        }
        "OpSeqTail" => {
            let arr = val.as_array()?;
            let idx = backend!(dynamic_fresh, "st", &backend!(int_sort));
            let idx_int = backend!(dynamic_as_int, &idx)
                .ok_or_else(|| "Seq::tail expected Int sequence index".to_owned())?;
            let one = backend!(int_lit, 1);
            let shifted = backend!(int_add, &[&idx_int, &one]);
            let body = backend!(array_select, arr, &backend!(dynamic_from_int, &shifted));
            let tail = backend!(lambda, &[&idx], &body);
            Ok(SmtValue::Array(tail))
        }
        "OpSeqLength" => {
            // Seq length via cardinality
            Err("Seq::length should use # (cardinality) operator".to_owned())
        }
        "OpSeqEmpty" => {
            // Check if sequence is empty (length == 0)
            Err("Seq::empty requires length tracking".to_owned())
        }
        // Map::domain, Map::range — deferred: requires domain tracking.
        // See.
        _ => Err(format!("unsupported unop: {op}")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn backend_neutral_ast_extension_traits_dispatch_to_active_backend() {
        let t = <Bool as BoolAstExt>::from_bool(true);
        let f = <Bool as BoolAstExt>::from_bool(false);
        let b = <Bool as BoolAstExt>::new_const("smt_ext_b");
        let not_b = <Bool as BoolAstExt>::not(&b);
        let excluded_middle = <Bool as BoolAstExt>::or(&[&b, &not_b]);
        let conjunction = <Bool as BoolAstExt>::and(&[&t, &excluded_middle]);
        let xor_tf = <Bool as BoolAstExt>::xor(&t, &f);
        let implication = <Bool as BoolAstExt>::implies(&conjunction, &xor_tf);
        let bool_eq_self = <Bool as BoolAstExt>::eq(&b, b.clone());

        let one = <Int as IntAstExt>::from_i64(1);
        let two = <Int as IntAstExt>::new_const("smt_ext_i");
        let int_constraints = [
            <Int as IntAstExt>::lt(&one, two.clone()),
            <Int as IntAstExt>::le(&one, two.clone()),
            <Int as IntAstExt>::gt(&two, one.clone()),
            <Int as IntAstExt>::ge(&two, one.clone()),
            <Int as IntAstExt>::eq(&one, one.clone()),
        ];

        let SmtValue::Real(real_one) = real_val(1, 1) else {
            panic!("expected real");
        };
        let SmtValue::Real(real_two) = real_val(2, 1) else {
            panic!("expected real");
        };
        let real_constraints = [
            <Real as RealAstExt>::lt(&real_one, real_two.clone()),
            <Real as RealAstExt>::le(&real_one, real_two.clone()),
            <Real as RealAstExt>::gt(&real_two, real_one.clone()),
            <Real as RealAstExt>::ge(&real_two, real_one.clone()),
            <Real as RealAstExt>::eq(&real_one, real_one.clone()),
        ];

        let _ = <Sort as SortExt>::int();
        let _ = <Sort as SortExt>::bool();
        let _ = <Sort as SortExt>::real();

        let solver = AbideSolver::new();
        solver.assert(&implication);
        solver.assert(&bool_eq_self);
        solver.assert(&int_eq(&two, &int_lit(2)));
        for constraint in &int_constraints {
            solver.assert(constraint);
        }
        for constraint in &real_constraints {
            solver.assert(constraint);
        }
        assert_eq!(solver.check(), SatResult::Sat);
    }
}
