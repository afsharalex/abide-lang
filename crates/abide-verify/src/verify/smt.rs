//! SMT solver facade — the single point of backend contact for the verify module.
//!
//! Every other file in verify/ imports solver types from here, never from `z3::`
//! directly. All operations dispatch through the `SolverBackend` trait
//! (implemented by `Z3Backend` in `solver.rs`), ensuring a future backend swap
//! only touches solver.rs.

#![allow(clippy::needless_borrows_for_generic_args)]

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
    static TUPLE_SORT_CACHE: RefCell<HashMap<(SolverFamily, String), Rc<DatatypeSort>>> =
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

/// Lift an integer SMT term into the real sort.
pub fn int_to_real(i: &Int) -> Real {
    backend!(int_to_real, i)
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

/// Create a named Dynamic term suitable for solver quantifier/lambda binders.
pub fn dynamic_bound_var(name: &str, sort: &Sort) -> Dynamic {
    backend!(dynamic_bound_var, name, sort)
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

pub fn tuple_sort(elements: &[IRType]) -> Rc<DatatypeSort> {
    let family = AB::family();
    let key = format!("{elements:?}");
    TUPLE_SORT_CACHE.with(|cache| {
        if let Some(found) = cache.borrow().get(&(family, key.clone())) {
            return Rc::clone(found);
        }

        let name = format!("TupleVal_{}", stable_hash_hex(&key));
        let field_names = (0..elements.len())
            .map(|idx| format!("field{idx}"))
            .collect::<Vec<_>>();
        let field_accessors = elements
            .iter()
            .map(|ty| datatype_accessor_sort(ir_type_to_sort(ty)))
            .collect::<Vec<_>>();
        let field_refs = field_names
            .iter()
            .zip(field_accessors)
            .map(|(name, accessor)| (name.as_str(), accessor))
            .collect::<Vec<_>>();
        let builder = datatype_builder_variant(datatype_builder(&name), "Tuple", field_refs);
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
    /// Tuple/product value with its structural elements retained for fieldwise equality.
    Tuple {
        value: Dynamic,
        elements: Vec<SmtValue>,
    },
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
            SmtValue::Tuple { value, .. } => value.clone(),
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
        | IRType::Record { .. } => int_like_dynamic_to_smt_value(d),
        IRType::Tuple { .. } => SmtValue::Dynamic(d),
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

pub fn tuple_value(element_tys: &[IRType], elements: Vec<SmtValue>) -> Result<SmtValue, String> {
    if element_tys.len() != elements.len() {
        return Err(format!(
            "tuple arity mismatch: type has {} elements, value has {}",
            element_tys.len(),
            elements.len()
        ));
    }
    let sort = tuple_sort(element_tys);
    let args = elements
        .iter()
        .map(SmtValue::to_dynamic)
        .collect::<Vec<_>>();
    let arg_refs = args.iter().collect::<Vec<_>>();
    Ok(SmtValue::Tuple {
        value: func_decl_apply(&sort.variants[0].constructor, &arg_refs),
        elements,
    })
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
        IRType::Tuple { elements } => tuple_sort(elements).sort(),
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
        (SmtValue::Real(x), SmtValue::Int(y)) => {
            Ok(backend!(real_eq, x, &backend!(int_to_real, y)))
        }
        (SmtValue::Int(x), SmtValue::Real(y)) => {
            Ok(backend!(real_eq, &backend!(int_to_real, x), y))
        }
        (SmtValue::Array(x), SmtValue::Array(y)) => Ok(backend!(array_eq, x, y.clone())),
        (SmtValue::Tuple { elements: xs, .. }, SmtValue::Tuple { elements: ys, .. }) => {
            if xs.len() != ys.len() {
                return Ok(bool_const(false));
            }
            let equalities = xs
                .iter()
                .zip(ys)
                .map(|(x, y)| smt_eq(x, y))
                .collect::<Result<Vec<_>, _>>()?;
            let refs = equalities.iter().collect::<Vec<_>>();
            Ok(bool_and(&refs))
        }
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
        (SmtValue::Real(t), SmtValue::Int(e)) => {
            SmtValue::Real(backend!(real_ite, cond, t, &backend!(int_to_real, e)))
        }
        (SmtValue::Int(t), SmtValue::Real(e)) => {
            SmtValue::Real(backend!(real_ite, cond, &backend!(int_to_real, t), e))
        }
        (SmtValue::Array(t), SmtValue::Array(e)) => {
            SmtValue::Array(backend!(array_ite, cond, t, e))
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

fn mixed_numeric_reals(lhs: &SmtValue, rhs: &SmtValue) -> Option<(Real, Real)> {
    match (lhs, rhs) {
        (SmtValue::Real(a), SmtValue::Int(b)) => Some((a.clone(), backend!(int_to_real, b))),
        (SmtValue::Int(a), SmtValue::Real(b)) => Some((backend!(int_to_real, a), b.clone())),
        _ => None,
    }
}

type BinopResult = Result<SmtValue, String>;

/// Apply a binary operation to two `SmtValue`s.
///
/// Returns the result as an `SmtValue`. Operand types must match.
pub fn binop(op: &str, lhs: &SmtValue, rhs: &SmtValue) -> Result<SmtValue, String> {
    if let Some(result) = int_binop(op, lhs, rhs) {
        return result;
    }
    if let Some(result) = real_binop(op, lhs, rhs) {
        return result;
    }
    if let Some(result) = mixed_numeric_binop(op, lhs, rhs) {
        return result;
    }
    if let Some(result) = bool_binop(op, lhs, rhs) {
        return result;
    }
    if let Some(result) = array_binop(op, lhs, rhs) {
        return result;
    }
    if let Some(result) = collection_binop(op, lhs, rhs) {
        return result;
    }
    if let Some(result) = composition_binop(op, lhs, rhs) {
        return result;
    }
    if let Some(result) = dynamic_binop(op, lhs, rhs) {
        return result;
    }
    Err(format!("unsupported binop: {op} on {lhs:?}, {rhs:?}"))
}

fn int_binop(op: &str, lhs: &SmtValue, rhs: &SmtValue) -> Option<BinopResult> {
    let (SmtValue::Int(a), SmtValue::Int(b)) = (lhs, rhs) else {
        return None;
    };
    Some(match op {
        "OpAdd" => Ok(SmtValue::Int(backend!(int_add, &[a, b]))),
        "OpSub" => Ok(SmtValue::Int(backend!(int_sub, &[a, b]))),
        "OpMul" => Ok(SmtValue::Int(backend!(int_mul, &[a, b]))),
        "OpDiv" => Ok(SmtValue::Int(backend!(int_div, a, b))),
        "OpMod" => Ok(SmtValue::Int(backend!(int_modulo, a, b))),
        "OpEq" => Ok(SmtValue::Bool(backend!(int_eq, a, b))),
        "OpNEq" => Ok(SmtValue::Bool(backend!(bool_not, &backend!(int_eq, a, b)))),
        "OpLt" => Ok(SmtValue::Bool(backend!(int_lt, a, b))),
        "OpGt" => Ok(SmtValue::Bool(backend!(int_gt, a, b))),
        "OpLe" => Ok(SmtValue::Bool(backend!(int_le, a, b))),
        "OpGe" => Ok(SmtValue::Bool(backend!(int_ge, a, b))),
        _ => return None,
    })
}

fn real_binop(op: &str, lhs: &SmtValue, rhs: &SmtValue) -> Option<BinopResult> {
    let (SmtValue::Real(a), SmtValue::Real(b)) = (lhs, rhs) else {
        return None;
    };
    Some(match op {
        "OpAdd" => Ok(SmtValue::Real(backend!(real_add, &[a, b]))),
        "OpSub" => Ok(SmtValue::Real(backend!(real_sub, &[a, b]))),
        "OpMul" => Ok(SmtValue::Real(backend!(real_mul, &[a, b]))),
        "OpDiv" => Ok(SmtValue::Real(backend!(real_div, a, b))),
        "OpEq" => Ok(SmtValue::Bool(backend!(real_eq, a, b))),
        "OpNEq" => Ok(SmtValue::Bool(backend!(bool_not, &backend!(real_eq, a, b)))),
        "OpLt" => Ok(SmtValue::Bool(backend!(real_lt, a, b))),
        "OpGt" => Ok(SmtValue::Bool(backend!(real_gt, a, b))),
        "OpLe" => Ok(SmtValue::Bool(backend!(real_le, a, b))),
        "OpGe" => Ok(SmtValue::Bool(backend!(real_ge, a, b))),
        _ => return None,
    })
}

fn mixed_numeric_binop(op: &str, lhs: &SmtValue, rhs: &SmtValue) -> Option<BinopResult> {
    let (a, b) = mixed_numeric_reals(lhs, rhs)?;
    Some(match op {
        "OpAdd" => Ok(SmtValue::Real(backend!(real_add, &[&a, &b]))),
        "OpSub" => Ok(SmtValue::Real(backend!(real_sub, &[&a, &b]))),
        "OpMul" => Ok(SmtValue::Real(backend!(real_mul, &[&a, &b]))),
        "OpDiv" => Ok(SmtValue::Real(backend!(real_div, &a, &b))),
        "OpEq" => Ok(SmtValue::Bool(backend!(real_eq, &a, &b))),
        "OpNEq" => Ok(SmtValue::Bool(backend!(
            bool_not,
            &backend!(real_eq, &a, &b)
        ))),
        "OpLt" => Ok(SmtValue::Bool(backend!(real_lt, &a, &b))),
        "OpLe" => Ok(SmtValue::Bool(backend!(real_le, &a, &b))),
        "OpGt" => Ok(SmtValue::Bool(backend!(real_gt, &a, &b))),
        "OpGe" => Ok(SmtValue::Bool(backend!(real_ge, &a, &b))),
        _ => return None,
    })
}

fn bool_binop(op: &str, lhs: &SmtValue, rhs: &SmtValue) -> Option<BinopResult> {
    let (SmtValue::Bool(a), SmtValue::Bool(b)) = (lhs, rhs) else {
        return None;
    };
    Some(match op {
        "OpEq" => Ok(SmtValue::Bool(backend!(bool_eq, a, b))),
        "OpNEq" => Ok(SmtValue::Bool(backend!(bool_not, &backend!(bool_eq, a, b)))),
        "OpAnd" => Ok(SmtValue::Bool(backend!(bool_and, &[a, b]))),
        "OpOr" => Ok(SmtValue::Bool(backend!(bool_or, &[a, b]))),
        "OpImplies" => Ok(SmtValue::Bool(backend!(bool_implies, a, b))),
        _ => return None,
    })
}

fn array_binop(op: &str, lhs: &SmtValue, rhs: &SmtValue) -> Option<BinopResult> {
    let (SmtValue::Array(a), SmtValue::Array(b)) = (lhs, rhs) else {
        return None;
    };
    Some(match op {
        "OpEq" => Ok(SmtValue::Bool(backend!(array_eq, a, b.clone()))),
        "OpNEq" => Ok(SmtValue::Bool(backend!(
            bool_not,
            &backend!(array_eq, a, b.clone())
        ))),
        _ => return None,
    })
}

fn composition_binop(op: &str, lhs: &SmtValue, rhs: &SmtValue) -> Option<BinopResult> {
    let (SmtValue::Bool(a), SmtValue::Bool(b)) = (lhs, rhs) else {
        return None;
    };
    Some(match op {
        "OpSeq" => Ok(SmtValue::Bool(backend!(bool_implies, a, b))),
        "OpSameStep" | "OpUnord" | "OpConc" => Ok(SmtValue::Bool(backend!(bool_and, &[a, b]))),
        "OpXor" => Ok(SmtValue::Bool(backend!(bool_xor, a, b))),
        _ => return None,
    })
}

fn collection_binop(op: &str, lhs: &SmtValue, rhs: &SmtValue) -> Option<BinopResult> {
    match (op, lhs, rhs) {
        ("OpDiamond" | "OpSetUnion", SmtValue::Array(a), SmtValue::Array(b)) => {
            Some(Ok(SmtValue::Array(set_lambda_binop("su", a, b, |x, y| {
                backend!(bool_or, &[x, y])
            }))))
        }
        ("OpSetIntersect", SmtValue::Array(a), SmtValue::Array(b)) => {
            Some(Ok(SmtValue::Array(set_lambda_binop("si", a, b, |x, y| {
                backend!(bool_and, &[x, y])
            }))))
        }
        ("OpSetDiff", SmtValue::Array(a), SmtValue::Array(b)) => {
            Some(Ok(SmtValue::Array(set_lambda_binop("sd", a, b, |x, y| {
                backend!(bool_and, &[x, &backend!(bool_not, y)])
            }))))
        }
        ("OpSetSubset", SmtValue::Array(a), SmtValue::Array(b)) => Some(Ok(SmtValue::Bool(
            set_quantified_binop("ss", a, b, |x, y| backend!(bool_implies, x, y)),
        ))),
        ("OpDisjoint" | "OpSetDisjoint", SmtValue::Array(a), SmtValue::Array(b)) => Some(Ok(
            SmtValue::Bool(set_quantified_binop("sj", a, b, |x, y| {
                backend!(bool_not, &backend!(bool_and, &[x, y]))
            })),
        )),
        ("OpSeqConcat" | "OpSeqCons", SmtValue::Array(_), SmtValue::Array(_)) => Some(Err(
            "Seq::concat on symbolic sequences requires length tracking; \
             use Seq literals directly for concrete concatenation"
                .to_owned(),
        )),
        ("OpSetMember", _, SmtValue::Array(s)) => Some(set_member(lhs, s)),
        _ => None,
    }
}

fn set_lambda_binop(
    prefix: &str,
    a: &Array,
    b: &Array,
    combine: impl FnOnce(&Bool, &Bool) -> Bool,
) -> Array {
    let (x, a_x, b_x) = set_operands(prefix, a, b);
    let body = combine(&a_x, &b_x);
    backend!(lambda, &[&x], &backend!(dynamic_from_bool, &body))
}

fn set_quantified_binop(
    prefix: &str,
    a: &Array,
    b: &Array,
    combine: impl FnOnce(&Bool, &Bool) -> Bool,
) -> Bool {
    let (x, a_x, b_x) = set_operands(prefix, a, b);
    let body = combine(&a_x, &b_x);
    backend!(forall, &[&x], &body)
}

fn set_operands(prefix: &str, a: &Array, b: &Array) -> (Dynamic, Bool, Bool) {
    let sort = backend!(array_get_sort, a);
    let domain = backend!(sort_array_domain, &sort).unwrap();
    let x = backend!(dynamic_fresh, prefix, &domain);
    let a_x = backend!(dynamic_as_bool, &backend!(array_select, a, &x)).unwrap();
    let b_x = backend!(dynamic_as_bool, &backend!(array_select, b, &x)).unwrap();
    (x, a_x, b_x)
}

fn set_member(elem: &SmtValue, set: &Array) -> BinopResult {
    let elem = match elem {
        SmtValue::Int(x) => backend!(dynamic_from_int, x),
        SmtValue::Dynamic(x) => x.clone(),
        SmtValue::Bool(x) => backend!(dynamic_from_bool, x),
        SmtValue::Real(x) => backend!(dynamic_from_real, x),
        other => {
            return Err(format!(
                "type error: Set::member element cannot be {other:?}"
            ));
        }
    };
    Ok(SmtValue::Bool(
        backend!(dynamic_as_bool, &backend!(array_select, set, &elem)).unwrap(),
    ))
}

fn dynamic_binop(op: &str, lhs: &SmtValue, rhs: &SmtValue) -> Option<BinopResult> {
    let (dynamic, other, dynamic_on_left) = match (lhs, rhs) {
        (SmtValue::Dynamic(d), other) => (d, other, true),
        (other, SmtValue::Dynamic(d)) => (d, other, false),
        _ => return None,
    };
    if let SmtValue::Dynamic(d2) = other {
        if let Some(i) = backend!(dynamic_as_int, dynamic) {
            return Some(if dynamic_on_left {
                binop(op, &SmtValue::Int(i), rhs)
            } else {
                binop(op, lhs, &SmtValue::Int(i))
            });
        }
        if let Some(b) = backend!(dynamic_as_bool, dynamic) {
            return Some(if dynamic_on_left {
                binop(op, &SmtValue::Bool(b), rhs)
            } else {
                binop(op, lhs, &SmtValue::Bool(b))
            });
        }
        return Some(match op {
            "OpEq" => Ok(SmtValue::Bool(backend!(dynamic_eq, dynamic, d2))),
            "OpNEq" => Ok(SmtValue::Bool(backend!(
                bool_not,
                &backend!(dynamic_eq, dynamic, d2)
            ))),
            _ => Err(format!(
                "type error: cannot apply {op} to ADT/Dynamic operands"
            )),
        });
    }
    Some(match coerce_dynamic(op, dynamic, other) {
        Ok(coerced) if dynamic_on_left => binop(op, &coerced, rhs),
        Ok(coerced) => binop(op, lhs, &coerced),
        Err(err) => Err(err),
    })
}

fn coerce_dynamic(op: &str, dynamic: &Dynamic, other: &SmtValue) -> BinopResult {
    match other {
        SmtValue::Int(_) => backend!(dynamic_as_int, dynamic)
            .map(SmtValue::Int)
            .ok_or_else(|| format!("type error: Dynamic->Int cast failed in {op}")),
        SmtValue::Bool(_) => backend!(dynamic_as_bool, dynamic)
            .map(SmtValue::Bool)
            .ok_or_else(|| format!("type error: Dynamic->Bool cast failed in {op}")),
        SmtValue::Real(_) => backend!(dynamic_as_real, dynamic)
            .map(SmtValue::Real)
            .ok_or_else(|| format!("type error: Dynamic->Real cast failed in {op}")),
        SmtValue::Dynamic(_) => unreachable!("handled by dynamic_binop"),
        SmtValue::Array(_) => Err(format!("type error: cannot apply {op} to Array operand")),
        SmtValue::Tuple { .. } => Err(format!("type error: cannot apply {op} to Tuple operand")),
        SmtValue::Func(_) => Err(format!("type error: cannot apply {op} to function value")),
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

    fn assert_unsat_with(assertion: &Bool) {
        let solver = AbideSolver::new();
        solver.assert(assertion);
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    fn assert_value_eq(actual: &SmtValue, expected: &SmtValue) {
        let eq = smt_eq(actual, expected).expect("value equality should encode");
        assert_unsat_with(&bool_not(&eq));
    }

    fn assert_bool_value(actual: SmtValue, expected: bool) {
        assert_value_eq(&actual, &bool_val(expected));
    }

    fn assert_int_value(actual: SmtValue, expected: i64) {
        assert_value_eq(&actual, &int_val(expected));
    }

    fn assert_real_value(actual: SmtValue, numerator: i64, denominator: i64) {
        assert_value_eq(&actual, &real_val(numerator, denominator));
    }

    fn int_set(elements: &[i64]) -> SmtValue {
        let set_ty = IRType::Set {
            element: Box::new(IRType::Int),
        };
        let set = dynamic_to_typed_value(default_dynamic(&set_ty), &set_ty);
        let mut array = set
            .as_array()
            .expect("set default should decode as array")
            .clone();
        for element in elements {
            array = array.store(
                &int_val(*element).to_dynamic(),
                &bool_val(true).to_dynamic(),
            );
        }
        SmtValue::Array(array)
    }

    fn assert_int_member(set: &SmtValue, element: i64, expected: bool) {
        let member = binop("OpSetMember", &int_val(element), set).expect("set membership");
        assert_bool_value(member, expected);
    }

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

    #[test]
    fn backend_helper_names_hashes_and_dynamic_projection_are_observable() {
        assert_eq!(sort_name(&sort_int()), "Int");
        assert_eq!(sort_name(&sort_bool()), "Bool");
        assert_eq!(sort_name(&sort_real()), "Real");

        let decl = func_decl("smt_helper_decl", &[&sort_int()], &sort_bool());
        assert_eq!(func_decl_name(&decl), "smt_helper_decl");
        assert_eq!(decl.name(), "smt_helper_decl");

        let int_hash = stable_hash_hex("Int");
        let bool_hash = stable_hash_hex("Bool");
        assert_eq!(int_hash.len(), 16);
        assert_eq!(bool_hash.len(), 16);
        assert_ne!(int_hash, bool_hash);

        let real_dynamic = real_val(3, 2).to_dynamic();
        let projected_real =
            dynamic_as_real(&real_dynamic).expect("dynamic should project to real");
        assert_value_eq(&SmtValue::Real(projected_real), &real_val(3, 2));
    }

    #[test]
    fn smt_eq_proves_typed_and_dynamic_equalities() {
        let int_eq_true = smt_eq(&int_val(1), &int_val(1)).expect("int equality");
        assert_unsat_with(&bool_not(&int_eq_true));

        let int_eq_false = smt_eq(&int_val(1), &int_val(2)).expect("int disequality");
        assert_unsat_with(&int_eq_false);

        let real_eq_true = smt_eq(&real_val(1, 2), &real_val(1, 2)).expect("real equality");
        assert_unsat_with(&bool_not(&real_eq_true));

        let mixed_eq_true = smt_eq(&int_val(1), &real_val(1, 1)).expect("int/real equality");
        assert_unsat_with(&bool_not(&mixed_eq_true));

        let dynamic_int = SmtValue::Dynamic(int_val(3).to_dynamic());
        let dynamic_eq = smt_eq(&dynamic_int, &int_val(3)).expect("dynamic/int equality");
        assert_unsat_with(&bool_not(&dynamic_eq));

        let dynamic_eq = smt_eq(&dynamic_int, &SmtValue::Dynamic(int_val(3).to_dynamic()))
            .expect("dynamic/dynamic equality");
        assert_unsat_with(&bool_not(&dynamic_eq));

        let set_ty = IRType::Set {
            element: Box::new(IRType::Int),
        };
        let empty_left = dynamic_to_typed_value(default_dynamic(&set_ty), &set_ty);
        let empty_right = dynamic_to_typed_value(default_dynamic(&set_ty), &set_ty);
        let set_eq = smt_eq(&empty_left, &empty_right).expect("array equality");
        assert_unsat_with(&bool_not(&set_eq));
    }

    #[test]
    fn smt_ite_preserves_branch_sorts_and_values() {
        let true_cond = bool_val(true).to_bool().expect("bool cond");
        let int_choice = smt_ite(&true_cond, &int_val(7), &int_val(9));
        assert!(matches!(int_choice, SmtValue::Int(_)));
        let int_eq = smt_eq(&int_choice, &int_val(7)).expect("int ite equality");
        assert_unsat_with(&bool_not(&int_eq));

        let false_cond = bool_val(false).to_bool().expect("bool cond");
        let bool_choice = smt_ite(&false_cond, &bool_val(true), &bool_val(false));
        assert!(matches!(bool_choice, SmtValue::Bool(_)));
        let bool_eq = smt_eq(&bool_choice, &bool_val(false)).expect("bool ite equality");
        assert_unsat_with(&bool_not(&bool_eq));

        let real_choice = smt_ite(&true_cond, &real_val(7, 2), &real_val(9, 2));
        assert!(matches!(real_choice, SmtValue::Real(_)));
        let real_eq = smt_eq(&real_choice, &real_val(7, 2)).expect("real ite equality");
        assert_unsat_with(&bool_not(&real_eq));

        let mixed_real_int_choice = smt_ite(&true_cond, &real_val(4, 1), &int_val(5));
        assert!(matches!(mixed_real_int_choice, SmtValue::Real(_)));
        let mixed_real_int_eq =
            smt_eq(&mixed_real_int_choice, &real_val(4, 1)).expect("real/int ite equality");
        assert_unsat_with(&bool_not(&mixed_real_int_eq));

        let dynamic_choice = smt_ite(&true_cond, &int_val(4), &real_val(5, 1));
        let dynamic_eq = smt_eq(&dynamic_choice, &int_val(4)).expect("dynamic ite equality");
        assert_unsat_with(&bool_not(&dynamic_eq));

        let dynamic_same_sort_choice = smt_ite(
            &true_cond,
            &SmtValue::Dynamic(int_val(4).to_dynamic()),
            &SmtValue::Dynamic(int_val(5).to_dynamic()),
        );
        let dynamic_same_sort_eq =
            smt_eq(&dynamic_same_sort_choice, &int_val(4)).expect("dynamic/dynamic ite equality");
        assert_unsat_with(&bool_not(&dynamic_same_sort_eq));

        let set_ty = IRType::Set {
            element: Box::new(IRType::Int),
        };
        let empty_set = dynamic_to_typed_value(default_dynamic(&set_ty), &set_ty);
        let singleton_set = binop("OpSetUnion", &empty_set, &empty_set).expect("set union");
        let array_choice = smt_ite(&true_cond, &empty_set, &singleton_set);
        assert!(matches!(array_choice, SmtValue::Array(_)));
    }

    #[test]
    fn smt_default_dynamic_decodes_to_zero_values_and_empty_collections() {
        let bool_default = dynamic_to_typed_value(default_dynamic(&IRType::Bool), &IRType::Bool);
        let bool_eq = smt_eq(&bool_default, &bool_val(false)).expect("bool default equality");
        assert_unsat_with(&bool_not(&bool_eq));

        let int_default = dynamic_to_typed_value(default_dynamic(&IRType::Int), &IRType::Int);
        let int_eq = smt_eq(&int_default, &int_val(0)).expect("int default equality");
        assert_unsat_with(&bool_not(&int_eq));

        let real_default = dynamic_to_typed_value(default_dynamic(&IRType::Real), &IRType::Real);
        let real_eq = smt_eq(&real_default, &real_val(0, 1)).expect("real default equality");
        assert_unsat_with(&bool_not(&real_eq));

        let seq_ty = IRType::Seq {
            element: Box::new(IRType::Int),
        };
        let seq_default = dynamic_to_typed_value(default_dynamic(&seq_ty), &seq_ty);
        let seq_len = seq_length(&seq_default, &IRType::Int).expect("seq length");
        let seq_len_eq = smt_eq(&seq_len, &int_val(0)).expect("seq length equality");
        assert_unsat_with(&bool_not(&seq_len_eq));

        let set_ty = IRType::Set {
            element: Box::new(IRType::Int),
        };
        let set_default = dynamic_to_typed_value(default_dynamic(&set_ty), &set_ty);
        let member = binop("OpSetMember", &int_val(1), &set_default).expect("set membership");
        let member_eq = smt_eq(&member, &bool_val(false)).expect("set default membership");
        assert_unsat_with(&bool_not(&member_eq));

        let map_ty = IRType::Map {
            key: Box::new(IRType::Int),
            value: Box::new(IRType::Bool),
        };
        let map_default = dynamic_to_typed_value(default_dynamic(&map_ty), &map_ty);
        let map_has_key = map_has(&map_default, &int_val(1), &IRType::Bool).expect("map has");
        let map_has_eq = smt_eq(&map_has_key, &bool_val(false)).expect("map default has");
        assert_unsat_with(&bool_not(&map_has_eq));
        let map_lookup_value =
            map_lookup(&map_default, &int_val(1), &IRType::Bool).expect("map lookup");
        let map_lookup_eq =
            smt_eq(&map_lookup_value, &bool_val(false)).expect("map default lookup");
        assert_unsat_with(&bool_not(&map_lookup_eq));
    }

    #[test]
    fn binop_evaluates_int_operator_family() {
        assert_int_value(
            binop("OpAdd", &int_val(2), &int_val(3)).expect("int add"),
            5,
        );
        assert_int_value(
            binop("OpSub", &int_val(7), &int_val(4)).expect("int sub"),
            3,
        );
        assert_int_value(
            binop("OpMul", &int_val(3), &int_val(4)).expect("int mul"),
            12,
        );
        assert_int_value(
            binop("OpDiv", &int_val(9), &int_val(3)).expect("int div"),
            3,
        );
        assert_int_value(
            binop("OpMod", &int_val(10), &int_val(4)).expect("int mod"),
            2,
        );

        assert_bool_value(
            binop("OpEq", &int_val(4), &int_val(4)).expect("int eq"),
            true,
        );
        assert_bool_value(
            binop("OpNEq", &int_val(4), &int_val(5)).expect("int neq"),
            true,
        );
        assert_bool_value(
            binop("OpLt", &int_val(2), &int_val(3)).expect("int lt"),
            true,
        );
        assert_bool_value(
            binop("OpGt", &int_val(3), &int_val(2)).expect("int gt"),
            true,
        );
        assert_bool_value(
            binop("OpLe", &int_val(2), &int_val(2)).expect("int le"),
            true,
        );
        assert_bool_value(
            binop("OpGe", &int_val(3), &int_val(3)).expect("int ge"),
            true,
        );
    }

    #[test]
    fn binop_evaluates_real_operator_family() {
        assert_real_value(
            binop("OpAdd", &real_val(1, 2), &real_val(3, 2)).expect("real add"),
            2,
            1,
        );
        assert_real_value(
            binop("OpSub", &real_val(5, 2), &real_val(1, 2)).expect("real sub"),
            2,
            1,
        );
        assert_real_value(
            binop("OpMul", &real_val(2, 1), &real_val(3, 2)).expect("real mul"),
            3,
            1,
        );
        assert_real_value(
            binop("OpDiv", &real_val(3, 1), &real_val(2, 1)).expect("real div"),
            3,
            2,
        );

        assert_bool_value(
            binop("OpEq", &real_val(4, 1), &real_val(4, 1)).expect("real eq"),
            true,
        );
        assert_bool_value(
            binop("OpNEq", &real_val(4, 1), &real_val(5, 1)).expect("real neq"),
            true,
        );
        assert_bool_value(
            binop("OpLt", &real_val(2, 1), &real_val(3, 1)).expect("real lt"),
            true,
        );
        assert_bool_value(
            binop("OpGt", &real_val(3, 1), &real_val(2, 1)).expect("real gt"),
            true,
        );
        assert_bool_value(
            binop("OpLe", &real_val(2, 1), &real_val(2, 1)).expect("real le"),
            true,
        );
        assert_bool_value(
            binop("OpGe", &real_val(3, 1), &real_val(3, 1)).expect("real ge"),
            true,
        );
    }

    #[test]
    fn binop_evaluates_mixed_numeric_operator_family() {
        assert_real_value(
            binop("OpAdd", &int_val(1), &real_val(1, 2)).expect("mixed add"),
            3,
            2,
        );
        assert_real_value(
            binop("OpSub", &int_val(2), &real_val(1, 2)).expect("mixed sub"),
            3,
            2,
        );
        assert_real_value(
            binop("OpMul", &int_val(2), &real_val(3, 2)).expect("mixed mul"),
            3,
            1,
        );
        assert_real_value(
            binop("OpDiv", &int_val(3), &real_val(2, 1)).expect("mixed div"),
            3,
            2,
        );

        assert_bool_value(
            binop("OpEq", &int_val(1), &real_val(1, 1)).expect("mixed eq"),
            true,
        );
        assert_bool_value(
            binop("OpNEq", &int_val(1), &real_val(2, 1)).expect("mixed neq"),
            true,
        );
        assert_bool_value(
            binop("OpLt", &int_val(1), &real_val(2, 1)).expect("mixed lt"),
            true,
        );
        assert_bool_value(
            binop("OpLe", &int_val(1), &real_val(1, 1)).expect("mixed le"),
            true,
        );
        assert_bool_value(
            binop("OpGt", &int_val(2), &real_val(1, 1)).expect("mixed gt"),
            true,
        );
        assert_bool_value(
            binop("OpGe", &int_val(1), &real_val(1, 1)).expect("mixed ge"),
            true,
        );
    }

    #[test]
    fn binop_evaluates_bool_and_array_operator_families() {
        assert_bool_value(
            binop("OpEq", &bool_val(true), &bool_val(true)).expect("bool eq"),
            true,
        );
        assert_bool_value(
            binop("OpNEq", &bool_val(true), &bool_val(false)).expect("bool neq"),
            true,
        );
        assert_bool_value(
            binop("OpAnd", &bool_val(true), &bool_val(true)).expect("bool and"),
            true,
        );
        assert_bool_value(
            binop("OpOr", &bool_val(false), &bool_val(true)).expect("bool or"),
            true,
        );
        assert_bool_value(
            binop("OpImplies", &bool_val(false), &bool_val(false)).expect("bool implies"),
            true,
        );

        let set_ty = IRType::Set {
            element: Box::new(IRType::Int),
        };
        let empty_set = dynamic_to_typed_value(default_dynamic(&set_ty), &set_ty);
        let singleton_set = SmtValue::Array(
            empty_set
                .as_array()
                .expect("empty set should decode as array")
                .store(&int_val(1).to_dynamic(), &bool_val(true).to_dynamic()),
        );
        assert_bool_value(
            binop("OpEq", &empty_set, &empty_set).expect("array eq"),
            true,
        );
        assert_bool_value(
            binop("OpNEq", &empty_set, &singleton_set).expect("array neq"),
            true,
        );
    }

    #[test]
    fn binop_evaluates_composition_operator_family() {
        assert_bool_value(
            binop("OpSeq", &bool_val(false), &bool_val(false)).expect("seq composition"),
            true,
        );
        assert_bool_value(
            binop("OpSameStep", &bool_val(true), &bool_val(true)).expect("same-step composition"),
            true,
        );
        assert_bool_value(
            binop("OpUnord", &bool_val(true), &bool_val(true)).expect("unordered composition"),
            true,
        );
        assert_bool_value(
            binop("OpConc", &bool_val(true), &bool_val(true)).expect("concurrent composition"),
            true,
        );
        assert_bool_value(
            binop("OpXor", &bool_val(true), &bool_val(false)).expect("xor composition"),
            true,
        );
    }

    #[test]
    fn binop_evaluates_collection_operator_family() {
        let left = int_set(&[1, 2]);
        let right = int_set(&[2, 3]);
        let singleton = int_set(&[2]);
        let disjoint = int_set(&[4]);

        let intersection =
            binop("OpSetIntersect", &left, &right).expect("set intersection should encode");
        assert_int_member(&intersection, 1, false);
        assert_int_member(&intersection, 2, true);

        let difference = binop("OpSetDiff", &left, &right).expect("set diff should encode");
        assert_int_member(&difference, 1, true);
        assert_int_member(&difference, 2, false);

        assert_bool_value(
            binop("OpSetSubset", &singleton, &left).expect("set subset"),
            true,
        );
        assert_bool_value(
            binop("OpSetDisjoint", &singleton, &disjoint).expect("set disjoint"),
            true,
        );

        let seq_concat_error = binop("OpSeqConcat", &left, &right)
            .expect_err("symbolic sequence concat should remain rejected");
        assert!(seq_concat_error.contains("requires length tracking"));
    }

    #[test]
    fn binop_evaluates_dynamic_operator_family() {
        let dynamic_int = SmtValue::Dynamic(int_val(2).to_dynamic());
        assert_int_value(
            binop("OpAdd", &dynamic_int, &int_val(3)).expect("dynamic int on left"),
            5,
        );

        let dynamic_rhs = SmtValue::Dynamic(int_val(2).to_dynamic());
        assert_int_value(
            binop("OpSub", &int_val(5), &dynamic_rhs).expect("dynamic int on right"),
            3,
        );

        let dynamic_bool = SmtValue::Dynamic(bool_val(true).to_dynamic());
        assert_bool_value(
            binop("OpAnd", &dynamic_bool, &bool_val(true)).expect("dynamic bool on left"),
            true,
        );

        let seq_one = seq_literal(&IRType::Int, &[int_val(1)]);
        let seq_two = seq_literal(&IRType::Int, &[int_val(2)]);
        assert_bool_value(binop("OpEq", &seq_one, &seq_one).expect("dynamic eq"), true);
        assert_bool_value(
            binop("OpNEq", &seq_one, &seq_two).expect("dynamic neq"),
            true,
        );
    }

    #[test]
    fn unop_evaluates_scalar_collection_and_error_cases() {
        assert_bool_value(unop("OpNot", &bool_val(false)).expect("bool not"), true);
        assert_int_value(unop("OpNeg", &int_val(3)).expect("int neg"), -3);

        let empty = int_set(&[]);
        let singleton = int_set(&[1]);
        assert_bool_value(unop("OpSetEmpty", &empty).expect("set empty"), true);
        assert_bool_value(
            unop("OpSetEmpty", &singleton).expect("set non-empty"),
            false,
        );

        let set_size_error = unop("OpSetSize", &empty).expect_err("set size should be rejected");
        assert!(set_size_error.contains("cardinality"));

        let seq = seq_literal(&IRType::Int, &[int_val(7), int_val(8)]);
        let seq_data = SmtValue::Array(seq_data(&seq, &IRType::Int).expect("seq data"));
        let head = unop("OpSeqHead", &seq_data).expect("seq head");
        assert_value_eq(&head, &int_val(7));

        let tail = unop("OpSeqTail", &seq_data).expect("seq tail");
        let tail_head = unop("OpSeqHead", &tail).expect("seq tail head");
        assert_value_eq(&tail_head, &int_val(8));

        let seq_length_error =
            unop("OpSeqLength", &seq_data).expect_err("seq length should be rejected");
        assert!(seq_length_error.contains("cardinality"));
        let seq_empty_error = unop("OpSeqEmpty", &seq_data).expect_err("seq empty should reject");
        assert!(seq_empty_error.contains("length tracking"));
    }

    #[test]
    fn binop_coerces_int_operands_for_mixed_real_comparisons() {
        let result = binop("OpGe", &real_var("mixed_cmp_real"), &int_val(0))
            .expect("real >= int should encode");
        assert!(
            matches!(result, SmtValue::Bool(_)),
            "mixed real/int comparison should return Bool: {result:?}"
        );

        let result = binop("OpLt", &int_val(0), &real_var("mixed_cmp_real_rhs"))
            .expect("int < real should encode");
        assert!(
            matches!(result, SmtValue::Bool(_)),
            "mixed int/real comparison should return Bool: {result:?}"
        );
    }

    #[test]
    fn binop_coerces_int_operands_for_mixed_real_arithmetic() {
        let result = binop("OpAdd", &real_var("mixed_arith_real"), &int_val(2))
            .expect("real + int should encode");
        assert!(
            matches!(result, SmtValue::Real(_)),
            "mixed real/int arithmetic should return Real: {result:?}"
        );

        let result = binop("OpMul", &int_val(3), &real_var("mixed_arith_real_rhs"))
            .expect("int * real should encode");
        assert!(
            matches!(result, SmtValue::Real(_)),
            "mixed int/real arithmetic should return Real: {result:?}"
        );
    }
}
