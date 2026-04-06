//! Z3 value types and sort mapping.
//!
//! Provides the `SmtValue` enum that wraps Z3 AST nodes, and functions
//! to create Z3 sorts from Abide IR types.
//!
//! Uses z3 crate v0.19 API (no explicit Context parameter — global context).

use z3::ast::{Array, Bool, Dynamic, Int, Real};
use z3::Sort;

use crate::ir::types::IRType;

// ── Z3 value wrapper ────────────────────────────────────────────────

/// A Z3 AST value — wraps the concrete Z3 sort variants.
///
/// All Abide expressions compile down to one of these.
#[derive(Debug, Clone)]
pub enum SmtValue {
    /// Z3 Int sort — used for Int, Id, enum variants (encoded as sequential IDs).
    Int(Int),
    /// Z3 Bool sort — direct mapping from Abide Bool.
    Bool(Bool),
    /// Z3 Real sort — used for Abide Real type (exact rational).
    Real(Real),
    /// Z3 Array sort — used for `Map<K,V>` (store/select), `Set<T>` (characteristic function).
    Array(Array),
    /// Z3 uninterpreted/dynamic sort — used for complex types and array select results.
    Dynamic(Dynamic),
    /// Z3 uninterpreted function — used for lambda encodings.
    /// The function has a definitional axiom asserted on the solver.
    /// Carries (FuncDecl, param_sorts, range_sort) for partial application.
    /// Wrapped in Rc because FuncDecl does not implement Clone.
    Func(std::rc::Rc<(z3::FuncDecl, Vec<z3::Sort>, z3::Sort)>),
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

    /// Extract the underlying Z3 AST as Dynamic (works for any variant).
    pub fn to_dynamic(&self) -> Dynamic {
        match self {
            SmtValue::Int(i) => Dynamic::from_ast(i),
            SmtValue::Bool(b) => Dynamic::from_ast(b),
            SmtValue::Real(r) => Dynamic::from_ast(r),
            SmtValue::Array(a) => Dynamic::from_ast(a),
            SmtValue::Dynamic(d) => d.clone(),
            SmtValue::Func(f) => {
                // A function value as Dynamic: create a nullary application
                // (this is a fallback — Func values are normally applied, not coerced)
                f.0.apply(&[])
            }
        }
    }

    /// Convert to a Bool (for use in assertions).
    /// Int → Bool via (int != 0), Bool → Bool, Dynamic → Bool (sort cast).
    pub fn to_bool(&self) -> Result<Bool, String> {
        match self {
            SmtValue::Bool(b) => Ok(b.clone()),
            SmtValue::Int(i) => Ok(i.eq(Int::from_i64(0)).not()),
            SmtValue::Dynamic(d) => d
                .as_bool()
                .ok_or_else(|| format!("type error: cannot convert Dynamic to Bool: {d:?}")),
            other => Err(format!("type error: cannot convert {other:?} to Bool")),
        }
    }
}

// ── Sort mapping ────────────────────────────────────────────────────

/// Map an Abide IR type to a Z3 sort.
///
/// Enums are encoded as Int (variant IDs).
/// Records and entities are handled structurally (not as Z3 datatypes for now).
#[allow(clippy::match_same_arms)] // arms will diverge as encoding matures
pub fn ir_type_to_sort(ty: &IRType) -> Sort {
    match ty {
        IRType::Int | IRType::Id => Sort::int(),
        IRType::Bool => Sort::bool(),
        IRType::Real | IRType::Float => Sort::real(),
        IRType::String => Sort::int(), // strings as uninterpreted ints for now
        IRType::Enum { .. } => Sort::int(), // enums encoded as sequential int IDs
        IRType::Entity { .. } => Sort::int(), // entity refs as slot indices
        IRType::Fn { .. } => Sort::int(), // functions as uninterpreted for now
        IRType::Record { .. } => Sort::int(), // records as uninterpreted for now
        IRType::Set { element } => Sort::array(&ir_type_to_sort(element), &Sort::bool()),
        IRType::Seq { element } => Sort::array(&Sort::int(), &ir_type_to_sort(element)),
        IRType::Map { key, value } => Sort::array(&ir_type_to_sort(key), &ir_type_to_sort(value)),
        IRType::Tuple { .. } => Sort::int(), // tuples as uninterpreted for now
        IRType::Refinement { base, .. } => ir_type_to_sort(base), // use base type sort
    }
}

// ── Literal construction ────────────────────────────────────────────

/// Create a Z3 Int constant from an i64 value.
pub fn int_val(v: i64) -> SmtValue {
    SmtValue::Int(Int::from_i64(v))
}

/// Create a Z3 Bool constant.
pub fn bool_val(v: bool) -> SmtValue {
    SmtValue::Bool(Bool::from_bool(v))
}

/// Create a Z3 Real constant from numerator/denominator.
pub fn real_val(num: i64, den: i64) -> SmtValue {
    SmtValue::Real(Real::from_rational(num, den))
}

/// Create a named Z3 Int variable.
pub fn int_var(name: &str) -> SmtValue {
    SmtValue::Int(Int::new_const(name))
}

/// Create a named Z3 Bool variable.
pub fn bool_var(name: &str) -> SmtValue {
    SmtValue::Bool(Bool::new_const(name))
}

/// Create a named Z3 Real variable.
pub fn real_var(name: &str) -> SmtValue {
    SmtValue::Real(Real::new_const(name))
}

/// Z3 default value for a given IR type, returned as Dynamic.
/// Used for constant-array initialization in collection literal encoding.
/// Recurses for nested collections: `Map<K, Set<T>>` gets a const-array default.
pub fn default_dynamic(ty: &IRType) -> Dynamic {
    match ty {
        IRType::Bool => Dynamic::from_ast(&Bool::from_bool(false)),
        IRType::Real | IRType::Float => Dynamic::from_ast(&Real::from_rational(0, 1)),
        IRType::Map { key, value } => {
            let key_sort = ir_type_to_sort(key);
            let val_default = default_dynamic(value);
            Dynamic::from_ast(&Array::const_array(&key_sort, &val_default))
        }
        IRType::Set { element } => {
            let elem_sort = ir_type_to_sort(element);
            let false_val = Dynamic::from_ast(&Bool::from_bool(false));
            Dynamic::from_ast(&Array::const_array(&elem_sort, &false_val))
        }
        IRType::Seq { element } => {
            let elem_default = default_dynamic(element);
            Dynamic::from_ast(&Array::const_array(&Sort::int(), &elem_default))
        }
        _ => Dynamic::from_ast(&Int::from_i64(0)),
    }
}

/// Create a named Z3 Array variable for a Map/Set/Seq field.
pub fn array_var(name: &str, ty: &IRType) -> Result<SmtValue, String> {
    let sort = ir_type_to_sort(ty);
    let domain = sort
        .array_domain()
        .ok_or_else(|| format!("type error: expected array sort for '{name}', got {ty:?}"))?;
    let range = sort
        .array_range()
        .ok_or_else(|| format!("type error: expected array sort for '{name}', got {ty:?}"))?;
    Ok(SmtValue::Array(Array::new_const(name, &domain, &range)))
}

/// Assert that two `SmtValue`s are equal, returning a Z3 Bool constraint.
///
/// Handles same-variant pairs directly. For cross-variant pairs involving
/// Dynamic (e.g., `Array::select` result vs Int field), coerces the typed
/// operand to Dynamic and uses Z3's generic equality.
pub fn smt_eq(a: &SmtValue, b: &SmtValue) -> Result<Bool, String> {
    match (a, b) {
        (SmtValue::Int(x), SmtValue::Int(y)) => Ok(x.eq(y.clone())),
        (SmtValue::Bool(x), SmtValue::Bool(y)) => Ok(x.eq(y.clone())),
        (SmtValue::Real(x), SmtValue::Real(y)) => Ok(x.eq(y.clone())),
        (SmtValue::Array(x), SmtValue::Array(y)) => Ok(x.eq(y.clone())),
        (SmtValue::Dynamic(x), SmtValue::Dynamic(y)) => Ok(x.eq(y.clone())),
        // Cross-variant: coerce both to Dynamic for Z3's generic equality
        (SmtValue::Dynamic(d), other) | (other, SmtValue::Dynamic(d)) => {
            Ok(d.eq(other.to_dynamic()))
        }
        _ => Err(format!("sort mismatch in equality: {a:?} vs {b:?}")),
    }
}

/// Compare two `SmtValue`s for inequality: `a != b`.
pub fn smt_neq(a: &SmtValue, b: &SmtValue) -> Result<Bool, String> {
    Ok(smt_eq(a, b)?.not())
}

/// Conditional select: `if cond then then_val else else_val`.
/// Both branches must have the same sort.
pub fn smt_ite(cond: &Bool, then_val: &SmtValue, else_val: &SmtValue) -> SmtValue {
    match (then_val, else_val) {
        (SmtValue::Int(t), SmtValue::Int(e)) => SmtValue::Int(cond.ite(t, e)),
        (SmtValue::Bool(t), SmtValue::Bool(e)) => SmtValue::Bool(cond.ite(t, e)),
        (SmtValue::Real(t), SmtValue::Real(e)) => SmtValue::Real(cond.ite(t, e)),
        (SmtValue::Array(t), SmtValue::Array(e)) => SmtValue::Array(cond.ite(t, e)),
        (SmtValue::Dynamic(t), SmtValue::Dynamic(e)) => SmtValue::Dynamic(cond.ite(t, e)),
        // Cross-variant: coerce to Dynamic
        _ => SmtValue::Dynamic(cond.ite(&then_val.to_dynamic(), &else_val.to_dynamic())),
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
        ("OpAdd", SmtValue::Int(a), SmtValue::Int(b)) => Ok(SmtValue::Int(Int::add(&[a, b]))),
        ("OpSub", SmtValue::Int(a), SmtValue::Int(b)) => Ok(SmtValue::Int(Int::sub(&[a, b]))),
        ("OpMul", SmtValue::Int(a), SmtValue::Int(b)) => Ok(SmtValue::Int(Int::mul(&[a, b]))),
        ("OpDiv", SmtValue::Int(a), SmtValue::Int(b)) => Ok(SmtValue::Int(a.div(b))),
        ("OpMod", SmtValue::Int(a), SmtValue::Int(b)) => Ok(SmtValue::Int(a.modulo(b))),

        // Arithmetic (Real)
        ("OpAdd", SmtValue::Real(a), SmtValue::Real(b)) => Ok(SmtValue::Real(Real::add(&[a, b]))),
        ("OpSub", SmtValue::Real(a), SmtValue::Real(b)) => Ok(SmtValue::Real(Real::sub(&[a, b]))),
        ("OpMul", SmtValue::Real(a), SmtValue::Real(b)) => Ok(SmtValue::Real(Real::mul(&[a, b]))),
        ("OpDiv", SmtValue::Real(a), SmtValue::Real(b)) => Ok(SmtValue::Real(Real::div(a, b))),

        // Comparison (Int)
        ("OpEq", SmtValue::Int(a), SmtValue::Int(b)) => Ok(SmtValue::Bool(a.eq(b))),
        ("OpNEq", SmtValue::Int(a), SmtValue::Int(b)) => Ok(SmtValue::Bool(a.eq(b).not())),
        ("OpLt", SmtValue::Int(a), SmtValue::Int(b)) => Ok(SmtValue::Bool(a.lt(b))),
        ("OpGt", SmtValue::Int(a), SmtValue::Int(b)) => Ok(SmtValue::Bool(a.gt(b))),
        ("OpLe", SmtValue::Int(a), SmtValue::Int(b)) => Ok(SmtValue::Bool(a.le(b))),
        ("OpGe", SmtValue::Int(a), SmtValue::Int(b)) => Ok(SmtValue::Bool(a.ge(b))),

        // Comparison (Real)
        ("OpEq", SmtValue::Real(a), SmtValue::Real(b)) => Ok(SmtValue::Bool(a.eq(b))),
        ("OpNEq", SmtValue::Real(a), SmtValue::Real(b)) => Ok(SmtValue::Bool(a.eq(b).not())),
        ("OpLt", SmtValue::Real(a), SmtValue::Real(b)) => Ok(SmtValue::Bool(Real::lt(a, b))),
        ("OpGt", SmtValue::Real(a), SmtValue::Real(b)) => Ok(SmtValue::Bool(Real::gt(a, b))),
        ("OpLe", SmtValue::Real(a), SmtValue::Real(b)) => Ok(SmtValue::Bool(Real::le(a, b))),
        ("OpGe", SmtValue::Real(a), SmtValue::Real(b)) => Ok(SmtValue::Bool(Real::ge(a, b))),

        // Boolean (Bool)
        ("OpEq", SmtValue::Bool(a), SmtValue::Bool(b)) => Ok(SmtValue::Bool(a.eq(b))),
        ("OpNEq", SmtValue::Bool(a), SmtValue::Bool(b)) => Ok(SmtValue::Bool(a.eq(b).not())),
        ("OpAnd", SmtValue::Bool(a), SmtValue::Bool(b)) => Ok(SmtValue::Bool(Bool::and(&[a, b]))),
        ("OpOr", SmtValue::Bool(a), SmtValue::Bool(b)) => Ok(SmtValue::Bool(Bool::or(&[a, b]))),
        ("OpImplies", SmtValue::Bool(a), SmtValue::Bool(b)) => Ok(SmtValue::Bool(a.implies(b))),

        // Array equality (Map/Set/Seq)
        ("OpEq", SmtValue::Array(a), SmtValue::Array(b)) => Ok(SmtValue::Bool(a.eq(b.clone()))),
        ("OpNEq", SmtValue::Array(a), SmtValue::Array(b)) => {
            Ok(SmtValue::Bool(a.eq(b.clone()).not()))
        }

        // ── Collection operations (Set/Seq/Map) ───────────────────────
        // Sets are Array<T, Bool> (characteristic functions).
        // Operations use Z3 lambda arrays and quantifiers.

        // ── Set operations (polymorphic over element sort) ────────────
        // Type-directed overloading (*, -, <=, + on sets) is done at IR
        // lowering time by checking the EExpr type, NOT here at SMT level.
        // This avoids confusing Set<T> with Map<K,Bool> or Seq<Bool>.
        //
        // Helper: create a fresh quantifier variable matching the array's
        // domain sort. Uses Ast::get_sort() to extract the element type.
        //
        // Set union (<> or Set::union): lambda x. a[x] OR b[x]
        ("OpDiamond" | "OpSetUnion", SmtValue::Array(a), SmtValue::Array(b)) => {
            use z3::ast::Ast;
            let domain = a.get_sort().array_domain().unwrap();
            let x = Dynamic::fresh_const("su", &domain);
            let a_x = a.select(&x).as_bool().unwrap();
            let b_x = b.select(&x).as_bool().unwrap();
            let body = Bool::or(&[&a_x, &b_x]);
            let arr = z3::ast::lambda_const(
                &[&x as &dyn z3::ast::Ast], &Dynamic::from_ast(&body),
            );
            Ok(SmtValue::Array(arr))
        }
        // Set intersection (* or Set::intersect)
        ("OpSetIntersect", SmtValue::Array(a), SmtValue::Array(b)) => {
            use z3::ast::Ast;
            let domain = a.get_sort().array_domain().unwrap();
            let x = Dynamic::fresh_const("si", &domain);
            let a_x = a.select(&x).as_bool().unwrap();
            let b_x = b.select(&x).as_bool().unwrap();
            let body = Bool::and(&[&a_x, &b_x]);
            let arr = z3::ast::lambda_const(
                &[&x as &dyn z3::ast::Ast], &Dynamic::from_ast(&body),
            );
            Ok(SmtValue::Array(arr))
        }
        // Set difference (- or Set::diff)
        ("OpSetDiff", SmtValue::Array(a), SmtValue::Array(b)) => {
            use z3::ast::Ast;
            let domain = a.get_sort().array_domain().unwrap();
            let x = Dynamic::fresh_const("sd", &domain);
            let a_x = a.select(&x).as_bool().unwrap();
            let b_x = b.select(&x).as_bool().unwrap();
            let body = Bool::and(&[&a_x, &b_x.not()]);
            let arr = z3::ast::lambda_const(
                &[&x as &dyn z3::ast::Ast], &Dynamic::from_ast(&body),
            );
            Ok(SmtValue::Array(arr))
        }
        // Set subset (<= or Set::subset): ∀ x. a[x] → b[x]
        ("OpSetSubset", SmtValue::Array(a), SmtValue::Array(b)) => {
            use z3::ast::Ast;
            let domain = a.get_sort().array_domain().unwrap();
            let x = Dynamic::fresh_const("ss", &domain);
            let a_x = a.select(&x).as_bool().unwrap();
            let b_x = b.select(&x).as_bool().unwrap();
            let body = a_x.implies(&b_x);
            let q = z3::ast::forall_const(
                &[&x as &dyn z3::ast::Ast], &[], &body,
            );
            Ok(SmtValue::Bool(q))
        }
        // Set disjointness (!* or Set::disjoint): ∀ x. ¬(a[x] ∧ b[x])
        ("OpDisjoint" | "OpSetDisjoint", SmtValue::Array(a), SmtValue::Array(b)) => {
            use z3::ast::Ast;
            let domain = a.get_sort().array_domain().unwrap();
            let x = Dynamic::fresh_const("sj", &domain);
            let a_x = a.select(&x).as_bool().unwrap();
            let b_x = b.select(&x).as_bool().unwrap();
            let body = Bool::and(&[&a_x, &b_x]).not();
            let q = z3::ast::forall_const(
                &[&x as &dyn z3::ast::Ast], &[], &body,
            );
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
            // Full ordered concat needs length tracking (deferred to DDR-047).
            Err("Seq::concat on symbolic sequences requires length tracking; \
                 use Seq literals directly for concrete concatenation"
                .to_owned())
        }
        // Set member (Set::member(elem, set)): select from characteristic function
        // Argument order: (elem, set) from surface syntax
        ("OpSetMember", SmtValue::Int(x), SmtValue::Array(s)) => {
            Ok(SmtValue::Bool(s.select(&Dynamic::from_ast(x)).as_bool().unwrap()))
        }
        ("OpSetMember", SmtValue::Dynamic(x), SmtValue::Array(s)) => {
            Ok(SmtValue::Bool(s.select(x).as_bool().unwrap()))
        }
        ("OpSetMember", SmtValue::Bool(x), SmtValue::Array(s)) => {
            Ok(SmtValue::Bool(s.select(&Dynamic::from_ast(x)).as_bool().unwrap()))
        }
        ("OpSetMember", SmtValue::Real(x), SmtValue::Array(s)) => {
            Ok(SmtValue::Bool(s.select(&Dynamic::from_ast(x)).as_bool().unwrap()))
        }
        // Map merge/has/domain/range: require domain tracking (a companion
        // boolean array recording which keys are present). Without it, merge
        // discards left-only keys, domain misses default-valued keys, and has
        // is unsound for non-Bool maps. Deferred — see DDR-047.

        // Composition operators
        ("OpSeq", SmtValue::Bool(a), SmtValue::Bool(b)) => Ok(SmtValue::Bool(a.implies(b))),
        ("OpSameStep", SmtValue::Bool(a), SmtValue::Bool(b)) => {
            Ok(SmtValue::Bool(Bool::and(&[a, b])))
        }
        ("OpUnord", SmtValue::Bool(a), SmtValue::Bool(b)) => Ok(SmtValue::Bool(Bool::and(&[a, b]))),
        ("OpConc", SmtValue::Bool(a), SmtValue::Bool(b)) => Ok(SmtValue::Bool(Bool::and(&[a, b]))),
        ("OpXor", SmtValue::Bool(a), SmtValue::Bool(b)) => Ok(SmtValue::Bool(Bool::xor(a, b))),

        // Dynamic operands — from array select, cast to matching type
        (op, SmtValue::Dynamic(d), other) | (op, other, SmtValue::Dynamic(d)) => {
            let coerced = match other {
                SmtValue::Int(_) => SmtValue::Int(
                    d.as_int()
                        .ok_or_else(|| format!("type error: Dynamic→Int cast failed in {op}"))?,
                ),
                SmtValue::Bool(_) => SmtValue::Bool(
                    d.as_bool()
                        .ok_or_else(|| format!("type error: Dynamic→Bool cast failed in {op}"))?,
                ),
                SmtValue::Real(_) => SmtValue::Real(
                    d.as_real()
                        .ok_or_else(|| format!("type error: Dynamic→Real cast failed in {op}"))?,
                ),
                SmtValue::Dynamic(d2) => {
                    if let Some(i) = d.as_int() {
                        SmtValue::Int(i)
                    } else if let Some(b) = d.as_bool() {
                        SmtValue::Bool(b)
                    } else {
                        // Both operands are genuine Dynamic (e.g., ADT sorts) —
                        // use Z3 generic equality/inequality directly.
                        return match op {
                            "OpEq" => Ok(SmtValue::Bool(d.eq(d2.clone()))),
                            "OpNEq" => Ok(SmtValue::Bool(d.eq(d2.clone()).not())),
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
    #[allow(unused_imports)]
    use z3::ast::Ast;
    match op {
        "OpNot" | "not" => Ok(SmtValue::Bool(val.as_bool()?.not())),
        "OpNeg" | "-" => Ok(SmtValue::Int(Int::unary_minus(val.as_int()?))),

        // Collection unary operations
        "OpSetEmpty" => {
            use z3::ast::Ast;
            let arr = val.as_array()?;
            let sort = arr.get_sort();
            let empty = z3::ast::Array::const_array(
                &sort.array_domain().unwrap(),
                &z3::ast::Bool::from_bool(false),
            );
            Ok(SmtValue::Bool(arr.eq(empty)))
        }
        "OpSetSize" => {
            // Set size via cardinality — reuse existing Card encoding path
            Err("Set::size should use # (cardinality) operator".to_owned())
        }
        "OpSeqHead" => {
            let arr = val.as_array()?;
            let zero = Int::from_i64(0);
            Ok(SmtValue::Dynamic(arr.select(&Dynamic::from_ast(&zero))))
        }
        "OpSeqTail" => {
            // Tail is complex: shift indices by -1. For now, return as-is.
            // Full implementation needs auxiliary length tracking.
            Err("Seq::tail requires length tracking (not yet implemented in pure expr)".to_owned())
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
        // See DDR-047.

        _ => Err(format!("unsupported unop: {op}")),
    }
}
