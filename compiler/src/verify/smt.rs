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
}

impl SmtValue {
    /// Extract as Bool, panics if wrong variant.
    pub fn as_bool(&self) -> &Bool {
        match self {
            SmtValue::Bool(b) => b,
            other => panic!("expected Bool, got {other:?}"),
        }
    }

    /// Extract as Int, panics if wrong variant.
    pub fn as_int(&self) -> &Int {
        match self {
            SmtValue::Int(i) => i,
            other => panic!("expected Int, got {other:?}"),
        }
    }

    /// Extract as Real, panics if wrong variant.
    pub fn as_real(&self) -> &Real {
        match self {
            SmtValue::Real(r) => r,
            other => panic!("expected Real, got {other:?}"),
        }
    }

    /// Extract as Array, panics if wrong variant.
    pub fn as_array(&self) -> &Array {
        match self {
            SmtValue::Array(a) => a,
            other => panic!("expected Array, got {other:?}"),
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
        }
    }

    /// Convert to a Bool (for use in assertions).
    /// Int → Bool via (int != 0), Bool → Bool, Dynamic → Bool (sort cast), others panic.
    pub fn to_bool(&self) -> Bool {
        match self {
            SmtValue::Bool(b) => b.clone(),
            SmtValue::Int(i) => i.eq(Int::from_i64(0)).not(),
            SmtValue::Dynamic(d) => d
                .as_bool()
                .unwrap_or_else(|| panic!("cannot convert Dynamic to Bool: {d:?}")),
            _ => panic!("cannot convert {self:?} to Bool"),
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
pub fn array_var(name: &str, ty: &IRType) -> SmtValue {
    let sort = ir_type_to_sort(ty);
    let domain = sort.array_domain().expect("array_var requires array sort");
    let range = sort.array_range().expect("array_var requires array sort");
    SmtValue::Array(Array::new_const(name, &domain, &range))
}

/// Assert that two `SmtValue`s are equal, returning a Z3 Bool constraint.
///
/// Handles same-variant pairs directly. For cross-variant pairs involving
/// Dynamic (e.g., `Array::select` result vs Int field), coerces the typed
/// operand to Dynamic and uses Z3's generic equality.
pub fn smt_eq(a: &SmtValue, b: &SmtValue) -> Bool {
    match (a, b) {
        (SmtValue::Int(x), SmtValue::Int(y)) => x.eq(y.clone()),
        (SmtValue::Bool(x), SmtValue::Bool(y)) => x.eq(y.clone()),
        (SmtValue::Real(x), SmtValue::Real(y)) => x.eq(y.clone()),
        (SmtValue::Array(x), SmtValue::Array(y)) => x.eq(y.clone()),
        (SmtValue::Dynamic(x), SmtValue::Dynamic(y)) => x.eq(y.clone()),
        // Cross-variant: coerce both to Dynamic for Z3's generic equality
        (SmtValue::Dynamic(d), other) | (other, SmtValue::Dynamic(d)) => d.eq(other.to_dynamic()),
        _ => panic!("sort mismatch in smt_eq: {a:?} vs {b:?}"),
    }
}

// ── Binary operations ───────────────────────────────────────────────

/// Apply a binary operation to two `SmtValue`s.
///
/// Returns the result as an `SmtValue`. Operand types must match.
#[allow(clippy::too_many_lines, clippy::match_same_arms)]
pub fn binop(op: &str, lhs: &SmtValue, rhs: &SmtValue) -> SmtValue {
    match (op, lhs, rhs) {
        // Arithmetic (Int) — IR emits "OpAdd", "OpSub", etc.
        ("OpAdd", SmtValue::Int(a), SmtValue::Int(b)) => SmtValue::Int(Int::add(&[a, b])),
        ("OpSub", SmtValue::Int(a), SmtValue::Int(b)) => SmtValue::Int(Int::sub(&[a, b])),
        ("OpMul", SmtValue::Int(a), SmtValue::Int(b)) => SmtValue::Int(Int::mul(&[a, b])),
        ("OpDiv", SmtValue::Int(a), SmtValue::Int(b)) => SmtValue::Int(a.div(b)),
        ("OpMod", SmtValue::Int(a), SmtValue::Int(b)) => SmtValue::Int(a.modulo(b)),

        // Arithmetic (Real)
        ("OpAdd", SmtValue::Real(a), SmtValue::Real(b)) => SmtValue::Real(Real::add(&[a, b])),
        ("OpSub", SmtValue::Real(a), SmtValue::Real(b)) => SmtValue::Real(Real::sub(&[a, b])),
        ("OpMul", SmtValue::Real(a), SmtValue::Real(b)) => SmtValue::Real(Real::mul(&[a, b])),
        ("OpDiv", SmtValue::Real(a), SmtValue::Real(b)) => SmtValue::Real(Real::div(a, b)),

        // Comparison (Int)
        ("OpEq", SmtValue::Int(a), SmtValue::Int(b)) => SmtValue::Bool(a.eq(b)),
        ("OpNEq", SmtValue::Int(a), SmtValue::Int(b)) => SmtValue::Bool(a.eq(b).not()),
        ("OpLt", SmtValue::Int(a), SmtValue::Int(b)) => SmtValue::Bool(a.lt(b)),
        ("OpGt", SmtValue::Int(a), SmtValue::Int(b)) => SmtValue::Bool(a.gt(b)),
        ("OpLe", SmtValue::Int(a), SmtValue::Int(b)) => SmtValue::Bool(a.le(b)),
        ("OpGe", SmtValue::Int(a), SmtValue::Int(b)) => SmtValue::Bool(a.ge(b)),

        // Comparison (Real)
        ("OpEq", SmtValue::Real(a), SmtValue::Real(b)) => SmtValue::Bool(a.eq(b)),
        ("OpNEq", SmtValue::Real(a), SmtValue::Real(b)) => SmtValue::Bool(a.eq(b).not()),
        ("OpLt", SmtValue::Real(a), SmtValue::Real(b)) => SmtValue::Bool(Real::lt(a, b)),
        ("OpGt", SmtValue::Real(a), SmtValue::Real(b)) => SmtValue::Bool(Real::gt(a, b)),
        ("OpLe", SmtValue::Real(a), SmtValue::Real(b)) => SmtValue::Bool(Real::le(a, b)),
        ("OpGe", SmtValue::Real(a), SmtValue::Real(b)) => SmtValue::Bool(Real::ge(a, b)),

        // Boolean (Bool)
        ("OpEq", SmtValue::Bool(a), SmtValue::Bool(b)) => SmtValue::Bool(a.eq(b)),
        ("OpNEq", SmtValue::Bool(a), SmtValue::Bool(b)) => SmtValue::Bool(a.eq(b).not()),
        ("OpAnd", SmtValue::Bool(a), SmtValue::Bool(b)) => SmtValue::Bool(Bool::and(&[a, b])),
        ("OpOr", SmtValue::Bool(a), SmtValue::Bool(b)) => SmtValue::Bool(Bool::or(&[a, b])),
        ("OpImplies", SmtValue::Bool(a), SmtValue::Bool(b)) => SmtValue::Bool(a.implies(b)),

        // Array equality (Map/Set/Seq)
        ("OpEq", SmtValue::Array(a), SmtValue::Array(b)) => SmtValue::Bool(a.eq(b.clone())),
        ("OpNEq", SmtValue::Array(a), SmtValue::Array(b)) => SmtValue::Bool(a.eq(b.clone()).not()),

        // Composition operators — encode as boolean combinators for now
        ("OpSeq", SmtValue::Bool(a), SmtValue::Bool(b)) => SmtValue::Bool(a.implies(b)),
        ("OpSameStep", SmtValue::Bool(a), SmtValue::Bool(b)) => SmtValue::Bool(Bool::and(&[a, b])),
        ("OpUnord", SmtValue::Bool(a), SmtValue::Bool(b)) => SmtValue::Bool(Bool::and(&[a, b])),
        ("OpConc", SmtValue::Bool(a), SmtValue::Bool(b)) => SmtValue::Bool(Bool::and(&[a, b])),
        ("OpXor", SmtValue::Bool(a), SmtValue::Bool(b)) => SmtValue::Bool(Bool::xor(a, b)),

        // Dynamic operands — from array select, cast to matching type
        (op, SmtValue::Dynamic(d), other) | (op, other, SmtValue::Dynamic(d)) => {
            let coerced = match other {
                SmtValue::Int(_) => SmtValue::Int(
                    d.as_int()
                        .unwrap_or_else(|| panic!("Dynamic→Int cast failed in {op}")),
                ),
                SmtValue::Bool(_) => SmtValue::Bool(
                    d.as_bool()
                        .unwrap_or_else(|| panic!("Dynamic→Bool cast failed in {op}")),
                ),
                SmtValue::Real(_) => SmtValue::Real(
                    d.as_real()
                        .unwrap_or_else(|| panic!("Dynamic→Real cast failed in {op}")),
                ),
                SmtValue::Dynamic(_) => {
                    // Both Dynamic — try Int (most common for map values)
                    if let Some(i) = d.as_int() {
                        SmtValue::Int(i)
                    } else if let Some(b) = d.as_bool() {
                        SmtValue::Bool(b)
                    } else {
                        panic!("cannot resolve Dynamic-Dynamic binop: {op}")
                    }
                }
                SmtValue::Array(_) => panic!("cannot apply {op} to Array operand"),
            };
            if matches!(lhs, SmtValue::Dynamic(_)) {
                binop(op, &coerced, rhs)
            } else {
                binop(op, lhs, &coerced)
            }
        }

        _ => panic!("unsupported binop: {op} on {lhs:?}, {rhs:?}"),
    }
}

/// Negate a boolean or apply unary minus to an int.
/// Accepts IR op names: `"OpNot"`, `"OpNeg"`.
pub fn unop(op: &str, val: &SmtValue) -> SmtValue {
    match op {
        "OpNot" | "not" => SmtValue::Bool(val.as_bool().not()),
        "OpNeg" | "-" => SmtValue::Int(Int::unary_minus(val.as_int())),
        _ => panic!("unsupported unop: {op}"),
    }
}
