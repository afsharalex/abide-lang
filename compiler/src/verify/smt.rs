//! Z3 value types and sort mapping.
//!
//! Provides the `SmtValue` enum that wraps Z3 AST nodes, and functions
//! to create Z3 sorts from Abide IR types.
//!
//! Uses z3 crate v0.19 API (no explicit Context parameter — global context).

use z3::ast::{Bool, Dynamic, Int, Real};
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
    /// Z3 uninterpreted/dynamic sort — used for complex types.
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

    /// Convert to a Bool (for use in assertions).
    /// Int → Bool via (int != 0), Bool → Bool, others panic.
    pub fn to_bool(&self) -> Bool {
        match self {
            SmtValue::Bool(b) => b.clone(),
            SmtValue::Int(i) => i.eq(Int::from_i64(0)).not(),
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
        IRType::Set { .. } => Sort::int(), // sets handled separately
        IRType::Seq { .. } => Sort::int(), // sequences as uninterpreted for now
        IRType::Map { .. } => Sort::int(), // maps handled via Z3 arrays separately
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

        // Composition operators — encode as boolean combinators for now
        ("OpSeq", SmtValue::Bool(a), SmtValue::Bool(b)) => SmtValue::Bool(a.implies(b)),
        ("OpSameStep", SmtValue::Bool(a), SmtValue::Bool(b)) => SmtValue::Bool(Bool::and(&[a, b])),
        ("OpUnord", SmtValue::Bool(a), SmtValue::Bool(b)) => SmtValue::Bool(Bool::and(&[a, b])),
        ("OpConc", SmtValue::Bool(a), SmtValue::Bool(b)) => SmtValue::Bool(Bool::and(&[a, b])),
        ("OpXor", SmtValue::Bool(a), SmtValue::Bool(b)) => SmtValue::Bool(Bool::xor(a, b)),

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
