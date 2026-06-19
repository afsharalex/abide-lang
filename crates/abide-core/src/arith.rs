//! Shared integer-arithmetic semantics for the concrete evaluators.
//!
//! The explicit-state checker (`abide-verify`) and the witness/QA simulator
//! (`abide`) must agree with each other — and with the SMT backend's `div`/`mod`
//! — on integer arithmetic. This module is the single source of truth for that
//! contract so the semantics can never drift between the two re-implementations:
//!
//! - `+`, `-`, `*` are **checked**: an `i64` overflow is a conservative error,
//!   never a panic and never a silent two's-complement wrap. Wrapping would
//!   diverge from the SMT backend, whose `Int` is unbounded; erroring keeps the
//!   concrete evaluators from materializing a value the solver never computed.
//! - `/` and `%` are **Euclidean** (remainder in `[0, |b|)`), matching the
//!   SMT-LIB `div`/`mod` the solver backends emit, so a verified property and a
//!   concrete witness agree on negative operands. Division/modulo by zero, and
//!   the `i64::MIN / -1` overflow, are undefined and rejected.
//!
//! The SMT backend keeps `div`/`mod` total and instead discharges a
//! reachability-aware div-by-zero well-definedness obligation, so a reachable
//! zero divisor surfaces as `Unprovable` rather than an arbitrary solver value.
//! The two sides are therefore consistent: the concrete evaluators refuse to
//! evaluate a zero divisor, and the solver path refuses to *prove around* one.

use core::fmt;

/// Why an integer operation has no well-defined `i64` result.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntArithError {
    /// `+`, `-`, or `*` overflowed the `i64` range. The payload names the
    /// operation for the diagnostic.
    Overflow(&'static str),
    /// The divisor of `/` was zero.
    DivByZero,
    /// The divisor of `%` was zero.
    ModByZero,
    /// `i64::MIN / -1` (or the analogous `%`) has no `i64` result.
    DivOverflow,
}

impl fmt::Display for IntArithError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IntArithError::Overflow(op) => write!(f, "integer {op} overflowed the i64 range"),
            IntArithError::DivByZero => write!(f, "division by zero"),
            IntArithError::ModByZero => write!(f, "modulo by zero"),
            IntArithError::DivOverflow => {
                write!(f, "integer division overflow (i64::MIN / -1)")
            }
        }
    }
}

/// Result of an integer operation that may be undefined on `i64`.
pub type IntResult = Result<i64, IntArithError>;

/// Checked integer addition: overflow is an error, never a wrap or panic.
pub fn add(a: i64, b: i64) -> IntResult {
    a.checked_add(b).ok_or(IntArithError::Overflow("addition"))
}

/// Checked integer subtraction: overflow is an error, never a wrap or panic.
pub fn sub(a: i64, b: i64) -> IntResult {
    a.checked_sub(b)
        .ok_or(IntArithError::Overflow("subtraction"))
}

/// Checked integer multiplication: overflow is an error, never a wrap or panic.
pub fn mul(a: i64, b: i64) -> IntResult {
    a.checked_mul(b)
        .ok_or(IntArithError::Overflow("multiplication"))
}

/// Euclidean integer division (`/`): remainder is always in `[0, |b|)`.
/// A zero divisor is [`IntArithError::DivByZero`]; `i64::MIN / -1` is
/// [`IntArithError::DivOverflow`].
pub fn div_euclid(a: i64, b: i64) -> IntResult {
    if b == 0 {
        return Err(IntArithError::DivByZero);
    }
    a.checked_div_euclid(b).ok_or(IntArithError::DivOverflow)
}

/// Euclidean integer remainder (`%`): the result is always in `[0, |b|)`.
/// A zero divisor is [`IntArithError::ModByZero`]; the `i64::MIN`/`-1` case is
/// [`IntArithError::DivOverflow`].
pub fn rem_euclid(a: i64, b: i64) -> IntResult {
    if b == 0 {
        return Err(IntArithError::ModByZero);
    }
    a.checked_rem_euclid(b).ok_or(IntArithError::DivOverflow)
}

/// Checked integer negation (unary `-`): `-i64::MIN` has no `i64` result and is
/// an [`IntArithError::Overflow`], never a panic or a wrap. The SMT backend's
/// `int_neg` is unbounded, so erroring keeps the concrete evaluators from
/// materializing a wrapped value the solver never computed.
pub fn neg(a: i64) -> IntResult {
    a.checked_neg().ok_or(IntArithError::Overflow("negation"))
}

/// Fixed-point scale for the canonical real-number semantics: real (and IEEE
/// `float`) literals are represented in millionths — six decimal places, with
/// the seventh and beyond truncated toward zero (see [`real_to_rational`]).
/// Every backend shares this scale so the SMT encoding and the concrete witness
/// agree on a literal's value instead of one truncating where the other keeps
/// full `f64` precision.
pub const REAL_SCALE: i64 = 1_000_000;

/// Convert a real literal to the canonical rational `(numerator, REAL_SCALE)`
/// the SMT backends encode. The value is scaled by [`REAL_SCALE`] and
/// **truncated toward zero** to an integer numerator; the `f64`→`i64` cast also
/// saturates (Rust semantics), so a non-finite or out-of-range value yields a
/// saturated/zero numerator rather than panicking.
#[must_use]
pub fn real_to_rational(value: f64) -> (i64, i64) {
    #[allow(clippy::cast_possible_truncation)]
    let scaled = (value * REAL_SCALE as f64) as i64;
    (scaled, REAL_SCALE)
}

/// The canonical real value: `value` quantized to [`REAL_SCALE`]. The concrete
/// evaluators apply this to a real literal so a witnessed real matches the
/// quantized value the SMT model reasons about.
#[must_use]
pub fn canonical_real(value: f64) -> f64 {
    let (num, den) = real_to_rational(value);
    #[allow(clippy::cast_precision_loss)]
    {
        num as f64 / den as f64
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn euclidean_division_rounds_toward_negative_infinity_remainder() {
        // The canonical contract cases shared by every backend.
        assert_eq!(div_euclid(-7, 2), Ok(-4));
        assert_eq!(rem_euclid(-7, 2), Ok(1));
        assert_eq!(div_euclid(7, -2), Ok(-3));
        assert_eq!(rem_euclid(7, -2), Ok(1));
        assert_eq!(div_euclid(7, 2), Ok(3));
        assert_eq!(rem_euclid(7, 2), Ok(1));
        // Remainder is never negative.
        for a in -5i64..=5 {
            for b in [-3i64, -1, 1, 3] {
                assert!((0..b.abs()).contains(&rem_euclid(a, b).unwrap()));
            }
        }
    }

    #[test]
    fn division_and_modulo_by_zero_are_distinct_errors() {
        assert_eq!(div_euclid(5, 0), Err(IntArithError::DivByZero));
        assert_eq!(rem_euclid(5, 0), Err(IntArithError::ModByZero));
    }

    #[test]
    fn integer_arithmetic_errors_have_specific_display_messages() {
        assert_eq!(
            IntArithError::Overflow("addition").to_string(),
            "integer addition overflowed the i64 range"
        );
        assert_eq!(IntArithError::DivByZero.to_string(), "division by zero");
        assert_eq!(IntArithError::ModByZero.to_string(), "modulo by zero");
        assert_eq!(
            IntArithError::DivOverflow.to_string(),
            "integer division overflow (i64::MIN / -1)"
        );
    }

    #[test]
    fn min_over_negative_one_overflows() {
        assert_eq!(div_euclid(i64::MIN, -1), Err(IntArithError::DivOverflow));
        assert_eq!(rem_euclid(i64::MIN, -1), Err(IntArithError::DivOverflow));
    }

    #[test]
    fn add_sub_mul_reject_overflow_instead_of_wrapping() {
        assert_eq!(add(i64::MAX, 1), Err(IntArithError::Overflow("addition")));
        assert_eq!(
            sub(i64::MIN, 1),
            Err(IntArithError::Overflow("subtraction"))
        );
        assert_eq!(
            mul(i64::MAX, 2),
            Err(IntArithError::Overflow("multiplication"))
        );
        // In-range arithmetic is unaffected.
        assert_eq!(add(2, 3), Ok(5));
        assert_eq!(sub(2, 3), Ok(-1));
        assert_eq!(mul(6, 7), Ok(42));
    }

    #[test]
    fn negation_rejects_min_overflow_instead_of_wrapping() {
        // `-i64::MIN` has no i64 result: an error, never a panic or a wrap to
        // `i64::MIN` (which would diverge from the SMT backend's unbounded neg).
        assert_eq!(neg(i64::MIN), Err(IntArithError::Overflow("negation")));
        assert_eq!(neg(5), Ok(-5));
        assert_eq!(neg(-5), Ok(5));
        assert_eq!(neg(0), Ok(0));
        assert_eq!(neg(i64::MAX), Ok(-i64::MAX));
    }

    #[test]
    fn real_literals_quantize_to_the_shared_scale() {
        // Exactly representable reals are unchanged.
        assert_eq!(real_to_rational(0.5), (500_000, REAL_SCALE));
        assert_eq!(real_to_rational(1.5), (1_500_000, REAL_SCALE));
        assert_eq!(real_to_rational(-0.25), (-250_000, REAL_SCALE));
        assert_eq!(real_to_rational(0.0), (0, REAL_SCALE));
        // Beyond six decimals the value is truncated toward zero — the same
        // quantization the SMT backend applies — and `canonical_real` reflects it.
        assert_eq!(real_to_rational(0.123_456_7), (123_456, REAL_SCALE));
        assert!((canonical_real(0.123_456_7) - 0.123_456).abs() < 1e-9);
        // Non-finite / out-of-range inputs saturate instead of panicking.
        let _ = real_to_rational(f64::NAN);
        let _ = real_to_rational(f64::INFINITY);
        let _ = canonical_real(f64::MAX);
    }
}
