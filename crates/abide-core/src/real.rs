//! Exact rational real arithmetic for the concrete evaluators.
//!
//! The SMT backends reason about reals as exact rationals (the Z3/cvc5 `Real`
//! sort): real literals are quantized to [`crate::arith::REAL_SCALE`], but
//! intermediate results stay exact, so `1/3 + 1/3 + 1/3 == 1`. For the
//! witness/QA simulator to agree with the solver when it forward-simulates real
//! arithmetic, it must use the same exact-rational semantics rather than `f64`
//! (which would diverge — e.g. `1.0 / 3.0` would round).
//!
//! [`Real`] is a reduced `i128` rational with positive denominator. Arithmetic
//! is checked: an `i128` overflow is a conservative [`RealArithError::Overflow`]
//! (matching the integer contract in [`crate::arith`]), never a panic or a
//! silently wrapped/rounded value. Division by zero is rejected.

use core::cmp::Ordering;
use core::fmt;
use core::str::FromStr;

use crate::arith;

/// Why a real operation has no well-defined exact-rational result.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RealArithError {
    /// The divisor of `/` was zero.
    DivByZero,
    /// The divisor of `%` was zero.
    ModByZero,
    /// An `i128` numerator/denominator overflowed during the operation.
    Overflow,
    /// A string could not be parsed as a real value.
    Parse,
}

impl fmt::Display for RealArithError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RealArithError::DivByZero => write!(f, "real division by zero"),
            RealArithError::ModByZero => write!(f, "real modulo by zero"),
            RealArithError::Overflow => write!(f, "real arithmetic overflowed the i128 range"),
            RealArithError::Parse => write!(f, "could not parse a real value"),
        }
    }
}

/// Largest number of fractional digits considered when rendering a real as a
/// terminating decimal before falling back to `num/den` form.
const MAX_DECIMAL_DIGITS: usize = 40;

/// An exact rational real number `num/den` in lowest terms with `den > 0`.
#[derive(Debug, Clone, Copy)]
pub struct Real {
    num: i128,
    den: i128,
}

impl Real {
    /// The rational `0`.
    pub const ZERO: Real = Real { num: 0, den: 1 };

    /// Build a reduced rational from `num/den`, rejecting a zero denominator and
    /// any reduction step that would overflow `i128`.
    pub fn from_parts(num: i128, den: i128) -> Result<Real, RealArithError> {
        let (num, den) = match den.cmp(&0) {
            Ordering::Equal => return Err(RealArithError::DivByZero),
            // Normalize the sign onto the numerator.
            Ordering::Less => (
                num.checked_neg().ok_or(RealArithError::Overflow)?,
                den.checked_neg().ok_or(RealArithError::Overflow)?,
            ),
            Ordering::Greater => (num, den),
        };
        let g = gcd(num.unsigned_abs(), den.unsigned_abs());
        // `g` is non-zero because `den != 0`.
        let g = g as i128;
        Ok(Real {
            num: num / g,
            den: den / g,
        })
    }

    /// An integer real value.
    #[must_use]
    pub fn from_int(value: i64) -> Real {
        Real {
            num: i128::from(value),
            den: 1,
        }
    }

    /// Build a real from an `f64` literal, quantized to the shared
    /// [`REAL_SCALE`] exactly as the SMT backends quantize real literals.
    #[must_use]
    pub fn from_f64_literal(value: f64) -> Real {
        let (num, den) = arith::real_to_rational(value);
        // `den` is `REAL_SCALE` (non-zero), so reduction always succeeds.
        Real::from_parts(i128::from(num), i128::from(den)).unwrap_or(Real::ZERO)
    }

    /// Checked addition.
    pub fn checked_add(self, other: Real) -> Result<Real, RealArithError> {
        let ad = mul(self.num, other.den)?;
        let cb = mul(other.num, self.den)?;
        let num = ad.checked_add(cb).ok_or(RealArithError::Overflow)?;
        let den = mul(self.den, other.den)?;
        Real::from_parts(num, den)
    }

    /// Checked subtraction.
    pub fn checked_sub(self, other: Real) -> Result<Real, RealArithError> {
        let ad = mul(self.num, other.den)?;
        let cb = mul(other.num, self.den)?;
        let num = ad.checked_sub(cb).ok_or(RealArithError::Overflow)?;
        let den = mul(self.den, other.den)?;
        Real::from_parts(num, den)
    }

    /// Checked multiplication.
    pub fn checked_mul(self, other: Real) -> Result<Real, RealArithError> {
        Real::from_parts(mul(self.num, other.num)?, mul(self.den, other.den)?)
    }

    /// Checked division. Dividing by zero is [`RealArithError::DivByZero`].
    pub fn checked_div(self, other: Real) -> Result<Real, RealArithError> {
        if other.num == 0 {
            return Err(RealArithError::DivByZero);
        }
        Real::from_parts(mul(self.num, other.den)?, mul(self.den, other.num)?)
    }

    /// Negation. `den` is positive and unchanged, so this only fails if the
    /// numerator is `i128::MIN` (unreachable for reduced values from `i64`
    /// literals, but checked anyway).
    pub fn checked_neg(self) -> Result<Real, RealArithError> {
        Ok(Real {
            num: self.num.checked_neg().ok_or(RealArithError::Overflow)?,
            den: self.den,
        })
    }

    /// Euclidean remainder (`%`): `r = self - |other| * floor(self / |other|)`,
    /// always in `[0, |other|)`, matching the integer `%` in [`crate::arith`].
    /// A zero divisor is [`RealArithError::ModByZero`]; intermediate `i128`
    /// overflow is a conservative [`RealArithError::Overflow`].
    pub fn checked_rem_euclid(self, other: Real) -> Result<Real, RealArithError> {
        if other.num == 0 {
            return Err(RealArithError::ModByZero);
        }
        let abs_other = Real {
            num: other.num.checked_abs().ok_or(RealArithError::Overflow)?,
            den: other.den,
        };
        // floor(self / |other|): both are exact rationals; the quotient's
        // floor is `num.div_euclid(den)` since the denominator is positive.
        let quotient = self.checked_div(abs_other)?;
        let q = quotient.num.div_euclid(quotient.den);
        self.checked_sub(abs_other.checked_mul(Real::from_parts(q, 1)?)?)
    }

    /// Render as a terminating decimal when the denominator's only prime
    /// factors are 2 and 5 (within [`MAX_DECIMAL_DIGITS`] places); otherwise
    /// return `None` so the caller falls back to `num/den` form.
    fn to_terminating_decimal(self) -> Option<String> {
        let den = self.den.unsigned_abs();
        let int_part = self.num.unsigned_abs() / den;
        let mut rem = self.num.unsigned_abs() % den;
        let mut digits = String::new();
        while rem != 0 {
            if digits.len() >= MAX_DECIMAL_DIGITS {
                return None;
            }
            rem = rem.checked_mul(10)?;
            #[allow(clippy::cast_possible_truncation)]
            digits.push(char::from(b'0' + (rem / den) as u8));
            rem %= den;
        }
        let mut out = String::new();
        if self.num < 0 {
            out.push('-');
        }
        out.push_str(&int_part.to_string());
        if !digits.is_empty() {
            out.push('.');
            out.push_str(&digits);
        }
        Some(out)
    }
}

impl PartialEq for Real {
    fn eq(&self, other: &Self) -> bool {
        // Both are reduced with positive denominator, so structural equality is
        // value equality.
        self.num == other.num && self.den == other.den
    }
}

impl Eq for Real {}

impl PartialOrd for Real {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Real {
    /// Total order on the rationals, computed **exactly** with no overflow.
    ///
    /// A cross-multiplying comparison (`a*d` vs `c*b`) would overflow `i128` for
    /// large operands and silently lose the answer; instead this uses the
    /// continued-fraction comparison, which only ever divides and takes
    /// remainders (never multiplies), so two distinct rationals always compare
    /// as distinct regardless of magnitude.
    fn cmp(&self, other: &Self) -> Ordering {
        cmp_fractions(self.num, self.den, other.num, other.den)
    }
}

impl fmt::Display for Real {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.den == 1 {
            return write!(f, "{}", self.num);
        }
        match self.to_terminating_decimal() {
            Some(decimal) => write!(f, "{decimal}"),
            None => write!(f, "{}/{}", self.num, self.den),
        }
    }
}

impl FromStr for Real {
    type Err = RealArithError;

    fn from_str(s: &str) -> Result<Real, RealArithError> {
        let s = s.trim();
        if s.is_empty() {
            return Err(RealArithError::Parse);
        }
        // Exact fraction form `num/den`.
        if let Some((num, den)) = s.split_once('/') {
            let num: i128 = num.trim().parse().map_err(|_| RealArithError::Parse)?;
            let den: i128 = den.trim().parse().map_err(|_| RealArithError::Parse)?;
            return Real::from_parts(num, den);
        }
        // Decimal or integer form.
        let (sign, body) = match s.strip_prefix('-') {
            Some(rest) => (-1i128, rest),
            None => (1, s.strip_prefix('+').unwrap_or(s)),
        };
        let (int_str, frac_str) = match body.split_once('.') {
            Some((i, f)) => (i, f),
            None => (body, ""),
        };
        if int_str.is_empty() && frac_str.is_empty() {
            return Err(RealArithError::Parse);
        }
        let int_part: i128 = if int_str.is_empty() {
            0
        } else {
            int_str.parse().map_err(|_| RealArithError::Parse)?
        };
        if frac_str.is_empty() {
            return Real::from_parts(sign * int_part, 1);
        }
        if !frac_str.bytes().all(|b| b.is_ascii_digit()) {
            return Err(RealArithError::Parse);
        }
        let frac_digits = u32::try_from(frac_str.len()).map_err(|_| RealArithError::Parse)?;
        let den = 10i128
            .checked_pow(frac_digits)
            .ok_or(RealArithError::Overflow)?;
        let frac_part: i128 = frac_str.parse().map_err(|_| RealArithError::Parse)?;
        let scaled_int = int_part.checked_mul(den).ok_or(RealArithError::Overflow)?;
        let num = scaled_int
            .checked_add(frac_part)
            .ok_or(RealArithError::Overflow)?;
        Real::from_parts(sign * num, den)
    }
}

/// Checked `i128` multiplication mapping overflow to [`RealArithError::Overflow`].
fn mul(a: i128, b: i128) -> Result<i128, RealArithError> {
    a.checked_mul(b).ok_or(RealArithError::Overflow)
}

/// Compare `a/b` against `c/d` (with `b > 0`, `d > 0`) exactly and without
/// overflow, via the continued-fraction algorithm: compare the integer (floor)
/// parts; on a tie, compare the fractional remainders, which by reciprocal
/// equivalence (`r1/b < r2/d  ⟺  d/r2 < b/r1`) reduces to comparing the swapped
/// fractions. The operands strictly shrink each step (like Euclid's gcd), so it
/// terminates, and it only divides/takes remainders — never multiplies — so it
/// cannot overflow.
fn cmp_fractions(mut a: i128, mut b: i128, mut c: i128, mut d: i128) -> Ordering {
    loop {
        let (q1, q2) = (a.div_euclid(b), c.div_euclid(d));
        if q1 != q2 {
            return q1.cmp(&q2);
        }
        // Euclidean remainders lie in `[0, b)` / `[0, d)`, so the fractional
        // parts are non-negative even when `a` or `c` is negative.
        let (r1, r2) = (a.rem_euclid(b), c.rem_euclid(d));
        match (r1 == 0, r2 == 0) {
            (true, true) => return Ordering::Equal,
            (true, false) => return Ordering::Less,
            (false, true) => return Ordering::Greater,
            // Compare `r1/b` vs `r2/d` by comparing the reciprocals `d/r2` vs
            // `b/r1` (the same order, since reciprocating both flips it twice).
            (false, false) => {
                (a, b, c, d) = (d, r2, b, r1);
            }
        }
    }
}

/// Greatest common divisor (Euclid). `gcd(0, n) == n`, `gcd(0, 0) == 0`.
fn gcd(mut a: u128, mut b: u128) -> u128 {
    // Euclid over u128 terminates in far fewer than 256 iterations; the cap is
    // defensive and keeps broken arithmetic from hanging callers indefinitely.
    for _ in 0..256 {
        if b == 0 {
            return a.max(1);
        }
        let t = b;
        b = a % b;
        a = t;
    }
    a.max(1)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arith::REAL_SCALE;

    fn r(num: i128, den: i128) -> Real {
        Real::from_parts(num, den).unwrap()
    }

    #[test]
    fn literals_quantize_like_the_smt_backend() {
        assert_eq!(Real::from_f64_literal(0.5), r(1, 2));
        assert_eq!(Real::from_f64_literal(2.0), r(2, 1));
        assert_eq!(Real::from_f64_literal(-0.25), r(-1, 4));
        // Beyond six decimals the literal truncates to REAL_SCALE, matching SMT.
        assert_eq!(
            Real::from_f64_literal(0.123_456_7),
            r(123_456, REAL_SCALE.into())
        );
    }

    #[test]
    fn arithmetic_is_exact_not_rounded() {
        let third = r(1, 3);
        // 1/3 + 1/3 + 1/3 == 1 exactly (an f64 sum would not).
        assert_eq!(
            third
                .checked_add(third)
                .unwrap()
                .checked_add(third)
                .unwrap(),
            r(1, 1)
        );
        // 1/3 stays 1/3 rather than 0.333333.
        assert_eq!(r(1, 1).checked_div(r(3, 1)).unwrap(), third);
        assert_eq!(r(1, 2).checked_mul(r(2, 1)).unwrap(), r(1, 1));
        assert_eq!(r(1, 2).checked_sub(r(1, 4)).unwrap(), r(1, 4));
        assert_eq!(r(1, 1).checked_neg().unwrap(), r(-1, 1));
    }

    #[test]
    fn division_by_zero_is_rejected() {
        assert_eq!(
            r(1, 2).checked_div(Real::ZERO),
            Err(RealArithError::DivByZero)
        );
        assert_eq!(Real::from_parts(1, 0), Err(RealArithError::DivByZero));
    }

    #[test]
    fn real_arithmetic_errors_have_specific_display_messages() {
        assert_eq!(
            RealArithError::DivByZero.to_string(),
            "real division by zero"
        );
        assert_eq!(RealArithError::ModByZero.to_string(), "real modulo by zero");
        assert_eq!(
            RealArithError::Overflow.to_string(),
            "real arithmetic overflowed the i128 range"
        );
        assert_eq!(
            RealArithError::Parse.to_string(),
            "could not parse a real value"
        );
    }

    #[test]
    fn construction_normalizes_negative_denominators() {
        assert_eq!(Real::from_parts(1, -2), Ok(r(-1, 2)));
        assert_eq!(Real::from_parts(-1, -2), Ok(r(1, 2)));
        assert_eq!(Real::from_parts(0, -5), Ok(r(0, 1)));
    }

    #[test]
    fn euclidean_remainder_is_exact_and_non_negative() {
        // 7.5 % 2 == 1.5; -7.5 % 2 == 0.5 (Euclidean: result in [0, |b|)).
        assert_eq!(r(15, 2).checked_rem_euclid(r(2, 1)), Ok(r(3, 2)));
        assert_eq!(r(-15, 2).checked_rem_euclid(r(2, 1)), Ok(r(1, 2)));
        // Negative divisor: remainder still in [0, |b|).
        assert_eq!(r(15, 2).checked_rem_euclid(r(-2, 1)), Ok(r(3, 2)));
        // Exact rational result: (1/3) % (1/4) == 1/12.
        assert_eq!(r(1, 3).checked_rem_euclid(r(1, 4)), Ok(r(1, 12)));
        // Zero divisor is rejected.
        assert_eq!(
            r(1, 2).checked_rem_euclid(Real::ZERO),
            Err(RealArithError::ModByZero)
        );
    }

    #[test]
    fn overflow_is_a_conservative_error_not_a_panic() {
        let big = r(i128::MAX / 2, 1);
        assert_eq!(
            big.checked_add(big).and_then(|x| x.checked_add(big)),
            Err(RealArithError::Overflow)
        );
    }

    #[test]
    fn ordering_uses_exact_values() {
        assert!(r(1, 3) < r(1, 2));
        assert!(r(2, 4) == r(1, 2));
        assert!(r(-1, 2) < r(0, 1));
        assert_eq!(r(1, 3).cmp(&r(1, 3)), Ordering::Equal);
    }

    #[test]
    fn ordering_is_exact_even_when_cross_multiplication_would_overflow() {
        // `num * den` here exceeds i128, so a cross-multiplying comparison would
        // overflow; the continued-fraction comparison stays exact.
        assert!(r(i128::MAX, 2) > r(i128::MAX, 3));
        assert!(r(i128::MAX, 3) < r(i128::MAX, 2));
        // Two distinct rationals both just above 1 that an f64 fallback would
        // collapse to the same value must still compare as distinct:
        // M/(M-1) = 1 + 1/(M-1) < 1 + 1/(M-2) = (M-1)/(M-2).
        let a = r(i128::MAX, i128::MAX - 1);
        let b = r(i128::MAX - 1, i128::MAX - 2);
        assert_ne!(a, b);
        assert!(a < b);
        assert!(b > a);
        // Large negative magnitudes compare exactly too.
        assert!(r(-i128::MAX, 2) < r(-i128::MAX, 3));
    }

    #[test]
    fn display_uses_decimal_when_terminating_and_fraction_otherwise() {
        assert_eq!(r(1, 2).to_string(), "0.5");
        assert_eq!(r(-1, 4).to_string(), "-0.25");
        assert_eq!(r(2, 1).to_string(), "2");
        assert_eq!(r(0, 1).to_string(), "0");
        assert_eq!(
            Real { num: 0, den: 2 }.to_terminating_decimal(),
            Some("0".to_owned())
        );
        assert_eq!(r(123_456, REAL_SCALE.into()).to_string(), "0.123456");
        // 1/3 does not terminate, so it renders as an exact fraction.
        assert_eq!(r(1, 3).to_string(), "1/3");
        assert_eq!(r(2, 3).to_string(), "2/3");
    }

    #[test]
    fn structural_equality_requires_matching_reduced_parts() {
        assert_ne!(Real { num: 1, den: 2 }, Real { num: 1, den: 3 });
        assert_ne!(Real { num: 1, den: 2 }, Real { num: 2, den: 2 });
        assert_eq!(Real { num: 1, den: 2 }, Real { num: 1, den: 2 });
    }

    #[test]
    fn parse_round_trips_decimals_fractions_and_integers() {
        assert_eq!("0.5".parse::<Real>().unwrap(), r(1, 2));
        assert_eq!("-1.5".parse::<Real>().unwrap(), r(-3, 2));
        assert_eq!("2".parse::<Real>().unwrap(), r(2, 1));
        assert_eq!("0".parse::<Real>().unwrap(), r(0, 1));
        assert_eq!("1/3".parse::<Real>().unwrap(), r(1, 3));
        assert_eq!(
            "0.123456".parse::<Real>().unwrap(),
            r(123_456, REAL_SCALE.into())
        );
        // Parse ∘ Display is the identity on values.
        for value in [r(1, 2), r(1, 3), r(-3, 2), r(2, 1), r(0, 1), r(7, 8)] {
            assert_eq!(value.to_string().parse::<Real>().unwrap(), value);
        }
        assert!("".parse::<Real>().is_err());
        assert!("abc".parse::<Real>().is_err());
        assert!("1/0".parse::<Real>().is_err());
    }

    #[test]
    fn gcd_reduces_coprime_and_composite_values() {
        assert_eq!(gcd(10, 3), 1);
        assert_eq!(gcd(48, 18), 6);
        assert_eq!(gcd(0, 7), 7);
        assert_eq!(gcd(0, 0), 1);
    }
}
