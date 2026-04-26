//! CHC/IC3 backend routing.
//!
//! Ordinary SMT solving and CHC solving are related but distinct backend
//! surfaces. The former goes through `smt.rs` and the active ordinary solver
//! family. The latter is routed independently here so IC3/PDR can keep using a
//! reference backend even when SAT/BMC/property solving uses another solver.

use std::cell::RefCell;

use super::smt::ChcResult;
use super::solver::{is_solver_family_available, SolverFamily};

use super::solver::cvc5_check_chc;
use super::solver::z3_check_chc;

/// User-facing CHC backend selection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChcSelection {
    Z3,
    Cvc5,
    Auto,
}

thread_local! {
    static ACTIVE_CHC_FAMILY: RefCell<SolverFamily> = const { RefCell::new(SolverFamily::Z3) };
}

pub fn active_chc_family() -> SolverFamily {
    ACTIVE_CHC_FAMILY.with(|family| *family.borrow())
}

pub fn set_active_chc_family(family: SolverFamily) -> Result<(), String> {
    if !is_solver_family_available(family) {
        return Err(match family {
            SolverFamily::Z3 => "z3 CHC backend is not available".to_owned(),
            SolverFamily::Cvc5 => "cvc5 CHC backend is not available".to_owned(),
        });
    }
    ACTIVE_CHC_FAMILY.with(|active| *active.borrow_mut() = family);
    Ok(())
}

pub fn resolve_chc_family(selection: ChcSelection) -> Result<SolverFamily, String> {
    match selection {
        ChcSelection::Z3 => Ok(SolverFamily::Z3),
        ChcSelection::Cvc5 => {
            if is_solver_family_available(SolverFamily::Cvc5) {
                Ok(SolverFamily::Cvc5)
            } else {
                Err("requested CHC solver `cvc5` is not available".to_owned())
            }
        }
        // Keep CHC `auto` conservative until a second CHC backend reaches
        // parity with the Spacer path and counterexample handling.
        ChcSelection::Auto => Ok(SolverFamily::Z3),
    }
}

pub trait ChcBackend {
    fn family() -> SolverFamily;
    fn check(chc_text: &str, error_relation: &str, timeout_ms: u64) -> ChcResult;
}

pub struct Z3ChcBackend;

impl ChcBackend for Z3ChcBackend {
    fn family() -> SolverFamily {
        SolverFamily::Z3
    }

    fn check(chc_text: &str, error_relation: &str, timeout_ms: u64) -> ChcResult {
        z3_check_chc(chc_text, error_relation, timeout_ms)
    }
}

pub struct Cvc5ChcBackend;

impl ChcBackend for Cvc5ChcBackend {
    fn family() -> SolverFamily {
        SolverFamily::Cvc5
    }

    fn check(chc_text: &str, error_relation: &str, timeout_ms: u64) -> ChcResult {
        cvc5_check_chc(chc_text, error_relation, timeout_ms)
    }
}

pub fn check_chc(chc_text: &str, error_relation: &str, timeout_ms: u64) -> ChcResult {
    match active_chc_family() {
        SolverFamily::Z3 => Z3ChcBackend::check(chc_text, error_relation, timeout_ms),
        SolverFamily::Cvc5 => Cvc5ChcBackend::check(chc_text, error_relation, timeout_ms),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn chc_auto_resolves_conservatively_to_z3() {
        assert_eq!(resolve_chc_family(ChcSelection::Auto), Ok(SolverFamily::Z3));
    }

    #[test]
    fn chc_active_family_defaults_to_z3() {
        assert_eq!(active_chc_family(), SolverFamily::Z3);
    }

    #[test]
    fn z3_chc_backend_proves_simple_reachability_query() {
        let chc = r#"
            (declare-rel Reach (Int))
            (declare-rel Error ())
            (declare-var x Int)
            (rule (Reach 0) base)
            (rule (=> (and (Reach x) (< x 5)) (Reach (+ x 1))) step)
            (rule (=> (and (Reach x) (< x 0)) Error) err)
        "#;

        let prev = active_chc_family();
        set_active_chc_family(SolverFamily::Z3).expect("z3 CHC backend should be available");
        let result = check_chc(chc, "Error", 5_000);
        set_active_chc_family(prev).expect("restoring CHC backend should succeed");

        assert!(matches!(result, ChcResult::Proved), "got: {result:?}");
    }

    #[test]
    fn cvc5_chc_backend_returns_explicit_unknown_for_z3_style_chc_text() {
        let chc = r#"
            (declare-rel Reach (Int))
            (declare-rel Error ())
            (declare-var x Int)
            (rule (Reach 0) base)
            (rule (=> (and (Reach x) (< x 5)) (Reach (+ x 1))) step)
            (query Error)
        "#;

        let prev = active_chc_family();
        set_active_chc_family(SolverFamily::Cvc5)
            .expect("cvc5 CHC backend should be selectable in cvc5 builds");
        let result = check_chc(chc, "Error", 5_000);
        set_active_chc_family(prev).expect("restoring CHC backend should succeed");

        match result {
            ChcResult::Unknown(reason) => {
                assert!(
                    reason.contains("Z3-style fixedpoint CHC text"),
                    "reason should explain the current CHC boundary: {reason}"
                );
            }
            other => panic!("expected explicit unknown, got: {other:?}"),
        }
    }
}
