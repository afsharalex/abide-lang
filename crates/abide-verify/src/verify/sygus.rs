use std::collections::HashMap;
#[cfg(test)]
use std::time::Instant;

use cvc5_rs::{
    Kind as Cvc5Kind, Solver as Cvc5Solver, Sort as Cvc5Sort, Term as Cvc5Term,
    TermManager as Cvc5Tm,
};

use crate::ir::types::{
    IRAction, IRCreateField, IRDerivedField, IREntity, IRExpr, IRField, IRFsm, IRSystem,
    IRSystemAction, IRTransParam, IRTransition, IRType, LitVal,
};
mod core;
mod pooled;
#[cfg(test)]
pub use self::core::try_cvc5_sygus_single_entity;
#[cfg(test)]
pub use self::core::try_cvc5_sygus_system_safety;
use self::core::*;
#[cfg(test)]
pub use self::pooled::try_cvc5_sygus_multi_system_pooled_safety;
#[cfg(test)]
use self::pooled::*;

#[cfg(test)]
use super::ic3::Ic3Result;

#[cfg(test)]
mod tests;

#[cfg(test)]
const CVC5_SYGUS_ENABLE_ENV: &str = "ABIDE_ENABLE_INPROCESS_CVC5_SYGUS";

#[cfg(test)]
fn cvc5_sygus_enabled() -> bool {
    std::env::var_os(CVC5_SYGUS_ENABLE_ENV).is_some()
}

#[cfg(test)]
fn cvc5_sygus_disabled_reason() -> String {
    format!(
        "cvc5 SyGuS is disabled by default because the in-process cvc5 API does not provide a hard cancellation hook; set {CVC5_SYGUS_ENABLE_ENV}=1 to opt in"
    )
}

/// Run cvc5 SyGuS system-safety synthesis with its plain-SMT pre-filter and
/// return the synthesized invariant translated to `IRExpr` (`Some`) for the
/// caller's independent Z3/IR re-validation, `Ok(None)` when the invariant
/// passed the pre-filter but could not be translated (→ conservative
/// downgrade), or `Err` when synthesis or the pre-filter failed.
pub(super) fn try_cvc5_sygus_system_safety_opted_in(
    system: &IRSystem,
    property: &IRExpr,
    timeout_ms: u64,
) -> Result<Option<IRExpr>, String> {
    core::try_cvc5_sygus_system_safety_inner(system, property, timeout_ms)
}

/// Run cvc5 SyGuS pooled multi-system safety synthesis with its plain-SMT
/// pre-filter and return the synthesized invariant translated to `IRExpr`
/// (`Some`) for the caller's independent slot-aware Z3/IR re-validation,
/// `Ok(None)` when the invariant passed the pre-filter but could not be
/// translated (→ conservative downgrade), or `Err` when synthesis or the
/// pre-filter failed.
pub(super) fn try_cvc5_sygus_multi_system_pooled_safety_opted_in(
    root_system: &IRSystem,
    systems: &[IRSystem],
    entities: &[IREntity],
    slots_per_entity: &HashMap<String, usize>,
    property: &IRExpr,
    timeout_ms: u64,
) -> Result<Option<IRExpr>, String> {
    pooled::try_cvc5_sygus_multi_system_pooled_safety_inner(
        root_system,
        systems,
        entities,
        slots_per_entity,
        property,
        timeout_ms,
    )
}
