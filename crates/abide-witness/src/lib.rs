//! Native witness models for Abide verification results.
//!
//! This crate is intentionally separate from the language IR:
//! - `abide-ir` describes lowered source semantics and verifier inputs
//! - `abide-witness` describes concrete witness payloads produced by
//!   verification and checking backends
//!
//! Operational and relational witnesses share one stable result envelope.
//!
//! Construction policy:
//! - normal in-process construction should go through checked constructors and
//!   builder APIs in `op`
//! - `validate()` remains available as a defensive boundary check for:
//!   - deserialized payloads
//!   - imported/generated payloads
//!   - integration seams that need to reassert witness invariants
//! - importer boundaries should prefer the validated JSON helpers on
//!   `WitnessEnvelope` and `EvidenceEnvelope` so parse failures and validation
//!   failures stay distinct

pub mod evidence;
pub mod op;
pub mod rel;
pub mod shared;
pub mod value;

use std::fmt;

pub use evidence::{
    Countermodel, CountermodelBinding, CountermodelValidationError, EvidenceEnvelope,
    EvidencePayload, ProofArtifactRef, ProofArtifactRefValidationError,
    ValidationError as EvidenceValidationError,
};
pub use shared::{ValidationError as SharedValidationError, WitnessEnvelope, WitnessPayload};
pub use value::{EntitySlotRef, WitnessValue};

/// Failure modes when parsing a witness/evidence JSON payload at an
/// importer boundary.
///
/// Keeping deserialization and validation distinct lets callers report
/// "malformed JSON" separately from "well-formed but invalid witness",
/// which is the distinction Invaria's importer cares about.
#[derive(Debug)]
pub enum ValidatedJsonError<V> {
    /// `serde_json` could not parse the input.
    Deserialize(serde_json::Error),
    /// Parse succeeded but the payload failed witness/evidence
    /// invariants (e.g. a binding referenced an unknown entity slot).
    Validate(V),
}

impl<V> ValidatedJsonError<V> {
    /// Wraps a serde parse error.
    pub fn deserialize(err: serde_json::Error) -> Self {
        Self::Deserialize(err)
    }

    /// Wraps a payload validation error.
    pub fn validate(err: V) -> Self {
        Self::Validate(err)
    }
}

impl<V: fmt::Display> fmt::Display for ValidatedJsonError<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Deserialize(err) => write!(f, "failed to deserialize witness JSON: {err}"),
            Self::Validate(err) => write!(f, "deserialized witness JSON failed validation: {err}"),
        }
    }
}

impl<V: std::error::Error + 'static> std::error::Error for ValidatedJsonError<V> {}
