use std::fmt;
use std::io::Read;

use serde::{Deserialize, Serialize};

use crate::shared::{ValidationError as WitnessValidationError, WitnessEnvelope};
use crate::{ValidatedJsonError, WitnessValue};

/// Result-level evidence model above concrete witness families.
///
/// Behavioral failures normalize into `Witness`, while proof-oriented failures
/// can carry countermodels or external proof references without being forced
/// into trace-shaped concepts.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", content = "payload", rename_all = "snake_case")]
#[non_exhaustive]
pub enum EvidencePayload {
    Witness(WitnessEnvelope),
    Countermodel(Countermodel),
    ProofArtifactRef(ProofArtifactRef),
}

impl EvidencePayload {
    /// Wraps an operational/relational witness envelope.
    pub fn witness(witness: WitnessEnvelope) -> Self {
        Self::Witness(witness)
    }

    /// Wraps a solver countermodel.
    pub fn countermodel(countermodel: Countermodel) -> Self {
        Self::Countermodel(countermodel)
    }

    /// Wraps a reference to an external proof artifact (Agda/Lean/Rocq).
    pub fn proof_artifact_ref(proof_artifact_ref: ProofArtifactRef) -> Self {
        Self::ProofArtifactRef(proof_artifact_ref)
    }

    /// Re-runs the inner payload's structural validation. Useful at
    /// importer boundaries.
    pub fn validate(&self) -> Result<(), ValidationError> {
        match self {
            Self::Witness(witness) => witness.validate().map_err(ValidationError::Witness),
            Self::Countermodel(countermodel) => countermodel
                .validate()
                .map_err(ValidationError::Countermodel),
            Self::ProofArtifactRef(proof_artifact_ref) => proof_artifact_ref
                .validate()
                .map_err(ValidationError::ProofArtifactRef),
        }
    }

    /// Returns the inner witness envelope if this is a `Witness`
    /// payload, otherwise `None`.
    pub fn as_witness(&self) -> Option<&WitnessEnvelope> {
        match self {
            Self::Witness(witness) => Some(witness),
            Self::Countermodel(_) | Self::ProofArtifactRef(_) => None,
        }
    }

    /// Returns the inner countermodel if this is a `Countermodel`
    /// payload, otherwise `None`.
    pub fn as_countermodel(&self) -> Option<&Countermodel> {
        match self {
            Self::Countermodel(countermodel) => Some(countermodel),
            Self::Witness(_) | Self::ProofArtifactRef(_) => None,
        }
    }

    /// Returns the inner proof artifact reference if this is a
    /// `ProofArtifactRef` payload, otherwise `None`.
    pub fn as_proof_artifact_ref(&self) -> Option<&ProofArtifactRef> {
        match self {
            Self::ProofArtifactRef(proof_artifact_ref) => Some(proof_artifact_ref),
            Self::Witness(_) | Self::Countermodel(_) => None,
        }
    }
}

/// Stable result-level envelope around [`EvidencePayload`].
///
/// Like [`WitnessEnvelope`], the envelope buys forward-compatibility: a
/// new payload kind can be added without breaking the surface type
/// callers depend on.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EvidenceEnvelope {
    payload: EvidencePayload,
}

impl EvidenceEnvelope {
    /// Wraps `payload` after validating it.
    pub fn new(payload: EvidencePayload) -> Result<Self, ValidationError> {
        payload.validate()?;
        Ok(Self { payload })
    }

    /// Convenience: wrap a witness envelope directly.
    pub fn witness(witness: WitnessEnvelope) -> Result<Self, ValidationError> {
        Self::new(EvidencePayload::witness(witness))
    }

    /// Convenience: wrap a countermodel directly.
    pub fn countermodel(countermodel: Countermodel) -> Result<Self, ValidationError> {
        Self::new(EvidencePayload::countermodel(countermodel))
    }

    /// Convenience: wrap a proof-artifact reference directly.
    pub fn proof_artifact_ref(
        proof_artifact_ref: ProofArtifactRef,
    ) -> Result<Self, ValidationError> {
        Self::new(EvidencePayload::proof_artifact_ref(proof_artifact_ref))
    }

    /// Borrows the contained payload.
    pub fn payload(&self) -> &EvidencePayload {
        &self.payload
    }

    /// Returns the contained witness envelope if any.
    pub fn as_witness(&self) -> Option<&WitnessEnvelope> {
        self.payload.as_witness()
    }

    /// Returns the contained countermodel if any.
    pub fn as_countermodel(&self) -> Option<&Countermodel> {
        self.payload.as_countermodel()
    }

    /// Returns the contained proof artifact reference if any.
    pub fn as_proof_artifact_ref(&self) -> Option<&ProofArtifactRef> {
        self.payload.as_proof_artifact_ref()
    }

    /// Re-validates the contained payload.
    pub fn validate(&self) -> Result<(), ValidationError> {
        self.payload.validate()
    }

    /// Parses an envelope from a JSON string and validates it.
    pub fn from_json_validated(json: &str) -> Result<Self, ValidatedJsonError<ValidationError>> {
        let envelope: Self = serde_json::from_str(json).map_err(ValidatedJsonError::deserialize)?;
        envelope.validate().map_err(ValidatedJsonError::validate)?;
        Ok(envelope)
    }

    /// Streaming variant of [`Self::from_json_validated`].
    pub fn from_json_reader_validated<R: Read>(
        reader: R,
    ) -> Result<Self, ValidatedJsonError<ValidationError>> {
        let envelope: Self =
            serde_json::from_reader(reader).map_err(ValidatedJsonError::deserialize)?;
        envelope.validate().map_err(ValidatedJsonError::validate)?;
        Ok(envelope)
    }
}

/// Countermodel returned by a deductive backend when a proof
/// obligation is refuted at the SMT level.
///
/// A countermodel is a bag of name-to-value bindings; unlike an
/// operational witness it has no trace structure — it is a snapshot
/// model that satisfies the negation of the obligation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Countermodel {
    /// Solver that produced the countermodel (e.g. `"z3"`, `"cvc5"`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    backend: Option<String>,
    /// Optional one-line human-readable summary.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    summary: Option<String>,
    /// Name-to-value bindings describing the model.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    bindings: Vec<CountermodelBinding>,
}

impl Countermodel {
    /// Constructs an empty countermodel; chain `.backend(..)`,
    /// `.summary(..)`, and `.binding(..)` to populate it.
    pub fn new() -> Self {
        Self {
            backend: None,
            summary: None,
            bindings: Vec::new(),
        }
    }

    /// Records the producing solver name.
    pub fn backend(mut self, backend: impl Into<String>) -> Self {
        self.backend = Some(backend.into());
        self
    }

    /// Attaches a one-line summary.
    pub fn summary(mut self, summary: impl Into<String>) -> Self {
        self.summary = Some(summary.into());
        self
    }

    /// Appends one binding to the countermodel.
    pub fn binding(mut self, binding: CountermodelBinding) -> Self {
        self.bindings.push(binding);
        self
    }

    /// Returns the producing solver name, if recorded.
    pub fn backend_name(&self) -> Option<&str> {
        self.backend.as_deref()
    }

    /// Returns the summary text, if any.
    pub fn summary_text(&self) -> Option<&str> {
        self.summary.as_deref()
    }

    /// Borrows the full binding list.
    pub fn bindings(&self) -> &[CountermodelBinding] {
        &self.bindings
    }

    /// Validates every binding in turn.
    pub fn validate(&self) -> Result<(), CountermodelValidationError> {
        for binding in &self.bindings {
            binding.validate()?;
        }
        Ok(())
    }
}

impl Default for Countermodel {
    fn default() -> Self {
        Self::new()
    }
}

/// Single name-to-value binding inside a [`Countermodel`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CountermodelBinding {
    name: String,
    value: WitnessValue,
}

impl CountermodelBinding {
    /// Constructs and validates a binding (rejects empty names).
    pub fn new(
        name: impl Into<String>,
        value: WitnessValue,
    ) -> Result<Self, CountermodelValidationError> {
        let binding = Self {
            name: name.into(),
            value,
        };
        binding.validate()?;
        Ok(binding)
    }

    /// Binding name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Bound value.
    pub fn value(&self) -> &WitnessValue {
        &self.value
    }

    /// Rejects bindings whose name is empty or pure whitespace.
    pub fn validate(&self) -> Result<(), CountermodelValidationError> {
        if self.name.trim().is_empty() {
            return Err(CountermodelValidationError::EmptyBindingName);
        }
        Ok(())
    }
}

/// Reference to an external proof artifact carried by an `axiom`
/// declaration's `by "file"` clause (Agda, Lean 4, Rocq, …).
///
/// `checked` indicates whether the artifact has been validated by the
/// external prover during this run; the field is informational — the
/// `axiom` mechanism trusts the artifact regardless.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofArtifactRef {
    locator: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    backend: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    label: Option<String>,
    #[serde(default)]
    checked: bool,
}

impl ProofArtifactRef {
    /// Constructs and validates an artifact reference (rejects empty
    /// locators).
    pub fn new(locator: impl Into<String>) -> Result<Self, ProofArtifactRefValidationError> {
        let proof_artifact_ref = Self {
            locator: locator.into(),
            backend: None,
            label: None,
            checked: false,
        };
        proof_artifact_ref.validate()?;
        Ok(proof_artifact_ref)
    }

    /// Records the external prover that owns the artifact.
    pub fn backend(mut self, backend: impl Into<String>) -> Self {
        self.backend = Some(backend.into());
        self
    }

    /// Attaches a short label (typically the theorem name).
    pub fn label(mut self, label: impl Into<String>) -> Self {
        self.label = Some(label.into());
        self
    }

    /// Marks whether the artifact was verified during this run.
    pub fn checked(mut self, checked: bool) -> Self {
        self.checked = checked;
        self
    }

    /// Path or URI pointing at the artifact.
    pub fn locator(&self) -> &str {
        &self.locator
    }

    /// External prover name, if set.
    pub fn backend_name(&self) -> Option<&str> {
        self.backend.as_deref()
    }

    /// Label, if set.
    pub fn label_text(&self) -> Option<&str> {
        self.label.as_deref()
    }

    /// Returns `true` if the producer claims the artifact was checked.
    pub fn is_checked(&self) -> bool {
        self.checked
    }

    /// Rejects refs with an empty or whitespace-only locator.
    pub fn validate(&self) -> Result<(), ProofArtifactRefValidationError> {
        if self.locator.trim().is_empty() {
            return Err(ProofArtifactRefValidationError::EmptyLocator);
        }
        Ok(())
    }
}

/// Top-level error returned by [`EvidencePayload::validate`] /
/// [`EvidenceEnvelope::validate`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValidationError {
    /// Wrapped witness-envelope validation failure.
    Witness(WitnessValidationError),
    /// Countermodel validation failure.
    Countermodel(CountermodelValidationError),
    /// Proof-artifact-reference validation failure.
    ProofArtifactRef(ProofArtifactRefValidationError),
}

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Witness(err) => err.fmt(f),
            Self::Countermodel(err) => err.fmt(f),
            Self::ProofArtifactRef(err) => err.fmt(f),
        }
    }
}

impl std::error::Error for ValidationError {}

/// Errors produced while validating a [`Countermodel`] or its
/// [`CountermodelBinding`]s.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CountermodelValidationError {
    /// A binding's `name` field is empty or whitespace-only.
    EmptyBindingName,
}

impl fmt::Display for CountermodelValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyBindingName => write!(f, "countermodel binding name may not be empty"),
        }
    }
}

impl std::error::Error for CountermodelValidationError {}

/// Errors produced while validating a [`ProofArtifactRef`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofArtifactRefValidationError {
    /// `locator` is empty or whitespace-only.
    EmptyLocator,
}

impl fmt::Display for ProofArtifactRefValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyLocator => write!(f, "proof artifact locator may not be empty"),
        }
    }
}

impl std::error::Error for ProofArtifactRefValidationError {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{op, EntitySlotRef};

    fn sample_behavior() -> op::Behavior {
        let step = op::AtomicStep::builder(
            op::AtomicStepId::new("billing_charge").expect("valid id"),
            "Billing",
            "charge",
        )
        .build()
        .expect("valid atomic step");
        let transition = op::Transition::builder()
            .atomic_step(step)
            .build()
            .expect("valid transition");
        op::Behavior::builder()
            .state(op::State::default())
            .transition(transition)
            .state(op::State::default())
            .build()
            .expect("valid behavior")
    }

    #[test]
    fn evidence_envelope_wraps_witness_payload() {
        let witness = crate::WitnessEnvelope::operational(
            op::OperationalWitness::counterexample(sample_behavior()).expect("valid witness"),
        )
        .expect("valid witness envelope");
        let envelope = EvidenceEnvelope::witness(witness.clone()).expect("valid evidence");

        assert_eq!(envelope.as_witness(), Some(&witness));
        assert_eq!(envelope.as_countermodel(), None);
        assert_eq!(envelope.validate(), Ok(()));
    }

    #[test]
    fn evidence_envelope_wraps_countermodel() {
        let countermodel = Countermodel::new()
            .backend("z3")
            .summary("negated lemma body is satisfiable")
            .binding(
                CountermodelBinding::new(
                    "witness",
                    WitnessValue::SlotRef(EntitySlotRef::new("Order", 0)),
                )
                .expect("valid binding"),
            );
        let envelope =
            EvidenceEnvelope::countermodel(countermodel.clone()).expect("valid evidence");

        assert_eq!(envelope.as_countermodel(), Some(&countermodel));
        assert_eq!(envelope.as_witness(), None);
        assert_eq!(envelope.validate(), Ok(()));
    }

    #[test]
    fn proof_artifact_ref_rejects_empty_locator() {
        assert_eq!(
            ProofArtifactRef::new("").unwrap_err(),
            ProofArtifactRefValidationError::EmptyLocator
        );
    }

    #[test]
    fn evidence_round_trips_json() {
        let evidence = EvidenceEnvelope::proof_artifact_ref(
            ProofArtifactRef::new("proofs/order.agda")
                .expect("valid proof ref")
                .backend("agda")
                .label("order_no_overdraft")
                .checked(false),
        )
        .expect("valid evidence");

        let json = serde_json::to_string(&evidence).expect("serialize evidence");
        let decoded: EvidenceEnvelope = serde_json::from_str(&json).expect("deserialize evidence");

        assert_eq!(decoded, evidence);
        assert_eq!(decoded.validate(), Ok(()));
    }

    #[test]
    fn proof_artifact_payload_accessors_preserve_reference() {
        let artifact = ProofArtifactRef::new("proofs/order.agda")
            .expect("valid proof ref")
            .backend("agda")
            .label("order_no_overdraft")
            .checked(true);
        let payload = EvidencePayload::proof_artifact_ref(artifact.clone());
        let envelope =
            EvidenceEnvelope::proof_artifact_ref(artifact.clone()).expect("valid evidence");

        assert_eq!(payload.as_proof_artifact_ref(), Some(&artifact));
        assert_eq!(payload.as_countermodel(), None);
        assert_eq!(envelope.as_proof_artifact_ref(), Some(&artifact));
        assert_eq!(envelope.payload(), &payload);
        assert_eq!(artifact.locator(), "proofs/order.agda");
        assert_eq!(artifact.backend_name(), Some("agda"));
        assert_eq!(artifact.label_text(), Some("order_no_overdraft"));
        assert!(artifact.is_checked());
        assert!(!ProofArtifactRef::new("proofs/unchecked.agda")
            .expect("valid proof ref")
            .is_checked());
    }

    #[test]
    fn countermodel_builder_and_accessors_preserve_payload() {
        let binding = CountermodelBinding::new("n", WitnessValue::Int(42)).expect("valid binding");
        let countermodel = Countermodel::new()
            .backend("cvc5")
            .summary("model satisfies negated goal")
            .binding(binding.clone());

        assert_eq!(countermodel.backend_name(), Some("cvc5"));
        assert_eq!(
            countermodel.summary_text(),
            Some("model satisfies negated goal")
        );
        assert_eq!(countermodel.bindings(), std::slice::from_ref(&binding));
        assert_eq!(countermodel.validate(), Ok(()));
        assert_eq!(binding.name(), "n");
        assert_eq!(binding.value(), &WitnessValue::Int(42));
    }

    #[test]
    fn countermodel_validation_rejects_tampered_binding_names() {
        let binding = CountermodelBinding {
            name: " ".to_owned(),
            value: WitnessValue::Bool(true),
        };
        assert_eq!(
            binding.validate(),
            Err(CountermodelValidationError::EmptyBindingName)
        );

        let countermodel = Countermodel {
            backend: Some("z3".to_owned()),
            summary: None,
            bindings: vec![binding],
        };
        assert_eq!(
            countermodel.validate(),
            Err(CountermodelValidationError::EmptyBindingName)
        );
    }

    #[test]
    fn evidence_envelope_from_json_validated_accepts_valid_payload() {
        let evidence = EvidenceEnvelope::proof_artifact_ref(
            ProofArtifactRef::new("proofs/order.agda").expect("valid proof ref"),
        )
        .expect("valid evidence");
        let json = serde_json::to_string(&evidence).expect("serialize evidence");

        let decoded = EvidenceEnvelope::from_json_validated(&json).expect("validated decode");

        assert_eq!(decoded, evidence);
    }

    #[test]
    fn evidence_envelope_from_json_validated_rejects_invalid_payload() {
        let json = r#"{
            "payload": {
                "kind": "proof_artifact_ref",
                "payload": {
                    "locator": "",
                    "checked": false
                }
            }
        }"#;

        let err = EvidenceEnvelope::from_json_validated(json).expect_err("must fail validation");
        assert!(matches!(
            err,
            ValidatedJsonError::Validate(ValidationError::ProofArtifactRef(
                ProofArtifactRefValidationError::EmptyLocator
            ))
        ));
    }

    #[test]
    fn evidence_validation_errors_display_inner_context() {
        assert_eq!(
            ValidationError::ProofArtifactRef(ProofArtifactRefValidationError::EmptyLocator)
                .to_string(),
            "proof artifact locator may not be empty"
        );
        assert_eq!(
            ValidationError::Countermodel(CountermodelValidationError::EmptyBindingName)
                .to_string(),
            "countermodel binding name may not be empty"
        );
        assert_eq!(
            CountermodelValidationError::EmptyBindingName.to_string(),
            "countermodel binding name may not be empty"
        );
        assert_eq!(
            ProofArtifactRefValidationError::EmptyLocator.to_string(),
            "proof artifact locator may not be empty"
        );
    }
}
