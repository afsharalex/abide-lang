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
    pub fn witness(witness: WitnessEnvelope) -> Self {
        Self::Witness(witness)
    }

    pub fn countermodel(countermodel: Countermodel) -> Self {
        Self::Countermodel(countermodel)
    }

    pub fn proof_artifact_ref(proof_artifact_ref: ProofArtifactRef) -> Self {
        Self::ProofArtifactRef(proof_artifact_ref)
    }

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

    pub fn as_witness(&self) -> Option<&WitnessEnvelope> {
        match self {
            Self::Witness(witness) => Some(witness),
            Self::Countermodel(_) | Self::ProofArtifactRef(_) => None,
        }
    }

    pub fn as_countermodel(&self) -> Option<&Countermodel> {
        match self {
            Self::Countermodel(countermodel) => Some(countermodel),
            Self::Witness(_) | Self::ProofArtifactRef(_) => None,
        }
    }

    pub fn as_proof_artifact_ref(&self) -> Option<&ProofArtifactRef> {
        match self {
            Self::ProofArtifactRef(proof_artifact_ref) => Some(proof_artifact_ref),
            Self::Witness(_) | Self::Countermodel(_) => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EvidenceEnvelope {
    payload: EvidencePayload,
}

impl EvidenceEnvelope {
    pub fn new(payload: EvidencePayload) -> Result<Self, ValidationError> {
        payload.validate()?;
        Ok(Self { payload })
    }

    pub fn witness(witness: WitnessEnvelope) -> Result<Self, ValidationError> {
        Self::new(EvidencePayload::witness(witness))
    }

    pub fn countermodel(countermodel: Countermodel) -> Result<Self, ValidationError> {
        Self::new(EvidencePayload::countermodel(countermodel))
    }

    pub fn proof_artifact_ref(
        proof_artifact_ref: ProofArtifactRef,
    ) -> Result<Self, ValidationError> {
        Self::new(EvidencePayload::proof_artifact_ref(proof_artifact_ref))
    }

    pub fn payload(&self) -> &EvidencePayload {
        &self.payload
    }

    pub fn as_witness(&self) -> Option<&WitnessEnvelope> {
        self.payload.as_witness()
    }

    pub fn as_countermodel(&self) -> Option<&Countermodel> {
        self.payload.as_countermodel()
    }

    pub fn as_proof_artifact_ref(&self) -> Option<&ProofArtifactRef> {
        self.payload.as_proof_artifact_ref()
    }

    pub fn validate(&self) -> Result<(), ValidationError> {
        self.payload.validate()
    }

    pub fn from_json_validated(json: &str) -> Result<Self, ValidatedJsonError<ValidationError>> {
        let envelope: Self = serde_json::from_str(json).map_err(ValidatedJsonError::deserialize)?;
        envelope.validate().map_err(ValidatedJsonError::validate)?;
        Ok(envelope)
    }

    pub fn from_json_reader_validated<R: Read>(
        reader: R,
    ) -> Result<Self, ValidatedJsonError<ValidationError>> {
        let envelope: Self =
            serde_json::from_reader(reader).map_err(ValidatedJsonError::deserialize)?;
        envelope.validate().map_err(ValidatedJsonError::validate)?;
        Ok(envelope)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Countermodel {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    backend: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    summary: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    bindings: Vec<CountermodelBinding>,
}

impl Countermodel {
    pub fn new() -> Self {
        Self {
            backend: None,
            summary: None,
            bindings: Vec::new(),
        }
    }

    pub fn backend(mut self, backend: impl Into<String>) -> Self {
        self.backend = Some(backend.into());
        self
    }

    pub fn summary(mut self, summary: impl Into<String>) -> Self {
        self.summary = Some(summary.into());
        self
    }

    pub fn binding(mut self, binding: CountermodelBinding) -> Self {
        self.bindings.push(binding);
        self
    }

    pub fn backend_name(&self) -> Option<&str> {
        self.backend.as_deref()
    }

    pub fn summary_text(&self) -> Option<&str> {
        self.summary.as_deref()
    }

    pub fn bindings(&self) -> &[CountermodelBinding] {
        &self.bindings
    }

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

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CountermodelBinding {
    name: String,
    value: WitnessValue,
}

impl CountermodelBinding {
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

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn value(&self) -> &WitnessValue {
        &self.value
    }

    pub fn validate(&self) -> Result<(), CountermodelValidationError> {
        if self.name.trim().is_empty() {
            return Err(CountermodelValidationError::EmptyBindingName);
        }
        Ok(())
    }
}

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

    pub fn backend(mut self, backend: impl Into<String>) -> Self {
        self.backend = Some(backend.into());
        self
    }

    pub fn label(mut self, label: impl Into<String>) -> Self {
        self.label = Some(label.into());
        self
    }

    pub fn checked(mut self, checked: bool) -> Self {
        self.checked = checked;
        self
    }

    pub fn locator(&self) -> &str {
        &self.locator
    }

    pub fn backend_name(&self) -> Option<&str> {
        self.backend.as_deref()
    }

    pub fn label_text(&self) -> Option<&str> {
        self.label.as_deref()
    }

    pub fn is_checked(&self) -> bool {
        self.checked
    }

    pub fn validate(&self) -> Result<(), ProofArtifactRefValidationError> {
        if self.locator.trim().is_empty() {
            return Err(ProofArtifactRefValidationError::EmptyLocator);
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValidationError {
    Witness(WitnessValidationError),
    Countermodel(CountermodelValidationError),
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CountermodelValidationError {
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofArtifactRefValidationError {
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
}
