use std::fmt;
use std::io::Read;

use serde::{Deserialize, Serialize};

use crate::{op, rel, ValidatedJsonError};

/// Shared witness payload surface for verification results.
///
/// This sits above the concrete witness families. Result consumers should
/// depend on this enum rather than assuming a single witness shape.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "family", content = "payload", rename_all = "snake_case")]
#[non_exhaustive]
pub enum WitnessPayload {
    Operational(op::OperationalWitness),
    Relational(rel::RelationalWitness),
}

impl WitnessPayload {
    pub fn operational(witness: op::OperationalWitness) -> Self {
        Self::Operational(witness)
    }

    pub fn relational(witness: rel::RelationalWitness) -> Self {
        Self::Relational(witness)
    }

    pub fn validate(&self) -> Result<(), ValidationError> {
        match self {
            Self::Operational(witness) => witness.validate().map_err(ValidationError::Operational),
            Self::Relational(witness) => witness.validate().map_err(ValidationError::Relational),
        }
    }

    pub fn as_operational(&self) -> Option<&op::OperationalWitness> {
        match self {
            Self::Operational(witness) => Some(witness),
            Self::Relational(_) => None,
        }
    }

    pub fn as_relational(&self) -> Option<&rel::RelationalWitness> {
        match self {
            Self::Operational(_) => None,
            Self::Relational(witness) => Some(witness),
        }
    }
}

/// Shared result-envelope witness wrapper.
///
/// The envelope allows higher layers to depend on one stable field even as
/// additional witness families arrive in later revisions.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WitnessEnvelope {
    payload: WitnessPayload,
}

impl WitnessEnvelope {
    pub fn new(payload: WitnessPayload) -> Result<Self, ValidationError> {
        payload.validate()?;
        Ok(Self { payload })
    }

    pub fn operational(witness: op::OperationalWitness) -> Result<Self, ValidationError> {
        Self::new(WitnessPayload::operational(witness))
    }

    pub fn relational(witness: rel::RelationalWitness) -> Result<Self, ValidationError> {
        Self::new(WitnessPayload::relational(witness))
    }

    pub fn payload(&self) -> &WitnessPayload {
        &self.payload
    }

    pub fn as_operational(&self) -> Option<&op::OperationalWitness> {
        self.payload.as_operational()
    }

    pub fn as_relational(&self) -> Option<&rel::RelationalWitness> {
        self.payload.as_relational()
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValidationError {
    Operational(op::ValidationError),
    Relational(rel::ValidationError),
}

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Operational(err) => err.fmt(f),
            Self::Relational(err) => err.fmt(f),
        }
    }
}

impl std::error::Error for ValidationError {}

#[cfg(test)]
mod tests {
    use super::*;

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

    fn sample_relational_state() -> rel::RelationalState {
        rel::RelationalState::builder()
            .extent_member("orders", crate::EntitySlotRef::new("Order", 0))
            .expect("valid extent")
            .named_relation(
                "pending_orders",
                rel::RelationInstance::builder(1)
                    .tuple(rel::TupleValue::new(vec![crate::WitnessValue::Identity(
                        "order0".to_owned(),
                    )]))
                    .expect("tuple arity matches")
                    .build()
                    .expect("valid relation"),
            )
            .expect("valid relation name")
            .build()
            .expect("valid relational state")
    }

    #[test]
    fn witness_envelope_wraps_operational_payload() {
        let witness =
            op::OperationalWitness::counterexample(sample_behavior()).expect("valid witness");
        let envelope = WitnessEnvelope::operational(witness.clone()).expect("valid envelope");

        assert!(matches!(
            envelope.payload(),
            WitnessPayload::Operational(inner) if inner == &witness
        ));
        assert_eq!(envelope.as_operational(), Some(&witness));
        assert_eq!(envelope.validate(), Ok(()));
    }

    #[test]
    fn witness_envelope_round_trips_json() {
        let witness =
            op::OperationalWitness::counterexample(sample_behavior()).expect("valid witness");
        let envelope = WitnessEnvelope::operational(witness).expect("valid envelope");

        let json = serde_json::to_string(&envelope).expect("serialize envelope");
        let decoded: WitnessEnvelope = serde_json::from_str(&json).expect("deserialize envelope");

        assert_eq!(decoded, envelope);
        assert_eq!(decoded.validate(), Ok(()));
    }

    #[test]
    fn witness_envelope_wraps_relational_payload() {
        let witness =
            rel::RelationalWitness::snapshot(sample_relational_state()).expect("valid witness");
        let envelope = WitnessEnvelope::relational(witness.clone()).expect("valid envelope");

        assert!(matches!(
            envelope.payload(),
            WitnessPayload::Relational(inner) if inner == &witness
        ));
        assert_eq!(envelope.as_relational(), Some(&witness));
        assert_eq!(envelope.validate(), Ok(()));
    }

    #[test]
    fn witness_envelope_from_json_validated_accepts_valid_payload() {
        let envelope = WitnessEnvelope::operational(
            op::OperationalWitness::counterexample(sample_behavior()).expect("valid witness"),
        )
        .expect("valid envelope");
        let json = serde_json::to_string(&envelope).expect("serialize envelope");

        let decoded = WitnessEnvelope::from_json_validated(&json).expect("validated decode");

        assert_eq!(decoded, envelope);
    }

    #[test]
    fn witness_envelope_from_json_validated_rejects_invalid_payload() {
        let json = r#"{
            "payload": {
                "family": "operational",
                "payload": {
                    "kind": "counterexample",
                    "behavior": {
                        "states": [
                            { "entity_slots": [], "system_fields": {} }
                        ],
                        "transitions": [
                            { "atomic_steps": [], "relations": [], "observations": [] }
                        ]
                    }
                }
            }
        }"#;

        let err = WitnessEnvelope::from_json_validated(json).expect_err("must fail validation");
        assert!(matches!(
            err,
            ValidatedJsonError::Validate(ValidationError::Operational(
                op::ValidationError::TransitionCount { .. }
            ))
        ));
    }
}
