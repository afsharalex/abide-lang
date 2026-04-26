use std::collections::BTreeMap;
use std::fmt;

use serde::{Deserialize, Serialize};

use crate::value::{EntitySlotRef, WitnessValue};

/// Identity of a first-class relation inside a relational witness state.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum RelationId {
    StoreExtent { store: String },
    Field { owner: String, field: String },
    Named { name: String },
    Derived { name: String },
}

impl RelationId {
    pub fn store_extent(store: impl Into<String>) -> Result<Self, ValidationError> {
        let store = store.into();
        if store.trim().is_empty() {
            return Err(ValidationError::EmptyStoreName);
        }
        Ok(Self::StoreExtent { store })
    }

    pub fn field(
        owner: impl Into<String>,
        field: impl Into<String>,
    ) -> Result<Self, ValidationError> {
        let owner = owner.into();
        if owner.trim().is_empty() {
            return Err(ValidationError::EmptyFieldOwner);
        }
        let field = field.into();
        if field.trim().is_empty() {
            return Err(ValidationError::EmptyFieldName);
        }
        Ok(Self::Field { owner, field })
    }

    pub fn named(name: impl Into<String>) -> Result<Self, ValidationError> {
        let name = name.into();
        if name.trim().is_empty() {
            return Err(ValidationError::EmptyRelationName);
        }
        Ok(Self::Named { name })
    }

    pub fn derived(name: impl Into<String>) -> Result<Self, ValidationError> {
        let name = name.into();
        if name.trim().is_empty() {
            return Err(ValidationError::EmptyDerivedRelationName);
        }
        Ok(Self::Derived { name })
    }
}

/// Concrete tuple carried in a relational witness.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TupleValue {
    values: Vec<WitnessValue>,
}

impl TupleValue {
    pub fn new(values: Vec<WitnessValue>) -> Self {
        Self { values }
    }

    pub fn arity(&self) -> usize {
        self.values.len()
    }

    pub fn values(&self) -> &[WitnessValue] {
        &self.values
    }
}

/// A finite relation instance.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RelationInstance {
    arity: usize,
    tuples: Vec<TupleValue>,
}

impl RelationInstance {
    pub fn builder(arity: usize) -> RelationInstanceBuilder {
        RelationInstanceBuilder {
            arity,
            tuples: Vec::new(),
        }
    }

    pub fn arity(&self) -> usize {
        self.arity
    }

    pub fn tuples(&self) -> &[TupleValue] {
        &self.tuples
    }

    pub fn validate(&self) -> Result<(), ValidationError> {
        for tuple in &self.tuples {
            if tuple.arity() != self.arity {
                return Err(ValidationError::TupleArityMismatch {
                    expected: self.arity,
                    actual: tuple.arity(),
                });
            }
        }
        for (index, tuple) in self.tuples.iter().enumerate() {
            if self.tuples[..index].iter().any(|prior| prior == tuple) {
                return Err(ValidationError::DuplicateTuple);
            }
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct RelationInstanceBuilder {
    arity: usize,
    tuples: Vec<TupleValue>,
}

impl RelationInstanceBuilder {
    pub fn tuple(mut self, tuple: TupleValue) -> Result<Self, ValidationError> {
        if tuple.arity() != self.arity {
            return Err(ValidationError::TupleArityMismatch {
                expected: self.arity,
                actual: tuple.arity(),
            });
        }
        if self.tuples.iter().any(|prior| prior == &tuple) {
            return Err(ValidationError::DuplicateTuple);
        }
        self.tuples.push(tuple);
        Ok(self)
    }

    pub fn build(self) -> Result<RelationInstance, ValidationError> {
        let relation = RelationInstance {
            arity: self.arity,
            tuples: self.tuples,
        };
        relation.validate()?;
        Ok(relation)
    }
}

/// One named relation instance inside a relational witness state.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NamedRelationInstance {
    id: RelationId,
    relation: RelationInstance,
}

impl NamedRelationInstance {
    pub fn new(id: RelationId, relation: RelationInstance) -> Self {
        Self { id, relation }
    }

    pub fn id(&self) -> &RelationId {
        &self.id
    }

    pub fn relation(&self) -> &RelationInstance {
        &self.relation
    }
}

/// One relational snapshot or temporal state.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct RelationalState {
    relations: Vec<NamedRelationInstance>,
    evaluations: BTreeMap<String, WitnessValue>,
}

impl RelationalState {
    pub fn builder() -> RelationalStateBuilder {
        RelationalStateBuilder {
            relations: Vec::new(),
            evaluations: BTreeMap::new(),
        }
    }

    /// First-class relation instances. This is the primary representation.
    pub fn relation_instances(&self) -> &[NamedRelationInstance] {
        &self.relations
    }

    pub fn relation(&self, id: &RelationId) -> Option<&RelationInstance> {
        self.relations
            .iter()
            .find(|relation| relation.id() == id)
            .map(NamedRelationInstance::relation)
    }

    /// Convenience projection for store extents over the relation-native core.
    pub fn store_extent(&self, store: &str) -> Option<&RelationInstance> {
        let id = RelationId::store_extent(store).ok()?;
        self.relation(&id)
    }

    /// Convenience projection for field relations over the relation-native core.
    pub fn field_relation(&self, owner: &str, field: &str) -> Option<&RelationInstance> {
        let id = RelationId::field(owner, field).ok()?;
        self.relation(&id)
    }

    pub fn evaluations(&self) -> &BTreeMap<String, WitnessValue> {
        &self.evaluations
    }

    pub fn validate(&self) -> Result<(), ValidationError> {
        for (index, relation) in self.relations.iter().enumerate() {
            relation.relation.validate()?;
            if self.relations[..index]
                .iter()
                .any(|prior| prior.id == relation.id)
            {
                return Err(ValidationError::DuplicateRelationId);
            }
            validate_relation_id_shape(relation.id(), relation.relation())?;
        }
        for name in self.evaluations.keys() {
            if name.trim().is_empty() {
                return Err(ValidationError::EmptyEvaluationName);
            }
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct RelationalStateBuilder {
    relations: Vec<NamedRelationInstance>,
    evaluations: BTreeMap<String, WitnessValue>,
}

impl RelationalStateBuilder {
    pub fn relation_instance(
        mut self,
        id: RelationId,
        relation: RelationInstance,
    ) -> Result<Self, ValidationError> {
        if self.relations.iter().any(|prior| prior.id == id) {
            return Err(ValidationError::DuplicateRelationId);
        }
        validate_relation_id_shape(&id, &relation)?;
        self.relations
            .push(NamedRelationInstance::new(id, relation));
        Ok(self)
    }

    pub fn store_extent(
        self,
        store: impl Into<String>,
        relation: RelationInstance,
    ) -> Result<Self, ValidationError> {
        self.relation_instance(RelationId::store_extent(store)?, relation)
    }

    pub fn extent_member(
        mut self,
        store: impl Into<String>,
        member: EntitySlotRef,
    ) -> Result<Self, ValidationError> {
        let id = RelationId::store_extent(store)?;
        if let Some(existing) = self.relations.iter_mut().find(|prior| prior.id == id) {
            let tuple = TupleValue::new(vec![WitnessValue::SlotRef(member)]);
            if tuple.arity() != existing.relation.arity {
                return Err(ValidationError::StoreExtentArityMismatch {
                    actual: existing.relation.arity,
                });
            }
            if existing.relation.tuples.iter().any(|prior| prior == &tuple) {
                return Ok(self);
            }
            existing.relation.tuples.push(tuple);
            existing.relation.validate()?;
        } else {
            let relation = RelationInstance::builder(1)
                .tuple(TupleValue::new(vec![WitnessValue::SlotRef(member)]))?
                .build()?;
            self.relations
                .push(NamedRelationInstance::new(id, relation));
        }
        Ok(self)
    }

    pub fn field_relation(
        self,
        owner: impl Into<String>,
        field: impl Into<String>,
        relation: RelationInstance,
    ) -> Result<Self, ValidationError> {
        self.relation_instance(RelationId::field(owner, field)?, relation)
    }

    pub fn named_relation(
        self,
        name: impl Into<String>,
        relation: RelationInstance,
    ) -> Result<Self, ValidationError> {
        self.relation_instance(RelationId::named(name)?, relation)
    }

    pub fn derived_relation(
        self,
        name: impl Into<String>,
        relation: RelationInstance,
    ) -> Result<Self, ValidationError> {
        self.relation_instance(RelationId::derived(name)?, relation)
    }

    pub fn evaluation(
        mut self,
        name: impl Into<String>,
        value: WitnessValue,
    ) -> Result<Self, ValidationError> {
        let name = name.into();
        if name.trim().is_empty() {
            return Err(ValidationError::EmptyEvaluationName);
        }
        self.evaluations.insert(name, value);
        Ok(self)
    }

    pub fn build(self) -> Result<RelationalState, ValidationError> {
        let state = RelationalState {
            relations: self.relations,
            evaluations: self.evaluations,
        };
        state.validate()?;
        Ok(state)
    }
}

/// Bounded temporal relational witness.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TemporalRelationalWitness {
    states: Vec<RelationalState>,
    #[serde(skip_serializing_if = "Option::is_none")]
    loop_start: Option<usize>,
}

impl TemporalRelationalWitness {
    pub fn new(
        states: Vec<RelationalState>,
        loop_start: Option<usize>,
    ) -> Result<Self, ValidationError> {
        if states.is_empty() {
            return Err(ValidationError::EmptyStateSequence);
        }
        if let Some(loop_start) = loop_start {
            if loop_start >= states.len() {
                return Err(ValidationError::LoopOutOfBounds {
                    loop_start,
                    states_len: states.len(),
                });
            }
        }
        let witness = Self { states, loop_start };
        witness.validate()?;
        Ok(witness)
    }

    pub fn states(&self) -> &[RelationalState] {
        &self.states
    }

    pub fn loop_start(&self) -> Option<usize> {
        self.loop_start
    }

    pub fn validate(&self) -> Result<(), ValidationError> {
        if self.states.is_empty() {
            return Err(ValidationError::EmptyStateSequence);
        }
        if let Some(loop_start) = self.loop_start {
            if loop_start >= self.states.len() {
                return Err(ValidationError::LoopOutOfBounds {
                    loop_start,
                    states_len: self.states.len(),
                });
            }
        }
        for state in &self.states {
            state.validate()?;
        }
        Ok(())
    }
}

/// Native relational witness payload.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", content = "payload", rename_all = "snake_case")]
pub enum RelationalWitness {
    Snapshot(RelationalState),
    Temporal(TemporalRelationalWitness),
}

impl RelationalWitness {
    pub fn snapshot(state: RelationalState) -> Result<Self, ValidationError> {
        state.validate()?;
        Ok(Self::Snapshot(state))
    }

    pub fn temporal(witness: TemporalRelationalWitness) -> Result<Self, ValidationError> {
        witness.validate()?;
        Ok(Self::Temporal(witness))
    }

    pub fn validate(&self) -> Result<(), ValidationError> {
        match self {
            Self::Snapshot(state) => state.validate(),
            Self::Temporal(witness) => witness.validate(),
        }
    }

    pub fn as_snapshot(&self) -> Option<&RelationalState> {
        match self {
            Self::Snapshot(state) => Some(state),
            Self::Temporal(_) => None,
        }
    }

    pub fn as_temporal(&self) -> Option<&TemporalRelationalWitness> {
        match self {
            Self::Snapshot(_) => None,
            Self::Temporal(witness) => Some(witness),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValidationError {
    EmptyFieldOwner,
    EmptyFieldName,
    EmptyStoreName,
    EmptyRelationName,
    EmptyDerivedRelationName,
    EmptyEvaluationName,
    EmptyStateSequence,
    TupleArityMismatch {
        expected: usize,
        actual: usize,
    },
    DuplicateTuple,
    DuplicateRelationId,
    StoreExtentArityMismatch {
        actual: usize,
    },
    StoreExtentMemberMustBeSlotRef,
    FieldRelationArityMismatch {
        actual: usize,
    },
    LoopOutOfBounds {
        loop_start: usize,
        states_len: usize,
    },
}

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyFieldOwner => f.write_str("field relation owner must not be empty"),
            Self::EmptyFieldName => f.write_str("field relation field name must not be empty"),
            Self::EmptyStoreName => f.write_str("store extent name must not be empty"),
            Self::EmptyRelationName => f.write_str("relation name must not be empty"),
            Self::EmptyDerivedRelationName => {
                f.write_str("derived relation name must not be empty")
            }
            Self::EmptyEvaluationName => f.write_str("evaluation name must not be empty"),
            Self::EmptyStateSequence => {
                f.write_str("relational witness must contain at least one state")
            }
            Self::TupleArityMismatch { expected, actual } => write!(
                f,
                "relation tuple arity mismatch: expected {expected}, got {actual}"
            ),
            Self::DuplicateTuple => f.write_str("relation tuples must be unique"),
            Self::DuplicateRelationId => {
                f.write_str("relation ids must be unique within a relational state")
            }
            Self::StoreExtentArityMismatch { actual } => {
                write!(f, "store extent relations must have arity 1, got {actual}")
            }
            Self::StoreExtentMemberMustBeSlotRef => {
                f.write_str("store extent members must be slot references")
            }
            Self::FieldRelationArityMismatch { actual } => {
                write!(f, "field relations must have arity 2, got {actual}")
            }
            Self::LoopOutOfBounds {
                loop_start,
                states_len,
            } => write!(
                f,
                "relational loop start {loop_start} is out of bounds for {states_len} states"
            ),
        }
    }
}

impl std::error::Error for ValidationError {}

fn validate_relation_id_shape(
    id: &RelationId,
    relation: &RelationInstance,
) -> Result<(), ValidationError> {
    match id {
        RelationId::StoreExtent { .. } => {
            if relation.arity() != 1 {
                return Err(ValidationError::StoreExtentArityMismatch {
                    actual: relation.arity(),
                });
            }
            for tuple in relation.tuples() {
                match tuple.values() {
                    [WitnessValue::SlotRef(_)] => {}
                    _ => return Err(ValidationError::StoreExtentMemberMustBeSlotRef),
                }
            }
        }
        RelationId::Field { .. } => {
            if relation.arity() != 2 {
                return Err(ValidationError::FieldRelationArityMismatch {
                    actual: relation.arity(),
                });
            }
        }
        RelationId::Named { .. } | RelationId::Derived { .. } => {}
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_relation() -> RelationInstance {
        RelationInstance::builder(2)
            .tuple(TupleValue::new(vec![
                WitnessValue::Identity("a0".to_owned()),
                WitnessValue::Bool(true),
            ]))
            .expect("tuple arity matches")
            .build()
            .expect("valid relation")
    }

    fn sample_state() -> RelationalState {
        RelationalState::builder()
            .extent_member("orders", EntitySlotRef::new("Order", 0))
            .expect("valid extent")
            .field_relation("Order", "status", sample_relation())
            .expect("valid field relation")
            .named_relation(
                "pending_orders",
                RelationInstance::builder(1)
                    .tuple(TupleValue::new(vec![WitnessValue::Identity(
                        "a0".to_owned(),
                    )]))
                    .expect("tuple arity matches")
                    .build()
                    .expect("valid relation"),
            )
            .expect("valid relation name")
            .derived_relation(
                "cardinality_relation",
                RelationInstance::builder(1)
                    .tuple(TupleValue::new(vec![WitnessValue::Int(1)]))
                    .expect("tuple arity matches")
                    .build()
                    .expect("valid derived relation"),
            )
            .expect("valid derived relation name")
            .evaluation("cardinality", WitnessValue::Int(1))
            .expect("valid evaluation name")
            .build()
            .expect("valid relational state")
    }

    #[test]
    fn relational_snapshot_validates() {
        let witness = RelationalWitness::snapshot(sample_state()).expect("valid witness");
        assert!(matches!(witness, RelationalWitness::Snapshot(_)));
        assert_eq!(witness.validate(), Ok(()));
    }

    #[test]
    fn temporal_relational_witness_tracks_loop_start() {
        let temporal =
            TemporalRelationalWitness::new(vec![sample_state(), sample_state()], Some(1))
                .expect("valid temporal witness");
        let witness = RelationalWitness::temporal(temporal.clone()).expect("valid witness");
        assert_eq!(temporal.loop_start(), Some(1));
        assert_eq!(witness.as_temporal(), Some(&temporal));
    }

    #[test]
    fn relation_builder_rejects_wrong_arity() {
        let err = RelationInstance::builder(1)
            .tuple(TupleValue::new(vec![
                WitnessValue::Int(1),
                WitnessValue::Int(2),
            ]))
            .expect_err("wrong arity must fail");
        assert!(matches!(
            err,
            ValidationError::TupleArityMismatch {
                expected: 1,
                actual: 2
            }
        ));
    }

    #[test]
    fn temporal_relational_witness_rejects_bad_loop() {
        let err =
            TemporalRelationalWitness::new(vec![sample_state()], Some(1)).expect_err("bad loop");
        assert!(matches!(
            err,
            ValidationError::LoopOutOfBounds {
                loop_start: 1,
                states_len: 1
            }
        ));
    }

    #[test]
    fn relation_id_rejects_empty_names() {
        assert!(matches!(
            RelationId::field("", "status"),
            Err(ValidationError::EmptyFieldOwner)
        ));
        assert!(matches!(
            RelationId::field("Order", "   "),
            Err(ValidationError::EmptyFieldName)
        ));
        assert!(matches!(
            RelationId::store_extent(""),
            Err(ValidationError::EmptyStoreName)
        ));
        assert!(matches!(
            RelationId::derived("   "),
            Err(ValidationError::EmptyDerivedRelationName)
        ));
    }

    #[test]
    fn relation_builder_rejects_duplicate_tuples() {
        let tuple = TupleValue::new(vec![WitnessValue::Identity("a0".to_owned())]);
        let err = RelationInstance::builder(1)
            .tuple(tuple.clone())
            .expect("first tuple is fine")
            .tuple(tuple)
            .expect_err("duplicate tuple must fail");
        assert_eq!(err, ValidationError::DuplicateTuple);
    }

    #[test]
    fn state_exposes_relations_as_primary_representation() {
        let state = sample_state();
        assert!(!state.relation_instances().is_empty());
        assert!(state.store_extent("orders").is_some());
        assert!(state.field_relation("Order", "status").is_some());
        assert!(state
            .relation(&RelationId::derived("cardinality_relation").expect("valid id"))
            .is_some());
    }

    #[test]
    fn store_extent_shape_is_validated() {
        let relation = RelationInstance::builder(1)
            .tuple(TupleValue::new(vec![WitnessValue::Bool(true)]))
            .expect("tuple arity matches")
            .build()
            .expect("valid relation");
        let err = RelationalState::builder()
            .store_extent("orders", relation)
            .expect_err("store extents must contain slot refs");
        assert_eq!(err, ValidationError::StoreExtentMemberMustBeSlotRef);
    }

    #[test]
    fn field_relation_shape_is_validated() {
        let relation = RelationInstance::builder(1)
            .tuple(TupleValue::new(vec![WitnessValue::Int(1)]))
            .expect("tuple arity matches")
            .build()
            .expect("valid relation");
        let err = RelationalState::builder()
            .field_relation("Order", "status", relation)
            .expect_err("field relations must be binary");
        assert_eq!(
            err,
            ValidationError::FieldRelationArityMismatch { actual: 1 }
        );
    }
}
