//! Solver-agnostic value vocabulary shared between operational and
//! relational witnesses.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

/// Stable identifier for an entity slot in a concrete witness state.
///
/// Slots are the concrete instances backing each `Store<T>` in the
/// system being verified; the `slot` index is a stable
/// position within that store within the witness scene.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct EntitySlotRef {
    entity: String,
    slot: usize,
}

impl EntitySlotRef {
    /// Constructs a reference to slot `slot` of `entity`.
    pub fn new(entity: impl Into<String>, slot: usize) -> Self {
        Self {
            entity: entity.into(),
            slot,
        }
    }

    /// Entity type name (matches the source-level `entity` declaration).
    pub fn entity(&self) -> &str {
        &self.entity
    }

    /// Zero-based slot index within the entity's store.
    pub fn slot(&self) -> usize {
        self.slot
    }
}

/// Concrete semantic value carried in witness payloads.
///
/// This is intentionally solver-agnostic and shared across the operational and
/// relational witness families. Real and Float values are carried as
/// strings to preserve the exact textual representation emitted by the
/// backend solver — converting to `f64` here would lose precision.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", content = "value", rename_all = "snake_case")]
pub enum WitnessValue {
    /// Value is present but the backend declined to materialize it
    /// (e.g. an unused choice in a disjunctive witness).
    Unknown,
    /// Signed 64-bit integer.
    Int(i64),
    /// Boolean.
    Bool(bool),
    /// Real number, kept as the solver's exact textual form.
    Real(String),
    /// IEEE float, kept as the solver's textual form.
    Float(String),
    /// String literal.
    String(String),
    /// Abide `identity` value.
    Identity(String),
    /// Enum constructor with optional named field values.
    EnumVariant {
        enum_name: String,
        variant: String,
        #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
        fields: BTreeMap<String, WitnessValue>,
    },
    /// Reference to a concrete entity instance by entity name and slot.
    SlotRef(EntitySlotRef),
    /// Positional tuple.
    Tuple(Vec<WitnessValue>),
    /// Named-field record / struct.
    Record(BTreeMap<String, WitnessValue>),
    /// `Set<T>` value (unordered; order is rendering-only).
    Set(Vec<WitnessValue>),
    /// `Seq<T>` value (ordered).
    Seq(Vec<WitnessValue>),
    /// `Map<K, V>` value as an association list.
    Map(Vec<(WitnessValue, WitnessValue)>),
    /// Escape hatch for values we can pretty-print but not model
    /// structurally (e.g. solver-internal sorts).
    Opaque {
        /// Backend-supplied display string.
        display: String,
        /// Optional type label.
        #[serde(skip_serializing_if = "Option::is_none")]
        ty: Option<String>,
    },
}
