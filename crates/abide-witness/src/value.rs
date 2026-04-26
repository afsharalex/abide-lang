use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

/// Stable identifier for an entity slot in a concrete witness state.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct EntitySlotRef {
    entity: String,
    slot: usize,
}

impl EntitySlotRef {
    pub fn new(entity: impl Into<String>, slot: usize) -> Self {
        Self {
            entity: entity.into(),
            slot,
        }
    }

    pub fn entity(&self) -> &str {
        &self.entity
    }

    pub fn slot(&self) -> usize {
        self.slot
    }
}

/// Concrete semantic value carried in witness payloads.
///
/// This is intentionally solver-agnostic and shared across the operational and
/// relational witness families.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", content = "value", rename_all = "snake_case")]
pub enum WitnessValue {
    Unknown,
    Int(i64),
    Bool(bool),
    Real(String),
    Float(String),
    String(String),
    Identity(String),
    EnumVariant {
        enum_name: String,
        variant: String,
    },
    SlotRef(EntitySlotRef),
    Tuple(Vec<WitnessValue>),
    Record(BTreeMap<String, WitnessValue>),
    Set(Vec<WitnessValue>),
    Seq(Vec<WitnessValue>),
    Map(Vec<(WitnessValue, WitnessValue)>),
    Opaque {
        display: String,
        #[serde(skip_serializing_if = "Option::is_none")]
        ty: Option<String>,
    },
}
