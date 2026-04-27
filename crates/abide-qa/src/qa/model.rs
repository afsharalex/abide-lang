//! `FlowModel` types — the structural model that QA queries operate on.

use std::collections::HashMap;

/// The complete structural model of a specification.
/// Built from IR, queried by QA commands.
#[derive(Debug, Clone)]
pub struct FlowModel {
    /// State graphs per owner, per field.
    /// Key: `(owner_name, field_name)`, where owner is an entity or system.
    pub state_graphs: HashMap<(String, String), StateGraph>,
    /// Field graph metadata for every entity/system field QA can see, including
    /// unsupported graph targets. Used for precise diagnostics.
    pub field_graph_meta: HashMap<(String, String), FieldGraphMeta>,
    /// System information.
    pub systems: HashMap<String, SystemInfo>,
    /// Entity names.
    pub entity_names: Vec<String>,
    /// System names.
    pub system_names: Vec<String>,
    /// Type names.
    pub type_names: Vec<String>,
    /// Action contracts per entity.
    /// Key: `(entity_name, action_name)`
    pub action_contracts: HashMap<(String, String), ActionContract>,
    /// fsm declarations per owner, per field.
    /// Key: `(owner_name, field_name)`. Each entry holds the
    /// declared transition table (NOT the action-extracted state
    /// graph) so QA queries can distinguish "what the user declared"
    /// from "what actions actually drive."
    pub fsm_decls: HashMap<(String, String), FsmInfo>,
}

/// What kind of declaration owns a graph-addressable field.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OwnerKind {
    Entity,
    System,
}

/// The graph-extraction status of one owner field.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldGraphMeta {
    pub owner: String,
    pub field: String,
    pub owner_kind: OwnerKind,
    pub graphable: bool,
    pub type_name: String,
}

/// structural info for one fsm declaration. The
/// `terminal_states` set is precomputed at extraction time for fast
/// `ask terminal states of E::field` queries.
#[derive(Debug, Clone)]
pub struct FsmInfo {
    pub owner: String,
    pub field: String,
    pub enum_name: String,
    /// Flattened (from, to) pairs from the declared transition table.
    pub transitions: Vec<(String, String)>,
    /// Variants with no outgoing transitions in the declared table.
    pub terminal_states: Vec<String>,
}

/// A state machine graph for a single finite owner field.
#[derive(Debug, Clone)]
pub struct StateGraph {
    pub owner: String,
    pub owner_kind: OwnerKind,
    pub field: String,
    /// All states in the field's finite domain.
    pub states: Vec<String>,
    /// Initial state (from field default), if known.
    pub initial: Option<String>,
    /// All transitions.
    pub transitions: Vec<TransitionEdge>,
}

/// A single edge in a state graph.
#[derive(Debug, Clone)]
pub struct TransitionEdge {
    /// The action/transition name that causes this state change.
    pub action: String,
    /// Source state (enum variant), or None if guard doesn't constrain the source.
    pub from: Option<String>,
    /// Target state (enum variant).
    pub to: String,
}

/// Structural information about a system.
#[derive(Debug, Clone)]
pub struct SystemInfo {
    pub name: String,
    /// Entity names referenced by this system.
    pub entities: Vec<String>,
    /// Events in this system.
    pub events: Vec<EventInfo>,
}

/// Structural information about an event.
#[derive(Debug, Clone)]
pub struct EventInfo {
    pub name: String,
    /// Cross-system calls made by this event.
    pub cross_calls: Vec<CrossCall>,
    /// Entity actions applied by this event.
    pub applies: Vec<ApplyInfo>,
}

/// A cross-system call from an event.
#[derive(Debug, Clone)]
pub struct CrossCall {
    pub target_system: String,
    pub target_event: String,
}

/// An entity action application within an event.
#[derive(Debug, Clone)]
pub struct ApplyInfo {
    pub entity: String,
    pub action: String,
}

/// Contract information for an entity action (transition).
#[derive(Debug, Clone)]
pub struct ActionContract {
    /// Entity name.
    pub entity: String,
    /// Action/transition name.
    pub action: String,
    /// Guard (requires) clause as a human-readable string.
    pub guard: String,
    /// Postcondition (ensures) clause, if present.
    pub postcondition: Option<String>,
    /// Fields updated by this action.
    pub updates: Vec<String>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn flow_model_construction() {
        let mut sg = StateGraph {
            owner: "Order".to_owned(),
            owner_kind: OwnerKind::Entity,
            field: "status".to_owned(),
            states: vec!["Pending".to_owned(), "Confirmed".to_owned()],
            initial: Some("Pending".to_owned()),
            transitions: vec![TransitionEdge {
                action: "submit".to_owned(),
                from: Some("Pending".to_owned()),
                to: "Confirmed".to_owned(),
            }],
        };
        assert_eq!(sg.states.len(), 2);
        assert_eq!(sg.transitions.len(), 1);
        sg.transitions.push(TransitionEdge {
            action: "cancel".to_owned(),
            from: Some("Pending".to_owned()),
            to: "Cancelled".to_owned(),
        });
        assert_eq!(sg.transitions.len(), 2);
    }
}
