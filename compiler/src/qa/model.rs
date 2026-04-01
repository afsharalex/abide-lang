//! `FlowModel` types — the structural model that QA queries operate on.

use std::collections::HashMap;

/// The complete structural model of a specification.
/// Built from IR, queried by QA commands.
#[derive(Debug, Clone)]
pub struct FlowModel {
    /// State graphs per entity, per field.
    /// Key: `(entity_name, field_name)`
    pub state_graphs: HashMap<(String, String), StateGraph>,
    /// System information.
    pub systems: HashMap<String, SystemInfo>,
    /// Entity names.
    pub entity_names: Vec<String>,
    /// Type names.
    pub type_names: Vec<String>,
}

/// A state machine graph for a single enum-typed field of an entity.
#[derive(Debug, Clone)]
pub struct StateGraph {
    pub entity: String,
    pub field: String,
    /// All states (enum variant names).
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn flow_model_construction() {
        let mut sg = StateGraph {
            entity: "Order".to_owned(),
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
