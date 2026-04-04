//! Extract a `FlowModel` from IR.
//!
//! Walks the `IRProgram` to build state graphs for each enum-typed entity field,
//! and extracts system/event structure for cross-system queries.

use std::collections::HashMap;

use crate::ir::types::{IRAction, IREntity, IRExpr, IRProgram, IRSystem, IRType};

use super::model::{
    ApplyInfo, CrossCall, EventInfo, FlowModel, StateGraph, SystemInfo, TransitionEdge,
};

/// Extract a `FlowModel` from an `IRProgram`.
pub fn extract(ir: &IRProgram) -> FlowModel {
    let mut state_graphs = HashMap::new();

    for entity in &ir.entities {
        let graphs = extract_entity_graphs(entity, ir);
        for sg in graphs {
            state_graphs.insert((sg.entity.clone(), sg.field.clone()), sg);
        }
    }

    let mut systems = HashMap::new();
    for system in &ir.systems {
        systems.insert(system.name.clone(), extract_system_info(system));
    }

    let entity_names = ir.entities.iter().map(|e| e.name.clone()).collect();
    let type_names = ir.types.iter().map(|t| t.name.clone()).collect();

    FlowModel {
        state_graphs,
        systems,
        entity_names,
        type_names,
    }
}

/// Extract state graphs for all enum-typed fields of an entity.
fn extract_entity_graphs(entity: &IREntity, _ir: &IRProgram) -> Vec<StateGraph> {
    let mut graphs = Vec::new();

    for field in &entity.fields {
        // Only build state graphs for enum-typed fields
        let variants = match &field.ty {
            IRType::Enum { variants: vs, .. } => vs.iter().map(|v| v.name.clone()).collect::<Vec<_>>(),
            _ => continue,
        };

        let initial = field.default.as_ref().and_then(extract_ctor_name);

        let mut transitions = Vec::new();
        for transition in &entity.transitions {
            // Check if this transition updates this field
            for update in &transition.updates {
                if update.field == field.name {
                    let Some(to) = extract_ctor_name(&update.value) else {
                        continue;
                    };
                    let from = extract_guard_state(&transition.guard, &field.name);
                    transitions.push(TransitionEdge {
                        action: transition.name.clone(),
                        from,
                        to,
                    });
                }
            }
        }

        graphs.push(StateGraph {
            entity: entity.name.clone(),
            field: field.name.clone(),
            states: variants,
            initial,
            transitions,
        });
    }

    graphs
}

/// Extract a constructor name from an IR expression (Ctor node).
fn extract_ctor_name(expr: &IRExpr) -> Option<String> {
    match expr {
        IRExpr::Ctor { ctor, .. } => Some(ctor.clone()),
        _ => None,
    }
}

/// Try to extract the source state from a guard expression.
/// Looks for patterns like `status == @Pending` in the guard.
fn extract_guard_state(guard: &IRExpr, field_name: &str) -> Option<String> {
    match guard {
        // Direct: field == @State
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpEq" => {
            if is_field_ref(left, field_name) {
                return extract_ctor_name(right);
            }
            if is_field_ref(right, field_name) {
                return extract_ctor_name(left);
            }
            None
        }
        // Conjunction: ... and field == @State
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpAnd" => {
            extract_guard_state(left, field_name).or_else(|| extract_guard_state(right, field_name))
        }
        _ => None,
    }
}

/// Check if an expression is a reference to a field (`Var` with `field_name`).
fn is_field_ref(expr: &IRExpr, field_name: &str) -> bool {
    match expr {
        IRExpr::Var { name, .. } => name == field_name,
        _ => false,
    }
}

/// Extract system information from an `IRSystem`.
fn extract_system_info(system: &IRSystem) -> SystemInfo {
    let events = system
        .events
        .iter()
        .map(|ev| {
            let mut cross_calls = Vec::new();
            let mut applies = Vec::new();
            collect_event_actions(&ev.body, &mut cross_calls, &mut applies);
            EventInfo {
                name: ev.name.clone(),
                cross_calls,
                applies,
            }
        })
        .collect();

    SystemInfo {
        name: system.name.clone(),
        entities: system.entities.clone(),
        events,
    }
}

/// Recursively collect cross-calls and applies from event actions.
fn collect_event_actions(
    actions: &[IRAction],
    cross_calls: &mut Vec<CrossCall>,
    applies: &mut Vec<ApplyInfo>,
) {
    for action in actions {
        match action {
            IRAction::Apply {
                target, transition, ..
            } => {
                // target is a variable name bound to an entity
                applies.push(ApplyInfo {
                    entity: target.clone(),
                    action: transition.clone(),
                });
            }
            IRAction::CrossCall { system, event, .. } => {
                cross_calls.push(CrossCall {
                    target_system: system.clone(),
                    target_event: event.clone(),
                });
            }
            IRAction::Choose { ops, .. } | IRAction::ForAll { ops, .. } => {
                collect_event_actions(ops, cross_calls, applies);
            }
            IRAction::Create { .. } | IRAction::ExprStmt { .. } => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::types::*;

    fn make_enum_field(name: &str, variants: &[&str], default: Option<&str>) -> IRField {
        IRField {
            name: name.to_owned(),
            ty: IRType::Enum {
                name: format!("{}Status", name),
                variants: variants
                    .iter()
                    .map(|s| crate::ir::types::IRVariant::simple(*s))
                    .collect(),
            },
            default: default.map(|d| IRExpr::Ctor {
                enum_name: format!("{}Status", name),
                ctor: d.to_owned(),
                args: vec![],
                span: None,
            }),
        }
    }

    fn make_transition(
        name: &str,
        field: &str,
        guard_state: Option<&str>,
        to: &str,
    ) -> IRTransition {
        let guard = match guard_state {
            Some(from) => IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: field.to_owned(),
                    ty: IRType::String,
                    span: None,
                }),
                right: Box::new(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: from.to_owned(),
                    args: vec![],
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            },
            None => IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
        };
        IRTransition {
            name: name.to_owned(),
            refs: vec![],
            params: vec![],
            guard,
            updates: vec![IRUpdate {
                field: field.to_owned(),
                value: IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: to.to_owned(),
                    args: vec![],
                    span: None,
                },
            }],
            postcondition: None,
        }
    }

    #[test]
    fn extract_simple_entity() {
        let entity = IREntity {
            name: "Order".to_owned(),
            fields: vec![make_enum_field(
                "status",
                &["Pending", "Confirmed", "Shipped"],
                Some("Pending"),
            )],
            transitions: vec![
                make_transition("submit", "status", Some("Pending"), "Confirmed"),
                make_transition("ship", "status", Some("Confirmed"), "Shipped"),
            ],
        };
        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        };
        let model = extract(&ir);
        let sg = model
            .state_graphs
            .get(&("Order".to_owned(), "status".to_owned()))
            .expect("state graph for Order.status");
        assert_eq!(sg.states.len(), 3);
        assert_eq!(sg.initial, Some("Pending".to_owned()));
        assert_eq!(sg.transitions.len(), 2);
        assert_eq!(sg.transitions[0].action, "submit");
        assert_eq!(sg.transitions[0].from, Some("Pending".to_owned()));
        assert_eq!(sg.transitions[0].to, "Confirmed");
        assert_eq!(sg.transitions[1].action, "ship");
        assert_eq!(sg.transitions[1].to, "Shipped");
    }

    #[test]
    fn extract_multi_field_entity() {
        let entity = IREntity {
            name: "Ticket".to_owned(),
            fields: vec![
                make_enum_field("status", &["Open", "Closed"], Some("Open")),
                make_enum_field("priority", &["Low", "High"], Some("Low")),
                IRField {
                    name: "title".to_owned(),
                    ty: IRType::String,
                    default: None,
                },
            ],
            transitions: vec![make_transition("close", "status", Some("Open"), "Closed")],
        };
        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        };
        let model = extract(&ir);
        // Should have graphs for status and priority, but not title (String, not Enum)
        assert!(model
            .state_graphs
            .contains_key(&("Ticket".to_owned(), "status".to_owned())));
        assert!(model
            .state_graphs
            .contains_key(&("Ticket".to_owned(), "priority".to_owned())));
        assert!(!model
            .state_graphs
            .contains_key(&("Ticket".to_owned(), "title".to_owned())));
    }

    #[test]
    fn extract_system_info() {
        let system = IRSystem {
            name: "Commerce".to_owned(),
            entities: vec!["Order".to_owned()],
            events: vec![IREvent {
                name: "submit_order".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                postcondition: None,
                body: vec![IRAction::Choose {
                    var: "o".to_owned(),
                    entity: "Order".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                        span: None,
                    }),
                    ops: vec![IRAction::Apply {
                        target: "o".to_owned(),
                        transition: "submit".to_owned(),
                        refs: vec![],
                        args: vec![],
                    }],
                }],
            }],
            schedule: IRSchedule {
                when: vec![],
                idle: false,
            },
        };
        let info = super::extract_system_info(&system);
        assert_eq!(info.name, "Commerce");
        assert_eq!(info.entities, vec!["Order"]);
        assert_eq!(info.events.len(), 1);
        assert_eq!(info.events[0].name, "submit_order");
        assert_eq!(info.events[0].applies.len(), 1);
        assert_eq!(info.events[0].applies[0].action, "submit");
    }
}
