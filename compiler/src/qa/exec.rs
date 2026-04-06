//! QA query executor — runs parsed queries against a `FlowModel`.
//!
//! All queries are graph-based — no SMT, microsecond response times.

use std::collections::HashMap;

use super::ast::{BlockArg, BlockPredicate, QAStatement, Query};
use super::graph;
use super::model::{FlowModel, StateGraph, TransitionEdge};

/// Result of executing a QA query.
#[derive(Debug, Clone)]
pub enum QueryResult {
    /// Boolean result (reachable, cycles, deadlock, etc.)
    Bool(bool),
    /// A set of state names (terminal, initial)
    StateSet(Vec<String>),
    /// A path: sequence of `(action, target_state)` steps
    Path(Vec<(String, String)>),
    /// A list of names (entities, systems, types)
    NameList(Vec<String>),
    /// Transition edges matching the query
    Transitions(Vec<TransitionInfo>),
    /// Tabular results from block-form queries
    Table {
        columns: Vec<String>,
        rows: Vec<Vec<String>>,
    },
    /// Expression string (for always/eventually — not yet evaluated)
    ExprStr(String),
    /// Error — query could not be executed
    Error(String),
}

/// A transition edge with display-friendly fields.
#[derive(Debug, Clone)]
pub struct TransitionInfo {
    pub action: String,
    pub from: String,
    pub to: String,
}

/// The verb that produced this result (for formatting).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verb {
    Ask,
    Explain,
    Assert,
}

/// Execute a QA statement, returning the verb and result.
pub fn execute_statement(model: &FlowModel, stmt: &QAStatement) -> (Verb, QueryResult) {
    match stmt {
        QAStatement::Ask(q) => (Verb::Ask, execute_query(model, q)),
        QAStatement::Explain(q) => (Verb::Explain, execute_query(model, q)),
        QAStatement::Assert(q) => (Verb::Assert, execute_query(model, q)),
        QAStatement::Load(_) | QAStatement::AbideBlock(_) => (
            Verb::Ask,
            QueryResult::Error(
                "load/abide blocks are handled by the runner, not the executor".to_owned(),
            ),
        ),
    }
}

/// Execute a single query against the `FlowModel`.
#[allow(clippy::too_many_lines)]
pub fn execute_query(model: &FlowModel, query: &Query) -> QueryResult {
    match query {
        Query::Reachable {
            entity,
            field,
            state,
        } => match lookup_graph(model, entity, field) {
            Some(sg) => {
                if let Some(ref init) = sg.initial {
                    QueryResult::Bool(graph::is_reachable(sg, init, state))
                } else {
                    QueryResult::Error(format!("no initial state for {entity}.{field}"))
                }
            }
            None => QueryResult::Error(format!("no state graph for {entity}.{field}")),
        },
        Query::Path {
            entity,
            field,
            from,
            to,
        } => match lookup_graph(model, entity, field) {
            Some(sg) => match graph::find_path(sg, from, to) {
                Some(path) => QueryResult::Path(path),
                None => QueryResult::Path(vec![]),
            },
            None => QueryResult::Error(format!("no state graph for {entity}.{field}")),
        },
        Query::Terminal { entity, field } => match lookup_graph(model, entity, field) {
            Some(sg) => QueryResult::StateSet(graph::terminal_states(sg)),
            None => QueryResult::Error(format!("no state graph for {entity}.{field}")),
        },
        Query::Initial { entity, field } => match lookup_graph(model, entity, field) {
            Some(sg) => QueryResult::StateSet(graph::initial_states(sg)),
            None => QueryResult::Error(format!("no state graph for {entity}.{field}")),
        },
        Query::Cycles { entity, field } => match lookup_graph(model, entity, field) {
            Some(sg) => QueryResult::Bool(graph::has_cycles(sg)),
            None => QueryResult::Error(format!("no state graph for {entity}.{field}")),
        },
        Query::Transitions {
            entity,
            field,
            state,
        } => match lookup_graph(model, entity, field) {
            Some(sg) => {
                let edges = graph::transitions_from(sg, state);
                QueryResult::Transitions(edges.into_iter().map(edge_to_info).collect())
            }
            None => QueryResult::Error(format!("no state graph for {entity}.{field}")),
        },
        Query::Updates {
            entity,
            field,
            from,
            to,
        } => match lookup_graph(model, entity, field) {
            Some(sg) => {
                let matching: Vec<TransitionInfo> = sg
                    .transitions
                    .iter()
                    .filter(|e| e.from.as_deref() == Some(from.as_str()) && e.to == *to)
                    .map(edge_to_info)
                    .collect();
                QueryResult::Transitions(matching)
            }
            None => QueryResult::Error(format!("no state graph for {entity}.{field}")),
        },

        Query::Entities => QueryResult::NameList(model.entity_names.clone()),
        Query::Systems => QueryResult::NameList(model.systems.keys().cloned().collect()),
        Query::Types => QueryResult::NameList(model.type_names.clone()),
        Query::Invariants { entity } => {
            // Return all action contracts (guards) for the entity as invariants.
            // These are the requires clauses that constrain entity state transitions.
            let mut invariants: Vec<String> = Vec::new();
            for ((ent, action), contract) in &model.action_contracts {
                if ent == entity {
                    if contract.guard != "true" {
                        invariants.push(format!("{action}: requires {}", contract.guard));
                    }
                }
            }
            if invariants.is_empty() {
                QueryResult::NameList(vec![format!("no action guards found for '{entity}'")])
            } else {
                invariants.sort();
                QueryResult::NameList(invariants)
            }
        }
        Query::Contracts { entity, action } => {
            match model.action_contracts.get(&(entity.clone(), action.clone())) {
                Some(contract) => {
                    let mut parts = Vec::new();
                    parts.push(format!("requires {}", contract.guard));
                    if let Some(ref post) = contract.postcondition {
                        parts.push(format!("ensures {post}"));
                    }
                    for update in &contract.updates {
                        parts.push(format!("updates {update}"));
                    }
                    QueryResult::NameList(parts)
                }
                None => QueryResult::Error(format!(
                    "no action '{action}' found on entity '{entity}'"
                )),
            }
        }
        Query::Events { entity, field } => {
            let mut event_names = Vec::new();
            for sys in model.systems.values() {
                for ev in &sys.events {
                    for apply in &ev.applies {
                        if let Some(sg) = lookup_graph(model, entity, field) {
                            if sg.transitions.iter().any(|t| t.action == apply.action) {
                                event_names.push(format!("{}::{}", sys.name, ev.name));
                            }
                        }
                    }
                }
            }
            QueryResult::NameList(event_names)
        }
        Query::MatchCoverage { entity, field } => match lookup_graph(model, entity, field) {
            Some(sg) => {
                let terminals = graph::terminal_states(sg);
                if terminals.is_empty() {
                    QueryResult::Bool(true)
                } else {
                    QueryResult::StateSet(terminals)
                }
            }
            None => QueryResult::Error(format!("no state graph for {entity}.{field}")),
        },
        Query::CrossCalls { system } => match model.systems.get(system) {
            Some(sys) => {
                let calls: Vec<String> = sys
                    .events
                    .iter()
                    .flat_map(|ev| ev.cross_calls.iter())
                    .map(|cc| format!("{}::{}", cc.target_system, cc.target_event))
                    .collect();
                QueryResult::NameList(calls)
            }
            None => QueryResult::Error(format!("no system named '{system}'")),
        },
        Query::Deadlock { system } => match model.systems.get(system) {
            Some(sys) => {
                let mut has_deadlock = false;
                for entity_name in &sys.entities {
                    for ((e, _), sg) in &model.state_graphs {
                        if e == entity_name {
                            let terminals = graph::terminal_states(sg);
                            if let Some(ref init) = sg.initial {
                                for term in &terminals {
                                    if graph::is_reachable(sg, init, term) {
                                        has_deadlock = true;
                                    }
                                }
                            }
                        }
                    }
                }
                QueryResult::Bool(has_deadlock)
            }
            None => QueryResult::Error(format!("no system named '{system}'")),
        },

        Query::Not(inner) => match execute_query(model, inner) {
            QueryResult::Bool(b) => QueryResult::Bool(!b),
            other => other,
        },
        Query::AlwaysExpr(expr) => QueryResult::ExprStr(format!("always ({expr})")),
        Query::EventuallyExpr(expr) => QueryResult::ExprStr(format!("eventually ({expr})")),

        Query::Block {
            bindings,
            predicates,
            select,
        } => execute_block(model, bindings, predicates, select),
    }
}

fn execute_block(
    model: &FlowModel,
    bindings: &[String],
    predicates: &[BlockPredicate],
    select: &[String],
) -> QueryResult {
    let mut rows: Vec<Vec<String>> = Vec::new();
    let mut candidates: Vec<Vec<String>> = Vec::new();
    for ((entity, field), sg) in &model.state_graphs {
        for state in &sg.states {
            candidates.push(vec![entity.clone(), field.clone(), state.clone()]);
        }
    }
    for candidate in &candidates {
        let env = bind_vars(bindings, candidate);
        let mut pass = true;
        for pred in predicates {
            let matches = eval_block_predicate(model, pred, &env);
            if pred.negated {
                if matches {
                    pass = false;
                    break;
                }
            } else if !matches {
                pass = false;
                break;
            }
        }
        if pass {
            let row: Vec<String> = select
                .iter()
                .map(|col| env.get(col.as_str()).cloned().unwrap_or_default())
                .collect();
            rows.push(row);
        }
    }
    QueryResult::Table {
        columns: select.to_vec(),
        rows,
    }
}

fn bind_vars<'a>(bindings: &'a [String], values: &'a [String]) -> HashMap<&'a str, String> {
    bindings
        .iter()
        .zip(values.iter())
        .map(|(name, val)| (name.as_str(), val.clone()))
        .collect()
}

fn eval_block_predicate(
    model: &FlowModel,
    pred: &BlockPredicate,
    env: &HashMap<&str, String>,
) -> bool {
    let args: Vec<String> = pred.args.iter().map(|a| resolve_arg(a, env)).collect();
    match pred.name.as_str() {
        "state" => {
            args.len() >= 3
                && lookup_graph(model, &args[0], &args[1])
                    .is_some_and(|sg| sg.states.contains(&args[2]))
        }
        "transition" => {
            if args.len() >= 2 {
                let from_val = get_named_arg(&pred.args, "from", env);
                let to_val = get_named_arg(&pred.args, "to", env);
                lookup_graph(model, &args[0], &args[1]).is_some_and(|sg| {
                    sg.transitions.iter().any(|t| {
                        let from_ok = from_val
                            .as_ref()
                            .is_none_or(|f| t.from.as_deref() == Some(f.as_str()));
                        let to_ok = to_val.as_ref().is_none_or(|v| t.to == *v);
                        from_ok && to_ok
                    })
                })
            } else {
                false
            }
        }
        "initial" => {
            args.len() >= 3
                && lookup_graph(model, &args[0], &args[1])
                    .and_then(|sg| sg.initial.as_ref())
                    .is_some_and(|init| *init == args[2])
        }
        "terminal" => {
            args.len() >= 3
                && lookup_graph(model, &args[0], &args[1])
                    .is_some_and(|sg| graph::terminal_states(sg).contains(&args[2]))
        }
        _ => false,
    }
}

fn resolve_arg(arg: &BlockArg, env: &HashMap<&str, String>) -> String {
    match arg {
        BlockArg::Positional(name) => env
            .get(name.as_str())
            .cloned()
            .unwrap_or_else(|| name.clone()),
        BlockArg::Named(_, value) => env
            .get(value.as_str())
            .cloned()
            .unwrap_or_else(|| value.clone()),
    }
}

fn get_named_arg(args: &[BlockArg], name: &str, env: &HashMap<&str, String>) -> Option<String> {
    args.iter().find_map(|a| {
        if let BlockArg::Named(n, v) = a {
            if n == name {
                return Some(env.get(v.as_str()).cloned().unwrap_or_else(|| v.clone()));
            }
        }
        None
    })
}

fn lookup_graph<'a>(model: &'a FlowModel, entity: &str, field: &str) -> Option<&'a StateGraph> {
    model
        .state_graphs
        .get(&(entity.to_owned(), field.to_owned()))
}

fn edge_to_info(edge: &TransitionEdge) -> TransitionInfo {
    TransitionInfo {
        action: edge.action.clone(),
        from: edge.from.clone().unwrap_or_else(|| "*".to_owned()),
        to: edge.to.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::qa::model::*;

    fn commerce_model() -> FlowModel {
        let mut state_graphs = HashMap::new();
        state_graphs.insert(
            ("Order".to_owned(), "status".to_owned()),
            StateGraph {
                entity: "Order".to_owned(),
                field: "status".to_owned(),
                states: vec![
                    "Pending".to_owned(),
                    "Confirmed".to_owned(),
                    "Shipped".to_owned(),
                    "Cancelled".to_owned(),
                ],
                initial: Some("Pending".to_owned()),
                transitions: vec![
                    TransitionEdge {
                        action: "submit".to_owned(),
                        from: Some("Pending".to_owned()),
                        to: "Confirmed".to_owned(),
                    },
                    TransitionEdge {
                        action: "ship".to_owned(),
                        from: Some("Confirmed".to_owned()),
                        to: "Shipped".to_owned(),
                    },
                    TransitionEdge {
                        action: "cancel".to_owned(),
                        from: Some("Pending".to_owned()),
                        to: "Cancelled".to_owned(),
                    },
                ],
            },
        );
        let mut systems = HashMap::new();
        systems.insert(
            "Commerce".to_owned(),
            SystemInfo {
                name: "Commerce".to_owned(),
                entities: vec!["Order".to_owned()],
                events: vec![
                    EventInfo {
                        name: "submit_order".to_owned(),
                        cross_calls: vec![],
                        applies: vec![ApplyInfo {
                            entity: "o".to_owned(),
                            action: "submit".to_owned(),
                        }],
                    },
                    EventInfo {
                        name: "ship_order".to_owned(),
                        cross_calls: vec![],
                        applies: vec![ApplyInfo {
                            entity: "o".to_owned(),
                            action: "ship".to_owned(),
                        }],
                    },
                ],
            },
        );
        FlowModel {
            state_graphs,
            systems,
            entity_names: vec!["Order".to_owned()],
            type_names: vec!["OrderStatus".to_owned()],
            action_contracts: std::collections::HashMap::new(),
        }
    }

    #[test]
    fn exec_reachable_true() {
        let m = commerce_model();
        let q = Query::Reachable {
            entity: "Order".into(),
            field: "status".into(),
            state: "Shipped".into(),
        };
        assert!(matches!(execute_query(&m, &q), QueryResult::Bool(true)));
    }

    #[test]
    fn exec_reachable_false() {
        let m = commerce_model();
        let q = Query::Reachable {
            entity: "Order".into(),
            field: "status".into(),
            state: "Refunded".into(),
        };
        assert!(matches!(execute_query(&m, &q), QueryResult::Bool(false)));
    }

    #[test]
    fn exec_path_found() {
        let m = commerce_model();
        let q = Query::Path {
            entity: "Order".into(),
            field: "status".into(),
            from: "Pending".into(),
            to: "Shipped".into(),
        };
        match execute_query(&m, &q) {
            QueryResult::Path(p) => {
                assert_eq!(p.len(), 2);
                assert_eq!(p[0].0, "submit");
                assert_eq!(p[1].0, "ship");
            }
            other => panic!("expected Path, got {other:?}"),
        }
    }

    #[test]
    fn exec_path_not_found() {
        let m = commerce_model();
        let q = Query::Path {
            entity: "Order".into(),
            field: "status".into(),
            from: "Shipped".into(),
            to: "Pending".into(),
        };
        match execute_query(&m, &q) {
            QueryResult::Path(p) => assert!(p.is_empty()),
            other => panic!("expected empty Path, got {other:?}"),
        }
    }

    #[test]
    fn exec_terminal() {
        let m = commerce_model();
        match execute_query(
            &m,
            &Query::Terminal {
                entity: "Order".into(),
                field: "status".into(),
            },
        ) {
            QueryResult::StateSet(s) => {
                assert!(s.contains(&"Shipped".to_owned()));
                assert!(s.contains(&"Cancelled".to_owned()));
            }
            other => panic!("expected StateSet, got {other:?}"),
        }
    }

    #[test]
    fn exec_initial() {
        let m = commerce_model();
        match execute_query(
            &m,
            &Query::Initial {
                entity: "Order".into(),
                field: "status".into(),
            },
        ) {
            QueryResult::StateSet(s) => assert!(s.contains(&"Pending".to_owned())),
            other => panic!("expected StateSet, got {other:?}"),
        }
    }

    #[test]
    fn exec_cycles_false() {
        let m = commerce_model();
        assert!(matches!(
            execute_query(
                &m,
                &Query::Cycles {
                    entity: "Order".into(),
                    field: "status".into()
                }
            ),
            QueryResult::Bool(false)
        ));
    }

    #[test]
    fn exec_not_cycles() {
        let m = commerce_model();
        let q = Query::Not(Box::new(Query::Cycles {
            entity: "Order".into(),
            field: "status".into(),
        }));
        assert!(matches!(execute_query(&m, &q), QueryResult::Bool(true)));
    }

    #[test]
    fn exec_entities() {
        let m = commerce_model();
        match execute_query(&m, &Query::Entities) {
            QueryResult::NameList(n) => assert!(n.contains(&"Order".to_owned())),
            other => panic!("got {other:?}"),
        }
    }

    #[test]
    fn exec_systems() {
        let m = commerce_model();
        match execute_query(&m, &Query::Systems) {
            QueryResult::NameList(n) => assert!(n.contains(&"Commerce".to_owned())),
            other => panic!("got {other:?}"),
        }
    }

    #[test]
    fn exec_transitions() {
        let m = commerce_model();
        let q = Query::Transitions {
            entity: "Order".into(),
            field: "status".into(),
            state: "Pending".into(),
        };
        match execute_query(&m, &q) {
            QueryResult::Transitions(ts) => {
                assert_eq!(ts.len(), 2);
            }
            other => panic!("got {other:?}"),
        }
    }

    #[test]
    fn exec_updates() {
        let m = commerce_model();
        let q = Query::Updates {
            entity: "Order".into(),
            field: "status".into(),
            from: "Pending".into(),
            to: "Confirmed".into(),
        };
        match execute_query(&m, &q) {
            QueryResult::Transitions(ts) => {
                assert_eq!(ts.len(), 1);
                assert_eq!(ts[0].action, "submit");
            }
            other => panic!("got {other:?}"),
        }
    }

    #[test]
    fn exec_events_on_field() {
        let m = commerce_model();
        match execute_query(
            &m,
            &Query::Events {
                entity: "Order".into(),
                field: "status".into(),
            },
        ) {
            QueryResult::NameList(n) => {
                assert!(n.iter().any(|s| s.contains("submit_order")));
            }
            other => panic!("got {other:?}"),
        }
    }

    #[test]
    fn exec_cross_calls_empty() {
        let m = commerce_model();
        match execute_query(
            &m,
            &Query::CrossCalls {
                system: "Commerce".into(),
            },
        ) {
            QueryResult::NameList(n) => assert!(n.is_empty()),
            other => panic!("got {other:?}"),
        }
    }

    #[test]
    fn exec_block_terminal_states() {
        let m = commerce_model();
        let q = Query::Block {
            bindings: vec!["e".into(), "f".into(), "s".into()],
            predicates: vec![
                BlockPredicate {
                    negated: false,
                    name: "state".into(),
                    args: vec![
                        BlockArg::Positional("e".into()),
                        BlockArg::Positional("f".into()),
                        BlockArg::Positional("s".into()),
                    ],
                },
                BlockPredicate {
                    negated: true,
                    name: "transition".into(),
                    args: vec![
                        BlockArg::Positional("e".into()),
                        BlockArg::Positional("f".into()),
                        BlockArg::Named("from".into(), "s".into()),
                    ],
                },
            ],
            select: vec!["e".into(), "f".into(), "s".into()],
        };
        match execute_query(&m, &q) {
            QueryResult::Table { rows, .. } => {
                let states: Vec<&str> = rows.iter().map(|r| r[2].as_str()).collect();
                assert!(states.contains(&"Shipped"));
                assert!(states.contains(&"Cancelled"));
                assert!(!states.contains(&"Pending"));
            }
            other => panic!("expected Table, got {other:?}"),
        }
    }

    #[test]
    fn exec_error_missing_graph() {
        let m = commerce_model();
        assert!(matches!(
            execute_query(
                &m,
                &Query::Reachable {
                    entity: "X".into(),
                    field: "y".into(),
                    state: "Z".into()
                }
            ),
            QueryResult::Error(_)
        ));
    }

    #[test]
    fn exec_assert_semantics() {
        let m = commerce_model();
        let stmt = QAStatement::Assert(Query::Reachable {
            entity: "Order".into(),
            field: "status".into(),
            state: "Shipped".into(),
        });
        let (verb, result) = execute_statement(&m, &stmt);
        assert_eq!(verb, Verb::Assert);
        assert!(matches!(result, QueryResult::Bool(true)));
    }
}
