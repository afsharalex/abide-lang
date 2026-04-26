//! Graph algorithms for QA queries.
//!
//! Operates on `StateGraph` — pure graph traversals, no SMT.

use std::collections::{HashMap, HashSet, VecDeque};

use super::model::{StateGraph, TransitionEdge};

/// Check if state `to` is reachable from state `from` in the state graph.
pub fn is_reachable(graph: &StateGraph, from: &str, to: &str) -> bool {
    if from == to {
        return true;
    }
    let adj = build_adjacency(graph);
    let mut visited = HashSet::new();
    let mut queue = VecDeque::new();
    queue.push_back(from.to_owned());
    visited.insert(from.to_owned());

    while let Some(current) = queue.pop_front() {
        if let Some(neighbors) = adj.get(&current) {
            for (next, _action) in neighbors {
                if next == to {
                    return true;
                }
                if visited.insert(next.clone()) {
                    queue.push_back(next.clone());
                }
            }
        }
    }
    false
}

/// Find a path (sequence of actions) from state `from` to state `to`.
/// Returns the list of `(action_name, target_state)` steps, or `None` if unreachable.
pub fn find_path(graph: &StateGraph, from: &str, to: &str) -> Option<Vec<(String, String)>> {
    if from == to {
        return Some(vec![]);
    }
    let adj = build_adjacency(graph);
    let mut visited = HashSet::new();
    // BFS with parent tracking: state -> (action, prev_state)
    let mut parent: HashMap<String, (String, String)> = HashMap::new();
    let mut queue = VecDeque::new();
    queue.push_back(from.to_owned());
    visited.insert(from.to_owned());

    while let Some(current) = queue.pop_front() {
        if let Some(neighbors) = adj.get(&current) {
            for (next, action) in neighbors {
                if visited.insert(next.clone()) {
                    parent.insert(next.clone(), (action.clone(), current.clone()));
                    if next == to {
                        // Reconstruct path
                        let mut path = Vec::new();
                        let mut cur = to.to_owned();
                        while let Some((act, prev)) = parent.get(&cur) {
                            path.push((act.clone(), cur.clone()));
                            cur = prev.clone();
                        }
                        path.reverse();
                        return Some(path);
                    }
                    queue.push_back(next.clone());
                }
            }
        }
    }
    None
}

/// Find all terminal states (states with no outgoing transitions).
pub fn terminal_states(graph: &StateGraph) -> Vec<String> {
    let adj = build_adjacency(graph);
    graph
        .states
        .iter()
        .filter(|s| adj.get(s.as_str()).is_none_or(Vec::is_empty))
        .cloned()
        .collect()
}

/// Find all initial states (states with no incoming transitions).
/// If the graph has a known initial state (from field default), it's always included.
pub fn initial_states(graph: &StateGraph) -> Vec<String> {
    let mut has_incoming: HashSet<&str> = HashSet::new();
    for edge in &graph.transitions {
        has_incoming.insert(&edge.to);
    }
    let mut result: Vec<String> = graph
        .states
        .iter()
        .filter(|s| !has_incoming.contains(s.as_str()))
        .cloned()
        .collect();

    // Ensure the declared initial state is included
    if let Some(ref init) = graph.initial {
        if !result.contains(init) {
            result.push(init.clone());
        }
    }
    result
}

/// Detect cycles in the state graph. Returns true if any cycle exists.
pub fn has_cycles(graph: &StateGraph) -> bool {
    let adj = build_adjacency(graph);
    let mut visited = HashSet::new();
    let mut in_stack = HashSet::new();

    for state in &graph.states {
        if !visited.contains(state.as_str()) && dfs_cycle(&adj, state, &mut visited, &mut in_stack)
        {
            return true;
        }
    }
    false
}

/// Find a cycle in the state graph. Returns the cycle path if one exists.
pub fn find_cycle(graph: &StateGraph) -> Option<Vec<String>> {
    let adj = build_adjacency(graph);
    let mut visited = HashSet::new();
    let mut in_stack = HashSet::new();
    let mut path = Vec::new();

    for state in &graph.states {
        if !visited.contains(state.as_str()) {
            if let Some(cycle) = dfs_find_cycle(&adj, state, &mut visited, &mut in_stack, &mut path)
            {
                return Some(cycle);
            }
        }
    }
    None
}

/// List transitions from a specific state.
pub fn transitions_from<'a>(graph: &'a StateGraph, state: &str) -> Vec<&'a TransitionEdge> {
    graph
        .transitions
        .iter()
        .filter(|e| e.from.as_deref() == Some(state) || e.from.is_none())
        .collect()
}

/// List transitions to a specific state.
pub fn transitions_to<'a>(graph: &'a StateGraph, state: &str) -> Vec<&'a TransitionEdge> {
    graph.transitions.iter().filter(|e| e.to == state).collect()
}

// ── Internal helpers ─────────────────────────────────────────────────

/// Build adjacency list: `state -> [(next_state, action_name)]`
fn build_adjacency(graph: &StateGraph) -> HashMap<String, Vec<(String, String)>> {
    let mut adj: HashMap<String, Vec<(String, String)>> = HashMap::new();
    // Initialize all states with empty neighbor lists
    for state in &graph.states {
        adj.entry(state.clone()).or_default();
    }
    for edge in &graph.transitions {
        match &edge.from {
            Some(from) => {
                adj.entry(from.clone())
                    .or_default()
                    .push((edge.to.clone(), edge.action.clone()));
            }
            None => {
                // No guard on source state — transition from any state
                for state in &graph.states {
                    adj.entry(state.clone())
                        .or_default()
                        .push((edge.to.clone(), edge.action.clone()));
                }
            }
        }
    }
    adj
}

fn dfs_cycle(
    adj: &HashMap<String, Vec<(String, String)>>,
    node: &str,
    visited: &mut HashSet<String>,
    in_stack: &mut HashSet<String>,
) -> bool {
    visited.insert(node.to_owned());
    in_stack.insert(node.to_owned());

    if let Some(neighbors) = adj.get(node) {
        for (next, _) in neighbors {
            if in_stack.contains(next.as_str()) {
                return true;
            }
            if !visited.contains(next.as_str()) && dfs_cycle(adj, next, visited, in_stack) {
                return true;
            }
        }
    }

    in_stack.remove(node);
    false
}

fn dfs_find_cycle(
    adj: &HashMap<String, Vec<(String, String)>>,
    node: &str,
    visited: &mut HashSet<String>,
    in_stack: &mut HashSet<String>,
    path: &mut Vec<String>,
) -> Option<Vec<String>> {
    visited.insert(node.to_owned());
    in_stack.insert(node.to_owned());
    path.push(node.to_owned());

    if let Some(neighbors) = adj.get(node) {
        for (next, _) in neighbors {
            if in_stack.contains(next.as_str()) {
                // Found cycle — extract it from path
                if let Some(pos) = path.iter().position(|s| s == next) {
                    let mut cycle = path[pos..].to_vec();
                    cycle.push(next.clone());
                    return Some(cycle);
                }
            }
            if !visited.contains(next.as_str()) {
                if let Some(cycle) = dfs_find_cycle(adj, next, visited, in_stack, path) {
                    return Some(cycle);
                }
            }
        }
    }

    path.pop();
    in_stack.remove(node);
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::qa::model::{StateGraph, TransitionEdge};

    fn order_graph() -> StateGraph {
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
        }
    }

    #[test]
    fn reachability_direct() {
        let g = order_graph();
        assert!(is_reachable(&g, "Pending", "Confirmed"));
        assert!(is_reachable(&g, "Confirmed", "Shipped"));
        assert!(is_reachable(&g, "Pending", "Cancelled"));
    }

    #[test]
    fn reachability_transitive() {
        let g = order_graph();
        assert!(is_reachable(&g, "Pending", "Shipped"));
    }

    #[test]
    fn reachability_self() {
        let g = order_graph();
        assert!(is_reachable(&g, "Pending", "Pending"));
    }

    #[test]
    fn unreachable() {
        let g = order_graph();
        assert!(!is_reachable(&g, "Shipped", "Pending"));
        assert!(!is_reachable(&g, "Cancelled", "Confirmed"));
    }

    #[test]
    fn find_path_direct() {
        let g = order_graph();
        let path = find_path(&g, "Pending", "Confirmed").unwrap();
        assert_eq!(path.len(), 1);
        assert_eq!(path[0], ("submit".to_owned(), "Confirmed".to_owned()));
    }

    #[test]
    fn find_path_transitive() {
        let g = order_graph();
        let path = find_path(&g, "Pending", "Shipped").unwrap();
        assert_eq!(path.len(), 2);
        assert_eq!(path[0].0, "submit");
        assert_eq!(path[1].0, "ship");
    }

    #[test]
    fn find_path_none() {
        let g = order_graph();
        assert!(find_path(&g, "Shipped", "Pending").is_none());
    }

    #[test]
    fn terminal() {
        let g = order_graph();
        let terms = terminal_states(&g);
        assert!(terms.contains(&"Shipped".to_owned()));
        assert!(terms.contains(&"Cancelled".to_owned()));
        assert!(!terms.contains(&"Pending".to_owned()));
        assert!(!terms.contains(&"Confirmed".to_owned()));
    }

    #[test]
    fn initial() {
        let g = order_graph();
        let inits = initial_states(&g);
        assert!(inits.contains(&"Pending".to_owned()));
        assert!(!inits.contains(&"Confirmed".to_owned()));
    }

    #[test]
    fn no_cycles_linear() {
        let g = order_graph();
        assert!(!has_cycles(&g));
    }

    #[test]
    fn cycles_detected() {
        let mut g = order_graph();
        // Add a cycle: Shipped -> Pending
        g.transitions.push(TransitionEdge {
            action: "return".to_owned(),
            from: Some("Shipped".to_owned()),
            to: "Pending".to_owned(),
        });
        assert!(has_cycles(&g));
        let cycle = find_cycle(&g).unwrap();
        assert!(cycle.len() >= 2);
    }

    #[test]
    fn transitions_from_state() {
        let g = order_graph();
        let from_pending = transitions_from(&g, "Pending");
        assert_eq!(from_pending.len(), 2); // submit + cancel
        let from_shipped = transitions_from(&g, "Shipped");
        assert_eq!(from_shipped.len(), 0); // terminal
    }

    #[test]
    fn transitions_to_state() {
        let g = order_graph();
        let to_confirmed = transitions_to(&g, "Confirmed");
        assert_eq!(to_confirmed.len(), 1);
        assert_eq!(to_confirmed[0].action, "submit");
    }
}
