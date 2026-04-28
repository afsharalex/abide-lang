use std::collections::{HashMap, VecDeque};
use std::fmt::Write;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) enum Formula {
    True,
    False,
    Atom(usize),
    Not(Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Next(Box<Formula>),
    Previously(Box<Formula>),
    Eventually(Box<Formula>),
    Always(Box<Formula>),
    Once(Box<Formula>),
    Historically(Box<Formula>),
    Until(Box<Formula>, Box<Formula>),
    Release(Box<Formula>, Box<Formula>),
    Since(Box<Formula>, Box<Formula>),
    Triggered(Box<Formula>, Box<Formula>),
}

impl Formula {
    pub(crate) fn atom(id: usize) -> Self {
        Self::Atom(id)
    }

    pub(crate) fn not(inner: Self) -> Self {
        Self::Not(Box::new(inner))
    }

    pub(crate) fn and(left: Self, right: Self) -> Self {
        Self::And(Box::new(left), Box::new(right))
    }

    pub(crate) fn or(left: Self, right: Self) -> Self {
        Self::Or(Box::new(left), Box::new(right))
    }

    pub(crate) fn implies(left: Self, right: Self) -> Self {
        Self::Implies(Box::new(left), Box::new(right))
    }

    pub(crate) fn next(inner: Self) -> Self {
        Self::Next(Box::new(inner))
    }

    pub(crate) fn previously(inner: Self) -> Self {
        Self::Previously(Box::new(inner))
    }

    pub(crate) fn eventually(inner: Self) -> Self {
        Self::Eventually(Box::new(inner))
    }

    pub(crate) fn always(inner: Self) -> Self {
        Self::Always(Box::new(inner))
    }

    pub(crate) fn once(inner: Self) -> Self {
        Self::Once(Box::new(inner))
    }

    pub(crate) fn historically(inner: Self) -> Self {
        Self::Historically(Box::new(inner))
    }

    pub(crate) fn until(left: Self, right: Self) -> Self {
        Self::Until(Box::new(left), Box::new(right))
    }

    pub(crate) fn release(left: Self, right: Self) -> Self {
        Self::Release(Box::new(left), Box::new(right))
    }

    pub(crate) fn since(left: Self, right: Self) -> Self {
        Self::Since(Box::new(left), Box::new(right))
    }

    fn triggered(left: Self, right: Self) -> Self {
        Self::Triggered(Box::new(left), Box::new(right))
    }

    pub(crate) fn nnf(&self) -> Self {
        match self {
            Self::True => Self::True,
            Self::False => Self::False,
            Self::Atom(atom) => Self::Atom(*atom),
            Self::Not(inner) => inner.nnf_negated(),
            Self::And(left, right) => Self::and(left.nnf(), right.nnf()),
            Self::Or(left, right) => Self::or(left.nnf(), right.nnf()),
            Self::Implies(left, right) => Self::or(left.nnf_negated(), right.nnf()),
            Self::Next(inner) => Self::next(inner.nnf()),
            Self::Previously(inner) => Self::previously(inner.nnf()),
            Self::Eventually(inner) => Self::eventually(inner.nnf()),
            Self::Always(inner) => Self::always(inner.nnf()),
            Self::Once(inner) => Self::once(inner.nnf()),
            Self::Historically(inner) => Self::historically(inner.nnf()),
            Self::Until(left, right) => Self::until(left.nnf(), right.nnf()),
            Self::Release(left, right) => Self::release(left.nnf(), right.nnf()),
            Self::Since(left, right) => Self::since(left.nnf(), right.nnf()),
            Self::Triggered(left, right) => Self::triggered(left.nnf(), right.nnf()),
        }
    }

    pub(crate) fn closure(&self) -> FormulaClosure {
        let mut formulas = Vec::new();
        let mut ids = HashMap::new();
        self.collect_closure(&mut formulas, &mut ids);
        FormulaClosure { formulas, ids }
    }

    fn automaton_form(&self) -> Self {
        self.nnf().expand_temporal_sugar()
    }

    fn nnf_negated(&self) -> Self {
        match self {
            Self::True => Self::False,
            Self::False => Self::True,
            Self::Atom(atom) => Self::not(Self::Atom(*atom)),
            Self::Not(inner) => inner.nnf(),
            Self::And(left, right) => Self::or(left.nnf_negated(), right.nnf_negated()),
            Self::Or(left, right) => Self::and(left.nnf_negated(), right.nnf_negated()),
            Self::Implies(left, right) => Self::and(left.nnf(), right.nnf_negated()),
            Self::Next(inner) => Self::next(inner.nnf_negated()),
            Self::Previously(inner) => Self::previously(inner.nnf_negated()),
            Self::Eventually(inner) => Self::always(inner.nnf_negated()),
            Self::Always(inner) => Self::eventually(inner.nnf_negated()),
            Self::Once(inner) => Self::historically(inner.nnf_negated()),
            Self::Historically(inner) => Self::once(inner.nnf_negated()),
            Self::Until(left, right) => Self::release(left.nnf_negated(), right.nnf_negated()),
            Self::Release(left, right) => Self::until(left.nnf_negated(), right.nnf_negated()),
            Self::Since(left, right) => Self::triggered(left.nnf_negated(), right.nnf_negated()),
            Self::Triggered(left, right) => Self::since(left.nnf_negated(), right.nnf_negated()),
        }
    }

    fn expand_temporal_sugar(&self) -> Self {
        match self {
            Self::True => Self::True,
            Self::False => Self::False,
            Self::Atom(atom) => Self::Atom(*atom),
            Self::Not(inner) => Self::not(inner.expand_temporal_sugar()),
            Self::And(left, right) => {
                Self::and(left.expand_temporal_sugar(), right.expand_temporal_sugar())
            }
            Self::Or(left, right) => {
                Self::or(left.expand_temporal_sugar(), right.expand_temporal_sugar())
            }
            Self::Implies(left, right) => {
                Self::implies(left.expand_temporal_sugar(), right.expand_temporal_sugar())
            }
            Self::Next(inner) => Self::next(inner.expand_temporal_sugar()),
            Self::Previously(inner) => Self::previously(inner.expand_temporal_sugar()),
            Self::Eventually(inner) => Self::until(Self::True, inner.expand_temporal_sugar()),
            Self::Always(inner) => Self::release(Self::False, inner.expand_temporal_sugar()),
            Self::Once(inner) => Self::since(Self::True, inner.expand_temporal_sugar()),
            Self::Historically(inner) => {
                Self::triggered(Self::False, inner.expand_temporal_sugar())
            }
            Self::Until(left, right) => {
                Self::until(left.expand_temporal_sugar(), right.expand_temporal_sugar())
            }
            Self::Release(left, right) => {
                Self::release(left.expand_temporal_sugar(), right.expand_temporal_sugar())
            }
            Self::Since(left, right) => {
                Self::since(left.expand_temporal_sugar(), right.expand_temporal_sugar())
            }
            Self::Triggered(left, right) => {
                Self::triggered(left.expand_temporal_sugar(), right.expand_temporal_sugar())
            }
        }
    }

    fn collect_closure(&self, formulas: &mut Vec<Self>, ids: &mut HashMap<Self, usize>) {
        match self {
            Self::True | Self::False | Self::Atom(_) => {}
            Self::Not(inner)
            | Self::Next(inner)
            | Self::Previously(inner)
            | Self::Eventually(inner)
            | Self::Always(inner)
            | Self::Once(inner)
            | Self::Historically(inner) => {
                inner.collect_closure(formulas, ids);
            }
            Self::And(left, right)
            | Self::Or(left, right)
            | Self::Implies(left, right)
            | Self::Until(left, right)
            | Self::Release(left, right)
            | Self::Since(left, right)
            | Self::Triggered(left, right) => {
                left.collect_closure(formulas, ids);
                right.collect_closure(formulas, ids);
            }
        }

        if !ids.contains_key(self) {
            let id = formulas.len();
            formulas.push(self.clone());
            ids.insert(self.clone(), id);
        }
    }

    fn past_horizon(&self, period: usize) -> usize {
        match self {
            Self::True | Self::False | Self::Atom(_) => 0,
            Self::Not(inner)
            | Self::Next(inner)
            | Self::Eventually(inner)
            | Self::Always(inner) => inner.past_horizon(period),
            Self::Previously(inner) => 1 + inner.past_horizon(period),
            Self::Once(inner) | Self::Historically(inner) => period + inner.past_horizon(period),
            Self::And(left, right)
            | Self::Or(left, right)
            | Self::Implies(left, right)
            | Self::Until(left, right)
            | Self::Release(left, right) => {
                left.past_horizon(period).max(right.past_horizon(period))
            }
            Self::Since(left, right) | Self::Triggered(left, right) => {
                period + left.past_horizon(period).max(right.past_horizon(period))
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct GeneralizedBuchi {
    closure: FormulaClosure,
    states: Vec<u128>,
    transitions: Vec<Vec<usize>>,
    initial_states: Vec<usize>,
    acceptance_sets: Vec<(usize, usize)>,
    atom_count: usize,
    atom_formula_ids: Vec<Option<usize>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct BuchiWitness {
    prefix: Vec<Vec<usize>>,
    cycle: Vec<Vec<usize>>,
}

impl BuchiWitness {
    pub(crate) fn prefix_len(&self) -> usize {
        self.prefix.len()
    }

    pub(crate) fn loop_len(&self) -> usize {
        self.cycle.len()
    }

    pub(crate) fn to_lasso_word(&self) -> LassoWord {
        LassoWord::new(self.prefix.clone(), self.cycle.clone())
    }
}

impl GeneralizedBuchi {
    pub(crate) fn from_formula(formula: &Formula, atom_count: usize) -> Self {
        let root = formula.automaton_form();
        let closure = root.closure();
        let Some(root_id) = closure.id_of(&root) else {
            return Self::empty(closure, atom_count);
        };

        if closure.len() >= u128::BITS as usize {
            return Self::empty(closure, atom_count);
        }

        let masks = 0..(1u128 << closure.len());
        let states = masks
            .filter(|mask| local_consistency_holds(&closure, *mask))
            .collect::<Vec<_>>();

        let initial_states = states
            .iter()
            .enumerate()
            .filter_map(|(state_id, mask)| formula_id_present(*mask, root_id).then_some(state_id))
            .filter(|state_id| initial_past_consistency_holds(&closure, states[*state_id]))
            .collect::<Vec<_>>();

        let acceptance_sets = closure
            .iter()
            .enumerate()
            .filter_map(|(id, item)| match item {
                Formula::Until(_, right) => closure.id_of(right).map(|right_id| (id, right_id)),
                _ => None,
            })
            .collect::<Vec<_>>();
        let atom_formula_ids = (0..atom_count)
            .map(|atom| closure.id_of(&Formula::atom(atom)))
            .collect::<Vec<_>>();

        let transitions = states
            .iter()
            .map(|source| {
                states
                    .iter()
                    .enumerate()
                    .filter_map(|(target_id, target)| {
                        transition_consistency_holds(&closure, *source, *target)
                            .then_some(target_id)
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        Self {
            closure,
            states,
            transitions,
            initial_states,
            acceptance_sets,
            atom_count,
            atom_formula_ids,
        }
    }

    pub(crate) fn accepts_lasso(&self, word: &LassoWord) -> bool {
        if self.states.is_empty() {
            return false;
        }

        let node_count = word.period() * self.states.len();
        let mut graph = vec![Vec::new(); node_count];
        let mut reverse_graph = vec![Vec::new(); node_count];
        let mut valid_node = vec![false; node_count];

        for position in 0..word.period() {
            for (state_id, state) in self.states.iter().enumerate() {
                let node = self.node_id(position, state_id);
                valid_node[node] = self.state_matches_valuation(*state, word.state_at(position));
            }
        }

        for position in 0..word.period() {
            let next_position = word.successor_position(position);
            for state_id in 0..self.states.len() {
                let node = self.node_id(position, state_id);
                if !valid_node[node] {
                    continue;
                }

                for &next_state_id in &self.transitions[state_id] {
                    let next_node = self.node_id(next_position, next_state_id);
                    if valid_node[next_node] {
                        graph[node].push(next_node);
                        reverse_graph[next_node].push(node);
                    }
                }
            }
        }

        let mut reachable = vec![false; node_count];
        let mut queue = VecDeque::new();
        for &state_id in &self.initial_states {
            let node = self.node_id(0, state_id);
            if valid_node[node] && !reachable[node] {
                reachable[node] = true;
                queue.push_back(node);
            }
        }

        while let Some(node) = queue.pop_front() {
            for &next in &graph[node] {
                if !reachable[next] {
                    reachable[next] = true;
                    queue.push_back(next);
                }
            }
        }

        self.has_accepting_reachable_cycle(&graph, &reverse_graph, &reachable)
    }

    pub(crate) fn witness(&self) -> Option<BuchiWitness> {
        if self.states.is_empty() {
            return None;
        }

        let graph = self.transitions.clone();
        let mut reverse_graph = vec![Vec::new(); self.states.len()];
        for (source, targets) in graph.iter().enumerate() {
            for &target in targets {
                reverse_graph[target].push(source);
            }
        }

        let reachable = self.reachable_states();
        let mut visited = vec![false; graph.len()];
        let mut order = Vec::new();
        for state in 0..graph.len() {
            if reachable[state] && !visited[state] {
                finish_order_dfs(state, &graph, &reachable, &mut visited, &mut order);
            }
        }

        let mut assigned = vec![false; graph.len()];
        while let Some(state) = order.pop() {
            if assigned[state] || !reachable[state] {
                continue;
            }

            let mut component = Vec::new();
            collect_component_dfs(
                state,
                &reverse_graph,
                &reachable,
                &mut assigned,
                &mut component,
            );

            if self.state_component_is_accepting_cycle(&component, &graph) {
                return self.witness_from_component(&component);
            }
        }

        None
    }

    pub(crate) fn state_count(&self) -> usize {
        self.states.len()
    }

    pub(crate) fn transitions(&self) -> &[Vec<usize>] {
        &self.transitions
    }

    pub(crate) fn initial_states(&self) -> &[usize] {
        &self.initial_states
    }

    pub(crate) fn acceptance_set_count(&self) -> usize {
        self.acceptance_sets.len()
    }

    pub(crate) fn state_atoms(&self, state_id: usize) -> Vec<usize> {
        self.states
            .get(state_id)
            .map_or_else(Vec::new, |state| self.state_valuation(*state))
    }

    pub(crate) fn state_satisfies_acceptance(&self, state_id: usize, acceptance_id: usize) -> bool {
        let Some(&(until_id, right_id)) = self.acceptance_sets.get(acceptance_id) else {
            return false;
        };
        self.state_accepts_until(state_id, until_id, right_id)
    }

    pub(crate) fn to_hoa(&self, atom_labels: &[String]) -> String {
        let mut out = String::new();
        let _ = writeln!(out, "HOA: v1");
        let _ = writeln!(out, "States: {}", self.states.len());
        for initial in &self.initial_states {
            let _ = writeln!(out, "Start: {initial}");
        }
        let _ = write!(out, "AP: {}", self.atom_count);
        for atom in 0..self.atom_count {
            let label = atom_labels
                .get(atom)
                .cloned()
                .unwrap_or_else(|| format!("p{atom}"));
            let _ = write!(out, " \"{}\"", escape_hoa_string(&label));
        }
        let _ = writeln!(out);
        if self.acceptance_sets.is_empty() {
            let _ = writeln!(out, "acc-name: all");
            let _ = writeln!(out, "Acceptance: 0 t");
        } else {
            let _ = writeln!(
                out,
                "acc-name: generalized-Buchi {}",
                self.acceptance_sets.len()
            );
            let _ = writeln!(
                out,
                "Acceptance: {} {}",
                self.acceptance_sets.len(),
                render_hoa_acceptance_condition(self.acceptance_sets.len())
            );
        }
        let _ = writeln!(out, "properties: trans-labels explicit-labels state-acc");
        let _ = writeln!(out, "--BODY--");
        for state_id in 0..self.states.len() {
            let marks = self.hoa_acceptance_marks(state_id);
            if marks.is_empty() {
                let _ = writeln!(out, "State: {state_id}");
            } else {
                let _ = writeln!(out, "State: {state_id} {marks}");
            }
            let label = self.hoa_state_label(state_id);
            for target in &self.transitions[state_id] {
                let _ = writeln!(out, "[{label}] {target}");
            }
        }
        let _ = writeln!(out, "--END--");
        out
    }

    fn empty(closure: FormulaClosure, atom_count: usize) -> Self {
        let atom_formula_ids = (0..atom_count)
            .map(|atom| closure.id_of(&Formula::atom(atom)))
            .collect();
        Self {
            closure,
            states: Vec::new(),
            transitions: Vec::new(),
            initial_states: Vec::new(),
            acceptance_sets: Vec::new(),
            atom_count,
            atom_formula_ids,
        }
    }

    fn node_id(&self, position: usize, state_id: usize) -> usize {
        position * self.states.len() + state_id
    }

    fn state_id_from_node(&self, node: usize) -> usize {
        node % self.states.len()
    }

    fn state_matches_valuation(&self, state: u128, valuation: &[usize]) -> bool {
        self.atom_formula_ids
            .iter()
            .enumerate()
            .all(|(atom, atom_id)| {
                atom_id.is_none_or(|atom_id| {
                    formula_id_present(state, atom_id) == valuation.contains(&atom)
                })
            })
    }

    fn reachable_states(&self) -> Vec<bool> {
        let mut reachable = vec![false; self.states.len()];
        let mut queue = VecDeque::new();
        for &state_id in &self.initial_states {
            if !reachable[state_id] {
                reachable[state_id] = true;
                queue.push_back(state_id);
            }
        }

        while let Some(state_id) = queue.pop_front() {
            for &next in &self.transitions[state_id] {
                if !reachable[next] {
                    reachable[next] = true;
                    queue.push_back(next);
                }
            }
        }

        reachable
    }

    fn state_component_is_accepting_cycle(
        &self,
        component: &[usize],
        graph: &[Vec<usize>],
    ) -> bool {
        if component.is_empty() {
            return false;
        }

        let cyclic = component.len() > 1 || graph[component[0]].contains(&component[0]);
        if !cyclic {
            return false;
        }

        self.acceptance_sets.iter().all(|&(until_id, right_id)| {
            component
                .iter()
                .any(|state_id| self.state_accepts_until(*state_id, until_id, right_id))
        })
    }

    fn state_accepts_until(&self, state_id: usize, until_id: usize, right_id: usize) -> bool {
        let state = self.states[state_id];
        !formula_id_present(state, until_id) || formula_id_present(state, right_id)
    }

    fn witness_from_component(&self, component: &[usize]) -> Option<BuchiWitness> {
        let start = component[0];
        let prefix_path = self.path_to_state(start)?;
        let cycle_path = self.cycle_path_through_acceptance(start, component)?;

        Some(BuchiWitness {
            prefix: self.path_to_valuations(&prefix_path[..prefix_path.len().saturating_sub(1)]),
            cycle: self.path_to_valuations(&cycle_path),
        })
    }

    fn path_to_state(&self, target: usize) -> Option<Vec<usize>> {
        let mut predecessor = vec![None; self.states.len()];
        let mut seen = vec![false; self.states.len()];
        let mut queue = VecDeque::new();
        for &initial in &self.initial_states {
            if !seen[initial] {
                seen[initial] = true;
                queue.push_back(initial);
            }
        }

        while let Some(state) = queue.pop_front() {
            if state == target {
                return Some(reconstruct_path(target, &predecessor));
            }

            for &next in &self.transitions[state] {
                if !seen[next] {
                    seen[next] = true;
                    predecessor[next] = Some(state);
                    queue.push_back(next);
                }
            }
        }

        None
    }

    fn cycle_path_through_acceptance(
        &self,
        start: usize,
        component: &[usize],
    ) -> Option<Vec<usize>> {
        let mut cycle = vec![start];
        let mut current = start;

        for &(until_id, right_id) in &self.acceptance_sets {
            let target = component
                .iter()
                .copied()
                .find(|state_id| self.state_accepts_until(*state_id, until_id, right_id))?;
            let path = self.path_within_component(current, target, component)?;
            cycle.extend(path.into_iter().skip(1));
            current = target;
        }

        let return_path = self.path_within_component(current, start, component)?;
        let return_without_duplicate_start = return_path.len().saturating_sub(2);
        cycle.extend(
            return_path
                .into_iter()
                .skip(1)
                .take(return_without_duplicate_start),
        );

        if cycle.len() == 1 && !self.transitions[start].contains(&start) {
            let next = self.transitions[start]
                .iter()
                .copied()
                .find(|candidate| component.contains(candidate))?;
            let path_back = self.path_within_component(next, start, component)?;
            let path_back_without_duplicate_start = path_back.len().saturating_sub(2);
            cycle.push(next);
            cycle.extend(
                path_back
                    .into_iter()
                    .skip(1)
                    .take(path_back_without_duplicate_start),
            );
        }

        Some(cycle)
    }

    fn path_within_component(
        &self,
        start: usize,
        target: usize,
        component: &[usize],
    ) -> Option<Vec<usize>> {
        let mut predecessor = vec![None; self.states.len()];
        let mut seen = vec![false; self.states.len()];
        let mut queue = VecDeque::new();
        seen[start] = true;
        queue.push_back(start);

        while let Some(state) = queue.pop_front() {
            if state == target {
                return Some(reconstruct_path(target, &predecessor));
            }

            for &next in &self.transitions[state] {
                if component.contains(&next) && !seen[next] {
                    seen[next] = true;
                    predecessor[next] = Some(state);
                    queue.push_back(next);
                }
            }
        }

        None
    }

    fn path_to_valuations(&self, path: &[usize]) -> Vec<Vec<usize>> {
        path.iter()
            .map(|state_id| self.state_valuation(self.states[*state_id]))
            .collect()
    }

    fn state_valuation(&self, state: u128) -> Vec<usize> {
        self.atom_formula_ids
            .iter()
            .enumerate()
            .filter_map(|(atom, atom_id)| {
                atom_id
                    .is_some_and(|atom_id| formula_id_present(state, atom_id))
                    .then_some(atom)
            })
            .collect()
    }

    fn hoa_state_label(&self, state_id: usize) -> String {
        if self.atom_count == 0 {
            return "t".to_owned();
        }

        let valuation = self.state_atoms(state_id);
        (0..self.atom_count)
            .map(|atom| {
                if valuation.contains(&atom) {
                    atom.to_string()
                } else {
                    format!("!{atom}")
                }
            })
            .collect::<Vec<_>>()
            .join("&")
    }

    fn hoa_acceptance_marks(&self, state_id: usize) -> String {
        let marks = (0..self.acceptance_sets.len())
            .filter(|acceptance_id| self.state_satisfies_acceptance(state_id, *acceptance_id))
            .map(|acceptance_id| acceptance_id.to_string())
            .collect::<Vec<_>>();
        if marks.is_empty() {
            String::new()
        } else {
            format!("{{{}}}", marks.join(" "))
        }
    }

    fn has_accepting_reachable_cycle(
        &self,
        graph: &[Vec<usize>],
        reverse_graph: &[Vec<usize>],
        reachable: &[bool],
    ) -> bool {
        let mut visited = vec![false; graph.len()];
        let mut order = Vec::new();
        for node in 0..graph.len() {
            if reachable[node] && !visited[node] {
                finish_order_dfs(node, graph, reachable, &mut visited, &mut order);
            }
        }

        let mut assigned = vec![false; graph.len()];
        while let Some(node) = order.pop() {
            if assigned[node] || !reachable[node] {
                continue;
            }

            let mut component = Vec::new();
            collect_component_dfs(
                node,
                reverse_graph,
                reachable,
                &mut assigned,
                &mut component,
            );

            if self.component_is_accepting_cycle(&component, graph) {
                return true;
            }
        }

        false
    }

    fn component_is_accepting_cycle(&self, component: &[usize], graph: &[Vec<usize>]) -> bool {
        if component.is_empty() {
            return false;
        }

        let cyclic = component.len() > 1 || graph[component[0]].contains(&component[0]);
        if !cyclic {
            return false;
        }

        self.acceptance_sets.iter().all(|&(until_id, right_id)| {
            component.iter().any(|node| {
                let state = self.states[self.state_id_from_node(*node)];
                !formula_id_present(state, until_id) || formula_id_present(state, right_id)
            })
        })
    }
}

fn escape_hoa_string(value: &str) -> String {
    value.replace('\\', "\\\\").replace('"', "\\\"")
}

fn render_hoa_acceptance_condition(count: usize) -> String {
    (0..count)
        .map(|id| format!("Inf({id})"))
        .collect::<Vec<_>>()
        .join("&")
}

fn reconstruct_path(target: usize, predecessor: &[Option<usize>]) -> Vec<usize> {
    let mut path = vec![target];
    let mut current = target;
    while let Some(previous) = predecessor[current] {
        path.push(previous);
        current = previous;
    }
    path.reverse();
    path
}

fn local_consistency_holds(closure: &FormulaClosure, mask: u128) -> bool {
    for (id, formula) in closure.iter().enumerate() {
        let present = formula_id_present(mask, id);
        match formula {
            Formula::True if !present => return false,
            Formula::False if present => return false,
            Formula::Not(inner) => {
                let Some(inner_present) = formula_present(closure, mask, inner) else {
                    return false;
                };
                if present == inner_present {
                    return false;
                }
            }
            Formula::And(left, right) => {
                let (Some(left), Some(right)) = (
                    formula_present(closure, mask, left),
                    formula_present(closure, mask, right),
                ) else {
                    return false;
                };
                if present != (left && right) {
                    return false;
                }
            }
            Formula::Or(left, right) => {
                let (Some(left), Some(right)) = (
                    formula_present(closure, mask, left),
                    formula_present(closure, mask, right),
                ) else {
                    return false;
                };
                if present != (left || right) {
                    return false;
                }
            }
            Formula::Implies(left, right) => {
                let (Some(left), Some(right)) = (
                    formula_present(closure, mask, left),
                    formula_present(closure, mask, right),
                ) else {
                    return false;
                };
                if present != (!left || right) {
                    return false;
                }
            }
            Formula::Until(left, right) => {
                let (Some(left), Some(right)) = (
                    formula_present(closure, mask, left),
                    formula_present(closure, mask, right),
                ) else {
                    return false;
                };
                if present && !right && !left {
                    return false;
                }
            }
            Formula::Release(_, right) => {
                let Some(right) = formula_present(closure, mask, right) else {
                    return false;
                };
                if present && !right {
                    return false;
                }
            }
            Formula::Since(left, right) => {
                let (Some(left), Some(right)) = (
                    formula_present(closure, mask, left),
                    formula_present(closure, mask, right),
                ) else {
                    return false;
                };
                if present && !right && !left {
                    return false;
                }
            }
            Formula::Triggered(_, right) => {
                let Some(right) = formula_present(closure, mask, right) else {
                    return false;
                };
                if present && !right {
                    return false;
                }
            }
            Formula::True
            | Formula::False
            | Formula::Atom(_)
            | Formula::Next(_)
            | Formula::Previously(_)
            | Formula::Eventually(_)
            | Formula::Always(_)
            | Formula::Once(_)
            | Formula::Historically(_) => {}
        }
    }

    true
}

fn transition_consistency_holds(closure: &FormulaClosure, source: u128, target: u128) -> bool {
    for (id, formula) in closure.iter().enumerate() {
        let present = formula_id_present(source, id);
        match formula {
            Formula::Next(inner) => {
                let Some(inner_next) = formula_present(closure, target, inner) else {
                    return false;
                };
                if present != inner_next {
                    return false;
                }
            }
            Formula::Previously(inner) => {
                let Some(inner_previous) = formula_present(closure, source, inner) else {
                    return false;
                };
                if formula_id_present(target, id) != inner_previous {
                    return false;
                }
            }
            Formula::Until(left, right) => {
                let (Some(left), Some(right), Some(until_next)) = (
                    formula_present(closure, source, left),
                    formula_present(closure, source, right),
                    closure
                        .id_of(formula)
                        .map(|until_id| formula_id_present(target, until_id)),
                ) else {
                    return false;
                };
                if present != (right || (left && until_next)) {
                    return false;
                }
            }
            Formula::Release(left, right) => {
                let (Some(left), Some(right), Some(release_next)) = (
                    formula_present(closure, source, left),
                    formula_present(closure, source, right),
                    closure
                        .id_of(formula)
                        .map(|release_id| formula_id_present(target, release_id)),
                ) else {
                    return false;
                };
                if present != (right && (left || release_next)) {
                    return false;
                }
            }
            Formula::Since(left, right) => {
                let (Some(left_next), Some(right_next)) = (
                    formula_present(closure, target, left),
                    formula_present(closure, target, right),
                ) else {
                    return false;
                };
                let since_next = formula_id_present(target, id);
                if since_next != (right_next || (left_next && present)) {
                    return false;
                }
            }
            Formula::Triggered(left, right) => {
                let (Some(left_next), Some(right_next)) = (
                    formula_present(closure, target, left),
                    formula_present(closure, target, right),
                ) else {
                    return false;
                };
                let triggered_next = formula_id_present(target, id);
                if triggered_next != (right_next && (left_next || present)) {
                    return false;
                }
            }
            Formula::True
            | Formula::False
            | Formula::Atom(_)
            | Formula::Not(_)
            | Formula::And(_, _)
            | Formula::Or(_, _)
            | Formula::Implies(_, _)
            | Formula::Eventually(_)
            | Formula::Always(_)
            | Formula::Once(_)
            | Formula::Historically(_) => {}
        }
    }

    true
}

fn initial_past_consistency_holds(closure: &FormulaClosure, mask: u128) -> bool {
    for (id, formula) in closure.iter().enumerate() {
        match formula {
            Formula::Previously(_) if formula_id_present(mask, id) => return false,
            Formula::Since(_, right) => {
                let Some(right_present) = formula_present(closure, mask, right) else {
                    return false;
                };
                if formula_id_present(mask, id) != right_present {
                    return false;
                }
            }
            Formula::Triggered(_, right) => {
                let Some(right_present) = formula_present(closure, mask, right) else {
                    return false;
                };
                if formula_id_present(mask, id) != right_present {
                    return false;
                }
            }
            _ => {}
        }
    }

    true
}

fn formula_present(closure: &FormulaClosure, mask: u128, formula: &Formula) -> Option<bool> {
    closure
        .id_of(formula)
        .map(|id| formula_id_present(mask, id))
}

fn formula_id_present(mask: u128, id: usize) -> bool {
    (mask & (1u128 << id)) != 0
}

fn finish_order_dfs(
    node: usize,
    graph: &[Vec<usize>],
    reachable: &[bool],
    visited: &mut [bool],
    order: &mut Vec<usize>,
) {
    visited[node] = true;
    for &next in &graph[node] {
        if reachable[next] && !visited[next] {
            finish_order_dfs(next, graph, reachable, visited, order);
        }
    }
    order.push(node);
}

fn collect_component_dfs(
    node: usize,
    reverse_graph: &[Vec<usize>],
    reachable: &[bool],
    assigned: &mut [bool],
    component: &mut Vec<usize>,
) {
    assigned[node] = true;
    component.push(node);
    for &next in &reverse_graph[node] {
        if reachable[next] && !assigned[next] {
            collect_component_dfs(next, reverse_graph, reachable, assigned, component);
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct FormulaClosure {
    formulas: Vec<Formula>,
    ids: HashMap<Formula, usize>,
}

impl FormulaClosure {
    pub(crate) fn len(&self) -> usize {
        self.formulas.len()
    }

    pub(crate) fn id_of(&self, formula: &Formula) -> Option<usize> {
        self.ids.get(formula).copied()
    }

    pub(crate) fn formula(&self, id: usize) -> Option<&Formula> {
        self.formulas.get(id)
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = &Formula> {
        self.formulas.iter()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct LassoWord {
    prefix: Vec<Vec<usize>>,
    cycle: Vec<Vec<usize>>,
}

impl LassoWord {
    pub(crate) fn new(prefix: Vec<Vec<usize>>, cycle: Vec<Vec<usize>>) -> Self {
        assert!(!cycle.is_empty(), "lasso word cycle must be non-empty");
        Self { prefix, cycle }
    }

    pub(crate) fn holds(&self, formula: &Formula, position: usize) -> bool {
        self.eval(formula, position)
    }

    pub(crate) fn period(&self) -> usize {
        self.prefix.len() + self.cycle.len()
    }

    fn eval(&self, formula: &Formula, position: usize) -> bool {
        match formula {
            Formula::True => true,
            Formula::False => false,
            Formula::Atom(atom) => self.state_at(position).contains(atom),
            Formula::Not(inner) => !self.eval(inner, position),
            Formula::And(left, right) => self.eval(left, position) && self.eval(right, position),
            Formula::Or(left, right) => self.eval(left, position) || self.eval(right, position),
            Formula::Implies(left, right) => {
                !self.eval(left, position) || self.eval(right, position)
            }
            Formula::Next(inner) => self.eval(inner, position + 1),
            Formula::Previously(inner) => position > 0 && self.eval(inner, position - 1),
            Formula::Eventually(inner) => self
                .future_positions_for(inner, position)
                .any(|future| self.eval(inner, future)),
            Formula::Always(inner) => self
                .future_positions_for(inner, position)
                .all(|future| self.eval(inner, future)),
            Formula::Once(inner) => self
                .past_positions(position)
                .any(|past| self.eval(inner, past)),
            Formula::Historically(inner) => self
                .past_positions(position)
                .all(|past| self.eval(inner, past)),
            Formula::Until(left, right) => self.eval_until(left, right, position),
            Formula::Release(left, right) => !self.eval_until(
                &Formula::not((**left).clone()),
                &Formula::not((**right).clone()),
                position,
            ),
            Formula::Since(left, right) => self.eval_since(left, right, position),
            Formula::Triggered(left, right) => !self.eval_since(
                &Formula::not((**left).clone()),
                &Formula::not((**right).clone()),
                position,
            ),
        }
    }

    fn eval_until(&self, left: &Formula, right: &Formula, position: usize) -> bool {
        let mut left_held_so_far = true;
        let horizon = left
            .past_horizon(self.period())
            .max(right.past_horizon(self.period()));
        for future in self.future_positions_with_horizon(position, horizon) {
            if self.eval(right, future) && left_held_so_far {
                return true;
            }
            left_held_so_far &= self.eval(left, future);
        }
        false
    }

    fn eval_since(&self, left: &Formula, right: &Formula, position: usize) -> bool {
        let mut left_held_since = true;
        for past in self.past_positions(position).rev() {
            if self.eval(right, past) && left_held_since {
                return true;
            }
            left_held_since &= self.eval(left, past);
        }
        false
    }

    fn future_positions_for(
        &self,
        formula: &Formula,
        position: usize,
    ) -> impl Iterator<Item = usize> {
        self.future_positions_with_horizon(position, formula.past_horizon(self.period()))
    }

    fn future_positions_with_horizon(
        &self,
        position: usize,
        horizon: usize,
    ) -> std::ops::Range<usize> {
        let count = if position < self.prefix.len() {
            self.prefix.len() - position + self.cycle.len()
        } else {
            self.cycle.len()
        };
        position..position + count + horizon
    }

    fn past_positions(&self, position: usize) -> std::ops::RangeInclusive<usize> {
        0..=position
    }

    fn state_at(&self, position: usize) -> &[usize] {
        if position < self.prefix.len() {
            &self.prefix[position]
        } else {
            let cycle_index = (position - self.prefix.len()) % self.cycle.len();
            &self.cycle[cycle_index]
        }
    }

    fn successor_position(&self, position: usize) -> usize {
        let next = position + 1;
        if next < self.period() {
            next
        } else {
            self.prefix.len()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{BuchiWitness, Formula, GeneralizedBuchi, LassoWord};

    const P: usize = 0;
    const Q: usize = 1;

    fn word(prefix: &[&[usize]], cycle: &[&[usize]]) -> LassoWord {
        LassoWord::new(
            prefix.iter().map(|state| state.to_vec()).collect(),
            cycle.iter().map(|state| state.to_vec()).collect(),
        )
    }

    fn p() -> Formula {
        Formula::atom(P)
    }

    fn q() -> Formula {
        Formula::atom(Q)
    }

    #[test]
    fn lasso_semantics_handles_boolean_atoms_and_next() {
        let word = word(&[&[P]], &[&[Q], &[P, Q]]);

        assert!(word.holds(&p(), 0));
        assert!(!word.holds(&q(), 0));
        assert!(word.holds(&Formula::not(q()), 0));
        assert!(word.holds(&Formula::and(p(), Formula::not(q())), 0));
        assert!(word.holds(&Formula::or(Formula::not(p()), q()), 1));
        assert!(word.holds(&Formula::True, 0));
        assert!(!word.holds(&Formula::False, 0));
        assert!(!word.holds(&Formula::implies(q(), p()), 1));
        assert!(word.holds(&Formula::implies(p(), q()), 1));
        assert!(word.holds(&Formula::next(q()), 0));
        assert!(word.holds(&Formula::next(p()), 1));
    }

    #[test]
    fn lasso_semantics_handles_eventuality_and_recurrence_patterns() {
        let recurrent = word(&[], &[&[P], &[]]);
        let persistent = word(&[&[]], &[&[P]]);
        let never = word(&[], &[&[]]);

        assert!(recurrent.holds(&Formula::eventually(p()), 0));
        assert!(recurrent.holds(&Formula::always(Formula::eventually(p())), 0));
        assert!(!recurrent.holds(&Formula::eventually(Formula::always(p())), 0));
        assert!(persistent.holds(&Formula::eventually(Formula::always(p())), 0));
        assert!(!never.holds(&Formula::eventually(p()), 0));
    }

    #[test]
    fn lasso_semantics_handles_response_until_and_release_patterns() {
        let response_ok = word(&[], &[&[P], &[Q], &[]]);
        let response_bad = word(&[], &[&[P], &[]]);

        let response = Formula::always(Formula::implies(p(), Formula::eventually(q())));
        assert!(response_ok.holds(&response, 0));
        assert!(!response_bad.holds(&response, 0));

        assert!(response_ok.holds(&Formula::until(p(), q()), 0));
        assert!(!response_bad.holds(&Formula::until(p(), q()), 0));

        let release = Formula::release(p(), q());
        assert!(word(&[], &[&[P, Q], &[Q]]).holds(&release, 0));
        assert!(!word(&[], &[&[Q], &[]]).holds(&release, 0));
    }

    #[test]
    fn lasso_semantics_handles_past_time_patterns() {
        let sample = word(&[&[P], &[], &[Q]], &[&[]]);

        assert!(!sample.holds(&Formula::previously(p()), 0));
        assert!(sample.holds(&Formula::previously(p()), 1));
        assert!(sample.holds(&Formula::once(p()), 2));
        assert!(!sample.holds(&Formula::once(q()), 1));
        assert!(sample.holds(&Formula::historically(p()), 0));
        assert!(!sample.holds(&Formula::historically(p()), 1));
        assert!(sample.holds(&Formula::since(p(), p()), 0));
        assert!(sample.holds(&Formula::since(Formula::True, q()), 2));
        assert!(!sample.holds(&Formula::since(p(), q()), 3));
    }

    #[test]
    fn lasso_semantics_pins_standard_dualities() {
        let samples = [
            word(&[], &[&[P], &[]]),
            word(&[&[]], &[&[P]]),
            word(&[], &[&[Q], &[P, Q]]),
        ];

        for sample in samples {
            for position in 0..sample.period() {
                assert_eq!(
                    sample.holds(&Formula::not(Formula::eventually(p())), position),
                    sample.holds(&Formula::always(Formula::not(p())), position)
                );
                assert_eq!(
                    sample.holds(&Formula::not(Formula::always(p())), position),
                    sample.holds(&Formula::eventually(Formula::not(p())), position)
                );
                assert_eq!(
                    sample.holds(&Formula::not(Formula::until(p(), q())), position),
                    sample.holds(
                        &Formula::release(Formula::not(p()), Formula::not(q())),
                        position
                    )
                );
                assert_eq!(
                    sample.holds(&Formula::not(Formula::since(p(), q())), position),
                    sample.holds(
                        &Formula::triggered(Formula::not(p()), Formula::not(q())),
                        position
                    )
                );
            }
        }
    }

    #[test]
    fn normalization_eliminates_implication_and_pushes_negation() {
        assert_eq!(
            Formula::implies(p(), Formula::eventually(q())).nnf(),
            Formula::or(Formula::not(p()), Formula::eventually(q()))
        );
        assert_eq!(
            Formula::not(Formula::eventually(p())).nnf(),
            Formula::always(Formula::not(p()))
        );
        assert_eq!(
            Formula::not(Formula::always(p())).nnf(),
            Formula::eventually(Formula::not(p()))
        );
        assert_eq!(
            Formula::not(Formula::until(p(), q())).nnf(),
            Formula::release(Formula::not(p()), Formula::not(q()))
        );
        assert_eq!(
            Formula::not(Formula::release(p(), q())).nnf(),
            Formula::until(Formula::not(p()), Formula::not(q()))
        );
        assert_eq!(
            Formula::not(Formula::since(p(), q())).nnf(),
            Formula::triggered(Formula::not(p()), Formula::not(q()))
        );
        assert_eq!(Formula::not(Formula::not(p())).nnf(), p());
    }

    #[test]
    fn closure_indexes_subformulas_once_in_stable_postorder() {
        let eventually_p = Formula::eventually(p());
        let formula = Formula::and(Formula::always(eventually_p.clone()), eventually_p.clone());
        let closure = formula.closure();

        let p_id = closure.id_of(&p()).expect("atom is present");
        let eventually_id = closure
            .id_of(&eventually_p)
            .expect("eventually subformula is present");
        let root_id = closure.id_of(&formula).expect("root formula is present");

        assert_eq!(closure.formula(p_id), Some(&p()));
        assert_eq!(closure.formula(eventually_id), Some(&eventually_p));
        assert_eq!(root_id, closure.len() - 1);
        assert_eq!(
            closure.iter().filter(|item| *item == &eventually_p).count(),
            1
        );
    }

    fn assert_buchi_matches_lasso_semantics(formula: Formula, samples: &[LassoWord]) {
        let automaton = GeneralizedBuchi::from_formula(&formula, 2);

        for sample in samples {
            assert_eq!(
                automaton.accepts_lasso(sample),
                sample.holds(&formula, 0),
                "formula {formula:?} disagreed on lasso {sample:?}"
            );
        }
    }

    fn generated_formula_family() -> Vec<Formula> {
        let atoms = [p(), q(), Formula::not(p()), Formula::not(q())];
        let mut formulas = vec![Formula::True, Formula::False, p(), q()];
        for atom in atoms {
            formulas.push(Formula::next(atom.clone()));
            formulas.push(Formula::eventually(atom.clone()));
            formulas.push(Formula::always(atom));
        }
        for left in [p(), Formula::eventually(p()), Formula::always(p())] {
            for right in [q(), Formula::eventually(q()), Formula::always(q())] {
                formulas.push(Formula::and(left.clone(), right.clone()));
                formulas.push(Formula::or(left.clone(), right.clone()));
                formulas.push(Formula::implies(left.clone(), right.clone()));
                formulas.push(Formula::until(left.clone(), right.clone()));
                formulas.push(Formula::release(left.clone(), right.clone()));
            }
        }
        formulas.push(Formula::always(Formula::implies(
            p(),
            Formula::next(Formula::eventually(q())),
        )));
        formulas.push(Formula::eventually(Formula::always(Formula::or(
            p(),
            Formula::not(q()),
        ))));
        formulas
    }

    fn next_seed(seed: &mut u64) -> u64 {
        *seed ^= *seed << 13;
        *seed ^= *seed >> 7;
        *seed ^= *seed << 17;
        *seed
    }

    fn generated_formula(seed: &mut u64, depth: usize) -> Formula {
        if depth == 0 {
            return match next_seed(seed) % 4 {
                0 => Formula::True,
                1 => Formula::False,
                2 => p(),
                _ => q(),
            };
        }

        match next_seed(seed) % 14 {
            0 => Formula::not(generated_formula(seed, depth - 1)),
            1 => Formula::next(generated_formula(seed, depth - 1)),
            2 => Formula::previously(generated_formula(seed, depth - 1)),
            3 => Formula::eventually(generated_formula(seed, depth - 1)),
            4 => Formula::always(generated_formula(seed, depth - 1)),
            5 => Formula::once(generated_formula(seed, depth - 1)),
            6 => Formula::historically(generated_formula(seed, depth - 1)),
            7 => Formula::and(
                generated_formula(seed, depth - 1),
                generated_formula(seed, depth - 1),
            ),
            8 => Formula::or(
                generated_formula(seed, depth - 1),
                generated_formula(seed, depth - 1),
            ),
            9 => Formula::implies(
                generated_formula(seed, depth - 1),
                generated_formula(seed, depth - 1),
            ),
            10 => Formula::until(
                generated_formula(seed, depth - 1),
                generated_formula(seed, depth - 1),
            ),
            11 => Formula::release(
                generated_formula(seed, depth - 1),
                generated_formula(seed, depth - 1),
            ),
            _ => Formula::since(
                generated_formula(seed, depth - 1),
                generated_formula(seed, depth - 1),
            ),
        }
    }

    fn generated_word(seed: &mut u64) -> LassoWord {
        let prefix_len = (next_seed(seed) % 3) as usize;
        let cycle_len = 1 + (next_seed(seed) % 3) as usize;
        let mut states = Vec::new();
        for _ in 0..prefix_len + cycle_len {
            let mask = next_seed(seed) % 4;
            let mut valuation = Vec::new();
            if (mask & 1) != 0 {
                valuation.push(P);
            }
            if (mask & 2) != 0 {
                valuation.push(Q);
            }
            states.push(valuation);
        }
        let cycle = states.split_off(prefix_len);
        LassoWord::new(states, cycle)
    }

    #[test]
    fn buchi_construction_matches_lasso_semantics_for_safety_liveness_and_response() {
        let samples = [
            word(&[], &[&[P], &[P, Q]]),
            word(&[&[P]], &[&[], &[Q]]),
            word(&[], &[&[P], &[]]),
            word(&[&[]], &[&[Q]]),
        ];

        assert_buchi_matches_lasso_semantics(Formula::always(Formula::implies(p(), q())), &samples);
        assert_buchi_matches_lasso_semantics(Formula::eventually(q()), &samples);
        assert_buchi_matches_lasso_semantics(
            Formula::always(Formula::implies(p(), Formula::eventually(q()))),
            &samples,
        );
    }

    #[test]
    fn buchi_construction_matches_lasso_semantics_for_recurrence_persistence_and_nested_next() {
        let samples = [
            word(&[], &[&[P], &[]]),
            word(&[&[]], &[&[P]]),
            word(&[], &[&[P, Q], &[P], &[]]),
            word(&[], &[&[P], &[Q], &[]]),
        ];

        assert_buchi_matches_lasso_semantics(Formula::always(Formula::eventually(p())), &samples);
        assert_buchi_matches_lasso_semantics(Formula::eventually(Formula::always(p())), &samples);
        assert_buchi_matches_lasso_semantics(
            Formula::always(Formula::implies(
                p(),
                Formula::next(Formula::eventually(q())),
            )),
            &samples,
        );
    }

    #[test]
    fn buchi_construction_matches_lasso_semantics_for_until_release_and_unsat_formulas() {
        let samples = [
            word(&[], &[&[P], &[Q], &[]]),
            word(&[], &[&[P], &[]]),
            word(&[&[P]], &[&[P, Q]]),
            word(&[], &[&[]]),
        ];

        assert_buchi_matches_lasso_semantics(Formula::until(p(), q()), &samples);
        assert_buchi_matches_lasso_semantics(Formula::release(p(), q()), &samples);
        assert_buchi_matches_lasso_semantics(Formula::and(p(), Formula::not(p())), &samples);
        assert_buchi_matches_lasso_semantics(Formula::eventually(Formula::False), &samples);
    }

    #[test]
    fn buchi_construction_matches_lasso_semantics_for_past_time_formulas() {
        let samples = [
            word(&[], &[&[]]),
            word(&[], &[&[P]]),
            word(&[], &[&[P], &[]]),
            word(&[&[]], &[&[P, Q]]),
            word(&[&[P]], &[&[], &[Q]]),
            word(&[&[Q]], &[&[P], &[P, Q]]),
        ];

        assert_buchi_matches_lasso_semantics(Formula::previously(p()), &samples);
        assert_buchi_matches_lasso_semantics(Formula::once(p()), &samples);
        assert_buchi_matches_lasso_semantics(Formula::historically(p()), &samples);
        assert_buchi_matches_lasso_semantics(Formula::since(p(), q()), &samples);
        assert_buchi_matches_lasso_semantics(
            Formula::always(Formula::implies(q(), Formula::once(p()))),
            &samples,
        );
    }

    #[test]
    fn buchi_construction_matches_lasso_semantics_for_generated_formula_family() {
        let samples = [
            word(&[], &[&[]]),
            word(&[], &[&[P]]),
            word(&[], &[&[Q]]),
            word(&[], &[&[P], &[]]),
            word(&[], &[&[P], &[Q], &[]]),
            word(&[&[]], &[&[P, Q]]),
            word(&[&[P]], &[&[], &[Q]]),
            word(&[&[Q]], &[&[P], &[P, Q]]),
        ];

        for formula in generated_formula_family() {
            assert_buchi_matches_lasso_semantics(formula, &samples);
        }
    }

    #[test]
    fn buchi_construction_matches_lasso_semantics_for_seeded_formula_and_word_matrix() {
        let mut seed = 0x5EED_5EED_CAFE_BABEu64;

        for _ in 0..64 {
            let formula = generated_formula(&mut seed, 2);
            let samples = (0..16)
                .map(|_| generated_word(&mut seed))
                .collect::<Vec<_>>();
            assert_buchi_matches_lasso_semantics(formula, &samples);
        }
    }

    fn witness_for(formula: &Formula) -> Option<BuchiWitness> {
        GeneralizedBuchi::from_formula(formula, 2).witness()
    }

    #[test]
    fn buchi_witness_satisfies_direct_lasso_semantics() {
        let formula = Formula::always(Formula::eventually(p()));
        let witness = witness_for(&formula).expect("recurrence is satisfiable");
        let lasso = witness.to_lasso_word();

        assert_eq!(witness.loop_len(), lasso.cycle.len());
        assert!(witness.loop_len() > 0);
        assert!(lasso.holds(&formula, 0));
    }

    #[test]
    fn buchi_witness_rejects_unsat_and_non_accepting_cycles() {
        assert!(witness_for(&Formula::and(p(), Formula::not(p()))).is_none());
        assert!(witness_for(&Formula::eventually(Formula::False)).is_none());
    }

    #[test]
    fn buchi_witness_preserves_prefix_and_loop_shape() {
        let formula = Formula::and(Formula::not(p()), Formula::next(Formula::eventually(p())));
        let witness = witness_for(&formula).expect("next eventuality is satisfiable");
        let lasso = witness.to_lasso_word();

        assert!(witness.prefix_len() > 0);
        assert!(witness.loop_len() > 0);
        assert!(lasso.holds(&formula, 0));
    }

    #[test]
    fn buchi_hoa_export_includes_generalized_acceptance_and_atom_labels() {
        let automaton =
            GeneralizedBuchi::from_formula(&Formula::always(Formula::eventually(p())), 2);
        let hoa = automaton.to_hoa(&["p".to_owned(), "q".to_owned()]);

        assert!(hoa.starts_with("HOA: v1\n"));
        assert!(hoa.contains("AP: 2 \"p\" \"q\"\n"));
        assert!(hoa.contains("Acceptance: 1 Inf(0)\n"));
        assert!(hoa.contains("--BODY--\n"));
        assert!(hoa.contains("--END--\n"));
        assert!(hoa.contains("[0&!1]"));
        assert!(hoa.contains("{0}"));
    }

    #[test]
    fn buchi_hoa_export_handles_zero_acceptance_sets() {
        let automaton = GeneralizedBuchi::from_formula(&Formula::always(p()), 1);
        let hoa = automaton.to_hoa(&["p".to_owned()]);

        assert!(hoa.contains("Acceptance: 0 t\n"));
        assert!(!hoa.contains("{0}"));
    }
}
