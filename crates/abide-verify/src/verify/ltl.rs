use std::collections::{HashMap, VecDeque};

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
    Eventually(Box<Formula>),
    Always(Box<Formula>),
    Until(Box<Formula>, Box<Formula>),
    Release(Box<Formula>, Box<Formula>),
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

    pub(crate) fn eventually(inner: Self) -> Self {
        Self::Eventually(Box::new(inner))
    }

    pub(crate) fn always(inner: Self) -> Self {
        Self::Always(Box::new(inner))
    }

    pub(crate) fn until(left: Self, right: Self) -> Self {
        Self::Until(Box::new(left), Box::new(right))
    }

    pub(crate) fn release(left: Self, right: Self) -> Self {
        Self::Release(Box::new(left), Box::new(right))
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
            Self::Eventually(inner) => Self::eventually(inner.nnf()),
            Self::Always(inner) => Self::always(inner.nnf()),
            Self::Until(left, right) => Self::until(left.nnf(), right.nnf()),
            Self::Release(left, right) => Self::release(left.nnf(), right.nnf()),
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
            Self::Eventually(inner) => Self::always(inner.nnf_negated()),
            Self::Always(inner) => Self::eventually(inner.nnf_negated()),
            Self::Until(left, right) => Self::release(left.nnf_negated(), right.nnf_negated()),
            Self::Release(left, right) => Self::until(left.nnf_negated(), right.nnf_negated()),
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
            Self::Eventually(inner) => Self::until(Self::True, inner.expand_temporal_sugar()),
            Self::Always(inner) => Self::release(Self::False, inner.expand_temporal_sugar()),
            Self::Until(left, right) => {
                Self::until(left.expand_temporal_sugar(), right.expand_temporal_sugar())
            }
            Self::Release(left, right) => {
                Self::release(left.expand_temporal_sugar(), right.expand_temporal_sugar())
            }
        }
    }

    fn collect_closure(&self, formulas: &mut Vec<Self>, ids: &mut HashMap<Self, usize>) {
        match self {
            Self::True | Self::False | Self::Atom(_) => {}
            Self::Not(inner)
            | Self::Next(inner)
            | Self::Eventually(inner)
            | Self::Always(inner) => {
                inner.collect_closure(formulas, ids);
            }
            Self::And(left, right)
            | Self::Or(left, right)
            | Self::Implies(left, right)
            | Self::Until(left, right)
            | Self::Release(left, right) => {
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
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct GeneralizedBuchi {
    closure: FormulaClosure,
    states: Vec<u128>,
    transitions: Vec<Vec<usize>>,
    initial_states: Vec<usize>,
    acceptance_sets: Vec<(usize, usize)>,
    atom_count: usize,
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
            .collect::<Vec<_>>();

        let acceptance_sets = closure
            .iter()
            .enumerate()
            .filter_map(|(id, item)| match item {
                Formula::Until(_, right) => closure.id_of(right).map(|right_id| (id, right_id)),
                _ => None,
            })
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

    fn empty(closure: FormulaClosure, atom_count: usize) -> Self {
        Self {
            closure,
            states: Vec::new(),
            transitions: Vec::new(),
            initial_states: Vec::new(),
            acceptance_sets: Vec::new(),
            atom_count,
        }
    }

    fn node_id(&self, position: usize, state_id: usize) -> usize {
        position * self.states.len() + state_id
    }

    fn state_id_from_node(&self, node: usize) -> usize {
        node % self.states.len()
    }

    fn state_matches_valuation(&self, state: u128, valuation: &[usize]) -> bool {
        (0..self.atom_count).all(|atom| {
            let atom_formula = Formula::atom(atom);
            self.closure.id_of(&atom_formula).is_none_or(|atom_id| {
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
        (0..self.atom_count)
            .filter(|atom| {
                let atom_formula = Formula::atom(*atom);
                self.closure
                    .id_of(&atom_formula)
                    .is_some_and(|atom_id| formula_id_present(state, atom_id))
            })
            .collect()
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
            Formula::True
            | Formula::False
            | Formula::Atom(_)
            | Formula::Next(_)
            | Formula::Eventually(_)
            | Formula::Always(_) => {}
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
            Formula::True
            | Formula::False
            | Formula::Atom(_)
            | Formula::Not(_)
            | Formula::And(_, _)
            | Formula::Or(_, _)
            | Formula::Implies(_, _)
            | Formula::Eventually(_)
            | Formula::Always(_) => {}
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
            Formula::Eventually(inner) => self
                .future_positions(position)
                .any(|future| self.eval(inner, future)),
            Formula::Always(inner) => self
                .future_positions(position)
                .all(|future| self.eval(inner, future)),
            Formula::Until(left, right) => self.eval_until(left, right, position),
            Formula::Release(left, right) => !self.eval_until(
                &Formula::not((**left).clone()),
                &Formula::not((**right).clone()),
                position,
            ),
        }
    }

    fn eval_until(&self, left: &Formula, right: &Formula, position: usize) -> bool {
        let mut left_held_so_far = true;
        for future in self.future_positions(position) {
            if self.eval(right, future) && left_held_so_far {
                return true;
            }
            left_held_so_far &= self.eval(left, future);
        }
        false
    }

    fn future_positions(&self, position: usize) -> impl Iterator<Item = usize> {
        let count = if position < self.prefix.len() {
            self.prefix.len() - position + self.cycle.len()
        } else {
            self.cycle.len()
        };
        position..position + count
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
}
