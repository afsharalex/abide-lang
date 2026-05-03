//! Bounded temporal relational core and lasso SAT encoder.
//!
//! This module defines the relational trace shape used by the
//! Alloy/Pardinus-style backend and the first bounded lasso SAT encoding over
//! that shape.

use std::collections::{HashMap, HashSet};

use rustsat::instances::SatInstance;
use rustsat::solvers::{Solve, SolverResult};
use rustsat::types::{Lit, TernaryVal};
use rustsat_batsat::BasicSolver;
use serde::Serialize;

use crate::ir::types::{
    IRAction, IRCreateField, IREntity, IRExpr, IRField, IRProgram, IRStoreDecl, IRType, IRVerify,
    LitVal,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct TemporalRelationalModel {
    pub(super) trace: RelTrace,
    pub(super) universes: Vec<RelUniverse>,
    pub(super) relations: Vec<RelTemporalRelation>,
}

impl TemporalRelationalModel {
    pub(super) fn from_verify(ir: &IRProgram, verify: &IRVerify) -> Result<Self, RelCoreError> {
        Self::from_verify_with_loop_start(ir, verify, 0)
    }

    pub(super) fn from_verify_with_loop_start(
        ir: &IRProgram,
        verify: &IRVerify,
        loop_start: usize,
    ) -> Result<Self, RelCoreError> {
        let depth = verify.depth.unwrap_or(0).max(0) as usize;
        let trace = RelTrace::new(depth, loop_start)?;
        let entity_by_name = ir
            .entities
            .iter()
            .map(|entity| (entity.name.as_str(), entity))
            .collect::<HashMap<_, _>>();

        let mut builder = RelCoreBuilder::new(trace);
        for store in &verify.stores {
            let entity = entity_by_name
                .get(store.entity_type.as_str())
                .ok_or_else(|| RelCoreError::Unsupported {
                    reason: format!(
                        "store {} references unknown entity type {}",
                        store.name, store.entity_type
                    ),
                })?;
            builder.add_store(store, entity)?;
        }

        Ok(builder.finish())
    }

    pub(super) fn relation(&self, name: &str) -> Option<&RelTemporalRelation> {
        self.relations
            .iter()
            .find(|relation| relation.symbol.name == name)
    }

    pub(super) fn universe(&self, name: &str) -> Option<&RelUniverse> {
        self.universes.iter().find(|universe| universe.name == name)
    }
}

fn transition_system_from_verify(
    ir: &IRProgram,
    verify: &IRVerify,
    model: &TemporalRelationalModel,
) -> Result<Option<RelTemporalTransitionSystem>, RelCoreError> {
    if verify.systems.len() != 1 {
        return Ok(None);
    }
    let system_name = &verify.systems[0].name;
    let Some(system) = ir
        .systems
        .iter()
        .find(|candidate| candidate.name == *system_name)
    else {
        return Err(RelCoreError::Unsupported {
            reason: format!("unknown temporal relational verify system `{system_name}`"),
        });
    };
    if !system.fields.is_empty() || !system.let_bindings.is_empty() {
        return Ok(None);
    }

    let entities = ir
        .entities
        .iter()
        .map(|entity| (entity.name.as_str(), entity))
        .collect::<HashMap<_, _>>();
    let stores = verify
        .stores
        .iter()
        .map(|store| (store.entity_type.as_str(), store))
        .collect::<HashMap<_, _>>();

    let mut transitions = Vec::new();
    for step in &system.actions {
        if !step.params.is_empty() || !is_true_expr(&step.guard) || step.body.is_empty() {
            return Ok(None);
        }
        let mut alternatives_by_action = Vec::new();
        for action in &step.body {
            let Some(action_transitions) =
                temporal_transitions_for_action(&step.name, action, &entities, &stores, model)?
            else {
                return Ok(None);
            };
            alternatives_by_action.push(action_transitions);
        }
        transitions.extend(combine_same_step_transitions(
            &step.name,
            &alternatives_by_action,
        ));
    }

    Ok(Some(RelTemporalTransitionSystem {
        transitions,
        allow_stutter: verify.assumption_set.stutter,
    }))
}

fn combine_same_step_transitions(
    step_name: &str,
    alternatives_by_action: &[Vec<RelTemporalTransition>],
) -> Vec<RelTemporalTransition> {
    if let [alternatives] = alternatives_by_action {
        return alternatives.clone();
    }
    let mut combined = vec![RelTemporalTransition {
        name: step_name.to_owned(),
        guard: RelTemporalFormula::True,
        updates: Vec::new(),
    }];
    for alternatives in alternatives_by_action {
        let mut next = Vec::new();
        for prefix in &combined {
            for alternative in alternatives {
                let guard = match (&prefix.guard, &alternative.guard) {
                    (RelTemporalFormula::True, guard) => guard.clone(),
                    (guard, RelTemporalFormula::True) => guard.clone(),
                    (left, right) => RelTemporalFormula::And(vec![left.clone(), right.clone()]),
                };
                let mut updates = prefix.updates.clone();
                updates.extend(alternative.updates.clone());
                next.push(RelTemporalTransition {
                    name: format!("{}+{}", prefix.name, alternative.name),
                    guard,
                    updates,
                });
            }
        }
        combined = next;
    }
    combined
}

fn temporal_transitions_for_action(
    step_name: &str,
    action: &IRAction,
    entities: &HashMap<&str, &IREntity>,
    stores: &HashMap<&str, &IRStoreDecl>,
    model: &TemporalRelationalModel,
) -> Result<Option<Vec<RelTemporalTransition>>, RelCoreError> {
    match action {
        IRAction::Create { entity, fields } => {
            let Some(store) = stores.get(entity.as_str()) else {
                return Ok(None);
            };
            let mut out = Vec::new();
            for slot in store_universe(store).atoms {
                let active_tuple = RelTuple(vec![slot.clone()]);
                let mut updates = vec![RelRelationAssignment {
                    relation: format!("{}.active", store.name),
                    tuple: active_tuple.clone(),
                    value: true,
                }];
                updates.extend(create_field_assignments(store, fields, &slot, model)?);
                out.push(RelTemporalTransition {
                    name: format!("{step_name}:create:{}", slot.name),
                    guard: RelTemporalFormula::not(RelTemporalFormula::Atom(
                        RelAtomPredicate::new(format!("{}.active", store.name), active_tuple),
                    )),
                    updates,
                });
            }
            Ok(Some(out))
        }
        IRAction::Choose {
            var,
            entity,
            filter,
            ops,
        } if ops.len() == 1 => {
            let IRAction::Apply {
                target,
                transition,
                refs,
                args,
            } = &ops[0]
            else {
                return Ok(None);
            };
            if target != var || !refs.is_empty() || !args.is_empty() {
                return Ok(None);
            }
            let Some(store) = stores.get(entity.as_str()) else {
                return Ok(None);
            };
            let Some(entity_ir) = entities.get(entity.as_str()) else {
                return Err(RelCoreError::Unsupported {
                    reason: format!("unknown temporal relational entity `{entity}`"),
                });
            };
            let Some(transition_ir) = entity_ir
                .transitions
                .iter()
                .find(|candidate| candidate.name == *transition)
            else {
                return Err(RelCoreError::Unsupported {
                    reason: format!("unknown temporal relational transition `{transition}`"),
                });
            };
            if !transition_ir.refs.is_empty()
                || !transition_ir.params.is_empty()
                || transition_ir.postcondition.is_some()
            {
                return Ok(None);
            }

            let mut out = Vec::new();
            for slot in store_universe(store).atoms {
                let active = RelTemporalFormula::Atom(RelAtomPredicate::new(
                    format!("{}.active", store.name),
                    RelTuple(vec![slot.clone()]),
                ));
                let filter = expr_for_slot(filter, var, store, &slot)?;
                let guard = expr_for_slot(&transition_ir.guard, var, store, &slot)?;
                let updates = transition_field_assignments(store, transition_ir, &slot, model)?;
                out.push(RelTemporalTransition {
                    name: format!("{step_name}:{transition}:{}", slot.name),
                    guard: RelTemporalFormula::And(vec![active, filter, guard]),
                    updates,
                });
            }
            Ok(Some(out))
        }
        _ => Ok(None),
    }
}

fn create_field_assignments(
    store: &IRStoreDecl,
    fields: &[IRCreateField],
    slot: &RelAtom,
    model: &TemporalRelationalModel,
) -> Result<Vec<RelRelationAssignment>, RelCoreError> {
    let mut assignments = Vec::new();
    for field in fields {
        let value = value_atom_for_expr(store, &field.name, &field.value)?;
        assignments.extend(field_value_assignments(
            store,
            &field.name,
            slot,
            &value,
            model,
        )?);
    }
    Ok(assignments)
}

fn transition_field_assignments(
    store: &IRStoreDecl,
    transition: &crate::ir::types::IRTransition,
    slot: &RelAtom,
    model: &TemporalRelationalModel,
) -> Result<Vec<RelRelationAssignment>, RelCoreError> {
    let mut assignments = Vec::new();
    for update in &transition.updates {
        let value = value_atom_for_expr(store, &update.field, &update.value)?;
        assignments.extend(field_value_assignments(
            store,
            &update.field,
            slot,
            &value,
            model,
        )?);
    }
    Ok(assignments)
}

fn field_value_assignments(
    store: &IRStoreDecl,
    field: &str,
    slot: &RelAtom,
    value: &RelAtom,
    model: &TemporalRelationalModel,
) -> Result<Vec<RelRelationAssignment>, RelCoreError> {
    let relation_name = format!("{}.{}", store.name, field);
    let relation = model
        .relation(&relation_name)
        .ok_or_else(|| RelCoreError::Unsupported {
            reason: format!("unknown temporal relational relation `{relation_name}`"),
        })?;
    Ok(relation.snapshots[0]
        .upper
        .iter()
        .filter(|tuple| tuple.0.first() == Some(slot))
        .map(|tuple| RelRelationAssignment {
            relation: relation_name.clone(),
            value: tuple.0.get(1) == Some(value),
            tuple: tuple.clone(),
        })
        .collect())
}

fn expr_for_slot(
    expr: &IRExpr,
    var: &str,
    store: &IRStoreDecl,
    slot: &RelAtom,
) -> Result<RelTemporalFormula, RelCoreError> {
    match expr {
        IRExpr::Lit {
            value: LitVal::Bool { value },
            ..
        } => Ok(if *value {
            RelTemporalFormula::True
        } else {
            RelTemporalFormula::False
        }),
        IRExpr::UnOp { op, operand, .. } if op == "!" || op == "not" => Ok(
            RelTemporalFormula::not(expr_for_slot(operand, var, store, slot)?),
        ),
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "&&" || op == "and" => Ok(RelTemporalFormula::And(vec![
            expr_for_slot(left, var, store, slot)?,
            expr_for_slot(right, var, store, slot)?,
        ])),
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "||" || op == "or" => Ok(RelTemporalFormula::Or(vec![
            expr_for_slot(left, var, store, slot)?,
            expr_for_slot(right, var, store, slot)?,
        ])),
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "==" || op == "!=" => {
            let atom = field_equality_atom(left, right, var, store, slot)
                .or_else(|| field_equality_atom(right, left, var, store, slot))
                .ok_or_else(|| RelCoreError::Unsupported {
                    reason: "unsupported temporal relational equality guard".to_owned(),
                })??;
            if op == "==" {
                Ok(atom)
            } else {
                Ok(RelTemporalFormula::not(atom))
            }
        }
        _ => Err(RelCoreError::Unsupported {
            reason: format!("unsupported temporal relational expression `{expr:?}`"),
        }),
    }
}

fn field_equality_atom(
    field_expr: &IRExpr,
    value_expr: &IRExpr,
    var: &str,
    store: &IRStoreDecl,
    slot: &RelAtom,
) -> Option<Result<RelTemporalFormula, RelCoreError>> {
    let IRExpr::Field { expr, field, .. } = field_expr else {
        return None;
    };
    let IRExpr::Var { name, .. } = &**expr else {
        return None;
    };
    if name != var {
        return None;
    }
    Some(value_atom_for_expr(store, field, value_expr).map(|value| {
        RelTemporalFormula::Atom(RelAtomPredicate::new(
            format!("{}.{}", store.name, field),
            RelTuple(vec![slot.clone(), value]),
        ))
    }))
}

fn value_atom_for_expr(
    store: &IRStoreDecl,
    field: &str,
    expr: &IRExpr,
) -> Result<RelAtom, RelCoreError> {
    let universe = format!("{}.{}", store.name, field);
    match expr {
        IRExpr::Lit {
            value: LitVal::Bool { value },
            ..
        } => Ok(RelAtom::new(
            &universe,
            if *value { "true" } else { "false" },
        )),
        IRExpr::Ctor {
            enum_name, ctor, ..
        } => Ok(RelAtom::new(&universe, format!("{enum_name}::{ctor}"))),
        _ => Err(RelCoreError::Unsupported {
            reason: format!("unsupported temporal relational finite value `{expr:?}`"),
        }),
    }
}

fn is_true_expr(expr: &IRExpr) -> bool {
    matches!(
        expr,
        IRExpr::Lit {
            value: LitVal::Bool { value: true },
            ..
        }
    )
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum RelTemporalFormula {
    True,
    False,
    Atom(RelAtomPredicate),
    Not(Box<RelTemporalFormula>),
    And(Vec<RelTemporalFormula>),
    Or(Vec<RelTemporalFormula>),
    Next(Box<RelTemporalFormula>),
    Previously(Box<RelTemporalFormula>),
    Eventually(Box<RelTemporalFormula>),
    Always(Box<RelTemporalFormula>),
    Once(Box<RelTemporalFormula>),
    Historically(Box<RelTemporalFormula>),
    Until(Box<RelTemporalFormula>, Box<RelTemporalFormula>),
    Release(Box<RelTemporalFormula>, Box<RelTemporalFormula>),
    Since(Box<RelTemporalFormula>, Box<RelTemporalFormula>),
}

impl RelTemporalFormula {
    fn not(inner: Self) -> Self {
        Self::Not(Box::new(inner))
    }

    fn eventually(inner: Self) -> Self {
        Self::Eventually(Box::new(inner))
    }

    fn previously(inner: Self) -> Self {
        Self::Previously(Box::new(inner))
    }

    fn always(inner: Self) -> Self {
        Self::Always(Box::new(inner))
    }

    fn once(inner: Self) -> Self {
        Self::Once(Box::new(inner))
    }

    fn historically(inner: Self) -> Self {
        Self::Historically(Box::new(inner))
    }

    fn until(left: Self, right: Self) -> Self {
        Self::Until(Box::new(left), Box::new(right))
    }

    fn release(left: Self, right: Self) -> Self {
        Self::Release(Box::new(left), Box::new(right))
    }

    fn since(left: Self, right: Self) -> Self {
        Self::Since(Box::new(left), Box::new(right))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct RelAtomPredicate {
    relation: String,
    tuple: RelTuple,
}

impl RelAtomPredicate {
    fn new(relation: impl Into<String>, tuple: RelTuple) -> Self {
        Self {
            relation: relation.into(),
            tuple,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(super) struct RelSatWitness {
    pub(super) loop_start: usize,
    pub(super) steps: Vec<RelSatWitnessStep>,
    pub(super) transitions: Vec<RelTransitionObservation>,
    pub(super) projections: Vec<RelProjectedStep>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(super) struct RelSatWitnessStep {
    pub(super) step: usize,
    pub(super) true_tuples: Vec<RelTrueTuple>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(super) struct RelTrueTuple {
    pub(super) relation: String,
    pub(super) tuple: RelTuple,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(super) struct RelTransitionObservation {
    pub(super) step: usize,
    pub(super) next_step: usize,
    pub(super) transition: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(super) struct RelProjectedStep {
    pub(super) step: usize,
    pub(super) stores: Vec<RelProjectedStore>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(super) struct RelProjectedStore {
    pub(super) store: String,
    pub(super) slots: Vec<RelProjectedEntitySlot>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(super) struct RelProjectedEntitySlot {
    pub(super) slot: String,
    pub(super) active: bool,
    pub(super) fields: Vec<RelProjectedField>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(super) struct RelProjectedField {
    pub(super) field: String,
    pub(super) values: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct RelTemporalTransitionSystem {
    pub(super) transitions: Vec<RelTemporalTransition>,
    pub(super) allow_stutter: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct RelTemporalTransition {
    pub(super) name: String,
    pub(super) guard: RelTemporalFormula,
    pub(super) updates: Vec<RelRelationAssignment>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct RelRelationAssignment {
    pub(super) relation: String,
    pub(super) tuple: RelTuple,
    pub(super) value: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct RelSatVarKey {
    relation: String,
    step: usize,
    tuple: RelTuple,
}

struct RelTransitionFireVar {
    step: usize,
    next_step: usize,
    transition: String,
    lit: Lit,
}

struct RelTemporalSatEncoder<'a> {
    model: &'a TemporalRelationalModel,
    sat: SatInstance,
    vars: HashMap<RelSatVarKey, Lit>,
    transition_fires: Vec<RelTransitionFireVar>,
}

impl<'a> RelTemporalSatEncoder<'a> {
    fn new(model: &'a TemporalRelationalModel) -> Self {
        Self {
            model,
            sat: SatInstance::new(),
            vars: HashMap::new(),
            transition_fires: Vec::new(),
        }
    }

    fn solve(
        mut self,
        formula: &RelTemporalFormula,
        transition_system: Option<&RelTemporalTransitionSystem>,
    ) -> Result<Option<RelSatWitness>, RelCoreError> {
        self.allocate_relation_vars();
        self.assert_relation_bounds()?;
        self.assert_loop_equality()?;
        if let Some(transition_system) = transition_system {
            self.assert_transition_system(transition_system)?;
        }
        let root = self.encode_formula(formula, 0)?;
        self.sat.add_unit(root);

        let (cnf, _) = self.sat.into_cnf();
        let mut solver = BasicSolver::default();
        solver
            .add_cnf(cnf)
            .map_err(|err| RelCoreError::Unsupported {
                reason: format!("RustSAT setup failed for temporal relational core: {err}"),
            })?;
        match solver.solve().map_err(|err| RelCoreError::Unsupported {
            reason: format!("RustSAT solve failed for temporal relational core: {err}"),
        })? {
            SolverResult::Sat => Ok(Some(build_witness(
                self.model,
                &self.vars,
                &self.transition_fires,
                &solver,
            )?)),
            SolverResult::Unsat | SolverResult::Interrupted => Ok(None),
        }
    }

    fn allocate_relation_vars(&mut self) {
        for relation in &self.model.relations {
            for (step, snapshot) in relation.snapshots.iter().enumerate() {
                for tuple in &snapshot.upper {
                    let key = RelSatVarKey {
                        relation: relation.symbol.name.clone(),
                        step,
                        tuple: tuple.clone(),
                    };
                    self.vars.entry(key).or_insert_with(|| self.sat.new_lit());
                }
            }
        }
    }

    fn assert_relation_bounds(&mut self) -> Result<(), RelCoreError> {
        for relation in &self.model.relations {
            for (step, snapshot) in relation.snapshots.iter().enumerate() {
                for tuple in &snapshot.lower {
                    let lit = self.relation_lit(&relation.symbol.name, tuple, step)?;
                    self.sat.add_unit(lit);
                }
            }
        }
        Ok(())
    }

    fn assert_loop_equality(&mut self) -> Result<(), RelCoreError> {
        let loop_start = self.model.trace.loop_start;
        let depth = self.model.trace.depth;
        for relation in &self.model.relations {
            if !relation.symbol.mutable {
                continue;
            }
            for tuple in &relation.snapshots[loop_start].upper {
                let loop_lit = self.relation_lit(&relation.symbol.name, tuple, loop_start)?;
                let depth_lit = self.relation_lit(&relation.symbol.name, tuple, depth)?;
                self.sat.add_binary(!loop_lit, depth_lit);
                self.sat.add_binary(loop_lit, !depth_lit);
            }
        }
        Ok(())
    }

    fn assert_transition_system(
        &mut self,
        system: &RelTemporalTransitionSystem,
    ) -> Result<(), RelCoreError> {
        for step in 0..self.model.trace.step_count() {
            let next_step = self.model.trace.successor(step)?;
            let mut fires = Vec::with_capacity(system.transitions.len());
            for transition in &system.transitions {
                let fire = self.sat.new_lit();
                let guard = self.encode_formula(&transition.guard, step)?;
                self.sat.add_binary(!fire, guard);
                for update in &transition.updates {
                    let next = self.relation_lit(&update.relation, &update.tuple, next_step)?;
                    self.sat
                        .add_binary(!fire, if update.value { next } else { !next });
                }
                self.transition_fires.push(RelTransitionFireVar {
                    step,
                    next_step,
                    transition: transition.name.clone(),
                    lit: fire,
                });
                fires.push((fire, transition));
            }

            for i in 0..fires.len() {
                for j in (i + 1)..fires.len() {
                    self.sat.add_binary(!fires[i].0, !fires[j].0);
                }
            }
            if !system.allow_stutter && !fires.is_empty() {
                let fire_lits = fires.iter().map(|(fire, _)| *fire).collect::<Vec<_>>();
                self.sat.add_clause(fire_lits.as_slice().into());
            }

            self.assert_transition_frame(step, next_step, &fires)?;
        }
        Ok(())
    }

    fn assert_transition_frame(
        &mut self,
        step: usize,
        next_step: usize,
        fires: &[(Lit, &RelTemporalTransition)],
    ) -> Result<(), RelCoreError> {
        let no_fire_inputs = fires.iter().map(|(fire, _)| !*fire).collect::<Vec<_>>();
        let no_fire = self.and_lit(&no_fire_inputs);
        for relation in &self.model.relations {
            if !relation.symbol.mutable {
                continue;
            }
            for tuple in &relation.snapshots[step].upper {
                let current = self.relation_lit(&relation.symbol.name, tuple, step)?;
                let next = self.relation_lit(&relation.symbol.name, tuple, next_step)?;
                let mut true_reasons = vec![self.and_lit(&[no_fire, current])];
                for (fire, transition) in fires {
                    match transition_assignment(transition, &relation.symbol.name, tuple) {
                        Some(true) => true_reasons.push(*fire),
                        Some(false) => {}
                        None => true_reasons.push(self.and_lit(&[*fire, current])),
                    }
                }
                let source = self.or_lit(&true_reasons);
                self.sat.add_binary(!next, source);
                self.sat.add_binary(!source, next);
            }
        }
        Ok(())
    }

    fn encode_formula(
        &mut self,
        formula: &RelTemporalFormula,
        step: usize,
    ) -> Result<Lit, RelCoreError> {
        match formula {
            RelTemporalFormula::True => Ok(self.const_lit(true)),
            RelTemporalFormula::False => Ok(self.const_lit(false)),
            RelTemporalFormula::Atom(atom) => self.relation_lit(&atom.relation, &atom.tuple, step),
            RelTemporalFormula::Not(inner) => Ok(!self.encode_formula(inner, step)?),
            RelTemporalFormula::And(parts) => {
                let lits = parts
                    .iter()
                    .map(|part| self.encode_formula(part, step))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.and_lit(&lits))
            }
            RelTemporalFormula::Or(parts) => {
                let lits = parts
                    .iter()
                    .map(|part| self.encode_formula(part, step))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.or_lit(&lits))
            }
            RelTemporalFormula::Next(inner) => {
                let next = self.model.trace.successor(step)?;
                self.encode_formula(inner, next)
            }
            RelTemporalFormula::Previously(inner) => {
                if step == 0 {
                    Ok(self.const_lit(false))
                } else {
                    self.encode_formula(inner, step - 1)
                }
            }
            RelTemporalFormula::Eventually(inner) => {
                let lits = self
                    .future_window(step)
                    .into_iter()
                    .map(|future| self.encode_formula(inner, future))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.or_lit(&lits))
            }
            RelTemporalFormula::Always(inner) => {
                let lits = self
                    .future_window(step)
                    .into_iter()
                    .map(|future| self.encode_formula(inner, future))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.and_lit(&lits))
            }
            RelTemporalFormula::Once(inner) => {
                let lits = self
                    .past_window(step)
                    .into_iter()
                    .map(|past| self.encode_formula(inner, past))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.or_lit(&lits))
            }
            RelTemporalFormula::Historically(inner) => {
                let lits = self
                    .past_window(step)
                    .into_iter()
                    .map(|past| self.encode_formula(inner, past))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.and_lit(&lits))
            }
            RelTemporalFormula::Until(left, right) => {
                let mut disjuncts = Vec::new();
                let window = self.future_window(step);
                for (offset, candidate) in window.iter().enumerate() {
                    let mut conjuncts = vec![self.encode_formula(right, *candidate)?];
                    for prior in window.iter().take(offset) {
                        conjuncts.push(self.encode_formula(left, *prior)?);
                    }
                    let conjunct = self.and_lit(&conjuncts);
                    disjuncts.push(conjunct);
                }
                Ok(self.or_lit(&disjuncts))
            }
            RelTemporalFormula::Release(left, right) => {
                let dual = RelTemporalFormula::not(RelTemporalFormula::until(
                    RelTemporalFormula::not((**left).clone()),
                    RelTemporalFormula::not((**right).clone()),
                ));
                self.encode_formula(&dual, step)
            }
            RelTemporalFormula::Since(left, right) => {
                let mut disjuncts = Vec::new();
                let window = self.past_window(step);
                for (offset, candidate) in window.iter().enumerate() {
                    let mut conjuncts = vec![self.encode_formula(right, *candidate)?];
                    for prior in window.iter().skip(offset + 1) {
                        conjuncts.push(self.encode_formula(left, *prior)?);
                    }
                    let conjunct = self.and_lit(&conjuncts);
                    disjuncts.push(conjunct);
                }
                Ok(self.or_lit(&disjuncts))
            }
        }
    }

    fn relation_lit(
        &self,
        relation: &str,
        tuple: &RelTuple,
        step: usize,
    ) -> Result<Lit, RelCoreError> {
        self.vars
            .get(&RelSatVarKey {
                relation: relation.to_owned(),
                step,
                tuple: tuple.clone(),
            })
            .copied()
            .ok_or_else(|| RelCoreError::Unsupported {
                reason: format!("tuple {tuple:?} is outside relation {relation} at step {step}"),
            })
    }

    fn future_window(&self, step: usize) -> Vec<usize> {
        if step < self.model.trace.loop_start {
            (step..=self.model.trace.depth).collect()
        } else {
            (step..=self.model.trace.depth)
                .chain(self.model.trace.loop_start..step)
                .collect()
        }
    }

    fn past_window(&self, step: usize) -> Vec<usize> {
        (0..=step).collect()
    }

    fn const_lit(&mut self, value: bool) -> Lit {
        let lit = self.sat.new_lit();
        self.sat.add_unit(if value { lit } else { !lit });
        lit
    }

    fn and_lit(&mut self, lits: &[Lit]) -> Lit {
        if lits.is_empty() {
            return self.const_lit(true);
        }
        if lits.len() == 1 {
            return lits[0];
        }
        let out = self.sat.new_lit();
        for &lit in lits {
            self.sat.add_binary(!out, lit);
        }
        let mut clause = vec![out];
        clause.extend(lits.iter().map(|lit| !*lit));
        self.sat.add_clause(clause.as_slice().into());
        out
    }

    fn or_lit(&mut self, lits: &[Lit]) -> Lit {
        if lits.is_empty() {
            return self.const_lit(false);
        }
        if lits.len() == 1 {
            return lits[0];
        }
        let out = self.sat.new_lit();
        for &lit in lits {
            self.sat.add_binary(!lit, out);
        }
        let mut clause = vec![!out];
        clause.extend(lits.iter().copied());
        self.sat.add_clause(clause.as_slice().into());
        out
    }
}

fn build_witness(
    model: &TemporalRelationalModel,
    vars: &HashMap<RelSatVarKey, Lit>,
    transition_fires: &[RelTransitionFireVar],
    solver: &BasicSolver,
) -> Result<RelSatWitness, RelCoreError> {
    let mut steps = Vec::new();
    for step in 0..model.trace.step_count() {
        let mut true_tuples = Vec::new();
        for relation in &model.relations {
            for tuple in &relation.snapshots[step].upper {
                let key = RelSatVarKey {
                    relation: relation.symbol.name.clone(),
                    step,
                    tuple: tuple.clone(),
                };
                let Some(lit) = vars.get(&key) else {
                    continue;
                };
                if matches!(solver.lit_val(*lit), Ok(TernaryVal::True)) {
                    true_tuples.push(RelTrueTuple {
                        relation: relation.symbol.name.clone(),
                        tuple: tuple.clone(),
                    });
                }
            }
        }
        steps.push(RelSatWitnessStep { step, true_tuples });
    }
    let transitions = transition_fires
        .iter()
        .filter(|fire| matches!(solver.lit_val(fire.lit), Ok(TernaryVal::True)))
        .map(|fire| RelTransitionObservation {
            step: fire.step,
            next_step: fire.next_step,
            transition: fire.transition.clone(),
        })
        .collect::<Vec<_>>();
    let projections = project_witness(model, &steps);
    Ok(RelSatWitness {
        loop_start: model.trace.loop_start,
        steps,
        transitions,
        projections,
    })
}

fn project_witness(
    model: &TemporalRelationalModel,
    steps: &[RelSatWitnessStep],
) -> Vec<RelProjectedStep> {
    steps
        .iter()
        .map(|step| {
            let true_tuples = step
                .true_tuples
                .iter()
                .map(|true_tuple| (true_tuple.relation.as_str(), &true_tuple.tuple))
                .collect::<HashSet<_>>();
            let stores = model
                .relations
                .iter()
                .filter_map(|relation| match &relation.symbol.kind {
                    RelationKind::Active { store, .. } => Some((store, relation)),
                    RelationKind::Field { .. } => None,
                })
                .map(|(store, active_relation)| {
                    let slots = active_relation.snapshots[step.step]
                        .upper
                        .iter()
                        .filter_map(|tuple| {
                            let slot = tuple.0.first()?;
                            let active = true_tuples
                                .contains(&(active_relation.symbol.name.as_str(), tuple));
                            let fields =
                                project_slot_fields(model, step.step, store, slot, &true_tuples);
                            Some(RelProjectedEntitySlot {
                                slot: slot.name.clone(),
                                active,
                                fields,
                            })
                        })
                        .collect::<Vec<_>>();
                    RelProjectedStore {
                        store: store.clone(),
                        slots,
                    }
                })
                .collect::<Vec<_>>();
            RelProjectedStep {
                step: step.step,
                stores,
            }
        })
        .collect()
}

fn project_slot_fields(
    model: &TemporalRelationalModel,
    step: usize,
    store: &str,
    slot: &RelAtom,
    true_tuples: &HashSet<(&str, &RelTuple)>,
) -> Vec<RelProjectedField> {
    model
        .relations
        .iter()
        .filter_map(|relation| match &relation.symbol.kind {
            RelationKind::Field {
                store: field_store,
                field,
                ..
            } if field_store == store => Some((field, relation)),
            _ => None,
        })
        .map(|(field, relation)| {
            let values = relation.snapshots[step]
                .upper
                .iter()
                .filter(|tuple| tuple.0.first() == Some(slot))
                .filter(|tuple| true_tuples.contains(&(relation.symbol.name.as_str(), *tuple)))
                .filter_map(|tuple| tuple.0.get(1).map(|atom| atom.name.clone()))
                .collect::<Vec<_>>();
            RelProjectedField {
                field: field.clone(),
                values,
            }
        })
        .collect()
}

fn solve_temporal_formula(
    model: &TemporalRelationalModel,
    formula: &RelTemporalFormula,
) -> Result<Option<RelSatWitness>, RelCoreError> {
    solve_temporal_formula_with_transitions(model, formula, None)
}

fn solve_temporal_formula_with_transitions(
    model: &TemporalRelationalModel,
    formula: &RelTemporalFormula,
    transition_system: Option<&RelTemporalTransitionSystem>,
) -> Result<Option<RelSatWitness>, RelCoreError> {
    RelTemporalSatEncoder::new(model).solve(formula, transition_system)
}

fn transition_assignment(
    transition: &RelTemporalTransition,
    relation: &str,
    tuple: &RelTuple,
) -> Option<bool> {
    transition
        .updates
        .iter()
        .find(|update| update.relation == relation && update.tuple == *tuple)
        .map(|update| update.value)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct RelTrace {
    pub(super) depth: usize,
    pub(super) loop_start: usize,
}

impl RelTrace {
    pub(super) fn new(depth: usize, loop_start: usize) -> Result<Self, RelCoreError> {
        if loop_start > depth {
            return Err(RelCoreError::Unsupported {
                reason: format!("loop start {loop_start} exceeds trace depth {depth}"),
            });
        }
        Ok(Self { depth, loop_start })
    }

    pub(super) fn step_count(&self) -> usize {
        self.depth + 1
    }

    pub(super) fn successor(&self, step: usize) -> Result<usize, RelCoreError> {
        if step > self.depth {
            return Err(RelCoreError::Unsupported {
                reason: format!("step {step} is outside trace depth {}", self.depth),
            });
        }
        Ok(if step == self.depth {
            self.loop_start
        } else {
            step + 1
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct RelUniverse {
    pub(super) name: String,
    pub(super) atoms: Vec<RelAtom>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub(super) struct RelAtom {
    pub(super) universe: String,
    pub(super) name: String,
}

impl RelAtom {
    fn new(universe: &str, name: impl Into<String>) -> Self {
        Self {
            universe: universe.to_owned(),
            name: name.into(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum RelationKind {
    Active {
        store: String,
        entity: String,
    },
    Field {
        store: String,
        entity: String,
        field: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct RelRelationSymbol {
    pub(super) name: String,
    pub(super) arity: usize,
    pub(super) mutable: bool,
    pub(super) kind: RelationKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub(super) struct RelTuple(pub(super) Vec<RelAtom>);

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct RelRelationBound {
    pub(super) lower: Vec<RelTuple>,
    pub(super) upper: Vec<RelTuple>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct RelTemporalRelation {
    pub(super) symbol: RelRelationSymbol,
    pub(super) snapshots: Vec<RelRelationBound>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct RelFiniteDomain {
    universe: RelUniverse,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum RelCoreError {
    Unsupported { reason: String },
}

struct RelCoreBuilder {
    trace: RelTrace,
    universes: Vec<RelUniverse>,
    relations: Vec<RelTemporalRelation>,
}

impl RelCoreBuilder {
    fn new(trace: RelTrace) -> Self {
        Self {
            trace,
            universes: Vec::new(),
            relations: Vec::new(),
        }
    }

    fn add_store(&mut self, store: &IRStoreDecl, entity: &IREntity) -> Result<(), RelCoreError> {
        let entity_universe = store_universe(store);
        self.universes.push(entity_universe.clone());
        self.relations.push(self.active_relation(store, entity));

        for field in &entity.fields {
            let domain = finite_domain_for_field(store, field)?;
            self.universes.push(domain.universe.clone());
            self.relations.push(self.field_relation(
                store,
                entity,
                field,
                &entity_universe,
                &domain,
            ));
        }

        Ok(())
    }

    fn active_relation(&self, store: &IRStoreDecl, entity: &IREntity) -> RelTemporalRelation {
        let upper = store_universe(store)
            .atoms
            .into_iter()
            .map(|atom| RelTuple(vec![atom]))
            .collect::<Vec<_>>();
        RelTemporalRelation {
            symbol: RelRelationSymbol {
                name: format!("{}.active", store.name),
                arity: 1,
                mutable: true,
                kind: RelationKind::Active {
                    store: store.name.clone(),
                    entity: entity.name.clone(),
                },
            },
            snapshots: repeated_empty_lower_bounds(&self.trace, upper),
        }
    }

    fn field_relation(
        &self,
        store: &IRStoreDecl,
        entity: &IREntity,
        field: &IRField,
        entity_universe: &RelUniverse,
        domain: &RelFiniteDomain,
    ) -> RelTemporalRelation {
        let upper =
            entity_universe
                .atoms
                .iter()
                .flat_map(|entity_atom| {
                    domain.universe.atoms.iter().map(move |value_atom| {
                        RelTuple(vec![entity_atom.clone(), value_atom.clone()])
                    })
                })
                .collect::<Vec<_>>();
        RelTemporalRelation {
            symbol: RelRelationSymbol {
                name: format!("{}.{}", store.name, field.name),
                arity: 2,
                mutable: true,
                kind: RelationKind::Field {
                    store: store.name.clone(),
                    entity: entity.name.clone(),
                    field: field.name.clone(),
                },
            },
            snapshots: repeated_empty_lower_bounds(&self.trace, upper),
        }
    }

    fn finish(self) -> TemporalRelationalModel {
        TemporalRelationalModel {
            trace: self.trace,
            universes: self.universes,
            relations: self.relations,
        }
    }
}

fn store_universe(store: &IRStoreDecl) -> RelUniverse {
    let atom_count = store.hi.max(0) as usize;
    RelUniverse {
        name: store.name.clone(),
        atoms: (0..atom_count)
            .map(|slot| RelAtom::new(&store.name, format!("{}[{slot}]", store.name)))
            .collect(),
    }
}

fn finite_domain_for_field(
    store: &IRStoreDecl,
    field: &IRField,
) -> Result<RelFiniteDomain, RelCoreError> {
    match unrefined_type(&field.ty) {
        IRType::Bool => Ok(RelFiniteDomain {
            universe: RelUniverse {
                name: format!("{}.{}", store.name, field.name),
                atoms: vec![
                    RelAtom::new(&format!("{}.{}", store.name, field.name), "false"),
                    RelAtom::new(&format!("{}.{}", store.name, field.name), "true"),
                ],
            },
        }),
        IRType::Identity => Ok(RelFiniteDomain {
            universe: store_universe(store),
        }),
        IRType::Enum { name, variants }
            if variants.iter().all(|variant| variant.fields.is_empty()) =>
        {
            let universe_name = format!("{}.{}", store.name, field.name);
            Ok(RelFiniteDomain {
                universe: RelUniverse {
                    name: universe_name.clone(),
                    atoms: variants
                        .iter()
                        .map(|variant| {
                            RelAtom::new(&universe_name, format!("{name}::{}", variant.name))
                        })
                        .collect(),
                },
            })
        }
        other => Err(RelCoreError::Unsupported {
            reason: format!(
                "field {}.{} has non-finite or unsupported temporal relational type {other:?}",
                store.name, field.name
            ),
        }),
    }
}

fn unrefined_type(ty: &IRType) -> &IRType {
    match ty {
        IRType::Refinement { base, .. } => unrefined_type(base),
        other => other,
    }
}

fn repeated_empty_lower_bounds(trace: &RelTrace, upper: Vec<RelTuple>) -> Vec<RelRelationBound> {
    (0..trace.step_count())
        .map(|_| RelRelationBound {
            lower: Vec::new(),
            upper: upper.clone(),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::types::{
        IRAssumptionSet, IRField, IRStoreDecl, IRSystem, IRSystemAction, IRTransition, IRUpdate,
        IRVariant, IRVerifySystem,
    };
    use crate::verify::ltl::{Formula, LassoWord};

    fn bool_expr(value: bool) -> IRExpr {
        IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value },
            span: None,
        }
    }

    fn bool_field(name: &str) -> IRField {
        IRField {
            name: name.to_owned(),
            ty: IRType::Bool,
            default: None,
            initial_constraint: None,
        }
    }

    fn enum_field(name: &str) -> IRField {
        IRField {
            name: name.to_owned(),
            ty: IRType::Enum {
                name: "OrderStatus".to_owned(),
                variants: vec![IRVariant::simple("Open"), IRVariant::simple("Closed")],
            },
            default: None,
            initial_constraint: None,
        }
    }

    fn int_field(name: &str) -> IRField {
        IRField {
            name: name.to_owned(),
            ty: IRType::Int,
            default: None,
            initial_constraint: None,
        }
    }

    fn entity_with_fields(fields: Vec<IRField>) -> IREntity {
        IREntity {
            name: "Order".to_owned(),
            fields,
            transitions: Vec::new(),
            derived_fields: Vec::new(),
            invariants: Vec::new(),
            fsm_decls: Vec::new(),
        }
    }

    fn program(entity: IREntity) -> IRProgram {
        IRProgram {
            types: Vec::new(),
            constants: Vec::new(),
            functions: Vec::new(),
            entities: vec![entity],
            systems: Vec::new(),
            verifies: Vec::new(),
            theorems: Vec::new(),
            axioms: Vec::new(),
            lemmas: Vec::new(),
            scenes: Vec::new(),
        }
    }

    fn program_with_system(entity: IREntity, system: IRSystem) -> IRProgram {
        program_with_entities_system(vec![entity], system)
    }

    fn program_with_entities_system(entities: Vec<IREntity>, system: IRSystem) -> IRProgram {
        IRProgram {
            types: Vec::new(),
            constants: Vec::new(),
            functions: Vec::new(),
            entities,
            systems: vec![system],
            verifies: Vec::new(),
            theorems: Vec::new(),
            axioms: Vec::new(),
            lemmas: Vec::new(),
            scenes: Vec::new(),
        }
    }

    fn verify(depth: usize) -> IRVerify {
        IRVerify {
            name: "temporal_relational".to_owned(),
            depth: Some(depth),
            systems: Vec::new(),
            stores: vec![IRStoreDecl {
                name: "orders".to_owned(),
                entity_type: "Order".to_owned(),
                lo: 0,
                hi: 2,
            }],
            assumption_set: IRAssumptionSet::default_for_verify(),
            asserts: Vec::new(),
            span: None,
            file: None,
        }
    }

    fn verify_for_system(depth: usize) -> IRVerify {
        IRVerify {
            systems: vec![IRVerifySystem {
                name: "Commerce".to_owned(),
                lo: 1,
                hi: 1,
            }],
            ..verify(depth)
        }
    }

    fn payable_entity() -> IREntity {
        IREntity {
            name: "Order".to_owned(),
            fields: vec![bool_field("paid")],
            transitions: vec![IRTransition {
                name: "pay".to_owned(),
                refs: Vec::new(),
                params: Vec::new(),
                guard: bool_expr(true),
                updates: vec![IRUpdate {
                    field: "paid".to_owned(),
                    value: bool_expr(true),
                }],
                postcondition: None,
            }],
            derived_fields: Vec::new(),
            invariants: Vec::new(),
            fsm_decls: Vec::new(),
        }
    }

    fn commerce_system() -> IRSystem {
        IRSystem {
            name: "Commerce".to_owned(),
            store_params: Vec::new(),
            fields: Vec::new(),
            entities: vec!["Order".to_owned()],
            commands: Vec::new(),
            actions: vec![
                IRSystemAction {
                    name: "open".to_owned(),
                    params: Vec::new(),
                    guard: bool_expr(true),
                    body: vec![IRAction::Create {
                        entity: "Order".to_owned(),
                        fields: vec![IRCreateField {
                            name: "paid".to_owned(),
                            value: bool_expr(false),
                        }],
                    }],
                    return_expr: None,
                },
                IRSystemAction {
                    name: "pay".to_owned(),
                    params: Vec::new(),
                    guard: bool_expr(true),
                    body: vec![IRAction::Choose {
                        var: "o".to_owned(),
                        entity: "Order".to_owned(),
                        filter: Box::new(bool_expr(true)),
                        ops: vec![IRAction::Apply {
                            target: "o".to_owned(),
                            transition: "pay".to_owned(),
                            refs: Vec::new(),
                            args: Vec::new(),
                        }],
                    }],
                    return_expr: None,
                },
            ],
            fsm_decls: Vec::new(),
            derived_fields: Vec::new(),
            invariants: Vec::new(),
            queries: Vec::new(),
            preds: Vec::new(),
            let_bindings: Vec::new(),
            procs: Vec::new(),
        }
    }

    fn model_with_loop(depth: usize, loop_start: usize) -> TemporalRelationalModel {
        let ir = program(entity_with_fields(vec![
            bool_field("paid"),
            enum_field("status"),
        ]));
        TemporalRelationalModel::from_verify_with_loop_start(&ir, &verify(depth), loop_start)
            .expect("model")
    }

    fn tuple(model: &TemporalRelationalModel, relation: &str, index: usize) -> RelTuple {
        model.relation(relation).expect(relation).snapshots[0].upper[index].clone()
    }

    fn atom(model: &TemporalRelationalModel, relation: &str, index: usize) -> RelTemporalFormula {
        RelTemporalFormula::Atom(RelAtomPredicate::new(
            relation,
            tuple(model, relation, index),
        ))
    }

    fn require_tuple_at_step_zero(
        model: &mut TemporalRelationalModel,
        relation: &str,
        tuple: RelTuple,
    ) {
        model
            .relations
            .iter_mut()
            .find(|candidate| candidate.symbol.name == relation)
            .expect(relation)
            .snapshots[0]
            .lower
            .push(tuple);
    }

    fn fire_pay_transition(model: &TemporalRelationalModel) -> RelTemporalTransitionSystem {
        RelTemporalTransitionSystem {
            allow_stutter: false,
            transitions: vec![RelTemporalTransition {
                name: "pay".to_owned(),
                guard: atom(model, "orders.active", 0),
                updates: vec![RelRelationAssignment {
                    relation: "orders.paid".to_owned(),
                    tuple: tuple(model, "orders.paid", 1),
                    value: true,
                }],
            }],
        }
    }

    #[test]
    fn trace_successor_wraps_at_lasso_boundary() {
        let trace = RelTrace::new(3, 1).expect("trace");

        assert_eq!(trace.step_count(), 4);
        assert_eq!(trace.successor(0), Ok(1));
        assert_eq!(trace.successor(1), Ok(2));
        assert_eq!(trace.successor(2), Ok(3));
        assert_eq!(trace.successor(3), Ok(1));
        assert!(matches!(
            RelTrace::new(2, 3),
            Err(RelCoreError::Unsupported { .. })
        ));
    }

    #[test]
    fn model_maps_store_slots_and_finite_fields_to_temporal_relations() {
        let ir = program(entity_with_fields(vec![
            bool_field("paid"),
            enum_field("status"),
        ]));
        let model = TemporalRelationalModel::from_verify(&ir, &verify(3)).expect("model");

        assert_eq!(model.trace.step_count(), 4);
        assert_eq!(model.universe("orders").expect("orders").atoms.len(), 2);

        let active = model.relation("orders.active").expect("active");
        assert_eq!(active.symbol.arity, 1);
        assert_eq!(active.snapshots.len(), 4);
        assert_eq!(active.snapshots[0].upper.len(), 2);

        let paid = model.relation("orders.paid").expect("paid");
        assert_eq!(paid.symbol.arity, 2);
        assert_eq!(paid.snapshots.len(), 4);
        assert_eq!(paid.snapshots[0].upper.len(), 4);

        let status = model.relation("orders.status").expect("status");
        assert_eq!(status.snapshots[0].upper.len(), 4);
        assert!(status.snapshots[0]
            .upper
            .iter()
            .any(|tuple| tuple.0[1].name == "OrderStatus::Closed"));
    }

    #[test]
    fn model_rejects_non_finite_field_before_sat_encoding() {
        let ir = program(entity_with_fields(vec![int_field("amount")]));
        let err = TemporalRelationalModel::from_verify(&ir, &verify(2)).expect_err("unsupported");

        assert!(matches!(err, RelCoreError::Unsupported { .. }));
        let RelCoreError::Unsupported { reason } = err;
        assert!(reason.contains("orders.amount"));
        assert!(reason.contains("unsupported temporal relational type"));
    }

    #[test]
    fn temporal_sat_finds_witness_for_eventually_relation_tuple() {
        let model = model_with_loop(2, 1);
        let active = tuple(&model, "orders.active", 0);
        let formula = RelTemporalFormula::eventually(RelTemporalFormula::Atom(
            RelAtomPredicate::new("orders.active", active.clone()),
        ));

        let witness = solve_temporal_formula(&model, &formula)
            .expect("solve")
            .expect("satisfiable");

        assert_eq!(witness.loop_start, 1);
        assert_eq!(witness.steps.len(), 3);
        assert!(witness.steps.iter().any(|step| step.true_tuples.iter().any(
            |true_tuple| true_tuple.relation == "orders.active" && true_tuple.tuple == active
        )));
    }

    #[test]
    fn temporal_sat_enforces_lasso_loop_equality() {
        let model = model_with_loop(2, 1);
        let active_at_one = RelTemporalFormula::Next(Box::new(atom(&model, "orders.active", 0)));
        let active_at_two = RelTemporalFormula::Next(Box::new(RelTemporalFormula::Next(Box::new(
            atom(&model, "orders.active", 0),
        ))));
        let formula =
            RelTemporalFormula::And(vec![active_at_two, RelTemporalFormula::not(active_at_one)]);

        let witness = solve_temporal_formula(&model, &formula).expect("solve");

        assert_eq!(witness, None);
    }

    #[test]
    fn temporal_sat_supports_until_and_release_over_bounded_lasso() {
        let model = model_with_loop(2, 1);
        let active = atom(&model, "orders.active", 0);
        let paid = atom(&model, "orders.paid", 1);
        let until = RelTemporalFormula::until(active.clone(), paid.clone());
        let release = RelTemporalFormula::release(active, paid);
        let formula = RelTemporalFormula::And(vec![until, release]);

        let witness = solve_temporal_formula(&model, &formula).expect("solve");

        assert!(witness.is_some());
    }

    #[test]
    fn temporal_sat_supports_boolean_and_always_forms() {
        let model = model_with_loop(1, 0);
        let active = atom(&model, "orders.active", 0);
        let formula = RelTemporalFormula::And(vec![
            RelTemporalFormula::True,
            RelTemporalFormula::Or(vec![
                RelTemporalFormula::False,
                RelTemporalFormula::always(active),
            ]),
        ]);

        let witness = solve_temporal_formula(&model, &formula).expect("solve");

        assert!(witness.is_some());
    }

    #[test]
    fn temporal_sat_rejects_atom_outside_relation_bounds() {
        let model = model_with_loop(1, 0);
        let bogus = RelTuple(vec![RelAtom::new("orders", "orders[9]")]);
        let formula = RelTemporalFormula::Atom(RelAtomPredicate::new("orders.active", bogus));

        let err = solve_temporal_formula(&model, &formula).expect_err("unsupported");

        let RelCoreError::Unsupported { reason } = err;
        assert!(reason.contains("is outside relation orders.active"));
    }

    #[test]
    fn temporal_sat_transition_updates_enable_eventual_relation_tuple() {
        let mut model = model_with_loop(2, 1);
        let active = tuple(&model, "orders.active", 0);
        require_tuple_at_step_zero(&mut model, "orders.active", active);
        let paid = atom(&model, "orders.paid", 1);
        let transition_system = fire_pay_transition(&model);

        let witness = solve_temporal_formula_with_transitions(
            &model,
            &RelTemporalFormula::eventually(paid),
            Some(&transition_system),
        )
        .expect("solve")
        .expect("satisfiable");

        assert!(witness.steps[1].true_tuples.iter().any(|true_tuple| {
            true_tuple.relation == "orders.paid"
                && true_tuple.tuple == tuple(&model, "orders.paid", 1)
        }));
    }

    #[test]
    fn temporal_sat_witness_reports_transitions_projection_and_json_shape() {
        let mut model = model_with_loop(2, 1);
        let active = tuple(&model, "orders.active", 0);
        require_tuple_at_step_zero(&mut model, "orders.active", active);
        let transition_system = fire_pay_transition(&model);

        let witness = solve_temporal_formula_with_transitions(
            &model,
            &RelTemporalFormula::eventually(atom(&model, "orders.paid", 1)),
            Some(&transition_system),
        )
        .expect("solve")
        .expect("satisfiable");

        assert!(witness
            .transitions
            .iter()
            .any(|transition| transition.transition == "pay"));

        let step_one = witness
            .projections
            .iter()
            .find(|projection| projection.step == 1)
            .expect("step one projection");
        let orders = step_one
            .stores
            .iter()
            .find(|store| store.store == "orders")
            .expect("orders projection");
        let slot_zero = orders
            .slots
            .iter()
            .find(|slot| slot.slot == "orders[0]")
            .expect("slot projection");
        assert!(slot_zero.active);
        assert!(slot_zero.fields.iter().any(|field| {
            field.field == "paid" && field.values.iter().any(|value| value == "true")
        }));

        let json = serde_json::to_value(&witness).expect("json witness");
        assert!(json.get("loop_start").is_some());
        assert!(json.get("steps").is_some());
        assert!(json.get("transitions").is_some());
        assert!(json.get("projections").is_some());
    }

    #[test]
    fn temporal_sat_transition_frame_preserves_unassigned_relation_tuples() {
        let mut model = model_with_loop(1, 0);
        let active = tuple(&model, "orders.active", 0);
        let open = tuple(&model, "orders.status", 0);
        require_tuple_at_step_zero(&mut model, "orders.active", active);
        require_tuple_at_step_zero(&mut model, "orders.status", open.clone());
        let transition_system = fire_pay_transition(&model);
        let formula = RelTemporalFormula::Next(Box::new(RelTemporalFormula::not(
            RelTemporalFormula::Atom(RelAtomPredicate::new("orders.status", open)),
        )));

        let witness =
            solve_temporal_formula_with_transitions(&model, &formula, Some(&transition_system))
                .expect("solve");

        assert_eq!(witness, None);
    }

    #[test]
    fn temporal_sat_rejects_deadlock_when_stutter_is_disabled() {
        let model = model_with_loop(1, 0);
        let transition_system = RelTemporalTransitionSystem {
            allow_stutter: false,
            transitions: vec![RelTemporalTransition {
                name: "blocked".to_owned(),
                guard: RelTemporalFormula::False,
                updates: Vec::new(),
            }],
        };

        let witness = solve_temporal_formula_with_transitions(
            &model,
            &RelTemporalFormula::True,
            Some(&transition_system),
        )
        .expect("solve");

        assert_eq!(witness, None);
    }

    #[test]
    fn temporal_sat_allows_stutter_when_enabled() {
        let mut model = model_with_loop(1, 0);
        let active = tuple(&model, "orders.active", 0);
        require_tuple_at_step_zero(&mut model, "orders.active", active);
        let transition_system = RelTemporalTransitionSystem {
            allow_stutter: true,
            transitions: Vec::new(),
        };

        let witness = solve_temporal_formula_with_transitions(
            &model,
            &RelTemporalFormula::always(atom(&model, "orders.active", 0)),
            Some(&transition_system),
        )
        .expect("solve");

        assert!(witness.is_some());
    }

    #[test]
    fn temporal_transition_system_from_verify_compiles_create_and_apply_steps() {
        let ir = program_with_system(payable_entity(), commerce_system());
        let verify = verify_for_system(2);
        let model = TemporalRelationalModel::from_verify(&ir, &verify).expect("model");
        let transition_system = transition_system_from_verify(&ir, &verify, &model)
            .expect("transition system")
            .expect("supported");

        assert_eq!(transition_system.transitions.len(), 4);
        assert!(transition_system.allow_stutter);
        assert!(transition_system
            .transitions
            .iter()
            .any(|transition| transition.name.starts_with("open:create")));
        assert!(transition_system
            .transitions
            .iter()
            .any(|transition| transition.name.starts_with("pay:pay")));

        let witness = solve_temporal_formula_with_transitions(
            &model,
            &RelTemporalFormula::eventually(atom(&model, "orders.paid", 1)),
            Some(&transition_system),
        )
        .expect("solve");

        assert!(witness.is_some());
    }

    #[test]
    fn temporal_transition_system_combines_multi_scope_same_step_updates() {
        let order = payable_entity();
        let payment = IREntity {
            name: "Payment".to_owned(),
            fields: vec![bool_field("captured")],
            transitions: vec![IRTransition {
                name: "capture".to_owned(),
                refs: Vec::new(),
                params: Vec::new(),
                guard: bool_expr(true),
                updates: vec![IRUpdate {
                    field: "captured".to_owned(),
                    value: bool_expr(true),
                }],
                postcondition: None,
            }],
            derived_fields: Vec::new(),
            invariants: Vec::new(),
            fsm_decls: Vec::new(),
        };
        let system = IRSystem {
            name: "Commerce".to_owned(),
            store_params: vec![
                crate::ir::types::IRStoreParam {
                    name: "orders".to_owned(),
                    entity_type: "Order".to_owned(),
                },
                crate::ir::types::IRStoreParam {
                    name: "payments".to_owned(),
                    entity_type: "Payment".to_owned(),
                },
            ],
            fields: Vec::new(),
            entities: vec!["Order".to_owned(), "Payment".to_owned()],
            commands: Vec::new(),
            actions: vec![IRSystemAction {
                name: "settle".to_owned(),
                params: Vec::new(),
                guard: bool_expr(true),
                body: vec![
                    IRAction::Choose {
                        var: "o".to_owned(),
                        entity: "Order".to_owned(),
                        filter: Box::new(bool_expr(true)),
                        ops: vec![IRAction::Apply {
                            target: "o".to_owned(),
                            transition: "pay".to_owned(),
                            refs: Vec::new(),
                            args: Vec::new(),
                        }],
                    },
                    IRAction::Choose {
                        var: "p".to_owned(),
                        entity: "Payment".to_owned(),
                        filter: Box::new(bool_expr(true)),
                        ops: vec![IRAction::Apply {
                            target: "p".to_owned(),
                            transition: "capture".to_owned(),
                            refs: Vec::new(),
                            args: Vec::new(),
                        }],
                    },
                ],
                return_expr: None,
            }],
            fsm_decls: Vec::new(),
            derived_fields: Vec::new(),
            invariants: Vec::new(),
            queries: Vec::new(),
            preds: Vec::new(),
            let_bindings: Vec::new(),
            procs: Vec::new(),
        };
        let ir = program_with_entities_system(vec![order, payment], system);
        let verify = IRVerify {
            stores: vec![
                IRStoreDecl {
                    name: "orders".to_owned(),
                    entity_type: "Order".to_owned(),
                    lo: 0,
                    hi: 1,
                },
                IRStoreDecl {
                    name: "payments".to_owned(),
                    entity_type: "Payment".to_owned(),
                    lo: 0,
                    hi: 1,
                },
            ],
            ..verify_for_system(1)
        };
        let model = TemporalRelationalModel::from_verify(&ir, &verify).expect("model");
        let transition_system = transition_system_from_verify(&ir, &verify, &model)
            .expect("transition system")
            .expect("supported");

        assert_eq!(transition_system.transitions.len(), 1);
        let transition = &transition_system.transitions[0];
        assert!(transition.name.contains("pay"));
        assert!(transition.name.contains("capture"));
        assert!(transition
            .updates
            .iter()
            .any(|update| update.relation == "orders.paid" && update.value));
        assert!(transition
            .updates
            .iter()
            .any(|update| update.relation == "payments.captured" && update.value));

        let formula = RelTemporalFormula::eventually(RelTemporalFormula::And(vec![
            atom(&model, "orders.paid", 1),
            atom(&model, "payments.captured", 1),
        ]));
        let witness =
            solve_temporal_formula_with_transitions(&model, &formula, Some(&transition_system))
                .expect("solve");
        assert!(witness.is_some());
    }

    #[test]
    fn temporal_sat_matches_native_initial_previously_semantics() {
        let model = model_with_loop(1, 0);
        let native = LassoWord::new(vec![vec![0]], vec![vec![0]]);
        assert!(!native.holds(&Formula::previously(Formula::atom(0)), 0));

        let witness = solve_temporal_formula(
            &model,
            &RelTemporalFormula::previously(atom(&model, "orders.active", 0)),
        )
        .expect("solve");

        assert_eq!(witness, None);
    }

    #[test]
    fn temporal_sat_matches_native_previously_after_next_semantics() {
        let mut model = model_with_loop(1, 0);
        let active = tuple(&model, "orders.active", 0);
        require_tuple_at_step_zero(&mut model, "orders.active", active);
        let native = LassoWord::new(vec![vec![0], vec![]], vec![vec![]]);
        assert!(native.holds(&Formula::next(Formula::previously(Formula::atom(0))), 0));

        let witness = solve_temporal_formula(
            &model,
            &RelTemporalFormula::Next(Box::new(RelTemporalFormula::previously(atom(
                &model,
                "orders.active",
                0,
            )))),
        )
        .expect("solve");

        assert!(witness.is_some());
    }

    #[test]
    fn temporal_sat_supports_once_historically_and_since() {
        let mut model = model_with_loop(2, 1);
        let active = tuple(&model, "orders.active", 0);
        require_tuple_at_step_zero(&mut model, "orders.active", active);

        let once = RelTemporalFormula::Next(Box::new(RelTemporalFormula::once(atom(
            &model,
            "orders.active",
            0,
        ))));
        let since = RelTemporalFormula::Next(Box::new(RelTemporalFormula::since(
            RelTemporalFormula::True,
            atom(&model, "orders.active", 0),
        )));

        assert!(solve_temporal_formula(&model, &once)
            .expect("solve")
            .is_some());
        assert!(solve_temporal_formula(&model, &since)
            .expect("solve")
            .is_some());

        let historically_conflict = RelTemporalFormula::And(vec![
            RelTemporalFormula::not(atom(&model, "orders.active", 0)),
            RelTemporalFormula::Next(Box::new(RelTemporalFormula::historically(atom(
                &model,
                "orders.active",
                0,
            )))),
        ]);
        assert_eq!(
            solve_temporal_formula(&model, &historically_conflict).expect("solve"),
            None
        );
    }
}
