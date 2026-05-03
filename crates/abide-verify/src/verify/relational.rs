//! Narrow RustSAT-backed bounded relational backend.
//!
//! This owns the first bounded relational product slices:
//! - create-only scene fragments
//! - narrow stateful scenes with given-bound entity selections
//! - bounded relational verify fragments over one pooled entity type with
//!   finite field domains and narrow create / choose-apply operational steps

use std::collections::HashMap;
use std::time::Instant;

use rustsat::instances::SatInstance;
use rustsat::solvers::{Solve, SolverResult};
use rustsat::types::constraints::CardConstraint;
use rustsat::types::TernaryVal;
use rustsat_batsat::BasicSolver;

use abide_witness::{rel, EntitySlotRef, WitnessValue};

use crate::ir::types::{
    Cardinality, IRAction, IREntity, IRExpr, IRProgram, IRScene, IRStoreDecl, IRSystemAction,
    IRType, IRVerify, LitVal,
};

use super::scene::collect_ordering_leaf_vars;
use super::{VerificationResult, WitnessSemantics};

const STATEFUL_SCENE_SOME_EVENT_BUDGET: usize = 3;
const STATEFUL_SCENE_MAX_TOTAL_EVENT_INSTANCES: usize = 6;

#[derive(Debug, Clone)]
struct CreateInstance {
    entity: String,
    fire: rustsat::types::Lit,
    assigns: Vec<rustsat::types::Lit>,
    positions: Vec<rustsat::types::Lit>,
    field_values: HashMap<String, SimpleValue>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum SimpleValue {
    Bool(bool),
    Int(i64),
    Ctor(String, String),
}

#[derive(Debug, Clone)]
enum RelPred {
    True,
    Eq {
        field: String,
        value: SimpleValue,
    },
    Cmp {
        field: String,
        op: RelCmpOp,
        value: SimpleValue,
    },
    And(Box<RelPred>, Box<RelPred>),
    Or(Box<RelPred>, Box<RelPred>),
    Not(Box<RelPred>),
}

#[derive(Debug, Clone)]
enum RelScopedPred {
    True,
    Eq {
        binding: String,
        field: String,
        value: SimpleValue,
    },
    Cmp {
        binding: String,
        field: String,
        op: RelCmpOp,
        value: SimpleValue,
    },
    EqBindings {
        left_binding: String,
        left_field: String,
        right_binding: String,
        right_field: String,
    },
    CmpBindings {
        left_binding: String,
        left_field: String,
        op: RelCmpOp,
        right_binding: String,
        right_field: String,
    },
    And(Box<RelScopedPred>, Box<RelScopedPred>),
    Or(Box<RelScopedPred>, Box<RelScopedPred>),
    Not(Box<RelScopedPred>),
}

#[derive(Debug, Clone, Copy)]
enum RelQuantifier {
    Exists,
    Forall,
}

#[derive(Debug, Clone)]
struct RelQuantBinding {
    quantifier: RelQuantifier,
    var: String,
    entity: String,
}

#[derive(Debug, Clone, Copy)]
enum RelCmpOp {
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Debug, Clone)]
enum RelSnapshotExpr {
    Bool(bool),
    Exists {
        entity: String,
        pred: RelPred,
    },
    Forall {
        entity: String,
        pred: RelPred,
    },
    ScopedQuantified {
        bindings: Vec<RelQuantBinding>,
        pred: RelScopedPred,
    },
    StoreExtentSubset {
        entity: String,
        left: RelStateRef,
        right: RelStateRef,
    },
    FieldRelationSubset {
        entity: String,
        field: String,
        left: RelStateRef,
        right: RelStateRef,
    },
    RelationSubset {
        left: RelValueExpr,
        right: RelValueExpr,
    },
    And(Box<RelSnapshotExpr>, Box<RelSnapshotExpr>),
    Or(Box<RelSnapshotExpr>, Box<RelSnapshotExpr>),
    Not(Box<RelSnapshotExpr>),
}

#[derive(Debug, Clone, Copy)]
enum RelStateRef {
    Current,
    Next,
}

#[derive(Debug, Clone)]
enum RelValueExpr {
    StoreExtent {
        entity: String,
        state_ref: RelStateRef,
    },
    Field {
        entity: String,
        field: String,
        state_ref: RelStateRef,
    },
    Comprehension {
        projection: Vec<RelProjection>,
        bindings: Vec<RelComprehensionBinding>,
        filter: RelScopedPred,
    },
    Join(Box<RelValueExpr>, Box<RelValueExpr>),
    Product(Box<RelValueExpr>, Box<RelValueExpr>),
    Project {
        expr: Box<RelValueExpr>,
        columns: Vec<usize>,
    },
    Union(Box<RelValueExpr>, Box<RelValueExpr>),
    Intersection(Box<RelValueExpr>, Box<RelValueExpr>),
    Difference(Box<RelValueExpr>, Box<RelValueExpr>),
    Transpose(Box<RelValueExpr>),
    Closure {
        expr: Box<RelValueExpr>,
        reflexive: bool,
    },
}

#[derive(Debug, Clone)]
struct RelComprehensionBinding {
    var: String,
    entity: String,
    source_ref: RelStateRef,
}

#[derive(Debug, Clone)]
enum RelProjection {
    Entity {
        binding: String,
        entity: String,
    },
    Field {
        binding: String,
        entity: String,
        field: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum RelAtomRef {
    EntitySlot { entity: String, slot: usize },
    Value(SimpleValue),
}

#[derive(Debug, Clone)]
struct RelActionBinding {
    name: String,
    entity: String,
    alias_of: Option<String>,
    predicate: RelScopedPred,
}

#[derive(Debug, Clone)]
enum RelationalActionSpec {
    Create {
        entity: String,
        field_values: HashMap<String, SimpleValue>,
    },
    Apply {
        entity: String,
        target_binding: String,
        binding_aliases: Vec<(String, String)>,
        bindings: Vec<RelActionBinding>,
        guard: RelScopedPred,
        updates: HashMap<String, SimpleValue>,
    },
}

#[derive(Debug, Clone)]
struct RelationalSystemStepSpec {
    actions: Vec<RelationalActionSpec>,
}

#[derive(Debug, Clone)]
struct RelationalEntitySpec {
    slot_count: usize,
    initial_lower_bound: usize,
    defaults: HashMap<String, SimpleValue>,
    field_domains: HashMap<String, Vec<SimpleValue>>,
}

#[derive(Debug, Clone)]
struct RelationalVerifySpec {
    entities: HashMap<String, RelationalEntitySpec>,
    steps: Vec<RelationalSystemStepSpec>,
    assertions: Vec<RelSnapshotExpr>,
}

#[derive(Debug, Clone)]
struct RelationalSceneGivenSpec {
    var: String,
    entity: String,
    predicate: RelPred,
}

#[derive(Debug, Clone)]
struct RelationalStatefulSceneSpec {
    entities: HashMap<String, RelationalEntitySpec>,
    givens: Vec<RelationalSceneGivenSpec>,
    step_schedules: Vec<Vec<RelationalSystemStepSpec>>,
    assertions: Vec<RelScopedPred>,
}

#[derive(Debug)]
struct FieldDomainEncoding {
    values: Vec<SimpleValue>,
    state_lits: Vec<Vec<Vec<rustsat::types::Lit>>>,
}

#[derive(Debug)]
struct EntityStateEncoding {
    slot_count: usize,
    active_by_state: Vec<Vec<rustsat::types::Lit>>,
    field_encodings: HashMap<String, FieldDomainEncoding>,
}

pub(super) fn try_check_scene_block_relational(
    ir: &IRProgram,
    scene: &IRScene,
) -> Option<VerificationResult> {
    let obligation = RelationalSceneObligation::build(ir, scene).ok()??;
    Some(obligation.solve())
}

#[derive(Debug)]
struct RelationalSceneObligation<'a> {
    scene: &'a IRScene,
    sat: SatInstance,
}

pub(super) enum RelationalVerifyOutcome {
    Checked {
        time_ms: u64,
    },
    Counterexample {
        witness: Option<rel::RelationalWitness>,
        witness_error: Option<String>,
    },
}

#[derive(Debug)]
struct RelationalVerifyObligation<'a> {
    verify: &'a IRVerify,
    sat: SatInstance,
    entity_states: HashMap<String, EntityStateEncoding>,
    bound: usize,
}

impl<'a> RelationalSceneObligation<'a> {
    fn build(ir: &'a IRProgram, scene: &'a IRScene) -> Result<Option<Self>, String> {
        if let Some(sat) = build_create_only_scene_sat(ir, scene)? {
            return Ok(Some(Self { scene, sat }));
        }
        if let Some(sat) = build_stateful_scene_sat(ir, scene)? {
            return Ok(Some(Self { scene, sat }));
        }
        Ok(None)
    }

    fn solve(self) -> VerificationResult {
        let start = Instant::now();
        let elapsed = || start.elapsed().as_millis().try_into().unwrap_or(u64::MAX);
        let (cnf, _) = self.sat.into_cnf();
        let mut solver = BasicSolver::default();
        if let Err(err) = solver.add_cnf(cnf) {
            return VerificationResult::SceneFail {
                name: self.scene.name.clone(),
                reason: format!("RustSAT setup failed: {err}"),
                span: None,
                file: None,
            };
        }
        match solver.solve() {
            Ok(SolverResult::Sat) => VerificationResult::ScenePass {
                name: self.scene.name.clone(),
                time_ms: elapsed(),
                evidence: None,
                span: None,
                file: None,
            },
            Ok(SolverResult::Unsat) => VerificationResult::SceneFail {
                name: self.scene.name.clone(),
                reason: crate::messages::SCENE_UNSATISFIABLE.to_owned(),
                span: None,
                file: None,
            },
            Ok(SolverResult::Interrupted) => VerificationResult::SceneFail {
                name: self.scene.name.clone(),
                reason: crate::messages::SCENE_UNKNOWN.to_owned(),
                span: None,
                file: None,
            },
            Err(err) => VerificationResult::SceneFail {
                name: self.scene.name.clone(),
                reason: format!("RustSAT solve failed: {err}"),
                span: None,
                file: None,
            },
        }
    }
}

fn build_create_only_scene_sat(
    ir: &IRProgram,
    scene: &IRScene,
) -> Result<Option<SatInstance>, String> {
    if !supports_create_only_scene_fragment(ir, scene)? {
        return Ok(None);
    }

    let mut sat = SatInstance::new();
    let entities_by_name: HashMap<_, _> = ir.entities.iter().map(|e| (e.name.clone(), e)).collect();
    let systems_by_name: HashMap<_, _> = ir.systems.iter().map(|s| (s.name.clone(), s)).collect();

    let store_slots = build_store_slots(scene);
    let mut create_instances = Vec::new();
    let some_budget = scene.events.len().max(2);
    let mut event_instance_ranges = Vec::with_capacity(scene.events.len());
    let horizon: usize = scene
        .events
        .iter()
        .map(|scene_event| cardinality_budget(&scene_event.cardinality, some_budget))
        .sum::<usize>()
        .max(1);

    for scene_event in &scene.events {
        let system = systems_by_name
            .get(&scene_event.system)
            .ok_or_else(|| format!("unknown system `{}`", scene_event.system))?;
        let step = system
            .actions
            .iter()
            .find(|step| step.name == scene_event.event)
            .ok_or_else(|| {
                format!(
                    "scene `{}` references unknown command `{}` on `{}`",
                    scene.name, scene_event.event, scene_event.system
                )
            })?;
        let (entity_name, field_values) = create_spec(step, &entities_by_name)?;
        let slot_count = store_slots.get(entity_name.as_str()).copied().unwrap_or(0);
        let potential_count = cardinality_budget(&scene_event.cardinality, some_budget);
        let mut fire_lits = Vec::new();
        let start_idx = create_instances.len();

        for _ in 0..potential_count {
            let fire = sat.new_lit();
            fire_lits.push(fire);
            let assigns: Vec<_> = (0..slot_count).map(|_| sat.new_lit()).collect();
            let positions: Vec<_> = (0..horizon).map(|_| sat.new_lit()).collect();

            for &assign in &assigns {
                sat.add_binary(!assign, fire);
            }
            for i in 0..assigns.len() {
                for j in (i + 1)..assigns.len() {
                    sat.add_binary(!assigns[i], !assigns[j]);
                }
            }
            if !assigns.is_empty() {
                let mut clause = vec![!fire];
                clause.extend(assigns.iter().copied());
                sat.add_clause(clause.as_slice().into());
            } else {
                sat.add_unit(!fire);
            }
            for &position in &positions {
                sat.add_binary(!position, fire);
            }
            for i in 0..positions.len() {
                for j in (i + 1)..positions.len() {
                    sat.add_binary(!positions[i], !positions[j]);
                }
            }
            let mut pos_clause = vec![!fire];
            pos_clause.extend(positions.iter().copied());
            sat.add_clause(pos_clause.as_slice().into());

            create_instances.push(CreateInstance {
                entity: entity_name.clone(),
                fire,
                assigns,
                positions,
                field_values: field_values.clone(),
            });
        }
        event_instance_ranges.push(start_idx..create_instances.len());

        add_cardinality_constraint(&mut sat, fire_lits, &scene_event.cardinality);
    }

    if !scene.ordering.is_empty() {
        let var_to_idx: HashMap<_, _> = scene
            .events
            .iter()
            .enumerate()
            .map(|(idx, event)| (event.var.as_str(), idx))
            .collect();
        for ordering in &scene.ordering {
            encode_relational_scene_ordering(
                &mut sat,
                ordering,
                &var_to_idx,
                &event_instance_ranges,
                &create_instances,
                scene,
            )?;
        }
    }

    for (entity_name, slot_count) in &store_slots {
        for slot in 0..*slot_count {
            let slot_assigns: Vec<_> = create_instances
                .iter()
                .filter(|inst| inst.entity == *entity_name)
                .filter_map(|inst| inst.assigns.get(slot).copied())
                .collect();
            for i in 0..slot_assigns.len() {
                for j in (i + 1)..slot_assigns.len() {
                    sat.add_binary(!slot_assigns[i], !slot_assigns[j]);
                }
            }
        }
    }

    for assertion in &scene.assertions {
        let clause = encode_assertion_into(assertion, &create_instances, &mut sat)?;
        sat.add_unit(clause);
    }

    Ok(Some(sat))
}

fn build_stateful_scene_sat(
    ir: &IRProgram,
    scene: &IRScene,
) -> Result<Option<SatInstance>, String> {
    let Some(spec) = relational_stateful_scene_spec(ir, scene)? else {
        return Ok(None);
    };
    let RelationalStatefulSceneSpec {
        entities,
        givens,
        step_schedules,
        assertions,
    } = spec;
    if step_schedules.is_empty() {
        return Ok(None);
    }

    let mut sat = SatInstance::new();
    let mut entity_states = HashMap::new();
    let all_steps: Vec<_> = step_schedules
        .iter()
        .flat_map(|schedule| schedule.iter().cloned())
        .collect();
    for (entity_name, entity_spec) in &entities {
        let active_by_state = vec![(0..entity_spec.slot_count)
            .map(|_| sat.new_lit())
            .collect::<Vec<_>>()];

        let mut field_domains = collect_field_domains(
            &entity_spec.defaults,
            &entity_spec.field_domains,
            &all_steps,
            &[],
            entity_name,
        );
        for given in &givens {
            if given.entity == *entity_name {
                collect_pred_values(&given.predicate, &mut field_domains);
            }
        }
        let binding_entities: HashMap<_, _> = givens
            .iter()
            .map(|given| (given.var.as_str(), given.entity.as_str()))
            .collect();
        for assertion in &assertions {
            collect_scoped_pred_values_for_entity(
                assertion,
                &binding_entities,
                &mut field_domains,
                entity_name,
            );
        }

        let field_encodings = build_field_encodings(
            &mut sat,
            &entity_spec.defaults,
            &field_domains,
            entity_spec.slot_count,
            0,
        )?;
        entity_states.insert(
            entity_name.clone(),
            EntityStateEncoding {
                slot_count: entity_spec.slot_count,
                active_by_state,
                field_encodings,
            },
        );
    }

    let mut binding_slots: HashMap<String, (String, Vec<rustsat::types::Lit>)> = HashMap::new();
    for given in &givens {
        let state = entity_states
            .get(&given.entity)
            .ok_or_else(|| format!("missing relational entity state for `{}`", given.entity))?;
        let slots: Vec<_> = (0..state.slot_count).map(|_| sat.new_lit()).collect();
        sat.add_card_constr(CardConstraint::new_eq(slots.clone(), 1));
        for (slot_idx, slot_lit) in slots.iter().enumerate() {
            sat.add_binary(!*slot_lit, state.active_by_state[0][slot_idx]);
            let pred_lit = encode_rel_pred_for_slot(
                &given.predicate,
                &state.field_encodings,
                0,
                slot_idx,
                &mut sat,
            )?;
            sat.add_binary(!*slot_lit, pred_lit);
        }
        binding_slots.insert(given.var.clone(), (given.entity.clone(), slots));
    }

    for (entity_name, state) in &entity_states {
        for slot_idx in 0..state.slot_count {
            let selectors: Vec<_> = binding_slots
                .values()
                .filter(|(entity, _)| entity == entity_name)
                .filter_map(|(_, slots)| slots.get(slot_idx).copied())
                .collect();
            let selected = or_lit(&mut sat, &selectors)?;
            let active = state.active_by_state[0][slot_idx];
            sat.add_binary(!active, selected);
            sat.add_binary(!selected, active);
        }
    }

    let schedule_selectors: Vec<_> = (0..step_schedules.len()).map(|_| sat.new_lit()).collect();
    sat.add_card_constr(CardConstraint::new_eq(schedule_selectors.clone(), 1));

    let base_active: HashMap<String, Vec<rustsat::types::Lit>> = entity_states
        .iter()
        .map(|(entity_name, state)| (entity_name.clone(), state.active_by_state[0].clone()))
        .collect();
    let base_fields: HashMap<String, HashMap<String, Vec<Vec<rustsat::types::Lit>>>> =
        entity_states
            .iter()
            .map(|(entity_name, state)| {
                (
                    entity_name.clone(),
                    state
                        .field_encodings
                        .iter()
                        .map(|(field_name, encoding)| {
                            (field_name.clone(), encoding.state_lits[0].clone())
                        })
                        .collect(),
                )
            })
            .collect();

    for (schedule_idx, steps) in step_schedules.iter().enumerate() {
        let mut current_active = base_active.clone();
        let mut current_fields = base_fields.clone();
        let step_fire = schedule_selectors[schedule_idx];
        for step in steps {
            for action in &step.actions {
                apply_relational_action(
                    &mut sat,
                    action,
                    step_fire,
                    &binding_slots,
                    &mut current_active,
                    &mut current_fields,
                    &entity_states,
                )?;
            }
        }
        let selector = schedule_selectors[schedule_idx];
        for assertion in &assertions {
            let clause = encode_scoped_pred_with_bindings(
                &mut sat,
                assertion,
                &binding_slots,
                &current_fields,
                &entity_states,
            )?;
            sat.add_binary(!selector, clause);
        }
    }

    Ok(Some(sat))
}

impl<'a> RelationalVerifyObligation<'a> {
    fn build(
        ir: &'a IRProgram,
        verify: &'a IRVerify,
        bound: usize,
        symmetry_breaking: bool,
    ) -> Result<Option<Self>, String> {
        let Some(spec) = relational_verify_spec(ir, verify)? else {
            return Ok(None);
        };
        let RelationalVerifySpec {
            entities,
            steps,
            assertions,
        } = spec;

        let mut sat = SatInstance::new();
        let mut entity_states = HashMap::new();
        for (entity_name, entity_spec) in &entities {
            let mut active_by_state = Vec::with_capacity(bound + 1);
            if entity_spec.initial_lower_bound == 0 {
                active_by_state.push(
                    (0..entity_spec.slot_count)
                        .map(|_| const_lit(&mut sat, false))
                        .collect::<Vec<_>>(),
                );
            } else {
                active_by_state.push(
                    (0..entity_spec.slot_count)
                        .map(|_| sat.new_lit())
                        .collect::<Vec<_>>(),
                );
                sat.add_card_constr(CardConstraint::new_lb(
                    active_by_state[0].clone(),
                    entity_spec.initial_lower_bound,
                ));
            }
            for _ in 0..bound {
                active_by_state.push(
                    (0..entity_spec.slot_count)
                        .map(|_| sat.new_lit())
                        .collect::<Vec<_>>(),
                );
            }
            let field_domains = collect_field_domains(
                &entity_spec.defaults,
                &entity_spec.field_domains,
                &steps,
                &assertions,
                entity_name,
            );
            let field_encodings = build_field_encodings(
                &mut sat,
                &entity_spec.defaults,
                &field_domains,
                entity_spec.slot_count,
                bound,
            )?;
            entity_states.insert(
                entity_name.clone(),
                EntityStateEncoding {
                    slot_count: entity_spec.slot_count,
                    active_by_state,
                    field_encodings,
                },
            );
        }

        if symmetry_breaking {
            add_active_prefix_symmetry_breaking(&mut sat, &entity_states);
        }

        for step_idx in 0..bound {
            let base_active: HashMap<String, Vec<rustsat::types::Lit>> = entity_states
                .iter()
                .map(|(entity_name, state)| {
                    (entity_name.clone(), state.active_by_state[step_idx].clone())
                })
                .collect();
            let base_fields: HashMap<String, HashMap<String, Vec<Vec<rustsat::types::Lit>>>> =
                entity_states
                    .iter()
                    .map(|(entity_name, state)| {
                        (
                            entity_name.clone(),
                            state
                                .field_encodings
                                .iter()
                                .map(|(field_name, encoding)| {
                                    (field_name.clone(), encoding.state_lits[step_idx].clone())
                                })
                                .collect(),
                        )
                    })
                    .collect();

            let mut branches = Vec::with_capacity(steps.len());
            let mut fire_lits = Vec::with_capacity(steps.len());
            for step in &steps {
                let step_fire = sat.new_lit();
                let mut branch_active = base_active.clone();
                let mut branch_fields = base_fields.clone();
                let fixed_bindings = HashMap::new();
                for action in &step.actions {
                    apply_relational_action(
                        &mut sat,
                        action,
                        step_fire,
                        &fixed_bindings,
                        &mut branch_active,
                        &mut branch_fields,
                        &entity_states,
                    )?;
                }
                fire_lits.push(step_fire);
                branches.push((step_fire, branch_active, branch_fields));
            }

            for i in 0..fire_lits.len() {
                for j in (i + 1)..fire_lits.len() {
                    sat.add_binary(!fire_lits[i], !fire_lits[j]);
                }
            }
            let no_fire_inputs: Vec<_> = fire_lits.iter().map(|lit| !*lit).collect();
            let no_fire = and_lit(&mut sat, &no_fire_inputs)?;
            if !verify.assumption_set.stutter && !fire_lits.is_empty() {
                sat.add_clause(fire_lits.as_slice().into());
            }

            for (entity_name, state) in &mut entity_states {
                for slot in 0..state.slot_count {
                    let next_lit = state.active_by_state[step_idx + 1][slot];
                    let mut reasons = vec![and_lit(
                        &mut sat,
                        &[no_fire, base_active[entity_name][slot]],
                    )?];
                    for (fire, branch_active, _) in &branches {
                        reasons.push(and_lit(
                            &mut sat,
                            &[*fire, branch_active[entity_name][slot]],
                        )?);
                    }
                    let source = or_lit(&mut sat, &reasons)?;
                    sat.add_binary(!next_lit, source);
                    sat.add_binary(!source, next_lit);
                }

                for (field_name, encoding) in &mut state.field_encodings {
                    for slot in 0..state.slot_count {
                        for value_idx in 0..encoding.values.len() {
                            let next_lit = encoding.state_lits[step_idx + 1][slot][value_idx];
                            let mut reasons = vec![and_lit(
                                &mut sat,
                                &[
                                    no_fire,
                                    base_fields[entity_name][field_name][slot][value_idx],
                                ],
                            )?];
                            for (fire, _, branch_fields) in &branches {
                                reasons.push(and_lit(
                                    &mut sat,
                                    &[
                                        *fire,
                                        branch_fields[entity_name][field_name][slot][value_idx],
                                    ],
                                )?);
                            }
                            let source = or_lit(&mut sat, &reasons)?;
                            sat.add_binary(!next_lit, source);
                            sat.add_binary(!source, next_lit);
                        }
                    }
                }
            }
        }

        let violation = encode_verify_violation_into(&assertions, &entity_states, &mut sat, bound)?;
        sat.add_unit(violation);

        Ok(Some(Self {
            verify,
            sat,
            entity_states,
            bound,
        }))
    }

    fn solve(self, witness_semantics: WitnessSemantics) -> RelationalVerifyOutcome {
        let Self {
            verify: _verify,
            sat,
            entity_states,
            bound,
        } = self;
        let start = Instant::now();
        let elapsed = || start.elapsed().as_millis().try_into().unwrap_or(u64::MAX);
        let (cnf, _) = sat.into_cnf();
        let mut solver = BasicSolver::default();
        if let Err(err) = solver.add_cnf(cnf) {
            return RelationalVerifyOutcome::Counterexample {
                witness: None,
                witness_error: Some(format!("RustSAT setup failed: {err}")),
            };
        }
        match solver.solve() {
            Ok(SolverResult::Unsat) => RelationalVerifyOutcome::Checked { time_ms: elapsed() },
            Ok(SolverResult::Sat) => {
                let witness = match witness_semantics {
                    WitnessSemantics::Relational => build_relational_verify_counterexample_witness(
                        &solver,
                        &entity_states,
                        bound,
                    )
                    .map(Some),
                    WitnessSemantics::Operational => Ok(None),
                };
                let (witness, witness_error) = match witness {
                    Ok(witness) => (witness, None),
                    Err(err) => (None, Some(err)),
                };
                RelationalVerifyOutcome::Counterexample {
                    witness,
                    witness_error,
                }
            }
            Ok(SolverResult::Interrupted) => RelationalVerifyOutcome::Counterexample {
                witness: None,
                witness_error: Some("RustSAT solve interrupted".to_owned()),
            },
            Err(err) => RelationalVerifyOutcome::Counterexample {
                witness: None,
                witness_error: Some(format!("RustSAT solve failed: {err}")),
            },
        }
    }
}

pub(super) fn try_check_verify_block_relational(
    ir: &IRProgram,
    verify: &IRVerify,
    bound: usize,
    witness_semantics: WitnessSemantics,
    symmetry_breaking: bool,
) -> Option<RelationalVerifyOutcome> {
    let obligation =
        RelationalVerifyObligation::build(ir, verify, bound, symmetry_breaking).ok()??;
    Some(obligation.solve(witness_semantics))
}

#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn supports_verify_fragment(ir: &IRProgram, verify: &IRVerify) -> Result<bool, String> {
    Ok(relational_verify_spec(ir, verify)?.is_some())
}

#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn supports_scene_fragment(ir: &IRProgram, scene: &IRScene) -> Result<bool, String> {
    Ok(supports_create_only_scene_fragment(ir, scene)?
        || relational_stateful_scene_spec(ir, scene)?.is_some())
}

fn supports_create_only_scene_fragment(ir: &IRProgram, scene: &IRScene) -> Result<bool, String> {
    if !scene.givens.is_empty()
        || !scene.given_constraints.is_empty()
        || !scene.activations.is_empty()
    {
        return Ok(false);
    }
    if scene.systems.len() != 1 {
        return Ok(false);
    }

    let system_name = &scene.systems[0];
    let Some(system) = ir.systems.iter().find(|sys| sys.name == *system_name) else {
        return Err(format!("unknown scene system `{system_name}`"));
    };
    if !system.let_bindings.is_empty() || system.entities.is_empty() {
        return Ok(false);
    }

    let entities_by_name: HashMap<_, _> = ir.entities.iter().map(|e| (e.name.clone(), e)).collect();
    for scene_event in &scene.events {
        if !scene_event.args.is_empty() || scene_event.system != *system_name {
            return Ok(false);
        }
        let Some(step) = system
            .actions
            .iter()
            .find(|step| step.name == scene_event.event)
        else {
            return Err(format!(
                "scene `{}` references unknown command `{}`",
                scene.name, scene_event.event
            ));
        };
        if !matches!(
            step.guard,
            IRExpr::Lit {
                value: LitVal::Bool { value: true },
                ..
            }
        ) {
            return Ok(false);
        }
        if step.body.len() != 1 {
            return Ok(false);
        }
        let body = &step.body;
        let params = &step.params;
        if !params.is_empty() {
            return Ok(false);
        }
        let crate::ir::types::IRAction::Create { entity, fields } = &body[0] else {
            return Ok(false);
        };
        let Some(entity_ir) = entities_by_name.get(entity.as_str()) else {
            return Err(format!("unknown entity `{entity}`"));
        };
        if build_field_value_map(entity_ir, fields)?.is_none() {
            return Ok(false);
        }
    }

    for assertion in &scene.assertions {
        if !supports_assertion_expr(assertion) {
            return Ok(false);
        }
    }

    Ok(true)
}

fn relational_stateful_scene_spec(
    ir: &IRProgram,
    scene: &IRScene,
) -> Result<Option<RelationalStatefulSceneSpec>, String> {
    if scene.systems.len() != 1
        || scene.givens.is_empty()
        || !scene.given_constraints.is_empty()
        || !scene.activations.is_empty()
    {
        return Ok(None);
    }
    let Some(event_stage_schedules) = scene_event_stage_schedules(scene) else {
        return Ok(None);
    };

    let system_name = &scene.systems[0];
    let Some(system) = ir.systems.iter().find(|sys| sys.name == *system_name) else {
        return Err(format!("unknown scene system `{system_name}`"));
    };
    if !system.let_bindings.is_empty() || !system.fields.is_empty() || system.entities.is_empty() {
        return Ok(None);
    }

    let entities_by_name: HashMap<_, _> = ir.entities.iter().map(|e| (e.name.clone(), e)).collect();
    let mut entities = HashMap::new();
    for store in &scene.stores {
        if store.lo > 0 || store.hi <= 0 {
            return Ok(None);
        }
        if !system
            .entities
            .iter()
            .any(|entity| entity == &store.entity_type)
        {
            return Ok(None);
        }
        if entities.contains_key(&store.entity_type) {
            return Ok(None);
        }
        let Some(entity_ir) = entities_by_name.get(&store.entity_type) else {
            return Err(format!("unknown entity `{}`", store.entity_type));
        };
        let Some(defaults) = build_scene_default_field_map(entity_ir)? else {
            return Ok(None);
        };
        entities.insert(
            store.entity_type.clone(),
            RelationalEntitySpec {
                slot_count: usize::try_from(store.hi.max(1)).unwrap_or(1),
                initial_lower_bound: 0,
                defaults,
                field_domains: finite_field_domains(entity_ir),
            },
        );
    }
    if entities.is_empty() {
        return Ok(None);
    }

    let mut givens = Vec::with_capacity(scene.givens.len());
    let mut binding_entities = Vec::with_capacity(scene.givens.len());
    for given in &scene.givens {
        let Some(entity_ir) = entities_by_name.get(&given.entity) else {
            return Err(format!("unknown entity `{}`", given.entity));
        };
        if !entities.contains_key(&given.entity) {
            return Ok(None);
        }
        if let Some(store_name) = &given.store_name {
            if !scene
                .stores
                .iter()
                .any(|store| store.name == *store_name && store.entity_type == given.entity)
            {
                return Ok(None);
            }
        }
        let Some(predicate) = parse_slot_predicate_expr(
            &given.constraint,
            Some(given.var.as_str()),
            Some(entity_ir),
            &HashMap::new(),
        )?
        else {
            return Ok(None);
        };
        binding_entities.push((given.var.as_str(), given.entity.as_str()));
        givens.push(RelationalSceneGivenSpec {
            var: given.var.clone(),
            entity: given.entity.clone(),
            predicate,
        });
    }

    let events_by_var: HashMap<_, _> = scene
        .events
        .iter()
        .map(|event| (event.var.as_str(), event))
        .collect();
    let given_binding_map: HashMap<_, _> = givens
        .iter()
        .map(|given| (given.var.as_str(), given.entity.as_str()))
        .collect();
    let mut step_schedules = Vec::with_capacity(event_stage_schedules.len());
    for event_stages in event_stage_schedules {
        let mut steps = Vec::with_capacity(event_stages.len());
        for stage in event_stages {
            let mut stage_actions = Vec::new();
            let mut stage_entities = HashMap::new();
            for event_var in stage {
                let Some(event) = events_by_var.get(event_var) else {
                    return Ok(None);
                };
                if event.system != *system_name
                    || !scene_event_has_small_stateful_cardinality(
                        event,
                        STATEFUL_SCENE_SOME_EVENT_BUDGET,
                    )
                {
                    return Ok(None);
                }
                let Some(step) = system.actions.iter().find(|step| step.name == event.event) else {
                    return Err(format!(
                        "scene `{}` references unknown command `{}`",
                        scene.name, event.event
                    ));
                };
                let Some(spec) = parse_relational_scene_step(
                    step,
                    &event.args,
                    &entities_by_name,
                    &entities,
                    &given_binding_map,
                )?
                else {
                    return Ok(None);
                };
                for action in spec.actions {
                    let entity = relational_action_entity(&action);
                    if stage_entities.insert(entity.to_owned(), ()).is_some() {
                        return Ok(None);
                    }
                    stage_actions.push(action);
                }
            }
            steps.push(RelationalSystemStepSpec {
                actions: stage_actions,
            });
        }
        step_schedules.push(steps);
    }

    let allowed_bindings: Vec<_> = binding_entities.iter().map(|(name, _)| *name).collect();
    let binding_entities_map: HashMap<_, _> = binding_entities.into_iter().collect();
    let mut assertions = Vec::with_capacity(scene.assertions.len());
    for assertion in &scene.assertions {
        let Some(pred) =
            parse_scoped_predicate_expr(assertion, None, None, &HashMap::new(), &allowed_bindings)?
        else {
            return Ok(None);
        };
        if !scene_assertion_mentions_only_givens(&pred, &binding_entities_map) {
            return Ok(None);
        }
        assertions.push(pred);
    }
    if assertions.is_empty() {
        return Ok(None);
    }

    Ok(Some(RelationalStatefulSceneSpec {
        entities,
        givens,
        step_schedules,
        assertions,
    }))
}

fn create_spec(
    step: &IRSystemAction,
    entities_by_name: &HashMap<String, &IREntity>,
) -> Result<(String, HashMap<String, SimpleValue>), String> {
    let crate::ir::types::IRAction::Create { entity, fields } = &step.body[0] else {
        return Err(format!("step `{}` is not create-only", step.name));
    };
    let Some(entity_ir) = entities_by_name.get(entity) else {
        return Err(format!("unknown entity `{entity}`"));
    };
    let Some(field_values) = build_field_value_map(entity_ir, fields)? else {
        return Err(format!(
            "unsupported create field values in `{}`",
            step.name
        ));
    };
    Ok((entity.clone(), field_values))
}

fn build_store_slots(scene: &IRScene) -> HashMap<String, usize> {
    let mut out = HashMap::new();
    for store in &scene.stores {
        let slots = usize::try_from(store.hi.max(1)).unwrap_or(1);
        let entry = out.entry(store.entity_type.clone()).or_insert(0);
        *entry += slots;
    }
    out
}

fn cardinality_budget(cardinality: &Cardinality, some_budget: usize) -> usize {
    match cardinality {
        Cardinality::Named(name) => match name.as_str() {
            "one" | "lone" => 1,
            "no" => 0,
            "some" => some_budget,
            _ => 1,
        },
        Cardinality::Exact { exactly } => usize::try_from(*exactly).unwrap_or(0),
    }
}

fn add_cardinality_constraint(
    sat: &mut SatInstance,
    lits: Vec<rustsat::types::Lit>,
    cardinality: &Cardinality,
) {
    match cardinality {
        Cardinality::Named(name) => match name.as_str() {
            "one" => sat.add_card_constr(CardConstraint::new_eq(lits, 1)),
            "lone" => sat.add_card_constr(CardConstraint::new_ub(lits, 1)),
            "no" => sat.add_card_constr(CardConstraint::new_eq(lits, 0)),
            "some" => sat.add_card_constr(CardConstraint::new_lb(lits, 1)),
            _ => sat.add_card_constr(CardConstraint::new_eq(lits, 1)),
        },
        Cardinality::Exact { exactly } => sat.add_card_constr(CardConstraint::new_eq(
            lits,
            usize::try_from(*exactly).unwrap_or(0),
        )),
    }
}

fn scene_event_stage_schedules(scene: &IRScene) -> Option<Vec<Vec<Vec<&str>>>> {
    if scene.ordering.is_empty() {
        if scene.events.is_empty()
            || scene.events.len() > 5
            || !scene.events.iter().all(|event| {
                scene_event_has_small_stateful_cardinality(event, STATEFUL_SCENE_SOME_EVENT_BUDGET)
            })
        {
            return None;
        }
        let vars: Vec<_> = scene
            .events
            .iter()
            .map(|event| event.var.as_str())
            .collect();
        let events_by_var: HashMap<_, _> = scene
            .events
            .iter()
            .map(|event| (event.var.as_str(), event))
            .collect();
        let mut expanded = Vec::new();
        let mut current = Vec::new();
        enumerate_scene_count_variants(
            &vars,
            &events_by_var,
            STATEFUL_SCENE_SOME_EVENT_BUDGET,
            STATEFUL_SCENE_MAX_TOTAL_EVENT_INSTANCES,
            0,
            &mut current,
            &mut expanded,
        );
        let mut out = Vec::new();
        for variant in expanded {
            let mut used = vec![false; variant.len()];
            let mut current_perm = Vec::new();
            let mut perms = Vec::new();
            permute_scene_event_vars(&variant, &mut used, &mut current_perm, &mut perms);
            perms.sort();
            perms.dedup();
            out.extend(
                perms
                    .into_iter()
                    .map(|vars| vars.into_iter().map(|var| vec![var]).collect()),
            );
        }
        return Some(out);
    }
    if scene.ordering.len() != 1 {
        return None;
    }
    let mut stages = Vec::new();
    if !collect_scene_event_stages(&scene.ordering[0], &mut stages) {
        return None;
    }
    let vars: Vec<_> = stages
        .iter()
        .flat_map(|stage| stage.iter().copied())
        .collect();
    if vars.len() != scene.events.len() {
        return None;
    }
    let event_vars: HashMap<_, _> = scene
        .events
        .iter()
        .map(|event| (event.var.as_str(), ()))
        .collect();
    let mut seen = HashMap::new();
    for var in &vars {
        if !event_vars.contains_key(var) || seen.insert(*var, ()).is_some() {
            return None;
        }
    }
    let events_by_var: HashMap<_, _> = scene
        .events
        .iter()
        .map(|event| (event.var.as_str(), event))
        .collect();
    expand_stage_count_options(
        &stages,
        &events_by_var,
        STATEFUL_SCENE_SOME_EVENT_BUDGET,
        STATEFUL_SCENE_MAX_TOTAL_EVENT_INSTANCES,
    )
}

fn permute_scene_event_vars<'a>(
    vars: &[&'a str],
    used: &mut [bool],
    current: &mut Vec<&'a str>,
    out: &mut Vec<Vec<&'a str>>,
) {
    if current.len() == vars.len() {
        out.push(current.clone());
        return;
    }
    for idx in 0..vars.len() {
        if used[idx] {
            continue;
        }
        used[idx] = true;
        current.push(vars[idx]);
        permute_scene_event_vars(vars, used, current, out);
        current.pop();
        used[idx] = false;
    }
}

fn scene_event_has_small_stateful_cardinality(
    event: &crate::ir::types::IRSceneEvent,
    some_budget: usize,
) -> bool {
    scene_event_count_options(event, some_budget).is_some()
}

fn scene_event_count_options(
    event: &crate::ir::types::IRSceneEvent,
    some_budget: usize,
) -> Option<Vec<usize>> {
    match &event.cardinality {
        Cardinality::Named(name) if name == "one" => Some(vec![1]),
        Cardinality::Named(name) if name == "lone" => Some(vec![0, 1]),
        Cardinality::Named(name) if name == "no" => Some(vec![0]),
        Cardinality::Named(name) if name == "some" => Some((1..=some_budget).collect()),
        Cardinality::Exact { exactly } => usize::try_from(*exactly)
            .ok()
            .filter(|count| *count <= some_budget)
            .map(|count| vec![count]),
        _ => None,
    }
}

fn enumerate_scene_count_variants<'a>(
    vars: &[&'a str],
    events_by_var: &HashMap<&'a str, &crate::ir::types::IRSceneEvent>,
    some_budget: usize,
    max_total_instances: usize,
    idx: usize,
    current: &mut Vec<&'a str>,
    out: &mut Vec<Vec<&'a str>>,
) {
    if idx == vars.len() {
        out.push(current.clone());
        return;
    }
    let var = vars[idx];
    let Some(event) = events_by_var.get(var) else {
        return;
    };
    let Some(options) = scene_event_count_options(event, some_budget) else {
        return;
    };
    for count in options {
        if current.len() + count > max_total_instances {
            continue;
        }
        for _ in 0..count {
            current.push(var);
        }
        enumerate_scene_count_variants(
            vars,
            events_by_var,
            some_budget,
            max_total_instances,
            idx + 1,
            current,
            out,
        );
        for _ in 0..count {
            current.pop();
        }
    }
}

fn expand_stage_count_options<'a>(
    stages: &[Vec<&'a str>],
    events_by_var: &HashMap<&'a str, &crate::ir::types::IRSceneEvent>,
    some_budget: usize,
    max_total_instances: usize,
) -> Option<Vec<Vec<Vec<&'a str>>>> {
    let mut all = Vec::new();
    let mut current = Vec::new();
    expand_stage_count_options_rec(
        stages,
        events_by_var,
        some_budget,
        max_total_instances,
        0,
        0,
        &mut current,
        &mut all,
    )?;
    Some(all)
}

fn expand_stage_count_options_rec<'a>(
    stages: &[Vec<&'a str>],
    events_by_var: &HashMap<&'a str, &crate::ir::types::IRSceneEvent>,
    some_budget: usize,
    max_total_instances: usize,
    idx: usize,
    total_instances: usize,
    current: &mut Vec<Vec<&'a str>>,
    out: &mut Vec<Vec<Vec<&'a str>>>,
) -> Option<()> {
    if idx == stages.len() {
        out.push(current.clone());
        return Some(());
    }
    let variants = expand_single_stage_count_options(
        &stages[idx],
        events_by_var,
        some_budget,
        max_total_instances,
    )?;
    for variant in variants {
        let added_instances: usize = variant.iter().map(Vec::len).sum();
        if total_instances + added_instances > max_total_instances {
            continue;
        }
        let pushed = variant.len();
        current.extend(variant.iter().cloned());
        expand_stage_count_options_rec(
            stages,
            events_by_var,
            some_budget,
            max_total_instances,
            idx + 1,
            total_instances + added_instances,
            current,
            out,
        )?;
        for _ in 0..pushed {
            current.pop();
        }
    }
    Some(())
}

fn expand_single_stage_count_options<'a>(
    stage: &[&'a str],
    events_by_var: &HashMap<&'a str, &crate::ir::types::IRSceneEvent>,
    some_budget: usize,
    max_total_instances: usize,
) -> Option<Vec<Vec<Vec<&'a str>>>> {
    let mut expanded = Vec::new();
    let mut current = Vec::new();
    enumerate_scene_count_variants(
        stage,
        events_by_var,
        some_budget,
        max_total_instances,
        0,
        &mut current,
        &mut expanded,
    );
    let mut out = Vec::new();
    for variant in expanded {
        if variant.is_empty() {
            out.push(Vec::new());
            continue;
        }
        if stage.len() == 1 {
            out.push(variant.into_iter().map(|var| vec![var]).collect());
            continue;
        }
        let mut seen = HashMap::new();
        for var in &variant {
            if seen.insert(*var, ()).is_some() {
                return None;
            }
        }
        out.push(vec![variant]);
    }
    Some(out)
}

fn collect_scene_event_stages<'a>(expr: &'a IRExpr, out: &mut Vec<Vec<&'a str>>) -> bool {
    match expr {
        IRExpr::Var { name, .. } => {
            out.push(vec![name.as_str()]);
            true
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpSeq" => {
            collect_scene_event_stages(left, out) && collect_scene_event_stages(right, out)
        }
        IRExpr::BinOp { op, .. } if op == "OpSameStep" => {
            let mut stage = Vec::new();
            if !collect_same_step_vars(expr, &mut stage) {
                return false;
            }
            out.push(stage);
            true
        }
        _ => false,
    }
}

fn collect_same_step_vars<'a>(expr: &'a IRExpr, out: &mut Vec<&'a str>) -> bool {
    match expr {
        IRExpr::Var { name, .. } => {
            out.push(name.as_str());
            true
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpSameStep" => {
            collect_same_step_vars(left, out) && collect_same_step_vars(right, out)
        }
        _ => false,
    }
}

fn relational_action_entity(action: &RelationalActionSpec) -> &str {
    match action {
        RelationalActionSpec::Create { entity, .. }
        | RelationalActionSpec::Apply { entity, .. } => entity,
    }
}

fn scene_assertion_mentions_only_givens(
    pred: &RelScopedPred,
    binding_entities: &HashMap<&str, &str>,
) -> bool {
    match pred {
        RelScopedPred::True => true,
        RelScopedPred::Eq { binding, .. } => binding_entities.contains_key(binding.as_str()),
        RelScopedPred::Cmp { binding, .. } => binding_entities.contains_key(binding.as_str()),
        RelScopedPred::EqBindings {
            left_binding,
            right_binding,
            ..
        } => {
            binding_entities.contains_key(left_binding.as_str())
                && binding_entities.contains_key(right_binding.as_str())
        }
        RelScopedPred::CmpBindings {
            left_binding,
            right_binding,
            ..
        } => {
            binding_entities.contains_key(left_binding.as_str())
                && binding_entities.contains_key(right_binding.as_str())
        }
        RelScopedPred::And(left, right) | RelScopedPred::Or(left, right) => {
            scene_assertion_mentions_only_givens(left, binding_entities)
                && scene_assertion_mentions_only_givens(right, binding_entities)
        }
        RelScopedPred::Not(inner) => scene_assertion_mentions_only_givens(inner, binding_entities),
    }
}

fn encode_relational_scene_ordering(
    sat: &mut SatInstance,
    expr: &IRExpr,
    var_to_idx: &HashMap<&str, usize>,
    event_instance_ranges: &[std::ops::Range<usize>],
    instances: &[CreateInstance],
    scene: &IRScene,
) -> Result<(), String> {
    match expr {
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpSeq" => {
            constrain_scene_ordering_pairs(
                sat,
                collect_ordering_leaf_vars(left),
                collect_ordering_leaf_vars(right),
                var_to_idx,
                event_instance_ranges,
                instances,
                scene,
                add_position_before_constraint,
            )?;
            encode_relational_scene_ordering(
                sat,
                left,
                var_to_idx,
                event_instance_ranges,
                instances,
                scene,
            )?;
            encode_relational_scene_ordering(
                sat,
                right,
                var_to_idx,
                event_instance_ranges,
                instances,
                scene,
            )?;
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpSameStep" => {
            constrain_scene_ordering_pairs(
                sat,
                collect_ordering_leaf_vars(left),
                collect_ordering_leaf_vars(right),
                var_to_idx,
                event_instance_ranges,
                instances,
                scene,
                add_position_equal_constraint,
            )?;
            encode_relational_scene_ordering(
                sat,
                left,
                var_to_idx,
                event_instance_ranges,
                instances,
                scene,
            )?;
            encode_relational_scene_ordering(
                sat,
                right,
                var_to_idx,
                event_instance_ranges,
                instances,
                scene,
            )?;
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpXor" => {
            constrain_scene_ordering_pairs(
                sat,
                collect_ordering_leaf_vars(left),
                collect_ordering_leaf_vars(right),
                var_to_idx,
                event_instance_ranges,
                instances,
                scene,
                |sat, left, right| sat.add_binary(!left.fire, !right.fire),
            )?;
            encode_relational_scene_ordering(
                sat,
                left,
                var_to_idx,
                event_instance_ranges,
                instances,
                scene,
            )?;
            encode_relational_scene_ordering(
                sat,
                right,
                var_to_idx,
                event_instance_ranges,
                instances,
                scene,
            )?;
        }
        _ => {}
    }
    Ok(())
}

fn constrain_scene_ordering_pairs<F>(
    sat: &mut SatInstance,
    left_vars: Vec<&str>,
    right_vars: Vec<&str>,
    var_to_idx: &HashMap<&str, usize>,
    event_instance_ranges: &[std::ops::Range<usize>],
    instances: &[CreateInstance],
    scene: &IRScene,
    mut constraint: F,
) -> Result<(), String>
where
    F: FnMut(&mut SatInstance, &CreateInstance, &CreateInstance),
{
    if left_vars.is_empty() || right_vars.is_empty() {
        return Err(format!(
            "scene `{}`: ordering expression references unknown event variable",
            scene.name
        ));
    }
    for left_var in left_vars {
        let Some(&left_idx) = var_to_idx.get(left_var) else {
            return Err(format!(
                "scene `{}`: unknown ordering event `{left_var}`",
                scene.name
            ));
        };
        for right_var in &right_vars {
            let Some(&right_idx) = var_to_idx.get(right_var) else {
                return Err(format!(
                    "scene `{}`: unknown ordering event `{right_var}`",
                    scene.name
                ));
            };
            for left_inst in &instances[event_instance_ranges[left_idx].clone()] {
                for right_inst in &instances[event_instance_ranges[right_idx].clone()] {
                    constraint(sat, left_inst, right_inst);
                }
            }
        }
    }
    Ok(())
}

fn add_position_before_constraint(
    sat: &mut SatInstance,
    left: &CreateInstance,
    right: &CreateInstance,
) {
    for (left_pos, &left_lit) in left.positions.iter().enumerate() {
        for (right_pos, &right_lit) in right.positions.iter().enumerate() {
            if left_pos >= right_pos {
                sat.add_clause([!left.fire, !right.fire, !left_lit, !right_lit].into());
            }
        }
    }
}

fn add_position_equal_constraint(
    sat: &mut SatInstance,
    left: &CreateInstance,
    right: &CreateInstance,
) {
    for (left_pos, &left_lit) in left.positions.iter().enumerate() {
        for (right_pos, &right_lit) in right.positions.iter().enumerate() {
            if left_pos != right_pos {
                sat.add_clause([!left.fire, !right.fire, !left_lit, !right_lit].into());
            }
        }
    }
}

fn build_field_value_map(
    entity: &IREntity,
    fields: &[crate::ir::types::IRCreateField],
) -> Result<Option<HashMap<String, SimpleValue>>, String> {
    let mut out = HashMap::new();
    for field in &entity.fields {
        if let Some(default) = &field.default {
            let Some(value) = simple_value(default) else {
                return Ok(None);
            };
            out.insert(field.name.clone(), value);
        }
    }
    for field in fields {
        let Some(value) = simple_value(&field.value) else {
            return Ok(None);
        };
        out.insert(field.name.clone(), value);
    }
    Ok(Some(out))
}

fn simple_value(expr: &IRExpr) -> Option<SimpleValue> {
    simple_value_with_params(expr, &HashMap::new())
}

fn simple_value_with_params(
    expr: &IRExpr,
    params: &HashMap<String, SimpleValue>,
) -> Option<SimpleValue> {
    match expr {
        IRExpr::Lit {
            value: LitVal::Bool { value },
            ..
        } => Some(SimpleValue::Bool(*value)),
        IRExpr::Lit {
            value: LitVal::Int { value },
            ..
        } => Some(SimpleValue::Int(*value)),
        IRExpr::Ctor {
            enum_name,
            ctor,
            args,
            ..
        } if args.is_empty() => Some(SimpleValue::Ctor(enum_name.clone(), ctor.clone())),
        IRExpr::Var { name, .. } => params.get(name).cloned(),
        _ => None,
    }
}

fn supports_assertion_expr(expr: &IRExpr) -> bool {
    match expr {
        IRExpr::Exists { body, .. } | IRExpr::Forall { body, .. } => supports_slot_predicate(body),
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpAnd" || op == "OpOr" => {
            supports_assertion_expr(left) && supports_assertion_expr(right)
        }
        IRExpr::Lit {
            value: LitVal::Bool { .. },
            ..
        } => true,
        _ => false,
    }
}

fn supports_slot_predicate(expr: &IRExpr) -> bool {
    match expr {
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpAnd" || op == "OpOr" => {
            supports_slot_predicate(left) && supports_slot_predicate(right)
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpEq" => match (&**left, &**right) {
            (IRExpr::Field { expr, .. }, IRExpr::Ctor { args, .. }) => {
                matches!(&**expr, IRExpr::Var { .. }) && args.is_empty()
            }
            (IRExpr::Field { expr, .. }, IRExpr::Lit { .. }) => {
                matches!(&**expr, IRExpr::Var { .. })
            }
            _ => false,
        },
        _ => false,
    }
}

fn encode_assertion_into(
    expr: &IRExpr,
    instances: &[CreateInstance],
    sat: &mut SatInstance,
) -> Result<rustsat::types::Lit, String> {
    match expr {
        IRExpr::Lit {
            value: LitVal::Bool { value },
            ..
        } => {
            let lit = sat.new_lit();
            sat.add_unit(if *value { lit } else { !lit });
            Ok(lit)
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpAnd" || op == "OpOr" => {
            let left_lit = encode_assertion_into(left, instances, sat)?;
            let right_lit = encode_assertion_into(right, instances, sat)?;
            let out = sat.new_lit();
            if op == "OpAnd" {
                sat.add_binary(!out, left_lit);
                sat.add_binary(!out, right_lit);
                sat.add_clause([out, !left_lit, !right_lit].into());
            } else {
                sat.add_binary(!left_lit, out);
                sat.add_binary(!right_lit, out);
                sat.add_clause([!out, left_lit, right_lit].into());
            }
            Ok(out)
        }
        IRExpr::Exists {
            var, domain, body, ..
        } => {
            let entity_name = match domain {
                IRType::Entity { name } => name.clone(),
                _ => return Err("unsupported existential domain in relational scene".to_owned()),
            };
            let entity_name_ref = entity_name.as_str();
            let matches: Vec<_> = instances
                .iter()
                .flat_map(|inst| {
                    inst.assigns.iter().copied().filter(|_| {
                        inst.entity == entity_name_ref
                            && slot_predicate_matches(body, var, &inst.field_values)
                    })
                })
                .collect();
            let out = sat.new_lit();
            if matches.is_empty() {
                sat.add_unit(!out);
            } else {
                for matched in &matches {
                    sat.add_binary(!*matched, out);
                }
                let mut clause = vec![!out];
                clause.extend(matches);
                sat.add_clause(clause.as_slice().into());
            }
            Ok(out)
        }
        IRExpr::Forall {
            var, domain, body, ..
        } => {
            let entity_name = match domain {
                IRType::Entity { name } => name.clone(),
                _ => return Err("unsupported universal domain in relational scene".to_owned()),
            };
            let entity_name_ref = entity_name.as_str();
            let mut clauses = Vec::new();
            for inst in instances {
                if inst.entity != entity_name_ref {
                    continue;
                }
                for assign in inst.assigns.iter().copied() {
                    clauses.push(if slot_predicate_matches(body, var, &inst.field_values) {
                        const_lit(sat, true)
                    } else {
                        !assign
                    });
                }
            }
            and_lit(sat, &clauses)
        }
        _ => Err("unsupported relational scene assertion".to_owned()),
    }
}

fn relational_verify_spec(
    ir: &IRProgram,
    verify: &IRVerify,
) -> Result<Option<RelationalVerifySpec>, String> {
    if verify.assumption_set.has_fair_events() {
        return Ok(None);
    }
    if verify.systems.len() != 1 || verify.stores.is_empty() {
        return Ok(None);
    }

    let system_name = &verify.systems[0].name;
    let Some(system) = ir.systems.iter().find(|sys| sys.name == *system_name) else {
        return Err(format!("unknown verify system `{system_name}`"));
    };
    if !system.let_bindings.is_empty() || !system.fields.is_empty() || system.entities.is_empty() {
        return Ok(None);
    }
    let entities_by_name: HashMap<_, _> = ir.entities.iter().map(|e| (e.name.clone(), e)).collect();
    let mut entities = HashMap::new();
    for store in &verify.stores {
        if store.hi <= 0 || store.lo > store.hi || entities.contains_key(&store.entity_type) {
            return Ok(None);
        }
        if !system
            .entities
            .iter()
            .any(|entity| entity == &store.entity_type)
        {
            return Ok(None);
        }
        let Some(entity_ir) = entities_by_name.get(&store.entity_type) else {
            return Err(format!("unknown entity `{}`", store.entity_type));
        };
        let Some(defaults) = build_default_field_map(entity_ir)? else {
            return Ok(None);
        };
        entities.insert(
            store.entity_type.clone(),
            RelationalEntitySpec {
                slot_count: usize::try_from(store.hi.max(1)).unwrap_or(1),
                initial_lower_bound: usize::try_from(store.lo).unwrap_or(0),
                defaults,
                field_domains: finite_field_domains(entity_ir),
            },
        );
    }

    let mut steps = Vec::with_capacity(system.actions.len());
    for step in &system.actions {
        let Some(spec) = parse_relational_step(step, &entities_by_name, &entities)? else {
            return Ok(None);
        };
        steps.push(spec);
    }
    let entity_names: Vec<_> = entities.keys().cloned().collect();
    let mut assertions = Vec::with_capacity(verify.asserts.len());
    for assertion in &verify.asserts {
        let Some(snapshot) = parse_verify_assertion(assertion, &entity_names, &verify.stores)?
        else {
            return Ok(None);
        };
        assertions.push(snapshot);
    }
    if assertions.is_empty() {
        return Ok(None);
    }

    Ok(Some(RelationalVerifySpec {
        entities,
        steps,
        assertions,
    }))
}

fn build_default_field_map(
    entity: &IREntity,
) -> Result<Option<HashMap<String, SimpleValue>>, String> {
    let mut out = HashMap::new();
    for field in &entity.fields {
        if let Some(default) = &field.default {
            let Some(value) = simple_value(default) else {
                return Ok(None);
            };
            out.insert(field.name.clone(), value);
        }
    }
    Ok(Some(out))
}

fn finite_field_domains(entity: &IREntity) -> HashMap<String, Vec<SimpleValue>> {
    let mut out = HashMap::new();
    for field in &entity.fields {
        let Some(values) = finite_type_values(&field.ty) else {
            continue;
        };
        out.insert(field.name.clone(), values);
    }
    out
}

fn finite_type_values(ty: &IRType) -> Option<Vec<SimpleValue>> {
    match ty {
        IRType::Bool => Some(vec![SimpleValue::Bool(false), SimpleValue::Bool(true)]),
        IRType::Enum { name, variants } => Some(
            variants
                .iter()
                .map(|variant| SimpleValue::Ctor(name.clone(), variant.name.clone()))
                .collect(),
        ),
        _ => None,
    }
}

fn build_scene_default_field_map(
    entity: &IREntity,
) -> Result<Option<HashMap<String, SimpleValue>>, String> {
    let mut out = HashMap::new();
    for field in &entity.fields {
        match (&field.ty, &field.default) {
            (IRType::Identity, None) => {}
            (_, Some(default)) => {
                let Some(value) = simple_value(default) else {
                    return Ok(None);
                };
                out.insert(field.name.clone(), value);
            }
            _ => return Ok(None),
        }
    }
    Ok(Some(out))
}

fn parse_relational_step(
    step: &IRSystemAction,
    entities_by_name: &HashMap<String, &IREntity>,
    entity_specs: &HashMap<String, RelationalEntitySpec>,
) -> Result<Option<RelationalSystemStepSpec>, String> {
    if !matches!(
        step.guard,
        IRExpr::Lit {
            value: LitVal::Bool { value: true },
            ..
        }
    ) {
        return Ok(None);
    }
    if !step.params.is_empty() || step.body.is_empty() {
        return Ok(None);
    }

    let mut actions = Vec::with_capacity(step.body.len());
    for action in &step.body {
        let Some(spec) = parse_relational_action(action, entities_by_name, entity_specs)? else {
            return Ok(None);
        };
        actions.push(spec);
    }
    Ok(Some(RelationalSystemStepSpec { actions }))
}

fn parse_relational_scene_step(
    step: &IRSystemAction,
    args: &[IRExpr],
    entities_by_name: &HashMap<String, &IREntity>,
    entity_specs: &HashMap<String, RelationalEntitySpec>,
    given_bindings: &HashMap<&str, &str>,
) -> Result<Option<RelationalSystemStepSpec>, String> {
    if args.is_empty() {
        return parse_relational_step(step, entities_by_name, entity_specs);
    }
    if !matches!(
        step.guard,
        IRExpr::Lit {
            value: LitVal::Bool { value: true },
            ..
        }
    ) || step.body.len() != 1
        || step.params.len() != args.len()
    {
        return Ok(None);
    }

    let mut param_binding_map = HashMap::new();
    let mut param_values = HashMap::new();
    for (param, arg) in step.params.iter().zip(args) {
        if matches!(param.ty, IRType::Identity) {
            let Some(binding) = parse_scene_identity_arg_binding(arg, given_bindings) else {
                return Ok(None);
            };
            param_binding_map.insert(param.name.as_str(), binding);
        } else {
            let Some(value) = simple_value(arg) else {
                return Ok(None);
            };
            param_values.insert(param.name.clone(), value);
        }
    }

    let Some(action) = parse_relational_scene_action_with_bindings(
        &step.body[0],
        entities_by_name,
        entity_specs,
        given_bindings,
        &param_binding_map,
        &param_values,
        Vec::new(),
        None,
    )?
    else {
        return Ok(None);
    };

    Ok(Some(RelationalSystemStepSpec {
        actions: vec![action],
    }))
}

fn parse_relational_scene_action_with_bindings(
    action: &IRAction,
    entities_by_name: &HashMap<String, &IREntity>,
    entity_specs: &HashMap<String, RelationalEntitySpec>,
    given_bindings: &HashMap<&str, &str>,
    param_binding_map: &HashMap<&str, &str>,
    param_values: &HashMap<String, SimpleValue>,
    bindings: Vec<RelActionBinding>,
    target_context: Option<(String, String, String)>,
) -> Result<Option<RelationalActionSpec>, String> {
    match action {
        IRAction::Choose {
            var,
            entity,
            filter,
            ops,
        } if ops.len() == 1 && entity_specs.contains_key(entity) => {
            let available_binding_names: Vec<String> = bindings
                .iter()
                .map(|binding| binding.name.clone())
                .chain(given_bindings.keys().map(|name| (*name).to_owned()))
                .collect();
            let available_bindings: Vec<_> =
                available_binding_names.iter().map(String::as_str).collect();
            let current_target_context = if target_context.is_none() {
                let Some(target_binding) =
                    extract_scene_target_binding(filter, var.as_str(), param_binding_map)
                else {
                    return Ok(None);
                };
                Some((entity.clone(), target_binding.to_owned(), var.clone()))
            } else {
                target_context
            };

            let is_target_choose = current_target_context
                .as_ref()
                .is_some_and(|(_, _, target_var)| target_var == var);

            let mut next_bindings = bindings;
            if is_target_choose {
                let filter_pred = parse_scene_target_filter_predicate(
                    filter,
                    var.as_str(),
                    param_binding_map,
                    param_values,
                )?;
                if let Some(filter_pred) = filter_pred {
                    let (_, target_binding, _) = current_target_context
                        .as_ref()
                        .expect("target context must exist for target choose");
                    next_bindings.push(RelActionBinding {
                        name: target_binding.clone(),
                        entity: entity.clone(),
                        alias_of: None,
                        predicate: rel_pred_to_scoped(target_binding, filter_pred),
                    });
                }
            } else {
                let Some((alias_of, filter_pred)) = parse_scene_binding_filter_predicate(
                    filter,
                    var.as_str(),
                    param_binding_map,
                    &available_bindings,
                    param_values,
                )?
                else {
                    return Ok(None);
                };
                next_bindings.push(RelActionBinding {
                    name: var.clone(),
                    entity: entity.clone(),
                    alias_of,
                    predicate: filter_pred,
                });
            }

            parse_relational_scene_action_with_bindings(
                &ops[0],
                entities_by_name,
                entity_specs,
                given_bindings,
                param_binding_map,
                param_values,
                next_bindings,
                current_target_context,
            )
        }
        IRAction::Apply {
            target,
            transition,
            refs,
            args,
        } => {
            let Some((target_entity, target_binding, target_var)) = target_context else {
                return Ok(None);
            };
            if target != &target_var {
                return Ok(None);
            }
            let Some(entity_ir) = entities_by_name.get(&target_entity) else {
                return Err(format!("unknown entity `{target_entity}`"));
            };
            let Some(transition_ir) = entity_ir
                .transitions
                .iter()
                .find(|candidate| candidate.name == *transition)
            else {
                return Err(format!(
                    "unknown transition `{transition}` on `{}`",
                    entity_ir.name
                ));
            };
            if transition_ir.postcondition.is_some()
                || transition_ir.refs.len() != refs.len()
                || transition_ir.params.len() != args.len()
            {
                return Ok(None);
            }

            let mut binding_aliases = Vec::new();
            for (expected_ref, actual_ref) in transition_ir.refs.iter().zip(refs) {
                if let Some(bound_ref) = bindings.iter().find(|binding| binding.name == *actual_ref)
                {
                    if bound_ref.entity != expected_ref.entity || expected_ref.name != *actual_ref {
                        return Ok(None);
                    }
                    continue;
                }
                let Some(source_binding) = param_binding_map.get(actual_ref.as_str()) else {
                    return Ok(None);
                };
                if expected_ref.name != *actual_ref {
                    return Ok(None);
                }
                let Some(source_entity) = given_bindings.get(*source_binding) else {
                    return Ok(None);
                };
                if *source_entity != expected_ref.entity.as_str() {
                    return Ok(None);
                }
                binding_aliases.push((actual_ref.clone(), (*source_binding).to_owned()));
            }

            let mut transition_param_values = HashMap::new();
            for (param, arg) in transition_ir.params.iter().zip(args) {
                let Some(value) = simple_value_with_params(arg, param_values) else {
                    return Ok(None);
                };
                transition_param_values.insert(param.name.clone(), value);
            }
            let mut allowed_bindings: Vec<_> = binding_aliases
                .iter()
                .map(|(alias, _)| alias.as_str())
                .collect();
            allowed_bindings.extend(bindings.iter().map(|binding| binding.name.as_str()));
            let transition_pred = parse_scoped_predicate_expr(
                &transition_ir.guard,
                Some(target.as_str()),
                Some(entity_ir),
                &transition_param_values,
                &allowed_bindings,
            )?;

            let mut updates = HashMap::new();
            for update in &transition_ir.updates {
                let Some(value) = simple_value_with_params(&update.value, &transition_param_values)
                else {
                    return Ok(None);
                };
                updates.insert(update.field.clone(), value);
            }
            if updates.is_empty() {
                return Ok(None);
            }

            let bindings: Vec<_> = bindings
                .into_iter()
                .filter(|binding| binding.name != target_binding)
                .collect();

            Ok(Some(RelationalActionSpec::Apply {
                entity: target_entity,
                target_binding,
                binding_aliases,
                bindings,
                guard: transition_pred.unwrap_or(RelScopedPred::True),
                updates,
            }))
        }
        _ => Ok(None),
    }
}

fn parse_relational_action(
    action: &IRAction,
    entities_by_name: &HashMap<String, &IREntity>,
    entity_specs: &HashMap<String, RelationalEntitySpec>,
) -> Result<Option<RelationalActionSpec>, String> {
    parse_relational_action_with_bindings(action, entities_by_name, entity_specs, Vec::new())
}

fn parse_relational_action_with_bindings(
    action: &IRAction,
    entities_by_name: &HashMap<String, &IREntity>,
    entity_specs: &HashMap<String, RelationalEntitySpec>,
    bindings: Vec<RelActionBinding>,
) -> Result<Option<RelationalActionSpec>, String> {
    match action {
        IRAction::Create { entity, fields } => {
            if !bindings.is_empty() {
                return Ok(None);
            }
            if !entity_specs.contains_key(entity) {
                return Ok(None);
            }
            let Some(entity_ir) = entities_by_name.get(entity) else {
                return Err(format!("unknown entity `{entity}`"));
            };
            let Some(field_values) = build_field_value_map(entity_ir, fields)? else {
                return Ok(None);
            };
            Ok(Some(RelationalActionSpec::Create {
                entity: entity.clone(),
                field_values,
            }))
        }
        IRAction::Choose {
            var,
            entity,
            filter,
            ops,
        } if ops.len() == 1 && entity_specs.contains_key(entity) => {
            let allowed_bindings: Vec<_> = bindings
                .iter()
                .map(|binding| binding.name.as_str())
                .collect();
            let Some(filter_pred) = parse_scoped_predicate_expr(
                filter,
                Some(var.as_str()),
                None,
                &HashMap::new(),
                &allowed_bindings,
            )?
            else {
                return Ok(None);
            };
            let mut next_bindings = bindings;
            next_bindings.push(RelActionBinding {
                name: var.clone(),
                entity: entity.clone(),
                alias_of: None,
                predicate: filter_pred,
            });
            parse_relational_action_with_bindings(
                &ops[0],
                entities_by_name,
                entity_specs,
                next_bindings,
            )
        }
        IRAction::Apply {
            target,
            transition,
            refs,
            args,
        } => {
            let Some(target_binding) = bindings.iter().find(|binding| binding.name == *target)
            else {
                return Ok(None);
            };
            let Some(entity_ir) = entities_by_name.get(&target_binding.entity) else {
                return Err(format!("unknown entity `{}`", target_binding.entity));
            };
            let Some(transition_ir) = entity_ir
                .transitions
                .iter()
                .find(|candidate| candidate.name == *transition)
            else {
                return Err(format!(
                    "unknown transition `{transition}` on `{}`",
                    entity_ir.name
                ));
            };
            if transition_ir.postcondition.is_some()
                || transition_ir.params.len() != args.len()
                || transition_ir.refs.len() != refs.len()
            {
                return Ok(None);
            }
            for (expected_ref, actual_ref) in transition_ir.refs.iter().zip(refs) {
                let Some(bound_ref) = bindings.iter().find(|binding| binding.name == *actual_ref)
                else {
                    return Ok(None);
                };
                if bound_ref.entity != expected_ref.entity || expected_ref.name != *actual_ref {
                    return Ok(None);
                }
            }
            let mut param_values = HashMap::new();
            for (param, arg) in transition_ir.params.iter().zip(args) {
                let Some(value) = simple_value_with_params(arg, &HashMap::new()) else {
                    return Ok(None);
                };
                param_values.insert(param.name.clone(), value);
            }
            let allowed_bindings: Vec<_> = bindings
                .iter()
                .map(|binding| binding.name.as_str())
                .collect();
            let Some(guard) = parse_scoped_predicate_expr(
                &transition_ir.guard,
                Some(target.as_str()),
                Some(entity_ir),
                &param_values,
                &allowed_bindings,
            )?
            else {
                return Ok(None);
            };
            let mut updates = HashMap::new();
            for update in &transition_ir.updates {
                let Some(value) = simple_value_with_params(&update.value, &param_values) else {
                    return Ok(None);
                };
                updates.insert(update.field.clone(), value);
            }
            if updates.is_empty() {
                return Ok(None);
            }
            Ok(Some(RelationalActionSpec::Apply {
                entity: target_binding.entity.clone(),
                target_binding: target.clone(),
                binding_aliases: Vec::new(),
                bindings,
                guard,
                updates,
            }))
        }
        _ => Ok(None),
    }
}

fn parse_scoped_predicate_expr(
    expr: &IRExpr,
    implicit_binding: Option<&str>,
    entity_ir: Option<&IREntity>,
    param_values: &HashMap<String, SimpleValue>,
    allowed_bindings: &[&str],
) -> Result<Option<RelScopedPred>, String> {
    match expr {
        IRExpr::Lit {
            value: LitVal::Bool { value: true },
            ..
        } => Ok(Some(RelScopedPred::True)),
        IRExpr::Lit {
            value: LitVal::Bool { value: false },
            ..
        } => Ok(Some(RelScopedPred::Not(Box::new(RelScopedPred::True)))),
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpAnd" || op == "OpOr" || op == "OpImplies" => {
            let Some(left) = parse_scoped_predicate_expr(
                left,
                implicit_binding,
                entity_ir,
                param_values,
                allowed_bindings,
            )?
            else {
                return Ok(None);
            };
            let Some(right) = parse_scoped_predicate_expr(
                right,
                implicit_binding,
                entity_ir,
                param_values,
                allowed_bindings,
            )?
            else {
                return Ok(None);
            };
            Ok(Some(match op.as_str() {
                "OpAnd" => RelScopedPred::And(Box::new(left), Box::new(right)),
                "OpOr" => RelScopedPred::Or(Box::new(left), Box::new(right)),
                "OpImplies" => RelScopedPred::Or(
                    Box::new(RelScopedPred::Not(Box::new(left))),
                    Box::new(right),
                ),
                _ => unreachable!(),
            }))
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => {
            let Some(inner) = parse_scoped_predicate_expr(
                operand,
                implicit_binding,
                entity_ir,
                param_values,
                allowed_bindings,
            )?
            else {
                return Ok(None);
            };
            Ok(Some(RelScopedPred::Not(Box::new(inner))))
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpEq" || op == "OpNEq" => {
            if let Some((left_binding, left_field)) =
                parse_scoped_field_operand(left, implicit_binding, entity_ir, allowed_bindings)
            {
                if let Some((right_binding, right_field)) =
                    parse_scoped_field_operand(right, implicit_binding, entity_ir, allowed_bindings)
                {
                    let eq = RelScopedPred::EqBindings {
                        left_binding,
                        left_field,
                        right_binding,
                        right_field,
                    };
                    return Ok(Some(if op == "OpNEq" {
                        RelScopedPred::Not(Box::new(eq))
                    } else {
                        eq
                    }));
                }
            }
            if let Some((binding, field)) =
                parse_scoped_field_operand(left, implicit_binding, entity_ir, allowed_bindings)
            {
                if let Some(value) = simple_value_with_params(right, param_values) {
                    let eq = RelScopedPred::Eq {
                        binding,
                        field,
                        value,
                    };
                    return Ok(Some(if op == "OpNEq" {
                        RelScopedPred::Not(Box::new(eq))
                    } else {
                        eq
                    }));
                }
            }
            if let Some((binding, field)) =
                parse_scoped_field_operand(right, implicit_binding, entity_ir, allowed_bindings)
            {
                if let Some(value) = simple_value_with_params(left, param_values) {
                    let eq = RelScopedPred::Eq {
                        binding,
                        field,
                        value,
                    };
                    return Ok(Some(if op == "OpNEq" {
                        RelScopedPred::Not(Box::new(eq))
                    } else {
                        eq
                    }));
                }
            }
            Ok(None)
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if matches!(op.as_str(), "OpLt" | "OpLe" | "OpGt" | "OpGe") => {
            let cmp_op = match op.as_str() {
                "OpLt" => RelCmpOp::Lt,
                "OpLe" => RelCmpOp::Le,
                "OpGt" => RelCmpOp::Gt,
                "OpGe" => RelCmpOp::Ge,
                _ => unreachable!(),
            };
            if let Some((left_binding, left_field)) =
                parse_scoped_field_operand(left, implicit_binding, entity_ir, allowed_bindings)
            {
                if let Some((right_binding, right_field)) =
                    parse_scoped_field_operand(right, implicit_binding, entity_ir, allowed_bindings)
                {
                    return Ok(Some(RelScopedPred::CmpBindings {
                        left_binding,
                        left_field,
                        op: cmp_op,
                        right_binding,
                        right_field,
                    }));
                }
            }
            if let Some((binding, field)) =
                parse_scoped_field_operand(left, implicit_binding, entity_ir, allowed_bindings)
            {
                if let Some(value) = simple_value_with_params(right, param_values) {
                    return Ok(Some(RelScopedPred::Cmp {
                        binding,
                        field,
                        op: cmp_op,
                        value,
                    }));
                }
            }
            if let Some((binding, field)) =
                parse_scoped_field_operand(right, implicit_binding, entity_ir, allowed_bindings)
            {
                if let Some(value) = simple_value_with_params(left, param_values) {
                    let flipped = match cmp_op {
                        RelCmpOp::Lt => RelCmpOp::Gt,
                        RelCmpOp::Le => RelCmpOp::Ge,
                        RelCmpOp::Gt => RelCmpOp::Lt,
                        RelCmpOp::Ge => RelCmpOp::Le,
                    };
                    return Ok(Some(RelScopedPred::Cmp {
                        binding,
                        field,
                        op: flipped,
                        value,
                    }));
                }
            }
            Ok(None)
        }
        IRExpr::Var { .. } | IRExpr::Field { .. } => {
            let Some((binding, field)) =
                parse_scoped_field_operand(expr, implicit_binding, entity_ir, allowed_bindings)
            else {
                return Ok(None);
            };
            Ok(Some(RelScopedPred::Eq {
                binding,
                field,
                value: SimpleValue::Bool(true),
            }))
        }
        _ => Ok(None),
    }
}

fn parse_scene_identity_arg_binding<'a>(
    expr: &'a IRExpr,
    given_bindings: &HashMap<&'a str, &'a str>,
) -> Option<&'a str> {
    match expr {
        IRExpr::Field { expr, field, .. } if field == "id" => {
            let IRExpr::Var { name, .. } = &**expr else {
                return None;
            };
            given_bindings
                .get(name.as_str())
                .copied()
                .map(|_| name.as_str())
        }
        _ => None,
    }
}

fn extract_scene_target_binding<'a>(
    expr: &'a IRExpr,
    slot_var: &str,
    param_binding_map: &HashMap<&'a str, &'a str>,
) -> Option<&'a str> {
    let mut binding = None;
    for term in scene_filter_terms(expr) {
        if let Some(found) = parse_scene_identity_filter_term(term, slot_var, param_binding_map) {
            if binding.is_some() && binding != Some(found) {
                return None;
            }
            binding = Some(found);
        }
    }
    binding
}

fn parse_scene_target_filter_predicate(
    expr: &IRExpr,
    slot_var: &str,
    param_binding_map: &HashMap<&str, &str>,
    param_values: &HashMap<String, SimpleValue>,
) -> Result<Option<RelPred>, String> {
    let mut preds = Vec::new();
    for term in scene_filter_terms(expr) {
        if parse_scene_identity_filter_term(term, slot_var, param_binding_map).is_some() {
            continue;
        }
        let Some(pred) = parse_slot_predicate_expr(term, Some(slot_var), None, param_values)?
        else {
            return Ok(None);
        };
        preds.push(pred);
    }
    Ok(preds
        .into_iter()
        .reduce(|left, right| RelPred::And(Box::new(left), Box::new(right))))
}

fn parse_scene_binding_filter_predicate(
    expr: &IRExpr,
    slot_var: &str,
    param_binding_map: &HashMap<&str, &str>,
    available_bindings: &[&str],
    param_values: &HashMap<String, SimpleValue>,
) -> Result<Option<(Option<String>, RelScopedPred)>, String> {
    let mut alias_of: Option<String> = None;
    let mut preds = Vec::new();
    for term in scene_filter_terms(expr) {
        if let Some(found) =
            parse_scene_binding_alias_term(term, slot_var, param_binding_map, available_bindings)
        {
            if alias_of
                .as_deref()
                .is_some_and(|existing| existing != found)
            {
                return Ok(None);
            }
            alias_of = Some(found.to_owned());
            continue;
        }
        let Some(pred) = parse_scoped_predicate_expr(
            term,
            Some(slot_var),
            None,
            param_values,
            available_bindings,
        )?
        else {
            return Ok(None);
        };
        preds.push(pred);
    }
    let predicate = preds
        .into_iter()
        .reduce(|left, right| RelScopedPred::And(Box::new(left), Box::new(right)))
        .unwrap_or(RelScopedPred::True);
    Ok(Some((alias_of, predicate)))
}

fn scene_filter_terms<'a>(expr: &'a IRExpr) -> Vec<&'a IRExpr> {
    let mut out = Vec::new();
    collect_scene_filter_terms(expr, &mut out);
    out
}

fn collect_scene_filter_terms<'a>(expr: &'a IRExpr, out: &mut Vec<&'a IRExpr>) {
    match expr {
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpAnd" => {
            collect_scene_filter_terms(left, out);
            collect_scene_filter_terms(right, out);
        }
        _ => out.push(expr),
    }
}

fn parse_scene_identity_filter_term<'a>(
    expr: &'a IRExpr,
    slot_var: &str,
    param_binding_map: &HashMap<&'a str, &'a str>,
) -> Option<&'a str> {
    let IRExpr::BinOp {
        op, left, right, ..
    } = expr
    else {
        return None;
    };
    if op != "OpEq" {
        return None;
    }
    parse_scene_identity_eq_side(left, right, slot_var, param_binding_map)
        .or_else(|| parse_scene_identity_eq_side(right, left, slot_var, param_binding_map))
}

fn parse_scene_binding_alias_term<'a>(
    expr: &'a IRExpr,
    slot_var: &str,
    param_binding_map: &HashMap<&'a str, &'a str>,
    available_bindings: &[&'a str],
) -> Option<&'a str> {
    let IRExpr::BinOp {
        op, left, right, ..
    } = expr
    else {
        return None;
    };
    if op != "OpEq" {
        return None;
    }
    parse_scene_binding_alias_side(left, right, slot_var, param_binding_map, available_bindings)
        .or_else(|| {
            parse_scene_binding_alias_side(
                right,
                left,
                slot_var,
                param_binding_map,
                available_bindings,
            )
        })
}

fn parse_scene_binding_alias_side<'a>(
    lhs: &'a IRExpr,
    rhs: &'a IRExpr,
    slot_var: &str,
    param_binding_map: &HashMap<&'a str, &'a str>,
    available_bindings: &[&'a str],
) -> Option<&'a str> {
    let IRExpr::Field { expr, field, .. } = lhs else {
        return None;
    };
    if field != "id" {
        return None;
    }
    let IRExpr::Var { name, .. } = &**expr else {
        return None;
    };
    if name != slot_var {
        return None;
    }
    match rhs {
        IRExpr::Var { name, .. } => param_binding_map.get(name.as_str()).copied().or_else(|| {
            available_bindings
                .contains(&name.as_str())
                .then_some(name.as_str())
        }),
        IRExpr::Field { expr, field, .. } if field == "id" => {
            let IRExpr::Var { name, .. } = &**expr else {
                return None;
            };
            available_bindings
                .contains(&name.as_str())
                .then_some(name.as_str())
        }
        _ => None,
    }
}

fn parse_scene_identity_eq_side<'a>(
    lhs: &'a IRExpr,
    rhs: &'a IRExpr,
    slot_var: &str,
    param_binding_map: &HashMap<&'a str, &'a str>,
) -> Option<&'a str> {
    let IRExpr::Field { expr, field, .. } = lhs else {
        return None;
    };
    if field != "id" {
        return None;
    }
    let IRExpr::Var { name, .. } = &**expr else {
        return None;
    };
    if name != slot_var {
        return None;
    }
    let IRExpr::Var { name, .. } = rhs else {
        return None;
    };
    param_binding_map.get(name.as_str()).copied()
}

fn rel_pred_to_scoped(binding: &str, pred: RelPred) -> RelScopedPred {
    match pred {
        RelPred::True => RelScopedPred::True,
        RelPred::Eq { field, value } => RelScopedPred::Eq {
            binding: binding.to_owned(),
            field,
            value,
        },
        RelPred::Cmp { field, op, value } => RelScopedPred::Cmp {
            binding: binding.to_owned(),
            field,
            op,
            value,
        },
        RelPred::And(left, right) => RelScopedPred::And(
            Box::new(rel_pred_to_scoped(binding, *left)),
            Box::new(rel_pred_to_scoped(binding, *right)),
        ),
        RelPred::Or(left, right) => RelScopedPred::Or(
            Box::new(rel_pred_to_scoped(binding, *left)),
            Box::new(rel_pred_to_scoped(binding, *right)),
        ),
        RelPred::Not(inner) => RelScopedPred::Not(Box::new(rel_pred_to_scoped(binding, *inner))),
    }
}

fn parse_scoped_field_operand(
    expr: &IRExpr,
    implicit_binding: Option<&str>,
    entity_ir: Option<&IREntity>,
    allowed_bindings: &[&str],
) -> Option<(String, String)> {
    match expr {
        IRExpr::Field { expr, field, .. } => {
            let IRExpr::Var { name, .. } = &**expr else {
                return None;
            };
            if allowed_bindings.contains(&name.as_str()) || implicit_binding == Some(name.as_str())
            {
                Some((name.clone(), field.clone()))
            } else {
                None
            }
        }
        IRExpr::Var { name, .. } => entity_ir
            .and_then(|entity| entity.fields.iter().find(|field| field.name == *name))
            .and_then(|_| implicit_binding.map(|binding| (binding.to_owned(), name.clone()))),
        _ => None,
    }
}

fn parse_verify_assertion(
    expr: &IRExpr,
    entity_names: &[String],
    stores: &[IRStoreDecl],
) -> Result<Option<RelSnapshotExpr>, String> {
    let IRExpr::Always { body, .. } = expr else {
        return Ok(None);
    };
    parse_snapshot_expr(body, entity_names, stores)
}

fn parse_snapshot_expr(
    expr: &IRExpr,
    entity_names: &[String],
    stores: &[IRStoreDecl],
) -> Result<Option<RelSnapshotExpr>, String> {
    match expr {
        IRExpr::Lit {
            value: LitVal::Bool { value },
            ..
        } => Ok(Some(RelSnapshotExpr::Bool(*value))),
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpAnd" || op == "OpOr" || op == "OpImplies" => {
            let Some(left) = parse_snapshot_expr(left, entity_names, stores)? else {
                return Ok(None);
            };
            let Some(right) = parse_snapshot_expr(right, entity_names, stores)? else {
                return Ok(None);
            };
            Ok(Some(match op.as_str() {
                "OpAnd" => RelSnapshotExpr::And(Box::new(left), Box::new(right)),
                "OpOr" => RelSnapshotExpr::Or(Box::new(left), Box::new(right)),
                "OpImplies" => RelSnapshotExpr::Or(
                    Box::new(RelSnapshotExpr::Not(Box::new(left))),
                    Box::new(right),
                ),
                _ => unreachable!(),
            }))
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => {
            let Some(inner) = parse_snapshot_expr(operand, entity_names, stores)? else {
                return Ok(None);
            };
            Ok(Some(RelSnapshotExpr::Not(Box::new(inner))))
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpSetSubset" || op == "OpLe" => {
            if let Some((entity, left, right)) = parse_store_extent_subset(left, right, stores) {
                return Ok(Some(RelSnapshotExpr::StoreExtentSubset {
                    entity,
                    left,
                    right,
                }));
            }
            if let Some((entity, field, left, right)) =
                parse_field_relation_subset(left, right, stores)
            {
                return Ok(Some(RelSnapshotExpr::FieldRelationSubset {
                    entity,
                    field,
                    left,
                    right,
                }));
            }
            if let (Some(left_expr), Some(right_expr)) = (
                parse_relation_value_expr(left, stores)?,
                parse_relation_value_expr(right, stores)?,
            ) {
                return Ok(Some(RelSnapshotExpr::RelationSubset {
                    left: left_expr,
                    right: right_expr,
                }));
            }
            Ok(None)
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpEq" => {
            if let Some((entity, field, left_ref, right_ref)) =
                parse_field_relation_subset(left, right, stores)
            {
                return Ok(Some(RelSnapshotExpr::And(
                    Box::new(RelSnapshotExpr::FieldRelationSubset {
                        entity: entity.clone(),
                        field: field.clone(),
                        left: left_ref,
                        right: right_ref,
                    }),
                    Box::new(RelSnapshotExpr::FieldRelationSubset {
                        entity,
                        field,
                        left: right_ref,
                        right: left_ref,
                    }),
                )));
            }
            if let (Some(left_expr), Some(right_expr)) = (
                parse_relation_value_expr(left, stores)?,
                parse_relation_value_expr(right, stores)?,
            ) {
                return Ok(Some(RelSnapshotExpr::And(
                    Box::new(RelSnapshotExpr::RelationSubset {
                        left: left_expr.clone(),
                        right: right_expr.clone(),
                    }),
                    Box::new(RelSnapshotExpr::RelationSubset {
                        left: right_expr,
                        right: left_expr,
                    }),
                )));
            }
            Ok(None)
        }
        IRExpr::Exists { .. } => parse_snapshot_quantifier_chain(expr, entity_names),
        IRExpr::Forall { .. } => parse_snapshot_quantifier_chain(expr, entity_names),
        _ => Ok(None),
    }
}

fn parse_store_extent_subset(
    left: &IRExpr,
    right: &IRExpr,
    stores: &[IRStoreDecl],
) -> Option<(String, RelStateRef, RelStateRef)> {
    let (left_name, left_ref) = parse_store_extent_ref(left)?;
    let (right_name, right_ref) = parse_store_extent_ref(right)?;
    if left_name != right_name {
        return None;
    }
    stores
        .iter()
        .find(|store| store.name == left_name)
        .map(|store| (store.entity_type.clone(), left_ref, right_ref))
}

fn parse_relation_value_expr(
    expr: &IRExpr,
    stores: &[IRStoreDecl],
) -> Result<Option<RelValueExpr>, String> {
    if let Some((store_name, field, state_ref)) = parse_field_relation_ref(expr) {
        let Some(store) = stores.iter().find(|store| store.name == store_name) else {
            return Ok(None);
        };
        return Ok(Some(RelValueExpr::Field {
            entity: store.entity_type.clone(),
            field: field.to_owned(),
            state_ref,
        }));
    }
    if let Some((store_name, state_ref)) = parse_store_extent_ref(expr) {
        let Some(store) = stores.iter().find(|store| store.name == store_name) else {
            return Ok(None);
        };
        return Ok(Some(RelValueExpr::StoreExtent {
            entity: store.entity_type.clone(),
            state_ref,
        }));
    }

    match expr {
        IRExpr::RelComp {
            projection,
            bindings,
            filter,
            ..
        } => {
            let mut parsed_bindings = Vec::with_capacity(bindings.len());
            let mut binding_entities = HashMap::new();
            for binding in bindings {
                let IRType::Entity { name: entity } = &binding.domain else {
                    return Ok(None);
                };
                let Some(source) = &binding.source else {
                    return Ok(None);
                };
                let Some((store_name, source_ref)) = parse_store_extent_ref(source) else {
                    return Ok(None);
                };
                let Some(store) = stores.iter().find(|store| store.name == store_name) else {
                    return Ok(None);
                };
                if store.entity_type != *entity {
                    return Ok(None);
                }
                parsed_bindings.push(RelComprehensionBinding {
                    var: binding.var.clone(),
                    entity: entity.clone(),
                    source_ref,
                });
                binding_entities.insert(binding.var.clone(), entity.clone());
            }
            let allowed_bindings = parsed_bindings
                .iter()
                .map(|binding| binding.var.as_str())
                .collect::<Vec<_>>();
            let Some(filter) = parse_scoped_predicate_expr(
                filter,
                None,
                None,
                &HashMap::new(),
                &allowed_bindings,
            )?
            else {
                return Ok(None);
            };
            let Some(projection) =
                parse_relation_projection(projection, &binding_entities, &allowed_bindings)
            else {
                return Ok(None);
            };
            Ok(Some(RelValueExpr::Comprehension {
                projection,
                bindings: parsed_bindings,
                filter,
            }))
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpRelJoin" || op == "OpRelationJoin" => {
            let Some(left) = parse_relation_value_expr(left, stores)? else {
                return Ok(None);
            };
            let Some(right) = parse_relation_value_expr(right, stores)? else {
                return Ok(None);
            };
            Ok(Some(RelValueExpr::Join(Box::new(left), Box::new(right))))
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpRelProduct" || op == "OpRelationProduct" => {
            let Some(left) = parse_relation_value_expr(left, stores)? else {
                return Ok(None);
            };
            let Some(right) = parse_relation_value_expr(right, stores)? else {
                return Ok(None);
            };
            Ok(Some(RelValueExpr::Product(Box::new(left), Box::new(right))))
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpRelProject" || op == "OpRelationProject" => {
            let Some(expr) = parse_relation_value_expr(left, stores)? else {
                return Ok(None);
            };
            let Some(columns) = parse_relation_project_columns(right) else {
                return Ok(None);
            };
            Ok(Some(RelValueExpr::Project {
                expr: Box::new(expr),
                columns,
            }))
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if matches!(op.as_str(), "OpSetUnion" | "OpSetIntersect" | "OpSetDiff") => {
            let Some(left) = parse_relation_value_expr(left, stores)? else {
                return Ok(None);
            };
            let Some(right) = parse_relation_value_expr(right, stores)? else {
                return Ok(None);
            };
            Ok(Some(match op.as_str() {
                "OpSetUnion" => RelValueExpr::Union(Box::new(left), Box::new(right)),
                "OpSetIntersect" => RelValueExpr::Intersection(Box::new(left), Box::new(right)),
                "OpSetDiff" => RelValueExpr::Difference(Box::new(left), Box::new(right)),
                _ => unreachable!(),
            }))
        }
        IRExpr::UnOp { op, operand, .. }
            if op == "OpRelTranspose" || op == "OpRelationTranspose" =>
        {
            let Some(operand) = parse_relation_value_expr(operand, stores)? else {
                return Ok(None);
            };
            Ok(Some(RelValueExpr::Transpose(Box::new(operand))))
        }
        IRExpr::UnOp { op, operand, .. }
            if matches!(
                op.as_str(),
                "OpRelClosure" | "OpRelationClosure" | "OpRelReach" | "OpRelationReach"
            ) =>
        {
            let Some(operand) = parse_relation_value_expr(operand, stores)? else {
                return Ok(None);
            };
            Ok(Some(RelValueExpr::Closure {
                expr: Box::new(operand),
                reflexive: matches!(op.as_str(), "OpRelReach" | "OpRelationReach"),
            }))
        }
        _ => Ok(None),
    }
}

fn parse_relation_project_columns(expr: &IRExpr) -> Option<Vec<usize>> {
    let mut columns = Vec::new();
    collect_relation_project_columns(expr, &mut columns)?;
    (!columns.is_empty()).then_some(columns)
}

fn collect_relation_project_columns(expr: &IRExpr, out: &mut Vec<usize>) -> Option<()> {
    match expr {
        IRExpr::Lit {
            value: LitVal::Int { value },
            ..
        } if *value >= 0 => {
            out.push((*value).try_into().ok()?);
            Some(())
        }
        IRExpr::App { func, arg, .. } if is_relation_tuple_app(func) => {
            collect_relation_project_columns(func, out)?;
            collect_relation_project_columns(arg, out)
        }
        IRExpr::Var { name, .. } if name == "Tuple" => Some(()),
        _ => None,
    }
}

fn is_relation_tuple_app(expr: &IRExpr) -> bool {
    match expr {
        IRExpr::Var { name, .. } => name == "Tuple",
        IRExpr::App { func, .. } => is_relation_tuple_app(func),
        _ => false,
    }
}

fn parse_relation_projection(
    projection: &IRExpr,
    binding_entities: &HashMap<String, String>,
    allowed_bindings: &[&str],
) -> Option<Vec<RelProjection>> {
    let projection_items = relation_projection_items(projection)?;
    let mut out = Vec::with_capacity(projection_items.len());
    for item in projection_items {
        match item {
            IRExpr::Var { name, .. } if allowed_bindings.contains(&name.as_str()) => {
                out.push(RelProjection::Entity {
                    binding: name.clone(),
                    entity: binding_entities.get(name)?.clone(),
                });
            }
            IRExpr::Field { expr, field, .. } => {
                let IRExpr::Var { name, .. } = expr.as_ref() else {
                    return None;
                };
                if !allowed_bindings.contains(&name.as_str()) {
                    return None;
                }
                out.push(RelProjection::Field {
                    binding: name.clone(),
                    entity: binding_entities.get(name)?.clone(),
                    field: field.clone(),
                });
            }
            _ => return None,
        }
    }
    Some(out)
}

fn relation_projection_items(expr: &IRExpr) -> Option<Vec<&IRExpr>> {
    let mut items = Vec::new();
    let mut current = expr;
    loop {
        match current {
            IRExpr::App { func, arg, .. } => {
                items.push(arg.as_ref());
                current = func;
            }
            IRExpr::Var { name, .. } if name == "Tuple" => {
                items.reverse();
                return Some(items);
            }
            _ if items.is_empty() => return Some(vec![expr]),
            _ => return None,
        }
    }
}

fn parse_field_relation_subset(
    left: &IRExpr,
    right: &IRExpr,
    stores: &[IRStoreDecl],
) -> Option<(String, String, RelStateRef, RelStateRef)> {
    let (left_store, left_field, left_ref) = parse_field_relation_ref(left)?;
    let (right_store, right_field, right_ref) = parse_field_relation_ref(right)?;
    if left_store != right_store || left_field != right_field {
        return None;
    }
    stores
        .iter()
        .find(|store| store.name == left_store)
        .map(|store| {
            (
                store.entity_type.clone(),
                left_field.to_owned(),
                left_ref,
                right_ref,
            )
        })
}

fn parse_field_relation_ref(expr: &IRExpr) -> Option<(&str, &str, RelStateRef)> {
    let IRExpr::BinOp {
        op, left, right, ..
    } = expr
    else {
        return None;
    };
    if op != "OpRelationField" {
        return None;
    }
    let (store, state_ref) = parse_store_extent_ref(left)?;
    let IRExpr::Var { name, .. } = right.as_ref() else {
        return None;
    };
    let field = name.rsplit("::").next()?;
    Some((store, field, state_ref))
}

fn parse_store_extent_ref(expr: &IRExpr) -> Option<(&str, RelStateRef)> {
    match expr {
        IRExpr::Var { name, .. } => Some((name.as_str(), RelStateRef::Current)),
        IRExpr::Prime { expr, .. } => {
            let IRExpr::Var { name, .. } = expr.as_ref() else {
                return None;
            };
            Some((name.as_str(), RelStateRef::Next))
        }
        _ => None,
    }
}

fn parse_snapshot_quantifier_chain(
    expr: &IRExpr,
    entity_names: &[String],
) -> Result<Option<RelSnapshotExpr>, String> {
    let mut bindings = Vec::new();
    let mut current = expr;
    loop {
        match current {
            IRExpr::Exists {
                var, domain, body, ..
            } => {
                let IRType::Entity { name: entity_name } = domain else {
                    return Ok(None);
                };
                if !entity_names.contains(entity_name) {
                    return Ok(None);
                }
                bindings.push(RelQuantBinding {
                    quantifier: RelQuantifier::Exists,
                    var: var.clone(),
                    entity: entity_name.clone(),
                });
                current = body;
            }
            IRExpr::Forall {
                var, domain, body, ..
            } => {
                let IRType::Entity { name: entity_name } = domain else {
                    return Ok(None);
                };
                if !entity_names.contains(entity_name) {
                    return Ok(None);
                }
                bindings.push(RelQuantBinding {
                    quantifier: RelQuantifier::Forall,
                    var: var.clone(),
                    entity: entity_name.clone(),
                });
                current = body;
            }
            _ => break,
        }
    }

    if bindings.len() == 1 {
        let binding = &bindings[0];
        let Some(pred) =
            parse_slot_predicate_expr(current, Some(binding.var.as_str()), None, &HashMap::new())?
        else {
            return Ok(None);
        };
        return Ok(Some(match binding.quantifier {
            RelQuantifier::Exists => RelSnapshotExpr::Exists {
                entity: binding.entity.clone(),
                pred,
            },
            RelQuantifier::Forall => RelSnapshotExpr::Forall {
                entity: binding.entity.clone(),
                pred,
            },
        }));
    }

    let allowed_bindings = bindings
        .iter()
        .map(|binding| binding.var.as_str())
        .collect::<Vec<_>>();
    let Some(pred) =
        parse_scoped_predicate_expr(current, None, None, &HashMap::new(), &allowed_bindings)?
    else {
        return Ok(None);
    };
    Ok(Some(RelSnapshotExpr::ScopedQuantified { bindings, pred }))
}

fn parse_slot_predicate_expr(
    expr: &IRExpr,
    slot_var: Option<&str>,
    entity_ir: Option<&IREntity>,
    param_values: &HashMap<String, SimpleValue>,
) -> Result<Option<RelPred>, String> {
    match expr {
        IRExpr::Lit {
            value: LitVal::Bool { value: true },
            ..
        } => Ok(Some(RelPred::True)),
        IRExpr::Lit {
            value: LitVal::Bool { value: false },
            ..
        } => Ok(Some(RelPred::Not(Box::new(RelPred::True)))),
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpAnd" || op == "OpOr" || op == "OpImplies" => {
            let Some(left) = parse_slot_predicate_expr(left, slot_var, entity_ir, param_values)?
            else {
                return Ok(None);
            };
            let Some(right) = parse_slot_predicate_expr(right, slot_var, entity_ir, param_values)?
            else {
                return Ok(None);
            };
            Ok(Some(match op.as_str() {
                "OpAnd" => RelPred::And(Box::new(left), Box::new(right)),
                "OpOr" => RelPred::Or(Box::new(left), Box::new(right)),
                "OpImplies" => RelPred::Or(Box::new(RelPred::Not(Box::new(left))), Box::new(right)),
                _ => unreachable!(),
            }))
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => {
            let Some(inner) =
                parse_slot_predicate_expr(operand, slot_var, entity_ir, param_values)?
            else {
                return Ok(None);
            };
            Ok(Some(RelPred::Not(Box::new(inner))))
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpEq" || op == "OpNEq" => {
            if let Some(field) = parse_field_operand(left, slot_var, entity_ir) {
                if let Some(value) = simple_value_with_params(right, param_values) {
                    let eq = RelPred::Eq { field, value };
                    return Ok(Some(if op == "OpNEq" {
                        RelPred::Not(Box::new(eq))
                    } else {
                        eq
                    }));
                }
            }
            if let Some(field) = parse_field_operand(right, slot_var, entity_ir) {
                if let Some(value) = simple_value_with_params(left, param_values) {
                    let eq = RelPred::Eq { field, value };
                    return Ok(Some(if op == "OpNEq" {
                        RelPred::Not(Box::new(eq))
                    } else {
                        eq
                    }));
                }
            }
            Ok(None)
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if matches!(op.as_str(), "OpLt" | "OpLe" | "OpGt" | "OpGe") => {
            let cmp_op = match op.as_str() {
                "OpLt" => RelCmpOp::Lt,
                "OpLe" => RelCmpOp::Le,
                "OpGt" => RelCmpOp::Gt,
                "OpGe" => RelCmpOp::Ge,
                _ => unreachable!(),
            };
            if let Some(field) = parse_field_operand(left, slot_var, entity_ir) {
                if let Some(value) = simple_value_with_params(right, param_values) {
                    return Ok(Some(RelPred::Cmp {
                        field,
                        op: cmp_op,
                        value,
                    }));
                }
            }
            if let Some(field) = parse_field_operand(right, slot_var, entity_ir) {
                if let Some(value) = simple_value_with_params(left, param_values) {
                    let flipped = match cmp_op {
                        RelCmpOp::Lt => RelCmpOp::Gt,
                        RelCmpOp::Le => RelCmpOp::Ge,
                        RelCmpOp::Gt => RelCmpOp::Lt,
                        RelCmpOp::Ge => RelCmpOp::Le,
                    };
                    return Ok(Some(RelPred::Cmp {
                        field,
                        op: flipped,
                        value,
                    }));
                }
            }
            Ok(None)
        }
        IRExpr::Var { .. } | IRExpr::Field { .. } => {
            let Some(field) = parse_field_operand(expr, slot_var, entity_ir) else {
                return Ok(None);
            };
            Ok(Some(RelPred::Eq {
                field,
                value: SimpleValue::Bool(true),
            }))
        }
        _ => Ok(None),
    }
}

fn parse_field_operand(
    expr: &IRExpr,
    slot_var: Option<&str>,
    entity_ir: Option<&IREntity>,
) -> Option<String> {
    match expr {
        IRExpr::Field { expr, field, .. } => {
            let IRExpr::Var { name, .. } = &**expr else {
                return None;
            };
            if slot_var == Some(name.as_str()) {
                Some(field.clone())
            } else {
                None
            }
        }
        IRExpr::Var { name, .. } => entity_ir
            .and_then(|entity| entity.fields.iter().find(|field| field.name == *name))
            .map(|_| name.clone()),
        _ => None,
    }
}

fn collect_field_domains(
    defaults: &HashMap<String, SimpleValue>,
    base_domains: &HashMap<String, Vec<SimpleValue>>,
    steps: &[RelationalSystemStepSpec],
    assertions: &[RelSnapshotExpr],
    entity_name: &str,
) -> HashMap<String, Vec<SimpleValue>> {
    let mut domains = base_domains.clone();
    for (field, value) in defaults {
        push_domain_value(&mut domains, field, value.clone());
    }
    for step in steps {
        for action in &step.actions {
            match action {
                RelationalActionSpec::Create {
                    entity,
                    field_values,
                } if entity == entity_name => {
                    for (field, value) in field_values {
                        push_domain_value(&mut domains, field, value.clone());
                    }
                }
                RelationalActionSpec::Apply {
                    entity,
                    bindings,
                    guard,
                    updates,
                    ..
                } if entity == entity_name => {
                    for binding in bindings {
                        if binding.entity == entity_name {
                            let binding_entities =
                                HashMap::from([(binding.name.as_str(), binding.entity.as_str())]);
                            collect_scoped_pred_values_for_entity(
                                &binding.predicate,
                                &binding_entities,
                                &mut domains,
                                entity_name,
                            );
                        }
                    }
                    let binding_entities: HashMap<_, _> = bindings
                        .iter()
                        .map(|binding| (binding.name.as_str(), binding.entity.as_str()))
                        .collect();
                    collect_scoped_pred_values_for_entity(
                        guard,
                        &binding_entities,
                        &mut domains,
                        entity_name,
                    );
                    for (field, value) in updates {
                        push_domain_value(&mut domains, field, value.clone());
                    }
                }
                _ => {}
            }
        }
    }
    for assertion in assertions {
        collect_snapshot_values(assertion, &mut domains, entity_name);
    }
    domains
}

fn push_domain_value(
    domains: &mut HashMap<String, Vec<SimpleValue>>,
    field: &str,
    value: SimpleValue,
) {
    let entry = domains.entry(field.to_owned()).or_default();
    if !entry.contains(&value) {
        entry.push(value);
    }
}

fn collect_pred_values(pred: &RelPred, domains: &mut HashMap<String, Vec<SimpleValue>>) {
    match pred {
        RelPred::True => {}
        RelPred::Eq { field, value } => push_domain_value(domains, field, value.clone()),
        RelPred::Cmp { field, value, .. } => push_domain_value(domains, field, value.clone()),
        RelPred::And(left, right) | RelPred::Or(left, right) => {
            collect_pred_values(left, domains);
            collect_pred_values(right, domains);
        }
        RelPred::Not(inner) => collect_pred_values(inner, domains),
    }
}

fn collect_scoped_pred_values_for_entity(
    pred: &RelScopedPred,
    binding_entities: &HashMap<&str, &str>,
    domains: &mut HashMap<String, Vec<SimpleValue>>,
    entity_name: &str,
) {
    match pred {
        RelScopedPred::True => {}
        RelScopedPred::Eq {
            binding,
            field,
            value,
        } => {
            if binding_entities.get(binding.as_str()) == Some(&entity_name) {
                push_domain_value(domains, field, value.clone());
            }
        }
        RelScopedPred::Cmp {
            binding,
            field,
            value,
            ..
        } => {
            if binding_entities.get(binding.as_str()) == Some(&entity_name) {
                push_domain_value(domains, field, value.clone());
            }
        }
        RelScopedPred::EqBindings { .. } | RelScopedPred::CmpBindings { .. } => {}
        RelScopedPred::And(left, right) | RelScopedPred::Or(left, right) => {
            collect_scoped_pred_values_for_entity(left, binding_entities, domains, entity_name);
            collect_scoped_pred_values_for_entity(right, binding_entities, domains, entity_name);
        }
        RelScopedPred::Not(inner) => {
            collect_scoped_pred_values_for_entity(inner, binding_entities, domains, entity_name)
        }
    }
}

fn collect_snapshot_values(
    expr: &RelSnapshotExpr,
    domains: &mut HashMap<String, Vec<SimpleValue>>,
    entity_name: &str,
) {
    match expr {
        RelSnapshotExpr::Bool(_) => {}
        RelSnapshotExpr::Exists { entity, pred } | RelSnapshotExpr::Forall { entity, pred } => {
            if entity == entity_name {
                collect_pred_values(pred, domains);
            }
        }
        RelSnapshotExpr::ScopedQuantified { bindings, pred } => {
            let binding_entities = bindings
                .iter()
                .map(|binding| (binding.var.as_str(), binding.entity.as_str()))
                .collect::<HashMap<_, _>>();
            collect_scoped_pred_values_for_entity(pred, &binding_entities, domains, entity_name);
        }
        RelSnapshotExpr::StoreExtentSubset { .. } | RelSnapshotExpr::FieldRelationSubset { .. } => {
        }
        RelSnapshotExpr::RelationSubset { left, right } => {
            collect_relation_value_expr_values(left, domains, entity_name);
            collect_relation_value_expr_values(right, domains, entity_name);
        }
        RelSnapshotExpr::And(left, right) | RelSnapshotExpr::Or(left, right) => {
            collect_snapshot_values(left, domains, entity_name);
            collect_snapshot_values(right, domains, entity_name);
        }
        RelSnapshotExpr::Not(inner) => collect_snapshot_values(inner, domains, entity_name),
    }
}

fn collect_relation_value_expr_values(
    expr: &RelValueExpr,
    domains: &mut HashMap<String, Vec<SimpleValue>>,
    entity_name: &str,
) {
    match expr {
        RelValueExpr::StoreExtent { .. } => {}
        RelValueExpr::Field { .. } => {}
        RelValueExpr::Comprehension {
            projection: _,
            bindings,
            filter,
        } => {
            let binding_entities = bindings
                .iter()
                .map(|binding| (binding.var.as_str(), binding.entity.as_str()))
                .collect::<HashMap<_, _>>();
            collect_scoped_pred_values_for_entity(filter, &binding_entities, domains, entity_name);
        }
        RelValueExpr::Join(left, right) => {
            collect_relation_value_expr_values(left, domains, entity_name);
            collect_relation_value_expr_values(right, domains, entity_name);
        }
        RelValueExpr::Product(left, right)
        | RelValueExpr::Union(left, right)
        | RelValueExpr::Intersection(left, right)
        | RelValueExpr::Difference(left, right) => {
            collect_relation_value_expr_values(left, domains, entity_name);
            collect_relation_value_expr_values(right, domains, entity_name);
        }
        RelValueExpr::Project { expr, .. } => {
            collect_relation_value_expr_values(expr, domains, entity_name);
        }
        RelValueExpr::Transpose(inner) => {
            collect_relation_value_expr_values(inner, domains, entity_name);
        }
        RelValueExpr::Closure { expr, .. } => {
            collect_relation_value_expr_values(expr, domains, entity_name);
        }
    }
}

fn build_field_encodings(
    sat: &mut SatInstance,
    defaults: &HashMap<String, SimpleValue>,
    domains: &HashMap<String, Vec<SimpleValue>>,
    slot_count: usize,
    bound: usize,
) -> Result<HashMap<String, FieldDomainEncoding>, String> {
    let mut out = HashMap::new();
    for (field, domain) in domains {
        let default_idx = defaults
            .get(field)
            .map(|default| {
                domain
                    .iter()
                    .position(|candidate| candidate == default)
                    .ok_or_else(|| format!("default domain mismatch for field `{field}`"))
            })
            .transpose()?;
        let mut state_lits = Vec::with_capacity(bound + 1);
        for state_idx in 0..=bound {
            let mut slot_lits = Vec::with_capacity(slot_count);
            for _slot in 0..slot_count {
                let value_lits: Vec<_> = (0..domain.len()).map(|_| sat.new_lit()).collect();
                sat.add_card_constr(CardConstraint::new_eq(value_lits.clone(), 1));
                if state_idx == 0 {
                    if let Some(default_idx) = default_idx {
                        sat.add_unit(value_lits[default_idx]);
                    }
                }
                slot_lits.push(value_lits);
            }
            state_lits.push(slot_lits);
        }
        out.insert(
            field.clone(),
            FieldDomainEncoding {
                values: domain.clone(),
                state_lits,
            },
        );
    }
    Ok(out)
}

fn apply_relational_action(
    sat: &mut SatInstance,
    action: &RelationalActionSpec,
    step_fire: rustsat::types::Lit,
    fixed_bindings: &HashMap<String, (String, Vec<rustsat::types::Lit>)>,
    current_active: &mut HashMap<String, Vec<rustsat::types::Lit>>,
    current_fields: &mut HashMap<String, HashMap<String, Vec<Vec<rustsat::types::Lit>>>>,
    entity_states: &HashMap<String, EntityStateEncoding>,
) -> Result<(), String> {
    match action {
        RelationalActionSpec::Create {
            entity,
            field_values,
        } => {
            let prev_active = current_active
                .get(entity)
                .ok_or_else(|| format!("missing active-state projection for `{entity}`"))?
                .clone();
            let prev_fields = current_fields
                .get(entity)
                .ok_or_else(|| format!("missing field-state projection for `{entity}`"))?
                .clone();
            let entity_state = entity_states
                .get(entity)
                .ok_or_else(|| format!("missing entity encoding for `{entity}`"))?;
            let assigns: Vec<_> = (0..entity_state.slot_count)
                .map(|_| sat.new_lit())
                .collect();
            for &assign in &assigns {
                sat.add_binary(!assign, step_fire);
            }
            for slot in 0..entity_state.slot_count {
                sat.add_binary(!assigns[slot], !prev_active[slot]);
            }
            for i in 0..assigns.len() {
                for j in (i + 1)..assigns.len() {
                    sat.add_binary(!assigns[i], !assigns[j]);
                }
            }
            if !assigns.is_empty() {
                let mut clause = vec![!step_fire];
                clause.extend(assigns.iter().copied());
                sat.add_clause(clause.as_slice().into());
            } else {
                sat.add_unit(!step_fire);
            }

            let mut next_active = Vec::with_capacity(entity_state.slot_count);
            for slot in 0..entity_state.slot_count {
                let next = sat.new_lit();
                let create_hit = assigns[slot];
                let next_source = or_lit(sat, &[prev_active[slot], create_hit])?;
                sat.add_binary(!next, next_source);
                sat.add_binary(!next_source, next);
                next_active.push(next);
            }
            current_active.insert(entity.clone(), next_active);

            let mut next_fields = HashMap::new();
            for (field_name, encoding) in &entity_state.field_encodings {
                let prev_slots = prev_fields
                    .get(field_name)
                    .ok_or_else(|| format!("missing field projection `{entity}.{field_name}`"))?;
                let mut next_slots = Vec::with_capacity(entity_state.slot_count);
                for slot in 0..entity_state.slot_count {
                    let mut value_lits = Vec::with_capacity(encoding.values.len());
                    for (value_idx, value) in encoding.values.iter().enumerate() {
                        let next_lit = sat.new_lit();
                        let mut reasons = Vec::new();
                        if field_values.get(field_name) == Some(value) {
                            reasons.push(assigns[slot]);
                        }
                        let frame = and_lit(sat, &[prev_slots[slot][value_idx], !assigns[slot]])?;
                        reasons.push(frame);
                        let source = or_lit(sat, &reasons)?;
                        sat.add_binary(!next_lit, source);
                        sat.add_binary(!source, next_lit);
                        value_lits.push(next_lit);
                    }
                    next_slots.push(value_lits);
                }
                next_fields.insert(field_name.clone(), next_slots);
            }
            current_fields.insert(entity.clone(), next_fields);
        }
        RelationalActionSpec::Apply {
            entity,
            target_binding,
            binding_aliases,
            bindings,
            guard,
            updates,
        } => {
            let entity_state = entity_states
                .get(entity)
                .ok_or_else(|| format!("missing entity encoding for `{entity}`"))?;
            let mut binding_slots = fixed_bindings.clone();
            for (alias, source) in binding_aliases {
                let Some((source_entity, slots)) = fixed_bindings.get(source) else {
                    return Err(format!("missing aliased binding `{source}`"));
                };
                binding_slots.insert(alias.clone(), (source_entity.clone(), slots.clone()));
            }
            for binding in bindings {
                let prev_active = current_active.get(&binding.entity).ok_or_else(|| {
                    format!("missing active-state projection for `{}`", binding.entity)
                })?;
                let binding_state = entity_states
                    .get(&binding.entity)
                    .ok_or_else(|| format!("missing entity encoding for `{}`", binding.entity))?;
                let slots: Vec<_> = (0..binding_state.slot_count)
                    .map(|_| sat.new_lit())
                    .collect();
                for &slot_lit in &slots {
                    sat.add_binary(!slot_lit, step_fire);
                }
                if let Some(alias_of) = &binding.alias_of {
                    let Some((source_entity, source_slots)) = binding_slots.get(alias_of) else {
                        return Err(format!("missing aliased binding `{alias_of}`"));
                    };
                    if source_entity != &binding.entity {
                        return Err(format!(
                            "binding `{}` aliases `{alias_of}` with mismatched entity type",
                            binding.name
                        ));
                    }
                    if source_slots.len() != slots.len() {
                        return Err(format!(
                            "binding `{}` aliases `{alias_of}` with mismatched slot count",
                            binding.name
                        ));
                    }
                    for slot in 0..slots.len() {
                        sat.add_binary(!slots[slot], source_slots[slot]);
                        sat.add_clause([!step_fire, !source_slots[slot], slots[slot]].into());
                    }
                }
                for slot in 0..binding_state.slot_count {
                    sat.add_binary(!slots[slot], prev_active[slot]);
                    let mut temp_binding_slots = binding_slots.clone();
                    let temp_slots: Vec<_> = (0..binding_state.slot_count)
                        .map(|candidate| const_lit(sat, candidate == slot))
                        .collect();
                    temp_binding_slots
                        .insert(binding.name.clone(), (binding.entity.clone(), temp_slots));
                    let eligible = encode_scoped_pred_with_bindings(
                        sat,
                        &binding.predicate,
                        &temp_binding_slots,
                        current_fields,
                        entity_states,
                    )?;
                    sat.add_binary(!slots[slot], eligible);
                }
                for i in 0..slots.len() {
                    for j in (i + 1)..slots.len() {
                        sat.add_binary(!slots[i], !slots[j]);
                    }
                }
                if !slots.is_empty() {
                    let mut clause = vec![!step_fire];
                    clause.extend(slots.iter().copied());
                    sat.add_clause(clause.as_slice().into());
                } else {
                    sat.add_unit(!step_fire);
                }
                binding_slots.insert(binding.name.clone(), (binding.entity.clone(), slots));
            }
            let guard_lit = encode_scoped_pred_with_bindings(
                sat,
                guard,
                &binding_slots,
                current_fields,
                entity_states,
            )?;
            sat.add_binary(!step_fire, guard_lit);
            let (_, targets) = binding_slots
                .get(target_binding)
                .ok_or_else(|| format!("missing target binding `{target_binding}`"))?;

            let prev_fields = current_fields
                .get(entity)
                .ok_or_else(|| format!("missing field-state projection for `{entity}`"))?
                .clone();
            let mut next_fields = HashMap::new();
            for (field_name, encoding) in &entity_state.field_encodings {
                let prev_slots = prev_fields
                    .get(field_name)
                    .ok_or_else(|| format!("missing field projection `{entity}.{field_name}`"))?;
                let mut next_slots = Vec::with_capacity(entity_state.slot_count);
                for slot in 0..entity_state.slot_count {
                    let mut value_lits = Vec::with_capacity(encoding.values.len());
                    let field_is_updated = updates.contains_key(field_name);
                    for (value_idx, value) in encoding.values.iter().enumerate() {
                        let next_lit = sat.new_lit();
                        let mut reasons = Vec::new();
                        if updates.get(field_name) == Some(value) {
                            reasons.push(and_lit(sat, &[step_fire, targets[slot]])?);
                        }
                        let frame_guard = if field_is_updated {
                            or_lit(sat, &[!step_fire, !targets[slot]])?
                        } else {
                            const_lit(sat, true)
                        };
                        let frame = and_lit(sat, &[prev_slots[slot][value_idx], frame_guard])?;
                        reasons.push(frame);
                        let source = or_lit(sat, &reasons)?;
                        sat.add_binary(!next_lit, source);
                        sat.add_binary(!source, next_lit);
                        value_lits.push(next_lit);
                    }
                    next_slots.push(value_lits);
                }
                next_fields.insert(field_name.clone(), next_slots);
            }
            current_fields.insert(entity.clone(), next_fields);
        }
    }
    Ok(())
}

fn encode_verify_violation_into(
    assertions: &[RelSnapshotExpr],
    entity_states: &HashMap<String, EntityStateEncoding>,
    sat: &mut SatInstance,
    bound: usize,
) -> Result<rustsat::types::Lit, String> {
    let mut violations = Vec::with_capacity(assertions.len() * (bound + 1));
    for assertion in assertions {
        for state_idx in 0..=bound {
            let holds =
                encode_verify_snapshot_into(assertion, entity_states, sat, state_idx, bound)?;
            violations.push(!holds);
        }
    }
    if violations.is_empty() {
        return Err("relational verify fragment requires at least one always assertion".to_owned());
    }
    or_lit(sat, &violations)
}

fn encode_verify_snapshot_into(
    expr: &RelSnapshotExpr,
    entity_states: &HashMap<String, EntityStateEncoding>,
    sat: &mut SatInstance,
    state_idx: usize,
    bound: usize,
) -> Result<rustsat::types::Lit, String> {
    match expr {
        RelSnapshotExpr::Bool(value) => Ok(const_lit(sat, *value)),
        RelSnapshotExpr::Exists { entity, pred } => {
            let state = entity_states
                .get(entity)
                .ok_or_else(|| format!("missing relational entity state for `{entity}`"))?;
            let active_slots = &state.active_by_state[state_idx];
            let mut matches = Vec::with_capacity(active_slots.len());
            for (slot, &active) in active_slots.iter().enumerate() {
                let pred_lit =
                    encode_rel_pred_for_slot(pred, &state.field_encodings, state_idx, slot, sat)?;
                matches.push(and_lit(sat, &[active, pred_lit])?);
            }
            or_lit(sat, &matches)
        }
        RelSnapshotExpr::Forall { entity, pred } => {
            let state = entity_states
                .get(entity)
                .ok_or_else(|| format!("missing relational entity state for `{entity}`"))?;
            let active_slots = &state.active_by_state[state_idx];
            let mut clauses = Vec::with_capacity(active_slots.len());
            for (slot, &active) in active_slots.iter().enumerate() {
                let pred_lit =
                    encode_rel_pred_for_slot(pred, &state.field_encodings, state_idx, slot, sat)?;
                clauses.push(or_lit(sat, &[!active, pred_lit])?);
            }
            and_lit(sat, &clauses)
        }
        RelSnapshotExpr::ScopedQuantified { bindings, pred } => {
            let mut assignment = HashMap::new();
            encode_scoped_quantified_snapshot(
                bindings,
                pred,
                entity_states,
                sat,
                state_idx,
                0,
                &mut assignment,
            )
        }
        RelSnapshotExpr::StoreExtentSubset {
            entity,
            left,
            right,
        } => {
            let Some(left_idx) = relation_state_index(*left, state_idx, bound) else {
                return Ok(const_lit(sat, true));
            };
            let Some(right_idx) = relation_state_index(*right, state_idx, bound) else {
                return Ok(const_lit(sat, true));
            };
            let state = entity_states
                .get(entity)
                .ok_or_else(|| format!("missing relational entity state for `{entity}`"))?;
            let left_active = &state.active_by_state[left_idx];
            let right_active = &state.active_by_state[right_idx];
            let clauses = left_active
                .iter()
                .zip(right_active)
                .map(|(&left, &right)| or_lit(sat, &[!left, right]))
                .collect::<Result<Vec<_>, _>>()?;
            and_lit(sat, &clauses)
        }
        RelSnapshotExpr::FieldRelationSubset {
            entity,
            field,
            left,
            right,
        } => {
            let Some(left_idx) = relation_state_index(*left, state_idx, bound) else {
                return Ok(const_lit(sat, true));
            };
            let Some(right_idx) = relation_state_index(*right, state_idx, bound) else {
                return Ok(const_lit(sat, true));
            };
            let state = entity_states
                .get(entity)
                .ok_or_else(|| format!("missing relational entity state for `{entity}`"))?;
            let encoding = state
                .field_encodings
                .get(field)
                .ok_or_else(|| format!("missing relational field `{entity}.{field}`"))?;
            let mut clauses = Vec::new();
            for slot in 0..state.slot_count {
                let left_active = state.active_by_state[left_idx][slot];
                let right_active = state.active_by_state[right_idx][slot];
                for value_idx in 0..encoding.values.len() {
                    let left_lit = encoding.state_lits[left_idx][slot][value_idx];
                    let right_lit = encoding.state_lits[right_idx][slot][value_idx];
                    clauses.push(or_lit(sat, &[!left_active, !left_lit, right_active])?);
                    clauses.push(or_lit(sat, &[!left_active, !left_lit, right_lit])?);
                }
            }
            and_lit(sat, &clauses)
        }
        RelSnapshotExpr::RelationSubset { left, right } => {
            let domains = relation_value_domains(left, entity_states)?;
            let tuples = relation_domain_tuples(&domains);
            let mut clauses = Vec::with_capacity(tuples.len());
            for tuple in tuples {
                let left_lit = encode_relation_value_membership(
                    left,
                    &tuple,
                    entity_states,
                    sat,
                    state_idx,
                    bound,
                )?;
                let right_lit = encode_relation_value_membership(
                    right,
                    &tuple,
                    entity_states,
                    sat,
                    state_idx,
                    bound,
                )?;
                clauses.push(or_lit(sat, &[!left_lit, right_lit])?);
            }
            and_lit(sat, &clauses)
        }
        RelSnapshotExpr::And(left, right) => {
            let left_lit = encode_verify_snapshot_into(left, entity_states, sat, state_idx, bound)?;
            let right_lit =
                encode_verify_snapshot_into(right, entity_states, sat, state_idx, bound)?;
            and_lit(sat, &[left_lit, right_lit])
        }
        RelSnapshotExpr::Or(left, right) => {
            let left_lit = encode_verify_snapshot_into(left, entity_states, sat, state_idx, bound)?;
            let right_lit =
                encode_verify_snapshot_into(right, entity_states, sat, state_idx, bound)?;
            or_lit(sat, &[left_lit, right_lit])
        }
        RelSnapshotExpr::Not(inner) => Ok(!encode_verify_snapshot_into(
            inner,
            entity_states,
            sat,
            state_idx,
            bound,
        )?),
    }
}

fn relation_state_index(state_ref: RelStateRef, state_idx: usize, bound: usize) -> Option<usize> {
    match state_ref {
        RelStateRef::Current => Some(state_idx),
        RelStateRef::Next if state_idx < bound => Some(state_idx + 1),
        RelStateRef::Next => None,
    }
}

fn relation_value_domains(
    expr: &RelValueExpr,
    entity_states: &HashMap<String, EntityStateEncoding>,
) -> Result<Vec<Vec<RelAtomRef>>, String> {
    match expr {
        RelValueExpr::StoreExtent { entity, .. } => {
            let state = entity_states
                .get(entity)
                .ok_or_else(|| format!("missing relational entity state for `{entity}`"))?;
            Ok(vec![(0..state.slot_count)
                .map(|slot| RelAtomRef::EntitySlot {
                    entity: entity.clone(),
                    slot,
                })
                .collect()])
        }
        RelValueExpr::Field { entity, field, .. } => {
            let state = entity_states
                .get(entity)
                .ok_or_else(|| format!("missing relational entity state for `{entity}`"))?;
            let encoding = state
                .field_encodings
                .get(field)
                .ok_or_else(|| format!("missing relational field `{entity}.{field}`"))?;
            Ok(vec![
                (0..state.slot_count)
                    .map(|slot| RelAtomRef::EntitySlot {
                        entity: entity.clone(),
                        slot,
                    })
                    .collect(),
                encoding
                    .values
                    .iter()
                    .cloned()
                    .map(RelAtomRef::Value)
                    .collect(),
            ])
        }
        RelValueExpr::Comprehension { projection, .. } => projection
            .iter()
            .map(|item| match item {
                RelProjection::Entity { entity, .. } => {
                    let state = entity_states
                        .get(entity)
                        .ok_or_else(|| format!("missing relational entity state for `{entity}`"))?;
                    Ok((0..state.slot_count)
                        .map(|slot| RelAtomRef::EntitySlot {
                            entity: entity.clone(),
                            slot,
                        })
                        .collect())
                }
                RelProjection::Field { entity, field, .. } => {
                    let state = entity_states
                        .get(entity)
                        .ok_or_else(|| format!("missing relational entity state for `{entity}`"))?;
                    let encoding = state
                        .field_encodings
                        .get(field)
                        .ok_or_else(|| format!("missing relational field `{entity}.{field}`"))?;
                    Ok(encoding
                        .values
                        .iter()
                        .cloned()
                        .map(RelAtomRef::Value)
                        .collect())
                }
            })
            .collect(),
        RelValueExpr::Join(left, right) => {
            let left_domains = relation_value_domains(left, entity_states)?;
            let right_domains = relation_value_domains(right, entity_states)?;
            if left_domains.is_empty() || right_domains.is_empty() {
                return Ok(Vec::new());
            }
            let mut domains = Vec::new();
            domains.extend(left_domains[..left_domains.len() - 1].iter().cloned());
            domains.extend(right_domains[1..].iter().cloned());
            Ok(domains)
        }
        RelValueExpr::Product(left, right) => {
            let mut domains = relation_value_domains(left, entity_states)?;
            domains.extend(relation_value_domains(right, entity_states)?);
            Ok(domains)
        }
        RelValueExpr::Project { expr, columns } => {
            let domains = relation_value_domains(expr, entity_states)?;
            columns
                .iter()
                .map(|column| {
                    domains
                        .get(*column)
                        .cloned()
                        .ok_or_else(|| format!("relation project column {column} out of bounds"))
                })
                .collect()
        }
        RelValueExpr::Union(left, right)
        | RelValueExpr::Intersection(left, right)
        | RelValueExpr::Difference(left, right) => {
            let left_domains = relation_value_domains(left, entity_states)?;
            let right_domains = relation_value_domains(right, entity_states)?;
            if left_domains.len() != right_domains.len() {
                return Err("relation set operation arity mismatch".to_owned());
            }
            Ok(left_domains)
        }
        RelValueExpr::Transpose(inner) => {
            let mut domains = relation_value_domains(inner, entity_states)?;
            if domains.len() == 2 {
                domains.swap(0, 1);
                Ok(domains)
            } else {
                Err("Rel::transpose requires a binary relation".to_owned())
            }
        }
        RelValueExpr::Closure { expr, .. } => {
            let domains = relation_value_domains(expr, entity_states)?;
            if domains.len() != 2 {
                return Err("Rel::closure requires a binary relation".to_owned());
            }
            if domains[0] != domains[1] {
                return Err("Rel::closure requires a homogeneous binary relation".to_owned());
            }
            Ok(domains)
        }
    }
}

fn relation_domain_tuples(domains: &[Vec<RelAtomRef>]) -> Vec<Vec<RelAtomRef>> {
    let mut out = Vec::new();
    collect_relation_domain_tuples(domains, 0, &mut Vec::new(), &mut out);
    out
}

fn collect_relation_domain_tuples(
    domains: &[Vec<RelAtomRef>],
    index: usize,
    current: &mut Vec<RelAtomRef>,
    out: &mut Vec<Vec<RelAtomRef>>,
) {
    if index == domains.len() {
        out.push(current.clone());
        return;
    }
    for atom in &domains[index] {
        current.push(atom.clone());
        collect_relation_domain_tuples(domains, index + 1, current, out);
        current.pop();
    }
}

fn encode_relation_value_membership(
    expr: &RelValueExpr,
    tuple: &[RelAtomRef],
    entity_states: &HashMap<String, EntityStateEncoding>,
    sat: &mut SatInstance,
    state_idx: usize,
    bound: usize,
) -> Result<rustsat::types::Lit, String> {
    match expr {
        RelValueExpr::StoreExtent { entity, state_ref } => {
            if tuple.len() != 1 {
                return Ok(const_lit(sat, false));
            }
            let RelAtomRef::EntitySlot {
                entity: atom_entity,
                slot,
            } = &tuple[0]
            else {
                return Ok(const_lit(sat, false));
            };
            if atom_entity != entity {
                return Ok(const_lit(sat, false));
            }
            let Some(real_state_idx) = relation_state_index(*state_ref, state_idx, bound) else {
                return Ok(const_lit(sat, false));
            };
            let state = entity_states
                .get(entity)
                .ok_or_else(|| format!("missing relational entity state for `{entity}`"))?;
            if *slot >= state.slot_count {
                return Ok(const_lit(sat, false));
            }
            Ok(state.active_by_state[real_state_idx][*slot])
        }
        RelValueExpr::Field {
            entity,
            field,
            state_ref,
        } => encode_field_relation_membership(
            entity,
            field,
            *state_ref,
            tuple,
            entity_states,
            sat,
            state_idx,
            bound,
        ),
        RelValueExpr::Comprehension {
            projection,
            bindings,
            filter,
        } => encode_relation_comprehension_membership(
            projection,
            bindings,
            filter,
            tuple,
            entity_states,
            sat,
            state_idx,
            bound,
        ),
        RelValueExpr::Transpose(inner) => {
            if tuple.len() != 2 {
                return Ok(const_lit(sat, false));
            }
            let reversed = vec![tuple[1].clone(), tuple[0].clone()];
            encode_relation_value_membership(inner, &reversed, entity_states, sat, state_idx, bound)
        }
        RelValueExpr::Product(left, right) => {
            let left_arity = relation_value_domains(left, entity_states)?.len();
            if tuple.len() < left_arity {
                return Ok(const_lit(sat, false));
            }
            let left_lit = encode_relation_value_membership(
                left,
                &tuple[..left_arity],
                entity_states,
                sat,
                state_idx,
                bound,
            )?;
            let right_lit = encode_relation_value_membership(
                right,
                &tuple[left_arity..],
                entity_states,
                sat,
                state_idx,
                bound,
            )?;
            and_lit(sat, &[left_lit, right_lit])
        }
        RelValueExpr::Project { expr, columns } => {
            if tuple.len() != columns.len() {
                return Ok(const_lit(sat, false));
            }
            let inner_domains = relation_value_domains(expr, entity_states)?;
            let mut reasons = Vec::new();
            for candidate in relation_domain_tuples(&inner_domains) {
                let selected = columns
                    .iter()
                    .map(|column| candidate.get(*column).cloned())
                    .collect::<Option<Vec<_>>>();
                if selected.as_deref() == Some(tuple) {
                    reasons.push(encode_relation_value_membership(
                        expr,
                        &candidate,
                        entity_states,
                        sat,
                        state_idx,
                        bound,
                    )?);
                }
            }
            or_lit(sat, &reasons)
        }
        RelValueExpr::Union(left, right) => {
            let left_lit = encode_relation_value_membership(
                left,
                tuple,
                entity_states,
                sat,
                state_idx,
                bound,
            )?;
            let right_lit = encode_relation_value_membership(
                right,
                tuple,
                entity_states,
                sat,
                state_idx,
                bound,
            )?;
            or_lit(sat, &[left_lit, right_lit])
        }
        RelValueExpr::Intersection(left, right) => {
            let left_lit = encode_relation_value_membership(
                left,
                tuple,
                entity_states,
                sat,
                state_idx,
                bound,
            )?;
            let right_lit = encode_relation_value_membership(
                right,
                tuple,
                entity_states,
                sat,
                state_idx,
                bound,
            )?;
            and_lit(sat, &[left_lit, right_lit])
        }
        RelValueExpr::Difference(left, right) => {
            let left_lit = encode_relation_value_membership(
                left,
                tuple,
                entity_states,
                sat,
                state_idx,
                bound,
            )?;
            let right_lit = encode_relation_value_membership(
                right,
                tuple,
                entity_states,
                sat,
                state_idx,
                bound,
            )?;
            and_lit(sat, &[left_lit, !right_lit])
        }
        RelValueExpr::Join(left, right) => {
            let left_domains = relation_value_domains(left, entity_states)?;
            let right_domains = relation_value_domains(right, entity_states)?;
            if left_domains.is_empty() || right_domains.is_empty() {
                return Ok(const_lit(sat, false));
            }
            let left_arity = left_domains.len();
            let right_arity = right_domains.len();
            if tuple.len() != left_arity + right_arity - 2 {
                return Ok(const_lit(sat, false));
            }
            let mut middle = left_domains[left_arity - 1].clone();
            middle.retain(|atom| right_domains[0].contains(atom));
            let mut reasons = Vec::new();
            for atom in middle {
                let mut left_tuple = tuple[..left_arity - 1].to_vec();
                left_tuple.push(atom.clone());
                let mut right_tuple = vec![atom];
                right_tuple.extend(tuple[left_arity - 1..].iter().cloned());
                let left_lit = encode_relation_value_membership(
                    left,
                    &left_tuple,
                    entity_states,
                    sat,
                    state_idx,
                    bound,
                )?;
                let right_lit = encode_relation_value_membership(
                    right,
                    &right_tuple,
                    entity_states,
                    sat,
                    state_idx,
                    bound,
                )?;
                reasons.push(and_lit(sat, &[left_lit, right_lit])?);
            }
            or_lit(sat, &reasons)
        }
        RelValueExpr::Closure { expr, reflexive } => encode_relation_closure_membership(
            expr,
            *reflexive,
            tuple,
            entity_states,
            sat,
            state_idx,
            bound,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn encode_relation_closure_membership(
    expr: &RelValueExpr,
    reflexive: bool,
    tuple: &[RelAtomRef],
    entity_states: &HashMap<String, EntityStateEncoding>,
    sat: &mut SatInstance,
    state_idx: usize,
    bound: usize,
) -> Result<rustsat::types::Lit, String> {
    if tuple.len() != 2 {
        return Ok(const_lit(sat, false));
    }
    let domains = relation_value_domains(expr, entity_states)?;
    if domains.len() != 2 {
        return Err("Rel::closure requires a binary relation".to_owned());
    }
    if domains[0] != domains[1] {
        return Err("Rel::closure requires a homogeneous binary relation".to_owned());
    }
    if !domains[0].contains(&tuple[0]) || !domains[1].contains(&tuple[1]) {
        return Ok(const_lit(sat, false));
    }

    let node_count = domains[0].len();
    let mut reasons = Vec::new();
    if reflexive && tuple[0] == tuple[1] {
        reasons.push(const_lit(sat, true));
    }
    if node_count > 0 {
        let mut memo = HashMap::new();
        reasons.push(encode_relation_path_within(
            expr,
            &tuple[0],
            &tuple[1],
            node_count,
            &domains[0],
            entity_states,
            sat,
            state_idx,
            bound,
            &mut memo,
        )?);
    }
    or_lit(sat, &reasons)
}

#[allow(clippy::too_many_arguments)]
fn encode_relation_path_within(
    expr: &RelValueExpr,
    start: &RelAtomRef,
    end: &RelAtomRef,
    max_edges: usize,
    nodes: &[RelAtomRef],
    entity_states: &HashMap<String, EntityStateEncoding>,
    sat: &mut SatInstance,
    state_idx: usize,
    bound: usize,
    memo: &mut HashMap<(RelAtomRef, RelAtomRef, usize), rustsat::types::Lit>,
) -> Result<rustsat::types::Lit, String> {
    if max_edges == 0 {
        return Ok(const_lit(sat, false));
    }
    let key = (start.clone(), end.clone(), max_edges);
    if let Some(lit) = memo.get(&key) {
        return Ok(*lit);
    }

    let edge = encode_relation_value_membership(
        expr,
        &[start.clone(), end.clone()],
        entity_states,
        sat,
        state_idx,
        bound,
    )?;
    let lit = if max_edges == 1 {
        edge
    } else {
        let mut reasons = vec![edge];
        for middle in nodes {
            let first = encode_relation_value_membership(
                expr,
                &[start.clone(), middle.clone()],
                entity_states,
                sat,
                state_idx,
                bound,
            )?;
            let rest = encode_relation_path_within(
                expr,
                middle,
                end,
                max_edges - 1,
                nodes,
                entity_states,
                sat,
                state_idx,
                bound,
                memo,
            )?;
            reasons.push(and_lit(sat, &[first, rest])?);
        }
        or_lit(sat, &reasons)?
    };
    memo.insert(key, lit);
    Ok(lit)
}

#[allow(clippy::too_many_arguments)]
fn encode_field_relation_membership(
    entity: &str,
    field: &str,
    state_ref: RelStateRef,
    tuple: &[RelAtomRef],
    entity_states: &HashMap<String, EntityStateEncoding>,
    sat: &mut SatInstance,
    state_idx: usize,
    bound: usize,
) -> Result<rustsat::types::Lit, String> {
    if tuple.len() != 2 {
        return Ok(const_lit(sat, false));
    }
    let RelAtomRef::EntitySlot {
        entity: tuple_entity,
        slot,
    } = &tuple[0]
    else {
        return Ok(const_lit(sat, false));
    };
    let RelAtomRef::Value(value) = &tuple[1] else {
        return Ok(const_lit(sat, false));
    };
    if tuple_entity != entity {
        return Ok(const_lit(sat, false));
    }
    let Some(real_state_idx) = relation_state_index(state_ref, state_idx, bound) else {
        return Ok(const_lit(sat, false));
    };
    let state = entity_states
        .get(entity)
        .ok_or_else(|| format!("missing relational entity state for `{entity}`"))?;
    if *slot >= state.slot_count {
        return Ok(const_lit(sat, false));
    }
    let encoding = state
        .field_encodings
        .get(field)
        .ok_or_else(|| format!("missing relational field `{entity}.{field}`"))?;
    let Some(value_idx) = encoding
        .values
        .iter()
        .position(|candidate| candidate == value)
    else {
        return Ok(const_lit(sat, false));
    };
    and_lit(
        sat,
        &[
            state.active_by_state[real_state_idx][*slot],
            encoding.state_lits[real_state_idx][*slot][value_idx],
        ],
    )
}

#[allow(clippy::too_many_arguments)]
fn encode_relation_comprehension_membership(
    projection: &[RelProjection],
    bindings: &[RelComprehensionBinding],
    filter: &RelScopedPred,
    tuple: &[RelAtomRef],
    entity_states: &HashMap<String, EntityStateEncoding>,
    sat: &mut SatInstance,
    state_idx: usize,
    bound: usize,
) -> Result<rustsat::types::Lit, String> {
    if projection.len() != tuple.len() {
        return Ok(const_lit(sat, false));
    }
    let mut assignments = Vec::new();
    encode_relation_comprehension_assignments(
        projection,
        bindings,
        filter,
        tuple,
        entity_states,
        sat,
        state_idx,
        bound,
        0,
        &mut HashMap::new(),
        &mut assignments,
    )?;
    or_lit(sat, &assignments)
}

#[allow(clippy::too_many_arguments)]
fn encode_relation_comprehension_assignments(
    projection: &[RelProjection],
    bindings: &[RelComprehensionBinding],
    filter: &RelScopedPred,
    tuple: &[RelAtomRef],
    entity_states: &HashMap<String, EntityStateEncoding>,
    sat: &mut SatInstance,
    state_idx: usize,
    bound: usize,
    index: usize,
    assignment: &mut HashMap<String, (String, usize)>,
    out: &mut Vec<rustsat::types::Lit>,
) -> Result<(), String> {
    if index == bindings.len() {
        out.push(encode_relation_comprehension_assignment(
            projection,
            bindings,
            filter,
            tuple,
            entity_states,
            sat,
            state_idx,
            bound,
            assignment,
        )?);
        return Ok(());
    }
    let binding = &bindings[index];
    let state = entity_states
        .get(&binding.entity)
        .ok_or_else(|| format!("missing relational entity state for `{}`", binding.entity))?;
    for slot in 0..state.slot_count {
        assignment.insert(binding.var.clone(), (binding.entity.clone(), slot));
        encode_relation_comprehension_assignments(
            projection,
            bindings,
            filter,
            tuple,
            entity_states,
            sat,
            state_idx,
            bound,
            index + 1,
            assignment,
            out,
        )?;
    }
    assignment.remove(&binding.var);
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn encode_relation_comprehension_assignment(
    projection: &[RelProjection],
    bindings: &[RelComprehensionBinding],
    filter: &RelScopedPred,
    tuple: &[RelAtomRef],
    entity_states: &HashMap<String, EntityStateEncoding>,
    sat: &mut SatInstance,
    state_idx: usize,
    bound: usize,
    assignment: &HashMap<String, (String, usize)>,
) -> Result<rustsat::types::Lit, String> {
    let mut constraints = Vec::new();
    for binding in bindings {
        let Some(source_idx) = relation_state_index(binding.source_ref, state_idx, bound) else {
            return Ok(const_lit(sat, false));
        };
        let state = entity_states
            .get(&binding.entity)
            .ok_or_else(|| format!("missing relational entity state for `{}`", binding.entity))?;
        let Some((_, slot)) = assignment.get(&binding.var) else {
            return Ok(const_lit(sat, false));
        };
        constraints.push(state.active_by_state[source_idx][*slot]);
    }

    let binding_slots = assignment
        .iter()
        .map(|(var, (entity, slot))| {
            let state = entity_states
                .get(entity)
                .ok_or_else(|| format!("missing relational entity state for `{entity}`"))?;
            let slots = (0..state.slot_count)
                .map(|candidate| const_lit(sat, candidate == *slot))
                .collect::<Vec<_>>();
            Ok((var.clone(), (entity.clone(), slots)))
        })
        .collect::<Result<HashMap<_, _>, String>>()?;
    let current_fields = fields_for_state(entity_states, state_idx);
    constraints.push(encode_scoped_pred_with_bindings(
        sat,
        filter,
        &binding_slots,
        &current_fields,
        entity_states,
    )?);

    for (projection, atom) in projection.iter().zip(tuple) {
        constraints.push(encode_projection_matches_atom(
            projection,
            atom,
            assignment,
            entity_states,
            sat,
            state_idx,
        )?);
    }

    and_lit(sat, &constraints)
}

fn fields_for_state(
    entity_states: &HashMap<String, EntityStateEncoding>,
    state_idx: usize,
) -> HashMap<String, HashMap<String, Vec<Vec<rustsat::types::Lit>>>> {
    entity_states
        .iter()
        .map(|(entity_name, state)| {
            (
                entity_name.clone(),
                state
                    .field_encodings
                    .iter()
                    .map(|(field_name, encoding)| {
                        (field_name.clone(), encoding.state_lits[state_idx].clone())
                    })
                    .collect(),
            )
        })
        .collect()
}

fn encode_projection_matches_atom(
    projection: &RelProjection,
    atom: &RelAtomRef,
    assignment: &HashMap<String, (String, usize)>,
    entity_states: &HashMap<String, EntityStateEncoding>,
    sat: &mut SatInstance,
    state_idx: usize,
) -> Result<rustsat::types::Lit, String> {
    match projection {
        RelProjection::Entity { binding, entity } => {
            let Some((assigned_entity, slot)) = assignment.get(binding) else {
                return Ok(const_lit(sat, false));
            };
            let RelAtomRef::EntitySlot {
                entity: atom_entity,
                slot: atom_slot,
            } = atom
            else {
                return Ok(const_lit(sat, false));
            };
            Ok(const_lit(
                sat,
                assigned_entity == entity && atom_entity == entity && atom_slot == slot,
            ))
        }
        RelProjection::Field {
            binding,
            entity,
            field,
        } => {
            let Some((assigned_entity, slot)) = assignment.get(binding) else {
                return Ok(const_lit(sat, false));
            };
            let RelAtomRef::Value(value) = atom else {
                return Ok(const_lit(sat, false));
            };
            if assigned_entity != entity {
                return Ok(const_lit(sat, false));
            }
            let state = entity_states
                .get(entity)
                .ok_or_else(|| format!("missing relational entity state for `{entity}`"))?;
            let encoding = state
                .field_encodings
                .get(field)
                .ok_or_else(|| format!("missing relational field `{entity}.{field}`"))?;
            let Some(value_idx) = encoding
                .values
                .iter()
                .position(|candidate| candidate == value)
            else {
                return Ok(const_lit(sat, false));
            };
            Ok(encoding.state_lits[state_idx][*slot][value_idx])
        }
    }
}

fn add_active_prefix_symmetry_breaking(
    sat: &mut SatInstance,
    entity_states: &HashMap<String, EntityStateEncoding>,
) -> usize {
    let mut added = 0;
    for state in entity_states.values() {
        if state.slot_count < 2 {
            continue;
        }
        for active_slots in &state.active_by_state {
            for slot in 0..(state.slot_count - 1) {
                sat.add_binary(!active_slots[slot + 1], active_slots[slot]);
                added += 1;
            }
        }
    }
    added
}

fn encode_scoped_quantified_snapshot(
    bindings: &[RelQuantBinding],
    pred: &RelScopedPred,
    entity_states: &HashMap<String, EntityStateEncoding>,
    sat: &mut SatInstance,
    state_idx: usize,
    index: usize,
    assignment: &mut HashMap<String, (String, usize)>,
) -> Result<rustsat::types::Lit, String> {
    if index == bindings.len() {
        let mut binding_slots = HashMap::new();
        for (var, (entity, slot)) in assignment.iter() {
            let state = entity_states
                .get(entity)
                .ok_or_else(|| format!("missing relational entity state for `{entity}`"))?;
            let slots = (0..state.slot_count)
                .map(|candidate| const_lit(sat, candidate == *slot))
                .collect::<Vec<_>>();
            binding_slots.insert(var.clone(), (entity.clone(), slots));
        }
        let current_fields: HashMap<String, HashMap<String, Vec<Vec<rustsat::types::Lit>>>> =
            entity_states
                .iter()
                .map(|(entity_name, state)| {
                    (
                        entity_name.clone(),
                        state
                            .field_encodings
                            .iter()
                            .map(|(field_name, encoding)| {
                                (field_name.clone(), encoding.state_lits[state_idx].clone())
                            })
                            .collect(),
                    )
                })
                .collect();
        return encode_scoped_pred_with_bindings(
            sat,
            pred,
            &binding_slots,
            &current_fields,
            entity_states,
        );
    }

    let binding = &bindings[index];
    let state = entity_states
        .get(&binding.entity)
        .ok_or_else(|| format!("missing relational entity state for `{}`", binding.entity))?;
    let mut cases = Vec::with_capacity(state.slot_count);
    for slot in 0..state.slot_count {
        let active = state.active_by_state[state_idx][slot];
        assignment.insert(binding.var.clone(), (binding.entity.clone(), slot));
        let body = encode_scoped_quantified_snapshot(
            bindings,
            pred,
            entity_states,
            sat,
            state_idx,
            index + 1,
            assignment,
        )?;
        assignment.remove(&binding.var);
        cases.push(match binding.quantifier {
            RelQuantifier::Exists => and_lit(sat, &[active, body])?,
            RelQuantifier::Forall => or_lit(sat, &[!active, body])?,
        });
    }
    match binding.quantifier {
        RelQuantifier::Exists => or_lit(sat, &cases),
        RelQuantifier::Forall => and_lit(sat, &cases),
    }
}

fn encode_rel_pred_for_slot(
    pred: &RelPred,
    field_encodings: &HashMap<String, FieldDomainEncoding>,
    state_idx: usize,
    slot: usize,
    sat: &mut SatInstance,
) -> Result<rustsat::types::Lit, String> {
    match pred {
        RelPred::True => Ok(const_lit(sat, true)),
        RelPred::Eq { field, value } => {
            let Some(encoding) = field_encodings.get(field) else {
                return Ok(const_lit(sat, false));
            };
            let Some(value_idx) = encoding
                .values
                .iter()
                .position(|candidate| candidate == value)
            else {
                return Ok(const_lit(sat, false));
            };
            Ok(encoding.state_lits[state_idx][slot][value_idx])
        }
        RelPred::Cmp { field, op, value } => {
            let Some(encoding) = field_encodings.get(field) else {
                return Ok(const_lit(sat, false));
            };
            let mut reasons = Vec::new();
            for (value_idx, candidate) in encoding.values.iter().enumerate() {
                if rel_cmp_values(*op, candidate, value) {
                    reasons.push(encoding.state_lits[state_idx][slot][value_idx]);
                }
            }
            if reasons.is_empty() {
                Ok(const_lit(sat, false))
            } else {
                or_lit(sat, &reasons)
            }
        }
        RelPred::And(left, right) => {
            let left_lit = encode_rel_pred_for_slot(left, field_encodings, state_idx, slot, sat)?;
            let right_lit = encode_rel_pred_for_slot(right, field_encodings, state_idx, slot, sat)?;
            and_lit(sat, &[left_lit, right_lit])
        }
        RelPred::Or(left, right) => {
            let left_lit = encode_rel_pred_for_slot(left, field_encodings, state_idx, slot, sat)?;
            let right_lit = encode_rel_pred_for_slot(right, field_encodings, state_idx, slot, sat)?;
            or_lit(sat, &[left_lit, right_lit])
        }
        RelPred::Not(inner) => Ok(!encode_rel_pred_for_slot(
            inner,
            field_encodings,
            state_idx,
            slot,
            sat,
        )?),
    }
}

fn encode_scoped_pred_with_bindings(
    sat: &mut SatInstance,
    pred: &RelScopedPred,
    binding_slots: &HashMap<String, (String, Vec<rustsat::types::Lit>)>,
    current_fields: &HashMap<String, HashMap<String, Vec<Vec<rustsat::types::Lit>>>>,
    entity_states: &HashMap<String, EntityStateEncoding>,
) -> Result<rustsat::types::Lit, String> {
    match pred {
        RelScopedPred::True => Ok(const_lit(sat, true)),
        RelScopedPred::Eq {
            binding,
            field,
            value,
        } => {
            let Some((entity, slots)) = binding_slots.get(binding) else {
                return Ok(const_lit(sat, false));
            };
            let Some(binding_state) = entity_states.get(entity) else {
                return Ok(const_lit(sat, false));
            };
            let Some(prev_field_slots) = current_fields
                .get(entity)
                .and_then(|fields| fields.get(field))
            else {
                return Ok(const_lit(sat, false));
            };
            let Some(encoding) = binding_state.field_encodings.get(field) else {
                return Ok(const_lit(sat, false));
            };
            let Some(value_idx) = encoding
                .values
                .iter()
                .position(|candidate| candidate == value)
            else {
                return Ok(const_lit(sat, false));
            };
            let mut reasons = Vec::new();
            for (slot_idx, slot_lit) in slots.iter().enumerate() {
                reasons.push(and_lit(
                    sat,
                    &[*slot_lit, prev_field_slots[slot_idx][value_idx]],
                )?);
            }
            or_lit(sat, &reasons)
        }
        RelScopedPred::Cmp {
            binding,
            field,
            op,
            value,
        } => {
            let Some((entity, slots)) = binding_slots.get(binding) else {
                return Ok(const_lit(sat, false));
            };
            let Some(binding_state) = entity_states.get(entity) else {
                return Ok(const_lit(sat, false));
            };
            let Some(prev_field_slots) = current_fields
                .get(entity)
                .and_then(|fields| fields.get(field))
            else {
                return Ok(const_lit(sat, false));
            };
            let Some(encoding) = binding_state.field_encodings.get(field) else {
                return Ok(const_lit(sat, false));
            };
            let mut reasons = Vec::new();
            for (slot_idx, slot_lit) in slots.iter().enumerate() {
                for (value_idx, candidate) in encoding.values.iter().enumerate() {
                    if rel_cmp_values(*op, candidate, value) {
                        reasons.push(and_lit(
                            sat,
                            &[*slot_lit, prev_field_slots[slot_idx][value_idx]],
                        )?);
                    }
                }
            }
            if reasons.is_empty() {
                Ok(const_lit(sat, false))
            } else {
                or_lit(sat, &reasons)
            }
        }
        RelScopedPred::EqBindings {
            left_binding,
            left_field,
            right_binding,
            right_field,
        } => {
            let Some((left_entity, left_slots)) = binding_slots.get(left_binding) else {
                return Ok(const_lit(sat, false));
            };
            let Some((right_entity, right_slots)) = binding_slots.get(right_binding) else {
                return Ok(const_lit(sat, false));
            };
            let Some(left_state) = entity_states.get(left_entity) else {
                return Ok(const_lit(sat, false));
            };
            let Some(right_state) = entity_states.get(right_entity) else {
                return Ok(const_lit(sat, false));
            };
            let Some(left_field_slots) = current_fields
                .get(left_entity)
                .and_then(|fields| fields.get(left_field))
            else {
                return Ok(const_lit(sat, false));
            };
            let Some(right_field_slots) = current_fields
                .get(right_entity)
                .and_then(|fields| fields.get(right_field))
            else {
                return Ok(const_lit(sat, false));
            };
            let Some(left_encoding) = left_state.field_encodings.get(left_field) else {
                return Ok(const_lit(sat, false));
            };
            let Some(right_encoding) = right_state.field_encodings.get(right_field) else {
                return Ok(const_lit(sat, false));
            };
            let mut reasons = Vec::new();
            for (left_slot_idx, left_slot_lit) in left_slots.iter().enumerate() {
                for (right_slot_idx, right_slot_lit) in right_slots.iter().enumerate() {
                    for (left_value_idx, left_value) in left_encoding.values.iter().enumerate() {
                        let Some(right_value_idx) = right_encoding
                            .values
                            .iter()
                            .position(|candidate| candidate == left_value)
                        else {
                            continue;
                        };
                        reasons.push(and_lit(
                            sat,
                            &[
                                *left_slot_lit,
                                *right_slot_lit,
                                left_field_slots[left_slot_idx][left_value_idx],
                                right_field_slots[right_slot_idx][right_value_idx],
                            ],
                        )?);
                    }
                }
            }
            if reasons.is_empty() {
                Ok(const_lit(sat, false))
            } else {
                or_lit(sat, &reasons)
            }
        }
        RelScopedPred::CmpBindings {
            left_binding,
            left_field,
            op,
            right_binding,
            right_field,
        } => {
            let Some((left_entity, left_slots)) = binding_slots.get(left_binding) else {
                return Ok(const_lit(sat, false));
            };
            let Some((right_entity, right_slots)) = binding_slots.get(right_binding) else {
                return Ok(const_lit(sat, false));
            };
            let Some(left_state) = entity_states.get(left_entity) else {
                return Ok(const_lit(sat, false));
            };
            let Some(right_state) = entity_states.get(right_entity) else {
                return Ok(const_lit(sat, false));
            };
            let Some(left_field_slots) = current_fields
                .get(left_entity)
                .and_then(|fields| fields.get(left_field))
            else {
                return Ok(const_lit(sat, false));
            };
            let Some(right_field_slots) = current_fields
                .get(right_entity)
                .and_then(|fields| fields.get(right_field))
            else {
                return Ok(const_lit(sat, false));
            };
            let Some(left_encoding) = left_state.field_encodings.get(left_field) else {
                return Ok(const_lit(sat, false));
            };
            let Some(right_encoding) = right_state.field_encodings.get(right_field) else {
                return Ok(const_lit(sat, false));
            };
            let mut reasons = Vec::new();
            for (left_slot_idx, left_slot_lit) in left_slots.iter().enumerate() {
                for (right_slot_idx, right_slot_lit) in right_slots.iter().enumerate() {
                    for (left_value_idx, left_value) in left_encoding.values.iter().enumerate() {
                        for (right_value_idx, right_value) in
                            right_encoding.values.iter().enumerate()
                        {
                            if rel_cmp_values(*op, left_value, right_value) {
                                reasons.push(and_lit(
                                    sat,
                                    &[
                                        *left_slot_lit,
                                        *right_slot_lit,
                                        left_field_slots[left_slot_idx][left_value_idx],
                                        right_field_slots[right_slot_idx][right_value_idx],
                                    ],
                                )?);
                            }
                        }
                    }
                }
            }
            if reasons.is_empty() {
                Ok(const_lit(sat, false))
            } else {
                or_lit(sat, &reasons)
            }
        }
        RelScopedPred::And(left, right) => {
            let left_lit = encode_scoped_pred_with_bindings(
                sat,
                left,
                binding_slots,
                current_fields,
                entity_states,
            )?;
            let right_lit = encode_scoped_pred_with_bindings(
                sat,
                right,
                binding_slots,
                current_fields,
                entity_states,
            )?;
            and_lit(sat, &[left_lit, right_lit])
        }
        RelScopedPred::Or(left, right) => {
            let left_lit = encode_scoped_pred_with_bindings(
                sat,
                left,
                binding_slots,
                current_fields,
                entity_states,
            )?;
            let right_lit = encode_scoped_pred_with_bindings(
                sat,
                right,
                binding_slots,
                current_fields,
                entity_states,
            )?;
            or_lit(sat, &[left_lit, right_lit])
        }
        RelScopedPred::Not(inner) => Ok(!encode_scoped_pred_with_bindings(
            sat,
            inner,
            binding_slots,
            current_fields,
            entity_states,
        )?),
    }
}

fn rel_cmp_values(op: RelCmpOp, left: &SimpleValue, right: &SimpleValue) -> bool {
    match (left, right) {
        (SimpleValue::Int(left), SimpleValue::Int(right)) => match op {
            RelCmpOp::Lt => left < right,
            RelCmpOp::Le => left <= right,
            RelCmpOp::Gt => left > right,
            RelCmpOp::Ge => left >= right,
        },
        _ => false,
    }
}

fn const_lit(sat: &mut SatInstance, value: bool) -> rustsat::types::Lit {
    let lit = sat.new_lit();
    sat.add_unit(if value { lit } else { !lit });
    lit
}

fn and_lit(
    sat: &mut SatInstance,
    lits: &[rustsat::types::Lit],
) -> Result<rustsat::types::Lit, String> {
    if lits.is_empty() {
        return Ok(const_lit(sat, true));
    }
    if lits.len() == 1 {
        return Ok(lits[0]);
    }
    let out = sat.new_lit();
    for &lit in lits {
        sat.add_binary(!out, lit);
    }
    let mut clause = vec![out];
    clause.extend(lits.iter().map(|lit| !*lit));
    sat.add_clause(clause.as_slice().into());
    Ok(out)
}

fn or_lit(
    sat: &mut SatInstance,
    lits: &[rustsat::types::Lit],
) -> Result<rustsat::types::Lit, String> {
    if lits.is_empty() {
        return Ok(const_lit(sat, false));
    }
    if lits.len() == 1 {
        return Ok(lits[0]);
    }
    let out = sat.new_lit();
    for &lit in lits {
        sat.add_binary(!lit, out);
    }
    let mut clause = vec![!out];
    clause.extend(lits.iter().copied());
    sat.add_clause(clause.as_slice().into());
    Ok(out)
}

fn simple_witness_value(value: &SimpleValue) -> WitnessValue {
    match value {
        SimpleValue::Bool(value) => WitnessValue::Bool(*value),
        SimpleValue::Int(value) => WitnessValue::Int(*value),
        SimpleValue::Ctor(enum_name, variant) => WitnessValue::EnumVariant {
            enum_name: enum_name.clone(),
            variant: variant.clone(),
        },
    }
}

fn build_relational_verify_counterexample_witness(
    solver: &BasicSolver,
    entity_states: &HashMap<String, EntityStateEncoding>,
    bound: usize,
) -> Result<rel::RelationalWitness, String> {
    let mut states = Vec::with_capacity(bound + 1);
    for step in 0..=bound {
        states.push(build_relational_verify_state(solver, entity_states, step)?);
    }
    let temporal = rel::TemporalRelationalWitness::new(states, None)
        .map_err(|err| format!("relational temporal witness validation failed: {err}"))?;
    rel::RelationalWitness::temporal(temporal)
        .map_err(|err| format!("relational witness validation failed: {err}"))
}

fn build_relational_verify_state(
    solver: &BasicSolver,
    entity_states: &HashMap<String, EntityStateEncoding>,
    state_idx: usize,
) -> Result<rel::RelationalState, String> {
    let mut builder = rel::RelationalState::builder();
    for (entity_name, state) in entity_states {
        let mut field_tuples: HashMap<String, Vec<rel::TupleValue>> = HashMap::new();
        for (slot, &active_lit) in state.active_by_state[state_idx]
            .iter()
            .enumerate()
            .take(state.slot_count)
        {
            if solver
                .lit_val(active_lit)
                .map_err(|err| format!("RustSAT model access failed: {err}"))?
                != TernaryVal::True
            {
                continue;
            }

            let slot_ref = EntitySlotRef::new(entity_name.to_owned(), slot);
            builder = builder
                .extent_member(entity_name.to_owned(), slot_ref.clone())
                .map_err(|err| format!("generated relational extent member is invalid: {err}"))?;

            for (field, encoding) in &state.field_encodings {
                let Some(value) = encoding.state_lits[state_idx][slot]
                    .iter()
                    .enumerate()
                    .find_map(|(value_idx, &lit)| match solver.lit_val(lit) {
                        Ok(TernaryVal::True) => Some(encoding.values[value_idx].clone()),
                        _ => None,
                    })
                else {
                    return Err(format!(
                        "missing concrete RustSAT value for `{entity_name}.{field}` at state {state_idx}, slot {slot}"
                    ));
                };
                field_tuples
                    .entry(field.clone())
                    .or_default()
                    .push(rel::TupleValue::new(vec![
                        WitnessValue::SlotRef(slot_ref.clone()),
                        simple_witness_value(&value),
                    ]));
            }
        }

        for (field, tuples) in field_tuples {
            let mut relation = rel::RelationInstance::builder(2);
            for tuple in tuples {
                relation = relation
                    .tuple(tuple)
                    .map_err(|err| format!("generated relational field tuple is invalid: {err}"))?;
            }
            builder = builder
                .field_relation(
                    entity_name.to_owned(),
                    field,
                    relation.build().map_err(|err| {
                        format!("generated relational field relation is invalid: {err}")
                    })?,
                )
                .map_err(|err| format!("generated relational field relation is invalid: {err}"))?;
        }
    }

    builder
        .build()
        .map_err(|err| format!("relational state projection failed validation: {err}"))
}

fn slot_predicate_matches(
    expr: &IRExpr,
    var: &str,
    field_values: &HashMap<String, SimpleValue>,
) -> bool {
    match expr {
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpAnd" => {
            slot_predicate_matches(left, var, field_values)
                && slot_predicate_matches(right, var, field_values)
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpOr" => {
            slot_predicate_matches(left, var, field_values)
                || slot_predicate_matches(right, var, field_values)
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpEq" => {
            let (IRExpr::Field { expr, field, .. }, value_expr) = (&**left, &**right) else {
                return false;
            };
            let IRExpr::Var { name, .. } = &**expr else {
                return false;
            };
            if !var.is_empty() && name != var {
                return false;
            }
            let Some(expected) = simple_value(value_expr) else {
                return false;
            };
            field_values.get(field) == Some(&expected)
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn solve_instance(sat: SatInstance) -> SolverResult {
        let (cnf, _) = sat.into_cnf();
        let mut solver = BasicSolver::default();
        solver.add_cnf(cnf).expect("test CNF should load");
        solver.solve().expect("test solve should complete")
    }

    #[test]
    fn active_prefix_symmetry_breaking_prunes_non_prefix_slot_assignments() {
        let mut unsymmetrized = SatInstance::new();
        let inactive_first = unsymmetrized.new_lit();
        let active_second = unsymmetrized.new_lit();
        unsymmetrized.add_unit(!inactive_first);
        unsymmetrized.add_unit(active_second);
        assert!(matches!(solve_instance(unsymmetrized), SolverResult::Sat));

        let mut symmetrized = SatInstance::new();
        let inactive_first = symmetrized.new_lit();
        let active_second = symmetrized.new_lit();
        let entity_states = HashMap::from([(
            "Order".to_owned(),
            EntityStateEncoding {
                slot_count: 2,
                active_by_state: vec![vec![inactive_first, active_second]],
                field_encodings: HashMap::new(),
            },
        )]);
        let added = add_active_prefix_symmetry_breaking(&mut symmetrized, &entity_states);
        assert_eq!(added, 1);
        symmetrized.add_unit(!inactive_first);
        symmetrized.add_unit(active_second);
        assert!(matches!(solve_instance(symmetrized), SolverResult::Unsat));
    }
}
