//! Backend-neutral transition-system obligation routing.
//!
//! The current implementation still uses the existing IC3/CHC encoding and
//! backend path, but callers should depend on this obligation shape rather than
//! reaching directly into solver-specific entry points.

use std::collections::HashMap;

use crate::ir::types::{
    IRAssumptionSet, IRCommandRef, IREntity, IRExpr, IRProgram, IRSystem, IRTheorem, IRVerify,
};

use super::context::VerifyContext;
use super::defenv;
use super::harness::{
    create_slot_pool_with_systems, domain_constraints, initial_state_constraints, lasso_loopback,
    symmetry_breaking_constraints, try_fairness_constraints, try_system_field_initial_constraints,
    try_transition_constraints_with_fire, FireTracking, LassoLoop, SlotPool,
};
use super::ic3;
use super::scope::{
    compute_theorem_scope, compute_verify_scope, select_verify_relevant, VerifyStoreRange,
};
use super::smt::Bool;
use super::solver::{active_solver_family, SolverFamily};
use super::sygus;
use super::temporal::{CompiledTemporalFormula, LivenessPattern};
use super::walkers::count_entity_quantifiers;

#[derive(Debug, Clone)]
pub struct TransitionAssumptions {
    stutter: bool,
    weak_fair_event_keys: Vec<(String, String)>,
    strong_fair_event_keys: Vec<(String, String)>,
    per_tuple_fair_event_keys: Vec<(String, String)>,
}

impl TransitionAssumptions {
    fn from_ir(set: &IRAssumptionSet) -> Self {
        Self {
            stutter: set.stutter,
            weak_fair_event_keys: set
                .weak_fair
                .iter()
                .map(|event| (event.system.clone(), event.command.clone()))
                .collect(),
            strong_fair_event_keys: set
                .strong_fair
                .iter()
                .map(|event| (event.system.clone(), event.command.clone()))
                .collect(),
            per_tuple_fair_event_keys: set
                .per_tuple
                .iter()
                .map(|event| (event.system.clone(), event.command.clone()))
                .collect(),
        }
    }

    pub fn as_ir_assumption_set(&self) -> IRAssumptionSet {
        IRAssumptionSet {
            stutter: self.stutter,
            weak_fair: self
                .weak_fair_event_keys
                .iter()
                .map(|(system, command)| IRCommandRef {
                    system: system.clone(),
                    command: command.clone(),
                })
                .collect(),
            strong_fair: self
                .strong_fair_event_keys
                .iter()
                .map(|(system, command)| IRCommandRef {
                    system: system.clone(),
                    command: command.clone(),
                })
                .collect(),
            per_tuple: self
                .per_tuple_fair_event_keys
                .iter()
                .map(|(system, command)| IRCommandRef {
                    system: system.clone(),
                    command: command.clone(),
                })
                .collect(),
        }
    }

    pub fn stutter(&self) -> bool {
        self.stutter
    }

    pub fn weak_fair_event_keys(&self) -> &[(String, String)] {
        &self.weak_fair_event_keys
    }

    pub fn strong_fair_event_keys(&self) -> &[(String, String)] {
        &self.strong_fair_event_keys
    }

    pub fn per_tuple_fair_event_keys(&self) -> &[(String, String)] {
        &self.per_tuple_fair_event_keys
    }

    pub fn all_fair_event_keys(&self) -> Vec<(String, String)> {
        let mut out = self.weak_fair_event_keys.clone();
        for event in &self.strong_fair_event_keys {
            if !out.contains(event) {
                out.push(event.clone());
            }
        }
        out
    }
}

#[derive(Clone)]
pub struct TransitionSystemSpec<'a> {
    pub ir: &'a IRProgram,
    pub vctx: &'a VerifyContext,
    selected_system_names: Vec<String>,
    system_names: Vec<String>,
    slots_per_entity: HashMap<String, usize>,
    bound: usize,
    store_ranges: HashMap<String, VerifyStoreRange>,
    assumptions: TransitionAssumptions,
    relevant_entities: Vec<IREntity>,
    relevant_systems: Vec<IRSystem>,
}

impl<'a> TransitionSystemSpec<'a> {
    pub fn from_selected(
        ir: &'a IRProgram,
        vctx: &'a VerifyContext,
        selected_system_names: Vec<String>,
        relevant_entities: Vec<IREntity>,
        relevant_systems: Vec<IRSystem>,
        slots_per_entity: HashMap<String, usize>,
        bound: usize,
        store_ranges: HashMap<String, VerifyStoreRange>,
        assumption_set: &IRAssumptionSet,
    ) -> Option<Self> {
        let system_names: Vec<String> = relevant_systems.iter().map(|s| s.name.clone()).collect();
        if system_names.is_empty() {
            return None;
        }
        Some(Self {
            ir,
            vctx,
            selected_system_names,
            system_names,
            slots_per_entity,
            bound,
            store_ranges,
            assumptions: TransitionAssumptions::from_ir(assumption_set),
            relevant_entities,
            relevant_systems,
        })
    }

    fn from_verify_scope_parts(
        ir: &'a IRProgram,
        vctx: &'a VerifyContext,
        selected_system_names: Vec<String>,
        system_names: Vec<String>,
        slots_per_entity: HashMap<String, usize>,
        bound: usize,
        store_ranges: HashMap<String, VerifyStoreRange>,
        assumptions: TransitionAssumptions,
    ) -> Option<Self> {
        if system_names.is_empty() {
            return None;
        }
        let (relevant_entities, relevant_systems) =
            select_verify_relevant(ir, &slots_per_entity, &system_names);
        Some(Self {
            ir,
            vctx,
            selected_system_names,
            system_names,
            slots_per_entity,
            bound,
            store_ranges,
            assumptions,
            relevant_entities,
            relevant_systems,
        })
    }

    pub fn for_verify(
        ir: &'a IRProgram,
        vctx: &'a VerifyContext,
        verify_block: &IRVerify,
        defs: &defenv::DefEnv,
    ) -> Option<Self> {
        let (mut slots_per_entity, system_names, bound, store_ranges) =
            compute_verify_scope(ir, verify_block);
        if system_names.is_empty() {
            return None;
        }
        for assert_expr in &verify_block.asserts {
            let expanded = super::expand_through_defs(assert_expr, defs);
            let mut counts: HashMap<String, usize> = HashMap::new();
            count_entity_quantifiers(&expanded, &mut counts);
            for (entity, count) in counts {
                let min_slots = count + 1;
                if let Some(existing) = slots_per_entity.get_mut(&entity) {
                    *existing = (*existing).max(min_slots);
                }
            }
        }
        Self::from_verify_scope_parts(
            ir,
            vctx,
            verify_block
                .systems
                .iter()
                .map(|sys| sys.name.clone())
                .collect(),
            system_names,
            slots_per_entity,
            bound,
            store_ranges,
            TransitionAssumptions::from_ir(&verify_block.assumption_set),
        )
    }

    pub fn for_verify_shallow(
        ir: &'a IRProgram,
        vctx: &'a VerifyContext,
        verify_block: &IRVerify,
    ) -> Option<Self> {
        let (slots_per_entity, system_names, bound, store_ranges) =
            compute_verify_scope(ir, verify_block);
        Self::from_verify_scope_parts(
            ir,
            vctx,
            verify_block
                .systems
                .iter()
                .map(|sys| sys.name.clone())
                .collect(),
            system_names,
            slots_per_entity,
            bound,
            store_ranges,
            TransitionAssumptions::from_ir(&verify_block.assumption_set),
        )
    }

    pub fn for_theorem(
        ir: &'a IRProgram,
        vctx: &'a VerifyContext,
        theorem: &IRTheorem,
        defs: &defenv::DefEnv,
    ) -> Option<Self> {
        let quantifier_exprs: Vec<&IRExpr> = theorem.shows.iter().collect();
        let (slots_per_entity, system_names, _required_slots) =
            compute_theorem_scope(ir, theorem, &quantifier_exprs, defs);
        if system_names.is_empty() {
            return None;
        }
        let (relevant_entities, relevant_systems) =
            select_verify_relevant(ir, &slots_per_entity, &system_names);

        Some(Self {
            ir,
            vctx,
            selected_system_names: theorem.systems.clone(),
            system_names,
            slots_per_entity,
            bound: 0,
            store_ranges: HashMap::new(),
            assumptions: TransitionAssumptions::from_ir(&theorem.assumption_set),
            relevant_entities,
            relevant_systems,
        })
    }

    pub fn system_names(&self) -> &[String] {
        &self.system_names
    }

    pub fn selected_system_names(&self) -> &[String] {
        &self.selected_system_names
    }

    pub fn slots_per_entity(&self) -> &HashMap<String, usize> {
        &self.slots_per_entity
    }

    pub fn assumptions(&self) -> &TransitionAssumptions {
        &self.assumptions
    }

    pub fn bound(&self) -> usize {
        self.bound
    }

    pub fn store_ranges(&self) -> &HashMap<String, VerifyStoreRange> {
        &self.store_ranges
    }

    pub fn relevant_entities(&self) -> &[IREntity] {
        &self.relevant_entities
    }

    pub fn relevant_systems(&self) -> &[IRSystem] {
        &self.relevant_systems
    }
}

#[derive(Clone)]
pub struct TransitionSafetySpec<'a> {
    system: TransitionSystemSpec<'a>,
    step_properties: Vec<IRExpr>,
}

impl<'a> TransitionSafetySpec<'a> {
    pub fn for_verify(
        ir: &'a IRProgram,
        vctx: &'a VerifyContext,
        verify_block: &IRVerify,
        defs: &defenv::DefEnv,
    ) -> Option<Self> {
        let system = TransitionSystemSpec::for_verify(ir, vctx, verify_block, defs)?;
        let step_properties = verify_block
            .asserts
            .iter()
            .map(|assert_expr| {
                let expanded = super::expand_through_defs(assert_expr, defs);
                match expanded {
                    IRExpr::Always { body, .. } => *body,
                    other => other,
                }
            })
            .collect();
        Some(Self {
            system,
            step_properties,
        })
    }

    pub fn for_theorem(
        ir: &'a IRProgram,
        vctx: &'a VerifyContext,
        theorem: &IRTheorem,
        defs: &defenv::DefEnv,
    ) -> Option<Self> {
        let system = TransitionSystemSpec::for_theorem(ir, vctx, theorem, defs)?;
        let step_properties = theorem
            .shows
            .iter()
            .map(|show_expr| super::expand_through_defs(show_expr, defs))
            .collect();
        Some(Self {
            system,
            step_properties,
        })
    }

    pub fn system(&self) -> &TransitionSystemSpec<'a> {
        &self.system
    }

    pub fn step_properties(&self) -> &[IRExpr] {
        &self.step_properties
    }

    pub fn step_property(&self, index: usize) -> Option<&IRExpr> {
        self.step_properties.get(index)
    }

    pub fn combined_step_property(&self) -> Option<IRExpr> {
        let mut iter = self.step_properties.iter().cloned();
        let first = iter.next()?;
        Some(iter.fold(first, |left, right| IRExpr::BinOp {
            op: "OpAnd".to_owned(),
            left: Box::new(left),
            right: Box::new(right),
            ty: crate::ir::types::IRType::Bool,
            span: None,
        }))
    }

    pub fn obligation(&self, property_index: usize, timeout_ms: u64) -> TransitionObligation<'a> {
        TransitionObligation::SystemSafety {
            safety: self.clone(),
            property_index,
            timeout_ms,
        }
    }
}

#[derive(Clone)]
pub struct TransitionVerifySpec<'a> {
    system: TransitionSystemSpec<'a>,
    compiled_asserts: Vec<CompiledTemporalFormula>,
    safety: TransitionSafetySpec<'a>,
}

impl<'a> TransitionVerifySpec<'a> {
    pub fn for_verify(
        ir: &'a IRProgram,
        vctx: &'a VerifyContext,
        verify_block: &IRVerify,
        defs: &defenv::DefEnv,
    ) -> Option<Self> {
        let system = TransitionSystemSpec::for_verify(ir, vctx, verify_block, defs)?;
        let compiled_asserts: Vec<CompiledTemporalFormula> = verify_block
            .asserts
            .iter()
            .map(|assert_expr| {
                let expanded = super::expand_through_defs(assert_expr, defs);
                let temporal_scope = match expanded {
                    IRExpr::Always { .. } => expanded,
                    other => IRExpr::Always {
                        body: Box::new(other),
                        span: None,
                    },
                };
                CompiledTemporalFormula::from_expanded(temporal_scope)
            })
            .collect();
        let step_properties = compiled_asserts
            .iter()
            .map(|compiled| match compiled.expanded().clone() {
                IRExpr::Always { body, .. } => *body,
                other => other,
            })
            .collect();
        Some(Self {
            system: system.clone(),
            compiled_asserts,
            safety: TransitionSafetySpec {
                system,
                step_properties,
            },
        })
    }

    pub fn system(&self) -> &TransitionSystemSpec<'a> {
        &self.system
    }

    pub fn safety(&self) -> &TransitionSafetySpec<'a> {
        &self.safety
    }

    pub fn compiled_asserts(&self) -> &[CompiledTemporalFormula] {
        &self.compiled_asserts
    }

    pub fn has_liveness(&self) -> bool {
        self.compiled_asserts
            .iter()
            .any(CompiledTemporalFormula::contains_liveness)
    }
}

#[derive(Clone)]
pub struct TransitionVerifyObligation<'a> {
    verify: TransitionVerifySpec<'a>,
    fair_event_keys: Vec<(String, String)>,
    liveness: Option<TransitionLivenessSpec<'a>>,
}

impl<'a> TransitionVerifyObligation<'a> {
    pub fn for_verify(
        ir: &'a IRProgram,
        vctx: &'a VerifyContext,
        verify_block: &IRVerify,
        defs: &defenv::DefEnv,
    ) -> Option<Self> {
        let verify = TransitionVerifySpec::for_verify(ir, vctx, verify_block, defs)?;
        let fair_event_keys = verify.system().assumptions().all_fair_event_keys();
        let liveness = TransitionLivenessSpec::from_verify_spec(verify.clone(), defs);
        Some(Self {
            verify,
            fair_event_keys,
            liveness,
        })
    }

    pub fn verify(&self) -> &TransitionVerifySpec<'a> {
        &self.verify
    }

    pub fn system(&self) -> &TransitionSystemSpec<'a> {
        self.verify.system()
    }

    pub fn safety(&self) -> &TransitionSafetySpec<'a> {
        self.verify.safety()
    }

    pub fn fair_event_keys(&self) -> &[(String, String)] {
        &self.fair_event_keys
    }

    pub fn liveness(&self) -> Option<&TransitionLivenessSpec<'a>> {
        self.liveness.as_ref()
    }

    pub fn has_liveness(&self) -> bool {
        self.verify.has_liveness()
    }

    pub fn has_supported_liveness(&self) -> bool {
        self.liveness.is_some()
    }

    pub fn deadlock_plan(&self) -> TransitionExecutionPlan<'a> {
        TransitionExecutionPlan::for_deadlock_probe(self.system().clone())
    }

    pub fn prefix_plan(&self, steps: usize) -> TransitionExecutionPlan<'a> {
        TransitionExecutionPlan::for_prefix_probe(self.system().clone(), steps)
    }

    pub fn bmc_plan(&self) -> TransitionExecutionPlan<'a> {
        TransitionExecutionPlan::for_bmc(self.system().clone(), self.system().bound())
    }

    pub fn lasso_plan(&self) -> TransitionExecutionPlan<'a> {
        TransitionExecutionPlan::for_lasso(self.system().clone(), self.system().bound())
    }
}

pub struct TransitionSmtEncoding<'a> {
    system: TransitionSystemSpec<'a>,
    pool: SlotPool,
    initial_constraints: Vec<Bool>,
    system_initial_constraints: Vec<Bool>,
    symmetry_constraints: Vec<Bool>,
    domain_constraints: Vec<Bool>,
    fire_tracking: FireTracking,
    lasso: Option<LassoLoop>,
    fairness_constraints: Vec<Bool>,
}

#[derive(Clone)]
pub struct TransitionExecutionPlan<'a> {
    system: TransitionSystemSpec<'a>,
    steps: usize,
    include_system_initial_constraints: bool,
    include_symmetry_constraints: bool,
    include_lasso_and_fairness: bool,
}

impl<'a> TransitionExecutionPlan<'a> {
    fn new(
        system: TransitionSystemSpec<'a>,
        steps: usize,
        include_system_initial_constraints: bool,
        include_symmetry_constraints: bool,
        include_lasso_and_fairness: bool,
    ) -> Self {
        Self {
            system,
            steps,
            include_system_initial_constraints,
            include_symmetry_constraints,
            include_lasso_and_fairness,
        }
    }

    pub fn for_deadlock_probe(system: TransitionSystemSpec<'a>) -> Self {
        Self::new(system, 1, false, false, false)
    }

    pub fn for_prefix_probe(system: TransitionSystemSpec<'a>, steps: usize) -> Self {
        Self::new(system, steps, true, false, false)
    }

    pub fn for_bmc(system: TransitionSystemSpec<'a>, steps: usize) -> Self {
        Self::new(system, steps, true, true, false)
    }

    pub fn for_lasso(system: TransitionSystemSpec<'a>, steps: usize) -> Self {
        Self::new(system, steps, true, true, true)
    }

    pub fn for_inductive_step(system: TransitionSystemSpec<'a>) -> Self {
        Self::new(system, 1, false, false, false)
    }

    pub fn system(&self) -> &TransitionSystemSpec<'a> {
        &self.system
    }

    pub fn steps(&self) -> usize {
        self.steps
    }

    pub fn include_system_initial_constraints(&self) -> bool {
        self.include_system_initial_constraints
    }

    pub fn include_symmetry_constraints(&self) -> bool {
        self.include_symmetry_constraints
    }

    pub fn include_lasso_and_fairness(&self) -> bool {
        self.include_lasso_and_fairness
    }
}

impl<'a> TransitionSmtEncoding<'a> {
    pub fn from_plan(plan: TransitionExecutionPlan<'a>) -> Result<Self, String> {
        let system = plan.system;
        let steps = plan.steps;
        let assumption_set = system.assumptions().as_ir_assumption_set();
        let pool = create_slot_pool_with_systems(
            system.relevant_entities(),
            system.slots_per_entity(),
            steps,
            system.relevant_systems(),
        );
        let initial_constraints = initial_state_constraints(&pool);
        let system_initial_constraints = if plan.include_system_initial_constraints {
            let mut out = Vec::new();
            for sys in system.relevant_systems() {
                out.extend(try_system_field_initial_constraints(
                    &pool,
                    system.vctx,
                    sys,
                )?);
            }
            out
        } else {
            Vec::new()
        };
        let symmetry_constraints = if plan.include_symmetry_constraints {
            symmetry_breaking_constraints(&pool)
        } else {
            Vec::new()
        };
        let domain_constraints = domain_constraints(&pool, system.vctx, system.relevant_entities());
        let fire_tracking = try_transition_constraints_with_fire(
            &pool,
            system.vctx,
            system.relevant_entities(),
            system.relevant_systems(),
            steps,
            &assumption_set,
        )?;
        let (lasso, fairness_constraints) = if plan.include_lasso_and_fairness {
            let lasso =
                lasso_loopback(&pool, system.relevant_entities(), system.relevant_systems());
            let fairness_constraints = try_fairness_constraints(
                &pool,
                system.vctx,
                system.relevant_entities(),
                system.relevant_systems(),
                &fire_tracking,
                &lasso,
                &assumption_set,
            )?;
            (Some(lasso), fairness_constraints)
        } else {
            (None, Vec::new())
        };

        Ok(Self {
            system,
            pool,
            initial_constraints,
            system_initial_constraints,
            symmetry_constraints,
            domain_constraints,
            fire_tracking,
            lasso,
            fairness_constraints,
        })
    }

    pub fn for_deadlock_probe(system: TransitionSystemSpec<'a>) -> Result<Self, String> {
        Self::from_plan(TransitionExecutionPlan::for_deadlock_probe(system))
    }

    pub fn for_prefix_probe(
        system: TransitionSystemSpec<'a>,
        steps: usize,
    ) -> Result<Self, String> {
        Self::from_plan(TransitionExecutionPlan::for_prefix_probe(system, steps))
    }

    pub fn for_bmc(system: TransitionSystemSpec<'a>, steps: usize) -> Result<Self, String> {
        Self::from_plan(TransitionExecutionPlan::for_bmc(system, steps))
    }

    pub fn for_lasso(system: TransitionSystemSpec<'a>, steps: usize) -> Result<Self, String> {
        Self::from_plan(TransitionExecutionPlan::for_lasso(system, steps))
    }

    pub fn system(&self) -> &TransitionSystemSpec<'a> {
        &self.system
    }

    pub fn pool(&self) -> &SlotPool {
        &self.pool
    }

    pub fn initial_constraints(&self) -> &[Bool] {
        &self.initial_constraints
    }

    pub fn system_initial_constraints(&self) -> &[Bool] {
        &self.system_initial_constraints
    }

    pub fn symmetry_constraints(&self) -> &[Bool] {
        &self.symmetry_constraints
    }

    pub fn domain_constraints(&self) -> &[Bool] {
        &self.domain_constraints
    }

    pub fn fire_tracking(&self) -> &FireTracking {
        &self.fire_tracking
    }

    pub fn lasso(&self) -> Option<&LassoLoop> {
        self.lasso.as_ref()
    }

    pub fn fairness_constraints(&self) -> &[Bool] {
        &self.fairness_constraints
    }
}

#[derive(Clone)]
pub struct TransitionLivenessMonitorRecipe {
    assert_index: usize,
    trigger: Option<IRExpr>,
    response: IRExpr,
    quant_var: Option<String>,
    quant_entity: Option<String>,
    slot_count: usize,
    is_oneshot: bool,
}

impl TransitionLivenessMonitorRecipe {
    fn from_pattern(
        assert_index: usize,
        pattern: &LivenessPattern,
        system: &TransitionSystemSpec<'_>,
    ) -> Self {
        let (trigger, response, quant_var, quant_entity) = match pattern {
            LivenessPattern::Response { trigger, response } => {
                (Some(trigger.clone()), response.clone(), None, None)
            }
            LivenessPattern::Recurrence { response }
            | LivenessPattern::Eventuality { response } => (None, response.clone(), None, None),
            LivenessPattern::Persistence { condition } => (None, condition.clone(), None, None),
            LivenessPattern::QuantifiedResponse {
                var,
                entity,
                trigger,
                response,
            } => (
                Some(trigger.clone()),
                response.clone(),
                Some(var.clone()),
                Some(entity.clone()),
            ),
            LivenessPattern::QuantifiedRecurrence {
                var,
                entity,
                response,
            }
            | LivenessPattern::QuantifiedEventuality {
                var,
                entity,
                response,
            } => (
                None,
                response.clone(),
                Some(var.clone()),
                Some(entity.clone()),
            ),
            LivenessPattern::QuantifiedPersistence {
                var,
                entity,
                condition,
            } => (
                None,
                condition.clone(),
                Some(var.clone()),
                Some(entity.clone()),
            ),
        };
        let slot_count = quant_entity
            .as_ref()
            .and_then(|entity| system.slots_per_entity().get(entity).copied())
            .unwrap_or(1);

        Self {
            assert_index,
            trigger,
            response,
            quant_var,
            quant_entity,
            slot_count,
            is_oneshot: pattern.is_oneshot(),
        }
    }

    pub fn assert_index(&self) -> usize {
        self.assert_index
    }

    pub fn trigger<'a>(&'a self, true_expr: &'a IRExpr) -> &'a IRExpr {
        self.trigger.as_ref().unwrap_or(true_expr)
    }

    pub fn response(&self) -> &IRExpr {
        &self.response
    }

    pub fn quantified_binding(&self) -> (Option<&str>, Option<&str>) {
        (self.quant_var.as_deref(), self.quant_entity.as_deref())
    }

    pub fn slot_count(&self) -> usize {
        self.slot_count
    }

    pub fn is_quantified(&self) -> bool {
        self.quant_entity.is_some()
    }

    pub fn is_oneshot(&self) -> bool {
        self.is_oneshot
    }
}

#[derive(Clone)]
pub struct TransitionLivenessSpec<'a> {
    verify: TransitionVerifySpec<'a>,
    patterns: Vec<(usize, LivenessPattern)>,
    safety_obligations: Vec<IRExpr>,
    recipes: Vec<TransitionLivenessMonitorRecipe>,
}

impl<'a> TransitionLivenessSpec<'a> {
    pub fn for_verify(
        ir: &'a IRProgram,
        vctx: &'a VerifyContext,
        verify_block: &IRVerify,
        defs: &defenv::DefEnv,
    ) -> Option<Self> {
        let verify = TransitionVerifySpec::for_verify(ir, vctx, verify_block, defs)?;
        Self::from_verify_spec(verify, defs)
    }

    fn from_verify_spec(verify: TransitionVerifySpec<'a>, _defs: &defenv::DefEnv) -> Option<Self> {
        let mut patterns = Vec::new();
        let mut safety_obligations = Vec::new();
        let mut has_unrecognized_liveness = false;
        for (i, compiled) in verify.compiled_asserts().iter().enumerate() {
            if compiled.contains_liveness() {
                if let Some(extraction) = compiled.extraction().cloned() {
                    patterns.push((i, extraction.pattern));
                    safety_obligations.extend(extraction.safety_conjuncts);
                } else {
                    has_unrecognized_liveness = true;
                }
            } else {
                safety_obligations.push(compiled.expanded().clone());
            }
        }
        if patterns.is_empty() || has_unrecognized_liveness {
            return None;
        }
        let recipes = patterns
            .iter()
            .map(|(assert_index, pattern)| {
                TransitionLivenessMonitorRecipe::from_pattern(
                    *assert_index,
                    pattern,
                    verify.system(),
                )
            })
            .collect();
        Some(Self {
            verify,
            patterns,
            safety_obligations,
            recipes,
        })
    }

    pub fn verify(&self) -> &TransitionVerifySpec<'a> {
        &self.verify
    }

    pub fn system(&self) -> &TransitionSystemSpec<'a> {
        self.verify.system()
    }

    pub fn patterns(&self) -> &[(usize, LivenessPattern)] {
        &self.patterns
    }

    pub fn pattern(&self, index: usize) -> Option<&LivenessPattern> {
        self.patterns.get(index).map(|(_, pattern)| pattern)
    }

    pub fn safety_obligations(&self) -> &[IRExpr] {
        &self.safety_obligations
    }

    pub fn has_quantified_patterns(&self) -> bool {
        self.recipes
            .iter()
            .any(TransitionLivenessMonitorRecipe::is_quantified)
    }

    pub fn recipes(&self) -> &[TransitionLivenessMonitorRecipe] {
        &self.recipes
    }

    pub fn recipe(&self, index: usize) -> Option<&TransitionLivenessMonitorRecipe> {
        self.recipes.get(index)
    }

    pub fn pattern_slot_count(&self, pattern_index: usize) -> Option<usize> {
        Some(self.recipe(pattern_index)?.slot_count())
    }

    pub fn obligation(
        &self,
        recipe_index: usize,
        target_slot: Option<usize>,
        timeout_ms: u64,
    ) -> TransitionObligation<'a> {
        TransitionObligation::SystemLiveness {
            liveness: self.clone(),
            recipe_index,
            target_slot,
            timeout_ms,
        }
    }
}

pub use super::ic3::{Ic3Result as TransitionResult, Ic3TraceStep as TransitionTraceStep};

/// A transition-system obligation, independent of the current backend.
pub enum TransitionObligation<'a> {
    SingleEntitySafety {
        entity: &'a IREntity,
        vctx: &'a VerifyContext,
        property: &'a IRExpr,
        timeout_ms: u64,
    },
    MultiSlotSafety {
        entity: &'a IREntity,
        vctx: &'a VerifyContext,
        property: &'a IRExpr,
        n_slots: usize,
        timeout_ms: u64,
    },
    SystemSafety {
        safety: TransitionSafetySpec<'a>,
        property_index: usize,
        timeout_ms: u64,
    },
    SystemLiveness {
        liveness: TransitionLivenessSpec<'a>,
        recipe_index: usize,
        target_slot: Option<usize>,
        timeout_ms: u64,
    },
}

/// Transition-system backends consume backend-neutral obligations and return the
/// shared transition result shape.
pub trait TransitionBackend {
    fn solve(obligation: TransitionObligation<'_>) -> TransitionResult;
}

/// Current transition backend: the existing IC3/CHC path.
pub struct Ic3TransitionBackend;

impl TransitionBackend for Ic3TransitionBackend {
    fn solve(obligation: TransitionObligation<'_>) -> TransitionResult {
        match obligation {
            TransitionObligation::SingleEntitySafety {
                entity,
                vctx,
                property,
                timeout_ms,
            } => ic3::try_ic3_single_entity(entity, vctx, property, timeout_ms),
            TransitionObligation::MultiSlotSafety {
                entity,
                vctx,
                property,
                n_slots,
                timeout_ms,
            } => ic3::try_ic3_multi_slot(entity, vctx, property, n_slots, timeout_ms),
            TransitionObligation::SystemSafety {
                safety,
                property_index,
                timeout_ms,
            } => {
                let system = safety.system();
                let Some(property) = safety.step_property(property_index) else {
                    return TransitionResult::Unknown(format!(
                        "invalid transition safety property index {property_index}"
                    ));
                };
                ic3::try_ic3_system(
                    system.ir,
                    system.vctx,
                    system.system_names(),
                    property,
                    system.slots_per_entity(),
                    timeout_ms,
                )
            }
            TransitionObligation::SystemLiveness {
                liveness,
                recipe_index,
                target_slot,
                timeout_ms,
            } => {
                let system = liveness.system();
                let Some(recipe) = liveness.recipe(recipe_index) else {
                    return TransitionResult::Unknown(format!(
                        "invalid transition liveness recipe index {recipe_index}"
                    ));
                };
                let true_lit = IRExpr::Lit {
                    ty: crate::ir::types::IRType::Bool,
                    value: crate::ir::types::LitVal::Bool { value: true },
                    span: None,
                };
                let trigger = recipe.trigger(&true_lit);
                let response = recipe.response();
                let (ent_var, ent_name) = recipe.quantified_binding();
                let fair_event_keys = system.assumptions().all_fair_event_keys();
                ic3::try_ic3_liveness(
                    system.ir,
                    system.vctx,
                    system.system_names(),
                    trigger,
                    response,
                    ent_var,
                    ent_name,
                    &fair_event_keys,
                    system.slots_per_entity(),
                    recipe.is_oneshot(),
                    target_slot,
                    timeout_ms,
                )
            }
        }
    }
}

/// Solve a transition obligation using the current active transition backend.
pub fn solve_transition_obligation(obligation: TransitionObligation<'_>) -> TransitionResult {
    match (active_solver_family(), obligation) {
        (
            SolverFamily::Cvc5,
            TransitionObligation::SingleEntitySafety {
                entity,
                property,
                timeout_ms,
                ..
            },
        ) => sygus::try_cvc5_sygus_single_entity(entity, property, timeout_ms),
        (_, obligation) => Ic3TransitionBackend::solve(obligation),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::types::{
        IRAssumptionSet, IRCommandRef, IRField, IRProgram, IRSystem, IRTransition, IRType,
        IRVariant, IRVerify, IRVerifySystem, LitVal,
    };

    #[test]
    fn transition_obligation_single_entity_preserves_current_ic3_behavior() {
        let entity = IREntity {
            name: "Counter".to_owned(),
            fields: vec![IRField {
                name: "value".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },
                    span: None,
                }),
                initial_constraint: None,
            }],
            transitions: vec![IRTransition {
                name: "inc".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                updates: vec![],
                postcondition: None,
            }],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };
        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity.clone()],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };
        let vctx = VerifyContext::from_ir(&ir);
        let property = IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        };

        let direct = ic3::try_ic3_single_entity(&entity, &vctx, &property, 5_000);
        let via_transition =
            solve_transition_obligation(TransitionObligation::SingleEntitySafety {
                entity: &entity,
                vctx: &vctx,
                property: &property,
                timeout_ms: 5_000,
            });

        assert!(matches!(direct, TransitionResult::Proved));
        assert!(matches!(via_transition, TransitionResult::Proved));
    }

    #[test]
    fn transition_assumptions_merge_fair_event_keys_without_duplication() {
        let assumptions = TransitionAssumptions::from_ir(&IRAssumptionSet {
            stutter: false,
            weak_fair: vec![
                IRCommandRef {
                    system: "Sys".to_owned(),
                    command: "step".to_owned(),
                },
                IRCommandRef {
                    system: "Sys".to_owned(),
                    command: "other".to_owned(),
                },
            ],
            strong_fair: vec![IRCommandRef {
                system: "Sys".to_owned(),
                command: "step".to_owned(),
            }],
            per_tuple: vec![IRCommandRef {
                system: "Sys".to_owned(),
                command: "other".to_owned(),
            }],
        });

        assert!(!assumptions.stutter());
        assert_eq!(
            assumptions.all_fair_event_keys(),
            vec![
                ("Sys".to_owned(), "step".to_owned()),
                ("Sys".to_owned(), "other".to_owned()),
            ]
        );
        assert_eq!(
            assumptions.per_tuple_fair_event_keys(),
            &[("Sys".to_owned(), "other".to_owned())]
        );
        let roundtrip = assumptions.as_ir_assumption_set();
        assert!(!roundtrip.stutter);
        assert_eq!(roundtrip.weak_fair.len(), 2);
        assert_eq!(roundtrip.strong_fair.len(), 1);
        assert_eq!(roundtrip.per_tuple.len(), 1);
    }

    #[test]
    fn transition_system_spec_for_verify_applies_quantifier_scope_widening() {
        let order_status = crate::ir::types::IRTypeEntry {
            name: "OrderStatus".to_owned(),
            ty: crate::ir::types::IRType::Enum {
                name: "OrderStatus".to_owned(),
                variants: vec![IRVariant::simple("Pending")],
            },
        };
        let entity = IREntity {
            name: "Order".to_owned(),
            fields: vec![IRField {
                name: "id".to_owned(),
                ty: IRType::Identity,
                default: None,
                initial_constraint: None,
            }],
            transitions: vec![IRTransition {
                name: "noop".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                updates: vec![],
                postcondition: None,
            }],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };
        let system = IRSystem {
            name: "Orders".to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: vec!["Order".to_owned()],
            commands: vec![],
            actions: vec![],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        };
        let verify = IRVerify {
            name: "quantified".to_owned(),
            depth: Some(1),
            systems: vec![IRVerifySystem {
                name: "Orders".to_owned(),
                lo: 0,
                hi: 1,
            }],
            stores: vec![],
            assumption_set: IRAssumptionSet::default_for_verify(),
            asserts: vec![IRExpr::Always {
                body: Box::new(IRExpr::Forall {
                    var: "o".to_owned(),
                    domain: IRType::Entity {
                        name: "Order".to_owned(),
                    },
                    body: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                        span: None,
                    }),
                    span: None,
                }),
                span: None,
            }],
            span: None,
            file: None,
        };
        let ir = IRProgram {
            types: vec![order_status],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![verify.clone()],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);

        let spec =
            TransitionSystemSpec::for_verify(&ir, &vctx, &verify, &defs).expect("expected spec");

        assert_eq!(spec.system_names(), &["Orders".to_owned()]);
        assert_eq!(spec.slots_per_entity().get("Order"), Some(&2));
    }

    #[test]
    fn transition_safety_spec_normalizes_always_wrapped_asserts() {
        let verify = IRVerify {
            name: "safety".to_owned(),
            depth: Some(1),
            systems: vec![IRVerifySystem {
                name: "Orders".to_owned(),
                lo: 0,
                hi: 1,
            }],
            stores: vec![],
            assumption_set: IRAssumptionSet::default_for_verify(),
            asserts: vec![IRExpr::Always {
                body: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                }),
                span: None,
            }],
            span: None,
            file: None,
        };
        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![],
            systems: vec![IRSystem {
                name: "Orders".to_owned(),
                store_params: vec![],
                fields: vec![],
                entities: vec![],
                commands: vec![],
                actions: vec![],
                fsm_decls: vec![],
                derived_fields: vec![],
                invariants: vec![],
                queries: vec![],
                preds: vec![],
                let_bindings: vec![],
                procs: vec![],
            }],
            verifies: vec![verify.clone()],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);

        let safety =
            TransitionSafetySpec::for_verify(&ir, &vctx, &verify, &defs).expect("expected safety");

        assert_eq!(safety.step_properties().len(), 1);
        assert!(matches!(
            safety.step_properties()[0],
            IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                ..
            }
        ));
    }

    #[test]
    fn transition_verify_obligation_compiles_quantified_liveness_monitor_recipes() {
        let entity = IREntity {
            name: "Order".to_owned(),
            fields: vec![IRField {
                name: "id".to_owned(),
                ty: IRType::Identity,
                default: None,
                initial_constraint: None,
            }],
            transitions: vec![IRTransition {
                name: "noop".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                updates: vec![],
                postcondition: None,
            }],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };
        let verify = IRVerify {
            name: "liveness".to_owned(),
            depth: Some(1),
            systems: vec![IRVerifySystem {
                name: "Orders".to_owned(),
                lo: 0,
                hi: 1,
            }],
            stores: vec![],
            assumption_set: IRAssumptionSet::default_for_verify(),
            asserts: vec![IRExpr::Always {
                body: Box::new(IRExpr::Forall {
                    var: "o".to_owned(),
                    domain: IRType::Entity {
                        name: "Order".to_owned(),
                    },
                    body: Box::new(IRExpr::Eventually {
                        body: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        }),
                        span: None,
                    }),
                    span: None,
                }),
                span: None,
            }],
            span: None,
            file: None,
        };
        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![IRSystem {
                name: "Orders".to_owned(),
                store_params: vec![],
                fields: vec![],
                entities: vec!["Order".to_owned()],
                commands: vec![],
                actions: vec![],
                fsm_decls: vec![],
                derived_fields: vec![],
                invariants: vec![],
                queries: vec![],
                preds: vec![],
                let_bindings: vec![],
                procs: vec![],
            }],
            verifies: vec![verify.clone()],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);

        let obligation = TransitionVerifyObligation::for_verify(&ir, &vctx, &verify, &defs)
            .expect("expected verify obligation");
        let liveness = obligation.liveness().expect("expected supported liveness");
        let recipe = liveness.recipe(0).expect("expected liveness recipe");
        let true_lit = IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        };

        assert!(recipe.is_quantified());
        assert!(!recipe.is_oneshot());
        assert_eq!(recipe.slot_count(), 2);
        assert_eq!(recipe.assert_index(), 0);
        assert_eq!(recipe.quantified_binding(), (Some("o"), Some("Order")));
        assert!(matches!(
            recipe.trigger(&true_lit),
            IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                ..
            }
        ));
        assert!(matches!(
            recipe.response(),
            IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                ..
            }
        ));
        assert!(matches!(
            liveness.obligation(0, Some(1), 123),
            TransitionObligation::SystemLiveness {
                recipe_index: 0,
                target_slot: Some(1),
                timeout_ms: 123,
                ..
            }
        ));
    }

    #[test]
    fn transition_execution_plan_distinguishes_bmc_and_lasso_modes() {
        let system_ir = IRSystem {
            name: "Orders".to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: vec![],
            commands: vec![],
            actions: vec![],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        };
        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![],
            systems: vec![system_ir.clone()],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };
        let vctx = VerifyContext::from_ir(&ir);
        let system = TransitionSystemSpec::from_selected(
            &ir,
            &vctx,
            vec!["Orders".to_owned()],
            vec![],
            vec![system_ir],
            HashMap::new(),
            3,
            HashMap::new(),
            &IRAssumptionSet::default_for_verify(),
        )
        .expect("expected selected system");

        let bmc = TransitionExecutionPlan::for_bmc(system.clone(), 3);
        let lasso = TransitionExecutionPlan::for_lasso(system.clone(), 3);
        let inductive = TransitionExecutionPlan::for_inductive_step(system);

        assert_eq!(bmc.steps(), 3);
        assert!(bmc.include_system_initial_constraints());
        assert!(bmc.include_symmetry_constraints());
        assert!(!bmc.include_lasso_and_fairness());

        assert_eq!(lasso.steps(), 3);
        assert!(lasso.include_system_initial_constraints());
        assert!(lasso.include_symmetry_constraints());
        assert!(lasso.include_lasso_and_fairness());

        assert_eq!(inductive.steps(), 1);
        assert!(!inductive.include_system_initial_constraints());
        assert!(!inductive.include_symmetry_constraints());
        assert!(!inductive.include_lasso_and_fairness());
    }
}
