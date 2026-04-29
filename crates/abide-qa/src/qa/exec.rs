//! QA query executor — runs parsed queries against a `FlowModel`.
//!
//! Structural queries run on extracted graphs. Temporal fallback can also route
//! through bounded verifier-backed semantic evaluation when a graph is not
//! sufficient.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use abide_ir::ir;
use abide_sema::elab::env::Env;
use abide_sema::elab::types::{
    AssumptionSet, BuiltinTy, EExpr, ELetBinding, EPattern, EStoreDecl, EVerify, Quantifier, Ty,
};
use abide_syntax::{
    ast::{Expr, ExprKind, TypeRef, TypeRefKind},
    parse as syntax_parse,
};
use abide_verify::verify::{verify_all, VerificationResult, VerifyConfig};

use super::ast::{
    BlockArg, BlockPredicate, QAStatement, Query, TemporalBounds, TemporalOp, TemporalTarget,
};
use super::graph;
use super::model::{FlowModel, OwnerKind, StateGraph, TransitionEdge};

/// Result of executing a QA query.
#[derive(Debug, Clone)]
pub enum QueryResult {
    /// Boolean result (reachable, cycles, deadlock, etc.)
    Bool(bool),
    /// Boolean result annotated with the execution tier that produced it.
    BoolWithMode { value: bool, mode: String },
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

#[derive(Debug, Clone)]
pub struct StatementExecution {
    pub verb: Verb,
    pub result: QueryResult,
    pub semantic_artifact: Option<VerificationResult>,
}

/// Execute a QA statement, returning the verb and result.
pub fn execute_statement(model: &FlowModel, stmt: &QAStatement) -> (Verb, QueryResult) {
    execute_statement_with_env(model, None, stmt)
}

/// Execute a QA statement with optional semantic evaluation context.
pub fn execute_statement_with_env(
    model: &FlowModel,
    env: Option<&Env>,
    stmt: &QAStatement,
) -> (Verb, QueryResult) {
    let outcome = execute_statement_detailed_with_env(model, env, stmt);
    (outcome.verb, outcome.result)
}

pub fn execute_statement_detailed_with_env(
    model: &FlowModel,
    env: Option<&Env>,
    stmt: &QAStatement,
) -> StatementExecution {
    match stmt {
        QAStatement::Ask(q) => execute_query_statement(model, env, Verb::Ask, q),
        QAStatement::Explain(q) => execute_query_statement(model, env, Verb::Explain, q),
        QAStatement::Assert(q) => execute_query_statement(model, env, Verb::Assert, q),
        QAStatement::Load(_) | QAStatement::AbideBlock(_) => StatementExecution {
            verb: Verb::Ask,
            result: QueryResult::Error(
                "load/abide blocks are handled by the runner, not the executor".to_owned(),
            ),
            semantic_artifact: None,
        },
        QAStatement::Verify
        | QAStatement::Simulate(_)
        | QAStatement::Explore(_)
        | QAStatement::Artifacts
        | QAStatement::ShowArtifact(_)
        | QAStatement::DrawArtifact(_)
        | QAStatement::StateArtifact { .. }
        | QAStatement::DiffArtifact { .. }
        | QAStatement::ExportArtifact { .. } => StatementExecution {
            verb: Verb::Ask,
            result: QueryResult::Error(
                "verify/artifact statements are handled by the runner, not the executor".to_owned(),
            ),
            semantic_artifact: None,
        },
    }
}

fn execute_query_statement(
    model: &FlowModel,
    env: Option<&Env>,
    verb: Verb,
    query: &Query,
) -> StatementExecution {
    let (result, semantic_artifact) = execute_query_detailed_with_env(model, env, query);
    StatementExecution {
        verb,
        result,
        semantic_artifact,
    }
}

/// Execute a single query against the `FlowModel`.
#[allow(clippy::too_many_lines)]
pub fn execute_query(model: &FlowModel, query: &Query) -> QueryResult {
    execute_query_with_env(model, None, query)
}

/// Execute a single query with optional semantic evaluation context.
#[allow(clippy::too_many_lines)]
pub fn execute_query_with_env(model: &FlowModel, env: Option<&Env>, query: &Query) -> QueryResult {
    execute_query_detailed_with_env(model, env, query).0
}

#[allow(clippy::too_many_lines)]
fn execute_query_detailed_with_env(
    model: &FlowModel,
    env: Option<&Env>,
    query: &Query,
) -> (QueryResult, Option<VerificationResult>) {
    if let Query::Temporal {
        op,
        bounds,
        target,
        expr,
    } = query
    {
        match evaluate_temporal_query_with_fallback(model, env, *op, bounds, target.as_ref(), expr)
        {
            Ok(outcome) => (
                QueryResult::BoolWithMode {
                    value: outcome.value,
                    mode: outcome.mode,
                },
                outcome.semantic_artifact,
            ),
            Err(msg) => (QueryResult::Error(msg), None),
        }
    } else {
        (execute_query_core_with_env(model, env, query), None)
    }
}

#[allow(clippy::too_many_lines)]
fn execute_query_core_with_env(model: &FlowModel, env: Option<&Env>, query: &Query) -> QueryResult {
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
            None => QueryResult::Error(graph_lookup_error(model, entity, field)),
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
            None => QueryResult::Error(graph_lookup_error(model, entity, field)),
        },
        Query::Terminal { entity, field } => match lookup_graph(model, entity, field) {
            Some(sg) => QueryResult::StateSet(graph::terminal_states(sg)),
            None => QueryResult::Error(graph_lookup_error(model, entity, field)),
        },
        Query::Initial { entity, field } => match lookup_graph(model, entity, field) {
            Some(sg) => QueryResult::StateSet(graph::initial_states(sg)),
            None => QueryResult::Error(graph_lookup_error(model, entity, field)),
        },
        Query::Cycles { entity, field } => match lookup_graph(model, entity, field) {
            Some(sg) => QueryResult::Bool(graph::has_cycles(sg)),
            None => QueryResult::Error(graph_lookup_error(model, entity, field)),
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
            None => QueryResult::Error(graph_lookup_error(model, entity, field)),
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
            None => QueryResult::Error(graph_lookup_error(model, entity, field)),
        },

        Query::Entities => QueryResult::NameList(model.entity_names.clone()),
        Query::Systems => QueryResult::NameList(model.systems.keys().cloned().collect()),
        Query::Types => QueryResult::NameList(model.type_names.clone()),
        Query::Invariants { entity } => {
            // Return all action contracts (guards) for the entity as invariants.
            // These are the requires clauses that constrain entity state transitions.
            let mut invariants: Vec<String> = Vec::new();
            for ((ent, action), contract) in &model.action_contracts {
                if ent == entity && contract.guard != "true" {
                    invariants.push(format!("{action}: requires {}", contract.guard));
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
            match model
                .action_contracts
                .get(&(entity.clone(), action.clone()))
            {
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
                None => {
                    QueryResult::Error(format!("no action '{action}' found on entity '{entity}'"))
                }
            }
        }
        Query::Events { entity, field } => {
            let Some(sg) = lookup_graph(model, entity, field) else {
                return QueryResult::Error(graph_lookup_error(model, entity, field));
            };

            let mut event_names = Vec::new();
            match sg.owner_kind {
                OwnerKind::Entity => {
                    for sys in model.systems.values() {
                        for ev in &sys.events {
                            for apply in &ev.applies {
                                if sg.transitions.iter().any(|t| t.action == apply.action) {
                                    event_names.push(format!("{}::{}", sys.name, ev.name));
                                }
                            }
                        }
                    }
                }
                OwnerKind::System => {
                    if let Some(sys) = model.systems.get(entity) {
                        for ev in &sys.events {
                            if sg.transitions.iter().any(|t| t.action == ev.name) {
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
            None => QueryResult::Error(graph_lookup_error(model, entity, field)),
        },
        Query::Fsms { entity } => {
            // list every fsm field declared on
            // this owner. Reads from the IRFsm-derived metadata
            // populated in extract::extract.
            let mut fields: Vec<String> = model
                .fsm_decls
                .iter()
                .filter_map(|((e, f), _)| if e == entity { Some(f.clone()) } else { None })
                .collect();
            if fields.is_empty() {
                QueryResult::NameList(vec![format!("no fsm declarations on '{entity}'")])
            } else {
                fields.sort();
                QueryResult::NameList(fields)
            }
        }
        Query::FsmTransitions { entity, field } => {
            match model.fsm_decls.get(&(entity.clone(), field.clone())) {
                Some(info) => {
                    let edges: Vec<TransitionInfo> = info
                        .transitions
                        .iter()
                        .map(|(from, to)| TransitionInfo {
                            action: format!("fsm {}::{}", info.owner, info.field),
                            from: from.clone(),
                            to: to.clone(),
                        })
                        .collect();
                    QueryResult::Transitions(edges)
                }
                None => QueryResult::Error(format!("no fsm declaration on `{entity}::{field}`")),
            }
        }
        Query::FsmTerminalStates { entity, field } => {
            match model.fsm_decls.get(&(entity.clone(), field.clone())) {
                Some(info) => QueryResult::StateSet(info.terminal_states.clone()),
                None => QueryResult::Error(format!("no fsm declaration on `{entity}::{field}`")),
            }
        }
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
                for ((owner, _), sg) in &model.state_graphs {
                    let relevant = owner == system
                        || sys.entities.iter().any(|entity_name| entity_name == owner);
                    if relevant {
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
                QueryResult::Bool(has_deadlock)
            }
            None => QueryResult::Error(format!("no system named '{system}'")),
        },

        Query::Not(inner) => match execute_query_with_env(model, env, inner) {
            QueryResult::Bool(b) => QueryResult::Bool(!b),
            other => other,
        },
        Query::Temporal { .. } => QueryResult::Error(
            "internal QA error: temporal queries must route through detailed execution".to_owned(),
        ),

        Query::Block {
            bindings,
            predicates,
            select,
        } => execute_block(model, bindings, predicates, select),
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ResolvedTemporalTarget {
    owner: String,
    field: Option<String>,
    inferred: bool,
}

impl ResolvedTemporalTarget {
    fn display(&self) -> String {
        if let Some(field) = &self.field {
            format!("{}.{}", self.owner, field)
        } else {
            self.owner.clone()
        }
    }
}

fn resolve_temporal_target(
    model: &FlowModel,
    explicit: Option<&TemporalTarget>,
    expr: &str,
) -> Result<ResolvedTemporalTarget, String> {
    if let Some(target) = explicit {
        return resolve_explicit_temporal_target(model, target);
    }

    let parsed = syntax_parse::parse_expr_string(expr).map_err(|err| {
        format!(
            "unsupported temporal QA query: could not parse expression for scope inference: {err}"
        )
    })?;
    infer_temporal_target(model, &parsed)
}

fn evaluate_temporal_query(
    model: &FlowModel,
    op: TemporalOp,
    explicit: Option<&TemporalTarget>,
    expr: &str,
) -> Result<bool, String> {
    let resolved = resolve_temporal_target(model, explicit, expr)?;
    let field = resolved.field.as_ref().ok_or_else(|| {
        format!(
            "owner-scoped temporal QA evaluation is not implemented for `{}`; qualify a finite field target such as `on {}.<field>`",
            resolved.display(),
            resolved.owner
        )
    })?;
    let graph = lookup_graph(model, &resolved.owner, field)
        .ok_or_else(|| graph_lookup_error(model, &resolved.owner, field))?;
    let parsed = syntax_parse::parse_expr_string(expr).map_err(|err| {
        format!("unsupported temporal QA query: could not parse expression for evaluation: {err}")
    })?;
    let body_formula = compile_temporal_formula(
        model,
        &resolved,
        &parsed,
        &mut TemporalEvalContext::default(),
    )?;
    let formula = match op {
        TemporalOp::Always => TemporalFormula::Always(Box::new(body_formula)),
        TemporalOp::Eventually => TemporalFormula::Eventually(Box::new(body_formula)),
    };
    let initial = graph.initial.as_ref().ok_or_else(|| {
        format!(
            "no initial state for temporal QA target {}.{}",
            resolved.owner, field
        )
    })?;
    Ok(eval_temporal_formula(graph, &formula).contains(initial))
}

struct TemporalQueryOutcome {
    value: bool,
    mode: String,
    semantic_artifact: Option<VerificationResult>,
}

fn evaluate_temporal_query_with_fallback(
    model: &FlowModel,
    env: Option<&Env>,
    op: TemporalOp,
    bounds: &TemporalBounds,
    explicit: Option<&TemporalTarget>,
    expr: &str,
) -> Result<TemporalQueryOutcome, String> {
    if !bounds.is_empty() {
        let Some(env) = env else {
            return Err(
                "temporal QA semantic bounds require elaborated Abide specs; load a spec first"
                    .to_owned(),
            );
        };
        return evaluate_temporal_query_semantic(model, env, op, bounds, explicit, expr);
    }
    match evaluate_temporal_query(model, op, explicit, expr) {
        Ok(value) => Ok(TemporalQueryOutcome {
            value,
            mode: "graph:field-projection".to_owned(),
            semantic_artifact: None,
        }),
        Err(graph_err) => {
            let Some(env) = env else {
                return Err(graph_err);
            };
            match evaluate_temporal_query_semantic(model, env, op, bounds, explicit, expr) {
                Ok(outcome) => Ok(outcome),
                Err(semantic_err) => Err(if semantic_err == graph_err {
                    semantic_err
                } else {
                    format!("{semantic_err}\n\ngraph evaluator note: {graph_err}")
                }),
            }
        }
    }
}

fn resolve_explicit_temporal_target(
    model: &FlowModel,
    target: &TemporalTarget,
) -> Result<ResolvedTemporalTarget, String> {
    if let Some(field) = &target.field {
        if let Some(meta) = model
            .field_graph_meta
            .get(&(target.owner.clone(), field.clone()))
        {
            return Ok(ResolvedTemporalTarget {
                owner: meta.owner.clone(),
                field: Some(meta.field.clone()),
                inferred: false,
            });
        }
        if model.entity_names.iter().any(|name| name == &target.owner)
            || model.system_names.iter().any(|name| name == &target.owner)
        {
            return Err(format!("no field `{field}` on `{}`", target.owner));
        }
        return Err(format!("no entity or system named `{}`", target.owner));
    }

    if model.entity_names.iter().any(|name| name == &target.owner)
        || model.system_names.iter().any(|name| name == &target.owner)
    {
        return Ok(ResolvedTemporalTarget {
            owner: target.owner.clone(),
            field: None,
            inferred: false,
        });
    }

    Err(format!("no entity or system named `{}`", target.owner))
}

fn infer_temporal_target(model: &FlowModel, expr: &Expr) -> Result<ResolvedTemporalTarget, String> {
    let mut collector = TemporalTargetCollector::default();
    collector.collect_expr(model, expr);

    if collector.field_candidates.len() == 1 {
        let field = collector.field_candidates.iter().next().expect("one field");
        return Ok(ResolvedTemporalTarget {
            owner: field.owner.clone(),
            field: Some(field.field.clone()),
            inferred: true,
        });
    }

    let mut owners: BTreeSet<String> = collector.owner_candidates;
    owners.extend(
        collector
            .field_candidates
            .iter()
            .map(|field| field.owner.clone()),
    );

    if owners.len() == 1 {
        let owner = owners.into_iter().next().expect("one owner");
        return Ok(ResolvedTemporalTarget {
            owner,
            field: None,
            inferred: true,
        });
    }

    if collector.field_candidates.len() > 1 || owners.len() > 1 {
        let mut candidates: Vec<String> = collector
            .field_candidates
            .iter()
            .map(|field| format!("{}.{}", field.owner, field.field))
            .collect();
        candidates.extend(owners.into_iter().filter(|owner| {
            !collector
                .field_candidates
                .iter()
                .any(|field| &field.owner == owner)
        }));
        candidates.sort();
        return Err(format!(
            "ambiguous temporal QA target; expression references multiple candidates: {}. Use `on Owner` or `on Owner.field` to qualify the query",
            candidates.join(", ")
        ));
    }

    Err(
        "could not infer temporal QA target from expression; use `on Owner` or `on Owner.field` to qualify the query"
            .to_owned(),
    )
}

#[derive(Debug, Clone)]
enum TemporalFormula {
    Bool(bool),
    Predicate(StatePredicate),
    Not(Box<TemporalFormula>),
    And(Box<TemporalFormula>, Box<TemporalFormula>),
    Or(Box<TemporalFormula>, Box<TemporalFormula>),
    Implies(Box<TemporalFormula>, Box<TemporalFormula>),
    Always(Box<TemporalFormula>),
    Eventually(Box<TemporalFormula>),
}

#[derive(Debug, Clone)]
enum StatePredicate {
    BoolValue(bool),
    Equals(String),
    NotEquals(String),
}

#[derive(Default)]
struct TemporalEvalContext {
    bindings: HashMap<String, String>,
}

impl TemporalEvalContext {
    fn with_binding<F, T>(&mut self, name: &str, owner: &str, f: F) -> T
    where
        F: FnOnce(&mut Self) -> T,
    {
        let previous = self.bindings.insert(name.to_owned(), owner.to_owned());
        let result = f(self);
        if let Some(previous) = previous {
            self.bindings.insert(name.to_owned(), previous);
        } else {
            self.bindings.remove(name);
        }
        result
    }
}

fn compile_temporal_formula(
    model: &FlowModel,
    target: &ResolvedTemporalTarget,
    expr: &Expr,
    ctx: &mut TemporalEvalContext,
) -> Result<TemporalFormula, String> {
    match &expr.kind {
        ExprKind::Always(body) => Ok(TemporalFormula::Always(Box::new(compile_temporal_formula(
            model, target, body, ctx,
        )?))),
        ExprKind::Eventually(body) => Ok(TemporalFormula::Eventually(Box::new(
            compile_temporal_formula(model, target, body, ctx)?,
        ))),
        ExprKind::Not(body) => Ok(TemporalFormula::Not(Box::new(compile_temporal_formula(
            model, target, body, ctx,
        )?))),
        ExprKind::And(left, right) => Ok(TemporalFormula::And(
            Box::new(compile_temporal_formula(model, target, left, ctx)?),
            Box::new(compile_temporal_formula(model, target, right, ctx)?),
        )),
        ExprKind::Or(left, right) => Ok(TemporalFormula::Or(
            Box::new(compile_temporal_formula(model, target, left, ctx)?),
            Box::new(compile_temporal_formula(model, target, right, ctx)?),
        )),
        ExprKind::Impl(left, right) => Ok(TemporalFormula::Implies(
            Box::new(compile_temporal_formula(model, target, left, ctx)?),
            Box::new(compile_temporal_formula(model, target, right, ctx)?),
        )),
        ExprKind::True => Ok(TemporalFormula::Bool(true)),
        ExprKind::False => Ok(TemporalFormula::Bool(false)),
        ExprKind::All(var, domain, _, body)
        | ExprKind::Exists(var, domain, _, body)
        | ExprKind::SomeQ(var, domain, _, body)
        | ExprKind::OneQ(var, domain, _, body)
        | ExprKind::LoneQ(var, domain, _, body) => {
            let owner = type_ref_owner_name(domain).ok_or_else(|| {
                "unsupported temporal QA query: quantifier domain is not an entity or system type"
                    .to_owned()
            })?;
            if owner != target.owner {
                return Err(format!(
                    "unsupported temporal QA query: quantifier domain `{owner}` does not match target owner `{}`",
                    target.owner
                ));
            }
            ctx.with_binding(var, &owner, |ctx| {
                compile_temporal_formula(model, target, body, ctx)
            })
        }
        ExprKind::NoQ(var, domain, _, body) => {
            let owner = type_ref_owner_name(domain).ok_or_else(|| {
                "unsupported temporal QA query: quantifier domain is not an entity or system type"
                    .to_owned()
            })?;
            if owner != target.owner {
                return Err(format!(
                    "unsupported temporal QA query: quantifier domain `{owner}` does not match target owner `{}`",
                    target.owner
                ));
            }
            let body_formula = ctx.with_binding(var, &owner, |ctx| {
                compile_temporal_formula(model, target, body, ctx)
            })?;
            Ok(TemporalFormula::Not(Box::new(body_formula)))
        }
        ExprKind::Eq(left, right) => {
            compile_state_predicate(target, left, right, false, ctx).map(TemporalFormula::Predicate)
        }
        ExprKind::NEq(left, right) => {
            compile_state_predicate(target, left, right, true, ctx).map(TemporalFormula::Predicate)
        }
        ExprKind::Var(name) => {
            if is_target_field_ref(target, ctx, name, None) {
                if !target_is_bool(model, target)? {
                    return Err(format!(
                        "unsupported temporal QA query: bare `{name}` requires a bool-valued target field"
                    ));
                }
                Ok(TemporalFormula::Predicate(StatePredicate::BoolValue(true)))
            } else {
                Err(format!(
                    "unsupported temporal QA query: `{name}` is not the resolved target field {}",
                    target.display()
                ))
            }
        }
        other => Err(format!(
            "unsupported temporal QA query: `{}` is not in the supported field-temporal fragment",
            expr_kind_name(other)
        )),
    }
}

fn compile_state_predicate(
    target: &ResolvedTemporalTarget,
    left: &Expr,
    right: &Expr,
    negate: bool,
    ctx: &TemporalEvalContext,
) -> Result<StatePredicate, String> {
    if is_target_expr(target, left, ctx) {
        return compile_state_value(target, right, negate);
    }
    if is_target_expr(target, right, ctx) {
        return compile_state_value(target, left, negate);
    }
    Err(format!(
        "unsupported temporal QA query: comparisons must mention the resolved target field {}",
        target.display()
    ))
}

fn compile_state_value(
    target: &ResolvedTemporalTarget,
    expr: &Expr,
    negate: bool,
) -> Result<StatePredicate, String> {
    match &expr.kind {
        ExprKind::State1(name) | ExprKind::State2(_, name) => Ok(if negate {
            StatePredicate::NotEquals(name.clone())
        } else {
            StatePredicate::Equals(name.clone())
        }),
        ExprKind::True => {
            if negate {
                Ok(StatePredicate::BoolValue(false))
            } else {
                Ok(StatePredicate::BoolValue(true))
            }
        }
        ExprKind::False => {
            if negate {
                Ok(StatePredicate::BoolValue(true))
            } else {
                Ok(StatePredicate::BoolValue(false))
            }
        }
        _ => Err(format!(
            "unsupported temporal QA query: target {} may only be compared with enum states or bool literals",
            target.display()
        )),
    }
}

fn is_target_expr(target: &ResolvedTemporalTarget, expr: &Expr, ctx: &TemporalEvalContext) -> bool {
    match &expr.kind {
        ExprKind::Var(name) => is_target_field_ref(target, ctx, name, None),
        ExprKind::Field(base, field) => match &base.kind {
            ExprKind::Var(name) => is_target_field_ref(target, ctx, field, Some(name)),
            _ => false,
        },
        _ => false,
    }
}

fn is_target_field_ref(
    target: &ResolvedTemporalTarget,
    ctx: &TemporalEvalContext,
    field: &str,
    base: Option<&str>,
) -> bool {
    let Some(target_field) = target.field.as_deref() else {
        return false;
    };
    if field != target_field {
        return false;
    }
    match base {
        None => true,
        Some(name) => {
            if name == target.owner {
                return true;
            }
            ctx.bindings
                .get(name)
                .is_some_and(|owner| owner == &target.owner)
        }
    }
}

fn target_is_bool(model: &FlowModel, target: &ResolvedTemporalTarget) -> Result<bool, String> {
    let field = target.field.as_ref().ok_or_else(|| {
        format!(
            "owner-scoped temporal QA evaluation is not implemented for `{}`",
            target.display()
        )
    })?;
    model
        .field_graph_meta
        .get(&(target.owner.clone(), field.clone()))
        .map(|meta| meta.type_name == "bool")
        .ok_or_else(|| graph_lookup_error(model, &target.owner, field))
}

fn evaluate_temporal_query_semantic(
    model: &FlowModel,
    env: &Env,
    op: TemporalOp,
    bounds: &TemporalBounds,
    explicit: Option<&TemporalTarget>,
    expr: &str,
) -> Result<TemporalQueryOutcome, String> {
    let resolved = resolve_temporal_target(model, explicit, expr)?;
    let owner_kind = resolve_owner_kind(model, &resolved)?;
    let owner_fields = owner_field_names(env, owner_kind, &resolved.owner)?;

    let parsed = syntax_parse::parse_expr_string(expr).map_err(|err| {
        format!("unsupported temporal QA query: could not parse expression for semantic evaluation: {err}")
    })?;
    let collected = abide_sema::elab::collect::collect_query_expr(&parsed);
    let implicit_var = match owner_kind {
        OwnerKind::Entity => "__qa_owner",
        OwnerKind::System => "__qa_system",
    };
    let rewritten = rewrite_owner_scoped_expr(
        &collected,
        &resolved.owner,
        owner_kind,
        implicit_var,
        &owner_fields,
        &mut Vec::new(),
    )?;
    let scoped = if owner_kind == OwnerKind::Entity {
        EExpr::Quant(
            bool_ty(),
            Quantifier::All,
            implicit_var.to_owned(),
            Ty::Entity(resolved.owner.clone()),
            Box::new(rewritten),
            None,
        )
    } else {
        rewritten
    };
    let top = match op {
        TemporalOp::Always => EExpr::Always(bool_ty(), Box::new(scoped), None),
        TemporalOp::Eventually => EExpr::Eventually(bool_ty(), Box::new(scoped), None),
    };

    let (verify, mode_suffix) =
        build_semantic_verify(env, owner_kind, &resolved.owner, bounds, top)?;
    let mut synthetic_env = env.clone();
    synthetic_env.verifies.push(verify);

    let (result, elab_errors) = abide_sema::elab::elaborate_env(synthetic_env);
    let semantic_errors: Vec<String> = elab_errors
        .iter()
        .filter(|e| !matches!(e.severity, abide_sema::elab::error::Severity::Warning))
        .map(|e| e.to_string())
        .collect();
    if !semantic_errors.is_empty() {
        return Err(format!(
            "unsupported semantic QA query for `{}`: {}",
            resolved.display(),
            semantic_errors.join("; ")
        ));
    }

    let (ir_program, lower_diag) = ir::lower(&result);
    if lower_diag.has_errors() {
        let details = lower_diag
            .diagnostics
            .iter()
            .map(std::string::ToString::to_string)
            .collect::<Vec<_>>()
            .join("; ");
        return Err(format!(
            "unsupported semantic QA query for `{}`: {details}",
            resolved.display()
        ));
    }

    let result = verify_all(&ir_program, &VerifyConfig::default())
        .into_iter()
        .find(|result| semantic_result_name(result) == "__qa_temporal_query")
        .ok_or_else(|| {
            "internal QA error: synthetic temporal verification result missing".to_owned()
        })?;
    interpret_semantic_result(result, &mode_suffix)
}

const QA_SEMANTIC_DEFAULT_STORE_SLOTS: i64 = 4;

fn semantic_slots_for_entity(bounds: &TemporalBounds, entity_type: &str) -> i64 {
    bounds
        .scopes
        .iter()
        .rev()
        .find_map(|(entity, slots)| (entity == entity_type).then_some(*slots as i64))
        .or_else(|| bounds.slots.map(|slots| slots as i64))
        .unwrap_or(QA_SEMANTIC_DEFAULT_STORE_SLOTS)
}

fn validate_semantic_scope_bounds(
    bounds: &TemporalBounds,
    stores: &[EStoreDecl],
) -> Result<(), String> {
    let scoped_entities = stores
        .iter()
        .map(|store| store.entity_type.as_str())
        .collect::<BTreeSet<_>>();
    for (entity, _) in &bounds.scopes {
        if !scoped_entities.contains(entity.as_str()) {
            return Err(format!(
                "temporal scope override names unknown or unused entity `{entity}` for this query"
            ));
        }
    }
    Ok(())
}

fn resolve_owner_kind(
    model: &FlowModel,
    target: &ResolvedTemporalTarget,
) -> Result<OwnerKind, String> {
    if let Some(field) = &target.field {
        if let Some(meta) = model
            .field_graph_meta
            .get(&(target.owner.clone(), field.clone()))
        {
            return Ok(meta.owner_kind);
        }
    }
    if model.entity_names.iter().any(|name| name == &target.owner) {
        return Ok(OwnerKind::Entity);
    }
    if model.system_names.iter().any(|name| name == &target.owner) {
        return Ok(OwnerKind::System);
    }
    Err(format!(
        "unsupported semantic QA query: no entity or system named `{}`",
        target.owner
    ))
}

fn owner_field_names(
    env: &Env,
    owner_kind: OwnerKind,
    owner: &str,
) -> Result<BTreeSet<String>, String> {
    let fields = match owner_kind {
        OwnerKind::Entity => env
            .entities
            .get(owner)
            .ok_or_else(|| format!("unsupported semantic QA query: no entity named `{owner}`"))?
            .fields
            .iter()
            .map(|field| field.name.clone())
            .collect(),
        OwnerKind::System => env
            .systems
            .get(owner)
            .ok_or_else(|| format!("unsupported semantic QA query: no system named `{owner}`"))?
            .fields
            .iter()
            .map(|field| field.name.clone())
            .collect(),
    };
    Ok(fields)
}

fn build_semantic_verify(
    env: &Env,
    owner_kind: OwnerKind,
    owner: &str,
    bounds: &TemporalBounds,
    assertion: EExpr,
) -> Result<(EVerify, String), String> {
    let (stores, let_bindings) = match owner_kind {
        OwnerKind::Entity => semantic_entity_scaffold(env, owner, bounds)?,
        OwnerKind::System => semantic_system_scaffold(env, owner, bounds)?,
    };
    validate_semantic_scope_bounds(bounds, &stores)?;
    let mode_suffix = semantic_mode_suffix(&stores);
    Ok((
        EVerify {
            name: "__qa_temporal_query".to_owned(),
            depth: None,
            stores,
            proc_bounds: Vec::new(),
            let_bindings,
            assume_block: None,
            assumption_set: AssumptionSet::default_for_verify(),
            asserts: vec![assertion],
            span: None,
            file: None,
        },
        mode_suffix,
    ))
}

fn semantic_entity_scaffold(
    env: &Env,
    owner: &str,
    bounds: &TemporalBounds,
) -> Result<(Vec<EStoreDecl>, Vec<ELetBinding>), String> {
    let candidates: Vec<_> = env
        .systems
        .values()
        .filter_map(|system| {
            let matching: Vec<_> = system
                .store_params
                .iter()
                .filter(|(_, entity_type)| entity_type == owner)
                .collect();
            if matching.is_empty() {
                None
            } else {
                Some((system, matching))
            }
        })
        .collect();
    if candidates.is_empty() {
        return Err(format!(
            "unsupported semantic QA query on `{owner}`: no system instantiates a Store<{owner}>; whole-store/global owner semantics are not supported yet"
        ));
    }
    let mut stores = Vec::new();
    let mut let_bindings = Vec::new();
    for (system, _) in candidates {
        let (system_stores, system_binding) = build_scaffold_for_system(system, bounds);
        stores.extend(system_stores);
        let_bindings.push(system_binding);
    }
    Ok((stores, let_bindings))
}

fn semantic_system_scaffold(
    env: &Env,
    owner: &str,
    bounds: &TemporalBounds,
) -> Result<(Vec<EStoreDecl>, Vec<ELetBinding>), String> {
    let system = env
        .systems
        .get(owner)
        .ok_or_else(|| format!("unsupported semantic QA query: no system named `{owner}`"))?;
    let (stores, binding) = build_scaffold_for_system(system, bounds);
    Ok((stores, vec![binding]))
}

fn build_scaffold_for_system(
    system: &abide_sema::elab::types::ESystem,
    bounds: &TemporalBounds,
) -> (Vec<EStoreDecl>, ELetBinding) {
    let mut stores = Vec::new();
    let mut store_bindings = Vec::new();
    for (param_name, entity_type) in &system.store_params {
        let store_name = format!("__qa_store_{}_{}", system.name, param_name);
        let slots = semantic_slots_for_entity(bounds, entity_type);
        stores.push(EStoreDecl {
            name: store_name.clone(),
            entity_type: entity_type.clone(),
            lo: slots,
            hi: slots,
        });
        store_bindings.push((param_name.clone(), store_name));
    }
    let let_binding = ELetBinding {
        name: format!("__qa_system_{}", system.name),
        system_type: system.name.clone(),
        store_bindings,
    };
    (stores, let_binding)
}

fn rewrite_owner_scoped_expr(
    expr: &EExpr,
    owner: &str,
    owner_kind: OwnerKind,
    implicit_var: &str,
    owner_fields: &BTreeSet<String>,
    bound_vars: &mut Vec<String>,
) -> Result<EExpr, String> {
    Ok(match expr {
        EExpr::Var(ty, name, span) => {
            if !bound_vars.iter().any(|bound| bound == name) && name == owner {
                EExpr::Var(
                    owner_var_ty(owner_kind, owner),
                    implicit_var.to_owned(),
                    *span,
                )
            } else if owner_kind == OwnerKind::Entity
                && owner_fields.contains(name)
                && !bound_vars.iter().any(|bound| bound == name)
            {
                EExpr::Field(
                    Ty::Error,
                    Box::new(EExpr::Var(
                        owner_var_ty(owner_kind, owner),
                        implicit_var.to_owned(),
                        *span,
                    )),
                    name.clone(),
                    *span,
                )
            } else {
                EExpr::Var(ty.clone(), name.clone(), *span)
            }
        }
        EExpr::Field(ty, base, field, span) => {
            if let EExpr::Var(_, base_name, _) = &**base {
                if !bound_vars.iter().any(|bound| bound == base_name)
                    && base_name == owner
                    && owner_fields.contains(field)
                {
                    match owner_kind {
                        OwnerKind::Entity => EExpr::Field(
                            ty.clone(),
                            Box::new(EExpr::Var(
                                owner_var_ty(owner_kind, owner),
                                implicit_var.to_owned(),
                                *span,
                            )),
                            field.clone(),
                            *span,
                        ),
                        OwnerKind::System => EExpr::Var(ty.clone(), field.clone(), *span),
                    }
                } else {
                    EExpr::Field(
                        ty.clone(),
                        Box::new(rewrite_owner_scoped_expr(
                            base,
                            owner,
                            owner_kind,
                            implicit_var,
                            owner_fields,
                            bound_vars,
                        )?),
                        field.clone(),
                        *span,
                    )
                }
            } else {
                EExpr::Field(
                    ty.clone(),
                    Box::new(rewrite_owner_scoped_expr(
                        base,
                        owner,
                        owner_kind,
                        implicit_var,
                        owner_fields,
                        bound_vars,
                    )?),
                    field.clone(),
                    *span,
                )
            }
        }
        EExpr::Prime(ty, inner, span) => EExpr::Prime(
            ty.clone(),
            Box::new(rewrite_owner_scoped_expr(
                inner,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            *span,
        ),
        EExpr::BinOp(ty, op, left, right, span) => EExpr::BinOp(
            ty.clone(),
            *op,
            Box::new(rewrite_owner_scoped_expr(
                left,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            Box::new(rewrite_owner_scoped_expr(
                right,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            *span,
        ),
        EExpr::UnOp(ty, op, inner, span) => EExpr::UnOp(
            ty.clone(),
            *op,
            Box::new(rewrite_owner_scoped_expr(
                inner,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            *span,
        ),
        EExpr::Call(ty, func, args, span) => EExpr::Call(
            ty.clone(),
            Box::new(rewrite_owner_scoped_expr(
                func,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            rewrite_expr_list(
                args,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?,
            *span,
        ),
        EExpr::CallR(ty, func, refs, args, span) => EExpr::CallR(
            ty.clone(),
            Box::new(rewrite_owner_scoped_expr(
                func,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            rewrite_expr_list(
                refs,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?,
            rewrite_expr_list(
                args,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?,
            *span,
        ),
        EExpr::Qual(ty, a, b, span) => EExpr::Qual(ty.clone(), a.clone(), b.clone(), *span),
        EExpr::Quant(ty, quant, name, domain_ty, body, span) => {
            bound_vars.push(name.clone());
            let body = rewrite_owner_scoped_expr(
                body,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?;
            bound_vars.pop();
            EExpr::Quant(
                ty.clone(),
                *quant,
                name.clone(),
                domain_ty.clone(),
                Box::new(body),
                *span,
            )
        }
        EExpr::Always(ty, body, span) => EExpr::Always(
            ty.clone(),
            Box::new(rewrite_owner_scoped_expr(
                body,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            *span,
        ),
        EExpr::Eventually(ty, body, span) => EExpr::Eventually(
            ty.clone(),
            Box::new(rewrite_owner_scoped_expr(
                body,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            *span,
        ),
        EExpr::Until(ty, left, right, span) => EExpr::Until(
            ty.clone(),
            Box::new(rewrite_owner_scoped_expr(
                left,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            Box::new(rewrite_owner_scoped_expr(
                right,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            *span,
        ),
        EExpr::Historically(ty, body, span) => EExpr::Historically(
            ty.clone(),
            Box::new(rewrite_owner_scoped_expr(
                body,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            *span,
        ),
        EExpr::Once(ty, body, span) => EExpr::Once(
            ty.clone(),
            Box::new(rewrite_owner_scoped_expr(
                body,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            *span,
        ),
        EExpr::Previously(ty, body, span) => EExpr::Previously(
            ty.clone(),
            Box::new(rewrite_owner_scoped_expr(
                body,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            *span,
        ),
        EExpr::Since(ty, left, right, span) => EExpr::Since(
            ty.clone(),
            Box::new(rewrite_owner_scoped_expr(
                left,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            Box::new(rewrite_owner_scoped_expr(
                right,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            *span,
        ),
        EExpr::Assert(ty, body, span) => EExpr::Assert(
            ty.clone(),
            Box::new(rewrite_owner_scoped_expr(
                body,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            *span,
        ),
        EExpr::Assume(ty, body, span) => EExpr::Assume(
            ty.clone(),
            Box::new(rewrite_owner_scoped_expr(
                body,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            *span,
        ),
        EExpr::Assign(ty, left, right, span) => EExpr::Assign(
            ty.clone(),
            Box::new(rewrite_owner_scoped_expr(
                left,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            Box::new(rewrite_owner_scoped_expr(
                right,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            *span,
        ),
        EExpr::NamedPair(ty, name, expr, span) => EExpr::NamedPair(
            ty.clone(),
            name.clone(),
            Box::new(rewrite_owner_scoped_expr(
                expr,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            *span,
        ),
        EExpr::Seq(ty, left, right, span) => EExpr::Seq(
            ty.clone(),
            Box::new(rewrite_owner_scoped_expr(
                left,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            Box::new(rewrite_owner_scoped_expr(
                right,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            *span,
        ),
        EExpr::SameStep(ty, left, right, span) => EExpr::SameStep(
            ty.clone(),
            Box::new(rewrite_owner_scoped_expr(
                left,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            Box::new(rewrite_owner_scoped_expr(
                right,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            *span,
        ),
        EExpr::Let(bindings, body, span) => {
            let mut rewritten_bindings = Vec::with_capacity(bindings.len());
            let mut pushed = Vec::new();
            for (name, ty, value) in bindings {
                let rewritten_value = rewrite_owner_scoped_expr(
                    value,
                    owner,
                    owner_kind,
                    implicit_var,
                    owner_fields,
                    bound_vars,
                )?;
                rewritten_bindings.push((name.clone(), ty.clone(), rewritten_value));
                pushed.push(name.clone());
                bound_vars.push(name.clone());
            }
            let rewritten_body = rewrite_owner_scoped_expr(
                body,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?;
            for _ in pushed {
                bound_vars.pop();
            }
            EExpr::Let(rewritten_bindings, Box::new(rewritten_body), *span)
        }
        EExpr::TupleLit(ty, items, span) => EExpr::TupleLit(
            ty.clone(),
            rewrite_expr_list(
                items,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?,
            *span,
        ),
        EExpr::In(ty, left, right, span) => EExpr::In(
            ty.clone(),
            Box::new(rewrite_owner_scoped_expr(
                left,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            Box::new(rewrite_owner_scoped_expr(
                right,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            *span,
        ),
        EExpr::Card(ty, inner, span) => EExpr::Card(
            ty.clone(),
            Box::new(rewrite_owner_scoped_expr(
                inner,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            *span,
        ),
        EExpr::Pipe(ty, left, right, span) => EExpr::Pipe(
            ty.clone(),
            Box::new(rewrite_owner_scoped_expr(
                left,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            Box::new(rewrite_owner_scoped_expr(
                right,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            *span,
        ),
        EExpr::Lam(params, ret_ty, body, span) => {
            for (name, _) in params {
                bound_vars.push(name.clone());
            }
            let rewritten_body = rewrite_owner_scoped_expr(
                body,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?;
            for _ in params {
                bound_vars.pop();
            }
            EExpr::Lam(
                params.clone(),
                ret_ty.clone(),
                Box::new(rewritten_body),
                *span,
            )
        }
        EExpr::Match(scrutinee, arms, span) => {
            let rewritten_scrutinee = rewrite_owner_scoped_expr(
                scrutinee,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?;
            let mut rewritten_arms = Vec::with_capacity(arms.len());
            for (pattern, guard, body) in arms {
                let mut pushed = Vec::new();
                collect_pattern_bindings(pattern, &mut pushed);
                bound_vars.extend(pushed.iter().cloned());
                let rewritten_guard = guard
                    .as_ref()
                    .map(|guard| {
                        rewrite_owner_scoped_expr(
                            guard,
                            owner,
                            owner_kind,
                            implicit_var,
                            owner_fields,
                            bound_vars,
                        )
                    })
                    .transpose()?;
                let rewritten_body = rewrite_owner_scoped_expr(
                    body,
                    owner,
                    owner_kind,
                    implicit_var,
                    owner_fields,
                    bound_vars,
                )?;
                for _ in pushed {
                    bound_vars.pop();
                }
                rewritten_arms.push((pattern.clone(), rewritten_guard, rewritten_body));
            }
            EExpr::Match(Box::new(rewritten_scrutinee), rewritten_arms, *span)
        }
        EExpr::Choose(ty, name, domain_ty, filter, span) => {
            bound_vars.push(name.clone());
            let rewritten_filter = filter
                .as_ref()
                .map(|filter| {
                    rewrite_owner_scoped_expr(
                        filter,
                        owner,
                        owner_kind,
                        implicit_var,
                        owner_fields,
                        bound_vars,
                    )
                })
                .transpose()?;
            bound_vars.pop();
            EExpr::Choose(
                ty.clone(),
                name.clone(),
                domain_ty.clone(),
                rewritten_filter.map(Box::new),
                *span,
            )
        }
        EExpr::MapUpdate(ty, map, key, value, span) => EExpr::MapUpdate(
            ty.clone(),
            Box::new(rewrite_owner_scoped_expr(
                map,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            Box::new(rewrite_owner_scoped_expr(
                key,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            Box::new(rewrite_owner_scoped_expr(
                value,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            *span,
        ),
        EExpr::Index(ty, map, key, span) => EExpr::Index(
            ty.clone(),
            Box::new(rewrite_owner_scoped_expr(
                map,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            Box::new(rewrite_owner_scoped_expr(
                key,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            *span,
        ),
        EExpr::SetComp(ty, projection, name, domain_ty, filter, span) => {
            bound_vars.push(name.clone());
            let rewritten_projection = projection
                .as_ref()
                .map(|projection| {
                    rewrite_owner_scoped_expr(
                        projection,
                        owner,
                        owner_kind,
                        implicit_var,
                        owner_fields,
                        bound_vars,
                    )
                })
                .transpose()?;
            let rewritten_filter = rewrite_owner_scoped_expr(
                filter,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?;
            bound_vars.pop();
            EExpr::SetComp(
                ty.clone(),
                rewritten_projection.map(Box::new),
                name.clone(),
                domain_ty.clone(),
                Box::new(rewritten_filter),
                *span,
            )
        }
        EExpr::SetLit(ty, items, span) => EExpr::SetLit(
            ty.clone(),
            rewrite_expr_list(
                items,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?,
            *span,
        ),
        EExpr::SeqLit(ty, items, span) => EExpr::SeqLit(
            ty.clone(),
            rewrite_expr_list(
                items,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?,
            *span,
        ),
        EExpr::MapLit(ty, items, span) => EExpr::MapLit(
            ty.clone(),
            items
                .iter()
                .map(|(key, value)| {
                    Ok((
                        rewrite_owner_scoped_expr(
                            key,
                            owner,
                            owner_kind,
                            implicit_var,
                            owner_fields,
                            bound_vars,
                        )?,
                        rewrite_owner_scoped_expr(
                            value,
                            owner,
                            owner_kind,
                            implicit_var,
                            owner_fields,
                            bound_vars,
                        )?,
                    ))
                })
                .collect::<Result<Vec<_>, String>>()?,
            *span,
        ),
        EExpr::QualCall(ty, a, b, args, span) => EExpr::QualCall(
            ty.clone(),
            a.clone(),
            b.clone(),
            rewrite_expr_list(
                args,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?,
            *span,
        ),
        EExpr::Block(items, span) => EExpr::Block(
            rewrite_expr_list(
                items,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?,
            *span,
        ),
        EExpr::VarDecl(name, ty, init, rest, span) => {
            let rewritten_init = rewrite_owner_scoped_expr(
                init,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?;
            bound_vars.push(name.clone());
            let rewritten_rest = rewrite_owner_scoped_expr(
                rest,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?;
            bound_vars.pop();
            EExpr::VarDecl(
                name.clone(),
                ty.clone(),
                Box::new(rewritten_init),
                Box::new(rewritten_rest),
                *span,
            )
        }
        EExpr::While(cond, contracts, body, span) => EExpr::While(
            Box::new(rewrite_owner_scoped_expr(
                cond,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            contracts.clone(),
            Box::new(rewrite_owner_scoped_expr(
                body,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            *span,
        ),
        EExpr::IfElse(cond, then_body, else_body, span) => EExpr::IfElse(
            Box::new(rewrite_owner_scoped_expr(
                cond,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            Box::new(rewrite_owner_scoped_expr(
                then_body,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?),
            else_body
                .as_ref()
                .map(|else_body| {
                    rewrite_owner_scoped_expr(
                        else_body,
                        owner,
                        owner_kind,
                        implicit_var,
                        owner_fields,
                        bound_vars,
                    )
                    .map(Box::new)
                })
                .transpose()?,
            *span,
        ),
        EExpr::Aggregate(ty, kind, name, domain_ty, body, in_filter, span) => {
            bound_vars.push(name.clone());
            let rewritten_body = rewrite_owner_scoped_expr(
                body,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )?;
            let rewritten_filter = in_filter
                .as_ref()
                .map(|filter| {
                    rewrite_owner_scoped_expr(
                        filter,
                        owner,
                        owner_kind,
                        implicit_var,
                        owner_fields,
                        bound_vars,
                    )
                })
                .transpose()?;
            bound_vars.pop();
            EExpr::Aggregate(
                ty.clone(),
                *kind,
                name.clone(),
                domain_ty.clone(),
                Box::new(rewritten_body),
                rewritten_filter.map(Box::new),
                *span,
            )
        }
        EExpr::Saw(ty, a, b, args, span) => EExpr::Saw(
            ty.clone(),
            a.clone(),
            b.clone(),
            args.iter()
                .map(|arg| {
                    arg.as_ref()
                        .map(|expr| {
                            rewrite_owner_scoped_expr(
                                expr,
                                owner,
                                owner_kind,
                                implicit_var,
                                owner_fields,
                                bound_vars,
                            )
                            .map(Box::new)
                        })
                        .transpose()
                })
                .collect::<Result<Vec<_>, String>>()?,
            *span,
        ),
        EExpr::CtorRecord(ty, qualifier, ctor, fields, span) => EExpr::CtorRecord(
            ty.clone(),
            qualifier.clone(),
            ctor.clone(),
            fields
                .iter()
                .map(|(field, value)| {
                    Ok((
                        field.clone(),
                        rewrite_owner_scoped_expr(
                            value,
                            owner,
                            owner_kind,
                            implicit_var,
                            owner_fields,
                            bound_vars,
                        )?,
                    ))
                })
                .collect::<Result<Vec<_>, String>>()?,
            *span,
        ),
        EExpr::StructCtor(ty, name, fields, span) => EExpr::StructCtor(
            ty.clone(),
            name.clone(),
            fields
                .iter()
                .map(|(field, value)| {
                    Ok((
                        field.clone(),
                        rewrite_owner_scoped_expr(
                            value,
                            owner,
                            owner_kind,
                            implicit_var,
                            owner_fields,
                            bound_vars,
                        )?,
                    ))
                })
                .collect::<Result<Vec<_>, String>>()?,
            *span,
        ),
        EExpr::Lit(ty, lit, span) => EExpr::Lit(ty.clone(), lit.clone(), *span),
        EExpr::Unresolved(name, span) => EExpr::Unresolved(name.clone(), *span),
        EExpr::Sorry(span) => EExpr::Sorry(*span),
        EExpr::Todo(span) => EExpr::Todo(*span),
    })
}

fn rewrite_expr_list(
    exprs: &[EExpr],
    owner: &str,
    owner_kind: OwnerKind,
    implicit_var: &str,
    owner_fields: &BTreeSet<String>,
    bound_vars: &mut Vec<String>,
) -> Result<Vec<EExpr>, String> {
    exprs
        .iter()
        .map(|expr| {
            rewrite_owner_scoped_expr(
                expr,
                owner,
                owner_kind,
                implicit_var,
                owner_fields,
                bound_vars,
            )
        })
        .collect()
}

fn collect_pattern_bindings(pattern: &EPattern, out: &mut Vec<String>) {
    match pattern {
        EPattern::Var(name) => out.push(name.clone()),
        EPattern::Ctor(_, fields) => {
            for (_, inner) in fields {
                collect_pattern_bindings(inner, out);
            }
        }
        EPattern::Wild => {}
        EPattern::Or(left, right) => {
            collect_pattern_bindings(left, out);
            collect_pattern_bindings(right, out);
        }
    }
}

fn owner_var_ty(owner_kind: OwnerKind, owner: &str) -> Ty {
    let _ = (owner_kind, owner);
    Ty::Error
}

fn bool_ty() -> Ty {
    Ty::Builtin(BuiltinTy::Bool)
}

fn semantic_result_name(result: &VerificationResult) -> &str {
    match result {
        VerificationResult::Proved { name, .. }
        | VerificationResult::Admitted { name, .. }
        | VerificationResult::Checked { name, .. }
        | VerificationResult::Counterexample { name, .. }
        | VerificationResult::ScenePass { name, .. }
        | VerificationResult::SceneFail { name, .. }
        | VerificationResult::Unprovable { name, .. }
        | VerificationResult::FnContractProved { name, .. }
        | VerificationResult::FnContractAdmitted { name, .. }
        | VerificationResult::FnContractFailed { name, .. }
        | VerificationResult::LivenessViolation { name, .. }
        | VerificationResult::Deadlock { name, .. } => name,
    }
}

fn semantic_mode_suffix(stores: &[EStoreDecl]) -> String {
    if stores.is_empty() {
        String::new()
    } else {
        let unique_slots: BTreeSet<i64> = stores.iter().map(|store| store.hi).collect();
        if unique_slots.len() == 1 {
            format!(
                "[slots={}]",
                unique_slots
                    .iter()
                    .next()
                    .copied()
                    .unwrap_or(QA_SEMANTIC_DEFAULT_STORE_SLOTS)
            )
        } else {
            let mut scopes = BTreeMap::<String, i64>::new();
            for store in stores {
                scopes.entry(store.entity_type.clone()).or_insert(store.hi);
            }
            let rendered = scopes
                .into_iter()
                .map(|(entity, slots)| format!("{entity}={slots}"))
                .collect::<Vec<_>>()
                .join(",");
            format!("[scopes={rendered}]")
        }
    }
}

fn interpret_semantic_result(
    result: VerificationResult,
    mode_suffix: &str,
) -> Result<TemporalQueryOutcome, String> {
    match result {
        VerificationResult::Proved { .. } => Ok(TemporalQueryOutcome {
            value: true,
            mode: format!("semantic:proved{mode_suffix}"),
            semantic_artifact: None,
        }),
        VerificationResult::Checked { .. } => Ok(TemporalQueryOutcome {
            value: true,
            mode: format!("semantic:checked{mode_suffix}"),
            semantic_artifact: None,
        }),
        VerificationResult::Counterexample { .. }
        | VerificationResult::LivenessViolation { .. }
        | VerificationResult::Deadlock { .. }
        | VerificationResult::SceneFail { .. }
        | VerificationResult::FnContractFailed { .. } => Ok(TemporalQueryOutcome {
            value: false,
            mode: format!("semantic:counterexample{mode_suffix}"),
            semantic_artifact: Some(result),
        }),
        VerificationResult::Unprovable { hint, .. } => Err(format!(
            "semantic QA query could not be proved or checked: {hint}"
        )),
        other => Err(format!(
            "semantic QA query routed to unsupported verifier result: {}",
            semantic_result_name(&other)
        )),
    }
}

fn eval_temporal_formula(graph: &StateGraph, formula: &TemporalFormula) -> BTreeSet<String> {
    match formula {
        TemporalFormula::Bool(value) => {
            if *value {
                graph.states.iter().cloned().collect()
            } else {
                BTreeSet::new()
            }
        }
        TemporalFormula::Predicate(predicate) => graph
            .states
            .iter()
            .filter(|state| state_predicate_holds(predicate, state))
            .cloned()
            .collect(),
        TemporalFormula::Not(inner) => {
            let inner_states = eval_temporal_formula(graph, inner);
            graph
                .states
                .iter()
                .filter(|state| !inner_states.contains(*state))
                .cloned()
                .collect()
        }
        TemporalFormula::And(left, right) => {
            let left_states = eval_temporal_formula(graph, left);
            let right_states = eval_temporal_formula(graph, right);
            left_states.intersection(&right_states).cloned().collect()
        }
        TemporalFormula::Or(left, right) => {
            let left_states = eval_temporal_formula(graph, left);
            let right_states = eval_temporal_formula(graph, right);
            left_states.union(&right_states).cloned().collect()
        }
        TemporalFormula::Implies(left, right) => {
            let left_states = eval_temporal_formula(graph, left);
            let right_states = eval_temporal_formula(graph, right);
            graph
                .states
                .iter()
                .filter(|state| !left_states.contains(*state) || right_states.contains(*state))
                .cloned()
                .collect()
        }
        TemporalFormula::Always(inner) => eval_always(graph, inner),
        TemporalFormula::Eventually(inner) => eval_eventually(graph, inner),
    }
}

fn state_predicate_holds(predicate: &StatePredicate, state: &str) -> bool {
    match predicate {
        StatePredicate::BoolValue(value) => match state {
            "true" => *value,
            "false" => !*value,
            _ => false,
        },
        StatePredicate::Equals(expected) => state == expected,
        StatePredicate::NotEquals(expected) => state != expected,
    }
}

fn eval_always(graph: &StateGraph, inner: &TemporalFormula) -> BTreeSet<String> {
    let inner_states = eval_temporal_formula(graph, inner);
    let adjacency = build_state_adjacency(graph);
    let mut current: BTreeSet<String> = graph.states.iter().cloned().collect();
    loop {
        let next: BTreeSet<String> = graph
            .states
            .iter()
            .filter(|state| {
                inner_states.contains(*state)
                    && adjacency
                        .get(state.as_str())
                        .is_none_or(|succ| succ.iter().all(|next| current.contains(next)))
            })
            .cloned()
            .collect();
        if next == current {
            return next;
        }
        current = next;
    }
}

fn eval_eventually(graph: &StateGraph, inner: &TemporalFormula) -> BTreeSet<String> {
    let adjacency = build_state_adjacency(graph);
    let mut current = eval_temporal_formula(graph, inner);
    loop {
        let next: BTreeSet<String> = graph
            .states
            .iter()
            .filter(|state| {
                current.contains(*state)
                    || adjacency.get(state.as_str()).is_some_and(|succ| {
                        !succ.is_empty() && succ.iter().all(|next| current.contains(next))
                    })
            })
            .cloned()
            .collect();
        if next == current {
            return next;
        }
        current = next;
    }
}

fn build_state_adjacency(graph: &StateGraph) -> HashMap<String, BTreeSet<String>> {
    let mut adjacency: HashMap<String, BTreeSet<String>> = graph
        .states
        .iter()
        .map(|state| (state.clone(), BTreeSet::new()))
        .collect();
    for edge in &graph.transitions {
        match &edge.from {
            Some(from) => {
                adjacency
                    .entry(from.clone())
                    .or_default()
                    .insert(edge.to.clone());
            }
            None => {
                for state in &graph.states {
                    adjacency
                        .entry(state.clone())
                        .or_default()
                        .insert(edge.to.clone());
                }
            }
        }
    }
    adjacency
}

fn expr_kind_name(kind: &ExprKind) -> &'static str {
    match kind {
        ExprKind::Error(_) => "error expression",
        ExprKind::Pipe(_, _) => "pipe expression",
        ExprKind::Unord(_, _) => "unordered composition",
        ExprKind::Conc(_, _) => "concurrent composition",
        ExprKind::Xor(_, _) => "exclusive choice",
        ExprKind::NamedPair(_, _) => "named pair",
        ExprKind::Seq(_, _) => "sequence",
        ExprKind::SameStep(_, _) => "same-step composition",
        ExprKind::Impl(_, _) => "implication",
        ExprKind::Always(_) => "always",
        ExprKind::Eventually(_) => "eventually",
        ExprKind::Until(_, _) => "until",
        ExprKind::Historically(_) => "historically",
        ExprKind::Once(_) => "once",
        ExprKind::Previously(_) => "previously",
        ExprKind::Since(_, _) => "since",
        ExprKind::Aggregate(_, _, _, _, _) => "aggregate",
        ExprKind::Saw(_, _) => "saw",
        ExprKind::AssertExpr(_) => "assert expression",
        ExprKind::AssumeExpr(_) => "assume expression",
        ExprKind::All(_, _, _, _) => "universal quantifier",
        ExprKind::Exists(_, _, _, _) => "existential quantifier",
        ExprKind::SomeQ(_, _, _, _) => "some quantifier",
        ExprKind::NoQ(_, _, _, _) => "no quantifier",
        ExprKind::OneQ(_, _, _, _) => "one quantifier",
        ExprKind::LoneQ(_, _, _, _) => "lone quantifier",
        ExprKind::Let(_, _) => "let expression",
        ExprKind::Lambda(_, _) => "lambda",
        ExprKind::LambdaT(_, _, _) => "typed lambda",
        ExprKind::Match(_, _) => "match",
        ExprKind::Choose(_, _, _) => "choose",
        ExprKind::Assign(_, _) => "assignment",
        ExprKind::Or(_, _) => "or",
        ExprKind::And(_, _) => "and",
        ExprKind::Not(_) => "not",
        ExprKind::Eq(_, _) => "equality",
        ExprKind::NEq(_, _) => "inequality",
        ExprKind::In(_, _) => "membership",
        ExprKind::Lt(_, _) => "less-than comparison",
        ExprKind::Gt(_, _) => "greater-than comparison",
        ExprKind::Le(_, _) => "less-or-equal comparison",
        ExprKind::Ge(_, _) => "greater-or-equal comparison",
        ExprKind::Add(_, _) => "addition",
        ExprKind::Sub(_, _) => "subtraction",
        ExprKind::Mul(_, _) => "multiplication",
        ExprKind::Div(_, _) => "division",
        ExprKind::Mod(_, _) => "modulo",
        ExprKind::Diamond(_, _) => "diamond operator",
        ExprKind::Disjoint(_, _) => "disjointness",
        ExprKind::Neg(_) => "negation",
        ExprKind::Card(_) => "cardinality",
        ExprKind::Prime(_) => "prime expression",
        ExprKind::Field(_, _) => "field access",
        ExprKind::CallR(_, _, _) => "call with refinement args",
        ExprKind::Call(_, _) => "call",
        ExprKind::MapUpdate(_, _, _) => "map update",
        ExprKind::Index(_, _) => "index access",
        ExprKind::SetComp { .. } => "set comprehension",
        ExprKind::Block(_) => "block",
        ExprKind::VarDecl { .. } => "variable declaration",
        ExprKind::While { .. } => "while loop",
        ExprKind::IfElse { .. } => "if/else",
        ExprKind::StructCtor(_, _) => "struct constructor",
        ExprKind::State1(_) => "state atom",
        ExprKind::State1Record(_, _) => "state record constructor",
        ExprKind::State2(_, _) => "qualified state atom",
        ExprKind::State2Record(_, _, _) => "qualified state record constructor",
        ExprKind::State3(_, _, _) => "triple-qualified state atom",
        ExprKind::Qual2(_, _) => "qualified name",
        ExprKind::Qual3(_, _, _) => "triple-qualified name",
        ExprKind::TupleLit(_) => "tuple literal",
        ExprKind::Var(_) => "variable",
        ExprKind::Int(_) => "integer literal",
        ExprKind::Real(_) => "real literal",
        ExprKind::Float(_) => "float literal",
        ExprKind::Str(_) => "string literal",
        ExprKind::True => "true literal",
        ExprKind::False => "false literal",
        ExprKind::Sorry => "sorry",
        ExprKind::Todo => "todo",
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct FieldCandidate {
    owner: String,
    field: String,
}

#[derive(Default)]
struct TemporalTargetCollector {
    field_candidates: BTreeSet<FieldCandidate>,
    owner_candidates: BTreeSet<String>,
    bindings: HashMap<String, String>,
}

impl TemporalTargetCollector {
    fn collect_expr(&mut self, model: &FlowModel, expr: &Expr) {
        match &expr.kind {
            ExprKind::Field(base, field) => {
                if let ExprKind::Var(name) = &base.kind {
                    if let Some(owner) = self.bindings.get(name) {
                        if model
                            .field_graph_meta
                            .contains_key(&(owner.clone(), field.clone()))
                        {
                            self.field_candidates.insert(FieldCandidate {
                                owner: owner.clone(),
                                field: field.clone(),
                            });
                        }
                    } else if model
                        .field_graph_meta
                        .contains_key(&(name.clone(), field.clone()))
                    {
                        self.field_candidates.insert(FieldCandidate {
                            owner: name.clone(),
                            field: field.clone(),
                        });
                    }
                }
                self.collect_expr(model, base);
            }
            ExprKind::Var(name) => {
                let matches: Vec<_> = model
                    .field_graph_meta
                    .values()
                    .filter(|meta| meta.field == *name)
                    .map(|meta| FieldCandidate {
                        owner: meta.owner.clone(),
                        field: meta.field.clone(),
                    })
                    .collect();
                self.field_candidates.extend(matches);
            }
            ExprKind::Always(body)
            | ExprKind::Eventually(body)
            | ExprKind::Historically(body)
            | ExprKind::Once(body)
            | ExprKind::Previously(body)
            | ExprKind::AssertExpr(body)
            | ExprKind::AssumeExpr(body)
            | ExprKind::Not(body)
            | ExprKind::Neg(body)
            | ExprKind::Card(body)
            | ExprKind::Prime(body) => self.collect_expr(model, body),
            ExprKind::NamedPair(_, left) => self.collect_expr(model, left),
            ExprKind::Until(left, right)
            | ExprKind::Since(left, right)
            | ExprKind::Pipe(left, right)
            | ExprKind::Unord(left, right)
            | ExprKind::Conc(left, right)
            | ExprKind::Xor(left, right)
            | ExprKind::Seq(left, right)
            | ExprKind::SameStep(left, right)
            | ExprKind::Impl(left, right)
            | ExprKind::Assign(left, right)
            | ExprKind::Or(left, right)
            | ExprKind::And(left, right)
            | ExprKind::Eq(left, right)
            | ExprKind::NEq(left, right)
            | ExprKind::In(left, right)
            | ExprKind::Lt(left, right)
            | ExprKind::Gt(left, right)
            | ExprKind::Le(left, right)
            | ExprKind::Ge(left, right)
            | ExprKind::Add(left, right)
            | ExprKind::Sub(left, right)
            | ExprKind::Mul(left, right)
            | ExprKind::Div(left, right)
            | ExprKind::Mod(left, right)
            | ExprKind::Diamond(left, right)
            | ExprKind::Disjoint(left, right)
            | ExprKind::Index(left, right) => {
                self.collect_expr(model, left);
                self.collect_expr(model, right);
            }
            ExprKind::All(var, domain, in_expr, body)
            | ExprKind::Exists(var, domain, in_expr, body)
            | ExprKind::SomeQ(var, domain, in_expr, body)
            | ExprKind::NoQ(var, domain, in_expr, body)
            | ExprKind::OneQ(var, domain, in_expr, body)
            | ExprKind::LoneQ(var, domain, in_expr, body)
            | ExprKind::Aggregate(_, var, domain, in_expr, body) => {
                if let Some(owner) = type_ref_owner_name(domain) {
                    if model.entity_names.iter().any(|name| name == &owner)
                        || model.system_names.iter().any(|name| name == &owner)
                    {
                        self.owner_candidates.insert(owner.clone());
                        let previous = self.bindings.insert(var.clone(), owner);
                        if let Some(in_expr) = in_expr {
                            self.collect_expr(model, in_expr);
                        }
                        self.collect_expr(model, body);
                        if let Some(previous) = previous {
                            self.bindings.insert(var.clone(), previous);
                        } else {
                            self.bindings.remove(var);
                        }
                        return;
                    }
                }
                if let Some(in_expr) = in_expr {
                    self.collect_expr(model, in_expr);
                }
                self.collect_expr(model, body);
            }
            ExprKind::Let(bindings, body) => {
                for binding in bindings {
                    self.collect_expr(model, &binding.value);
                    if let Some(ty) = &binding.ty {
                        if let Some(owner) = type_ref_owner_name(ty) {
                            self.bindings.insert(binding.name.clone(), owner);
                        }
                    }
                }
                self.collect_expr(model, body);
                for binding in bindings {
                    self.bindings.remove(&binding.name);
                }
            }
            ExprKind::Lambda(params, body) | ExprKind::LambdaT(params, _, body) => {
                for param in params {
                    if let Some(owner) = type_ref_owner_name(&param.ty) {
                        self.bindings.insert(param.name.clone(), owner);
                    }
                }
                self.collect_expr(model, body);
                for param in params {
                    self.bindings.remove(&param.name);
                }
            }
            ExprKind::Match(scrutinee, arms) => {
                self.collect_expr(model, scrutinee);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        self.collect_expr(model, guard);
                    }
                    self.collect_expr(model, &arm.body);
                }
            }
            ExprKind::Choose(_, domain, where_clause) => {
                if let Some(owner) = type_ref_owner_name(domain) {
                    if model.entity_names.iter().any(|name| name == &owner)
                        || model.system_names.iter().any(|name| name == &owner)
                    {
                        self.owner_candidates.insert(owner);
                    }
                }
                if let Some(where_clause) = where_clause {
                    self.collect_expr(model, where_clause);
                }
            }
            ExprKind::Call(func, args) => {
                self.collect_expr(model, func);
                for arg in args {
                    self.collect_expr(model, arg);
                }
            }
            ExprKind::CallR(func, type_args, args) => {
                self.collect_expr(model, func);
                for arg in type_args {
                    self.collect_expr(model, arg);
                }
                for arg in args {
                    self.collect_expr(model, arg);
                }
            }
            ExprKind::MapUpdate(map, key, value) => {
                self.collect_expr(model, map);
                self.collect_expr(model, key);
                self.collect_expr(model, value);
            }
            ExprKind::SetComp {
                projection,
                domain,
                filter,
                ..
            } => {
                if let Some(owner) = type_ref_owner_name(domain) {
                    if model.entity_names.iter().any(|name| name == &owner)
                        || model.system_names.iter().any(|name| name == &owner)
                    {
                        self.owner_candidates.insert(owner);
                    }
                }
                if let Some(projection) = projection {
                    self.collect_expr(model, projection);
                }
                self.collect_expr(model, filter);
            }
            ExprKind::Block(exprs) | ExprKind::TupleLit(exprs) => {
                for expr in exprs {
                    self.collect_expr(model, expr);
                }
            }
            ExprKind::VarDecl { ty, init, .. } => {
                if let Some(ty) = ty {
                    if let Some(owner) = type_ref_owner_name(ty) {
                        self.owner_candidates.insert(owner);
                    }
                }
                self.collect_expr(model, init);
            }
            ExprKind::While {
                cond,
                contracts,
                body,
            } => {
                self.collect_expr(model, cond);
                for contract in contracts {
                    match contract {
                        abide_syntax::ast::Contract::Requires { expr, .. }
                        | abide_syntax::ast::Contract::Ensures { expr, .. }
                        | abide_syntax::ast::Contract::Invariant { expr, .. } => {
                            self.collect_expr(model, expr);
                        }
                        abide_syntax::ast::Contract::Decreases { measures, .. } => {
                            for measure in measures {
                                self.collect_expr(model, measure);
                            }
                        }
                    }
                }
                self.collect_expr(model, body);
            }
            ExprKind::IfElse {
                cond,
                then_body,
                else_body,
            } => {
                self.collect_expr(model, cond);
                self.collect_expr(model, then_body);
                if let Some(else_body) = else_body {
                    self.collect_expr(model, else_body);
                }
            }
            ExprKind::StructCtor(_, fields)
            | ExprKind::State1Record(_, fields)
            | ExprKind::State2Record(_, _, fields) => {
                for (_, expr) in fields {
                    self.collect_expr(model, expr);
                }
            }
            ExprKind::State3(_, _, _)
            | ExprKind::Qual2(_, _)
            | ExprKind::Qual3(_, _, _)
            | ExprKind::State1(_)
            | ExprKind::State2(_, _)
            | ExprKind::Int(_)
            | ExprKind::Real(_)
            | ExprKind::Float(_)
            | ExprKind::Str(_)
            | ExprKind::True
            | ExprKind::False
            | ExprKind::Sorry
            | ExprKind::Todo
            | ExprKind::Error(_)
            | ExprKind::Saw(_, _) => {}
        }
    }
}

fn type_ref_owner_name(ty: &TypeRef) -> Option<String> {
    match &ty.kind {
        TypeRefKind::Simple(name) | TypeRefKind::Param(name, _) => Some(name.clone()),
        TypeRefKind::Paren(inner)
        | TypeRefKind::Refine(inner, _)
        | TypeRefKind::RefineParam(inner, _)
        | TypeRefKind::NamedRefine(_, inner, _) => type_ref_owner_name(inner),
        TypeRefKind::Fn(_, _) | TypeRefKind::Tuple(_) => None,
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

fn graph_lookup_error(model: &FlowModel, owner: &str, field: &str) -> String {
    if let Some(meta) = model
        .field_graph_meta
        .get(&(owner.to_owned(), field.to_owned()))
    {
        if meta.graphable {
            return format!("no extracted finite state graph for {owner}.{field}");
        }
        return format!(
            "no extracted finite state graph for {owner}.{field}; QA graph queries currently support finite bool- and enum-backed lifecycle fields, but this field has type `{}`",
            meta.type_name
        );
    }

    if model.entity_names.iter().any(|name| name == owner)
        || model.system_names.iter().any(|name| name == owner)
    {
        return format!("no field `{field}` on `{owner}`");
    }

    format!("no entity or system named `{owner}`")
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
    use std::path::PathBuf;

    use abide_sema::loader;

    use super::*;
    use crate::qa::model::*;

    fn commerce_model() -> FlowModel {
        let mut state_graphs = HashMap::new();
        state_graphs.insert(
            ("Order".to_owned(), "status".to_owned()),
            StateGraph {
                owner: "Order".to_owned(),
                owner_kind: OwnerKind::Entity,
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
        state_graphs.insert(
            ("Commerce".to_owned(), "running".to_owned()),
            StateGraph {
                owner: "Commerce".to_owned(),
                owner_kind: OwnerKind::System,
                field: "running".to_owned(),
                states: vec!["false".to_owned(), "true".to_owned()],
                initial: Some("false".to_owned()),
                transitions: vec![TransitionEdge {
                    action: "ship_order".to_owned(),
                    from: Some("false".to_owned()),
                    to: "true".to_owned(),
                }],
            },
        );
        let mut field_graph_meta = HashMap::new();
        field_graph_meta.insert(
            ("Order".to_owned(), "status".to_owned()),
            FieldGraphMeta {
                owner: "Order".to_owned(),
                field: "status".to_owned(),
                owner_kind: OwnerKind::Entity,
                graphable: true,
                type_name: "OrderStatus".to_owned(),
            },
        );
        field_graph_meta.insert(
            ("Order".to_owned(), "total".to_owned()),
            FieldGraphMeta {
                owner: "Order".to_owned(),
                field: "total".to_owned(),
                owner_kind: OwnerKind::Entity,
                graphable: false,
                type_name: "real".to_owned(),
            },
        );
        field_graph_meta.insert(
            ("Commerce".to_owned(), "running".to_owned()),
            FieldGraphMeta {
                owner: "Commerce".to_owned(),
                field: "running".to_owned(),
                owner_kind: OwnerKind::System,
                graphable: true,
                type_name: "bool".to_owned(),
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
            field_graph_meta,
            systems,
            entity_names: vec!["Order".to_owned()],
            system_names: vec!["Commerce".to_owned()],
            type_names: vec!["OrderStatus".to_owned()],
            action_contracts: std::collections::HashMap::new(),
            fsm_decls: std::collections::HashMap::new(),
        }
    }

    fn branching_temporal_model() -> FlowModel {
        let mut state_graphs = HashMap::new();
        state_graphs.insert(
            ("Order".to_owned(), "status".to_owned()),
            StateGraph {
                owner: "Order".to_owned(),
                owner_kind: OwnerKind::Entity,
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
                        from: Some("Confirmed".to_owned()),
                        to: "Cancelled".to_owned(),
                    },
                    TransitionEdge {
                        action: "reopen".to_owned(),
                        from: Some("Cancelled".to_owned()),
                        to: "Confirmed".to_owned(),
                    },
                ],
            },
        );
        let mut field_graph_meta = HashMap::new();
        field_graph_meta.insert(
            ("Order".to_owned(), "status".to_owned()),
            FieldGraphMeta {
                owner: "Order".to_owned(),
                field: "status".to_owned(),
                owner_kind: OwnerKind::Entity,
                graphable: true,
                type_name: "OrderStatus".to_owned(),
            },
        );
        FlowModel {
            state_graphs,
            field_graph_meta,
            systems: HashMap::new(),
            entity_names: vec!["Order".to_owned()],
            system_names: Vec::new(),
            type_names: vec!["OrderStatus".to_owned()],
            action_contracts: HashMap::new(),
            fsm_decls: HashMap::new(),
        }
    }

    fn payload_graph_model() -> FlowModel {
        let mut state_graphs = HashMap::new();
        state_graphs.insert(
            ("Workflow".to_owned(), "mode".to_owned()),
            StateGraph {
                owner: "Workflow".to_owned(),
                owner_kind: OwnerKind::Entity,
                field: "mode".to_owned(),
                states: vec![
                    "Idle".to_owned(),
                    "Ready{armed=false}".to_owned(),
                    "Ready{armed=true}".to_owned(),
                ],
                initial: Some("Ready{armed=false}".to_owned()),
                transitions: vec![TransitionEdge {
                    action: "arm".to_owned(),
                    from: Some("Ready{armed=false}".to_owned()),
                    to: "Ready{armed=true}".to_owned(),
                }],
            },
        );
        let mut field_graph_meta = HashMap::new();
        field_graph_meta.insert(
            ("Workflow".to_owned(), "mode".to_owned()),
            FieldGraphMeta {
                owner: "Workflow".to_owned(),
                field: "mode".to_owned(),
                owner_kind: OwnerKind::Entity,
                graphable: true,
                type_name: "WorkflowMode".to_owned(),
            },
        );
        FlowModel {
            state_graphs,
            field_graph_meta,
            systems: HashMap::new(),
            entity_names: vec!["Workflow".to_owned()],
            system_names: Vec::new(),
            type_names: vec!["WorkflowMode".to_owned()],
            action_contracts: HashMap::new(),
            fsm_decls: HashMap::new(),
        }
    }

    fn semantic_env_and_model(source: &str, name: &str) -> (Env, FlowModel) {
        let dir =
            std::env::temp_dir().join(format!("abide-qa-semantic-{}-{}", std::process::id(), name));
        std::fs::create_dir_all(&dir).expect("create temp dir");
        let path = dir.join(format!("{name}.ab"));
        std::fs::write(&path, source).expect("write spec");
        let (env, load_errors, _paths) = loader::load_files(&[PathBuf::from(&path)]);
        assert!(load_errors.is_empty(), "load errors: {load_errors:?}");
        assert!(
            env.include_load_errors.is_empty(),
            "include load errors: {:?}",
            env.include_load_errors
        );
        let (result, elab_errors) = abide_sema::elab::elaborate_env(env.clone());
        let hard_errors: Vec<_> = elab_errors
            .into_iter()
            .filter(|e| !matches!(e.severity, abide_sema::elab::error::Severity::Warning))
            .collect();
        assert!(hard_errors.is_empty(), "elab errors: {hard_errors:?}");
        let (ir_program, _lower_diag) = ir::lower(&result);
        if path.exists() {
            let _ = std::fs::remove_file(&path);
        }
        let _ = std::fs::remove_dir(&dir);
        (env, crate::qa::extract::extract(&ir_program))
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
    fn exec_reachable_payload_enum_state() {
        let m = payload_graph_model();
        let q = Query::Reachable {
            entity: "Workflow".into(),
            field: "mode".into(),
            state: "Ready{armed=true}".into(),
        };
        assert!(matches!(execute_query(&m, &q), QueryResult::Bool(true)));
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
    fn exec_events_on_system_field() {
        let m = commerce_model();
        match execute_query(
            &m,
            &Query::Events {
                entity: "Commerce".into(),
                field: "running".into(),
            },
        ) {
            QueryResult::NameList(n) => {
                assert!(n.iter().any(|s| s == "Commerce::ship_order"));
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
    fn exec_deadlock_considers_system_field_graphs() {
        let m = commerce_model();
        match execute_query(
            &m,
            &Query::Deadlock {
                system: "Commerce".into(),
            },
        ) {
            QueryResult::Bool(value) => assert!(value),
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
    fn exec_error_unsupported_field_graph_is_precise() {
        let m = commerce_model();
        match execute_query(
            &m,
            &Query::Reachable {
                entity: "Order".into(),
                field: "total".into(),
                state: "1".into(),
            },
        ) {
            QueryResult::Error(msg) => {
                assert!(msg.contains("no extracted finite state graph for Order.total"));
                assert!(msg.contains("type `real`"));
            }
            other => panic!("expected Error, got {other:?}"),
        }
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

    #[test]
    fn exec_temporal_infers_single_field_target() {
        let m = commerce_model();
        let resolved = resolve_temporal_target(&m, None, "running == true").expect("resolve");
        assert_eq!(resolved.display(), "Commerce.running");
        assert!(resolved.inferred);
        assert!(matches!(
            execute_query(
                &m,
                &Query::Temporal {
                    op: TemporalOp::Always,
                    bounds: TemporalBounds::default(),
                    target: None,
                    expr: "running == true".to_owned(),
                },
            ),
            QueryResult::BoolWithMode { value: false, mode } if mode == "graph:field-projection"
        ));
    }

    #[test]
    fn exec_temporal_infers_owner_when_multiple_fields_share_owner() {
        let m = commerce_model();
        let resolved = resolve_temporal_target(
            &m,
            None,
            "(all o: Order | o.status == @Pending or o.total >= 0)",
        )
        .expect("resolve");
        assert_eq!(resolved.display(), "Order");
        assert!(resolved.inferred);
    }

    #[test]
    fn exec_temporal_explicit_target_preserved() {
        let m = commerce_model();
        let resolved = resolve_temporal_target(
            &m,
            Some(&TemporalTarget {
                owner: "Order".to_owned(),
                field: Some("status".to_owned()),
            }),
            "o.status == @Shipped",
        )
        .expect("resolve");
        assert_eq!(resolved.display(), "Order.status");
        assert!(!resolved.inferred);
    }

    #[test]
    fn exec_temporal_ambiguity_is_precise() {
        let mut m = commerce_model();
        m.field_graph_meta.insert(
            ("Account".to_owned(), "status".to_owned()),
            super::super::model::FieldGraphMeta {
                owner: "Account".to_owned(),
                field: "status".to_owned(),
                owner_kind: OwnerKind::Entity,
                graphable: true,
                type_name: "AccountStatus".to_owned(),
            },
        );
        m.entity_names.push("Account".to_owned());
        match execute_query(
            &m,
            &Query::Temporal {
                op: TemporalOp::Always,
                bounds: TemporalBounds::default(),
                target: None,
                expr: "status == @Pending".to_owned(),
            },
        ) {
            QueryResult::Error(msg) => {
                assert!(msg.contains("ambiguous temporal QA target"));
                assert!(msg.contains("Account.status"));
                assert!(msg.contains("Order.status"));
            }
            other => panic!("expected Error, got {other:?}"),
        }
    }

    #[test]
    fn exec_temporal_eventually_is_universal_not_reachability() {
        let m = branching_temporal_model();
        assert!(matches!(
            execute_query(
                &m,
                &Query::Temporal {
                    op: TemporalOp::Eventually,
                    bounds: TemporalBounds::default(),
                    target: Some(TemporalTarget {
                        owner: "Order".to_owned(),
                        field: Some("status".to_owned()),
                    }),
                    expr: "status == @Shipped".to_owned(),
                },
            ),
            QueryResult::BoolWithMode { value: false, mode } if mode == "graph:field-projection"
        ));
        assert!(matches!(
            execute_query(
                &m,
                &Query::Reachable {
                    entity: "Order".to_owned(),
                    field: "status".to_owned(),
                    state: "Shipped".to_owned(),
                },
            ),
            QueryResult::Bool(true)
        ));
    }

    #[test]
    fn exec_temporal_always_uses_universal_future_semantics() {
        let m = branching_temporal_model();
        assert!(matches!(
            execute_query(
                &m,
                &Query::Temporal {
                    op: TemporalOp::Always,
                    bounds: TemporalBounds::default(),
                    target: Some(TemporalTarget {
                        owner: "Order".to_owned(),
                        field: Some("status".to_owned()),
                    }),
                    expr: "status != @Pending".to_owned(),
                },
            ),
            QueryResult::BoolWithMode { value: false, mode } if mode == "graph:field-projection"
        ));
    }

    #[test]
    fn exec_temporal_nested_always_eventually_supported() {
        let m = branching_temporal_model();
        assert!(matches!(
            execute_query(
                &m,
                &Query::Temporal {
                    op: TemporalOp::Always,
                    bounds: TemporalBounds::default(),
                    target: Some(TemporalTarget {
                        owner: "Order".to_owned(),
                        field: Some("status".to_owned()),
                    }),
                    expr: "eventually (status == @Shipped or status == @Cancelled)".to_owned(),
                },
            ),
            QueryResult::BoolWithMode { value: true, mode } if mode == "graph:field-projection"
        ));
    }

    #[test]
    fn exec_temporal_nested_eventually_always_supported() {
        let m = commerce_model();
        assert!(matches!(
            execute_query(
                &m,
                &Query::Temporal {
                    op: TemporalOp::Eventually,
                    bounds: TemporalBounds::default(),
                    target: Some(TemporalTarget {
                        owner: "Order".to_owned(),
                        field: Some("status".to_owned()),
                    }),
                    expr: "always (status == @Shipped or status == @Cancelled)".to_owned(),
                },
            ),
            QueryResult::BoolWithMode { value: true, mode } if mode == "graph:field-projection"
        ));
    }

    #[test]
    fn exec_temporal_owner_scoped_queries_fail_honestly() {
        let (env, model) = semantic_env_and_model(
            r#"
enum OrderStatus = Pending | Shipped

entity Order {
  id: identity
  status: OrderStatus = @Pending
  total: real = 0
}

system Commerce(orders: Store<Order>) {
  revenue: real = 0
  command ship(order: Order)
  command tick()
  step ship(order: Order) requires order.status == @Pending {
    order.status' = @Shipped
    order.total' = order.total
    revenue' = revenue
  }
  step tick() {
    revenue' = revenue
  }
}
"#,
            "owner_scope_entity_inferred",
        );

        match execute_query_with_env(
            &model,
            Some(&env),
            &Query::Temporal {
                op: TemporalOp::Always,
                bounds: TemporalBounds::default(),
                target: None,
                expr: "(all o: Order | o.total >= 0.0)".to_owned(),
            },
        ) {
            QueryResult::BoolWithMode { value: true, mode } => {
                assert!(mode.starts_with("semantic:"));
                assert!(mode.contains("[slots=4]"));
            }
            other => panic!("expected semantic success, got {other:?}"),
        }
    }

    #[test]
    fn exec_temporal_semantic_owner_scope_supports_non_graph_system_fields() {
        let (env, model) = semantic_env_and_model(
            r#"
enum OrderStatus = Pending | Shipped

entity Order {
  id: identity
  status: OrderStatus = @Pending
  total: real = 0
}

system Commerce(orders: Store<Order>) {
  revenue: real = 0
  command ship(order: Order)
  command tick()
  step ship(order: Order) requires order.status == @Pending {
    order.status' = @Shipped
    order.total' = order.total
    revenue' = revenue
  }
  step tick() {
    revenue' = revenue
  }
}
"#,
            "owner_scope_numeric_system",
        );

        match execute_query_with_env(
            &model,
            Some(&env),
            &Query::Temporal {
                op: TemporalOp::Always,
                bounds: TemporalBounds::default(),
                target: Some(TemporalTarget {
                    owner: "Commerce".to_owned(),
                    field: None,
                }),
                expr: "true".to_owned(),
            },
        ) {
            QueryResult::BoolWithMode { value: true, mode } => {
                assert!(mode.starts_with("semantic:"));
                assert!(mode.contains("[slots=4]"));
            }
            other => panic!("expected semantic success, got {other:?}"),
        }
    }

    #[test]
    fn exec_temporal_semantic_deadlock_is_visible_with_verify_defaults() {
        let (env, model) = semantic_env_and_model(
            r#"
enum OrderStatus = Pending | Shipped

entity Order {
  id: identity
  status: OrderStatus = @Pending
  total: real = 0
}

system Commerce(orders: Store<Order>) {
  revenue: real = 0
  command ship(order: Order)
  step ship(order: Order) requires order.status == @Pending {
    order.status' = @Shipped
    order.total' = order.total
    revenue' = revenue
  }
}
"#,
            "semantic_deadlock_visibility",
        );

        match execute_query_with_env(
            &model,
            Some(&env),
            &Query::Temporal {
                op: TemporalOp::Always,
                bounds: TemporalBounds::default(),
                target: Some(TemporalTarget {
                    owner: "Commerce".to_owned(),
                    field: None,
                }),
                expr: "true".to_owned(),
            },
        ) {
            QueryResult::BoolWithMode { value: false, mode } => {
                assert_eq!(mode, "semantic:counterexample[slots=4]");
            }
            other => panic!("expected semantic deadlock/counterexample, got {other:?}"),
        }
    }

    #[test]
    fn exec_temporal_semantic_owner_scope_supports_bare_system_field_predicates() {
        let (env, model) = semantic_env_and_model(
            r#"
enum OrderStatus = Pending | Shipped

entity Order {
  id: identity
  status: OrderStatus = @Pending
  total: real = 0
}

system Commerce(orders: Store<Order>) {
  revenue: real = 0
  command ship(order: Order)
  command tick()
  step ship(order: Order) requires order.status == @Pending {
    order.status' = @Shipped
    order.total' = order.total
    revenue' = revenue
  }
  step tick() {
    revenue' = revenue
  }
}
"#,
            "owner_scope_bare_system_field",
        );

        match execute_query_with_env(
            &model,
            Some(&env),
            &Query::Temporal {
                op: TemporalOp::Always,
                bounds: TemporalBounds::default(),
                target: Some(TemporalTarget {
                    owner: "Commerce".to_owned(),
                    field: None,
                }),
                expr: "revenue >= 0.0".to_owned(),
            },
        ) {
            QueryResult::BoolWithMode { value: true, mode } => {
                assert!(mode.starts_with("semantic:"));
                assert!(mode.contains("[slots=4]"));
            }
            other => panic!("expected semantic success, got {other:?}"),
        }
    }

    #[test]
    fn exec_temporal_semantic_owner_scope_supports_owner_qualified_system_field_predicates() {
        let (env, model) = semantic_env_and_model(
            r#"
enum OrderStatus = Pending | Shipped

entity Order {
  id: identity
  status: OrderStatus = @Pending
  total: real = 0
}

system Commerce(orders: Store<Order>) {
  revenue: real = 0
  command ship(order: Order)
  command tick()
  step ship(order: Order) requires order.status == @Pending {
    order.status' = @Shipped
    order.total' = order.total
    revenue' = revenue
  }
  step tick() {
    revenue' = revenue
  }
}
"#,
            "owner_scope_qualified_system_field",
        );

        match execute_query_with_env(
            &model,
            Some(&env),
            &Query::Temporal {
                op: TemporalOp::Always,
                bounds: TemporalBounds::default(),
                target: Some(TemporalTarget {
                    owner: "Commerce".to_owned(),
                    field: None,
                }),
                expr: "Commerce.revenue >= 0.0".to_owned(),
            },
        ) {
            QueryResult::BoolWithMode { value: true, mode } => {
                assert!(mode.starts_with("semantic:"));
                assert!(mode.contains("[slots=4]"));
            }
            other => panic!("expected semantic success, got {other:?}"),
        }
    }

    #[test]
    fn exec_temporal_semantic_supports_non_graph_system_field_target() {
        let (env, model) = semantic_env_and_model(
            r#"
enum OrderStatus = Pending | Shipped

entity Order {
  id: identity
  status: OrderStatus = @Pending
  total: real = 0
}

system Commerce(orders: Store<Order>) {
  revenue: real = 0
  command ship(order: Order)
  command tick()
  step ship(order: Order) requires order.status == @Pending {
    order.status' = @Shipped
    order.total' = order.total
    revenue' = revenue
  }
  step tick() {
    revenue' = revenue
  }
}
"#,
            "non_graph_system_field_target",
        );

        match execute_query_with_env(
            &model,
            Some(&env),
            &Query::Temporal {
                op: TemporalOp::Always,
                bounds: TemporalBounds::default(),
                target: Some(TemporalTarget {
                    owner: "Commerce".to_owned(),
                    field: Some("revenue".to_owned()),
                }),
                expr: "revenue >= 0.0".to_owned(),
            },
        ) {
            QueryResult::BoolWithMode { value: true, mode } => {
                assert!(mode.starts_with("semantic:"));
                assert!(mode.contains("[slots=4]"));
            }
            other => panic!("expected semantic success, got {other:?}"),
        }
    }

    #[test]
    fn exec_temporal_semantic_supports_non_graph_entity_field_target() {
        let (env, model) = semantic_env_and_model(
            r#"
enum OrderStatus = Pending | Shipped

entity Order {
  id: identity
  status: OrderStatus = @Pending
  total: real = 0
}

system Commerce(orders: Store<Order>) {
  revenue: real = 0
  command ship(order: Order)
  command tick()
  step ship(order: Order) requires order.status == @Pending {
    order.status' = @Shipped
    order.total' = order.total
    revenue' = revenue
  }
  step tick() {
    revenue' = revenue
  }
}
"#,
            "non_graph_entity_field_target",
        );

        match execute_query_with_env(
            &model,
            Some(&env),
            &Query::Temporal {
                op: TemporalOp::Always,
                bounds: TemporalBounds::default(),
                target: Some(TemporalTarget {
                    owner: "Order".to_owned(),
                    field: Some("total".to_owned()),
                }),
                expr: "Order.total >= 0.0".to_owned(),
            },
        ) {
            QueryResult::BoolWithMode { value: true, mode } => {
                assert!(mode.starts_with("semantic:"));
                assert!(mode.contains("[slots=4]"));
            }
            other => panic!("expected semantic success, got {other:?}"),
        }
    }

    #[test]
    fn exec_temporal_semantic_supports_whole_store_system_scope_query() {
        let (env, model) = semantic_env_and_model(
            r#"
enum OrderStatus = Pending | Shipped

entity Order {
  id: identity
  status: OrderStatus = @Pending
  total: real = 0
}

system Commerce(orders: Store<Order>) {
  revenue: real = 0
  command ship(order: Order)
  command tick()
  step ship(order: Order) requires order.status == @Pending {
    order.status' = @Shipped
    order.total' = order.total
    revenue' = revenue
  }
  step tick() {
    revenue' = revenue
  }
}
"#,
            "entity_scope_counterexample",
        );

        match execute_query_with_env(
            &model,
            Some(&env),
            &Query::Temporal {
                op: TemporalOp::Always,
                bounds: TemporalBounds::default(),
                target: Some(TemporalTarget {
                    owner: "Commerce".to_owned(),
                    field: None,
                }),
                expr: "(all o: Order | o.total >= 0.0)".to_owned(),
            },
        ) {
            QueryResult::BoolWithMode { value: true, mode } => {
                assert!(mode.starts_with("semantic:"));
                assert!(mode.contains("[slots=4]"));
            }
            other => panic!("expected semantic success, got {other:?}"),
        }
    }

    #[test]
    fn exec_temporal_semantic_supports_multi_system_entity_scope() {
        let (env, model) = semantic_env_and_model(
            r#"
enum OrderStatus = Pending | Shipped

entity Order {
  id: identity
  status: OrderStatus = @Pending
  total: real = 0
}

system Commerce(orders: Store<Order>) {
  command ship(order: Order)
  command tick()
  step ship(order: Order) requires order.status == @Pending {
    order.status' = @Shipped
  }
  step tick() {}
}

system Audit(orders: Store<Order>) {
  command inspect(order: Order)
  command tick()
  step inspect(order: Order) requires order.status == @Pending {}
  step tick() {}
}
"#,
            "multi_system_entity_scope",
        );

        match execute_query_with_env(
            &model,
            Some(&env),
            &Query::Temporal {
                op: TemporalOp::Always,
                bounds: TemporalBounds::default(),
                target: Some(TemporalTarget {
                    owner: "Order".to_owned(),
                    field: None,
                }),
                expr: "total >= 0.0".to_owned(),
            },
        ) {
            QueryResult::BoolWithMode { value: true, mode } => {
                assert!(mode.starts_with("semantic:"));
                assert!(mode.contains("[slots=4]"));
            }
            other => panic!("expected semantic success, got {other:?}"),
        }
    }

    #[test]
    fn exec_temporal_semantic_respects_custom_slot_bounds() {
        let (env, model) = semantic_env_and_model(
            r#"
enum OrderStatus = Pending | Shipped
enum PaymentStatus = Open | Captured

entity Order {
  id: identity
  status: OrderStatus = @Pending
  total: real = 0
}

entity Payment {
  id: identity
  status: PaymentStatus = @Open
  amount: real = 0
}

system Commerce(orders: Store<Order>, payments: Store<Payment>) {
  revenue: real = 0
  command tick()
  step tick() {
    revenue' = revenue
  }
}
"#,
            "semantic_custom_slot_bounds",
        );

        match execute_query_with_env(
            &model,
            Some(&env),
            &Query::Temporal {
                op: TemporalOp::Always,
                bounds: TemporalBounds {
                    slots: Some(6),
                    scopes: vec![("Order".to_owned(), 2)],
                },
                target: Some(TemporalTarget {
                    owner: "Commerce".to_owned(),
                    field: None,
                }),
                expr: "true".to_owned(),
            },
        ) {
            QueryResult::BoolWithMode { value: true, mode } => {
                assert!(mode.starts_with("semantic:"));
                assert!(mode.contains("[scopes=Order=2,Payment=6]"));
            }
            other => panic!("expected semantic success, got {other:?}"),
        }
    }

    #[test]
    fn exec_temporal_semantic_rejects_unknown_scope_override() {
        let (env, model) = semantic_env_and_model(
            r#"
entity Order {
  id: identity
}

system Commerce(orders: Store<Order>) {
  command tick()
  step tick() {}
}
"#,
            "semantic_unknown_scope_bounds",
        );

        match execute_query_with_env(
            &model,
            Some(&env),
            &Query::Temporal {
                op: TemporalOp::Always,
                bounds: TemporalBounds {
                    slots: Some(1),
                    scopes: vec![("Missing".to_owned(), 2)],
                },
                target: Some(TemporalTarget {
                    owner: "Commerce".to_owned(),
                    field: None,
                }),
                expr: "true".to_owned(),
            },
        ) {
            QueryResult::Error(message) => {
                assert!(message.contains("unknown or unused entity `Missing`"));
            }
            other => panic!("expected clear unknown scope error, got {other:?}"),
        }
    }

    #[test]
    fn exec_temporal_bounds_force_semantic_mode_for_graph_targets() {
        let (env, model) = semantic_env_and_model(
            r#"
enum OrderStatus = Pending | Shipped

entity Order {
  id: identity
  status: OrderStatus = @Pending
}

system Commerce(orders: Store<Order>) {
  command ship(order: Order)
  command tick()
  step ship(order: Order) requires order.status == @Pending {
    order.status' = @Shipped
  }
  step tick() {}
}
"#,
            "semantic_bounds_force_graph_target",
        );

        match execute_query_with_env(
            &model,
            Some(&env),
            &Query::Temporal {
                op: TemporalOp::Always,
                bounds: TemporalBounds {
                    slots: Some(2),
                    scopes: Vec::new(),
                },
                target: Some(TemporalTarget {
                    owner: "Order".to_owned(),
                    field: Some("status".to_owned()),
                }),
                expr: "status == @Pending or status == @Shipped".to_owned(),
            },
        ) {
            QueryResult::BoolWithMode { value: true, mode } => {
                assert!(mode.starts_with("semantic:"));
                assert_eq!(mode, "semantic:proved[slots=2]");
            }
            other => panic!("expected semantic success, got {other:?}"),
        }
    }
}
