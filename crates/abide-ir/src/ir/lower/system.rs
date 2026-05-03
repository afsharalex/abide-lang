//! System lowering — systems, actions, queries, procs.

use std::collections::{HashMap, HashSet};

use super::super::types::{
    IRAction, IRActionMatchArm, IRActionMatchScrutinee, IRCommand, IRCreateField, IREntity, IRExpr,
    IRField, IRFunction, IRPattern, IRStoreParam, IRSystem, IRSystemAction, IRTransParam,
    IRTransRef, IRTransition, IRType, IRUpdate, LitVal,
};
use super::expr::lower_pattern;
use super::qualify::{qualify_action_query_vars, qualify_query_vars_scoped};
use super::{
    canonical, extract_param_refinements, flatten_system_fields, lower_derived_field, lower_expr,
    lower_guard_refs, lower_invariant, lower_pred, lower_ty, unwrap_alias, LowerCtx,
};
use crate::elab::types as E;

pub(super) fn lower_system(
    es: &E::ESystem,
    all_systems: &[E::ESystem],
    aliases: &HashMap<String, String>,
    ctx: &LowerCtx<'_>,
) -> IRSystem {
    // Start with entities from the system's own store params.
    let mut entities: Vec<String> = es
        .store_params
        .iter()
        .map(|store| canonical(aliases, &store.entity_type).to_owned())
        .collect();
    // For programs with let bindings, include composed systems' entities
    // so the verifier can see all pooled entity types.
    for lb in &es.let_bindings {
        let sys_name = canonical(aliases, &lb.system_type);
        if let Some(composed) = all_systems.iter().find(|s| s.name == sys_name) {
            for store in &composed.store_params {
                let canonical_ent = canonical(aliases, &store.entity_type).to_owned();
                if !entities.contains(&canonical_ent) {
                    entities.push(canonical_ent);
                }
            }
        }
    }
    for proc in &es.procs {
        let hidden = proc_instance_entity_name(&es.name, &proc.name);
        if !entities.contains(&hidden) {
            entities.push(hidden);
        }
    }
    let let_binding_system_types: HashMap<&str, String> = es
        .let_bindings
        .iter()
        .map(|lb| {
            (
                lb.name.as_str(),
                canonical(aliases, &lb.system_type).to_owned(),
            )
        })
        .collect();

    let mut ir_system = IRSystem {
        name: es.name.clone(),
        store_params: es
            .store_params
            .iter()
            .map(|store| IRStoreParam {
                name: store.name.clone(),
                entity_type: canonical(aliases, &store.entity_type).to_owned(),
            })
            .collect(),
        fields: flatten_system_fields(&es.fields, ctx),
        entities,
        commands: es
            .commands
            .iter()
            .map(|c| crate::ir::types::IRCommand {
                name: c.name.clone(),
                params: c
                    .params
                    .iter()
                    .map(|(pn, pt)| {
                        let base_ty = match unwrap_alias(pt) {
                            E::Ty::Refinement(base, _) => base.as_ref(),
                            _ => pt,
                        };
                        IRTransParam {
                            name: pn.clone(),
                            ty: lower_ty(base_ty, ctx),
                        }
                    })
                    .collect(),
                return_type: c.return_type.as_ref().map(|t| lower_ty(t, ctx)),
            })
            .collect(),
        actions: {
            // Build bare→qualified name map for queries AND system-local preds.
            // All system-scoped names (queries + preds) need rewriting so
            // DefEnv resolves them under qualified names at verification time.
            let scoped_renames: HashMap<String, String> = es
                .queries
                .iter()
                .map(|q| (q.name.clone(), format!("{}::{}", es.name, q.name)))
                .chain(
                    es.preds
                        .iter()
                        .map(|p| (p.name.clone(), format!("{}::{}", es.name, p.name))),
                )
                .collect();
            es.actions
                .iter()
                .map(|action| {
                    let mut s = lower_system_action(action, aliases, ctx);
                    if !scoped_renames.is_empty() {
                        let param_bound: std::collections::HashSet<String> =
                            s.params.iter().map(|p| p.name.clone()).collect();
                        s.guard =
                            qualify_query_vars_scoped(&s.guard, &scoped_renames, &param_bound);
                        s.body = s
                            .body
                            .iter()
                            .map(|a| qualify_action_query_vars(a, &scoped_renames, &param_bound))
                            .collect();
                        if let Some(ref re) = s.return_expr {
                            s.return_expr =
                                Some(qualify_query_vars_scoped(re, &scoped_renames, &param_bound));
                        }
                    }
                    s
                })
                .collect()
        },
        fsm_decls: es.fsm_decls.iter().map(super::lower_fsm).collect(),
        derived_fields: {
            // Build the same scoped rename map for derived/invariant/pred/query bodies.
            let scoped_renames: HashMap<String, String> = es
                .queries
                .iter()
                .map(|q| (q.name.clone(), format!("{}::{}", es.name, q.name)))
                .chain(
                    es.preds
                        .iter()
                        .map(|p| (p.name.clone(), format!("{}::{}", es.name, p.name))),
                )
                .collect();
            let empty_bound = std::collections::HashSet::new();
            es.derived_fields
                .iter()
                .map(|d| {
                    let mut df = lower_derived_field(d, ctx);
                    if !scoped_renames.is_empty() {
                        df.body =
                            qualify_query_vars_scoped(&df.body, &scoped_renames, &empty_bound);
                    }
                    df
                })
                .collect()
        },
        invariants: {
            let scoped_renames: HashMap<String, String> = es
                .queries
                .iter()
                .map(|q| (q.name.clone(), format!("{}::{}", es.name, q.name)))
                .chain(
                    es.preds
                        .iter()
                        .map(|p| (p.name.clone(), format!("{}::{}", es.name, p.name))),
                )
                .collect();
            let empty_bound = std::collections::HashSet::new();
            es.invariants
                .iter()
                .map(|inv| {
                    let mut ii = lower_invariant(inv, ctx);
                    if !scoped_renames.is_empty() {
                        ii.body =
                            qualify_query_vars_scoped(&ii.body, &scoped_renames, &empty_bound);
                    }
                    ii
                })
                .collect()
        },
        preds: {
            let scoped_renames: HashMap<String, String> = es
                .queries
                .iter()
                .map(|q| (q.name.clone(), format!("{}::{}", es.name, q.name)))
                .chain(
                    es.preds
                        .iter()
                        .map(|p| (p.name.clone(), format!("{}::{}", es.name, p.name))),
                )
                .collect();
            es.preds
                .iter()
                .map(|p| {
                    let mut ip = lower_pred(p, ctx);
                    if !scoped_renames.is_empty() {
                        let param_bound: std::collections::HashSet<String> =
                            p.params.iter().map(|(n, _)| n.clone()).collect();
                        ip.body =
                            qualify_query_vars_scoped(&ip.body, &scoped_renames, &param_bound);
                    }
                    ip
                })
                .collect()
        },
        queries: {
            let scoped_renames: HashMap<String, String> = es
                .queries
                .iter()
                .map(|q| (q.name.clone(), format!("{}::{}", es.name, q.name)))
                .chain(
                    es.preds
                        .iter()
                        .map(|p| (p.name.clone(), format!("{}::{}", es.name, p.name))),
                )
                .collect();
            es.queries
                .iter()
                .map(|q| {
                    let mut iq = lower_query(q, ctx);
                    if !scoped_renames.is_empty() {
                        let param_bound: std::collections::HashSet<String> =
                            iq.params.iter().map(|p| p.name.clone()).collect();
                        iq.body =
                            qualify_query_vars_scoped(&iq.body, &scoped_renames, &param_bound);
                    }
                    iq
                })
                .collect()
        },
        let_bindings: es
            .let_bindings
            .iter()
            .map(|lb| crate::ir::types::IRLetBinding {
                name: lb.name.clone(),
                system_type: canonical(aliases, &lb.system_type).to_owned(),
                store_bindings: lb.store_bindings.clone(),
            })
            .collect(),
        procs: es.procs.iter().map(|p| lower_proc(p, ctx)).collect(),
    };

    if !es.procs.is_empty() {
        for proc in &es.procs {
            synthesize_proc_workflow(
                &mut ir_system,
                &es.name,
                proc,
                &let_binding_system_types,
                all_systems,
                aliases,
                ctx,
            );
        }
    }

    ir_system
}

pub(super) fn lower_extern(ext: &E::EExtern, ctx: &LowerCtx<'_>) -> IRSystem {
    let commands: Vec<crate::ir::types::IRCommand> = ext
        .commands
        .iter()
        .map(|c| crate::ir::types::IRCommand {
            name: c.name.clone(),
            params: c
                .params
                .iter()
                .map(|(pn, pt)| IRTransParam {
                    name: pn.clone(),
                    ty: lower_ty(pt, ctx),
                })
                .collect(),
            return_type: c.return_type.as_ref().map(|t| lower_ty(t, ctx)),
        })
        .collect();

    let mut actions = Vec::new();
    for may in &ext.mays {
        let command = ext.commands.iter().find(|c| c.name == may.command);
        let params: Vec<IRTransParam> = command
            .map(|c| {
                c.params
                    .iter()
                    .map(|(pn, pt)| IRTransParam {
                        name: pn.clone(),
                        ty: lower_ty(pt, ctx),
                    })
                    .collect()
            })
            .unwrap_or_default();

        for ret in &may.returns {
            actions.push(IRSystemAction {
                name: may.command.clone(),
                params: params.clone(),
                guard: crate::ir::types::IRExpr::Lit {
                    ty: crate::ir::types::IRType::Bool,
                    value: crate::ir::types::LitVal::Bool { value: true },
                    span: may.span,
                },
                body: Vec::new(),
                return_expr: Some(lower_expr(ret, ctx)),
            });
        }
    }

    let mut preds = vec![hidden_extern_pred("__abide_extern__marker")];
    for (idx, assume) in ext.assumes.iter().enumerate() {
        match assume {
            E::EExternAssume::Fair(path, _) if path.len() == 1 => {
                preds.push(hidden_extern_pred(&format!(
                    "__abide_extern_assume_wf__{}",
                    path[0]
                )));
            }
            E::EExternAssume::StrongFair(path, _) if path.len() == 1 => {
                preds.push(hidden_extern_pred(&format!(
                    "__abide_extern_assume_sf__{}",
                    path[0]
                )));
            }
            E::EExternAssume::Expr(expr, _) => {
                preds.push(hidden_extern_pred_with_body(
                    &format!("__abide_extern_assume_expr__{}", idx + 1),
                    lower_expr(expr, ctx),
                ));
            }
            _ => {}
        }
    }

    IRSystem {
        name: ext.name.clone(),
        store_params: Vec::new(),
        fields: Vec::new(),
        entities: Vec::new(),
        commands,
        actions,
        fsm_decls: Vec::new(),
        derived_fields: Vec::new(),
        invariants: Vec::new(),
        queries: Vec::new(),
        preds,
        let_bindings: Vec::new(),
        procs: Vec::new(),
    }
}

fn hidden_extern_pred(name: &str) -> IRFunction {
    hidden_extern_pred_with_body(
        name,
        IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        },
    )
}

fn hidden_extern_pred_with_body(name: &str, body: IRExpr) -> IRFunction {
    IRFunction {
        name: name.to_owned(),
        ty: IRType::Bool,
        body,
        prop_target: None,
        requires: Vec::new(),
        ensures: Vec::new(),
        decreases: None,
        span: None,
        file: None,
    }
}

/// lower an elaborated proc to its IR form.
pub(super) fn lower_proc(p: &E::EProc, ctx: &LowerCtx<'_>) -> crate::ir::types::IRProc {
    crate::ir::types::IRProc {
        name: p.name.clone(),
        params: p
            .params
            .iter()
            .map(|(pn, pt)| {
                let base_ty = match unwrap_alias(pt) {
                    E::Ty::Refinement(base, _) => base.as_ref(),
                    _ => pt,
                };
                IRTransParam {
                    name: pn.clone(),
                    ty: lower_ty(base_ty, ctx),
                }
            })
            .collect(),
        requires: p.requires.as_ref().map(|expr| lower_expr(expr, ctx)),
        nodes: p
            .nodes
            .iter()
            .map(|n| crate::ir::types::IRProcNode {
                name: n.name.clone(),
                instance: n.instance.clone(),
                command: n.command.clone(),
                args: n.args.iter().map(|a| lower_expr(a, ctx)).collect(),
            })
            .collect(),
        edges: p
            .edges
            .iter()
            .map(|e| crate::ir::types::IRProcEdge {
                target: e.target.clone(),
                condition: lower_proc_dep_cond(&e.condition),
            })
            .collect(),
    }
}

pub(super) fn synthesize_proc_entities(
    es: &E::ESystem,
    _aliases: &HashMap<String, String>,
    ctx: &LowerCtx<'_>,
) -> Vec<IREntity> {
    es.procs
        .iter()
        .map(|proc| {
            let mut outcome_ports: HashMap<String, HashSet<String>> = HashMap::new();
            for edge in &proc.edges {
                collect_proc_condition_ports(&edge.condition, &mut outcome_ports);
            }
            let mut fields = Vec::new();
            for (name, ty) in &proc.params {
                let base_ty = match unwrap_alias(ty) {
                    E::Ty::Refinement(base, _) => base.as_ref(),
                    _ => ty,
                };
                fields.push(IRField {
                    name: proc_param_field_name(name),
                    ty: lower_ty(base_ty, ctx),
                    default: None,
                    initial_constraint: None,
                });
            }
            for node in &proc.nodes {
                fields.push(IRField {
                    name: node_done_field_name(node),
                    ty: IRType::Bool,
                    default: Some(bool_lit_expr(false, proc.span)),
                    initial_constraint: None,
                });
                if let Some(ports) = outcome_ports.get(&node.name) {
                    for port in ports {
                        fields.push(IRField {
                            name: node_outcome_field_name(node, port),
                            ty: IRType::Bool,
                            default: Some(bool_lit_expr(false, proc.span)),
                            initial_constraint: None,
                        });
                    }
                }
            }
            let mut transitions = Vec::new();
            for node in &proc.nodes {
                transitions.push(IRTransition {
                    name: proc_node_mark_transition_name(node),
                    refs: Vec::<IRTransRef>::new(),
                    params: Vec::new(),
                    guard: bool_lit_expr(true, proc.span),
                    updates: vec![IRUpdate {
                        field: node_done_field_name(node),
                        value: bool_lit_expr(true, proc.span),
                    }],
                    postcondition: None,
                });
                if let Some(ports) = outcome_ports.get(&node.name) {
                    for port in ports {
                        transitions.push(IRTransition {
                            name: proc_node_outcome_transition_name(node, port),
                            refs: Vec::<IRTransRef>::new(),
                            params: Vec::new(),
                            guard: bool_lit_expr(true, proc.span),
                            updates: vec![
                                IRUpdate {
                                    field: node_done_field_name(node),
                                    value: bool_lit_expr(true, proc.span),
                                },
                                IRUpdate {
                                    field: node_outcome_field_name(node, port),
                                    value: bool_lit_expr(true, proc.span),
                                },
                            ],
                            postcondition: None,
                        });
                    }
                }
            }
            IREntity {
                name: proc_instance_entity_name(&es.name, &proc.name),
                fields,
                transitions,
                derived_fields: Vec::new(),
                invariants: Vec::new(),
                fsm_decls: Vec::new(),
            }
        })
        .collect()
}

struct ProcNodeLowerInfo {
    outcome_ports: Vec<String>,
    system: String,
    return_variants: Vec<String>,
}

fn synthesize_proc_workflow(
    ir_system: &mut IRSystem,
    owner_system: &str,
    proc: &E::EProc,
    let_binding_system_types: &HashMap<&str, String>,
    all_systems: &[E::ESystem],
    aliases: &HashMap<String, String>,
    ctx: &LowerCtx<'_>,
) {
    let proc_params = lower_proc_params(proc, ctx);
    let mut incoming: HashMap<&str, Vec<&E::EProcEdge>> = HashMap::new();
    let mut outcome_ports: HashMap<String, HashSet<String>> = HashMap::new();
    for edge in &proc.edges {
        incoming.entry(edge.target.as_str()).or_default().push(edge);
        collect_proc_condition_ports(&edge.condition, &mut outcome_ports);
    }
    let hidden_entity = proc_instance_entity_name(owner_system, &proc.name);
    let return_variants_by_node: HashMap<String, Vec<String>> = proc
        .nodes
        .iter()
        .map(|node| {
            (
                node.name.clone(),
                proc_node_return_variants(node, let_binding_system_types, all_systems, aliases),
            )
        })
        .collect();

    ir_system.commands.push(IRCommand {
        name: proc.name.clone(),
        params: proc_params.clone(),
        return_type: None,
    });
    ir_system.actions.push(IRSystemAction {
        name: proc.name.clone(),
        params: proc_params.clone(),
        guard: proc_start_guard(proc, ctx),
        body: vec![IRAction::Create {
            entity: hidden_entity.clone(),
            fields: proc
                .params
                .iter()
                .map(|(name, ty)| IRCreateField {
                    name: proc_param_field_name(name),
                    value: IRExpr::Var {
                        name: name.clone(),
                        ty: lower_ty(
                            match unwrap_alias(ty) {
                                E::Ty::Refinement(base, _) => base.as_ref(),
                                _ => ty,
                            },
                            ctx,
                        ),
                        span: proc.span,
                    },
                })
                .collect(),
        }],
        return_expr: None,
    });

    for node in &proc.nodes {
        let step_name = proc_node_action_name(proc, &node.name);
        ir_system.commands.push(IRCommand {
            name: step_name.clone(),
            params: proc_params.clone(),
            return_type: None,
        });
        ir_system.actions.push(IRSystemAction {
            name: step_name,
            params: proc_params.clone(),
            guard: bool_lit_expr(true, proc.span),
            body: lower_proc_node_actions(
                proc,
                node,
                ProcNodeLowerInfo {
                    outcome_ports: outcome_ports
                        .get(&node.name)
                        .map(|ports| {
                            let mut ports: Vec<String> = ports.iter().cloned().collect();
                            ports.sort();
                            ports
                        })
                        .unwrap_or_default(),
                    system: let_binding_system_types
                        .get(node.instance.as_str())
                        .cloned()
                        .unwrap_or_else(|| canonical(aliases, &node.instance).to_owned()),
                    return_variants: return_variants_by_node
                        .get(&node.name)
                        .cloned()
                        .unwrap_or_default(),
                },
                &hidden_entity,
                incoming
                    .get(node.name.as_str())
                    .cloned()
                    .unwrap_or_default(),
                ctx,
            ),
            return_expr: None,
        });
    }
}

fn lower_proc_params(proc: &E::EProc, ctx: &LowerCtx<'_>) -> Vec<IRTransParam> {
    proc.params
        .iter()
        .map(|(pn, pt)| {
            let base_ty = match unwrap_alias(pt) {
                E::Ty::Refinement(base, _) => base.as_ref(),
                _ => pt,
            };
            IRTransParam {
                name: pn.clone(),
                ty: lower_ty(base_ty, ctx),
            }
        })
        .collect()
}

fn lower_proc_node_actions(
    proc: &E::EProc,
    node: &E::EProcNode,
    node_info: ProcNodeLowerInfo,
    hidden_entity: &str,
    incoming: Vec<&E::EProcEdge>,
    ctx: &LowerCtx<'_>,
) -> Vec<IRAction> {
    let filter = proc_instance_filter(proc, node, &incoming, hidden_entity, ctx);
    let args: Vec<IRExpr> = node.args.iter().map(|arg| lower_expr(arg, ctx)).collect();

    if !node_info.outcome_ports.is_empty() {
        let mut actions = vec![IRAction::LetCrossCall {
            name: node.name.clone(),
            system: node_info.system.clone(),
            command: node.command.clone(),
            args,
        }];
        let mut arms = Vec::new();
        for port in &node_info.return_variants {
            let transition = if node_info
                .outcome_ports
                .iter()
                .any(|used_port| used_port == port)
            {
                proc_node_outcome_transition_name(node, port)
            } else {
                proc_node_mark_transition_name(node)
            };
            arms.push(IRActionMatchArm {
                pattern: IRPattern::PCtor {
                    name: port.clone(),
                    fields: Vec::new(),
                },
                guard: None,
                body: vec![IRAction::Choose {
                    var: proc_instance_var(proc),
                    entity: hidden_entity.to_owned(),
                    filter: Box::new(filter.clone()),
                    ops: vec![IRAction::Apply {
                        target: proc_instance_var(proc),
                        transition,
                        refs: Vec::new(),
                        args: Vec::new(),
                    }],
                }],
            });
        }
        arms.push(IRActionMatchArm {
            pattern: IRPattern::PWild,
            guard: None,
            body: vec![IRAction::Choose {
                var: proc_instance_var(proc),
                entity: hidden_entity.to_owned(),
                filter: Box::new(filter),
                ops: vec![IRAction::Apply {
                    target: proc_instance_var(proc),
                    transition: proc_node_mark_transition_name(node),
                    refs: Vec::new(),
                    args: Vec::new(),
                }],
            }],
        });
        actions.push(IRAction::Match {
            scrutinee: IRActionMatchScrutinee::Var {
                name: node.name.clone(),
            },
            arms,
        });
        actions
    } else {
        vec![IRAction::Choose {
            var: proc_instance_var(proc),
            entity: hidden_entity.to_owned(),
            filter: Box::new(filter),
            ops: vec![
                IRAction::CrossCall {
                    system: node_info.system,
                    command: node.command.clone(),
                    args,
                },
                IRAction::Apply {
                    target: proc_instance_var(proc),
                    transition: proc_node_mark_transition_name(node),
                    refs: Vec::new(),
                    args: Vec::new(),
                },
            ],
        }]
    }
}

fn proc_instance_entity_name(system: &str, proc: &str) -> String {
    format!("__abide_procinst__{system}__{proc}")
}

fn proc_instance_var(proc: &E::EProc) -> String {
    format!("__abide_procinst__{}", proc.name)
}

fn proc_param_field_name(param: &str) -> String {
    format!("param__{param}")
}

fn node_done_field_name(node: &E::EProcNode) -> String {
    format!("done__{}", node.name)
}

fn node_outcome_field_name(node: &E::EProcNode, port: &str) -> String {
    format!("outcome__{}__{port}", node.name)
}

fn proc_node_action_name(proc: &E::EProc, node: &str) -> String {
    format!("__abide_proc_{}__node__{node}", proc.name)
}

fn proc_node_mark_transition_name(node: &E::EProcNode) -> String {
    format!("__abide_mark__{}", node.name)
}

fn proc_node_outcome_transition_name(node: &E::EProcNode, port: &str) -> String {
    format!("__abide_mark__{}__{port}", node.name)
}

fn bool_lit(value: bool, span: Option<crate::span::Span>) -> IRExpr {
    IRExpr::Lit {
        ty: IRType::Bool,
        value: LitVal::Bool { value },
        span,
    }
}

fn bool_lit_expr(value: bool, span: Option<crate::span::Span>) -> IRExpr {
    bool_lit(value, span)
}

fn bool_not(expr: IRExpr) -> IRExpr {
    IRExpr::UnOp {
        op: "OpNot".to_owned(),
        operand: Box::new(expr),
        ty: IRType::Bool,
        span: None,
    }
}

fn bool_and(left: IRExpr, right: IRExpr) -> IRExpr {
    IRExpr::BinOp {
        op: "OpAnd".to_owned(),
        left: Box::new(left),
        right: Box::new(right),
        ty: IRType::Bool,
        span: None,
    }
}

fn bool_or(left: IRExpr, right: IRExpr) -> IRExpr {
    IRExpr::BinOp {
        op: "OpOr".to_owned(),
        left: Box::new(left),
        right: Box::new(right),
        ty: IRType::Bool,
        span: None,
    }
}

fn proc_start_guard(proc: &E::EProc, ctx: &LowerCtx<'_>) -> IRExpr {
    proc.requires.as_ref().map_or_else(
        || bool_lit_expr(true, proc.span),
        |req| lower_expr(req, ctx),
    )
}

fn entity_field_expr(field_name: &str, ty: IRType, span: Option<crate::span::Span>) -> IRExpr {
    IRExpr::Var {
        name: field_name.to_owned(),
        ty,
        span,
    }
}

fn proc_instance_filter(
    proc: &E::EProc,
    node: &E::EProcNode,
    incoming: &[&E::EProcEdge],
    _hidden_entity: &str,
    ctx: &LowerCtx<'_>,
) -> IRExpr {
    let mut filter = bool_not(entity_field_expr(
        &node_done_field_name(node),
        IRType::Bool,
        proc.span,
    ));
    for (name, ty) in &proc.params {
        let base_ty = match unwrap_alias(ty) {
            E::Ty::Refinement(base, _) => base.as_ref(),
            _ => ty,
        };
        let lhs = entity_field_expr(
            &proc_param_field_name(name),
            lower_ty(base_ty, ctx),
            proc.span,
        );
        let rhs = IRExpr::Var {
            name: name.clone(),
            ty: lower_ty(base_ty, ctx),
            span: proc.span,
        };
        filter = bool_and(
            filter,
            IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(lhs),
                right: Box::new(rhs),
                ty: IRType::Bool,
                span: proc.span,
            },
        );
    }
    for edge in incoming {
        filter = bool_and(
            filter,
            encode_proc_dep_cond(node, &edge.condition, proc.span),
        );
    }
    filter
}

fn proc_node_return_variants(
    node: &E::EProcNode,
    let_binding_system_types: &HashMap<&str, String>,
    all_systems: &[E::ESystem],
    aliases: &HashMap<String, String>,
) -> Vec<String> {
    let Some(sys_type) = let_binding_system_types.get(node.instance.as_str()) else {
        return Vec::new();
    };
    let sys_name = canonical(aliases, sys_type).to_owned();
    let Some(system) = all_systems.iter().find(|system| system.name == sys_name) else {
        return Vec::new();
    };
    let Some(command) = system
        .commands
        .iter()
        .find(|command| command.name == node.command)
    else {
        return Vec::new();
    };
    match &command.return_type {
        Some(E::Ty::Enum(_, variants)) => variants.clone(),
        _ => Vec::new(),
    }
}

fn lower_proc_dep_cond(cond: &E::EProcDepCond) -> crate::ir::types::IRProcDepCond {
    match cond {
        E::EProcDepCond::Fact { node, qualifier } => crate::ir::types::IRProcDepCond::Fact {
            node: node.clone(),
            qualifier: qualifier.clone(),
        },
        E::EProcDepCond::Not(inner) => crate::ir::types::IRProcDepCond::Not {
            condition: Box::new(lower_proc_dep_cond(inner)),
        },
        E::EProcDepCond::And(left, right) => crate::ir::types::IRProcDepCond::And {
            left: Box::new(lower_proc_dep_cond(left)),
            right: Box::new(lower_proc_dep_cond(right)),
        },
        E::EProcDepCond::Or(left, right) => crate::ir::types::IRProcDepCond::Or {
            left: Box::new(lower_proc_dep_cond(left)),
            right: Box::new(lower_proc_dep_cond(right)),
        },
    }
}

fn collect_proc_condition_ports(
    cond: &E::EProcDepCond,
    outcome_ports: &mut HashMap<String, HashSet<String>>,
) {
    match cond {
        E::EProcDepCond::Fact { node, qualifier } => {
            if let Some(qualifier) = qualifier {
                if qualifier != "done" {
                    outcome_ports
                        .entry(node.clone())
                        .or_default()
                        .insert(qualifier.clone());
                }
            }
        }
        E::EProcDepCond::Not(inner) => collect_proc_condition_ports(inner, outcome_ports),
        E::EProcDepCond::And(left, right) | E::EProcDepCond::Or(left, right) => {
            collect_proc_condition_ports(left, outcome_ports);
            collect_proc_condition_ports(right, outcome_ports);
        }
    }
}

fn encode_proc_dep_cond(
    _current_node: &E::EProcNode,
    cond: &E::EProcDepCond,
    span: Option<crate::span::Span>,
) -> IRExpr {
    match cond {
        E::EProcDepCond::Fact { node, qualifier } => match qualifier.as_deref() {
            None | Some("done") => entity_field_expr(&format!("done__{node}"), IRType::Bool, span),
            Some(port) => {
                entity_field_expr(&format!("outcome__{node}__{port}"), IRType::Bool, span)
            }
        },
        E::EProcDepCond::Not(inner) => bool_not(encode_proc_dep_cond(_current_node, inner, span)),
        E::EProcDepCond::And(left, right) => bool_and(
            encode_proc_dep_cond(_current_node, left, span),
            encode_proc_dep_cond(_current_node, right, span),
        ),
        E::EProcDepCond::Or(left, right) => bool_or(
            encode_proc_dep_cond(_current_node, left, span),
            encode_proc_dep_cond(_current_node, right, span),
        ),
    }
}

/// lower an elaborated query to its IR form.
pub(super) fn lower_query(q: &E::EQuery, ctx: &LowerCtx<'_>) -> super::super::types::IRQuery {
    super::super::types::IRQuery {
        name: q.name.clone(),
        params: q
            .params
            .iter()
            .map(|(pn, pt)| {
                let base_ty = match unwrap_alias(pt) {
                    E::Ty::Refinement(base, _) => base.as_ref(),
                    _ => pt,
                };
                IRTransParam {
                    name: pn.clone(),
                    ty: lower_ty(base_ty, ctx),
                }
            })
            .collect(),
        body: lower_expr(&q.body, ctx),
    }
}

/// Lower an ESystemAction into an IRSystemAction.
pub(super) fn lower_system_action(
    action: &E::ESystemAction,
    aliases: &HashMap<String, String>,
    ctx: &LowerCtx<'_>,
) -> IRSystemAction {
    // Extract refinement predicates from params and add to guard
    let refinement_reqs = extract_param_refinements(&action.params);
    let mut all_requires: Vec<&E::EExpr> = refinement_reqs.iter().collect();
    all_requires.extend(action.requires.iter());
    IRSystemAction {
        name: action.name.clone(),
        params: action
            .params
            .iter()
            .map(|(pn, pt)| {
                let base_ty = match unwrap_alias(pt) {
                    E::Ty::Refinement(base, _) => base.as_ref(),
                    _ => pt,
                };
                IRTransParam {
                    name: pn.clone(),
                    ty: lower_ty(base_ty, ctx),
                }
            })
            .collect(),
        guard: lower_guard_refs(&all_requires, ctx),
        body: action
            .body
            .iter()
            .map(|a| lower_event_action(a, aliases, ctx))
            .collect(),
        return_expr: action.return_expr.as_ref().map(|e| lower_expr(e, ctx)),
    }
}

pub(super) fn lower_event_action(
    ea: &E::EEventAction,
    aliases: &HashMap<String, String>,
    ctx: &LowerCtx<'_>,
) -> IRAction {
    match ea {
        E::EEventAction::Choose(v, ty, guard, body) => IRAction::Choose {
            var: v.clone(),
            entity: ty.name().to_owned(),
            filter: Box::new(lower_expr(guard, ctx)),
            ops: body
                .iter()
                .map(|a| lower_event_action(a, aliases, ctx))
                .collect(),
        },
        E::EEventAction::ForAll(v, ty, body) => IRAction::ForAll {
            var: v.clone(),
            entity: ty.name().to_owned(),
            ops: body
                .iter()
                .map(|a| lower_event_action(a, aliases, ctx))
                .collect(),
        },
        E::EEventAction::Create(entity, _store, fields) => IRAction::Create {
            entity: canonical(aliases, entity).to_owned(),
            fields: fields
                .iter()
                .map(|(fn_, fe)| IRCreateField {
                    name: fn_.clone(),
                    value: lower_expr(fe, ctx),
                })
                .collect(),
        },
        E::EEventAction::LetCrossCall(name, sys, ev, args) => IRAction::LetCrossCall {
            name: name.clone(),
            system: canonical(aliases, sys).to_owned(),
            command: ev.clone(),
            args: args.iter().map(|a| lower_expr(a, ctx)).collect(),
        },
        E::EEventAction::CrossCall(sys, ev, args) => IRAction::CrossCall {
            system: canonical(aliases, sys).to_owned(),
            command: ev.clone(),
            args: args.iter().map(|a| lower_expr(a, ctx)).collect(),
        },
        E::EEventAction::Match(scrutinee, arms) => IRAction::Match {
            scrutinee: match scrutinee {
                E::EMatchScrutinee::Var(name) => IRActionMatchScrutinee::Var { name: name.clone() },
                E::EMatchScrutinee::CrossCall(system, command, args) => {
                    IRActionMatchScrutinee::CrossCall {
                        system: canonical(aliases, system).to_owned(),
                        command: command.clone(),
                        args: args.iter().map(|a| lower_expr(a, ctx)).collect(),
                    }
                }
            },
            arms: arms
                .iter()
                .map(|arm| IRActionMatchArm {
                    pattern: lower_pattern(&arm.pattern),
                    guard: arm.guard.as_ref().map(|g| lower_expr(g, ctx)),
                    body: arm
                        .body
                        .iter()
                        .map(|a| lower_event_action(a, aliases, ctx))
                        .collect(),
                })
                .collect(),
        },
        E::EEventAction::Apply(target, act, refs, args) => IRAction::Apply {
            target: extract_target_name(target),
            transition: act.clone(),
            refs: refs.iter().map(extract_target_name).collect(),
            args: args.iter().map(|a| lower_expr(a, ctx)).collect(),
        },
        E::EEventAction::Expr(e) => IRAction::ExprStmt {
            expr: lower_expr(e, ctx),
        },
    }
}

pub(super) fn extract_target_name(e: &E::EExpr) -> String {
    match e {
        E::EExpr::Var(_, n, _) => n.clone(),
        _ => "_".to_owned(),
    }
}
