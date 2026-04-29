//! System and program collection — systems, commands, actions, queries, procs.

use std::collections::HashSet;

use super::entity::{
    check_fsm_reachability, collect_derived, collect_field, collect_fsms, collect_invariant,
    detect_derived_cycle, synthesize_fsm_is_terminal,
};
use super::expr::{collect_expr, collect_pattern};
use super::{resolve_param_ty, resolve_type_ref};
use crate::ast::{self, Visibility};
use crate::elab::env::{DeclKind, Env};
use crate::elab::error::{ElabError, ErrorKind};
use crate::elab::types::{
    ECommand, EEventAction, EExpr, EExtern, EExternAssume, EInterface, ELetBinding, EMatchArm,
    EMatchScrutinee, EMay, EPred, EProc, EProcDepCond, EProcEdge, EProcNode, EProcUse, EQuery,
    EQuerySig, ESystem, ESystemAction, Ty,
};

// ── Program declarations ────────────────────────────────────────────

/// R4: `program` is the composition root. For verification purposes,
/// a program is lowered into an `ESystem` with no commands/actions/queries.
/// The program's let bindings become system store params, and its
/// invariants travel with the system.
pub(super) fn collect_program(env: &mut Env, pd: &ast::ProgramDecl) {
    let name = &pd.name;
    let store_params: Vec<(String, String)> = pd
        .params
        .iter()
        .map(|p| (p.name.clone(), p.entity_type.clone()))
        .collect();
    let mut invariants = Vec::new();
    let mut let_bindings = Vec::new();
    let mut procs = Vec::new();
    let mut proc_uses = Vec::new();

    for item in &pd.items {
        match item {
            ast::ProgramItem::Let(ld) => {
                let_bindings.push(ELetBinding {
                    name: ld.name.clone(),
                    system_type: ld.system_type.clone(),
                    store_bindings: ld.fields.clone(),
                });
            }
            ast::ProgramItem::Invariant(inv) => {
                invariants.push(collect_invariant(inv));
            }
            ast::ProgramItem::UseProc(use_decl) => {
                proc_uses.push(EProcUse {
                    proc_name: use_decl.proc_name.clone(),
                    args: use_decl.args.clone(),
                    alias: use_decl.alias.clone(),
                    span: Some(use_decl.span),
                });
            }
            ast::ProgramItem::Proc(p) => procs.push(collect_proc(p)),
            ast::ProgramItem::Error(_) => {}
        }
    }

    let es = ESystem {
        name: name.clone(),
        implements: None,
        deps: Vec::new(),
        fields: Vec::new(),
        store_params,
        scopes: Vec::new(),
        commands: Vec::new(),
        actions: Vec::new(),
        queries: Vec::new(),
        fsm_decls: Vec::new(),
        derived_fields: Vec::new(),
        invariants,
        preds: Vec::new(),
        let_bindings,
        procs,
        proc_uses,
        span: Some(pd.span),
    };

    let info = env.make_decl_info(
        DeclKind::System,
        name.clone(),
        None,
        Visibility::Public,
        pd.span,
    );
    env.add_decl(name, info);
    env.insert_system(name, es);
}

pub(super) fn collect_reusable_proc(env: &mut Env, pd: &ast::ProcDecl) {
    let proc_decl = collect_proc(pd);
    let info = env.make_decl_info(
        DeclKind::Proc,
        pd.name.clone(),
        None,
        Visibility::Public,
        pd.span,
    );
    env.add_decl(&pd.name, info);
    env.insert_proc(&pd.name, proc_decl);
}

// ── System declarations ──────────────────────────────────────────────

pub(super) fn collect_interface(env: &mut Env, id: &ast::InterfaceDecl) {
    let name = &id.name;
    let mut commands = Vec::new();
    let mut queries = Vec::new();

    for item in &id.items {
        match item {
            ast::InterfaceItem::Command(c) => commands.push(collect_command(c)),
            ast::InterfaceItem::QuerySig(q) => queries.push(collect_query_sig(q)),
            ast::InterfaceItem::Error(_) => {}
        }
    }

    let iface = EInterface {
        name: name.clone(),
        commands,
        queries,
        span: Some(id.span),
    };

    let info = env.make_decl_info(
        DeclKind::Interface,
        name.clone(),
        None,
        Visibility::Public,
        id.span,
    );
    env.add_decl(name, info);
    env.insert_interface(name, iface);
}

pub(super) fn collect_extern(env: &mut Env, ed: &ast::ExternDecl) {
    let name = &ed.name;
    let mut commands = Vec::new();
    let mut mays = Vec::new();
    let mut assumes = Vec::new();

    for item in &ed.items {
        match item {
            ast::ExternItem::Command(c) => commands.push(collect_command(c)),
            ast::ExternItem::May(m) => mays.push(EMay {
                command: m.command.clone(),
                returns: m.returns.iter().map(collect_expr).collect(),
                span: Some(m.span),
            }),
            ast::ExternItem::Assume(block) => {
                for item in &block.items {
                    match item {
                        ast::ExternAssumeItem::Fair { path, span } => {
                            assumes.push(EExternAssume::Fair(path.segments.clone(), Some(*span)));
                        }
                        ast::ExternAssumeItem::StrongFair { path, span } => {
                            assumes.push(EExternAssume::StrongFair(
                                path.segments.clone(),
                                Some(*span),
                            ));
                        }
                        ast::ExternAssumeItem::Expr { expr, span } => {
                            assumes.push(EExternAssume::Expr(collect_expr(expr), Some(*span)));
                        }
                    }
                }
            }
            ast::ExternItem::Error(_) => {}
        }
    }

    let ext = EExtern {
        name: name.clone(),
        commands,
        mays,
        assumes,
        span: Some(ed.span),
    };

    let info = env.make_decl_info(
        DeclKind::Extern,
        name.clone(),
        None,
        Visibility::Public,
        ed.span,
    );
    env.add_decl(name, info);
    env.insert_extern(name, ext);
}

pub(super) fn collect_system(env: &mut Env, sd: &ast::SystemDecl) {
    let name = &sd.name;
    // collect store params from system constructor.
    let store_params: Vec<(String, String)> = sd
        .params
        .iter()
        .map(|p| (p.name.clone(), p.entity_type.clone()))
        .collect();
    let mut fields = Vec::new();
    let mut deps = Vec::new();
    let mut commands = Vec::new();
    let mut actions = Vec::new();
    let mut queries = Vec::new();
    let mut sys_preds = Vec::new();
    let mut raw_fsms = Vec::new();
    let mut derived_fields = Vec::new();
    let mut invariants = Vec::new();
    let mut explicit_action_names = Vec::new();

    for item in &sd.items {
        match item {
            ast::SystemItem::Field(f) => fields.push(collect_field(f)),
            ast::SystemItem::Dep(d) => deps.push(d.name.clone()),
            ast::SystemItem::Command(c) => {
                let cmd = collect_command(c);
                push_system_command(env, &mut commands, &cmd, name, c.span);
                if c.body.is_some() {
                    actions.push(collect_action_from_command(c));
                }
            }
            ast::SystemItem::Action(s) => {
                explicit_action_names.push((s.name.clone(), s.span));
                actions.push(collect_system_action(s));
            }
            ast::SystemItem::Query(q) => queries.push(collect_query(q)),
            ast::SystemItem::Pred(p) => sys_preds.push(collect_system_pred(p)),
            ast::SystemItem::Fsm(fsm) => raw_fsms.push(fsm),
            // derived field declarations on the
            // system. Body type is inferred from the expression.
            ast::SystemItem::Derived(d) => derived_fields.push(collect_derived(d)),
            // invariant declarations on the
            // system. Body is elaborated as a Boolean expression.
            ast::SystemItem::Invariant(inv) => invariants.push(collect_invariant(inv)),
            ast::SystemItem::Error(_) => {}
        }
    }

    let fsm_decls = collect_fsms(env, name, &fields, &raw_fsms, sd.span);
    synthesize_fsm_is_terminal(env, &fsm_decls, &mut derived_fields);
    for fsm in &fsm_decls {
        check_fsm_reachability(env, name, fsm);
    }

    let command_names: HashSet<&str> = commands.iter().map(|c| c.name.as_str()).collect();
    let mut seen_explicit_actions = HashSet::new();
    for (action_name, span) in &explicit_action_names {
        if command_names.contains(action_name.as_str()) {
            env.errors.push(ElabError::with_span(
                ErrorKind::DuplicateDecl,
                format!(
                    "system `{name}` action `{action_name}` conflicts with public command `{action_name}`"
                ),
                "put the executable body directly on the `command`, or choose a distinct private action name".to_owned(),
                *span,
            ));
        }
        if !seen_explicit_actions.insert(action_name.as_str()) {
            env.errors.push(ElabError::with_span(
                ErrorKind::DuplicateDecl,
                format!("duplicate action `{action_name}` in system `{name}`"),
                String::new(),
                *span,
            ));
        }
    }

    // enforce
    // name uniqueness across commands, queries, derived fields, AND
    // invariants for system-level scope per /.
    // (Pool/use entity names live in their own namespace and are
    // intentionally allowed to reuse names.
    let mut seen: HashSet<String> = HashSet::new();
    for c in &commands {
        seen.insert(c.name.clone());
    }
    for q in &queries {
        if !seen.insert(q.name.clone()) {
            env.errors.push(ElabError::with_span(
                ErrorKind::DuplicateDecl,
                format!(
                    "duplicate name `{}` for query in system `{}` \
                     — conflicts with an earlier command, query, derived \
                     field, or invariant declaration",
                    q.name, name
                ),
                String::new(),
                q.span.unwrap_or(sd.span),
            ));
        }
    }
    for d in &derived_fields {
        if !seen.insert(d.name.clone()) {
            env.errors.push(ElabError::with_span(
                ErrorKind::DuplicateDecl,
                format!(
                    "duplicate name `{}` for derived field in system `{}` \
                     — conflicts with an earlier command, query, derived \
                     field, or invariant declaration",
                    d.name, name
                ),
                String::new(),
                d.span.unwrap_or(sd.span),
            ));
        }
    }
    for inv in &invariants {
        if !seen.insert(inv.name.clone()) {
            env.errors.push(ElabError::with_span(
                ErrorKind::DuplicateDecl,
                format!(
                    "duplicate name `{}` for invariant in system `{}` \
                     — conflicts with an earlier command, query, derived \
                     field, or invariant declaration",
                    inv.name, name
                ),
                String::new(),
                inv.span.unwrap_or(sd.span),
            ));
        }
    }

    // detect cycles in system-level derived
    // field references before the system is committed.
    if let Some(cycle) = detect_derived_cycle(&derived_fields) {
        env.errors.push(ElabError::with_span(
            ErrorKind::CyclicDefinition,
            crate::messages::derived_cycle(&cycle),
            String::new(),
            sd.span,
        ));
    }

    check_system_action_fsm_violations(env, name, &actions, &fsm_decls);

    let es = ESystem {
        name: name.clone(),
        implements: sd.implements.clone(),
        deps,
        fields,
        store_params,
        scopes: Vec::new(),
        commands,
        actions,
        queries,
        fsm_decls,
        derived_fields,
        invariants,
        preds: sys_preds,
        let_bindings: Vec::new(),
        procs: Vec::new(),
        proc_uses: Vec::new(),
        span: Some(sd.span),
    };

    let info = env.make_decl_info(
        DeclKind::System,
        name.clone(),
        None,
        Visibility::Public,
        sd.span,
    );
    env.add_decl(name, info);
    env.insert_system(name, es);
}

fn check_system_action_fsm_violations(
    env: &mut Env,
    system_name: &str,
    actions: &[ESystemAction],
    fsm_decls: &[crate::elab::types::EFsm],
) {
    for fsm in fsm_decls {
        let allowed: HashSet<(String, String)> = fsm
            .rows
            .iter()
            .flat_map(|r| {
                let from = r.from.clone();
                r.targets.iter().map(move |t| (from.clone(), t.clone()))
            })
            .collect();

        for action in actions {
            let assignments = collect_system_prime_assignments(&action.body, &fsm.field);
            for (target_atom, span) in assignments {
                let sources =
                    super::entity::literal_sources_from_requires(&action.requires, &fsm.field);
                if sources.is_empty() {
                    continue;
                }
                for source in sources {
                    if !allowed.contains(&(source.clone(), target_atom.clone())) {
                        let valid: Vec<String> = fsm
                            .rows
                            .iter()
                            .filter(|r| r.from == source)
                            .flat_map(|r| r.targets.iter().cloned())
                            .collect();
                        env.errors.push(ElabError::with_span(
                            ErrorKind::TypeMismatch,
                            crate::messages::fsm_action_violation(
                                system_name,
                                &fsm.field,
                                &action.name,
                                &source,
                                &target_atom,
                                &valid,
                            ),
                            String::new(),
                            span.or(action.span)
                                .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                        ));
                    }
                }
            }
        }
    }
}

fn collect_system_prime_assignments(
    body: &[EEventAction],
    field: &str,
) -> Vec<(String, Option<crate::span::Span>)> {
    let mut out = Vec::new();
    for action in body {
        collect_system_prime_assignments_inner(action, field, &mut out);
    }
    out
}

fn collect_system_prime_assignments_inner(
    action: &EEventAction,
    field: &str,
    out: &mut Vec<(String, Option<crate::span::Span>)>,
) {
    match action {
        EEventAction::Expr(expr) => {
            super::entity::collect_prime_assignments_inner(expr, field, out);
        }
        EEventAction::Choose(_, _, _, body) | EEventAction::ForAll(_, _, body) => {
            for inner in body {
                collect_system_prime_assignments_inner(inner, field, out);
            }
        }
        EEventAction::Match(_, arms) => {
            for arm in arms {
                for inner in &arm.body {
                    collect_system_prime_assignments_inner(inner, field, out);
                }
            }
        }
        EEventAction::Create(_, _, _)
        | EEventAction::LetCrossCall(_, _, _, _)
        | EEventAction::CrossCall(_, _, _)
        | EEventAction::Apply(_, _, _, _) => {}
    }
}

pub(super) fn collect_command(c: &ast::CommandDecl) -> ECommand {
    let params = c
        .params
        .iter()
        .map(|p| (p.name.clone(), resolve_param_ty(p)))
        .collect();
    ECommand {
        name: c.name.clone(),
        params,
        return_type: c.return_type.as_ref().map(resolve_type_ref),
        span: Some(c.span),
    }
}

fn push_system_command(
    env: &mut Env,
    commands: &mut Vec<ECommand>,
    cmd: &ECommand,
    system_name: &str,
    span: crate::span::Span,
) {
    if let Some(existing) = commands.iter().find(|c| c.name == cmd.name) {
        let same_params = existing.params.len() == cmd.params.len()
            && existing
                .params
                .iter()
                .zip(cmd.params.iter())
                .all(|((_, lhs), (_, rhs))| format!("{lhs:?}") == format!("{rhs:?}"));
        let same_return = format!("{:?}", existing.return_type) == format!("{:?}", cmd.return_type);
        if !same_params || !same_return {
            env.errors.push(ElabError::with_span(
                ErrorKind::DuplicateDecl,
                format!(
                    "system `{system_name}` repeats command `{}` with a different signature; repeated command clauses must reuse the same parameter and return types",
                    cmd.name
                ),
                String::new(),
                span,
            ));
        }
        return;
    }
    commands.push(cmd.clone());
}

pub(super) fn collect_system_action(s: &ast::SystemActionDecl) -> ESystemAction {
    let params = s
        .params
        .iter()
        .map(|p| (p.name.clone(), resolve_param_ty(p)))
        .collect();
    let requires = s
        .contracts
        .iter()
        .filter_map(|c| match c {
            ast::Contract::Requires { expr, .. } => Some(collect_expr(expr)),
            _ => None,
        })
        .collect();
    let body = collect_event_items(&s.items);
    ESystemAction {
        name: s.name.clone(),
        params,
        requires,
        body,
        return_expr: s.return_expr.as_ref().map(collect_expr),
        span: Some(s.span),
    }
}

pub(super) fn collect_action_from_command(c: &ast::CommandDecl) -> ESystemAction {
    let body = c
        .body
        .as_ref()
        .expect("collect_action_from_command requires a command body");
    let params = c
        .params
        .iter()
        .map(|p| (p.name.clone(), resolve_param_ty(p)))
        .collect();
    let requires = body
        .contracts
        .iter()
        .filter_map(|contract| match contract {
            ast::Contract::Requires { expr, .. } => Some(collect_expr(expr)),
            _ => None,
        })
        .collect();
    let body_items = collect_event_items(&body.items);
    ESystemAction {
        name: c.name.clone(),
        params,
        requires,
        body: body_items,
        return_expr: body.return_expr.as_ref().map(collect_expr),
        span: Some(c.span),
    }
}

pub(super) fn collect_event_items(items: &[ast::EventItem]) -> Vec<EEventAction> {
    items.iter().map(collect_event_item).collect()
}

pub(super) fn collect_proc(p: &ast::ProcDecl) -> EProc {
    let params = p
        .params
        .iter()
        .map(|param| (param.name.clone(), resolve_param_ty(param)))
        .collect();
    let mut nodes = Vec::new();
    let mut edges = Vec::new();
    let mut proc_uses = Vec::new();
    for item in &p.items {
        match item {
            ast::ProcItem::Node {
                name,
                instance,
                command,
                args,
                ..
            } => nodes.push(EProcNode {
                name: name.clone(),
                instance: instance.clone(),
                command: command.clone(),
                args: args.iter().map(collect_expr).collect(),
            }),
            ast::ProcItem::NeedsEdge {
                target, condition, ..
            } => edges.push(EProcEdge {
                target: target.clone(),
                condition: collect_proc_dep_cond(condition),
            }),
            ast::ProcItem::UseProc(use_decl) => proc_uses.push(EProcUse {
                proc_name: use_decl.proc_name.clone(),
                args: use_decl.args.clone(),
                alias: use_decl.alias.clone(),
                span: Some(use_decl.span),
            }),
            ast::ProcItem::Error(_) => {}
        }
    }
    EProc {
        name: p.name.clone(),
        params,
        requires: p.requires.as_ref().map(collect_expr),
        nodes,
        edges,
        proc_uses,
        span: Some(p.span),
    }
}

fn collect_proc_dep_cond(cond: &ast::ProcDepCond) -> EProcDepCond {
    match cond {
        ast::ProcDepCond::Fact { node, qualifier } => EProcDepCond::Fact {
            node: node.clone(),
            qualifier: qualifier.clone(),
        },
        ast::ProcDepCond::Not(inner) => EProcDepCond::Not(Box::new(collect_proc_dep_cond(inner))),
        ast::ProcDepCond::And(left, right) => EProcDepCond::And(
            Box::new(collect_proc_dep_cond(left)),
            Box::new(collect_proc_dep_cond(right)),
        ),
        ast::ProcDepCond::Or(left, right) => EProcDepCond::Or(
            Box::new(collect_proc_dep_cond(left)),
            Box::new(collect_proc_dep_cond(right)),
        ),
    }
}

pub(super) fn collect_query(q: &ast::QueryDecl) -> EQuery {
    let params = q
        .params
        .iter()
        .map(|p| (p.name.clone(), resolve_param_ty(p)))
        .collect();
    let body = collect_expr(&q.body);
    EQuery {
        name: q.name.clone(),
        params,
        body,
        span: Some(q.span),
    }
}

pub(super) fn collect_query_sig(q: &ast::QuerySigDecl) -> EQuerySig {
    let params = q
        .params
        .iter()
        .map(|p| (p.name.clone(), resolve_param_ty(p)))
        .collect();
    EQuerySig {
        name: q.name.clone(),
        params,
        return_type: resolve_type_ref(&q.return_type),
        span: Some(q.span),
    }
}

pub(super) fn collect_event_item(item: &ast::EventItem) -> EEventAction {
    match item {
        ast::EventItem::Choose(cb) => EEventAction::Choose(
            cb.var.clone(),
            Ty::Named(cb.ty.clone()),
            collect_expr(&cb.condition),
            cb.body.iter().map(collect_event_item).collect(),
        ),
        ast::EventItem::For(fb) => EEventAction::ForAll(
            fb.var.clone(),
            Ty::Named(fb.ty.clone()),
            fb.body.iter().map(collect_event_item).collect(),
        ),
        ast::EventItem::Create(cb) => EEventAction::Create(
            cb.ty.clone(),
            cb.store.clone(),
            cb.fields
                .iter()
                .map(|f| (f.name.clone(), collect_expr(&f.value)))
                .collect(),
        ),
        ast::EventItem::LetCall(call) => EEventAction::LetCrossCall(
            call.name.clone(),
            call.system.clone(),
            call.command.clone(),
            call.args.iter().map(collect_expr).collect(),
        ),
        ast::EventItem::Match(mb) => EEventAction::Match(
            collect_match_scrutinee(&mb.scrutinee),
            mb.arms.iter().map(collect_match_arm).collect(),
        ),
        ast::EventItem::Expr(e) => classify_expr(&collect_expr(e)),
        ast::EventItem::Error(_) => EEventAction::Expr(EExpr::Todo(None)),
    }
}

fn collect_match_scrutinee(scrutinee: &ast::EventMatchScrutinee) -> EMatchScrutinee {
    match scrutinee {
        ast::EventMatchScrutinee::Var(name, _) => EMatchScrutinee::Var(name.clone()),
        ast::EventMatchScrutinee::Call {
            system,
            command,
            args,
            ..
        } => EMatchScrutinee::CrossCall(
            system.clone(),
            command.clone(),
            args.iter().map(collect_expr).collect(),
        ),
    }
}

fn collect_match_arm(arm: &ast::EventMatchArm) -> EMatchArm {
    EMatchArm {
        pattern: collect_pattern(&arm.pattern),
        guard: arm.guard.as_deref().map(collect_expr),
        body: collect_event_items(&arm.items),
    }
}

/// Classify a collected expression as a structured action when possible.
/// Detects cross-system calls (`Sys::event(args)`) and action applies (`o.action(args)`).
pub(super) fn classify_expr(expr: &EExpr) -> EEventAction {
    match expr {
        // Cross-system call: Sys::event(args)
        EExpr::Call(_, callee, args, _) => {
            if let EExpr::Qual(_, sys, ev, _) = callee.as_ref() {
                return EEventAction::CrossCall(sys.clone(), ev.clone(), extract_named_args(args));
            }
            // Action apply: o.action(args)
            if let EExpr::Field(_, target, action, _) = callee.as_ref() {
                return EEventAction::Apply(
                    *target.clone(),
                    action.clone(),
                    Vec::new(),
                    extract_named_args(args),
                );
            }
            EEventAction::Expr(expr.clone())
        }
        // Action apply with refs: o.action[refs](args)
        EExpr::CallR(_, callee, refs, args, _) => {
            if let EExpr::Field(_, target, action, _) = callee.as_ref() {
                return EEventAction::Apply(
                    *target.clone(),
                    action.clone(),
                    extract_named_args(refs),
                    extract_named_args(args),
                );
            }
            EEventAction::Expr(expr.clone())
        }
        _ => EEventAction::Expr(expr.clone()),
    }
}

pub(super) fn extract_named_args(args: &[EExpr]) -> Vec<EExpr> {
    args.iter()
        .map(|e| match e {
            EExpr::NamedPair(_, _, inner, _) => *inner.clone(),
            other => other.clone(),
        })
        .collect()
}

/// Collect a system-local pred (not registered in global namespace).
pub(super) fn collect_system_pred(pd: &ast::PredDecl) -> EPred {
    let params: Vec<(String, Ty)> = pd
        .params
        .iter()
        .map(|p| (p.name.clone(), resolve_param_ty(p)))
        .collect();
    EPred {
        name: pd.name.clone(),
        params,
        body: collect_expr(&pd.body),
        span: Some(pd.span),
        file: None,
    }
}
