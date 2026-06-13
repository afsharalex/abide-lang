//! Post-resolution validation passes.

use super::super::env::Env;
use super::super::error::{ElabError, ErrorKind};
use super::super::types::{
    BuiltinTy, EContract, EEventAction, EExpr, EExternAssume, EFieldDefault, EMatchScrutinee,
    ESceneWhen, Ty,
};
use super::collection::validate_set_comp_binder_shape;
use std::collections::{HashMap, HashSet};

fn walk_expr(expr: &EExpr, visit: &mut impl FnMut(&EExpr)) {
    visit(expr);
    match expr {
        EExpr::Always(_, e, _)
        | EExpr::Eventually(_, e, _)
        | EExpr::Historically(_, e, _)
        | EExpr::Once(_, e, _)
        | EExpr::Previously(_, e, _)
        | EExpr::UnOp(_, _, e, _)
        | EExpr::Field(_, e, _, _)
        | EExpr::Prime(_, e, _)
        | EExpr::Assert(_, e, _)
        | EExpr::Assume(_, e, _)
        | EExpr::Card(_, e, _)
        | EExpr::NamedPair(_, _, e, _) => walk_expr(e, visit),
        EExpr::Choose(_, _, _, predicate, _) => {
            if let Some(predicate) = predicate {
                walk_expr(predicate, visit);
            }
        }
        EExpr::BinOp(_, _, a, b, _)
        | EExpr::Until(_, a, b, _)
        | EExpr::Since(_, a, b, _)
        | EExpr::Assign(_, a, b, _)
        | EExpr::Seq(_, a, b, _)
        | EExpr::SameStep(_, a, b, _)
        | EExpr::In(_, a, b, _)
        | EExpr::Pipe(_, a, b, _)
        | EExpr::Index(_, a, b, _) => {
            walk_expr(a, visit);
            walk_expr(b, visit);
        }
        EExpr::Quant(_, _, _, _, body, _) | EExpr::Lam(_, _, body, _) => {
            walk_expr(body, visit);
        }
        EExpr::Call(_, f, args, _) => {
            walk_expr(f, visit);
            for arg in args {
                walk_expr(arg, visit);
            }
        }
        EExpr::CallR(_, f, args, refs, _) => {
            walk_expr(f, visit);
            for arg in args {
                walk_expr(arg, visit);
            }
            for reference in refs {
                walk_expr(reference, visit);
            }
        }
        EExpr::Let(bindings, body, _) => {
            for (_, _, value) in bindings {
                walk_expr(value, visit);
            }
            walk_expr(body, visit);
        }
        EExpr::Match(scrutinee, arms, _) => {
            walk_expr(scrutinee, visit);
            for (_, guard, body) in arms {
                if let Some(guard) = guard {
                    walk_expr(guard, visit);
                }
                walk_expr(body, visit);
            }
        }
        EExpr::MapUpdate(_, map, key, value, _) => {
            walk_expr(map, visit);
            walk_expr(key, visit);
            walk_expr(value, visit);
        }
        EExpr::SetComp(_, projection, _, _, source, filter, _) => {
            if let Some(projection) = projection {
                walk_expr(projection, visit);
            }
            if let Some(source) = source {
                walk_expr(source, visit);
            }
            walk_expr(filter, visit);
        }
        EExpr::RelComp(_, projection, bindings, filter, _) => {
            walk_expr(projection, visit);
            for binding in bindings {
                if let Some(source) = &binding.source {
                    walk_expr(source, visit);
                }
            }
            walk_expr(filter, visit);
        }
        EExpr::TupleLit(_, elems, _) | EExpr::SetLit(_, elems, _) | EExpr::SeqLit(_, elems, _) => {
            for elem in elems {
                walk_expr(elem, visit);
            }
        }
        EExpr::MapLit(_, entries, _) => {
            for (key, value) in entries {
                walk_expr(key, visit);
                walk_expr(value, visit);
            }
        }
        EExpr::QualCall(_, _, _, args, _) => {
            for arg in args {
                walk_expr(arg, visit);
            }
        }
        EExpr::CtorRecord(_, _, _, fields, _) | EExpr::StructCtor(_, _, fields, _) => {
            for (_, value) in fields {
                walk_expr(value, visit);
            }
        }
        EExpr::Aggregate(_, _, _, _, body, in_filter, _) => {
            walk_expr(body, visit);
            if let Some(in_filter) = in_filter {
                walk_expr(in_filter, visit);
            }
        }
        EExpr::Saw(_, _, _, args, _) => {
            for arg in args.iter().flatten() {
                walk_expr(arg, visit);
            }
        }
        EExpr::Block(exprs, _) => {
            for expr in exprs {
                walk_expr(expr, visit);
            }
        }
        EExpr::VarDecl(_, _, init, rest, _) => {
            walk_expr(init, visit);
            walk_expr(rest, visit);
        }
        EExpr::While(cond, contracts, body, _) => {
            walk_expr(cond, visit);
            for contract in contracts {
                walk_contract(contract, visit);
            }
            walk_expr(body, visit);
        }
        EExpr::IfElse(cond, then_body, else_body, _) => {
            walk_expr(cond, visit);
            walk_expr(then_body, visit);
            if let Some(else_body) = else_body {
                walk_expr(else_body, visit);
            }
        }
        EExpr::Lit(..)
        | EExpr::Var(..)
        | EExpr::Qual(..)
        | EExpr::Sorry(_)
        | EExpr::Todo(_)
        | EExpr::Unresolved(..) => {}
    }
}

fn walk_contract(contract: &EContract, visit: &mut impl FnMut(&EExpr)) {
    match contract {
        EContract::Requires(expr) | EContract::Ensures(expr) | EContract::Invariant(expr) => {
            walk_expr(expr, visit);
        }
        EContract::Decreases { measures, .. } => {
            for measure in measures {
                walk_expr(measure, visit);
            }
        }
    }
}

fn walk_field_default(default: &EFieldDefault, visit: &mut impl FnMut(&EExpr)) {
    match default {
        EFieldDefault::Value(expr) | EFieldDefault::Where(expr) => walk_expr(expr, visit),
        EFieldDefault::In(values) => {
            for value in values {
                walk_expr(value, visit);
            }
        }
    }
}

fn walk_event_action(action: &EEventAction, visit: &mut impl FnMut(&EExpr)) {
    match action {
        EEventAction::Choose(_, _, guard, body) => {
            walk_expr(guard, visit);
            for action in body {
                walk_event_action(action, visit);
            }
        }
        EEventAction::ForAll(_, _, body) => {
            for action in body {
                walk_event_action(action, visit);
            }
        }
        EEventAction::Create(_, _, fields) => {
            for (_, value) in fields {
                walk_expr(value, visit);
            }
        }
        EEventAction::CrossCall(_, _, args) | EEventAction::LetCrossCall(_, _, _, args) => {
            for arg in args {
                walk_expr(arg, visit);
            }
        }
        EEventAction::Match(scrutinee, arms) => {
            if let EMatchScrutinee::CrossCall(_, _, args) = scrutinee {
                for arg in args {
                    walk_expr(arg, visit);
                }
            }
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    walk_expr(guard, visit);
                }
                for action in &arm.body {
                    walk_event_action(action, visit);
                }
            }
        }
        EEventAction::Apply(target, _, refs, args) => {
            walk_expr(target, visit);
            for reference in refs {
                walk_expr(reference, visit);
            }
            for arg in args {
                walk_expr(arg, visit);
            }
        }
        EEventAction::Expr(expr) => walk_expr(expr, visit),
    }
}

fn walk_scene_when(when: &ESceneWhen, visit: &mut impl FnMut(&EExpr)) {
    match when {
        ESceneWhen::Action { args, .. } => {
            for arg in args {
                walk_expr(arg, visit);
            }
        }
        ESceneWhen::Assume(expr) => walk_expr(expr, visit),
    }
}

fn walk_env_exprs(env: &Env, visit: &mut impl FnMut(&EExpr)) {
    for verify in &env.verifies {
        for constraint in &verify.initial_constraints {
            walk_expr(constraint, visit);
        }
        for assert in &verify.asserts {
            walk_expr(assert, visit);
        }
    }
    for theorem in &env.theorems {
        for show in &theorem.shows {
            walk_expr(show, visit);
        }
        for invariant in &theorem.invariants {
            walk_expr(invariant, visit);
        }
    }
    for lemma in &env.lemmas {
        for expr in &lemma.body {
            walk_expr(expr, visit);
        }
    }
    for axiom in &env.axioms {
        walk_expr(&axiom.body, visit);
    }
    for scene in &env.scenes {
        for given in &scene.givens {
            if let Some(condition) = &given.condition {
                walk_expr(condition, visit);
            }
        }
        for when in &scene.whens {
            walk_scene_when(when, visit);
        }
        for constraint in &scene.given_constraints {
            walk_expr(constraint, visit);
        }
        for then_expr in &scene.thens {
            walk_expr(then_expr, visit);
        }
    }
    for prop in env.props.values() {
        walk_expr(&prop.body, visit);
    }
    for pred in env.preds.values() {
        walk_expr(&pred.body, visit);
    }
    for constant in env.consts.values() {
        walk_expr(&constant.body, visit);
    }
    for external in env.externs.values() {
        for may in &external.mays {
            for value in &may.returns {
                walk_expr(value, visit);
            }
        }
        for assume in &external.assumes {
            if let EExternAssume::Expr(expr, _) = assume {
                walk_expr(expr, visit);
            }
        }
    }
    for entity in env.entities.values() {
        for field in &entity.fields {
            if let Some(default) = &field.default {
                walk_field_default(default, visit);
            }
        }
        for action in &entity.actions {
            for req in &action.requires {
                walk_expr(req, visit);
            }
            for ens in &action.ensures {
                walk_expr(ens, visit);
            }
            for expr in &action.body {
                walk_expr(expr, visit);
            }
        }
        for invariant in &entity.invariants {
            walk_expr(&invariant.body, visit);
        }
        for derived in &entity.derived_fields {
            walk_expr(&derived.body, visit);
        }
    }
    for system in env.systems.values() {
        for field in &system.fields {
            if let Some(default) = &field.default {
                walk_field_default(default, visit);
            }
        }
        for action in &system.actions {
            for req in &action.requires {
                walk_expr(req, visit);
            }
            for body_item in &action.body {
                walk_event_action(body_item, visit);
            }
            if let Some(return_expr) = &action.return_expr {
                walk_expr(return_expr, visit);
            }
        }
        for query in &system.queries {
            walk_expr(&query.body, visit);
        }
        for pred in &system.preds {
            walk_expr(&pred.body, visit);
        }
        for invariant in &system.invariants {
            walk_expr(&invariant.body, visit);
        }
        for derived in &system.derived_fields {
            walk_expr(&derived.body, visit);
        }
        for proc in &system.procs {
            if let Some(requires) = &proc.requires {
                walk_expr(requires, visit);
            }
            for node in &proc.nodes {
                for arg in &node.args {
                    walk_expr(arg, visit);
                }
            }
        }
    }
    for func in env.fns.values() {
        walk_expr(&func.body, visit);
        for contract in &func.contracts {
            walk_contract(contract, visit);
        }
    }
}

/// Resolve and validate extern-boundary `saw` expressions.
///
/// Current policy:
/// - only explicit `saw Extern::command(args)` is allowed
/// - unqualified `saw command(...)` is rejected
/// - system-qualified `saw System::command(...)` is rejected
/// - 3+ segment paths are rejected
/// - extern existence and arity are validated here
pub(super) fn validate_saw_expressions(env: &mut Env, ctx: &super::Ctx) {
    let mut errors = Vec::new();

    fn validate_saw_expr(
        expr: &EExpr,
        arities: &HashMap<(String, String), usize>,
        extern_names: &HashSet<String>,
        errors: &mut Vec<(String, Option<crate::span::Span>)>,
    ) {
        let EExpr::Saw(_, sys, evt, args, sp) = expr else {
            return;
        };

        if sys.is_empty() {
            errors.push((crate::messages::SAW_EXTERN_QUALIFIED_ONLY.to_owned(), *sp));
        }

        if !sys.is_empty() {
            if sys.contains("::") || !extern_names.contains(sys) {
                errors.push((crate::messages::SAW_EXTERN_QUALIFIED_ONLY.to_owned(), *sp));
            } else {
                let key = (sys.clone(), evt.clone());
                if let Some(&expected) = arities.get(&key) {
                    if args.len() != expected {
                        errors.push((
                            crate::messages::saw_arity_mismatch(sys, evt, expected, args.len()),
                            *sp,
                        ));
                    }
                } else {
                    errors.push((crate::messages::SAW_UNKNOWN_EVENT.to_owned(), *sp));
                }
            }
        }
    }

    let arities = ctx.event_arities.clone();
    let extern_names: HashSet<String> = env.externs.keys().cloned().collect();
    walk_env_exprs(env, &mut |expr| {
        validate_saw_expr(expr, &arities, &extern_names, &mut errors);
    });

    for (msg, sp) in errors {
        let mut err = crate::elab::error::ElabError::new(
            crate::elab::error::ErrorKind::TypeMismatch,
            msg,
            "saw validation",
        );
        err.span = sp;
        env.errors.push(err);
    }
}

/// validate that aggregate body types match
/// their kind. `count` body must be bool; `sum`/`product`/`min`/`max`
/// body must be numeric (int, real, float). Runs after resolve so
/// body types are fully resolved.
pub(super) fn validate_aggregate_bodies(env: &mut Env) {
    use crate::ast::AggKind;
    use crate::elab::types::{BuiltinTy, Ty};

    fn validate_aggregate_expr(
        expr: &EExpr,
        errors: &mut Vec<(String, Option<crate::span::Span>)>,
    ) {
        let EExpr::Aggregate(_, kind, _, _, body, _in_filter, sp) = expr else {
            return;
        };

        let body_ty = body.ty();
        match kind {
            AggKind::Count => {
                if !matches!(body_ty, Ty::Builtin(BuiltinTy::Bool)) && !matches!(body_ty, Ty::Error)
                {
                    errors.push((
                        format!(
                            "`count` body must be a bool predicate, got `{}`",
                            body_ty.name()
                        ),
                        *sp,
                    ));
                }
            }
            AggKind::Sum | AggKind::Product | AggKind::Min | AggKind::Max => {
                let is_numeric = matches!(
                    body_ty,
                    Ty::Builtin(BuiltinTy::Int | BuiltinTy::Real | BuiltinTy::Float) | Ty::Error
                );
                if !is_numeric {
                    errors.push((
                        format!(
                            "`{kind:?}` body must be numeric (int, real, or float), got `{}`",
                            body_ty.name()
                        ),
                        *sp,
                    ));
                }
            }
        }
    }

    let mut errors = Vec::new();
    walk_env_exprs(env, &mut |expr| {
        validate_aggregate_expr(expr, &mut errors);
    });

    for (msg, sp) in errors {
        let mut err = crate::elab::error::ElabError::new(
            crate::elab::error::ErrorKind::TypeMismatch,
            msg,
            "aggregate body type",
        );
        err.span = sp;
        env.errors.push(err);
    }
}

/// Validate that set comprehensions do not implicitly range over
/// non-enumerable real domains. A finite source is still allowed, e.g.
/// `{ x | x in Set(0.0, 0.5) where x >= 0.0 }`.
pub(super) fn validate_set_comprehension_sources(env: &mut Env) {
    let mut errors = Vec::new();

    for v in &env.verifies {
        for a in &v.asserts {
            validate_set_comprehension_expr(a, &mut errors);
        }
    }
    for t in &env.theorems {
        for s in &t.shows {
            validate_set_comprehension_expr(s, &mut errors);
        }
        for inv in &t.invariants {
            validate_set_comprehension_expr(inv, &mut errors);
        }
    }
    for l in &env.lemmas {
        for b in &l.body {
            validate_set_comprehension_expr(b, &mut errors);
        }
    }
    for a in &env.axioms {
        validate_set_comprehension_expr(&a.body, &mut errors);
    }
    for scene in &env.scenes {
        for e in &scene.given_constraints {
            validate_set_comprehension_expr(e, &mut errors);
        }
        for e in &scene.thens {
            validate_set_comprehension_expr(e, &mut errors);
        }
    }
    for p in env.props.values() {
        validate_set_comprehension_expr(&p.body, &mut errors);
    }
    for p in env.preds.values() {
        validate_set_comprehension_expr(&p.body, &mut errors);
    }
    for c in env.consts.values() {
        validate_set_comprehension_expr(&c.body, &mut errors);
    }
    for entity in env.entities.values() {
        for field in &entity.fields {
            if let Some(default) = &field.default {
                validate_set_comprehension_field_default(default, &mut errors);
            }
        }
        for action in &entity.actions {
            for req in &action.requires {
                validate_set_comprehension_expr(req, &mut errors);
            }
            for ens in &action.ensures {
                validate_set_comprehension_expr(ens, &mut errors);
            }
            for body in &action.body {
                validate_set_comprehension_expr(body, &mut errors);
            }
        }
        for inv in &entity.invariants {
            validate_set_comprehension_expr(&inv.body, &mut errors);
        }
        for d in &entity.derived_fields {
            validate_set_comprehension_expr(&d.body, &mut errors);
        }
    }
    for system in env.systems.values() {
        for field in &system.fields {
            if let Some(default) = &field.default {
                validate_set_comprehension_field_default(default, &mut errors);
            }
        }
        for action in &system.actions {
            for req in &action.requires {
                validate_set_comprehension_expr(req, &mut errors);
            }
            for item in &action.body {
                validate_set_comprehension_event_action(item, &mut errors);
            }
            if let Some(ret) = &action.return_expr {
                validate_set_comprehension_expr(ret, &mut errors);
            }
        }
        for query in &system.queries {
            validate_set_comprehension_expr(&query.body, &mut errors);
        }
        for pred in &system.preds {
            validate_set_comprehension_expr(&pred.body, &mut errors);
        }
        for inv in &system.invariants {
            validate_set_comprehension_expr(&inv.body, &mut errors);
        }
        for d in &system.derived_fields {
            validate_set_comprehension_expr(&d.body, &mut errors);
        }
    }
    for f in env.fns.values() {
        validate_set_comprehension_expr(&f.body, &mut errors);
        for c in &f.contracts {
            match c {
                EContract::Requires(e) | EContract::Ensures(e) | EContract::Invariant(e) => {
                    validate_set_comprehension_expr(e, &mut errors);
                }
                EContract::Decreases { measures, .. } => {
                    for m in measures {
                        validate_set_comprehension_expr(m, &mut errors);
                    }
                }
            }
        }
    }

    env.errors.extend(errors);
}

fn validate_set_comprehension_expr(expr: &EExpr, errors: &mut Vec<ElabError>) {
    match expr {
        EExpr::SetComp(_, projection, binder, domain, source, filter, span) => {
            if source.is_none() && is_real_domain(domain) {
                let mut err = ElabError::new(
                    ErrorKind::InvalidScope,
                    "set comprehension over real requires an explicit finite source",
                    "set comprehension domain",
                )
                .with_help(
                    "Use a finite source such as `{ x | x in Set(0.0, 0.5, 1.0) where ... }`; real intervals are not enumerable.",
                );
                err.span = *span;
                errors.push(err);
            }
            if let Some(shape_error) = validate_set_comp_binder_shape(binder, domain) {
                let mut err = ElabError::new(
                    ErrorKind::TypeMismatch,
                    shape_error.message(),
                    "set comprehension binder",
                );
                err.span = *span;
                errors.push(err);
            }
            if let Some(projection) = projection {
                validate_set_comprehension_expr(projection, errors);
            }
            if let Some(source) = source {
                validate_set_comprehension_expr(source, errors);
            }
            validate_set_comprehension_expr(filter, errors);
        }
        EExpr::Call(_, f, args, _) => {
            validate_set_comprehension_expr(f, errors);
            for a in args {
                validate_set_comprehension_expr(a, errors);
            }
        }
        EExpr::CallR(_, f, args, refs, _) => {
            validate_set_comprehension_expr(f, errors);
            for a in args {
                validate_set_comprehension_expr(a, errors);
            }
            for r in refs {
                validate_set_comprehension_expr(r, errors);
            }
        }
        EExpr::Quant(_, _, _, _, body, _) | EExpr::Lam(_, _, body, _) => {
            validate_set_comprehension_expr(body, errors);
        }
        EExpr::Let(bindings, body, _) => {
            for (_, _, value) in bindings {
                validate_set_comprehension_expr(value, errors);
            }
            validate_set_comprehension_expr(body, errors);
        }
        EExpr::BinOp(_, _, l, r, _)
        | EExpr::Until(_, l, r, _)
        | EExpr::Since(_, l, r, _)
        | EExpr::Seq(_, l, r, _)
        | EExpr::SameStep(_, l, r, _)
        | EExpr::Assign(_, l, r, _)
        | EExpr::In(_, l, r, _)
        | EExpr::Pipe(_, l, r, _)
        | EExpr::Index(_, l, r, _) => {
            validate_set_comprehension_expr(l, errors);
            validate_set_comprehension_expr(r, errors);
        }
        EExpr::UnOp(_, _, e, _)
        | EExpr::Always(_, e, _)
        | EExpr::Eventually(_, e, _)
        | EExpr::Historically(_, e, _)
        | EExpr::Once(_, e, _)
        | EExpr::Previously(_, e, _)
        | EExpr::Prime(_, e, _)
        | EExpr::Card(_, e, _)
        | EExpr::Assert(_, e, _)
        | EExpr::Assume(_, e, _)
        | EExpr::Field(_, e, _, _)
        | EExpr::NamedPair(_, _, e, _) => validate_set_comprehension_expr(e, errors),
        EExpr::IfElse(cond, then_e, else_e, _) => {
            validate_set_comprehension_expr(cond, errors);
            validate_set_comprehension_expr(then_e, errors);
            if let Some(e) = else_e {
                validate_set_comprehension_expr(e, errors);
            }
        }
        EExpr::Match(scrutinee, arms, _) => {
            validate_set_comprehension_expr(scrutinee, errors);
            for (_, guard, body) in arms {
                if let Some(g) = guard {
                    validate_set_comprehension_expr(g, errors);
                }
                validate_set_comprehension_expr(body, errors);
            }
        }
        EExpr::CtorRecord(_, _, _, fields, _) | EExpr::StructCtor(_, _, fields, _) => {
            for (_, e) in fields {
                validate_set_comprehension_expr(e, errors);
            }
        }
        EExpr::Block(exprs, _) => {
            for e in exprs {
                validate_set_comprehension_expr(e, errors);
            }
        }
        EExpr::Aggregate(_, _, _, _, body, filter, _) => {
            validate_set_comprehension_expr(body, errors);
            if let Some(f) = filter {
                validate_set_comprehension_expr(f, errors);
            }
        }
        EExpr::While(cond, _, body, _) => {
            validate_set_comprehension_expr(cond, errors);
            validate_set_comprehension_expr(body, errors);
        }
        EExpr::VarDecl(_, _, init, rest, _) => {
            validate_set_comprehension_expr(init, errors);
            validate_set_comprehension_expr(rest, errors);
        }
        EExpr::RelComp(_, projection, bindings, filter, _) => {
            validate_set_comprehension_expr(projection, errors);
            for binding in bindings {
                if let Some(source) = &binding.source {
                    validate_set_comprehension_expr(source, errors);
                }
            }
            validate_set_comprehension_expr(filter, errors);
        }
        EExpr::MapUpdate(_, map, key, val, _) => {
            validate_set_comprehension_expr(map, errors);
            validate_set_comprehension_expr(key, errors);
            validate_set_comprehension_expr(val, errors);
        }
        EExpr::Choose(_, _, _, predicate, _) => {
            if let Some(predicate) = predicate {
                validate_set_comprehension_expr(predicate, errors);
            }
        }
        EExpr::Saw(_, _, _, args, _) => {
            for e in args.iter().flatten() {
                validate_set_comprehension_expr(e, errors);
            }
        }
        EExpr::QualCall(_, _, _, args, _) => {
            for a in args {
                validate_set_comprehension_expr(a, errors);
            }
        }
        EExpr::TupleLit(_, elems, _) | EExpr::SetLit(_, elems, _) | EExpr::SeqLit(_, elems, _) => {
            for e in elems {
                validate_set_comprehension_expr(e, errors);
            }
        }
        EExpr::MapLit(_, pairs, _) => {
            for (k, v) in pairs {
                validate_set_comprehension_expr(k, errors);
                validate_set_comprehension_expr(v, errors);
            }
        }
        EExpr::Lit(..)
        | EExpr::Var(..)
        | EExpr::Qual(..)
        | EExpr::Sorry(_)
        | EExpr::Todo(_)
        | EExpr::Unresolved(..) => {}
    }
}

fn validate_set_comprehension_event_action(item: &EEventAction, errors: &mut Vec<ElabError>) {
    match item {
        EEventAction::Choose(_, _, guard, body) => {
            validate_set_comprehension_expr(guard, errors);
            for b in body {
                validate_set_comprehension_event_action(b, errors);
            }
        }
        EEventAction::ForAll(_, _, body) => {
            for b in body {
                validate_set_comprehension_event_action(b, errors);
            }
        }
        EEventAction::Create(_, _, fields) => {
            for (_, e) in fields {
                validate_set_comprehension_expr(e, errors);
            }
        }
        EEventAction::CrossCall(_, _, args) | EEventAction::LetCrossCall(_, _, _, args) => {
            for a in args {
                validate_set_comprehension_expr(a, errors);
            }
        }
        EEventAction::Match(scrutinee, arms) => {
            if let super::super::types::EMatchScrutinee::CrossCall(_, _, args) = scrutinee {
                for a in args {
                    validate_set_comprehension_expr(a, errors);
                }
            }
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    validate_set_comprehension_expr(guard, errors);
                }
                for item in &arm.body {
                    validate_set_comprehension_event_action(item, errors);
                }
            }
        }
        EEventAction::Apply(target, _, refs, args) => {
            validate_set_comprehension_expr(target, errors);
            for r in refs {
                validate_set_comprehension_expr(r, errors);
            }
            for a in args {
                validate_set_comprehension_expr(a, errors);
            }
        }
        EEventAction::Expr(e) => validate_set_comprehension_expr(e, errors),
    }
}

fn validate_set_comprehension_field_default(default: &EFieldDefault, errors: &mut Vec<ElabError>) {
    match default {
        EFieldDefault::Value(expr) | EFieldDefault::Where(expr) => {
            validate_set_comprehension_expr(expr, errors);
        }
        EFieldDefault::In(values) => {
            for value in values {
                validate_set_comprehension_expr(value, errors);
            }
        }
    }
}

fn is_real_domain(ty: &Ty) -> bool {
    match ty {
        Ty::Builtin(BuiltinTy::Real) => true,
        Ty::Alias(_, inner) | Ty::Refinement(inner, _) => is_real_domain(inner),
        _ => false,
    }
}

/// catch any Ty::Param that survived resolution — wrong-arity
/// generics or non-generic types used with type args in expression-level
/// positions (let bindings, lambda params, etc.) that the pre-pass missed.
pub(super) fn validate_remaining_type_params(env: &mut Env) {
    let generic_types = env.generic_types.clone();
    let known_types = env.types.clone();
    let mut reported: HashSet<String> = HashSet::new();

    let mut bad_params: Vec<(String, Vec<Ty>)> = Vec::new();

    // ── Entities ────────────────────────────────────────────────────
    for entity in env.entities.values() {
        for action in &entity.actions {
            for (_, t) in &action.refs {
                super::collect_all_param_uses(t, &mut bad_params);
            }
            for (_, t) in &action.params {
                super::collect_all_param_uses(t, &mut bad_params);
            }
            for e in &action.requires {
                collect_ty_params_in_expr(e, &mut bad_params);
            }
            for e in &action.ensures {
                collect_ty_params_in_expr(e, &mut bad_params);
            }
            for e in &action.body {
                collect_ty_params_in_expr(e, &mut bad_params);
            }
        }
    }

    // ── Systems ─────────────────────────────────────────────────────
    for system in env.systems.values() {
        for step in &system.actions {
            for req in &step.requires {
                collect_ty_params_in_expr(req, &mut bad_params);
            }
            for item in &step.body {
                collect_ty_params_in_event_action(item, &mut bad_params);
            }
            if let Some(ret) = &step.return_expr {
                collect_ty_params_in_expr(ret, &mut bad_params);
            }
        }
        for query in &system.queries {
            collect_ty_params_in_expr(&query.body, &mut bad_params);
        }
        for derived in &system.derived_fields {
            collect_ty_params_in_expr(&derived.body, &mut bad_params);
        }
        for inv in &system.invariants {
            collect_ty_params_in_expr(&inv.body, &mut bad_params);
        }
        for pred in &system.preds {
            collect_ty_params_in_expr(&pred.body, &mut bad_params);
        }
    }

    // ── Verify / theorem / lemma / axiom ────────────────────────────
    for v in &env.verifies {
        for a in &v.asserts {
            collect_ty_params_in_expr(a, &mut bad_params);
        }
    }
    for t in &env.theorems {
        for inv in &t.invariants {
            collect_ty_params_in_expr(inv, &mut bad_params);
        }
        for s in &t.shows {
            collect_ty_params_in_expr(s, &mut bad_params);
        }
    }
    for l in &env.lemmas {
        for b in &l.body {
            collect_ty_params_in_expr(b, &mut bad_params);
        }
    }
    for a in &env.axioms {
        collect_ty_params_in_expr(&a.body, &mut bad_params);
    }

    // ── Scenes ──────────────────────────────────────────────────────
    for scene in &env.scenes {
        for e in &scene.thens {
            collect_ty_params_in_expr(e, &mut bad_params);
        }
        for e in &scene.given_constraints {
            collect_ty_params_in_expr(e, &mut bad_params);
        }
    }

    // ── Props ───────────────────────────────────────────────────────
    for prop in env.props.values() {
        collect_ty_params_in_expr(&prop.body, &mut bad_params);
    }

    // ── Fns / preds / consts ────────────────────────────────────────
    for f in env.fns.values() {
        collect_ty_params_in_expr(&f.body, &mut bad_params);
    }
    for pred in env.preds.values() {
        collect_ty_params_in_expr(&pred.body, &mut bad_params);
    }
    for c in env.consts.values() {
        collect_ty_params_in_expr(&c.body, &mut bad_params);
    }

    // Report
    for (name, args) in &bad_params {
        if matches!(name.as_str(), "Set" | "Seq" | "Map" | "Store") {
            continue;
        }
        let report_key = format!("{}<{}>", name, args.len());
        if reported.contains(&report_key) {
            continue;
        }
        if let Some(gdef) = generic_types.get(name.as_str()) {
            if args.len() != gdef.type_params.len() {
                env.errors.push(ElabError::new(
                    ErrorKind::TypeMismatch,
                    crate::messages::generic_arity_mismatch(
                        name,
                        gdef.type_params.len(),
                        args.len(),
                    ),
                    format!(
                        "`{name}` declared with {} type parameter(s)",
                        gdef.type_params.len()
                    ),
                ));
                reported.insert(report_key);
            }
        } else if known_types.contains_key(name.as_str()) {
            env.errors.push(ElabError::new(
                ErrorKind::TypeMismatch,
                crate::messages::not_a_generic_type(name),
                format!("`{name}` is a concrete type"),
            ));
            reported.insert(report_key);
        }
    }
}

/// Collect Ty::Param occurrences from types embedded in an expression tree.
/// Walks the type tag of each expression node and recurses into sub-expressions.
pub(super) fn collect_ty_params_in_expr(expr: &EExpr, out: &mut Vec<(String, Vec<Ty>)>) {
    super::collect_all_param_uses(&expr.ty(), out);
    // Recurse into sub-expressions; focus on nodes that carry extra type info
    match expr {
        EExpr::Call(_, f, args, _) => {
            collect_ty_params_in_expr(f, out);
            for a in args {
                collect_ty_params_in_expr(a, out);
            }
        }
        EExpr::Quant(_, _, _, vty, body, _) => {
            super::collect_all_param_uses(vty, out);
            collect_ty_params_in_expr(body, out);
        }
        EExpr::Let(bindings, body, _) => {
            for (_, opt_ty, val) in bindings {
                if let Some(t) = opt_ty {
                    super::collect_all_param_uses(t, out);
                }
                collect_ty_params_in_expr(val, out);
            }
            collect_ty_params_in_expr(body, out);
        }
        EExpr::Lam(params, ret_ty, body, _) => {
            for (_, t) in params {
                super::collect_all_param_uses(t, out);
            }
            if let Some(rt) = ret_ty {
                super::collect_all_param_uses(rt, out);
            }
            collect_ty_params_in_expr(body, out);
        }
        EExpr::VarDecl(_, opt_ty, init, rest, _) => {
            if let Some(t) = opt_ty {
                super::collect_all_param_uses(t, out);
            }
            collect_ty_params_in_expr(init, out);
            collect_ty_params_in_expr(rest, out);
        }
        EExpr::BinOp(_, _, l, r, _)
        | EExpr::Until(_, l, r, _)
        | EExpr::Since(_, l, r, _)
        | EExpr::Seq(_, l, r, _)
        | EExpr::SameStep(_, l, r, _)
        | EExpr::Assign(_, l, r, _)
        | EExpr::In(_, l, r, _)
        | EExpr::Pipe(_, l, r, _)
        | EExpr::Index(_, l, r, _) => {
            collect_ty_params_in_expr(l, out);
            collect_ty_params_in_expr(r, out);
        }
        EExpr::UnOp(_, _, e, _)
        | EExpr::Always(_, e, _)
        | EExpr::Eventually(_, e, _)
        | EExpr::Historically(_, e, _)
        | EExpr::Once(_, e, _)
        | EExpr::Previously(_, e, _)
        | EExpr::Prime(_, e, _)
        | EExpr::Card(_, e, _)
        | EExpr::Assert(_, e, _)
        | EExpr::Assume(_, e, _)
        | EExpr::Field(_, e, _, _) => {
            collect_ty_params_in_expr(e, out);
        }
        EExpr::IfElse(cond, then_e, else_e, _) => {
            collect_ty_params_in_expr(cond, out);
            collect_ty_params_in_expr(then_e, out);
            if let Some(e) = else_e {
                collect_ty_params_in_expr(e, out);
            }
        }
        EExpr::Match(scrutinee, arms, _) => {
            collect_ty_params_in_expr(scrutinee, out);
            for (_, guard, body) in arms {
                if let Some(g) = guard {
                    collect_ty_params_in_expr(g, out);
                }
                collect_ty_params_in_expr(body, out);
            }
        }
        EExpr::CtorRecord(_, _, _, fields, _) | EExpr::StructCtor(_, _, fields, _) => {
            for (_, e) in fields {
                collect_ty_params_in_expr(e, out);
            }
        }
        EExpr::Block(stmts, _) => {
            for s in stmts {
                collect_ty_params_in_expr(s, out);
            }
        }
        EExpr::Aggregate(_, _, _, _, body, filter, _) => {
            collect_ty_params_in_expr(body, out);
            if let Some(f) = filter {
                collect_ty_params_in_expr(f, out);
            }
        }
        EExpr::While(cond, contracts, body, _) => {
            collect_ty_params_in_expr(cond, out);
            for contract in contracts {
                match contract {
                    EContract::Requires(expr)
                    | EContract::Ensures(expr)
                    | EContract::Invariant(expr) => collect_ty_params_in_expr(expr, out),
                    EContract::Decreases { measures, .. } => {
                        for measure in measures {
                            collect_ty_params_in_expr(measure, out);
                        }
                    }
                }
            }
            collect_ty_params_in_expr(body, out);
        }
        EExpr::Choose(_, _, domain_ty, predicate, _) => {
            super::collect_all_param_uses(domain_ty, out);
            if let Some(predicate) = predicate {
                collect_ty_params_in_expr(predicate, out);
            }
        }
        EExpr::SetComp(_, expr, _, _, source, body, _) => {
            if let Some(e) = expr {
                collect_ty_params_in_expr(e, out);
            }
            if let Some(source) = source {
                collect_ty_params_in_expr(source, out);
            }
            collect_ty_params_in_expr(body, out);
        }
        EExpr::RelComp(_, projection, bindings, filter, _) => {
            collect_ty_params_in_expr(projection, out);
            for binding in bindings {
                if let Some(source) = &binding.source {
                    collect_ty_params_in_expr(source, out);
                }
            }
            collect_ty_params_in_expr(filter, out);
        }
        EExpr::MapUpdate(_, map, key, val, _) => {
            collect_ty_params_in_expr(map, out);
            collect_ty_params_in_expr(key, out);
            collect_ty_params_in_expr(val, out);
        }
        EExpr::CallR(_, f, refs, args, _) => {
            collect_ty_params_in_expr(f, out);
            for r in refs {
                collect_ty_params_in_expr(r, out);
            }
            for a in args {
                collect_ty_params_in_expr(a, out);
            }
        }
        EExpr::QualCall(_, _, _, args, _) => {
            for a in args {
                collect_ty_params_in_expr(a, out);
            }
        }
        EExpr::TupleLit(_, elems, _) | EExpr::SetLit(_, elems, _) | EExpr::SeqLit(_, elems, _) => {
            for e in elems {
                collect_ty_params_in_expr(e, out);
            }
        }
        EExpr::MapLit(_, pairs, _) => {
            for (k, v) in pairs {
                collect_ty_params_in_expr(k, out);
                collect_ty_params_in_expr(v, out);
            }
        }
        EExpr::NamedPair(_, _, e, _) => collect_ty_params_in_expr(e, out),
        EExpr::Saw(_, _, _, args, _) => {
            for e in args.iter().flatten() {
                collect_ty_params_in_expr(e, out);
            }
        }
        EExpr::Lit(_, _, _)
        | EExpr::Var(_, _, _)
        | EExpr::Qual(_, _, _, _)
        | EExpr::Unresolved(_, _)
        | EExpr::Sorry(_)
        | EExpr::Todo(_) => {}
    }
}

/// Collect Ty::Param from an event action (assignment, etc.)
pub(super) fn collect_ty_params_in_event_action(
    item: &EEventAction,
    out: &mut Vec<(String, Vec<Ty>)>,
) {
    match item {
        EEventAction::Choose(_, ty, guard, body) => {
            super::collect_all_param_uses(ty, out);
            collect_ty_params_in_expr(guard, out);
            for b in body {
                collect_ty_params_in_event_action(b, out);
            }
        }
        EEventAction::ForAll(_, ty, body) => {
            super::collect_all_param_uses(ty, out);
            for b in body {
                collect_ty_params_in_event_action(b, out);
            }
        }
        EEventAction::Create(_, _store, fields) => {
            for (_, e) in fields {
                collect_ty_params_in_expr(e, out);
            }
        }
        EEventAction::CrossCall(_, _, args) => {
            for a in args {
                collect_ty_params_in_expr(a, out);
            }
        }
        EEventAction::LetCrossCall(_, _, _, args) => {
            for a in args {
                collect_ty_params_in_expr(a, out);
            }
        }
        EEventAction::Match(scrutinee, arms) => {
            if let super::super::types::EMatchScrutinee::CrossCall(_, _, args) = scrutinee {
                for a in args {
                    collect_ty_params_in_expr(a, out);
                }
            }
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_ty_params_in_expr(guard, out);
                }
                for item in &arm.body {
                    collect_ty_params_in_event_action(item, out);
                }
            }
        }
        EEventAction::Apply(target, _, refs, args) => {
            collect_ty_params_in_expr(target, out);
            for r in refs {
                collect_ty_params_in_expr(r, out);
            }
            for a in args {
                collect_ty_params_in_expr(a, out);
            }
        }
        EEventAction::Expr(e) => collect_ty_params_in_expr(e, out),
    }
}

// ── Named/error type validation ─────────────────────────────────────

/// Validate that no unresolved named type references survive resolution.
///
/// Any `Ty::Named(name)` still present at this point is a genuine
/// reference to a type that does not exist in the environment.
/// Emit one diagnostic per missing name, then rewrite those occurrences
/// to `Ty::Error` so downstream passes propagate poison silently.
pub(super) fn validate_unresolved_types(env: &mut Env) {
    let mut reported: HashSet<String> = HashSet::new();
    let mut unresolved: Vec<String> = Vec::new();

    for ty in env.types.values() {
        collect_named_in_ty(ty, &mut unresolved);
    }

    for entity in env.entities.values() {
        for field in &entity.fields {
            collect_named_in_ty(&field.ty, &mut unresolved);
        }
        for action in &entity.actions {
            for (_, t) in &action.refs {
                collect_named_in_ty(t, &mut unresolved);
            }
            for (_, t) in &action.params {
                collect_named_in_ty(t, &mut unresolved);
            }
        }
    }

    for system in env.systems.values() {
        for field in &system.fields {
            collect_named_in_ty(&field.ty, &mut unresolved);
        }
        for step in &system.actions {
            for (_, t) in &step.params {
                collect_named_in_ty(t, &mut unresolved);
            }
        }
        for query in &system.queries {
            for (_, t) in &query.params {
                collect_named_in_ty(t, &mut unresolved);
            }
        }
        for pred in &system.preds {
            for (_, t) in &pred.params {
                collect_named_in_ty(t, &mut unresolved);
            }
        }
    }

    for func in env.fns.values() {
        for (_, t) in &func.params {
            collect_named_in_ty(t, &mut unresolved);
        }
        collect_named_in_ty(&func.ret_ty, &mut unresolved);
    }

    for pred in env.preds.values() {
        for (_, t) in &pred.params {
            collect_named_in_ty(t, &mut unresolved);
        }
    }

    // Only report names that are NOT known to the environment. After
    // resolve, some Ty::Unresolved may survive legitimately if a
    // declaration refers to a type from a different module scope that
    // the walker couldn't resolve inline but that the env DOES know.
    for name in &unresolved {
        if reported.contains(name) {
            continue;
        }
        // Check against all known type sources
        if env.types.contains_key(name) {
            continue;
        }
        if env.entities.contains_key(name) {
            continue;
        }
        if env.aliases.contains_key(name) {
            continue;
        }
        if env.generic_types.contains_key(name) {
            continue;
        }
        reported.insert(name.clone());
        let mut err = ElabError::new(
            ErrorKind::UndefinedRef,
            format!("unknown type `{name}`"),
            format!("`{name}` is not a known type, entity, or type alias"),
        );
        if let Some(suggested) = case_mismatch_type_candidate(env, name) {
            err.help = Some(format!("did you mean `{suggested}`?"));
        }
        env.errors.push(err);
    }

    rewrite_named_types_to_error(env);
}

fn case_mismatch_type_candidate(env: &Env, name: &str) -> Option<String> {
    let mut candidates: HashSet<String> = HashSet::new();

    for builtin in [
        "int", "bool", "string", "identity", "real", "float", "Set", "Seq", "Map", "Store",
    ] {
        candidates.insert(builtin.to_owned());
    }

    candidates.extend(env.types.keys().cloned());
    candidates.extend(env.entities.keys().cloned());
    candidates.extend(env.aliases.keys().cloned());
    candidates.extend(env.generic_types.keys().cloned());

    let mut matches: Vec<String> = candidates
        .into_iter()
        .filter(|candidate| candidate != name && candidate.eq_ignore_ascii_case(name))
        .collect();
    matches.sort();
    matches.dedup();

    if matches.len() == 1 {
        matches.into_iter().next()
    } else {
        None
    }
}

/// Collect user-visible named type references from a `Ty`.
fn collect_named_in_ty(ty: &Ty, out: &mut Vec<String>) {
    match ty {
        Ty::Named(n) => {
            out.push(n.clone());
        }
        Ty::Param(name, args) => {
            out.push(name.clone());
            for a in args {
                collect_named_in_ty(a, out);
            }
        }
        Ty::Record(_, fields) => {
            for (_, ft) in fields {
                collect_named_in_ty(ft, out);
            }
        }
        Ty::Alias(_, inner) | Ty::Newtype(_, inner) | Ty::Set(inner) | Ty::Seq(inner) => {
            collect_named_in_ty(inner, out);
        }
        Ty::Map(k, v) | Ty::Fn(k, v) => {
            collect_named_in_ty(k, out);
            collect_named_in_ty(v, out);
        }
        Ty::Tuple(ts) => {
            for t in ts {
                collect_named_in_ty(t, out);
            }
        }
        Ty::Relation(columns) => {
            for column in columns {
                collect_named_in_ty(column, out);
            }
        }
        Ty::Refinement(base, _) => {
            collect_named_in_ty(base, out);
        }
        Ty::Enum(_, _) | Ty::Builtin(_) | Ty::Entity(_) | Ty::Error | Ty::Store(_) => {}
    }
}

fn rewrite_named_ty(ty: &mut Ty) {
    match ty {
        Ty::Named(_) => *ty = Ty::Error,
        Ty::Param(_, args) | Ty::Tuple(args) => {
            for arg in args {
                rewrite_named_ty(arg);
            }
        }
        Ty::Record(_, fields) => {
            for (_, field_ty) in fields {
                rewrite_named_ty(field_ty);
            }
        }
        Ty::Alias(_, inner)
        | Ty::Newtype(_, inner)
        | Ty::Set(inner)
        | Ty::Seq(inner)
        | Ty::Refinement(inner, _) => rewrite_named_ty(inner),
        Ty::Map(key, value) | Ty::Fn(key, value) => {
            rewrite_named_ty(key);
            rewrite_named_ty(value);
        }
        Ty::Relation(columns) => {
            for column in columns {
                rewrite_named_ty(column);
            }
        }
        Ty::Enum(_, _) | Ty::Builtin(_) | Ty::Entity(_) | Ty::Error | Ty::Store(_) => {}
    }
}

fn rewrite_named_types_to_error(env: &mut Env) {
    for ty in env.types.values_mut() {
        rewrite_named_ty(ty);
    }

    for entity in env.entities.values_mut() {
        for field in &mut entity.fields {
            rewrite_named_ty(&mut field.ty);
        }
        for action in &mut entity.actions {
            for (_, ty) in &mut action.refs {
                rewrite_named_ty(ty);
            }
            for (_, ty) in &mut action.params {
                rewrite_named_ty(ty);
            }
        }
    }

    for system in env.systems.values_mut() {
        for field in &mut system.fields {
            rewrite_named_ty(&mut field.ty);
        }
        for step in &mut system.actions {
            for (_, ty) in &mut step.params {
                rewrite_named_ty(ty);
            }
        }
        for query in &mut system.queries {
            for (_, ty) in &mut query.params {
                rewrite_named_ty(ty);
            }
        }
        for pred in &mut system.preds {
            for (_, ty) in &mut pred.params {
                rewrite_named_ty(ty);
            }
        }
    }

    for func in env.fns.values_mut() {
        for (_, ty) in &mut func.params {
            rewrite_named_ty(ty);
        }
        rewrite_named_ty(&mut func.ret_ty);
    }

    for pred in env.preds.values_mut() {
        for (_, ty) in &mut pred.params {
            rewrite_named_ty(ty);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Visibility;
    use crate::elab::types::{
        BinOp, ECommand, EConst, EExtern, EScene, ESetCompBinder, ESystem, ESystemAction,
        GenericTypeDef, Literal,
    };
    use crate::span::Span;

    fn int_ty() -> Ty {
        Ty::Builtin(BuiltinTy::Int)
    }

    fn bool_ty() -> Ty {
        Ty::Builtin(BuiltinTy::Bool)
    }

    fn param(name: &str) -> Ty {
        Ty::Param(name.to_owned(), vec![int_ty()])
    }

    fn var_with_ty(name: &str, ty: Ty) -> EExpr {
        EExpr::Var(ty, name.to_owned(), None)
    }

    fn lit_bool(value: bool) -> EExpr {
        EExpr::Lit(bool_ty(), Literal::Bool(value), None)
    }

    fn sum_bool_body() -> EExpr {
        EExpr::Aggregate(
            int_ty(),
            crate::ast::AggKind::Sum,
            "c".to_owned(),
            bool_ty(),
            Box::new(lit_bool(true)),
            None,
            None,
        )
    }

    fn count_body(body: EExpr) -> EExpr {
        EExpr::Aggregate(
            int_ty(),
            crate::ast::AggKind::Count,
            "c".to_owned(),
            int_ty(),
            Box::new(body),
            None,
            None,
        )
    }

    fn real_set_comp(source: Option<EExpr>) -> EExpr {
        EExpr::SetComp(
            Ty::Set(Box::new(Ty::Builtin(BuiltinTy::Real))),
            None,
            ESetCompBinder::Var("x".to_owned()),
            Ty::Builtin(BuiltinTy::Real),
            source.map(Box::new),
            Box::new(lit_bool(true)),
            None,
        )
    }

    fn generic_def(name: &str, type_params: &[&str]) -> GenericTypeDef {
        GenericTypeDef {
            name: name.to_owned(),
            type_params: type_params
                .iter()
                .map(|param| (*param).to_owned())
                .collect(),
            variant_names: vec!["Some".to_owned()],
            variant_fields: vec![(
                "Some".to_owned(),
                vec![("value".to_owned(), Ty::Named("T".to_owned()))],
            )],
            visibility: Visibility::Private,
            span: Span { start: 0, end: 0 },
        }
    }

    fn empty_system_with_action(body: Vec<EEventAction>) -> ESystem {
        ESystem {
            name: "App".to_owned(),
            implements: None,
            deps: vec![],
            fields: vec![],
            store_params: vec![],
            scopes: vec![],
            commands: vec![],
            actions: vec![ESystemAction {
                name: "step".to_owned(),
                params: vec![],
                requires: vec![],
                body,
                return_expr: None,
                span: None,
            }],
            queries: vec![],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
            proc_uses: vec![],
            span: None,
        }
    }

    fn collected_param_names(expr: &EExpr) -> Vec<String> {
        let mut out = Vec::new();
        collect_ty_params_in_expr(expr, &mut out);
        out.into_iter().map(|(name, _)| name).collect()
    }

    fn record_var_names<'a>(names: &'a mut Vec<String>) -> impl FnMut(&EExpr) + 'a {
        |expr| {
            if let EExpr::Var(_, name, _) = expr {
                names.push(name.clone());
            }
        }
    }

    #[test]
    fn collect_ty_params_in_expr_walks_choose_and_while_contracts() {
        let expr = EExpr::While(
            Box::new(lit_bool(true)),
            vec![
                EContract::Requires(var_with_ty("req", param("ReqBox"))),
                EContract::Ensures(var_with_ty("ens", param("EnsBox"))),
                EContract::Invariant(var_with_ty("inv", param("InvBox"))),
                EContract::Decreases {
                    measures: vec![var_with_ty("dec", param("DecBox"))],
                    star: false,
                },
            ],
            Box::new(EExpr::Choose(
                param("ChooseResult"),
                "x".to_owned(),
                param("DomainBox"),
                Some(Box::new(EExpr::BinOp(
                    bool_ty(),
                    BinOp::Eq,
                    Box::new(var_with_ty("lhs", param("PredicateBox"))),
                    Box::new(var_with_ty("rhs", param("PredicateBox"))),
                    None,
                ))),
                None,
            )),
            None,
        );

        let names = collected_param_names(&expr);
        for expected in [
            "ReqBox",
            "EnsBox",
            "InvBox",
            "DecBox",
            "ChooseResult",
            "DomainBox",
            "PredicateBox",
        ] {
            assert!(
                names.iter().any(|name| name == expected),
                "expected to collect {expected}, got {names:?}"
            );
        }
    }

    #[test]
    fn validate_expression_walkers_cover_contract_defaults_actions_and_scenes() {
        let mut contract_names = Vec::new();
        {
            let mut visit = record_var_names(&mut contract_names);
            walk_contract(
                &EContract::Decreases {
                    measures: vec![var_with_ty("measure", int_ty())],
                    star: false,
                },
                &mut visit,
            );
        }
        assert_eq!(contract_names, vec!["measure"]);

        let mut default_names = Vec::new();
        {
            let mut visit = record_var_names(&mut default_names);
            walk_field_default(
                &EFieldDefault::In(vec![
                    var_with_ty("default_a", int_ty()),
                    var_with_ty("default_b", int_ty()),
                ]),
                &mut visit,
            );
        }
        assert_eq!(default_names, vec!["default_a", "default_b"]);

        let mut action_names = Vec::new();
        {
            let mut visit = record_var_names(&mut action_names);
            walk_event_action(
                &EEventAction::Choose(
                    "item".to_owned(),
                    int_ty(),
                    var_with_ty("guard", bool_ty()),
                    vec![
                        EEventAction::Create(
                            "Order".to_owned(),
                            None,
                            vec![("id".to_owned(), var_with_ty("created_id", int_ty()))],
                        ),
                        EEventAction::CrossCall(
                            "Gateway".to_owned(),
                            "authorize".to_owned(),
                            vec![var_with_ty("cross_arg", int_ty())],
                        ),
                        EEventAction::Apply(
                            var_with_ty("target", int_ty()),
                            "step".to_owned(),
                            vec![var_with_ty("ref_arg", int_ty())],
                            vec![var_with_ty("apply_arg", int_ty())],
                        ),
                    ],
                ),
                &mut visit,
            );
        }
        for expected in [
            "guard",
            "created_id",
            "cross_arg",
            "target",
            "ref_arg",
            "apply_arg",
        ] {
            assert!(
                action_names.iter().any(|name| name == expected),
                "expected event action walker to visit {expected}, got {action_names:?}"
            );
        }

        let mut scene_action_names = Vec::new();
        {
            let mut visit = record_var_names(&mut scene_action_names);
            walk_scene_when(
                &ESceneWhen::Action {
                    var: "seen".to_owned(),
                    system: "Gateway".to_owned(),
                    event: "authorize".to_owned(),
                    args: vec![var_with_ty("scene_arg", int_ty())],
                    card: None,
                },
                &mut visit,
            );
        }
        assert_eq!(scene_action_names, vec!["scene_arg"]);

        let mut scene_assume_names = Vec::new();
        {
            let mut visit = record_var_names(&mut scene_assume_names);
            walk_scene_when(
                &ESceneWhen::Assume(var_with_ty("scene_assume", bool_ty())),
                &mut visit,
            );
        }
        assert_eq!(scene_assume_names, vec!["scene_assume"]);
    }

    #[test]
    fn validate_saw_expressions_reports_qualification_and_arity_errors() {
        let mut env = Env::new();
        env.externs.insert(
            "Gateway".to_owned(),
            EExtern {
                name: "Gateway".to_owned(),
                implements: None,
                commands: vec![ECommand {
                    name: "authorize".to_owned(),
                    params: vec![("amount".to_owned(), int_ty())],
                    return_type: None,
                    span: None,
                }],
                mays: vec![],
                assumes: vec![],
                span: None,
            },
        );
        env.externs.insert(
            "Commerce::Gateway".to_owned(),
            EExtern {
                name: "Commerce::Gateway".to_owned(),
                implements: None,
                commands: vec![ECommand {
                    name: "authorize".to_owned(),
                    params: vec![],
                    return_type: None,
                    span: None,
                }],
                mays: vec![],
                assumes: vec![],
                span: None,
            },
        );
        env.scenes.push(EScene {
            name: "saw_checks".to_owned(),
            stores: vec![],
            let_bindings: vec![],
            givens: vec![],
            whens: vec![
                ESceneWhen::Assume(EExpr::Saw(
                    bool_ty(),
                    String::new(),
                    "authorize".to_owned(),
                    vec![],
                    None,
                )),
                ESceneWhen::Assume(EExpr::Saw(
                    bool_ty(),
                    "Commerce::Gateway".to_owned(),
                    "authorize".to_owned(),
                    vec![],
                    None,
                )),
                ESceneWhen::Assume(EExpr::Saw(
                    bool_ty(),
                    "Gateway".to_owned(),
                    "authorize".to_owned(),
                    vec![],
                    None,
                )),
                ESceneWhen::Assume(EExpr::Saw(
                    bool_ty(),
                    "Gateway".to_owned(),
                    "missing".to_owned(),
                    vec![Some(Box::new(var_with_ty("amount", int_ty())))],
                    None,
                )),
            ],
            thens: vec![],
            given_constraints: vec![],
            activations: vec![],
            span: None,
            file: None,
        });

        let ctx = super::super::Ctx::from_env(&env);
        validate_saw_expressions(&mut env, &ctx);

        let messages: Vec<&str> = env
            .errors
            .iter()
            .map(|error| error.message.as_str())
            .collect();
        assert!(
            messages
                .iter()
                .filter(|message| message.contains(crate::messages::SAW_EXTERN_QUALIFIED_ONLY))
                .count()
                >= 2,
            "expected unqualified and multi-segment saw diagnostics, got {messages:?}"
        );
        assert!(
            messages
                .iter()
                .any(|message| message.contains("expects 1") && message.contains("got 0")),
            "expected saw arity diagnostic, got {messages:?}"
        );
        assert!(
            messages
                .iter()
                .any(|message| message.contains(crate::messages::SAW_UNKNOWN_EVENT)),
            "expected unknown saw event diagnostic, got {messages:?}"
        );
    }

    #[test]
    fn validate_remaining_type_params_reports_wrong_arity_from_event_actions() {
        let mut env = Env::new();
        env.generic_types
            .insert("Option".to_owned(), generic_def("Option", &["T"]));
        env.systems.insert(
            "App".to_owned(),
            empty_system_with_action(vec![EEventAction::Choose(
                "item".to_owned(),
                Ty::Param("Option".to_owned(), vec![int_ty(), bool_ty()]),
                lit_bool(true),
                vec![EEventAction::Expr(var_with_ty(
                    "x",
                    Ty::Param("Option".to_owned(), vec![int_ty(), bool_ty()]),
                ))],
            )]),
        );

        validate_remaining_type_params(&mut env);

        assert_eq!(
            env.errors
                .iter()
                .filter(|error| error.message.contains("expects 1 type argument(s)")
                    && error.message.contains("2 were provided"))
                .count(),
            1,
            "wrong arity should be reported and deduplicated, got {:?}",
            env.errors
        );
    }

    #[test]
    fn validate_aggregate_bodies_checks_const_initializers() {
        let mut env = Env::new();
        env.consts.insert(
            "bad".to_owned(),
            EConst {
                name: "bad".to_owned(),
                body: sum_bool_body(),
                span: None,
            },
        );

        validate_aggregate_bodies(&mut env);

        assert!(
            env.errors
                .iter()
                .any(|error| error.message.contains("Sum") && error.message.contains("numeric")),
            "expected aggregate body diagnostic from const initializer, got {:?}",
            env.errors
        );
    }

    #[test]
    fn validate_aggregate_bodies_accepts_bool_count_and_rejects_numeric_count_body() {
        let mut valid = Env::new();
        valid.consts.insert(
            "count_bool".to_owned(),
            EConst {
                name: "count_bool".to_owned(),
                body: count_body(lit_bool(true)),
                span: None,
            },
        );
        validate_aggregate_bodies(&mut valid);
        assert!(
            valid.errors.is_empty(),
            "count with bool predicate should be accepted, got {:?}",
            valid.errors
        );

        let mut invalid = Env::new();
        invalid.consts.insert(
            "count_int".to_owned(),
            EConst {
                name: "count_int".to_owned(),
                body: count_body(var_with_ty("n", int_ty())),
                span: None,
            },
        );
        validate_aggregate_bodies(&mut invalid);
        assert!(
            invalid
                .errors
                .iter()
                .any(|error| error.message.contains("count") && error.message.contains("bool")),
            "count with int body should report a bool predicate diagnostic, got {:?}",
            invalid.errors
        );
    }

    #[test]
    fn validate_set_comprehension_sources_rejects_real_domains_across_contexts() {
        let mut env = Env::new();
        env.consts.insert(
            "bad_comp".to_owned(),
            EConst {
                name: "bad_comp".to_owned(),
                body: real_set_comp(None),
                span: None,
            },
        );
        validate_set_comprehension_sources(&mut env);
        assert!(
            env.errors.iter().any(|error| error
                .message
                .contains("set comprehension over real requires an explicit finite source")),
            "top-level set comprehension source validator should reject implicit real domains, got {:?}",
            env.errors
        );

        let mut valid_errors = Vec::new();
        validate_set_comprehension_expr(
            &real_set_comp(Some(EExpr::SetLit(
                Ty::Set(Box::new(Ty::Builtin(BuiltinTy::Real))),
                vec![],
                None,
            ))),
            &mut valid_errors,
        );
        assert!(
            valid_errors.is_empty(),
            "real-domain set comprehension with finite source should be accepted, got {valid_errors:?}"
        );

        let mut action_errors = Vec::new();
        validate_set_comprehension_event_action(
            &EEventAction::Expr(real_set_comp(None)),
            &mut action_errors,
        );
        assert!(
            action_errors.iter().any(|error| error
                .message
                .contains("set comprehension over real requires an explicit finite source")),
            "event-action set comprehension validator should reject implicit real domains, got {action_errors:?}"
        );

        let mut default_errors = Vec::new();
        validate_set_comprehension_field_default(
            &EFieldDefault::Value(real_set_comp(None)),
            &mut default_errors,
        );
        assert!(
            default_errors.iter().any(|error| error
                .message
                .contains("set comprehension over real requires an explicit finite source")),
            "field-default set comprehension validator should reject implicit real domains, got {default_errors:?}"
        );
    }

    #[test]
    fn validate_unresolved_types_reports_and_rewrites_surviving_named_types() {
        let mut env = Env::new();
        env.types.insert(
            "Alias".to_owned(),
            Ty::Set(Box::new(Ty::Named("Missing".to_owned()))),
        );

        validate_unresolved_types(&mut env);

        assert!(
            env.errors
                .iter()
                .any(|error| error.message == "unknown type `Missing`"),
            "expected unknown type diagnostic, got {:?}",
            env.errors
        );
        let Some(Ty::Set(inner)) = env.types.get("Alias") else {
            panic!(
                "expected Alias to remain a set, got {:?}",
                env.types.get("Alias")
            );
        };
        assert!(
            matches!(inner.as_ref(), Ty::Error),
            "unresolved named type should be rewritten to poison, got {inner:?}"
        );
    }

    #[test]
    fn unresolved_type_helpers_walk_relation_columns_exhaustively() {
        let mut names = Vec::new();
        collect_named_in_ty(
            &Ty::Relation(vec![
                Ty::Named("MissingLeft".to_owned()),
                Ty::Map(
                    Box::new(int_ty()),
                    Box::new(Ty::Named("MissingRight".to_owned())),
                ),
            ]),
            &mut names,
        );
        assert_eq!(names, vec!["MissingLeft", "MissingRight"]);

        let mut ty = Ty::Relation(vec![
            Ty::Named("MissingLeft".to_owned()),
            Ty::Map(
                Box::new(int_ty()),
                Box::new(Ty::Named("MissingRight".to_owned())),
            ),
        ]);
        rewrite_named_ty(&mut ty);
        let Ty::Relation(columns) = ty else {
            panic!("expected relation");
        };
        assert!(matches!(columns[0], Ty::Error));
        let Ty::Map(_, value) = &columns[1] else {
            panic!("expected map column");
        };
        assert!(matches!(value.as_ref(), Ty::Error));
    }
}
