//! Post-resolution validation passes.

use super::super::env::Env;
use super::super::error::{ElabError, ErrorKind};
use super::super::types::{EEventAction, EExpr, Ty};
use std::collections::{HashMap, HashSet};

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

    // ── Inner walker: mutates Saw nodes and collects errors ──────────
    fn walk(
        expr: &mut EExpr,
        arities: &HashMap<(String, String), usize>,
        extern_names: &HashSet<String>,
        errors: &mut Vec<(String, Option<crate::span::Span>)>,
    ) {
        match expr {
            EExpr::Saw(_, sys, evt, args, sp) => {
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
                                    crate::messages::saw_arity_mismatch(
                                        sys,
                                        evt,
                                        expected,
                                        args.len(),
                                    ),
                                    *sp,
                                ));
                            }
                        } else {
                            errors.push((crate::messages::SAW_UNKNOWN_EVENT.to_owned(), *sp));
                        }
                    }
                }

                // Recurse into arg expressions.
                for a in args.iter_mut().flatten() {
                    walk(a, arities, extern_names, errors);
                }
            }
            // Recurse into all subexpressions.
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
            | EExpr::NamedPair(_, _, e, _) => walk(e, arities, extern_names, errors),
            EExpr::Choose(_, _, _, predicate, _) => {
                if let Some(pred) = predicate {
                    walk(pred, arities, extern_names, errors);
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
                walk(a, arities, extern_names, errors);
                walk(b, arities, extern_names, errors);
            }
            EExpr::Quant(_, _, _, _, body, _) | EExpr::Lam(_, _, body, _) => {
                walk(body, arities, extern_names, errors);
            }
            EExpr::Call(_, f, args, _) => {
                walk(f, arities, extern_names, errors);
                for a in args {
                    walk(a, arities, extern_names, errors);
                }
            }
            EExpr::CallR(_, f, args, refs, _) => {
                walk(f, arities, extern_names, errors);
                for a in args {
                    walk(a, arities, extern_names, errors);
                }
                for r in refs {
                    walk(r, arities, extern_names, errors);
                }
            }
            EExpr::Let(binds, body, _) => {
                for (_, _, e) in binds {
                    walk(e, arities, extern_names, errors);
                }
                walk(body, arities, extern_names, errors);
            }
            EExpr::Match(scrut, arms, _) => {
                walk(scrut, arities, extern_names, errors);
                for (_, guard, body) in arms {
                    if let Some(g) = guard {
                        walk(g, arities, extern_names, errors);
                    }
                    walk(body, arities, extern_names, errors);
                }
            }
            EExpr::MapUpdate(_, m, k, v, _) => {
                walk(m, arities, extern_names, errors);
                walk(k, arities, extern_names, errors);
                walk(v, arities, extern_names, errors);
            }
            EExpr::SetComp(_, proj, _, _, filter, _) => {
                if let Some(p) = proj {
                    walk(p, arities, extern_names, errors);
                }
                walk(filter, arities, extern_names, errors);
            }
            EExpr::TupleLit(_, elems, _)
            | EExpr::SetLit(_, elems, _)
            | EExpr::SeqLit(_, elems, _) => {
                for e in elems {
                    walk(e, arities, extern_names, errors);
                }
            }
            EExpr::MapLit(_, entries, _) => {
                for (k, v) in entries {
                    walk(k, arities, extern_names, errors);
                    walk(v, arities, extern_names, errors);
                }
            }
            EExpr::QualCall(_, _, _, args, _) => {
                for a in args {
                    walk(a, arities, extern_names, errors);
                }
            }
            EExpr::CtorRecord(_, _, _, fields, _) | EExpr::StructCtor(_, _, fields, _) => {
                for (_, e) in fields {
                    walk(e, arities, extern_names, errors);
                }
            }
            EExpr::Aggregate(_, _, _, _, body, in_filter, _) => {
                walk(body, arities, extern_names, errors);
                if let Some(f) = in_filter {
                    walk(f, arities, extern_names, errors);
                }
            }
            EExpr::Block(exprs, _) => {
                for e in exprs {
                    walk(e, arities, extern_names, errors);
                }
            }
            EExpr::VarDecl(_, _, init, rest, _) => {
                walk(init, arities, extern_names, errors);
                walk(rest, arities, extern_names, errors);
            }
            EExpr::While(cond, _, body, _) => {
                walk(cond, arities, extern_names, errors);
                walk(body, arities, extern_names, errors);
            }
            EExpr::IfElse(cond, then_b, else_b, _) => {
                walk(cond, arities, extern_names, errors);
                walk(then_b, arities, extern_names, errors);
                if let Some(e) = else_b {
                    walk(e, arities, extern_names, errors);
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

    let arities = ctx.event_arities.clone();
    let extern_names: HashSet<String> = env.externs.keys().cloned().collect();

    for v in &mut env.verifies {
        for a in &mut v.asserts {
            walk(a, &arities, &extern_names, &mut errors);
        }
    }
    for t in &mut env.theorems {
        for s in &mut t.shows {
            walk(s, &arities, &extern_names, &mut errors);
        }
        for inv in &mut t.invariants {
            walk(inv, &arities, &extern_names, &mut errors);
        }
    }
    for l in &mut env.lemmas {
        for b in &mut l.body {
            walk(b, &arities, &extern_names, &mut errors);
        }
    }
    for p in env.props.values_mut() {
        walk(&mut p.body, &arities, &extern_names, &mut errors);
    }

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

    fn walk(expr: &EExpr, errors: &mut Vec<(String, Option<crate::span::Span>)>) {
        match expr {
            EExpr::Aggregate(_, kind, _, _, body, _in_filter, sp) => {
                let body_ty = body.ty();
                match kind {
                    AggKind::Count => {
                        // Body must be bool
                        if !matches!(body_ty, Ty::Builtin(BuiltinTy::Bool))
                            && !matches!(body_ty, Ty::Error)
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
                        // Body must be numeric
                        let is_numeric = matches!(
                            body_ty,
                            Ty::Builtin(BuiltinTy::Int | BuiltinTy::Real | BuiltinTy::Float)
                                | Ty::Error
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
                // Recurse into body
                walk(body, errors);
            }
            // Recurse into subexpressions
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
            | EExpr::NamedPair(_, _, e, _) => walk(e, errors),
            EExpr::BinOp(_, _, a, b, _)
            | EExpr::Until(_, a, b, _)
            | EExpr::Since(_, a, b, _)
            | EExpr::Assign(_, a, b, _)
            | EExpr::Seq(_, a, b, _)
            | EExpr::SameStep(_, a, b, _)
            | EExpr::In(_, a, b, _)
            | EExpr::Pipe(_, a, b, _)
            | EExpr::Index(_, a, b, _) => {
                walk(a, errors);
                walk(b, errors);
            }
            EExpr::Quant(_, _, _, _, body, _) | EExpr::Lam(_, _, body, _) => {
                walk(body, errors);
            }
            EExpr::Choose(_, _, _, predicate, _) => {
                if let Some(pred) = predicate {
                    walk(pred, errors);
                }
            }
            EExpr::Call(_, f, args, _) => {
                walk(f, errors);
                for a in args {
                    walk(a, errors);
                }
            }
            EExpr::CallR(_, f, args, refs, _) => {
                walk(f, errors);
                for a in args {
                    walk(a, errors);
                }
                for r in refs {
                    walk(r, errors);
                }
            }
            EExpr::Let(binds, body, _) => {
                for (_, _, e) in binds {
                    walk(e, errors);
                }
                walk(body, errors);
            }
            EExpr::Match(scrut, arms, _) => {
                walk(scrut, errors);
                for (_, guard, body) in arms {
                    if let Some(g) = guard {
                        walk(g, errors);
                    }
                    walk(body, errors);
                }
            }
            EExpr::MapUpdate(_, m, k, v, _) => {
                walk(m, errors);
                walk(k, errors);
                walk(v, errors);
            }
            EExpr::SetComp(_, proj, _, _, filter, _) => {
                if let Some(p) = proj {
                    walk(p, errors);
                }
                walk(filter, errors);
            }
            EExpr::TupleLit(_, elems, _)
            | EExpr::SetLit(_, elems, _)
            | EExpr::SeqLit(_, elems, _) => {
                for e in elems {
                    walk(e, errors);
                }
            }
            EExpr::MapLit(_, entries, _) => {
                for (k, v) in entries {
                    walk(k, errors);
                    walk(v, errors);
                }
            }
            EExpr::QualCall(_, _, _, args, _) => {
                for a in args {
                    walk(a, errors);
                }
            }
            EExpr::CtorRecord(_, _, _, fields, _) | EExpr::StructCtor(_, _, fields, _) => {
                for (_, e) in fields {
                    walk(e, errors);
                }
            }
            EExpr::Saw(_, _, _, args, _) => {
                for a in args.iter().flatten() {
                    walk(a, errors);
                }
            }
            EExpr::Block(exprs, _) => {
                for e in exprs {
                    walk(e, errors);
                }
            }
            EExpr::VarDecl(_, _, init, rest, _) => {
                walk(init, errors);
                walk(rest, errors);
            }
            EExpr::While(cond, _, body, _) => {
                walk(cond, errors);
                walk(body, errors);
            }
            EExpr::IfElse(cond, then_b, else_b, _) => {
                walk(cond, errors);
                walk(then_b, errors);
                if let Some(e) = else_b {
                    walk(e, errors);
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

    let mut errors = Vec::new();

    for v in &env.verifies {
        for a in &v.asserts {
            walk(a, &mut errors);
        }
    }
    for t in &env.theorems {
        for s in &t.shows {
            walk(s, &mut errors);
        }
        for inv in &t.invariants {
            walk(inv, &mut errors);
        }
    }
    for l in &env.lemmas {
        for b in &l.body {
            walk(b, &mut errors);
        }
    }
    for p in env.props.values() {
        walk(&p.body, &mut errors);
    }
    for p in env.preds.values() {
        walk(&p.body, &mut errors);
    }
    // Entity/system invariants and derived fields
    for e in env.entities.values() {
        for inv in &e.invariants {
            walk(&inv.body, &mut errors);
        }
        for d in &e.derived_fields {
            walk(&d.body, &mut errors);
        }
    }
    for s in env.systems.values() {
        for inv in &s.invariants {
            walk(&inv.body, &mut errors);
        }
        for d in &s.derived_fields {
            walk(&d.body, &mut errors);
        }
    }
    // Fn declarations: contracts (requires/ensures) and bodies
    for f in env.fns.values() {
        walk(&f.body, &mut errors);
        for c in &f.contracts {
            match c {
                crate::elab::types::EContract::Requires(e)
                | crate::elab::types::EContract::Ensures(e)
                | crate::elab::types::EContract::Invariant(e) => walk(e, &mut errors),
                crate::elab::types::EContract::Decreases { measures, .. } => {
                    for m in measures {
                        walk(m, &mut errors);
                    }
                }
            }
        }
    }

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
        EExpr::While(cond, _, body, _) => {
            collect_ty_params_in_expr(cond, out);
            collect_ty_params_in_expr(body, out);
        }
        EExpr::SetComp(_, expr, _, _, body, _) => {
            if let Some(e) = expr {
                collect_ty_params_in_expr(e, out);
            }
            collect_ty_params_in_expr(body, out);
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
        // Leaf expressions: Lit, Var, Qual, Unresolved, Sorry, Todo
        _ => {}
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
        Ty::Refinement(base, _) => {
            collect_named_in_ty(base, out);
        }
        _ => {}
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
        _ => {}
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
