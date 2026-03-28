//! Lower elaborated AST to Core IR.
//!
//! Desugars, resolves primed variables, computes frame conditions,
//! and produces a flat `IRProgram`.

use std::collections::HashMap;

use crate::elab::types as E;

use super::types::{
    Cardinality, IRAction, IRAxiom, IRConst, IRCreateField, IREntity, IREvent, IRExpr, IRField,
    IRFieldPat, IRFunction, IRMatchArm, IRPattern, IRProgram, IRRecordField, IRScene, IRSceneEvent,
    IRSceneGiven, IRSchedWhen, IRSchedule, IRSystem, IRTheorem, IRTransParam, IRTransRef,
    IRTransition, IRType, IRTypeEntry, IRUpdate, IRVerify, IRVerifySystem, LetBinding, LitVal,
};

// ── Top-level lowering ───────────────────────────────────────────────

pub fn lower(er: &E::ElabResult) -> IRProgram {
    // Collect props for inlining into verify/theorem blocks.
    // Props are parameterless named expressions.
    let mut prop_map: HashMap<String, IRExpr> = HashMap::new();
    for prop in &er.props {
        prop_map.insert(prop.name.clone(), lower_expr(&prop.body));
    }

    // Collect preds for inlining into verify/theorem blocks.
    // Preds have parameters — inlined via App substitution (replace param with arg).
    let mut pred_map: HashMap<String, (Vec<String>, IRExpr)> = HashMap::new();
    for pred in &er.preds {
        let param_names: Vec<String> = pred.params.iter().map(|(n, _)| n.clone()).collect();
        pred_map.insert(pred.name.clone(), (param_names, lower_expr(&pred.body)));
    }

    IRProgram {
        types: er.types.iter().map(lower_type).collect(),
        constants: er.consts.iter().map(lower_const).collect(),
        functions: er.fns.iter().map(lower_fn).collect(),
        entities: er.entities.iter().map(lower_entity).collect(),
        systems: er.systems.iter().map(lower_system).collect(),
        verifies: er
            .verifies
            .iter()
            .map(|v| lower_verify(v, &prop_map, &pred_map))
            .collect(),
        theorems: er
            .theorems
            .iter()
            .map(|t| lower_theorem(t, &prop_map, &pred_map))
            .collect(),
        axioms: er.axioms.iter().map(lower_axiom).collect(),
        scenes: er.scenes.iter().map(lower_scene).collect(),
    }
}

// ── Types ────────────────────────────────────────────────────────────

fn lower_type(et: &E::EType) -> IRTypeEntry {
    IRTypeEntry {
        name: et.name.clone(),
        ty: lower_ty(&et.ty),
    }
}

fn lower_ty(ty: &E::Ty) -> IRType {
    match ty {
        E::Ty::Enum(n, cs) => IRType::Enum {
            name: n.clone(),
            constructors: cs.clone(),
        },
        E::Ty::Record(n, fs) => IRType::Record {
            name: n.clone(),
            fields: fs
                .iter()
                .map(|(fn_, ft)| IRRecordField {
                    name: fn_.clone(),
                    ty: lower_ty(ft),
                })
                .collect(),
        },
        E::Ty::Alias(_, t) => lower_ty(t),
        E::Ty::Builtin(b) => lower_builtin(*b),
        E::Ty::Param(n, _) => IRType::Record {
            name: n.clone(),
            fields: Vec::new(),
        },
        E::Ty::Fn(a, b) => IRType::Fn {
            param: Box::new(lower_ty(a)),
            result: Box::new(lower_ty(b)),
        },
        E::Ty::Entity(n) => IRType::Entity { name: n.clone() },
        E::Ty::Unresolved(_) => IRType::String,
        E::Ty::Set(a) => IRType::Set {
            element: Box::new(lower_ty(a)),
        },
        E::Ty::Seq(a) => IRType::Seq {
            element: Box::new(lower_ty(a)),
        },
        E::Ty::Map(k, v) => IRType::Map {
            key: Box::new(lower_ty(k)),
            value: Box::new(lower_ty(v)),
        },
        E::Ty::Tuple(ts) => IRType::Tuple {
            elements: ts.iter().map(lower_ty).collect(),
        },
    }
}

fn lower_builtin(b: E::BuiltinTy) -> IRType {
    match b {
        E::BuiltinTy::Int => IRType::Int,
        E::BuiltinTy::Bool => IRType::Bool,
        E::BuiltinTy::String => IRType::String,
        E::BuiltinTy::Id => IRType::Id,
        E::BuiltinTy::Real => IRType::Real,
        E::BuiltinTy::Float => IRType::Float,
    }
}

// ── Constants and Functions ──────────────────────────────────────────

fn lower_const(ec: &E::EConst) -> IRConst {
    IRConst {
        name: ec.name.clone(),
        ty: lower_ty(&ec.body.ty()),
        value: lower_expr(&ec.body),
    }
}

fn lower_fn(ef: &E::EFn) -> IRFunction {
    let ret_ty = lower_ty(&ef.ret_ty);
    let fn_ty = ef
        .params
        .iter()
        .rev()
        .fold(ret_ty.clone(), |acc, (_, pt)| IRType::Fn {
            param: Box::new(lower_ty(pt)),
            result: Box::new(acc),
        });
    let body = ef
        .params
        .iter()
        .rev()
        .fold(lower_expr(&ef.body), |acc, (pn, pt)| IRExpr::Lam {
            param: pn.clone(),
            param_type: lower_ty(pt),
            body: Box::new(acc),
        });
    IRFunction {
        name: ef.name.clone(),
        ty: fn_ty,
        body,
    }
}

// ── Entities ─────────────────────────────────────────────────────────

fn lower_entity(ee: &E::EEntity) -> IREntity {
    IREntity {
        name: ee.name.clone(),
        fields: ee.fields.iter().map(lower_field).collect(),
        transitions: ee.actions.iter().map(lower_action).collect(),
    }
}

fn lower_field(ef: &E::EField) -> IRField {
    IRField {
        name: ef.name.clone(),
        ty: lower_ty(&ef.ty),
        default: ef.default.as_ref().map(lower_expr),
    }
}

fn lower_action(ea: &E::EAction) -> IRTransition {
    IRTransition {
        name: ea.name.clone(),
        refs: ea
            .refs
            .iter()
            .map(|(rn, rt)| IRTransRef {
                name: rn.clone(),
                entity: rt.name().to_owned(),
            })
            .collect(),
        params: ea
            .params
            .iter()
            .map(|(pn, pt)| IRTransParam {
                name: pn.clone(),
                ty: lower_ty(pt),
            })
            .collect(),
        guard: lower_guard(&ea.requires),
        updates: extract_updates(&ea.body),
        postcondition: None,
    }
}

fn lower_guard(reqs: &[E::EExpr]) -> IRExpr {
    match reqs {
        [] => IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
        },
        [e] => lower_expr(e),
        [e, rest @ ..] => IRExpr::BinOp {
            op: "OpAnd".to_owned(),
            left: Box::new(lower_expr(e)),
            right: Box::new(lower_guard(rest)),
            ty: IRType::Bool,
        },
    }
}

fn extract_updates(body: &[E::EExpr]) -> Vec<IRUpdate> {
    body.iter()
        .filter_map(|e| {
            if let E::EExpr::Assign(_, lhs, rhs) = e {
                if let E::EExpr::Prime(_, inner) = lhs.as_ref() {
                    if let E::EExpr::Var(_, field) = inner.as_ref() {
                        return Some(IRUpdate {
                            field: field.clone(),
                            value: lower_expr(rhs),
                        });
                    }
                }
            }
            None
        })
        .collect()
}

// ── Systems ──────────────────────────────────────────────────────────

fn lower_system(es: &E::ESystem) -> IRSystem {
    IRSystem {
        name: es.name.clone(),
        entities: es.uses.clone(),
        events: es.events.iter().map(lower_event).collect(),
        schedule: lower_schedule(&es.next_items),
    }
}

fn lower_event(ev: &E::EEvent) -> IREvent {
    let post = if ev.ensures.is_empty() {
        None
    } else {
        Some(lower_guard(&ev.ensures))
    };
    IREvent {
        name: ev.name.clone(),
        params: ev
            .params
            .iter()
            .map(|(pn, pt)| IRTransParam {
                name: pn.clone(),
                ty: lower_ty(pt),
            })
            .collect(),
        guard: lower_guard(&ev.requires),
        postcondition: post,
        body: ev.body.iter().map(lower_event_action).collect(),
    }
}

fn lower_event_action(ea: &E::EEventAction) -> IRAction {
    match ea {
        E::EEventAction::Choose(v, ty, guard, body) => IRAction::Choose {
            var: v.clone(),
            entity: ty.name().to_owned(),
            filter: Box::new(lower_expr(guard)),
            ops: body.iter().map(lower_event_action).collect(),
        },
        E::EEventAction::ForAll(v, ty, body) => IRAction::ForAll {
            var: v.clone(),
            entity: ty.name().to_owned(),
            ops: body.iter().map(lower_event_action).collect(),
        },
        E::EEventAction::Create(entity, fields) => IRAction::Create {
            entity: entity.clone(),
            fields: fields
                .iter()
                .map(|(fn_, fe)| IRCreateField {
                    name: fn_.clone(),
                    value: lower_expr(fe),
                })
                .collect(),
        },
        E::EEventAction::CrossCall(sys, ev, args) => IRAction::CrossCall {
            system: sys.clone(),
            event: ev.clone(),
            args: args.iter().map(lower_expr).collect(),
        },
        E::EEventAction::Apply(target, act, refs, args) => IRAction::Apply {
            target: extract_target_name(target),
            transition: act.clone(),
            refs: refs.iter().map(extract_target_name).collect(),
            args: args.iter().map(lower_expr).collect(),
        },
        E::EEventAction::Expr(e) => IRAction::ExprStmt {
            expr: lower_expr(e),
        },
    }
}

fn extract_target_name(e: &E::EExpr) -> String {
    match e {
        E::EExpr::Var(_, n) => n.clone(),
        _ => "_".to_owned(),
    }
}

fn lower_schedule(items: &[E::ENextItem]) -> IRSchedule {
    let when = items
        .iter()
        .filter_map(|ni| match ni {
            E::ENextItem::When(cond, ev_name) => Some(IRSchedWhen {
                condition: lower_expr(cond),
                event: ev_name.clone(),
            }),
            E::ENextItem::Else => None,
        })
        .collect();
    let idle = items.iter().any(|ni| matches!(ni, E::ENextItem::Else));
    IRSchedule { when, idle }
}

// ── Verification ─────────────────────────────────────────────────────

fn lower_verify(
    ev: &E::EVerify,
    prop_map: &HashMap<String, IRExpr>,
    pred_map: &HashMap<String, (Vec<String>, IRExpr)>,
) -> IRVerify {
    IRVerify {
        name: ev.name.clone(),
        systems: ev
            .targets
            .iter()
            .map(|(n, lo, hi)| IRVerifySystem {
                name: n.clone(),
                lo: *lo,
                hi: *hi,
            })
            .collect(),
        asserts: ev
            .asserts
            .iter()
            .map(|a| {
                let lowered = lower_expr(a);
                substitute_defs(lowered, prop_map, pred_map)
            })
            .collect(),
    }
}

fn lower_theorem(
    et: &E::ETheorem,
    prop_map: &HashMap<String, IRExpr>,
    pred_map: &HashMap<String, (Vec<String>, IRExpr)>,
) -> IRTheorem {
    IRTheorem {
        name: et.name.clone(),
        systems: et.targets.clone(),
        invariants: et
            .invariants
            .iter()
            .map(|i| substitute_defs(lower_expr(i), prop_map, pred_map))
            .collect(),
        shows: et
            .shows
            .iter()
            .map(|s| substitute_defs(lower_expr(s), prop_map, pred_map))
            .collect(),
    }
}

fn lower_axiom(ea: &E::EAxiom) -> IRAxiom {
    IRAxiom {
        name: ea.name.clone(),
        body: lower_expr(&ea.body),
    }
}

fn lower_scene(es: &E::EScene) -> IRScene {
    let (actions, assumes): (Vec<_>, Vec<_>) = es
        .whens
        .iter()
        .partition(|w| !matches!(w, E::ESceneWhen::Assume(_)));

    IRScene {
        name: es.name.clone(),
        systems: es.targets.clone(),
        givens: es.givens.iter().map(lower_given).collect(),
        events: actions.iter().map(|w| lower_scene_action(w)).collect(),
        ordering: assumes
            .iter()
            .filter_map(|w| match w {
                E::ESceneWhen::Assume(e) => Some(lower_expr(e)),
                E::ESceneWhen::Action { .. } => None,
            })
            .collect(),
        assertions: es.thens.iter().map(lower_expr).collect(),
    }
}

fn lower_given(g: &E::ESceneGiven) -> IRSceneGiven {
    let constraint = match &g.condition {
        Some(e) => lower_expr(e),
        None => IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
        },
    };
    IRSceneGiven {
        var: g.var.clone(),
        entity: g.entity_type.clone(),
        constraint,
    }
}

fn lower_scene_action(w: &E::ESceneWhen) -> IRSceneEvent {
    match w {
        E::ESceneWhen::Action {
            var,
            system,
            event,
            args,
            card,
        } => IRSceneEvent {
            var: var.clone(),
            system: system.clone(),
            event: event.clone(),
            args: args.iter().map(lower_expr).collect(),
            cardinality: card_from_text(card.as_deref()),
        },
        E::ESceneWhen::Assume(_) => unreachable!("assumes partitioned out"),
    }
}

fn card_from_text(s: Option<&str>) -> Cardinality {
    match s {
        None | Some("one") => Cardinality::Named("one".to_owned()),
        Some("lone") => Cardinality::Named("lone".to_owned()),
        Some("some") => Cardinality::Named("some".to_owned()),
        Some("no") => Cardinality::Named("no".to_owned()),
        Some(n) => match n.parse::<i64>() {
            Ok(i) => Cardinality::Exact { exactly: i },
            Err(_) => Cardinality::Named("one".to_owned()),
        },
    }
}

// ── Prop and pred inlining ───────────────────────────────────────────

/// Substitute `Var` references matching prop names, and `App(Var(pred), arg)`
/// calls matching pred names, with their inlined bodies.
///
/// Props are parameterless named expressions. Preds have parameters — when
/// `App { func: Var(name), arg }` matches a pred, the pred body is returned
/// with all occurrences of the parameter variable replaced by the argument.
#[allow(clippy::too_many_lines)]
/// Fixed-point inlining: run `substitute_defs_once` repeatedly until
/// the expression stops changing or we hit 20 iterations (safety cap).
fn substitute_defs(
    expr: IRExpr,
    prop_map: &HashMap<String, IRExpr>,
    pred_map: &HashMap<String, (Vec<String>, IRExpr)>,
) -> IRExpr {
    let mut result = expr;
    for _ in 0..20 {
        let next = substitute_defs_once(result.clone(), prop_map, pred_map);
        if format!("{next:?}") == format!("{result:?}") {
            return next;
        }
        result = next;
    }
    result
}

/// Single pass: inline prop Var references and pred App calls.
/// Does NOT recurse into inlined bodies — the caller loops to fixed point.
#[allow(clippy::too_many_lines)]
fn substitute_defs_once(
    expr: IRExpr,
    prop_map: &HashMap<String, IRExpr>,
    pred_map: &HashMap<String, (Vec<String>, IRExpr)>,
) -> IRExpr {
    match expr {
        IRExpr::Var { ref name, .. } => {
            if let Some(body) = prop_map.get(name) {
                body.clone()
            } else {
                expr
            }
        }
        // Pred call: App chain — inline once, don't recurse into result.
        IRExpr::App { .. } => {
            let mut args = Vec::new();
            let mut current = &expr;
            while let IRExpr::App { func, arg, .. } = current {
                args.push(arg.as_ref());
                current = func.as_ref();
            }
            args.reverse();

            if let IRExpr::Var { name, .. } = current {
                if let Some((params, body)) = pred_map.get(name) {
                    if params.len() == args.len() {
                        let mut result = body.clone();
                        for (param_name, arg_expr) in params.iter().zip(args.iter()) {
                            let substituted_arg =
                                substitute_defs_once((*arg_expr).clone(), prop_map, pred_map);
                            result = substitute_var_in_expr(result, param_name, &substituted_arg);
                        }
                        return result; // return without recursing — outer loop handles it
                    }
                }
            }
            // Not a pred call — recurse structurally
            let IRExpr::App { func, arg, ty } = expr else {
                unreachable!()
            };
            IRExpr::App {
                func: Box::new(substitute_defs_once(*func, prop_map, pred_map)),
                arg: Box::new(substitute_defs_once(*arg, prop_map, pred_map)),
                ty,
            }
        }
        IRExpr::Always { body } => IRExpr::Always {
            body: Box::new(substitute_defs_once(*body, prop_map, pred_map)),
        },
        IRExpr::Eventually { body } => IRExpr::Eventually {
            body: Box::new(substitute_defs_once(*body, prop_map, pred_map)),
        },
        IRExpr::BinOp {
            op,
            left,
            right,
            ty,
        } => IRExpr::BinOp {
            op,
            left: Box::new(substitute_defs_once(*left, prop_map, pred_map)),
            right: Box::new(substitute_defs_once(*right, prop_map, pred_map)),
            ty,
        },
        IRExpr::UnOp { op, operand, ty } => IRExpr::UnOp {
            op,
            operand: Box::new(substitute_defs_once(*operand, prop_map, pred_map)),
            ty,
        },
        IRExpr::Forall { var, domain, body } => IRExpr::Forall {
            var,
            domain,
            body: Box::new(substitute_defs_once(*body, prop_map, pred_map)),
        },
        IRExpr::Exists { var, domain, body } => IRExpr::Exists {
            var,
            domain,
            body: Box::new(substitute_defs_once(*body, prop_map, pred_map)),
        },
        IRExpr::Field { expr, field, ty } => IRExpr::Field {
            expr: Box::new(substitute_defs_once(*expr, prop_map, pred_map)),
            field,
            ty,
        },
        IRExpr::Prime { expr } => IRExpr::Prime {
            expr: Box::new(substitute_defs_once(*expr, prop_map, pred_map)),
        },
        IRExpr::Let { bindings, body } => IRExpr::Let {
            bindings: bindings
                .into_iter()
                .map(|b| LetBinding {
                    name: b.name,
                    ty: b.ty,
                    expr: substitute_defs_once(b.expr, prop_map, pred_map),
                })
                .collect(),
            body: Box::new(substitute_defs_once(*body, prop_map, pred_map)),
        },
        IRExpr::Lam {
            param,
            param_type,
            body,
        } => IRExpr::Lam {
            param,
            param_type,
            body: Box::new(substitute_defs_once(*body, prop_map, pred_map)),
        },
        IRExpr::Match { scrutinee, arms } => IRExpr::Match {
            scrutinee: Box::new(substitute_defs_once(*scrutinee, prop_map, pred_map)),
            arms: arms
                .into_iter()
                .map(|a| IRMatchArm {
                    pattern: a.pattern,
                    guard: a.guard.map(|g| substitute_defs_once(g, prop_map, pred_map)),
                    body: substitute_defs_once(a.body, prop_map, pred_map),
                })
                .collect(),
        },
        IRExpr::MapUpdate {
            map,
            key,
            value,
            ty,
        } => IRExpr::MapUpdate {
            map: Box::new(substitute_defs_once(*map, prop_map, pred_map)),
            key: Box::new(substitute_defs_once(*key, prop_map, pred_map)),
            value: Box::new(substitute_defs_once(*value, prop_map, pred_map)),
            ty,
        },
        IRExpr::Index { map, key, ty } => IRExpr::Index {
            map: Box::new(substitute_defs_once(*map, prop_map, pred_map)),
            key: Box::new(substitute_defs_once(*key, prop_map, pred_map)),
            ty,
        },
        IRExpr::SetComp {
            var,
            domain,
            filter,
            projection,
            ty,
        } => IRExpr::SetComp {
            var,
            domain,
            filter: Box::new(substitute_defs_once(*filter, prop_map, pred_map)),
            projection: projection.map(|p| Box::new(substitute_defs_once(*p, prop_map, pred_map))),
            ty,
        },
        IRExpr::SetLit { elements, ty } => IRExpr::SetLit {
            elements: elements
                .into_iter()
                .map(|e| substitute_defs_once(e, prop_map, pred_map))
                .collect(),
            ty,
        },
        IRExpr::SeqLit { elements, ty } => IRExpr::SeqLit {
            elements: elements
                .into_iter()
                .map(|e| substitute_defs_once(e, prop_map, pred_map))
                .collect(),
            ty,
        },
        IRExpr::MapLit { entries, ty } => IRExpr::MapLit {
            entries: entries
                .into_iter()
                .map(|(k, v)| {
                    (
                        substitute_defs_once(k, prop_map, pred_map),
                        substitute_defs_once(v, prop_map, pred_map),
                    )
                })
                .collect(),
            ty,
        },
        // Leaf nodes that contain no sub-expressions
        other => other,
    }
}

/// Replace all occurrences of `Var(var_name)` with `replacement` in `expr`.
///
/// Also handles `Field(Var(var_name), field)` by producing
/// `Field(replacement, field)` so that `d.status` with `d` replaced by the
/// argument expression correctly resolves field access.
#[allow(clippy::too_many_lines)]
fn substitute_var_in_expr(expr: IRExpr, var_name: &str, replacement: &IRExpr) -> IRExpr {
    match expr {
        IRExpr::Var { ref name, .. } if name == var_name => replacement.clone(),
        IRExpr::Field {
            expr: ref inner,
            ref field,
            ref ty,
        } => {
            if let IRExpr::Var { name, .. } = inner.as_ref() {
                if name == var_name {
                    return IRExpr::Field {
                        expr: Box::new(replacement.clone()),
                        field: field.clone(),
                        ty: ty.clone(),
                    };
                }
            }
            let IRExpr::Field { expr, field, ty } = expr else {
                unreachable!()
            };
            IRExpr::Field {
                expr: Box::new(substitute_var_in_expr(*expr, var_name, replacement)),
                field,
                ty,
            }
        }
        IRExpr::BinOp {
            op,
            left,
            right,
            ty,
        } => IRExpr::BinOp {
            op,
            left: Box::new(substitute_var_in_expr(*left, var_name, replacement)),
            right: Box::new(substitute_var_in_expr(*right, var_name, replacement)),
            ty,
        },
        IRExpr::UnOp { op, operand, ty } => IRExpr::UnOp {
            op,
            operand: Box::new(substitute_var_in_expr(*operand, var_name, replacement)),
            ty,
        },
        IRExpr::Always { body } => IRExpr::Always {
            body: Box::new(substitute_var_in_expr(*body, var_name, replacement)),
        },
        IRExpr::Eventually { body } => IRExpr::Eventually {
            body: Box::new(substitute_var_in_expr(*body, var_name, replacement)),
        },
        IRExpr::Forall { var, domain, body } => IRExpr::Forall {
            var: var.clone(),
            domain,
            body: if var == var_name {
                body // shadowed — don't substitute
            } else {
                Box::new(substitute_var_in_expr(*body, var_name, replacement))
            },
        },
        IRExpr::Exists { var, domain, body } => IRExpr::Exists {
            var: var.clone(),
            domain,
            body: if var == var_name {
                body
            } else {
                Box::new(substitute_var_in_expr(*body, var_name, replacement))
            },
        },
        IRExpr::App { func, arg, ty } => IRExpr::App {
            func: Box::new(substitute_var_in_expr(*func, var_name, replacement)),
            arg: Box::new(substitute_var_in_expr(*arg, var_name, replacement)),
            ty,
        },
        IRExpr::Prime { expr } => IRExpr::Prime {
            expr: Box::new(substitute_var_in_expr(*expr, var_name, replacement)),
        },
        IRExpr::Lam {
            param,
            param_type,
            body,
        } => IRExpr::Lam {
            param: param.clone(),
            param_type,
            body: if param == var_name {
                body
            } else {
                Box::new(substitute_var_in_expr(*body, var_name, replacement))
            },
        },
        IRExpr::Let { bindings, body } => {
            let mut shadowed = false;
            let new_bindings: Vec<LetBinding> = bindings
                .into_iter()
                .map(|b| {
                    let new_expr = if shadowed {
                        b.expr
                    } else {
                        substitute_var_in_expr(b.expr, var_name, replacement)
                    };
                    if b.name == var_name {
                        shadowed = true;
                    }
                    LetBinding {
                        name: b.name,
                        ty: b.ty,
                        expr: new_expr,
                    }
                })
                .collect();
            IRExpr::Let {
                bindings: new_bindings,
                body: if shadowed {
                    body
                } else {
                    Box::new(substitute_var_in_expr(*body, var_name, replacement))
                },
            }
        }
        // Leaf nodes and everything else — return as-is
        other => other,
    }
}

// ── Expression lowering ──────────────────────────────────────────────

#[allow(clippy::too_many_lines)]
fn lower_expr(e: &E::EExpr) -> IRExpr {
    match e {
        E::EExpr::Lit(ty, lit) => IRExpr::Lit {
            ty: lower_ty(ty),
            value: lower_lit(lit),
        },
        E::EExpr::Var(ty, n) => {
            // Check if this is a constructor of an enum type
            if let E::Ty::Enum(enum_name, ctors) = ty {
                if ctors.contains(n) {
                    return IRExpr::Ctor {
                        enum_name: enum_name.clone(),
                        ctor: n.clone(),
                    };
                }
            }
            IRExpr::Var {
                name: n.clone(),
                ty: lower_ty(ty),
            }
        }
        E::EExpr::Field(ty, expr, f) => IRExpr::Field {
            expr: Box::new(lower_expr(expr)),
            field: f.clone(),
            ty: lower_ty(ty),
        },
        E::EExpr::Prime(_, expr) => IRExpr::Prime {
            expr: Box::new(lower_expr(expr)),
        },
        E::EExpr::BinOp(ty, op, a, b) => IRExpr::BinOp {
            op: format!("{:?}", lower_binop(*op)),
            left: Box::new(lower_expr(a)),
            right: Box::new(lower_expr(b)),
            ty: lower_ty(ty),
        },
        E::EExpr::UnOp(ty, op, expr) => IRExpr::UnOp {
            op: format!("{:?}", lower_unop(*op)),
            operand: Box::new(lower_expr(expr)),
            ty: lower_ty(ty),
        },
        E::EExpr::Call(ty, f, args) => {
            let lowered_f = lower_expr(f);
            let ir_ty = lower_ty(ty);
            args.iter().fold(lowered_f, |acc, arg| IRExpr::App {
                func: Box::new(acc),
                arg: Box::new(lower_expr(arg)),
                ty: ir_ty.clone(),
            })
        }
        E::EExpr::CallR(ty, f, refs, args) => {
            let lowered_f = lower_expr(f);
            let ir_ty = lower_ty(ty);
            let with_refs = refs.iter().fold(lowered_f, |acc, r| IRExpr::App {
                func: Box::new(acc),
                arg: Box::new(lower_expr(r)),
                ty: ir_ty.clone(),
            });
            args.iter().fold(with_refs, |acc, arg| IRExpr::App {
                func: Box::new(acc),
                arg: Box::new(lower_expr(arg)),
                ty: ir_ty.clone(),
            })
        }
        E::EExpr::Qual(ty, s, n) => {
            if let E::Ty::Enum(enum_name, ctors) = ty {
                if ctors.contains(n) {
                    return IRExpr::Ctor {
                        enum_name: enum_name.clone(),
                        ctor: n.clone(),
                    };
                }
            }
            IRExpr::Var {
                name: format!("{s}::{n}"),
                ty: lower_ty(ty),
            }
        }
        E::EExpr::Quant(_, q, v, vty, body) => {
            let lowered = lower_expr(body);
            let vt = lower_ty(vty);
            match q {
                E::Quantifier::All => IRExpr::Forall {
                    var: v.clone(),
                    domain: vt,
                    body: Box::new(lowered),
                },
                E::Quantifier::Exists
                | E::Quantifier::Some
                | E::Quantifier::One
                | E::Quantifier::Lone => IRExpr::Exists {
                    var: v.clone(),
                    domain: vt,
                    body: Box::new(lowered),
                },
                E::Quantifier::No => IRExpr::UnOp {
                    op: "OpNot".to_owned(),
                    operand: Box::new(IRExpr::Exists {
                        var: v.clone(),
                        domain: vt,
                        body: Box::new(lowered),
                    }),
                    ty: IRType::Bool,
                },
            }
        }
        E::EExpr::Always(_, expr) => IRExpr::Always {
            body: Box::new(lower_expr(expr)),
        },
        E::EExpr::Eventually(_, expr) => IRExpr::Eventually {
            body: Box::new(lower_expr(expr)),
        },
        E::EExpr::Assert(_, expr) | E::EExpr::NamedPair(_, _, expr) => lower_expr(expr),
        E::EExpr::Assign(_, lhs, rhs) => IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(lower_expr(lhs)),
            right: Box::new(lower_expr(rhs)),
            ty: IRType::Bool,
        },
        E::EExpr::Seq(ty, a, b) => IRExpr::BinOp {
            op: "OpSeq".to_owned(),
            left: Box::new(lower_expr(a)),
            right: Box::new(lower_expr(b)),
            ty: lower_ty(ty),
        },
        E::EExpr::SameStep(ty, a, b) => IRExpr::BinOp {
            op: "OpSameStep".to_owned(),
            left: Box::new(lower_expr(a)),
            right: Box::new(lower_expr(b)),
            ty: lower_ty(ty),
        },
        E::EExpr::Let(binds, body) => {
            let bs = binds
                .iter()
                .map(|(n, mt, e)| LetBinding {
                    name: n.clone(),
                    ty: mt.as_ref().map_or(IRType::String, lower_ty),
                    expr: lower_expr(e),
                })
                .collect();
            IRExpr::Let {
                bindings: bs,
                body: Box::new(lower_expr(body)),
            }
        }
        E::EExpr::Lam(params, _mret, body) => {
            if params.is_empty() {
                return lower_expr(body);
            }
            params
                .iter()
                .rev()
                .fold(lower_expr(body), |acc, (pn, pt)| IRExpr::Lam {
                    param: pn.clone(),
                    param_type: lower_ty(pt),
                    body: Box::new(acc),
                })
        }
        E::EExpr::Unresolved(n) => IRExpr::Var {
            name: n.clone(),
            ty: IRType::String,
        },
        E::EExpr::TupleLit(ty, es) => {
            let lowered: Vec<IRExpr> = es.iter().map(lower_expr).collect();
            let tuple_ty = lower_ty(ty);
            lowered.into_iter().fold(
                IRExpr::Var {
                    name: "Tuple".to_owned(),
                    ty: tuple_ty.clone(),
                },
                |acc, arg| IRExpr::App {
                    func: Box::new(acc),
                    arg: Box::new(arg),
                    ty: tuple_ty.clone(),
                },
            )
        }
        E::EExpr::In(ty, e, s) => IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::App {
                func: Box::new(IRExpr::Var {
                    name: "contains".to_owned(),
                    ty: IRType::Bool,
                }),
                arg: Box::new(lower_expr(s)),
                ty: IRType::Bool,
            }),
            right: Box::new(lower_expr(e)),
            ty: lower_ty(ty),
        },
        E::EExpr::Card(ty, expr) => IRExpr::App {
            func: Box::new(IRExpr::Var {
                name: "card".to_owned(),
                ty: lower_ty(ty),
            }),
            arg: Box::new(lower_expr(expr)),
            ty: lower_ty(ty),
        },
        E::EExpr::Pipe(ty, a, f) => IRExpr::App {
            func: Box::new(lower_expr(f)),
            arg: Box::new(lower_expr(a)),
            ty: lower_ty(ty),
        },
        E::EExpr::Match(scrutinee, arms) => IRExpr::Match {
            scrutinee: Box::new(lower_expr(scrutinee)),
            arms: arms
                .iter()
                .map(|(pat, guard, body)| IRMatchArm {
                    pattern: lower_pattern(pat),
                    guard: guard.as_ref().map(lower_expr),
                    body: lower_expr(body),
                })
                .collect(),
        },
        E::EExpr::MapUpdate(ty, m, k, v) => IRExpr::MapUpdate {
            map: Box::new(lower_expr(m)),
            key: Box::new(lower_expr(k)),
            value: Box::new(lower_expr(v)),
            ty: lower_ty(ty),
        },
        E::EExpr::Index(ty, m, k) => IRExpr::Index {
            map: Box::new(lower_expr(m)),
            key: Box::new(lower_expr(k)),
            ty: lower_ty(ty),
        },
        E::EExpr::SetComp(ty, proj, var, domain, filter) => IRExpr::SetComp {
            var: var.clone(),
            domain: lower_ty(domain),
            filter: Box::new(lower_expr(filter)),
            projection: proj.as_ref().map(|p| Box::new(lower_expr(p))),
            ty: lower_ty(ty),
        },
        E::EExpr::SetLit(ty, elems) => IRExpr::SetLit {
            elements: elems.iter().map(lower_expr).collect(),
            ty: lower_ty(ty),
        },
        E::EExpr::SeqLit(ty, elems) => IRExpr::SeqLit {
            elements: elems.iter().map(lower_expr).collect(),
            ty: lower_ty(ty),
        },
        E::EExpr::MapLit(ty, entries) => IRExpr::MapLit {
            entries: entries
                .iter()
                .map(|(k, v)| (lower_expr(k), lower_expr(v)))
                .collect(),
            ty: lower_ty(ty),
        },
        E::EExpr::Sorry => IRExpr::Sorry,
        E::EExpr::Todo => IRExpr::Todo,
    }
}

fn lower_pattern(pat: &E::EPattern) -> IRPattern {
    match pat {
        E::EPattern::Var(name) => IRPattern::PVar { name: name.clone() },
        E::EPattern::Ctor(name, fields) => IRPattern::PCtor {
            name: name.clone(),
            fields: fields
                .iter()
                .map(|(fname, fpat)| IRFieldPat {
                    name: fname.clone(),
                    pattern: lower_pattern(fpat),
                })
                .collect(),
        },
        E::EPattern::Wild => IRPattern::PWild,
        E::EPattern::Or(left, right) => IRPattern::POr {
            left: Box::new(lower_pattern(left)),
            right: Box::new(lower_pattern(right)),
        },
    }
}

fn lower_lit(lit: &E::Literal) -> LitVal {
    match lit {
        E::Literal::Int(i) => LitVal::Int { value: *i },
        E::Literal::Real(d) => LitVal::Real { value: *d },
        E::Literal::Float(d) => LitVal::Float { value: *d },
        E::Literal::Str(s) => LitVal::Str { value: s.clone() },
        E::Literal::Bool(b) => LitVal::Bool { value: *b },
    }
}

/// Operator names match Haskell's `show` output for differential testing.
#[allow(clippy::enum_variant_names)]
enum IRBinOp {
    OpAdd,
    OpSub,
    OpMul,
    OpDiv,
    OpMod,
    OpEq,
    OpNEq,
    OpLt,
    OpGt,
    OpLe,
    OpGe,
    OpAnd,
    OpOr,
    OpImplies,
    OpUnord,
    OpConc,
    OpXor,
}

impl std::fmt::Debug for IRBinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OpAdd => write!(f, "OpAdd"),
            Self::OpSub => write!(f, "OpSub"),
            Self::OpMul => write!(f, "OpMul"),
            Self::OpDiv => write!(f, "OpDiv"),
            Self::OpMod => write!(f, "OpMod"),
            Self::OpEq => write!(f, "OpEq"),
            Self::OpNEq => write!(f, "OpNEq"),
            Self::OpLt => write!(f, "OpLt"),
            Self::OpGt => write!(f, "OpGt"),
            Self::OpLe => write!(f, "OpLe"),
            Self::OpGe => write!(f, "OpGe"),
            Self::OpAnd => write!(f, "OpAnd"),
            Self::OpOr => write!(f, "OpOr"),
            Self::OpImplies => write!(f, "OpImplies"),
            Self::OpUnord => write!(f, "OpUnord"),
            Self::OpConc => write!(f, "OpConc"),
            Self::OpXor => write!(f, "OpXor"),
        }
    }
}

fn lower_binop(op: E::BinOp) -> IRBinOp {
    match op {
        E::BinOp::Add => IRBinOp::OpAdd,
        E::BinOp::Sub => IRBinOp::OpSub,
        E::BinOp::Mul => IRBinOp::OpMul,
        E::BinOp::Div => IRBinOp::OpDiv,
        E::BinOp::Mod => IRBinOp::OpMod,
        E::BinOp::Eq => IRBinOp::OpEq,
        E::BinOp::NEq => IRBinOp::OpNEq,
        E::BinOp::Lt => IRBinOp::OpLt,
        E::BinOp::Gt => IRBinOp::OpGt,
        E::BinOp::Le => IRBinOp::OpLe,
        E::BinOp::Ge => IRBinOp::OpGe,
        E::BinOp::And => IRBinOp::OpAnd,
        E::BinOp::Or => IRBinOp::OpOr,
        E::BinOp::Implies => IRBinOp::OpImplies,
        E::BinOp::Unord => IRBinOp::OpUnord,
        E::BinOp::Conc => IRBinOp::OpConc,
        E::BinOp::Xor => IRBinOp::OpXor,
    }
}

#[allow(clippy::enum_variant_names)]
enum IRUnOp {
    OpNot,
    OpNeg,
}

impl std::fmt::Debug for IRUnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OpNot => write!(f, "OpNot"),
            Self::OpNeg => write!(f, "OpNeg"),
        }
    }
}

fn lower_unop(op: E::UnOp) -> IRUnOp {
    match op {
        E::UnOp::Not => IRUnOp::OpNot,
        E::UnOp::Neg => IRUnOp::OpNeg,
    }
}
