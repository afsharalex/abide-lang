//! Lower elaborated AST to Core IR.
//!
//! Desugars, resolves primed variables, computes frame conditions,
//! and produces a flat `IRProgram`.

use crate::elab::types as E;

use super::types::{
    Cardinality, IRAction, IRAxiom, IRConst, IRCreateField, IRDecreases, IREntity, IREvent, IRExpr,
    IRField, IRFieldPat, IRFunction, IRMatchArm, IRPattern, IRProgram, IRRecordField, IRScene,
    IRSceneEvent, IRSceneGiven, IRSchedWhen, IRSchedule, IRSystem, IRTheorem, IRTransParam,
    IRTransRef, IRTransition, IRType, IRTypeEntry, IRUpdate, IRVerify, IRVerifySystem, LetBinding,
    LitVal,
};

// ── Top-level lowering ───────────────────────────────────────────────

pub fn lower(er: &E::ElabResult) -> IRProgram {
    // All definitions (fn, pred, prop) are lowered uniformly into IRFunction.
    // pred is fn -> Bool with params. prop is nullary fn -> Bool.
    let mut functions: Vec<IRFunction> = Vec::new();
    for f in &er.fns {
        functions.push(lower_fn(f));
    }
    for pred in &er.preds {
        functions.push(lower_pred(pred));
    }
    for prop in &er.props {
        functions.push(lower_prop(prop));
    }

    IRProgram {
        types: er.types.iter().map(lower_type).collect(),
        constants: er.consts.iter().map(lower_const).collect(),
        functions,
        entities: er.entities.iter().map(lower_entity).collect(),
        systems: er.systems.iter().map(lower_system).collect(),
        verifies: er.verifies.iter().map(lower_verify).collect(),
        theorems: er.theorems.iter().map(lower_theorem).collect(),
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

fn lower_contracts(
    contracts: &[E::EContract],
) -> (Vec<IRExpr>, Vec<IRExpr>, Option<IRDecreases>) {
    let mut requires = Vec::new();
    let mut ensures = Vec::new();
    let mut decreases = None;
    for c in contracts {
        match c {
            E::EContract::Requires(e) => requires.push(lower_expr(e)),
            E::EContract::Ensures(e) => ensures.push(lower_expr(e)),
            E::EContract::Decreases { measures, star } => {
                decreases = Some(IRDecreases {
                    measures: measures.iter().map(lower_expr).collect(),
                    star: *star,
                });
            }
        }
    }
    (requires, ensures, decreases)
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
            span: ef.span,
        });
    let (requires, ensures, decreases) = lower_contracts(&ef.contracts);
    IRFunction {
        name: ef.name.clone(),
        ty: fn_ty,
        body,
        prop_target: None,
        requires,
        ensures,
        decreases,
        span: ef.span,
        file: ef.file.clone(),
    }
}

/// Lower a pred to an `IRFunction`. `pred p(x: T) = body` becomes a curried
/// function returning Bool: `Lam(x, T, body)` with type `T -> Bool`.
fn lower_pred(ep: &E::EPred) -> IRFunction {
    let fn_ty = ep
        .params
        .iter()
        .rev()
        .fold(IRType::Bool, |acc, (_, pt)| IRType::Fn {
            param: Box::new(lower_ty(pt)),
            result: Box::new(acc),
        });
    let body = ep
        .params
        .iter()
        .rev()
        .fold(lower_expr(&ep.body), |acc, (pn, pt)| IRExpr::Lam {
            param: pn.clone(),
            param_type: lower_ty(pt),
            body: Box::new(acc),
            span: ep.span,
        });
    IRFunction {
        name: ep.name.clone(),
        ty: fn_ty,
        body,
        prop_target: None,
        requires: vec![],
        ensures: vec![],
        decreases: None,
        span: ep.span,
        file: ep.file.clone(),
    }
}

/// Lower a prop to an `IRFunction`. `prop p = body` becomes a nullary function
/// returning Bool: body is the expression, type is `Bool`.
fn lower_prop(ep: &E::EProp) -> IRFunction {
    IRFunction {
        name: ep.name.clone(),
        ty: IRType::Bool,
        body: lower_expr(&ep.body),
        prop_target: ep.target.clone(),
        requires: vec![],
        ensures: vec![],
        decreases: None,
        span: ep.span,
        file: ep.file.clone(),
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
            span: None,
        },
        [e] => lower_expr(e),
        [e, rest @ ..] => IRExpr::BinOp {
            op: "OpAnd".to_owned(),
            left: Box::new(lower_expr(e)),
            right: Box::new(lower_guard(rest)),
            ty: IRType::Bool,
            span: None,
        },
    }
}

fn extract_updates(body: &[E::EExpr]) -> Vec<IRUpdate> {
    body.iter()
        .filter_map(|e| {
            if let E::EExpr::Assign(_, lhs, rhs, _) = e {
                if let E::EExpr::Prime(_, inner, _) = lhs.as_ref() {
                    if let E::EExpr::Var(_, field, _) = inner.as_ref() {
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
        E::EExpr::Var(_, n, _) => n.clone(),
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

fn lower_verify(ev: &E::EVerify) -> IRVerify {
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
        asserts: ev.asserts.iter().map(lower_expr).collect(),
        span: ev.span,
        file: ev.file.clone(),
    }
}

fn lower_theorem(et: &E::ETheorem) -> IRTheorem {
    IRTheorem {
        name: et.name.clone(),
        systems: et.targets.clone(),
        invariants: et.invariants.iter().map(lower_expr).collect(),
        shows: et.shows.iter().map(lower_expr).collect(),
        span: et.span,
        file: et.file.clone(),
    }
}

fn lower_axiom(ea: &E::EAxiom) -> IRAxiom {
    IRAxiom {
        name: ea.name.clone(),
        body: lower_expr(&ea.body),
        span: ea.span,
        file: ea.file.clone(),
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
        span: es.span,
        file: es.file.clone(),
    }
}

fn lower_given(g: &E::ESceneGiven) -> IRSceneGiven {
    let constraint = match &g.condition {
        Some(e) => lower_expr(e),
        None => IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
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

// ── Expression lowering ──────────────────────────────────────────────

#[allow(clippy::too_many_lines)]
fn lower_expr(e: &E::EExpr) -> IRExpr {
    match e {
        E::EExpr::Lit(ty, lit, sp) => IRExpr::Lit {
            ty: lower_ty(ty),
            value: lower_lit(lit),
            span: *sp,
        },
        E::EExpr::Var(ty, n, sp) => {
            // Check if this is a constructor of an enum type
            if let E::Ty::Enum(enum_name, ctors) = ty {
                if ctors.contains(n) {
                    return IRExpr::Ctor {
                        enum_name: enum_name.clone(),
                        ctor: n.clone(),
                        span: *sp,
                    };
                }
            }
            IRExpr::Var {
                name: n.clone(),
                ty: lower_ty(ty),
                span: *sp,
            }
        }
        E::EExpr::Field(ty, expr, f, sp) => IRExpr::Field {
            expr: Box::new(lower_expr(expr)),
            field: f.clone(),
            ty: lower_ty(ty),
            span: *sp,
        },
        E::EExpr::Prime(_, expr, sp) => IRExpr::Prime {
            expr: Box::new(lower_expr(expr)),
            span: *sp,
        },
        E::EExpr::BinOp(ty, op, a, b, sp) => IRExpr::BinOp {
            op: format!("{:?}", lower_binop(*op)),
            left: Box::new(lower_expr(a)),
            right: Box::new(lower_expr(b)),
            ty: lower_ty(ty),
            span: *sp,
        },
        E::EExpr::UnOp(ty, op, expr, sp) => IRExpr::UnOp {
            op: format!("{:?}", lower_unop(*op)),
            operand: Box::new(lower_expr(expr)),
            ty: lower_ty(ty),
            span: *sp,
        },
        E::EExpr::Call(ty, f, args, sp) => {
            let lowered_f = lower_expr(f);
            let ir_ty = lower_ty(ty);
            let outer_span = *sp;
            args.iter().fold(lowered_f, |acc, arg| IRExpr::App {
                func: Box::new(acc),
                arg: Box::new(lower_expr(arg)),
                ty: ir_ty.clone(),
                span: outer_span,
            })
        }
        E::EExpr::CallR(ty, f, refs, args, sp) => {
            let lowered_f = lower_expr(f);
            let ir_ty = lower_ty(ty);
            let outer_span = *sp;
            let with_refs = refs.iter().fold(lowered_f, |acc, r| IRExpr::App {
                func: Box::new(acc),
                arg: Box::new(lower_expr(r)),
                ty: ir_ty.clone(),
                span: outer_span,
            });
            args.iter().fold(with_refs, |acc, arg| IRExpr::App {
                func: Box::new(acc),
                arg: Box::new(lower_expr(arg)),
                ty: ir_ty.clone(),
                span: outer_span,
            })
        }
        E::EExpr::Qual(ty, s, n, sp) => {
            if let E::Ty::Enum(enum_name, ctors) = ty {
                if ctors.contains(n) {
                    return IRExpr::Ctor {
                        enum_name: enum_name.clone(),
                        ctor: n.clone(),
                        span: *sp,
                    };
                }
            }
            IRExpr::Var {
                name: format!("{s}::{n}"),
                ty: lower_ty(ty),
                span: *sp,
            }
        }
        E::EExpr::Quant(_, q, v, vty, body, sp) => {
            let lowered = lower_expr(body);
            let vt = lower_ty(vty);
            match q {
                E::Quantifier::All => IRExpr::Forall {
                    var: v.clone(),
                    domain: vt,
                    body: Box::new(lowered),
                    span: *sp,
                },
                E::Quantifier::Exists
                | E::Quantifier::Some
                | E::Quantifier::One
                | E::Quantifier::Lone => IRExpr::Exists {
                    var: v.clone(),
                    domain: vt,
                    body: Box::new(lowered),
                    span: *sp,
                },
                E::Quantifier::No => IRExpr::UnOp {
                    op: "OpNot".to_owned(),
                    operand: Box::new(IRExpr::Exists {
                        var: v.clone(),
                        domain: vt,
                        body: Box::new(lowered),
                        span: *sp,
                    }),
                    ty: IRType::Bool,
                    span: *sp,
                },
            }
        }
        E::EExpr::Always(_, expr, sp) => IRExpr::Always {
            body: Box::new(lower_expr(expr)),
            span: *sp,
        },
        E::EExpr::Eventually(_, expr, sp) => IRExpr::Eventually {
            body: Box::new(lower_expr(expr)),
            span: *sp,
        },
        E::EExpr::Assert(_, expr, _) | E::EExpr::NamedPair(_, _, expr, _) => lower_expr(expr),
        E::EExpr::Assign(_, lhs, rhs, sp) => IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(lower_expr(lhs)),
            right: Box::new(lower_expr(rhs)),
            ty: IRType::Bool,
            span: *sp,
        },
        E::EExpr::Seq(ty, a, b, sp) => IRExpr::BinOp {
            op: "OpSeq".to_owned(),
            left: Box::new(lower_expr(a)),
            right: Box::new(lower_expr(b)),
            ty: lower_ty(ty),
            span: *sp,
        },
        E::EExpr::SameStep(ty, a, b, sp) => IRExpr::BinOp {
            op: "OpSameStep".to_owned(),
            left: Box::new(lower_expr(a)),
            right: Box::new(lower_expr(b)),
            ty: lower_ty(ty),
            span: *sp,
        },
        E::EExpr::Let(binds, body, sp) => {
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
                span: *sp,
            }
        }
        E::EExpr::Lam(params, _mret, body, sp) => {
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
                    span: *sp,
                })
        }
        E::EExpr::Unresolved(n, sp) => IRExpr::Var {
            name: n.clone(),
            ty: IRType::String,
            span: *sp,
        },
        E::EExpr::TupleLit(ty, es, sp) => {
            let lowered: Vec<IRExpr> = es.iter().map(lower_expr).collect();
            let tuple_ty = lower_ty(ty);
            let outer_span = *sp;
            lowered.into_iter().fold(
                IRExpr::Var {
                    name: "Tuple".to_owned(),
                    ty: tuple_ty.clone(),
                    span: outer_span,
                },
                |acc, arg| IRExpr::App {
                    func: Box::new(acc),
                    arg: Box::new(arg),
                    ty: tuple_ty.clone(),
                    span: outer_span,
                },
            )
        }
        E::EExpr::In(_ty, e, s, sp) => {
            // `e in S` → `Index(S, e)` which returns Bool (Set<T> = Array<T, Bool>)
            IRExpr::Index {
                map: Box::new(lower_expr(s)),
                key: Box::new(lower_expr(e)),
                ty: IRType::Bool,
                span: *sp,
            }
        }
        E::EExpr::Card(_ty, expr, sp) => IRExpr::Card {
            expr: Box::new(lower_expr(expr)),
            span: *sp,
        },
        E::EExpr::Pipe(ty, a, f, sp) => IRExpr::App {
            func: Box::new(lower_expr(f)),
            arg: Box::new(lower_expr(a)),
            ty: lower_ty(ty),
            span: *sp,
        },
        E::EExpr::Match(scrutinee, arms, sp) => IRExpr::Match {
            scrutinee: Box::new(lower_expr(scrutinee)),
            arms: arms
                .iter()
                .map(|(pat, guard, body)| IRMatchArm {
                    pattern: lower_pattern(pat),
                    guard: guard.as_ref().map(lower_expr),
                    body: lower_expr(body),
                })
                .collect(),
            span: *sp,
        },
        E::EExpr::MapUpdate(ty, m, k, v, sp) => IRExpr::MapUpdate {
            map: Box::new(lower_expr(m)),
            key: Box::new(lower_expr(k)),
            value: Box::new(lower_expr(v)),
            ty: lower_ty(ty),
            span: *sp,
        },
        E::EExpr::Index(ty, m, k, sp) => IRExpr::Index {
            map: Box::new(lower_expr(m)),
            key: Box::new(lower_expr(k)),
            ty: lower_ty(ty),
            span: *sp,
        },
        E::EExpr::SetComp(ty, proj, var, domain, filter, sp) => IRExpr::SetComp {
            var: var.clone(),
            domain: lower_ty(domain),
            filter: Box::new(lower_expr(filter)),
            projection: proj.as_ref().map(|p| Box::new(lower_expr(p))),
            ty: lower_ty(ty),
            span: *sp,
        },
        E::EExpr::SetLit(ty, elems, sp) => IRExpr::SetLit {
            elements: elems.iter().map(lower_expr).collect(),
            ty: lower_ty(ty),
            span: *sp,
        },
        E::EExpr::SeqLit(ty, elems, sp) => IRExpr::SeqLit {
            elements: elems.iter().map(lower_expr).collect(),
            ty: lower_ty(ty),
            span: *sp,
        },
        E::EExpr::MapLit(ty, entries, sp) => IRExpr::MapLit {
            entries: entries
                .iter()
                .map(|(k, v)| (lower_expr(k), lower_expr(v)))
                .collect(),
            ty: lower_ty(ty),
            span: *sp,
        },
        E::EExpr::Sorry(sp) => IRExpr::Sorry { span: *sp },
        E::EExpr::Todo(sp) => IRExpr::Todo { span: *sp },
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::span::Span;

    #[test]
    fn lower_expr_propagates_span() {
        let sp = Span { start: 10, end: 20 };
        let expr = E::EExpr::Lit(
            E::Ty::Builtin(E::BuiltinTy::Int),
            E::Literal::Int(42),
            Some(sp),
        );
        let ir = lower_expr(&expr);
        match ir {
            IRExpr::Lit { span, .. } => assert_eq!(span, Some(sp)),
            other => panic!("expected Lit, got {other:?}"),
        }
    }

    #[test]
    fn lower_expr_propagates_none_span() {
        let expr = E::EExpr::Lit(
            E::Ty::Builtin(E::BuiltinTy::Bool),
            E::Literal::Bool(true),
            None,
        );
        let ir = lower_expr(&expr);
        match ir {
            IRExpr::Lit { span, .. } => assert_eq!(span, None),
            other => panic!("expected Lit, got {other:?}"),
        }
    }

    #[test]
    fn lower_expr_binop_propagates_span() {
        let sp = Span { start: 5, end: 15 };
        let a = E::EExpr::Lit(E::Ty::Builtin(E::BuiltinTy::Int), E::Literal::Int(1), None);
        let b = E::EExpr::Lit(E::Ty::Builtin(E::BuiltinTy::Int), E::Literal::Int(2), None);
        let expr = E::EExpr::BinOp(
            E::Ty::Builtin(E::BuiltinTy::Int),
            E::BinOp::Add,
            Box::new(a),
            Box::new(b),
            Some(sp),
        );
        let ir = lower_expr(&expr);
        match ir {
            IRExpr::BinOp { span, .. } => assert_eq!(span, Some(sp)),
            other => panic!("expected BinOp, got {other:?}"),
        }
    }

    #[test]
    fn lower_verify_propagates_span_and_file() {
        let sp = Span {
            start: 100,
            end: 200,
        };
        let ev = E::EVerify {
            name: "test".to_owned(),
            targets: vec![("Sys".to_owned(), 0, 10)],
            asserts: vec![E::EExpr::Lit(
                E::Ty::Builtin(E::BuiltinTy::Bool),
                E::Literal::Bool(true),
                None,
            )],
            span: Some(sp),
            file: Some("/test.abide".to_owned()),
        };
        let ir = lower_verify(&ev);
        assert_eq!(ir.span, Some(sp));
        assert_eq!(ir.file.as_deref(), Some("/test.abide"));
    }

    #[test]
    fn lower_theorem_propagates_span_and_file() {
        let sp = Span { start: 50, end: 80 };
        let et = E::ETheorem {
            name: "thm".to_owned(),
            targets: vec!["Sys".to_owned()],
            invariants: vec![],
            shows: vec![E::EExpr::Lit(
                E::Ty::Builtin(E::BuiltinTy::Bool),
                E::Literal::Bool(true),
                None,
            )],
            span: Some(sp),
            file: Some("/proof.abide".to_owned()),
        };
        let ir = lower_theorem(&et);
        assert_eq!(ir.span, Some(sp));
        assert_eq!(ir.file.as_deref(), Some("/proof.abide"));
    }

    #[test]
    fn lower_scene_propagates_span_and_file() {
        let sp = Span { start: 30, end: 60 };
        let es = E::EScene {
            name: "sc".to_owned(),
            targets: vec!["Sys".to_owned()],
            givens: vec![],
            whens: vec![],
            thens: vec![],
            span: Some(sp),
            file: Some("/scene.abide".to_owned()),
        };
        let ir = lower_scene(&es);
        assert_eq!(ir.span, Some(sp));
        assert_eq!(ir.file.as_deref(), Some("/scene.abide"));
    }

    #[test]
    fn lower_axiom_propagates_span_and_file() {
        let sp = Span { start: 0, end: 25 };
        let ea = E::EAxiom {
            name: "ax".to_owned(),
            body: E::EExpr::Lit(
                E::Ty::Builtin(E::BuiltinTy::Bool),
                E::Literal::Bool(true),
                None,
            ),
            span: Some(sp),
            file: Some("/ax.abide".to_owned()),
        };
        let ir = lower_axiom(&ea);
        assert_eq!(ir.span, Some(sp));
        assert_eq!(ir.file.as_deref(), Some("/ax.abide"));
    }

    #[test]
    fn lower_fn_propagates_file() {
        let sp = Span { start: 10, end: 40 };
        let ef = E::EFn {
            name: "f".to_owned(),
            params: vec![("x".to_owned(), E::Ty::Builtin(E::BuiltinTy::Int))],
            ret_ty: E::Ty::Builtin(E::BuiltinTy::Int),
            contracts: vec![],
            body: E::EExpr::Var(E::Ty::Builtin(E::BuiltinTy::Int), "x".to_owned(), None),
            span: Some(sp),
            file: Some("/fn.abide".to_owned()),
        };
        let ir = lower_fn(&ef);
        assert_eq!(ir.span, Some(sp));
        assert_eq!(ir.file.as_deref(), Some("/fn.abide"));
    }

    #[test]
    fn lower_pred_propagates_file() {
        let sp = Span { start: 20, end: 50 };
        let ep = E::EPred {
            name: "p".to_owned(),
            params: vec![("x".to_owned(), E::Ty::Builtin(E::BuiltinTy::Int))],
            body: E::EExpr::Lit(
                E::Ty::Builtin(E::BuiltinTy::Bool),
                E::Literal::Bool(true),
                None,
            ),
            span: Some(sp),
            file: Some("/pred.abide".to_owned()),
        };
        let ir = lower_pred(&ep);
        assert_eq!(ir.span, Some(sp));
        assert_eq!(ir.file.as_deref(), Some("/pred.abide"));
    }

    #[test]
    fn lower_prop_propagates_file() {
        let sp = Span { start: 30, end: 70 };
        let ep = E::EProp {
            name: "safe".to_owned(),
            target: Some("Sys".to_owned()),
            body: E::EExpr::Lit(
                E::Ty::Builtin(E::BuiltinTy::Bool),
                E::Literal::Bool(true),
                None,
            ),
            span: Some(sp),
            file: Some("/prop.abide".to_owned()),
        };
        let ir = lower_prop(&ep);
        assert_eq!(ir.span, Some(sp));
        assert_eq!(ir.file.as_deref(), Some("/prop.abide"));
    }
}
