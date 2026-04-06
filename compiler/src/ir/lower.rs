//! Lower elaborated AST to Core IR.
//!
//! Desugars, resolves primed variables, computes frame conditions,
//! and produces a flat `IRProgram`.

use crate::elab::types as E;

use super::types::{
    Cardinality, IRAction, IRAxiom, IRConst, IRCreateField, IRDecreases, IREntity, IREvent, IRExpr,
    IRField, IRFieldPat, IRFunction, IRLemma, IRMatchArm, IRPattern, IRProgram, IRRecordField, IRScene,
    IRSceneEvent, IRSceneGiven, IRSchedWhen, IRSchedule, IRSystem, IRTheorem, IRTransParam,
    IRTransRef, IRTransition, IRType, IRTypeEntry, IRUpdate, IRVerify, IRVerifySystem, LetBinding,
    LitVal,
};

/// Unwrap `Ty::Alias` wrappers to get to the underlying type.
///
/// `Alias("Positive", Refinement(Int, pred))` → `Refinement(Int, pred)`
/// This is needed because type aliases like `type Positive = Int { $ > 0 }`
/// are stored as `Alias("Positive", Refinement(...))`, and the lowering
/// needs to see the `Refinement` to extract `requires` clauses.
fn unwrap_alias(ty: &E::Ty) -> &E::Ty {
    let mut current = ty;
    while let E::Ty::Alias(_, inner) = current {
        current = inner;
    }
    current
}

// ── Top-level lowering ───────────────────────────────────────────────

/// Resolve an alias to its canonical name, or return the name as-is.
fn canonical<'a>(aliases: &'a std::collections::HashMap<String, String>, name: &'a str) -> &'a str {
    aliases.get(name).map_or(name, String::as_str)
}

pub fn lower(er: &E::ElabResult) -> IRProgram {
    let a = &er.aliases;

    // Build variant info map from elaborated types so that lower_ty can
    // carry constructor field information into IRType::Enum.
    let variant_info: std::collections::HashMap<String, &[E::EVariant]> = er
        .types
        .iter()
        .map(|t| (t.name.clone(), t.variants.as_slice()))
        .collect();

    // All definitions (fn, pred, prop) are lowered uniformly into IRFunction.
    // pred is fn -> Bool with params. prop is nullary fn -> Bool.
    let mut functions: Vec<IRFunction> = Vec::new();
    for f in &er.fns {
        functions.push(lower_fn(f, &variant_info));
    }
    for pred in &er.preds {
        functions.push(lower_pred(pred, &variant_info));
    }
    for prop in &er.props {
        functions.push(lower_prop(prop, &variant_info));
    }

    IRProgram {
        types: er.types.iter().map(|t| lower_type(t, &variant_info)).collect(),
        constants: er.consts.iter().map(|c| lower_const(c, &variant_info)).collect(),
        functions,
        entities: er.entities.iter().map(|e| lower_entity(e, &variant_info)).collect(),
        systems: er.systems.iter().map(|s| lower_system(s, a, &variant_info)).collect(),
        verifies: er.verifies.iter().map(|v| lower_verify(v, a, &variant_info)).collect(),
        theorems: er.theorems.iter().map(|t| lower_theorem(t, a, &variant_info)).collect(),
        axioms: er.axioms.iter().map(|ax| lower_axiom(ax, &variant_info)).collect(),
        lemmas: er.lemmas.iter().map(|l| lower_lemma(l, &variant_info)).collect(),
        scenes: er.scenes.iter().map(|s| lower_scene(s, a, &variant_info)).collect(),
    }
}

// ── Types ────────────────────────────────────────────────────────────

type VariantInfo<'a> = std::collections::HashMap<String, &'a [E::EVariant]>;

fn lower_type(et: &E::EType, vi: &VariantInfo<'_>) -> IRTypeEntry {
    IRTypeEntry {
        name: et.name.clone(),
        ty: lower_ty(&et.ty, vi),
    }
}

fn lower_ty(ty: &E::Ty, vi: &VariantInfo<'_>) -> IRType {
    match ty {
        E::Ty::Enum(n, cs) => {
            // Look up field info from the elab variant map
            let variants = if let Some(elab_variants) = vi.get(n.as_str()) {
                elab_variants
                    .iter()
                    .map(|ev| match ev {
                        E::EVariant::Simple(name) => super::types::IRVariant::simple(name),
                        E::EVariant::Record(name, fields) => super::types::IRVariant {
                            name: name.clone(),
                            fields: fields
                                .iter()
                                .map(|(fname, fty)| super::types::IRVariantField {
                                    name: fname.clone(),
                                    ty: lower_ty(fty, vi),
                                })
                                .collect(),
                        },
                        E::EVariant::Param(name, _tys) => super::types::IRVariant::simple(name),
                    })
                    .collect()
            } else {
                // Fallback: no elab info, treat all constructors as fieldless
                cs.iter()
                    .map(|c| super::types::IRVariant::simple(c))
                    .collect()
            };
            IRType::Enum {
                name: n.clone(),
                variants,
            }
        }
        E::Ty::Record(n, fs) => IRType::Record {
            name: n.clone(),
            fields: fs
                .iter()
                .map(|(fn_, ft)| IRRecordField {
                    name: fn_.clone(),
                    ty: lower_ty(ft, vi),
                })
                .collect(),
        },
        E::Ty::Alias(_, t) => lower_ty(t, vi),
        E::Ty::Builtin(b) => lower_builtin(*b),
        E::Ty::Param(n, _) => IRType::Record {
            name: n.clone(),
            fields: Vec::new(),
        },
        E::Ty::Fn(a, b) => IRType::Fn {
            param: Box::new(lower_ty(a, vi)),
            result: Box::new(lower_ty(b, vi)),
        },
        E::Ty::Entity(n) => IRType::Entity { name: n.clone() },
        E::Ty::Unresolved(_) => IRType::String,
        E::Ty::Set(a) => IRType::Set {
            element: Box::new(lower_ty(a, vi)),
        },
        E::Ty::Seq(a) => IRType::Seq {
            element: Box::new(lower_ty(a, vi)),
        },
        E::Ty::Map(k, v) => IRType::Map {
            key: Box::new(lower_ty(k, vi)),
            value: Box::new(lower_ty(v, vi)),
        },
        E::Ty::Tuple(ts) => IRType::Tuple {
            elements: ts.iter().map(|t| lower_ty(t, vi)).collect(),
        },
        E::Ty::Refinement(base, pred) => IRType::Refinement {
            base: Box::new(lower_ty(base, vi)),
            predicate: Box::new(lower_expr(pred, vi)),
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

fn lower_const(ec: &E::EConst, vi: &VariantInfo<'_>) -> IRConst {
    IRConst {
        name: ec.name.clone(),
        ty: lower_ty(&ec.body.ty(), vi),
        value: lower_expr(&ec.body, vi),
    }
}

fn lower_contracts(contracts: &[E::EContract], vi: &VariantInfo<'_>) -> (Vec<IRExpr>, Vec<IRExpr>, Option<IRDecreases>) {
    let mut requires = Vec::new();
    let mut ensures = Vec::new();
    let mut decreases = None;
    for c in contracts {
        match c {
            E::EContract::Requires(e) => requires.push(lower_expr(e, vi)),
            E::EContract::Ensures(e) => ensures.push(lower_expr(e, vi)),
            E::EContract::Decreases { measures, star } => {
                decreases = Some(IRDecreases {
                    measures: measures.iter().map(|m| lower_expr(m, vi)).collect(),
                    star: *star,
                });
            }
            E::EContract::Invariant(_) => {
                // Invariant contracts are handled separately (while loops)
            }
        }
    }
    (requires, ensures, decreases)
}

/// Extract invariants and decreases from while-loop contracts.
fn lower_while_contracts(contracts: &[E::EContract], vi: &VariantInfo<'_>) -> (Vec<IRExpr>, Option<IRDecreases>) {
    let mut invariants = Vec::new();
    let mut decreases = None;
    for c in contracts {
        match c {
            E::EContract::Invariant(e) => invariants.push(lower_expr(e, vi)),
            E::EContract::Decreases { measures, star } => {
                decreases = Some(IRDecreases {
                    measures: measures.iter().map(|m| lower_expr(m, vi)).collect(),
                    star: *star,
                });
            }
            _ => {}
        }
    }
    (invariants, decreases)
}

fn lower_fn(ef: &E::EFn, vi: &VariantInfo<'_>) -> IRFunction {
    // Extract refinement predicates from params, strip refinement from types.
    // Unwrap Alias wrappers so that alias-based refinements like `x: Positive`
    // (where `type Positive = Int { $ > 0 }`) are handled the same as inline
    // refinements like `x: Int { $ > 0 }`.
    let stripped_params: Vec<(String, E::Ty)> = ef
        .params
        .iter()
        .map(|(n, t)| match unwrap_alias(t) {
            E::Ty::Refinement(base, _) => (n.clone(), (**base).clone()),
            _ => (n.clone(), t.clone()),
        })
        .collect();
    let refinement_requires: Vec<IRExpr> = ef
        .params
        .iter()
        .filter_map(|(name, ty)| {
            if let E::Ty::Refinement(_, pred) = unwrap_alias(ty) {
                Some(subst_dollar(name, &lower_expr(pred, vi)))
            } else {
                None
            }
        })
        .collect();
    let ret_ty = lower_ty(&ef.ret_ty, vi);
    let fn_ty = stripped_params
        .iter()
        .rev()
        .fold(ret_ty.clone(), |acc, (_, pt)| IRType::Fn {
            param: Box::new(lower_ty(pt, vi)),
            result: Box::new(acc),
        });
    let body = stripped_params
        .iter()
        .rev()
        .fold(lower_expr(&ef.body, vi), |acc, (pn, pt)| IRExpr::Lam {
            param: pn.clone(),
            param_type: lower_ty(pt, vi),
            body: Box::new(acc),
            span: ef.span,
        });
    let (mut requires, ensures, decreases) = lower_contracts(&ef.contracts, vi);
    // Prepend refinement-derived requires before explicit contracts
    let mut all_requires = refinement_requires;
    all_requires.append(&mut requires);
    IRFunction {
        name: ef.name.clone(),
        ty: fn_ty,
        body,
        prop_target: None,
        requires: all_requires,
        ensures,
        decreases,
        span: ef.span,
        file: ef.file.clone(),
    }
}

/// Substitute `$` with a parameter name in an IR expression.
fn subst_dollar(name: &str, expr: &IRExpr) -> IRExpr {
    match expr {
        IRExpr::Var {
            name: n, ty, span, ..
        } if n == "$" => IRExpr::Var {
            name: name.to_owned(),
            ty: ty.clone(),
            span: *span,
        },
        IRExpr::BinOp {
            op,
            left,
            right,
            ty,
            span,
        } => IRExpr::BinOp {
            op: op.clone(),
            left: Box::new(subst_dollar(name, left)),
            right: Box::new(subst_dollar(name, right)),
            ty: ty.clone(),
            span: *span,
        },
        IRExpr::UnOp {
            op,
            operand,
            ty,
            span,
        } => IRExpr::UnOp {
            op: op.clone(),
            operand: Box::new(subst_dollar(name, operand)),
            ty: ty.clone(),
            span: *span,
        },
        IRExpr::App {
            func,
            arg,
            ty,
            span,
        } => IRExpr::App {
            func: Box::new(subst_dollar(name, func)),
            arg: Box::new(subst_dollar(name, arg)),
            ty: ty.clone(),
            span: *span,
        },
        IRExpr::Field {
            expr: e,
            field,
            ty,
            span,
        } => IRExpr::Field {
            expr: Box::new(subst_dollar(name, e)),
            field: field.clone(),
            ty: ty.clone(),
            span: *span,
        },
        IRExpr::Forall {
            var,
            domain,
            body,
            span,
        } if var != "$" => IRExpr::Forall {
            var: var.clone(),
            domain: domain.clone(),
            body: Box::new(subst_dollar(name, body)),
            span: *span,
        },
        IRExpr::Exists {
            var,
            domain,
            body,
            span,
        } if var != "$" => IRExpr::Exists {
            var: var.clone(),
            domain: domain.clone(),
            body: Box::new(subst_dollar(name, body)),
            span: *span,
        },
        _ => expr.clone(),
    }
}

/// Lower a pred to an `IRFunction`. `pred p(x: T) = body` becomes a curried
/// function returning Bool: `Lam(x, T, body)` with type `T -> Bool`.
fn lower_pred(ep: &E::EPred, vi: &VariantInfo<'_>) -> IRFunction {
    let fn_ty = ep
        .params
        .iter()
        .rev()
        .fold(IRType::Bool, |acc, (_, pt)| IRType::Fn {
            param: Box::new(lower_ty(pt, vi)),
            result: Box::new(acc),
        });
    let body = ep
        .params
        .iter()
        .rev()
        .fold(lower_expr(&ep.body, vi), |acc, (pn, pt)| IRExpr::Lam {
            param: pn.clone(),
            param_type: lower_ty(pt, vi),
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
fn lower_prop(ep: &E::EProp, vi: &VariantInfo<'_>) -> IRFunction {
    IRFunction {
        name: ep.name.clone(),
        ty: IRType::Bool,
        body: lower_expr(&ep.body, vi),
        prop_target: ep.target.clone(),
        requires: vec![],
        ensures: vec![],
        decreases: None,
        span: ep.span,
        file: ep.file.clone(),
    }
}

// ── Entities ─────────────────────────────────────────────────────────

fn lower_entity(ee: &E::EEntity, vi: &VariantInfo<'_>) -> IREntity {
    IREntity {
        name: ee.name.clone(),
        fields: ee.fields.iter().map(|f| lower_field(f, vi)).collect(),
        transitions: ee.actions.iter().map(|a| lower_action(a, vi)).collect(),
    }
}

fn lower_field(ef: &E::EField, vi: &VariantInfo<'_>) -> IRField {
    use crate::elab::types::EFieldDefault;
    let (default, initial_constraint) = match &ef.default {
        Some(EFieldDefault::Value(e)) => (Some(lower_expr(e, vi)), None),
        Some(EFieldDefault::In(es)) => {
            // default = None: nondeterministic, so induction/IC3 treat as unconstrained
            // (stronger: proves safety for ALL possible initial values)
            // constraint = $ == a || $ == b || ...
            let dollar_var = IRExpr::Var {
                name: "$".to_owned(),
                ty: lower_ty(&ef.ty, vi),
                span: None,
            };
            let mut disj: Option<IRExpr> = None;
            for e in es {
                let eq = IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(dollar_var.clone()),
                    right: Box::new(lower_expr(e, vi)),
                    ty: crate::ir::types::IRType::Bool,
                    span: None,
                };
                disj = Some(match disj {
                    None => eq,
                    Some(prev) => IRExpr::BinOp {
                        op: "OpOr".to_owned(),
                        left: Box::new(prev),
                        right: Box::new(eq),
                        ty: crate::ir::types::IRType::Bool,
                        span: None,
                    },
                });
            }
            (None, disj)
        }
        Some(EFieldDefault::Where(e)) => (None, Some(lower_expr(e, vi))),
        None => (None, None),
    };
    IRField {
        name: ef.name.clone(),
        ty: lower_ty(&ef.ty, vi),
        default,
        initial_constraint,
    }
}

fn lower_action(ea: &E::EAction, vi: &VariantInfo<'_>) -> IRTransition {
    // Extract refinement predicates from params and add to guard
    let refinement_reqs = extract_param_refinements(&ea.params);
    let mut all_requires: Vec<&E::EExpr> = refinement_reqs.iter().collect();
    all_requires.extend(ea.requires.iter());
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
            .map(|(pn, pt)| {
                let base_ty = match unwrap_alias(pt) {
                    E::Ty::Refinement(base, _) => base.as_ref(),
                    _ => pt,
                };
                IRTransParam {
                    name: pn.clone(),
                    ty: lower_ty(base_ty, vi),
                }
            })
            .collect(),
        guard: lower_guard_refs(&all_requires, vi),
        updates: extract_updates(&ea.body, vi),
        postcondition: if ea.ensures.is_empty() {
            None
        } else {
            Some(lower_guard_refs(&ea.ensures.iter().collect::<Vec<_>>(), vi))
        },
    }
}

/// Extract refinement predicates from params, substituting $ with param name.
fn extract_param_refinements(params: &[(String, E::Ty)]) -> Vec<E::EExpr> {
    params
        .iter()
        .filter_map(|(name, ty)| {
            if let E::Ty::Refinement(_, pred) = unwrap_alias(ty) {
                Some(subst_dollar_elab(name, pred))
            } else {
                None
            }
        })
        .collect()
}

/// Substitute $ with a parameter name in an elaborated expression.
fn subst_dollar_elab(name: &str, expr: &E::EExpr) -> E::EExpr {
    match expr {
        E::EExpr::Var(ty, n, sp) if n == "$" => E::EExpr::Var(ty.clone(), name.to_owned(), *sp),
        E::EExpr::BinOp(ty, op, a, b, sp) => E::EExpr::BinOp(
            ty.clone(),
            *op,
            Box::new(subst_dollar_elab(name, a)),
            Box::new(subst_dollar_elab(name, b)),
            *sp,
        ),
        E::EExpr::UnOp(ty, op, e, sp) => {
            E::EExpr::UnOp(ty.clone(), *op, Box::new(subst_dollar_elab(name, e)), *sp)
        }
        _ => expr.clone(),
    }
}

/// Lower a list of expression references (not owned) to a conjunction guard.
fn lower_guard_refs(reqs: &[&E::EExpr], vi: &VariantInfo<'_>) -> IRExpr {
    match reqs {
        [] => IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        },
        [e] => lower_expr(e, vi),
        [e, rest @ ..] => IRExpr::BinOp {
            op: "OpAnd".to_owned(),
            left: Box::new(lower_expr(e, vi)),
            right: Box::new(lower_guard_refs(rest, vi)),
            ty: IRType::Bool,
            span: None,
        },
    }
}

fn lower_guard(reqs: &[E::EExpr], vi: &VariantInfo<'_>) -> IRExpr {
    match reqs {
        [] => IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        },
        [e] => lower_expr(e, vi),
        [e, rest @ ..] => IRExpr::BinOp {
            op: "OpAnd".to_owned(),
            left: Box::new(lower_expr(e, vi)),
            right: Box::new(lower_guard(rest, vi)),
            ty: IRType::Bool,
            span: None,
        },
    }
}

fn extract_updates(body: &[E::EExpr], vi: &VariantInfo<'_>) -> Vec<IRUpdate> {
    body.iter()
        .filter_map(|e| {
            if let E::EExpr::Assign(_, lhs, rhs, _) = e {
                if let E::EExpr::Prime(_, inner, _) = lhs.as_ref() {
                    if let E::EExpr::Var(_, field, _) = inner.as_ref() {
                        return Some(IRUpdate {
                            field: field.clone(),
                            value: lower_expr(rhs, vi),
                        });
                    }
                }
            }
            None
        })
        .collect()
}

// ── Systems ──────────────────────────────────────────────────────────

fn lower_system(es: &E::ESystem, aliases: &std::collections::HashMap<String, String>, vi: &VariantInfo<'_>) -> IRSystem {
    IRSystem {
        name: es.name.clone(),
        entities: es.uses.iter().map(|u| canonical(aliases, u).to_owned()).collect(),
        events: es.events.iter().map(|ev| lower_event(ev, aliases, vi)).collect(),
        schedule: lower_schedule(&es.next_items, vi),
    }
}

fn lower_event(ev: &E::EEvent, aliases: &std::collections::HashMap<String, String>, vi: &VariantInfo<'_>) -> IREvent {
    let post = if ev.ensures.is_empty() {
        None
    } else {
        Some(lower_guard(&ev.ensures, vi))
    };
    // Extract refinement predicates from params and add to guard
    let refinement_reqs = extract_param_refinements(&ev.params);
    let mut all_requires: Vec<&E::EExpr> = refinement_reqs.iter().collect();
    all_requires.extend(ev.requires.iter());
    IREvent {
        name: ev.name.clone(),
        fairness: match ev.fairness {
            crate::ast::Fairness::None => crate::ir::types::IRFairness::None,
            crate::ast::Fairness::Weak => crate::ir::types::IRFairness::Weak,
            crate::ast::Fairness::Strong => crate::ir::types::IRFairness::Strong,
        },
        params: ev
            .params
            .iter()
            .map(|(pn, pt)| {
                let base_ty = match unwrap_alias(pt) {
                    E::Ty::Refinement(base, _) => base.as_ref(),
                    _ => pt,
                };
                IRTransParam {
                    name: pn.clone(),
                    ty: lower_ty(base_ty, vi),
                }
            })
            .collect(),
        guard: lower_guard_refs(&all_requires, vi),
        postcondition: post,
        body: ev.body.iter().map(|a| lower_event_action(a, aliases, vi)).collect(),
    }
}

fn lower_event_action(
    ea: &E::EEventAction,
    aliases: &std::collections::HashMap<String, String>,
    vi: &VariantInfo<'_>,
) -> IRAction {
    match ea {
        E::EEventAction::Choose(v, ty, guard, body) => IRAction::Choose {
            var: v.clone(),
            entity: ty.name().to_owned(),
            filter: Box::new(lower_expr(guard, vi)),
            ops: body.iter().map(|a| lower_event_action(a, aliases, vi)).collect(),
        },
        E::EEventAction::ForAll(v, ty, body) => IRAction::ForAll {
            var: v.clone(),
            entity: ty.name().to_owned(),
            ops: body.iter().map(|a| lower_event_action(a, aliases, vi)).collect(),
        },
        E::EEventAction::Create(entity, fields) => IRAction::Create {
            entity: canonical(aliases, entity).to_owned(),
            fields: fields
                .iter()
                .map(|(fn_, fe)| IRCreateField {
                    name: fn_.clone(),
                    value: lower_expr(fe, vi),
                })
                .collect(),
        },
        E::EEventAction::CrossCall(sys, ev, args) => IRAction::CrossCall {
            system: canonical(aliases, sys).to_owned(),
            event: ev.clone(),
            args: args.iter().map(|a| lower_expr(a, vi)).collect(),
        },
        E::EEventAction::Apply(target, act, refs, args) => IRAction::Apply {
            target: extract_target_name(target),
            transition: act.clone(),
            refs: refs.iter().map(extract_target_name).collect(),
            args: args.iter().map(|a| lower_expr(a, vi)).collect(),
        },
        E::EEventAction::Expr(e) => IRAction::ExprStmt {
            expr: lower_expr(e, vi),
        },
    }
}

fn extract_target_name(e: &E::EExpr) -> String {
    match e {
        E::EExpr::Var(_, n, _) => n.clone(),
        _ => "_".to_owned(),
    }
}

fn lower_schedule(items: &[E::ENextItem], vi: &VariantInfo<'_>) -> IRSchedule {
    let when = items
        .iter()
        .filter_map(|ni| match ni {
            E::ENextItem::When(cond, ev_name) => Some(IRSchedWhen {
                condition: lower_expr(cond, vi),
                event: ev_name.clone(),
            }),
            E::ENextItem::Else => None,
        })
        .collect();
    let idle = items.iter().any(|ni| matches!(ni, E::ENextItem::Else));
    IRSchedule { when, idle }
}

// ── Verification ─────────────────────────────────────────────────────

fn lower_verify(ev: &E::EVerify, aliases: &std::collections::HashMap<String, String>, vi: &VariantInfo<'_>) -> IRVerify {
    IRVerify {
        name: ev.name.clone(),
        systems: ev
            .targets
            .iter()
            .map(|(n, lo, hi)| IRVerifySystem {
                name: canonical(aliases, n).to_owned(),
                lo: *lo,
                hi: *hi,
            })
            .collect(),
        asserts: ev.asserts.iter().map(|e| lower_expr(e, vi)).collect(),
        span: ev.span,
        file: ev.file.clone(),
    }
}

fn lower_theorem(et: &E::ETheorem, aliases: &std::collections::HashMap<String, String>, vi: &VariantInfo<'_>) -> IRTheorem {
    IRTheorem {
        name: et.name.clone(),
        systems: et.targets.iter().map(|t| canonical(aliases, t).to_owned()).collect(),
        invariants: et.invariants.iter().map(|e| lower_expr(e, vi)).collect(),
        shows: et.shows.iter().map(|e| lower_expr(e, vi)).collect(),
        span: et.span,
        file: et.file.clone(),
    }
}

fn lower_axiom(ea: &E::EAxiom, vi: &VariantInfo<'_>) -> IRAxiom {
    IRAxiom {
        name: ea.name.clone(),
        body: lower_expr(&ea.body, vi),
        span: ea.span,
        file: ea.file.clone(),
    }
}

fn lower_lemma(el: &E::ELemma, vi: &VariantInfo<'_>) -> IRLemma {
    IRLemma {
        name: el.name.clone(),
        body: el.body.iter().map(|e| lower_expr(e, vi)).collect(),
        span: el.span,
        file: el.file.clone(),
    }
}

fn lower_scene(es: &E::EScene, aliases: &std::collections::HashMap<String, String>, vi: &VariantInfo<'_>) -> IRScene {
    let (actions, assumes): (Vec<_>, Vec<_>) = es
        .whens
        .iter()
        .partition(|w| !matches!(w, E::ESceneWhen::Assume(_)));

    IRScene {
        name: es.name.clone(),
        systems: es.targets.iter().map(|t| canonical(aliases, t).to_owned()).collect(),
        givens: es.givens.iter().map(|g| lower_given(g, aliases, vi)).collect(),
        events: actions.iter().map(|w| lower_scene_action(w, aliases, vi)).collect(),
        ordering: assumes
            .iter()
            .filter_map(|w| match w {
                E::ESceneWhen::Assume(e) => Some(lower_expr(e, vi)),
                E::ESceneWhen::Action { .. } => None,
            })
            .collect(),
        assertions: es.thens.iter().map(|e| lower_expr(e, vi)).collect(),
        span: es.span,
        file: es.file.clone(),
    }
}

fn lower_given(g: &E::ESceneGiven, aliases: &std::collections::HashMap<String, String>, vi: &VariantInfo<'_>) -> IRSceneGiven {
    let constraint = match &g.condition {
        Some(e) => lower_expr(e, vi),
        None => IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        },
    };
    IRSceneGiven {
        var: g.var.clone(),
        entity: canonical(aliases, &g.entity_type).to_owned(),
        constraint,
    }
}

fn lower_scene_action(w: &E::ESceneWhen, aliases: &std::collections::HashMap<String, String>, vi: &VariantInfo<'_>) -> IRSceneEvent {
    match w {
        E::ESceneWhen::Action {
            var,
            system,
            event,
            args,
            card,
        } => IRSceneEvent {
            var: var.clone(),
            system: canonical(aliases, system).to_owned(),
            event: event.clone(),
            args: args.iter().map(|a| lower_expr(a, vi)).collect(),
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

fn capitalize(s: &str) -> String {
    let mut c = s.chars();
    match c.next() {
        None => String::new(),
        Some(f) => f.to_uppercase().to_string() + c.as_str(),
    }
}

#[allow(clippy::too_many_lines)]
fn lower_expr(e: &E::EExpr, vi: &VariantInfo<'_>) -> IRExpr {
    match e {
        E::EExpr::Lit(ty, lit, sp) => IRExpr::Lit {
            ty: lower_ty(ty, vi),
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
                        args: vec![],
                        span: *sp,
                    };
                }
            }
            IRExpr::Var {
                name: n.clone(),
                ty: lower_ty(ty, vi),
                span: *sp,
            }
        }
        E::EExpr::Field(ty, expr, f, sp) => IRExpr::Field {
            expr: Box::new(lower_expr(expr, vi)),
            field: f.clone(),
            ty: lower_ty(ty, vi),
            span: *sp,
        },
        E::EExpr::Prime(_, expr, sp) => IRExpr::Prime {
            expr: Box::new(lower_expr(expr, vi)),
            span: *sp,
        },
        E::EExpr::BinOp(ty, op, a, b, sp) => {
            // Type-directed operator overloading: when both operands have
            // Set type, override arithmetic ops to set ops. This is done HERE
            // (not in the SMT layer) because the elaborated types distinguish
            // Set<T> from Map<K,Bool> and Seq<Bool>, which are all Array<_,Bool>
            // at the SMT level.
            let resolved_op = match (op, a.ty(), b.ty()) {
                (E::BinOp::Mul, E::Ty::Set(_), E::Ty::Set(_)) => "OpSetIntersect".to_owned(),
                (E::BinOp::Sub, E::Ty::Set(_), E::Ty::Set(_)) => "OpSetDiff".to_owned(),
                (E::BinOp::Le, E::Ty::Set(_), E::Ty::Set(_)) => "OpSetSubset".to_owned(),
                (E::BinOp::Add, E::Ty::Set(_), E::Ty::Set(_)) => "OpSetUnion".to_owned(),
                _ => format!("{:?}", lower_binop(*op)),
            };
            IRExpr::BinOp {
                op: resolved_op,
                left: Box::new(lower_expr(a, vi)),
                right: Box::new(lower_expr(b, vi)),
                ty: lower_ty(ty, vi),
                span: *sp,
            }
        }
        E::EExpr::UnOp(ty, op, expr, sp) => IRExpr::UnOp {
            op: format!("{:?}", lower_unop(*op)),
            operand: Box::new(lower_expr(expr, vi)),
            ty: lower_ty(ty, vi),
            span: *sp,
        },
        E::EExpr::Call(ty, f, args, sp) => {
            let lowered_f = lower_expr(f, vi);
            let ir_ty = lower_ty(ty, vi);
            let outer_span = *sp;
            args.iter().fold(lowered_f, |acc, arg| IRExpr::App {
                func: Box::new(acc),
                arg: Box::new(lower_expr(arg, vi)),
                ty: ir_ty.clone(),
                span: outer_span,
            })
        }
        E::EExpr::CallR(ty, f, refs, args, sp) => {
            let lowered_f = lower_expr(f, vi);
            let ir_ty = lower_ty(ty, vi);
            let outer_span = *sp;
            let with_refs = refs.iter().fold(lowered_f, |acc, r| IRExpr::App {
                func: Box::new(acc),
                arg: Box::new(lower_expr(r, vi)),
                ty: ir_ty.clone(),
                span: outer_span,
            });
            args.iter().fold(with_refs, |acc, arg| IRExpr::App {
                func: Box::new(acc),
                arg: Box::new(lower_expr(arg, vi)),
                ty: ir_ty.clone(),
                span: outer_span,
            })
        }
        E::EExpr::QualCall(ty, type_name, func_name, args, sp) => {
            let op = format!("Op{type_name}{}", capitalize(func_name));
            let lowered_args: Vec<IRExpr> = args.iter().map(|a| lower_expr(a, vi)).collect();
            match lowered_args.len() {
                1 => IRExpr::UnOp {
                    op,
                    operand: Box::new(lowered_args.into_iter().next().unwrap()),
                    ty: lower_ty(ty, vi),
                    span: *sp,
                },
                2 => {
                    let mut iter = lowered_args.into_iter();
                    IRExpr::BinOp {
                        op,
                        left: Box::new(iter.next().unwrap()),
                        right: Box::new(iter.next().unwrap()),
                        ty: lower_ty(ty, vi),
                        span: *sp,
                    }
                }
                0 | 3.. => {
                    // Emit the qualified call name as a Var so the verifier
                    // reports a clear error rather than silently mislowering.
                    IRExpr::Var {
                        name: format!(
                            "{}",
                            crate::messages::collection_op_unsupported_arity(
                                type_name,
                                func_name,
                                lowered_args.len(),
                            )
                        ),
                        ty: lower_ty(ty, vi),
                        span: *sp,
                    }
                }
            }
        }
        E::EExpr::Qual(ty, s, n, sp) => {
            if let E::Ty::Enum(enum_name, ctors) = ty {
                if ctors.contains(n) {
                    return IRExpr::Ctor {
                        enum_name: enum_name.clone(),
                        ctor: n.clone(),
                        args: vec![],
                        span: *sp,
                    };
                }
            }
            IRExpr::Var {
                name: format!("{s}::{n}"),
                ty: lower_ty(ty, vi),
                span: *sp,
            }
        }
        E::EExpr::Quant(_, q, v, vty, body, sp) => {
            let lowered = lower_expr(body, vi);
            let vt = lower_ty(vty, vi);
            match q {
                E::Quantifier::All => IRExpr::Forall {
                    var: v.clone(),
                    domain: vt,
                    body: Box::new(lowered),
                    span: *sp,
                },
                E::Quantifier::Exists | E::Quantifier::Some => IRExpr::Exists {
                    var: v.clone(),
                    domain: vt,
                    body: Box::new(lowered),
                    span: *sp,
                },
                E::Quantifier::One => IRExpr::One {
                    var: v.clone(),
                    domain: vt,
                    body: Box::new(lowered),
                    span: *sp,
                },
                E::Quantifier::Lone => IRExpr::Lone {
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
            body: Box::new(lower_expr(expr, vi)),
            span: *sp,
        },
        E::EExpr::Eventually(_, expr, sp) => IRExpr::Eventually {
            body: Box::new(lower_expr(expr, vi)),
            span: *sp,
        },
        E::EExpr::Until(_, left, right, sp) => IRExpr::Until {
            left: Box::new(lower_expr(left, vi)),
            right: Box::new(lower_expr(right, vi)),
            span: *sp,
        },
        E::EExpr::Assert(_, expr, sp) => IRExpr::Assert {
            expr: Box::new(lower_expr(expr, vi)),
            span: *sp,
        },
        E::EExpr::Assume(_, expr, sp) => IRExpr::Assume {
            expr: Box::new(lower_expr(expr, vi)),
            span: *sp,
        },
        E::EExpr::NamedPair(_, _, expr, _) => lower_expr(expr, vi),
        E::EExpr::Assign(_, lhs, rhs, sp) => IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(lower_expr(lhs, vi)),
            right: Box::new(lower_expr(rhs, vi)),
            ty: IRType::Bool,
            span: *sp,
        },
        E::EExpr::Seq(ty, a, b, sp) => IRExpr::BinOp {
            op: "OpSeq".to_owned(),
            left: Box::new(lower_expr(a, vi)),
            right: Box::new(lower_expr(b, vi)),
            ty: lower_ty(ty, vi),
            span: *sp,
        },
        E::EExpr::SameStep(ty, a, b, sp) => IRExpr::BinOp {
            op: "OpSameStep".to_owned(),
            left: Box::new(lower_expr(a, vi)),
            right: Box::new(lower_expr(b, vi)),
            ty: lower_ty(ty, vi),
            span: *sp,
        },
        E::EExpr::Let(binds, body, sp) => {
            let bs = binds
                .iter()
                .map(|(n, mt, e)| LetBinding {
                    name: n.clone(),
                    ty: mt.as_ref().map_or(IRType::String, |t| lower_ty(t, vi)),
                    expr: lower_expr(e, vi),
                })
                .collect();
            IRExpr::Let {
                bindings: bs,
                body: Box::new(lower_expr(body, vi)),
                span: *sp,
            }
        }
        E::EExpr::Lam(params, _mret, body, sp) => {
            if params.is_empty() {
                return lower_expr(body, vi);
            }
            params
                .iter()
                .rev()
                .fold(lower_expr(body, vi), |acc, (pn, pt)| IRExpr::Lam {
                    param: pn.clone(),
                    param_type: lower_ty(pt, vi),
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
            let lowered: Vec<IRExpr> = es.iter().map(|e| lower_expr(e, vi)).collect();
            let tuple_ty = lower_ty(ty, vi);
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
                map: Box::new(lower_expr(s, vi)),
                key: Box::new(lower_expr(e, vi)),
                ty: IRType::Bool,
                span: *sp,
            }
        }
        E::EExpr::Card(_ty, expr, sp) => IRExpr::Card {
            expr: Box::new(lower_expr(expr, vi)),
            span: *sp,
        },
        E::EExpr::Pipe(ty, a, f, sp) => IRExpr::App {
            func: Box::new(lower_expr(f, vi)),
            arg: Box::new(lower_expr(a, vi)),
            ty: lower_ty(ty, vi),
            span: *sp,
        },
        E::EExpr::Match(scrutinee, arms, sp) => IRExpr::Match {
            scrutinee: Box::new(lower_expr(scrutinee, vi)),
            arms: arms
                .iter()
                .map(|(pat, guard, body)| IRMatchArm {
                    pattern: lower_pattern(pat),
                    guard: guard.as_ref().map(|g| lower_expr(g, vi)),
                    body: lower_expr(body, vi),
                })
                .collect(),
            span: *sp,
        },
        E::EExpr::MapUpdate(ty, m, k, v, sp) => IRExpr::MapUpdate {
            map: Box::new(lower_expr(m, vi)),
            key: Box::new(lower_expr(k, vi)),
            value: Box::new(lower_expr(v, vi)),
            ty: lower_ty(ty, vi),
            span: *sp,
        },
        E::EExpr::Index(ty, m, k, sp) => IRExpr::Index {
            map: Box::new(lower_expr(m, vi)),
            key: Box::new(lower_expr(k, vi)),
            ty: lower_ty(ty, vi),
            span: *sp,
        },
        E::EExpr::SetComp(ty, proj, var, domain, filter, sp) => IRExpr::SetComp {
            var: var.clone(),
            domain: lower_ty(domain, vi),
            filter: Box::new(lower_expr(filter, vi)),
            projection: proj.as_ref().map(|p| Box::new(lower_expr(p, vi))),
            ty: lower_ty(ty, vi),
            span: *sp,
        },
        E::EExpr::SetLit(ty, elems, sp) => IRExpr::SetLit {
            elements: elems.iter().map(|e| lower_expr(e, vi)).collect(),
            ty: lower_ty(ty, vi),
            span: *sp,
        },
        E::EExpr::SeqLit(ty, elems, sp) => IRExpr::SeqLit {
            elements: elems.iter().map(|e| lower_expr(e, vi)).collect(),
            ty: lower_ty(ty, vi),
            span: *sp,
        },
        E::EExpr::MapLit(ty, entries, sp) => IRExpr::MapLit {
            entries: entries
                .iter()
                .map(|(k, v)| (lower_expr(k, vi), lower_expr(v, vi)))
                .collect(),
            ty: lower_ty(ty, vi),
            span: *sp,
        },
        E::EExpr::Sorry(sp) => IRExpr::Sorry { span: *sp },
        E::EExpr::Todo(sp) => IRExpr::Todo { span: *sp },
        // Imperative constructs
        E::EExpr::Block(items, sp) => IRExpr::Block {
            exprs: items.iter().map(|e| lower_expr(e, vi)).collect(),
            span: *sp,
        },
        E::EExpr::VarDecl(name, ty, init, rest, sp) => IRExpr::VarDecl {
            name: name.clone(),
            ty: ty.as_ref().map_or(IRType::String, |t| lower_ty(t, vi)),
            init: Box::new(lower_expr(init, vi)),
            rest: Box::new(lower_expr(rest, vi)),
            span: *sp,
        },
        E::EExpr::While(cond, contracts, body, sp) => {
            let (invariants, decreases) = lower_while_contracts(contracts, vi);
            IRExpr::While {
                cond: Box::new(lower_expr(cond, vi)),
                invariants,
                decreases,
                body: Box::new(lower_expr(body, vi)),
                span: *sp,
            }
        }
        E::EExpr::IfElse(cond, then_body, else_body, sp) => IRExpr::IfElse {
            cond: Box::new(lower_expr(cond, vi)),
            then_body: Box::new(lower_expr(then_body, vi)),
            else_body: else_body.as_ref().map(|e| Box::new(lower_expr(e, vi))),
            span: *sp,
        },
        E::EExpr::CtorRecord(ty, qual, ctor_name, fields, sp) => {
            // Determine the enum name from the qualifier or the resolved type
            let enum_name = if let Some(q) = qual {
                q.clone()
            } else if let E::Ty::Enum(en, _) = ty {
                en.clone()
            } else {
                // Search through known enum types for this constructor name
                vi.keys()
                    .find(|ename| {
                        vi.get(*ename).map_or(false, |variants| {
                            variants.iter().any(|v| match v {
                                E::EVariant::Simple(n)
                                | E::EVariant::Record(n, _)
                                | E::EVariant::Param(n, _) => n == ctor_name,
                            })
                        })
                    })
                    .cloned()
                    .unwrap_or_default()
            };
            IRExpr::Ctor {
                enum_name,
                ctor: ctor_name.clone(),
                args: fields
                    .iter()
                    .map(|(fname, fexpr)| (fname.clone(), lower_expr(fexpr, vi)))
                    .collect(),
                span: *sp,
            }
        }
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
    OpDiamond,
    OpDisjoint,
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
            Self::OpDiamond => write!(f, "OpDiamond"),
            Self::OpDisjoint => write!(f, "OpDisjoint"),
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
        E::BinOp::Diamond => IRBinOp::OpDiamond,
        E::BinOp::Disjoint => IRBinOp::OpDisjoint,
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
        let vi = VariantInfo::new();
        let ir = lower_expr(&expr, &vi);
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
        let vi = VariantInfo::new();
        let ir = lower_expr(&expr, &vi);
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
        let vi = VariantInfo::new();
        let ir = lower_expr(&expr, &vi);
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
            file: Some("/test.ab".to_owned()),
        };
        let vi = VariantInfo::new();
        let ir = lower_verify(&ev, &std::collections::HashMap::new(), &vi);
        assert_eq!(ir.span, Some(sp));
        assert_eq!(ir.file.as_deref(), Some("/test.ab"));
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
            file: Some("/proof.ab".to_owned()),
        };
        let vi = VariantInfo::new();
        let ir = lower_theorem(&et, &std::collections::HashMap::new(), &vi);
        assert_eq!(ir.span, Some(sp));
        assert_eq!(ir.file.as_deref(), Some("/proof.ab"));
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
            file: Some("/scene.ab".to_owned()),
        };
        let vi = VariantInfo::new();
        let ir = lower_scene(&es, &std::collections::HashMap::new(), &vi);
        assert_eq!(ir.span, Some(sp));
        assert_eq!(ir.file.as_deref(), Some("/scene.ab"));
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
            file: Some("/ax.ab".to_owned()),
        };
        let vi = VariantInfo::new();
        let ir = lower_axiom(&ea, &vi);
        assert_eq!(ir.span, Some(sp));
        assert_eq!(ir.file.as_deref(), Some("/ax.ab"));
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
            file: Some("/fn.ab".to_owned()),
        };
        let vi = VariantInfo::new();
        let ir = lower_fn(&ef, &vi);
        assert_eq!(ir.span, Some(sp));
        assert_eq!(ir.file.as_deref(), Some("/fn.ab"));
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
            file: Some("/pred.ab".to_owned()),
        };
        let vi = VariantInfo::new();
        let ir = lower_pred(&ep, &vi);
        assert_eq!(ir.span, Some(sp));
        assert_eq!(ir.file.as_deref(), Some("/pred.ab"));
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
            file: Some("/prop.ab".to_owned()),
        };
        let vi = VariantInfo::new();
        let ir = lower_prop(&ep, &vi);
        assert_eq!(ir.span, Some(sp));
        assert_eq!(ir.file.as_deref(), Some("/prop.ab"));
    }
}
