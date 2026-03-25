//! Pass 2: Resolve names to fully-qualified references.
//!
//! Resolves `TyUnresolved` references to actual types from the environment.
//! Resolves constructor names (e.g., `EVar "Pending"` → constructor of `OrderStatus`).

use std::collections::HashMap;

use super::env::Env;
use super::types::{EEventAction, EExpr, ENextItem, ESceneWhen, Ty};

/// Immutable context for expression resolution, cloned once from Env.
struct Ctx {
    types: HashMap<String, Ty>,
    entity_names: Vec<String>,
}

impl Ctx {
    fn from_env(env: &Env) -> Self {
        Self {
            types: env.types.clone(),
            entity_names: env.entities.keys().cloned().collect(),
        }
    }

    fn resolve_ty(&self, ty: &Ty) -> Ty {
        resolve_ty(&self.types, &self.entity_names, ty)
    }
}

/// Resolve all names in the collected environment.
pub fn resolve(env: &mut Env) {
    resolve_all_types(env);

    let ctx = Ctx::from_env(env);
    resolve_entities(env, &ctx);
    resolve_systems(env, &ctx);
    resolve_preds(env, &ctx);
    resolve_props(env, &ctx);
    resolve_verifies(env, &ctx);
    resolve_scenes(env, &ctx);
    resolve_proofs(env, &ctx);
    resolve_lemmas(env, &ctx);
}

// ── Type resolution ──────────────────────────────────────────────────

fn resolve_all_types(env: &mut Env) {
    let snapshot = env.types.clone();
    let entity_names: Vec<String> = env.entities.keys().cloned().collect();
    for ty in env.types.values_mut() {
        *ty = resolve_ty(&snapshot, &entity_names, ty);
    }
}

fn resolve_ty(types: &HashMap<String, Ty>, entities: &[String], ty: &Ty) -> Ty {
    match ty {
        Ty::Unresolved(n) => {
            if let Some(t) = types.get(n.as_str()) {
                t.clone()
            } else if entities.contains(n) {
                Ty::Entity(n.clone())
            } else {
                ty.clone()
            }
        }
        Ty::Record(n, fs) => Ty::Record(
            n.clone(),
            fs.iter()
                .map(|(fn_, ft)| (fn_.clone(), resolve_ty(types, entities, ft)))
                .collect(),
        ),
        Ty::Param(n, args) => Ty::Param(
            n.clone(),
            args.iter()
                .map(|a| resolve_ty(types, entities, a))
                .collect(),
        ),
        Ty::Alias(n, t) => Ty::Alias(n.clone(), Box::new(resolve_ty(types, entities, t))),
        Ty::Fn(a, b) => Ty::Fn(
            Box::new(resolve_ty(types, entities, a)),
            Box::new(resolve_ty(types, entities, b)),
        ),
        Ty::Set(a) => Ty::Set(Box::new(resolve_ty(types, entities, a))),
        Ty::Seq(a) => Ty::Seq(Box::new(resolve_ty(types, entities, a))),
        Ty::Map(k, v) => Ty::Map(
            Box::new(resolve_ty(types, entities, k)),
            Box::new(resolve_ty(types, entities, v)),
        ),
        Ty::Tuple(ts) => Ty::Tuple(ts.iter().map(|t| resolve_ty(types, entities, t)).collect()),
        _ => ty.clone(),
    }
}

// ── Entity resolution ────────────────────────────────────────────────

fn resolve_entities(env: &mut Env, ctx: &Ctx) {
    for entity in env.entities.values_mut() {
        for field in &mut entity.fields {
            field.ty = ctx.resolve_ty(&field.ty);
            if let Some(def) = &mut field.default {
                *def = resolve_expr(ctx, def);
            }
        }
        for action in &mut entity.actions {
            action.refs = action
                .refs
                .iter()
                .map(|(n, t)| (n.clone(), ctx.resolve_ty(t)))
                .collect();
            action.params = action
                .params
                .iter()
                .map(|(n, t)| (n.clone(), ctx.resolve_ty(t)))
                .collect();
            action.requires = action
                .requires
                .iter()
                .map(|e| resolve_expr(ctx, e))
                .collect();
            action.body = action.body.iter().map(|e| resolve_expr(ctx, e)).collect();
        }
    }
}

// ── System resolution ────────────────────────────────────────────────

fn resolve_systems(env: &mut Env, ctx: &Ctx) {
    for system in env.systems.values_mut() {
        for event in &mut system.events {
            event.params = event
                .params
                .iter()
                .map(|(n, t)| (n.clone(), ctx.resolve_ty(t)))
                .collect();
            event.requires = event
                .requires
                .iter()
                .map(|e| resolve_expr(ctx, e))
                .collect();
            event.ensures = event.ensures.iter().map(|e| resolve_expr(ctx, e)).collect();
            event.body = event
                .body
                .iter()
                .map(|ea| resolve_event_action(ctx, ea))
                .collect();
        }
        for ni in &mut system.next_items {
            if let ENextItem::When(cond, _) = ni {
                *cond = resolve_expr(ctx, cond);
            }
        }
    }
}

fn resolve_event_action(ctx: &Ctx, ea: &EEventAction) -> EEventAction {
    match ea {
        EEventAction::Choose(v, ty, guard, body) => EEventAction::Choose(
            v.clone(),
            ctx.resolve_ty(ty),
            resolve_expr(ctx, guard),
            body.iter().map(|b| resolve_event_action(ctx, b)).collect(),
        ),
        EEventAction::ForAll(v, ty, body) => EEventAction::ForAll(
            v.clone(),
            ctx.resolve_ty(ty),
            body.iter().map(|b| resolve_event_action(ctx, b)).collect(),
        ),
        EEventAction::Create(entity, fields) => EEventAction::Create(
            entity.clone(),
            fields
                .iter()
                .map(|(n, e)| (n.clone(), resolve_expr(ctx, e)))
                .collect(),
        ),
        EEventAction::CrossCall(sys, ev, args) => EEventAction::CrossCall(
            sys.clone(),
            ev.clone(),
            args.iter().map(|e| resolve_expr(ctx, e)).collect(),
        ),
        EEventAction::Apply(target, act, refs, args) => EEventAction::Apply(
            resolve_expr(ctx, target),
            act.clone(),
            refs.iter().map(|e| resolve_expr(ctx, e)).collect(),
            args.iter().map(|e| resolve_expr(ctx, e)).collect(),
        ),
        EEventAction::Expr(e) => EEventAction::Expr(resolve_expr(ctx, e)),
    }
}

// ── Pred/Prop/Verify/Scene/Proof/Lemma resolution ────────────────────

fn resolve_preds(env: &mut Env, ctx: &Ctx) {
    for pred in env.preds.values_mut() {
        pred.params = pred
            .params
            .iter()
            .map(|(n, t)| (n.clone(), ctx.resolve_ty(t)))
            .collect();
        pred.body = resolve_expr(ctx, &pred.body);
    }
}

fn resolve_props(env: &mut Env, ctx: &Ctx) {
    for prop in env.props.values_mut() {
        prop.body = resolve_expr(ctx, &prop.body);
    }
}

fn resolve_verifies(env: &mut Env, ctx: &Ctx) {
    for verify in &mut env.verifies {
        verify.asserts = verify
            .asserts
            .iter()
            .map(|e| resolve_expr(ctx, e))
            .collect();
    }
}

fn resolve_scenes(env: &mut Env, ctx: &Ctx) {
    for scene in &mut env.scenes {
        for given in &mut scene.givens {
            if let Some(c) = &given.condition {
                given.condition = Some(resolve_expr(ctx, c));
            }
        }
        for when in &mut scene.whens {
            match when {
                ESceneWhen::Action { args, .. } => {
                    *args = args.iter().map(|e| resolve_expr(ctx, e)).collect();
                }
                ESceneWhen::Assume(e) => {
                    *e = resolve_expr(ctx, e);
                }
            }
        }
        scene.thens = scene.thens.iter().map(|e| resolve_expr(ctx, e)).collect();
    }
}

fn resolve_proofs(env: &mut Env, ctx: &Ctx) {
    for proof in &mut env.proofs {
        proof.invariants = proof
            .invariants
            .iter()
            .map(|e| resolve_expr(ctx, e))
            .collect();
        proof.shows = proof.shows.iter().map(|e| resolve_expr(ctx, e)).collect();
    }
}

fn resolve_lemmas(env: &mut Env, ctx: &Ctx) {
    for lemma in &mut env.lemmas {
        lemma.body = lemma.body.iter().map(|e| resolve_expr(ctx, e)).collect();
    }
}

// ── Expression resolution ────────────────────────────────────────────

#[allow(clippy::too_many_lines)]
fn resolve_expr(ctx: &Ctx, expr: &EExpr) -> EExpr {
    match expr {
        EExpr::Var(_, name) => {
            let ty = resolve_var_type(ctx, name);
            EExpr::Var(ty, name.clone())
        }
        EExpr::Field(ty, e, f) => {
            EExpr::Field(ty.clone(), Box::new(resolve_expr(ctx, e)), f.clone())
        }
        EExpr::Prime(ty, e) => EExpr::Prime(ty.clone(), Box::new(resolve_expr(ctx, e))),
        EExpr::BinOp(ty, op, a, b) => EExpr::BinOp(
            ty.clone(),
            *op,
            Box::new(resolve_expr(ctx, a)),
            Box::new(resolve_expr(ctx, b)),
        ),
        EExpr::UnOp(ty, op, e) => EExpr::UnOp(ty.clone(), *op, Box::new(resolve_expr(ctx, e))),
        EExpr::Call(ty, f, args) => EExpr::Call(
            ty.clone(),
            Box::new(resolve_expr(ctx, f)),
            args.iter().map(|e| resolve_expr(ctx, e)).collect(),
        ),
        EExpr::CallR(ty, f, refs, args) => EExpr::CallR(
            ty.clone(),
            Box::new(resolve_expr(ctx, f)),
            refs.iter().map(|e| resolve_expr(ctx, e)).collect(),
            args.iter().map(|e| resolve_expr(ctx, e)).collect(),
        ),
        EExpr::Quant(ty, q, v, vty, body) => EExpr::Quant(
            ty.clone(),
            *q,
            v.clone(),
            ctx.resolve_ty(vty),
            Box::new(resolve_expr(ctx, body)),
        ),
        EExpr::Always(ty, e) => EExpr::Always(ty.clone(), Box::new(resolve_expr(ctx, e))),
        EExpr::Eventually(ty, e) => EExpr::Eventually(ty.clone(), Box::new(resolve_expr(ctx, e))),
        EExpr::Assert(ty, e) => EExpr::Assert(ty.clone(), Box::new(resolve_expr(ctx, e))),
        EExpr::Assign(ty, lhs, rhs) => EExpr::Assign(
            ty.clone(),
            Box::new(resolve_expr(ctx, lhs)),
            Box::new(resolve_expr(ctx, rhs)),
        ),
        EExpr::NamedPair(ty, n, e) => {
            EExpr::NamedPair(ty.clone(), n.clone(), Box::new(resolve_expr(ctx, e)))
        }
        EExpr::Seq(ty, a, b) => EExpr::Seq(
            ty.clone(),
            Box::new(resolve_expr(ctx, a)),
            Box::new(resolve_expr(ctx, b)),
        ),
        EExpr::SameStep(ty, a, b) => EExpr::SameStep(
            ty.clone(),
            Box::new(resolve_expr(ctx, a)),
            Box::new(resolve_expr(ctx, b)),
        ),
        EExpr::Let(binds, body) => {
            let bs = binds
                .iter()
                .map(|(n, mt, e)| {
                    (
                        n.clone(),
                        mt.as_ref().map(|t| ctx.resolve_ty(t)),
                        resolve_expr(ctx, e),
                    )
                })
                .collect();
            EExpr::Let(bs, Box::new(resolve_expr(ctx, body)))
        }
        EExpr::Lam(params, mret, body) => EExpr::Lam(
            params
                .iter()
                .map(|(n, t)| (n.clone(), ctx.resolve_ty(t)))
                .collect(),
            mret.as_ref().map(|t| ctx.resolve_ty(t)),
            Box::new(resolve_expr(ctx, body)),
        ),
        EExpr::Qual(_, s, n) => {
            let ty = ctx
                .types
                .get(s.as_str())
                .or_else(|| {
                    let last = last_segment(s);
                    ctx.types.get(last)
                })
                .cloned()
                .unwrap_or_else(|| Ty::Unresolved(s.clone()));
            EExpr::Qual(ty, s.clone(), n.clone())
        }
        EExpr::TupleLit(ty, es) => EExpr::TupleLit(
            ty.clone(),
            es.iter().map(|e| resolve_expr(ctx, e)).collect(),
        ),
        EExpr::In(ty, a, b) => EExpr::In(
            ty.clone(),
            Box::new(resolve_expr(ctx, a)),
            Box::new(resolve_expr(ctx, b)),
        ),
        EExpr::Card(ty, e) => EExpr::Card(ty.clone(), Box::new(resolve_expr(ctx, e))),
        EExpr::Pipe(ty, a, b) => EExpr::Pipe(
            ty.clone(),
            Box::new(resolve_expr(ctx, a)),
            Box::new(resolve_expr(ctx, b)),
        ),
        e => e.clone(),
    }
}

fn resolve_var_type(ctx: &Ctx, name: &str) -> Ty {
    if let Some(parent_ty) = find_constructor_type(ctx, name) {
        return parent_ty;
    }
    if let Some(t) = ctx.types.get(name) {
        return t.clone();
    }
    Ty::Unresolved(name.to_owned())
}

fn find_constructor_type(ctx: &Ctx, name: &str) -> Option<Ty> {
    for ty in ctx.types.values() {
        if let Ty::Enum(_, ctors) = ty {
            if ctors.iter().any(|c| c == name) {
                return Some(ty.clone());
            }
        }
    }
    None
}

fn last_segment(s: &str) -> &str {
    s.rsplit("::").next().unwrap_or(s)
}
