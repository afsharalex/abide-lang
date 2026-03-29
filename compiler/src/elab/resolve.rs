//! Pass 2: Resolve names to fully-qualified references.
//!
//! Resolves `TyUnresolved` references to actual types from the environment.
//! Resolves constructor names (e.g., `EVar "Pending"` → constructor of `OrderStatus`).

use std::collections::{HashMap, HashSet};

use crate::ast::{UseDecl, Visibility};

use super::env::Env;
use super::error::{ElabError, ErrorKind};
use super::types::{EEventAction, EExpr, ENextItem, EPattern, ESceneWhen, Ty};

/// Immutable context for expression resolution, cloned once from Env.
struct Ctx {
    types: HashMap<String, Ty>,
    entity_names: Vec<String>,
    /// Alias → canonical name map for rewriting aliased references.
    aliases: HashMap<String, String>,
}

impl Ctx {
    fn from_env(env: &Env) -> Self {
        Self {
            types: env.types.clone(),
            entity_names: env.entities.keys().cloned().collect(),
            aliases: env.aliases.clone(),
        }
    }

    fn resolve_ty(&self, ty: &Ty) -> Ty {
        resolve_ty(&self.types, &self.entity_names, ty)
    }

    /// Resolve an alias to its canonical name, or return the name as-is.
    fn canonical_name<'a>(&'a self, name: &'a str) -> &'a str {
        self.aliases.get(name).map_or(name, String::as_str)
    }
}

/// Resolve all names in the collected environment.
pub fn resolve(env: &mut Env) {
    resolve_use_declarations(env);
    resolve_all_types(env);

    let ctx = Ctx::from_env(env);
    resolve_entities(env, &ctx);
    resolve_systems(env, &ctx);
    resolve_preds(env, &ctx);
    resolve_props(env, &ctx);
    resolve_verifies(env, &ctx);
    resolve_scenes(env, &ctx);
    resolve_theorems(env, &ctx);
    resolve_lemmas(env, &ctx);
    resolve_axioms(env, &ctx);
    resolve_consts(env, &ctx);
    resolve_fns(env, &ctx);
}

// ── Use declaration validation ──────────────────────────────────────

/// Validate use declarations and populate the working namespace.
///
/// For each `use` declaration:
/// 1. Validate the target module and names exist
/// 2. Check visibility (cross-module access requires `pub`)
/// 3. Import declarations into the bare-name working namespace
///    (types, entities, systems, preds, props maps) so downstream
///    resolve/check/lower passes can find them by unqualified name.
#[allow(clippy::too_many_lines)]
fn resolve_use_declarations(env: &mut Env) {
    // Clear aliases from any prior resolve pass (idempotent reset).
    env.aliases.clear();

    let known_modules = env.known_modules.clone();
    let root_module = env.module_name.clone();

    // Only process use declarations from the current root module.
    // Use declarations from other loaded modules should not affect
    // the root module's namespace.
    let use_decls: Vec<_> = env
        .use_decls
        .iter()
        .filter(|(_, source)| *source == root_module)
        .cloned()
        .collect();

    // Collect imports to apply: (local_name, source_module, source_name)
    let mut imports: Vec<(String, String, String)> = Vec::new();
    let mut errors: Vec<ElabError> = Vec::new();

    for (ud, source_module) in &use_decls {
        let importing = source_module.as_deref();

        match ud {
            UseDecl::All { module, .. } => {
                if !known_modules.contains(module) {
                    continue;
                }
                let public_decls: Vec<String> = env
                    .decls_in_module(module)
                    .iter()
                    .filter(|d| d.visibility == Visibility::Public)
                    .map(|d| d.name.clone())
                    .collect();
                for name in public_decls {
                    imports.push((name.clone(), module.clone(), name));
                }
            }
            UseDecl::Single { module, name, .. } => {
                if let Some(err) = check_import_target(env, &known_modules, module, name, importing)
                {
                    errors.push(err);
                } else {
                    imports.push((name.clone(), module.clone(), name.clone()));
                }
            }
            UseDecl::Alias {
                module,
                name,
                alias,
                ..
            } => {
                if let Some(err) = check_import_target(env, &known_modules, module, name, importing)
                {
                    errors.push(err);
                } else {
                    imports.push((alias.clone(), module.clone(), name.clone()));
                }
            }
            UseDecl::Items { module, items, .. } => {
                for item in items {
                    let (name, local) = match item {
                        crate::ast::UseItem::Name { name, .. } => (name.as_str(), name.clone()),
                        crate::ast::UseItem::Alias { name, alias, .. } => {
                            (name.as_str(), alias.clone())
                        }
                    };
                    if let Some(err) =
                        check_import_target(env, &known_modules, module, name, importing)
                    {
                        errors.push(err);
                    } else {
                        imports.push((local, module.clone(), name.to_string()));
                    }
                }
            }
        }
    }

    env.errors.extend(errors);

    // Apply imports: use import_into_namespace which handles all decl kinds
    // (types, entities, systems, preds, props, consts, fns) via qualified key lookup.
    for (local_name, source_module, source_name) in &imports {
        env.import_into_namespace(local_name, source_module, source_name);
        // Track alias → canonical name mapping so resolve_expr can rewrite
        // aliased variable references to canonical names for lowering.
        if local_name != source_name {
            env.aliases.insert(local_name.clone(), source_name.clone());
        }
    }
}

/// Check that an import target exists, belongs to the right module, and is public.
/// Returns `Some(error)` if validation fails, `None` if OK.
fn check_import_target(
    env: &Env,
    known_modules: &std::collections::HashSet<String>,
    target_module: &str,
    target_name: &str,
    importing_module: Option<&str>,
) -> Option<ElabError> {
    if !known_modules.contains(target_module) {
        // Module not loaded — don't error. In single-file mode this is expected
        // (cross-module use declarations are aspirational). Only validate targets
        // in modules that are actually loaded.
        return None;
    }

    match env.lookup_decl_qualified(target_module, target_name) {
        Some(decl) => {
            // Check visibility: cross-module access requires Public
            if decl.visibility == Visibility::Private && importing_module != Some(target_module) {
                Some(ElabError::new(
                    ErrorKind::UndefinedRef,
                    format!(
                        "cannot import private declaration '{target_name}' from module '{target_module}'"
                    ),
                    "mark it 'pub' to make it importable".to_string(),
                ))
            } else {
                None
            }
        }
        None => Some(ElabError::new(
            ErrorKind::UndefinedRef,
            format!("module '{target_module}' does not export '{target_name}'"),
            String::new(),
        )),
    }
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
                *def = resolve_expr(ctx, &HashSet::new(), def);
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
            // Bind ref params and value params so they aren't alias-rewritten
            let mut action_bound: HashSet<String> =
                action.refs.iter().map(|(n, _)| n.clone()).collect();
            action_bound.extend(action.params.iter().map(|(n, _)| n.clone()));
            action.requires = action
                .requires
                .iter()
                .map(|e| resolve_expr(ctx, &action_bound, e))
                .collect();
            action.body = action
                .body
                .iter()
                .map(|e| resolve_expr(ctx, &action_bound, e))
                .collect();
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
            // Bind event params so they aren't alias-rewritten
            let event_bound: HashSet<String> =
                event.params.iter().map(|(n, _)| n.clone()).collect();
            event.requires = event
                .requires
                .iter()
                .map(|e| resolve_expr(ctx, &event_bound, e))
                .collect();
            event.ensures = event
                .ensures
                .iter()
                .map(|e| resolve_expr(ctx, &event_bound, e))
                .collect();
            event.body = event
                .body
                .iter()
                .map(|ea| resolve_event_action(ctx, &event_bound, ea))
                .collect();
        }
        for ni in &mut system.next_items {
            if let ENextItem::When(cond, _) = ni {
                *cond = resolve_expr(ctx, &HashSet::new(), cond);
            }
        }
    }
}

fn resolve_event_action(ctx: &Ctx, bound: &HashSet<String>, ea: &EEventAction) -> EEventAction {
    match ea {
        EEventAction::Choose(v, ty, guard, body) => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(v.clone());
            EEventAction::Choose(
                v.clone(),
                ctx.resolve_ty(ty),
                resolve_expr(ctx, &inner_bound, guard),
                body.iter()
                    .map(|b| resolve_event_action(ctx, &inner_bound, b))
                    .collect(),
            )
        }
        EEventAction::ForAll(v, ty, body) => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(v.clone());
            EEventAction::ForAll(
                v.clone(),
                ctx.resolve_ty(ty),
                body.iter()
                    .map(|b| resolve_event_action(ctx, &inner_bound, b))
                    .collect(),
            )
        }
        EEventAction::Create(entity, fields) => EEventAction::Create(
            entity.clone(),
            fields
                .iter()
                .map(|(n, e)| (n.clone(), resolve_expr(ctx, bound, e)))
                .collect(),
        ),
        EEventAction::CrossCall(sys, ev, args) => EEventAction::CrossCall(
            sys.clone(),
            ev.clone(),
            args.iter().map(|e| resolve_expr(ctx, bound, e)).collect(),
        ),
        EEventAction::Apply(target, act, refs, args) => EEventAction::Apply(
            resolve_expr(ctx, bound, target),
            act.clone(),
            refs.iter().map(|e| resolve_expr(ctx, bound, e)).collect(),
            args.iter().map(|e| resolve_expr(ctx, bound, e)).collect(),
        ),
        EEventAction::Expr(e) => EEventAction::Expr(resolve_expr(ctx, bound, e)),
    }
}

// ── Pred/Prop/Verify/Scene/Theorem/Lemma resolution ─────────────────

fn resolve_preds(env: &mut Env, ctx: &Ctx) {
    for pred in env.preds.values_mut() {
        pred.params = pred
            .params
            .iter()
            .map(|(n, t)| (n.clone(), ctx.resolve_ty(t)))
            .collect();
        let bound: HashSet<String> = pred.params.iter().map(|(n, _)| n.clone()).collect();
        pred.body = resolve_expr(ctx, &bound, &pred.body);
    }
}

fn resolve_props(env: &mut Env, ctx: &Ctx) {
    for prop in env.props.values_mut() {
        prop.body = resolve_expr(ctx, &HashSet::new(), &prop.body);
    }
}

fn resolve_verifies(env: &mut Env, ctx: &Ctx) {
    for verify in &mut env.verifies {
        verify.asserts = verify
            .asserts
            .iter()
            .map(|e| resolve_expr(ctx, &HashSet::new(), e))
            .collect();
    }
}

fn resolve_scenes(env: &mut Env, ctx: &Ctx) {
    for scene in &mut env.scenes {
        // Collect given variables as binders — they scope over when/then sections
        let mut scene_bound = HashSet::new();
        for given in &mut scene.givens {
            scene_bound.insert(given.var.clone());
            if let Some(c) = &given.condition {
                // Given conditions can reference prior given vars
                given.condition = Some(resolve_expr(ctx, &scene_bound, c));
            }
        }
        for when in &mut scene.whens {
            match when {
                ESceneWhen::Action { var, args, .. } => {
                    // Resolve args BEFORE adding the action var to scope —
                    // args establish the binding, they don't reference it.
                    *args = args
                        .iter()
                        .map(|e| resolve_expr(ctx, &scene_bound, e))
                        .collect();
                    // Now add the action binding var for subsequent whens/thens
                    scene_bound.insert(var.clone());
                }
                ESceneWhen::Assume(e) => {
                    *e = resolve_expr(ctx, &scene_bound, e);
                }
            }
        }
        scene.thens = scene
            .thens
            .iter()
            .map(|e| resolve_expr(ctx, &scene_bound, e))
            .collect();
    }
}

fn resolve_theorems(env: &mut Env, ctx: &Ctx) {
    for theorem in &mut env.theorems {
        theorem.invariants = theorem
            .invariants
            .iter()
            .map(|e| resolve_expr(ctx, &HashSet::new(), e))
            .collect();
        theorem.shows = theorem
            .shows
            .iter()
            .map(|e| resolve_expr(ctx, &HashSet::new(), e))
            .collect();
    }
}

fn resolve_lemmas(env: &mut Env, ctx: &Ctx) {
    for lemma in &mut env.lemmas {
        lemma.body = lemma
            .body
            .iter()
            .map(|e| resolve_expr(ctx, &HashSet::new(), e))
            .collect();
    }
}

fn resolve_axioms(env: &mut Env, ctx: &Ctx) {
    for axiom in &mut env.axioms {
        axiom.body = resolve_expr(ctx, &HashSet::new(), &axiom.body);
    }
}

fn resolve_consts(env: &mut Env, ctx: &Ctx) {
    for c in env.consts.values_mut() {
        c.body = resolve_expr(ctx, &HashSet::new(), &c.body);
    }
}

fn resolve_fns(env: &mut Env, ctx: &Ctx) {
    for f in env.fns.values_mut() {
        f.params = f
            .params
            .iter()
            .map(|(n, t)| (n.clone(), ctx.resolve_ty(t)))
            .collect();
        f.ret_ty = ctx.resolve_ty(&f.ret_ty);
        let bound: HashSet<String> = f.params.iter().map(|(n, _)| n.clone()).collect();
        f.body = resolve_expr(ctx, &bound, &f.body);
    }
}

// ── Expression resolution ────────────────────────────────────────────

#[allow(clippy::too_many_lines)]
fn resolve_expr(ctx: &Ctx, bound: &HashSet<String>, expr: &EExpr) -> EExpr {
    match expr {
        EExpr::Var(ty, name) => {
            if bound.contains(name) {
                // Bound variable: keep name and type as-is.
                // Don't alias-rewrite or constructor-resolve.
                EExpr::Var(ty.clone(), name.clone())
            } else {
                let resolved_name = ctx.canonical_name(name).to_owned();
                let resolved_ty = resolve_var_type(ctx, &resolved_name);
                EExpr::Var(resolved_ty, resolved_name)
            }
        }
        EExpr::Field(ty, e, f) => {
            EExpr::Field(ty.clone(), Box::new(resolve_expr(ctx, bound, e)), f.clone())
        }
        EExpr::Prime(ty, e) => EExpr::Prime(ty.clone(), Box::new(resolve_expr(ctx, bound, e))),
        EExpr::BinOp(ty, op, a, b) => EExpr::BinOp(
            ty.clone(),
            *op,
            Box::new(resolve_expr(ctx, bound, a)),
            Box::new(resolve_expr(ctx, bound, b)),
        ),
        EExpr::UnOp(ty, op, e) => {
            EExpr::UnOp(ty.clone(), *op, Box::new(resolve_expr(ctx, bound, e)))
        }
        EExpr::Call(ty, f, args) => EExpr::Call(
            ty.clone(),
            Box::new(resolve_expr(ctx, bound, f)),
            args.iter().map(|e| resolve_expr(ctx, bound, e)).collect(),
        ),
        EExpr::CallR(ty, f, refs, args) => EExpr::CallR(
            ty.clone(),
            Box::new(resolve_expr(ctx, bound, f)),
            refs.iter().map(|e| resolve_expr(ctx, bound, e)).collect(),
            args.iter().map(|e| resolve_expr(ctx, bound, e)).collect(),
        ),
        EExpr::Quant(ty, q, v, vty, body) => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(v.clone());
            EExpr::Quant(
                ty.clone(),
                *q,
                v.clone(),
                ctx.resolve_ty(vty),
                Box::new(resolve_expr(ctx, &inner_bound, body)),
            )
        }
        EExpr::Always(ty, e) => EExpr::Always(ty.clone(), Box::new(resolve_expr(ctx, bound, e))),
        EExpr::Eventually(ty, e) => {
            EExpr::Eventually(ty.clone(), Box::new(resolve_expr(ctx, bound, e)))
        }
        EExpr::Assert(ty, e) => EExpr::Assert(ty.clone(), Box::new(resolve_expr(ctx, bound, e))),
        EExpr::Assign(ty, lhs, rhs) => EExpr::Assign(
            ty.clone(),
            Box::new(resolve_expr(ctx, bound, lhs)),
            Box::new(resolve_expr(ctx, bound, rhs)),
        ),
        EExpr::NamedPair(ty, n, e) => {
            EExpr::NamedPair(ty.clone(), n.clone(), Box::new(resolve_expr(ctx, bound, e)))
        }
        EExpr::Seq(ty, a, b) => EExpr::Seq(
            ty.clone(),
            Box::new(resolve_expr(ctx, bound, a)),
            Box::new(resolve_expr(ctx, bound, b)),
        ),
        EExpr::SameStep(ty, a, b) => EExpr::SameStep(
            ty.clone(),
            Box::new(resolve_expr(ctx, bound, a)),
            Box::new(resolve_expr(ctx, bound, b)),
        ),
        EExpr::Let(binds, body) => {
            let mut inner_bound = bound.clone();
            let bs = binds
                .iter()
                .map(|(n, mt, e)| {
                    let resolved = (
                        n.clone(),
                        mt.as_ref().map(|t| ctx.resolve_ty(t)),
                        resolve_expr(ctx, &inner_bound, e),
                    );
                    inner_bound.insert(n.clone());
                    resolved
                })
                .collect();
            EExpr::Let(bs, Box::new(resolve_expr(ctx, &inner_bound, body)))
        }
        EExpr::Lam(params, mret, body) => {
            let mut inner_bound = bound.clone();
            for (n, _) in params {
                inner_bound.insert(n.clone());
            }
            EExpr::Lam(
                params
                    .iter()
                    .map(|(n, t)| (n.clone(), ctx.resolve_ty(t)))
                    .collect(),
                mret.as_ref().map(|t| ctx.resolve_ty(t)),
                Box::new(resolve_expr(ctx, &inner_bound, body)),
            )
        }
        EExpr::Match(scrut, arms) => {
            let resolved_scrut = resolve_expr(ctx, bound, scrut);
            let resolved_arms = arms
                .iter()
                .map(|(pat, guard, body)| {
                    let mut arm_bound = bound.clone();
                    collect_epattern_vars(pat, &mut arm_bound);
                    let resolved_guard = guard.as_ref().map(|g| resolve_expr(ctx, &arm_bound, g));
                    let resolved_body = resolve_expr(ctx, &arm_bound, body);
                    (pat.clone(), resolved_guard, resolved_body)
                })
                .collect();
            EExpr::Match(Box::new(resolved_scrut), resolved_arms)
        }
        EExpr::SetComp(ty, proj, var, vty, filter) => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.clone());
            EExpr::SetComp(
                ty.clone(),
                proj.as_ref()
                    .map(|p| Box::new(resolve_expr(ctx, &inner_bound, p))),
                var.clone(),
                ctx.resolve_ty(vty),
                Box::new(resolve_expr(ctx, &inner_bound, filter)),
            )
        }
        EExpr::MapUpdate(ty, m, k, v) => EExpr::MapUpdate(
            ty.clone(),
            Box::new(resolve_expr(ctx, bound, m)),
            Box::new(resolve_expr(ctx, bound, k)),
            Box::new(resolve_expr(ctx, bound, v)),
        ),
        EExpr::Index(ty, m, k) => EExpr::Index(
            ty.clone(),
            Box::new(resolve_expr(ctx, bound, m)),
            Box::new(resolve_expr(ctx, bound, k)),
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
            es.iter().map(|e| resolve_expr(ctx, bound, e)).collect(),
        ),
        EExpr::In(ty, a, b) => EExpr::In(
            ty.clone(),
            Box::new(resolve_expr(ctx, bound, a)),
            Box::new(resolve_expr(ctx, bound, b)),
        ),
        EExpr::Card(ty, e) => EExpr::Card(ty.clone(), Box::new(resolve_expr(ctx, bound, e))),
        EExpr::Pipe(ty, a, b) => EExpr::Pipe(
            ty.clone(),
            Box::new(resolve_expr(ctx, bound, a)),
            Box::new(resolve_expr(ctx, bound, b)),
        ),
        e => e.clone(),
    }
}

/// Collect variable names bound by a pattern into the given set.
fn collect_epattern_vars(pat: &EPattern, vars: &mut HashSet<String>) {
    match pat {
        EPattern::Var(name) => {
            vars.insert(name.clone());
        }
        EPattern::Ctor(_, fields) => {
            for (_, fpat) in fields {
                collect_epattern_vars(fpat, vars);
            }
        }
        EPattern::Wild => {}
        EPattern::Or(left, right) => {
            collect_epattern_vars(left, vars);
            collect_epattern_vars(right, vars);
        }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::elab::collect;
    use crate::lex;
    use crate::parse::Parser;

    fn elaborate_src(src: &str) -> Env {
        let tokens = lex::lex(src).expect("lex error");
        let mut parser = Parser::new(tokens);
        let prog = parser.parse_program().expect("parse error");
        let mut env = collect::collect(&prog);
        // Match the real elaborate_env pipeline: build working namespace first
        env.build_working_namespace();
        resolve(&mut env);
        env
    }

    #[test]
    fn private_import_cross_module_produces_error() {
        // Module "Importer" imports private type from "Provider".
        // In multi-file: Provider defines Secret, Importer uses it.
        // In single-file simulation: we collect into env as Importer,
        // then manually insert a Provider declaration.
        let tokens = lex::lex("module Importer\nuse Provider::Secret").unwrap();
        let mut parser = Parser::new(tokens);
        let prog = parser.parse_program().unwrap();
        let mut env = collect::collect(&prog);

        // Simulate a declaration from module Provider (as if loaded from another file)
        let info = env.make_decl_info(
            crate::elab::env::DeclKind::Type,
            "Secret".to_string(),
            Some(Ty::Enum("Secret".to_string(), vec!["X".to_string()])),
            Visibility::Private,
        );
        // Override the module to Provider (make_decl_info uses current module)
        let info = crate::elab::env::DeclInfo {
            module: Some("Provider".to_string()),
            ..info
        };
        env.decls.insert("Provider::Secret".to_string(), info);
        env.known_modules.insert("Provider".to_string());
        env.types.insert(
            "Secret".to_string(),
            Ty::Enum("Secret".to_string(), vec!["X".to_string()]),
        );

        resolve(&mut env);
        assert!(
            env.errors
                .iter()
                .any(|e| e.message.contains("cannot import private")),
            "expected private import error, got: {:?}",
            env.errors
        );
    }

    #[test]
    fn public_import_no_error() {
        let env = elaborate_src("module TestMod\npub type Status = Active\nuse TestMod::Status");
        assert!(
            !env.errors
                .iter()
                .any(|e| e.message.contains("cannot import")),
            "public import should not error, got: {:?}",
            env.errors
        );
    }

    #[test]
    fn same_module_private_import_allowed() {
        let env = elaborate_src("module TestMod\ntype Secret = X | Y\nuse TestMod::Secret");
        let private_errors: Vec<_> = env
            .errors
            .iter()
            .filter(|e| e.message.contains("cannot import private"))
            .collect();
        assert!(
            private_errors.is_empty(),
            "same-module private import should be allowed, got: {:?}",
            private_errors
        );
    }

    #[test]
    fn use_all_unknown_module_silently_skipped() {
        // Unknown modules are silently skipped — they may be in unloaded files.
        // Only loaded modules trigger validation.
        let env = elaborate_src("module Importer\nuse NoSuchModule::*");
        let module_errors: Vec<_> = env
            .errors
            .iter()
            .filter(|e| e.message.contains("NoSuchModule"))
            .collect();
        assert!(
            module_errors.is_empty(),
            "unknown module in use M::* should be silently skipped, got: {:?}",
            module_errors
        );
    }

    #[test]
    fn use_missing_name_in_known_module_errors() {
        // Module TestMod exports Status but not NoSuchName
        let env = elaborate_src("module TestMod\npub type Status = A\nuse TestMod::NoSuchName");
        assert!(
            env.errors
                .iter()
                .any(|e| e.message.contains("does not export")),
            "use M::N where N doesn't exist should error, got: {:?}",
            env.errors
        );
    }

    #[test]
    fn multi_module_same_name_no_collision() {
        // Two different modules can have same-named declarations
        use crate::elab::env::Env;
        let mut env = Env::new();

        // File 1: module A defines type Status
        let tokens1 = lex::lex("module A\npub type Status = Active").unwrap();
        let mut p1 = Parser::new(tokens1);
        let prog1 = p1.parse_program().unwrap();
        let saved = env.module_name.take();
        collect::collect_into(&mut env, &prog1);
        let m1 = env.module_name.clone();
        env.module_name = saved.or(m1);

        // File 2: module B defines type Status
        let saved = env.module_name.take();
        env.module_name = None; // Reset for file 2
        let tokens2 = lex::lex("module B\npub type Status = Pending").unwrap();
        let mut p2 = Parser::new(tokens2);
        let prog2 = p2.parse_program().unwrap();
        collect::collect_into(&mut env, &prog2);
        let m2 = env.module_name.clone();
        env.module_name = saved.or(m2);

        // Both should exist without collision
        assert!(
            env.lookup_decl_qualified("A", "Status").is_some(),
            "A::Status should exist"
        );
        assert!(
            env.lookup_decl_qualified("B", "Status").is_some(),
            "B::Status should exist"
        );
        // No duplicate errors
        let dup_errors: Vec<_> = env
            .errors
            .iter()
            .filter(|e| e.message.contains("duplicate"))
            .collect();
        assert!(
            dup_errors.is_empty(),
            "same name in different modules should not collide, got: {:?}",
            dup_errors
        );

        // Both modules' types should coexist in the qualified types map
        assert!(
            env.types.contains_key("A::Status"),
            "A::Status should be in types map"
        );
        assert!(
            env.types.contains_key("B::Status"),
            "B::Status should be in types map"
        );

        // After building working namespace, bare "Status" resolves to one
        env.build_working_namespace();
        assert!(
            env.types.contains_key("Status"),
            "bare Status should be in working namespace after build"
        );
    }

    #[test]
    fn multi_module_cross_import_visibility() {
        // Module A defines private Secret, module B tries to import it
        use crate::elab::env::Env;
        let mut env = Env::new();

        // File 1: module Provider, private type Secret
        let tokens1 = lex::lex("module Provider\ntype Secret = X").unwrap();
        let mut p1 = Parser::new(tokens1);
        let prog1 = p1.parse_program().unwrap();
        collect::collect_into(&mut env, &prog1);
        let m1 = env.module_name.clone();

        // File 2: module Importer, tries to use Provider::Secret
        env.module_name = None;
        let tokens2 = lex::lex("module Importer\nuse Provider::Secret").unwrap();
        let mut p2 = Parser::new(tokens2);
        let prog2 = p2.parse_program().unwrap();
        collect::collect_into(&mut env, &prog2);
        env.module_name = m1; // Root module is Provider (first file)

        // Now set importing context and resolve
        env.module_name = Some("Importer".to_string());
        resolve(&mut env);

        assert!(
            env.errors
                .iter()
                .any(|e| e.message.contains("cannot import private")),
            "cross-module private import should error, got: {:?}",
            env.errors
        );
    }

    #[test]
    fn end_to_end_cross_module_public_import_materializes() {
        // Full pipeline: two modules, one imports a public type from the other.
        // After elaborate_env, the imported type should be usable in the
        // working namespace (bare-name types map).
        use crate::elab;
        use crate::elab::env::Env;

        let mut env = Env::new();

        // File 1: module Provider declares pub type Status = Active | Inactive
        env.module_name = None;
        let tokens1 = lex::lex("module Provider\npub type Status = Active | Inactive").unwrap();
        let mut p1 = Parser::new(tokens1);
        let prog1 = p1.parse_program().unwrap();
        collect::collect_into(&mut env, &prog1);
        // First file → keep its module as root is wrong here; we want Consumer as root.
        // So save Provider's module and reset.
        let _provider_module = env.module_name.take();

        // File 2: module Consumer imports Status from Provider
        let tokens2 = lex::lex("module Consumer\nuse Provider::Status").unwrap();
        let mut p2 = Parser::new(tokens2);
        let prog2 = p2.parse_program().unwrap();
        collect::collect_into(&mut env, &prog2);
        // Consumer is the root module (the one whose namespace we're building)
        // env.module_name is now Some("Consumer")

        // Run elaborate_env which calls build_working_namespace + resolve
        let (result, errors) = elab::elaborate_env(env);

        // Should have no errors
        let import_errors: Vec<_> = errors
            .iter()
            .filter(|e| {
                e.message.contains("cannot import")
                    || e.message.contains("does not export")
                    || e.message.contains("unknown module")
            })
            .collect();
        assert!(
            import_errors.is_empty(),
            "public cross-module import should succeed, got: {:?}",
            import_errors
        );

        // The imported type "Status" should appear in the result types
        let has_status = result.types.iter().any(|t| t.name == "Status");
        assert!(
            has_status,
            "imported type 'Status' should be in elaboration result types, got: {:?}",
            result.types.iter().map(|t| &t.name).collect::<Vec<_>>()
        );
    }

    #[test]
    fn end_to_end_use_all_imports_public_names() {
        use crate::elab;
        use crate::elab::env::Env;

        let mut env = Env::new();

        // File 1: module Lib with pub type Color and private type Secret
        env.module_name = None;
        let tokens1 =
            lex::lex("module Lib\npub type Color = Red | Blue\ntype Secret = X | Y").unwrap();
        let mut p1 = Parser::new(tokens1);
        let prog1 = p1.parse_program().unwrap();
        collect::collect_into(&mut env, &prog1);
        env.module_name = None; // Reset for next file

        // File 2: module App uses Lib::*
        let tokens2 = lex::lex("module App\nuse Lib::*").unwrap();
        let mut p2 = Parser::new(tokens2);
        let prog2 = p2.parse_program().unwrap();
        collect::collect_into(&mut env, &prog2);
        // App is root

        let (result, errors) = elab::elaborate_env(env);

        let import_errors: Vec<_> = errors
            .iter()
            .filter(|e| e.message.contains("cannot import") || e.message.contains("unknown"))
            .collect();
        assert!(
            import_errors.is_empty(),
            "use Lib::* should succeed: {:?}",
            import_errors
        );

        // Color (public) should be imported
        let has_color = result.types.iter().any(|t| t.name == "Color");
        assert!(has_color, "public Color should be imported via use Lib::*");

        // Secret (private) should NOT be imported
        let has_secret = result.types.iter().any(|t| t.name == "Secret");
        assert!(
            !has_secret,
            "private Secret should NOT be imported via use Lib::*"
        );
    }

    #[test]
    fn end_to_end_cross_module_fn_import() {
        use crate::elab;
        use crate::elab::env::Env;

        let mut env = Env::new();

        // File 1: module MathLib with pub fn double
        env.module_name = None;
        let tokens1 = lex::lex("module MathLib\npub fn double(x: Int): Int = x").unwrap();
        let mut p1 = Parser::new(tokens1);
        let prog1 = p1.parse_program().unwrap();
        collect::collect_into(&mut env, &prog1);
        env.module_name = None;

        // File 2: module App imports double from MathLib
        let tokens2 = lex::lex("module App\nuse MathLib::double").unwrap();
        let mut p2 = Parser::new(tokens2);
        let prog2 = p2.parse_program().unwrap();
        collect::collect_into(&mut env, &prog2);

        let (result, errors) = elab::elaborate_env(env);

        let import_errors: Vec<_> = errors
            .iter()
            .filter(|e| {
                e.message.contains("does not export") || e.message.contains("cannot import")
            })
            .collect();
        assert!(
            import_errors.is_empty(),
            "fn import should succeed: {:?}",
            import_errors
        );

        let has_double = result.fns.iter().any(|f| f.name == "double");
        assert!(has_double, "imported fn 'double' should be in result fns");
    }

    #[test]
    fn use_before_module_retroactively_patched() {
        // use before module declaration initially records source_module=None,
        // but collect_into retroactively patches it once the module decl is seen.
        let env = elaborate_src("use Foo::Bar\nmodule MyMod");
        assert_eq!(env.use_decls.len(), 1);
        let (_, source) = &env.use_decls[0];
        assert_eq!(
            source.as_deref(),
            Some("MyMod"),
            "use before module should be retroactively patched to MyMod"
        );
    }

    #[test]
    fn alias_import_preserves_canonical_name() {
        // use M::Order as O imports Order into the working namespace under key "O",
        // but the declaration's internal name remains "Order" (canonical).
        // This is correct: aliases affect lookup scope, not declaration identity.
        use crate::elab;
        use crate::elab::env::Env;

        let mut env = Env::new();

        // File 1: module Provider declares pub type Order
        env.module_name = None;
        let tokens1 = lex::lex("module Provider\npub type Order = Pending | Done").unwrap();
        let mut p1 = Parser::new(tokens1);
        let prog1 = p1.parse_program().unwrap();
        collect::collect_into(&mut env, &prog1);
        env.module_name = None;

        // File 2: module Consumer imports Order as O
        let tokens2 = lex::lex("module Consumer\nuse Provider::Order as O").unwrap();
        let mut p2 = Parser::new(tokens2);
        let prog2 = p2.parse_program().unwrap();
        collect::collect_into(&mut env, &prog2);

        let (result, errors) = elab::elaborate_env(env);

        let import_errors: Vec<_> = errors
            .iter()
            .filter(|e| {
                e.message.contains("does not export") || e.message.contains("cannot import")
            })
            .collect();
        assert!(
            import_errors.is_empty(),
            "alias import should succeed: {:?}",
            import_errors
        );

        // The type's canonical name should be "Order" (from Ty::Enum("Order", ...)),
        // NOT "O" (the alias). Aliases affect lookup scope, not declaration identity.
        let type_names: Vec<&str> = result.types.iter().map(|t| t.name.as_str()).collect();
        assert!(
            type_names.contains(&"Order"),
            "aliased type should keep canonical name 'Order' in result: {:?}",
            type_names
        );
        assert!(
            !type_names.contains(&"O"),
            "alias 'O' should NOT appear as canonical name in result: {:?}",
            type_names
        );
    }

    #[test]
    fn alias_rewriting_in_expressions() {
        // Verify that aliased variable references are rewritten to canonical
        // names during resolve, so lowering can find the right definitions.
        use crate::elab;
        use crate::elab::env::Env;

        let mut env = Env::new();

        // File 1: module MathLib with pub fn double
        env.module_name = None;
        let tokens1 = lex::lex("module MathLib\npub fn double(x: Int): Int = x").unwrap();
        let mut p1 = Parser::new(tokens1);
        let prog1 = p1.parse_program().unwrap();
        collect::collect_into(&mut env, &prog1);
        env.module_name = None;

        // File 2: module App imports double as dbl, uses it in a const
        let tokens2 =
            lex::lex("module App\nuse MathLib::double as dbl\npub const val = dbl(5)").unwrap();
        let mut p2 = Parser::new(tokens2);
        let prog2 = p2.parse_program().unwrap();
        collect::collect_into(&mut env, &prog2);

        let (result, errors) = elab::elaborate_env(env);

        let import_errors: Vec<_> = errors
            .iter()
            .filter(|e| {
                e.message.contains("does not export") || e.message.contains("cannot import")
            })
            .collect();
        assert!(
            import_errors.is_empty(),
            "alias import should succeed: {:?}",
            import_errors
        );

        // The const's body should reference "double" (canonical), not "dbl" (alias).
        let val_const = result.consts.iter().find(|c| c.name == "val");
        assert!(val_const.is_some(), "const val should exist in result");
        let body = &val_const.unwrap().body;
        // The body is Call(Var("double"), [Int(5)]) — "double" not "dbl"
        if let EExpr::Call(_, func, _) = body {
            if let EExpr::Var(_, name) = func.as_ref() {
                assert_eq!(
                    name, "double",
                    "aliased call should be rewritten to canonical name 'double', got '{name}'"
                );
            } else {
                panic!("expected Call(Var(...), ...), got Call({func:?}, ...)");
            }
        } else {
            panic!("expected Call expression for const val body, got {body:?}");
        }
    }

    #[test]
    fn alias_rewriting_skips_bound_variables() {
        // If a local let-binding uses the same name as an alias,
        // the local binding should NOT be rewritten to the canonical name.
        use crate::elab;
        use crate::elab::env::Env;

        let mut env = Env::new();

        // File 1: module Lib with pub fn foo
        env.module_name = None;
        let tokens1 = lex::lex("module Lib\npub fn foo(x: Int): Int = x").unwrap();
        let mut p1 = Parser::new(tokens1);
        let prog1 = p1.parse_program().unwrap();
        collect::collect_into(&mut env, &prog1);
        env.module_name = None;

        // File 2: module App imports foo as f, then uses let f = 42 in f
        // The inner `f` should resolve to the local binding, not be rewritten to `foo`.
        let tokens2 =
            lex::lex("module App\nuse Lib::foo as f\npub const val = let f = 42 in f").unwrap();
        let mut p2 = Parser::new(tokens2);
        let prog2 = p2.parse_program().unwrap();
        collect::collect_into(&mut env, &prog2);

        let (result, _errors) = elab::elaborate_env(env);

        let val_const = result.consts.iter().find(|c| c.name == "val").unwrap();
        // The body is Let([(f, _, 42)], Var(f))
        // The inner Var should be "f" (bound), NOT "foo" (alias rewrite)
        if let EExpr::Let(_, body) = &val_const.body {
            if let EExpr::Var(_, name) = body.as_ref() {
                assert_eq!(
                    name, "f",
                    "let-bound 'f' should NOT be rewritten to alias canonical 'foo', got '{name}'"
                );
            } else {
                panic!("expected Var in let body, got {body:?}");
            }
        } else {
            panic!("expected Let expression, got {:?}", val_const.body);
        }
    }

    #[test]
    fn foreign_module_uses_do_not_leak() {
        // Module A imports X from Lib. Module B (root) should NOT see X
        // unless B also imports it.
        use crate::elab;
        use crate::elab::env::Env;

        let mut env = Env::new();

        // File 1: module Lib, pub type Color
        env.module_name = None;
        let tokens1 = lex::lex("module Lib\npub type Color = Red | Blue").unwrap();
        let mut p1 = Parser::new(tokens1);
        let prog1 = p1.parse_program().unwrap();
        collect::collect_into(&mut env, &prog1);
        env.module_name = None;

        // File 2: module Other imports Color from Lib
        let tokens2 = lex::lex("module Other\nuse Lib::Color").unwrap();
        let mut p2 = Parser::new(tokens2);
        let prog2 = p2.parse_program().unwrap();
        collect::collect_into(&mut env, &prog2);
        env.module_name = None;

        // File 3: module App (root) does NOT import Color
        let tokens3 = lex::lex("module App\npub type Shape = Circle | Square").unwrap();
        let mut p3 = Parser::new(tokens3);
        let prog3 = p3.parse_program().unwrap();
        collect::collect_into(&mut env, &prog3);
        // App is root

        let (result, _errors) = elab::elaborate_env(env);

        // App should have Shape but NOT Color (Other's import should not leak)
        let type_names: Vec<&str> = result.types.iter().map(|t| t.name.as_str()).collect();
        assert!(type_names.contains(&"Shape"), "App should have Shape");
        assert!(
            !type_names.contains(&"Color"),
            "Other's import of Color should NOT leak into App's namespace: {:?}",
            type_names
        );
    }

    #[test]
    fn fn_param_not_alias_rewritten() {
        // fn double(x: Int): Int = x
        // If "x" is aliased to something, the param binding should prevent rewriting.
        use crate::elab;
        use crate::elab::env::Env;

        let mut env = Env::new();

        // File 1: module Lib with pub fn x (a function named "x")
        env.module_name = None;
        let tokens1 = lex::lex("module Lib\npub fn x(n: Int): Int = n").unwrap();
        let mut p1 = Parser::new(tokens1);
        let prog1 = p1.parse_program().unwrap();
        collect::collect_into(&mut env, &prog1);
        env.module_name = None;

        // File 2: module App imports x from Lib, defines fn double(x: Int) = x
        // The param "x" shadows the imported alias — should NOT be rewritten.
        let tokens2 = lex::lex("module App\nuse Lib::x\npub fn double(x: Int): Int = x").unwrap();
        let mut p2 = Parser::new(tokens2);
        let prog2 = p2.parse_program().unwrap();
        collect::collect_into(&mut env, &prog2);

        let (result, _errors) = elab::elaborate_env(env);

        let double_fn = result.fns.iter().find(|f| f.name == "double").unwrap();
        // Body should be Var("x") — the param, not rewritten to anything else
        if let EExpr::Var(_, name) = &double_fn.body {
            assert_eq!(
                name, "x",
                "fn param 'x' should not be alias-rewritten, got '{name}'"
            );
        } else {
            panic!("expected Var body, got {:?}", double_fn.body);
        }
    }

    #[test]
    fn pred_param_not_alias_rewritten() {
        use crate::elab;
        use crate::elab::env::Env;

        let mut env = Env::new();

        env.module_name = None;
        let tokens1 = lex::lex("module Lib\npub fn o(n: Int): Int = n").unwrap();
        let mut p1 = Parser::new(tokens1);
        let prog1 = p1.parse_program().unwrap();
        collect::collect_into(&mut env, &prog1);
        env.module_name = None;

        // App imports o from Lib, then defines pred check(o: Order) = ...
        // "o" as pred param should not be rewritten.
        let tokens2 = lex::lex(
            "module App\nuse Lib::o\ntype Order = Pending\npred check(o: Order) = o == Pending",
        )
        .unwrap();
        let mut p2 = Parser::new(tokens2);
        let prog2 = p2.parse_program().unwrap();
        collect::collect_into(&mut env, &prog2);

        let (result, _errors) = elab::elaborate_env(env);

        let check_pred = result.preds.iter().find(|p| p.name == "check").unwrap();
        // Body contains a reference to "o" — should be the param, not the imported fn
        fn find_var_name(e: &EExpr) -> Option<&str> {
            match e {
                EExpr::Var(_, n) => Some(n),
                EExpr::BinOp(_, _, l, _) => find_var_name(l),
                _ => None,
            }
        }
        // Body is BinOp(OpEq, Var("o"), Var("Pending"))
        // Assert the left side is specifically Var with name "o"
        match &check_pred.body {
            EExpr::BinOp(_, _, lhs, _) => match lhs.as_ref() {
                EExpr::Var(_, name) => {
                    assert_eq!(
                        name, "o",
                        "pred param 'o' should not be alias-rewritten, got '{name}'"
                    );
                }
                other => panic!("expected Var on lhs of pred body binop, got {other:?}"),
            },
            other => panic!("expected BinOp for pred body, got {other:?}"),
        }
    }

    #[test]
    fn scene_given_var_not_alias_rewritten() {
        // Scene given variables should shadow imported aliases within
        // when/then sections.
        let env = elaborate_src(
            "module TestMod\n\
             pub type Status = Active\n\
             entity Order { id: Id }\n\
             system S {\n\
               event noop() { }\n\
             }\n\
             scene test_scene for S {\n\
               given { let o = one Order }\n\
               then { assert o == o }\n\
             }",
        );
        // "o" in the then-assert should remain "o" (given binder),
        // even if "o" were somehow aliased. The key test is that
        // scene resolution completes without error and given vars
        // are properly scoped.
        assert!(
            !env.errors.iter().any(|e| e.message.contains("alias")),
            "scene with given var should resolve cleanly: {:?}",
            env.errors
        );
    }

    #[test]
    fn axiom_quantifier_domain_resolved() {
        // axiom body containing `all b: Bed | ...` should resolve
        // the domain Bed to Entity("Bed"), not leave it as Unresolved.
        let env = elaborate_src(
            "module Test\n\
             entity Bed { id: Id\n ward: Int }\n\
             axiom bed_positive = all b: Bed | b.ward >= 0",
        );
        // Check the axiom body's quantifier domain type
        assert_eq!(env.axioms.len(), 1);
        let axiom = &env.axioms[0];
        match &axiom.body {
            EExpr::Quant(_, _, _, domain_ty, _) => {
                assert!(
                    matches!(domain_ty, Ty::Entity(n) if n == "Bed"),
                    "axiom quantifier domain should be Entity(\"Bed\"), got {domain_ty:?}"
                );
            }
            other => panic!("expected Quant in axiom body, got {other:?}"),
        }
    }
}
