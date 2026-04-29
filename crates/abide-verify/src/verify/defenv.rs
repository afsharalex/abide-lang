//! Definition environment for fn/pred/prop lookup during Z3 encoding.
//!
//! After lowering, all definitions (fn, pred, prop) are stored uniformly as
//! `IRFunction` in `IRProgram.functions`. This module provides on-demand
//! expansion of definition references during verification encoding.
//!
//! - Props (nullary, return Bool) are expanded when a `Var` reference matches.
//! - Preds (parameterized, return Bool) are expanded when an `App` chain matches.
//! - Fns (general) are expanded the same way as preds.

use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicU64, Ordering};

use crate::ir::types::{IRExpr, IRProgram, IRQuery, IRType};

/// Global counter for generating fresh variable names during alpha-renaming.
static FRESH_COUNTER: AtomicU64 = AtomicU64::new(0);

/// A single definition entry: parameters + body + contracts.
#[derive(Debug, Clone)]
pub struct DefEntry {
    pub params: Vec<(String, IRType)>,
    pub body: IRExpr,
    /// Requires clauses (preconditions). Empty for most preds/props.
    pub requires: Vec<IRExpr>,
}

/// Definition environment built from `IRProgram.functions`, plus the
/// derived field index from `IRProgram.entities` and `IRProgram.systems`.
#[derive(Debug)]
pub struct DefEnv {
    defs: HashMap<String, DefEntry>,
    /// per-entity derived field bodies.
    /// Key: entity name → derived field name → body.
    entity_derived: HashMap<String, HashMap<String, IRExpr>>,
    /// per-entity field name set (regular + derived).
    /// Used during derived-body expansion to decide which bare `Var(name)`
    /// references should be rewritten as `Field(receiver, name,...)`.
    entity_field_names: HashMap<String, HashSet<String>>,
}

/// Semantic classification for the head of an expression-level `App` chain.
///
/// `App` is used for pure application and query evaluation. Operational
/// occurrence is represented elsewhere in IR and should not appear here.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AppHeadKind {
    PureDef,
    Query,
}

impl DefEnv {
    /// Build a definition environment from the IR program. Walks
    /// functions, entities, and systems.
    pub fn from_ir(program: &IRProgram) -> Self {
        let mut defs = HashMap::new();
        for f in &program.functions {
            let (params, body) = uncurry(&f.body);
            defs.insert(
                f.name.clone(),
                DefEntry {
                    params,
                    body,
                    requires: f.requires.clone(),
                },
            );
        }

        // index entity-level derived fields and
        // entity field name sets for derived-body expansion.
        let mut entity_derived: HashMap<String, HashMap<String, IRExpr>> = HashMap::new();
        let mut entity_field_names: HashMap<String, HashSet<String>> = HashMap::new();
        for ent in &program.entities {
            let mut names: HashSet<String> = ent.fields.iter().map(|f| f.name.clone()).collect();
            let mut derived_map: HashMap<String, IRExpr> = HashMap::new();
            for d in &ent.derived_fields {
                names.insert(d.name.clone());
                derived_map.insert(d.name.clone(), d.body.clone());
            }
            if !derived_map.is_empty() {
                entity_derived.insert(ent.name.clone(), derived_map);
            }
            entity_field_names.insert(ent.name.clone(), names);
        }

        // system-level derived fields are
        // nullary, so they slot into the existing `defs` map and
        // are expanded by `expand_var` (mirroring `prop` expansion).
        for sys in &program.systems {
            for d in &sys.derived_fields {
                defs.insert(
                    d.name.clone(),
                    DefEntry {
                        params: vec![],
                        body: d.body.clone(),
                        requires: vec![],
                    },
                );
            }
        }

        // Load axioms as trusted facts into the definition environment.
        for axiom in &program.axioms {
            defs.insert(
                axiom.name.clone(),
                DefEntry {
                    params: vec![],
                    body: axiom.body.clone(),
                    requires: vec![],
                },
            );
        }

        // Load system queries into the definition environment.
        // Register only under qualified name. Bare references in step
        // guards/bodies are rewritten to qualified form during IR lowering.
        for sys in &program.systems {
            for q in &sys.queries {
                let entry = DefEntry {
                    params: q
                        .params
                        .iter()
                        .map(|p| (p.name.clone(), p.ty.clone()))
                        .collect(),
                    body: q.body.clone(),
                    requires: vec![],
                };
                defs.insert(format!("{}::{}", sys.name, q.name), entry);
            }
            // load system-local preds into DefEnv under qualified names.
            for p in &sys.preds {
                let (params, body) = uncurry(&p.body);
                defs.insert(
                    format!("{}::{}", sys.name, p.name),
                    DefEntry {
                        params,
                        body,
                        requires: p.requires.clone(),
                    },
                );
            }
        }

        Self {
            defs,
            entity_derived,
            entity_field_names,
        }
    }

    /// try to expand a `Field { expr: receiver, field: name }`
    /// reference as an entity-level derived field. Returns `Some(body)` with
    /// bare field references in the body rewritten to `Field(receiver,...)`
    /// if `field_name` is a derived field on `receiver`'s entity type.
    pub fn expand_entity_derived(&self, receiver: &IRExpr, field_name: &str) -> Option<IRExpr> {
        let entity_name = entity_type_of(receiver)?;
        let derived = self.entity_derived.get(&entity_name)?;
        let body = derived.get(field_name)?.clone();
        let field_set = self.entity_field_names.get(&entity_name)?;
        Some(rewrite_self_field_refs(body, receiver, field_set))
    }

    /// Rewrite an entity invariant body so that bare `Var(field)`
    /// references resolve against `receiver`. Used by the verifier when
    /// wrapping each entity invariant in a per-instance `Forall` for
    /// encoding. The walker is binder-aware so local
    /// lets/quantifiers/lambdas inside the invariant body are not
    /// clobbered.
    ///
    /// Returns the rewritten body if `entity_name` is a known entity
    /// in the IR; otherwise returns the body unchanged (the verifier
    /// will encode it as-is, which is a no-op for invariants that
    /// don't reference any fields).
    pub fn rewrite_entity_invariant_body(
        &self,
        body: IRExpr,
        receiver: &IRExpr,
        entity_name: &str,
    ) -> IRExpr {
        match self.entity_field_names.get(entity_name) {
            Some(field_set) => rewrite_self_field_refs(body, receiver, field_set),
            None => body,
        }
    }

    /// Look up a definition by name.
    pub fn get(&self, name: &str) -> Option<&DefEntry> {
        self.defs.get(name)
    }

    /// Add a proved lemma body expression as a trusted fact.
    ///
    /// Stored under the lemma's declared name so that later theorems and verify
    /// blocks can reference it directly (e.g., `show helper` references a lemma
    /// named `helper`). For multi-expression lemma bodies, the conjunction of
    /// all expressions is stored as a single entry.
    pub fn add_lemma_fact(&mut self, lemma_name: &str, exprs: &[IRExpr]) {
        let body = if exprs.len() == 1 {
            exprs[0].clone()
        } else {
            // Conjoin multiple body expressions into one
            let mut result = exprs[0].clone();
            for expr in &exprs[1..] {
                result = IRExpr::BinOp {
                    op: "OpAnd".to_owned(),
                    left: Box::new(result),
                    right: Box::new(expr.clone()),
                    ty: crate::ir::types::IRType::Bool,
                    span: None,
                };
            }
            result
        };
        self.defs.insert(
            lemma_name.to_owned(),
            DefEntry {
                params: vec![],
                body,
                requires: vec![],
            },
        );
    }

    /// Try to expand a `Var` reference. Returns `Some(body)` for nullary defs (props).
    pub fn expand_var(&self, name: &str) -> Option<IRExpr> {
        let entry = self.defs.get(name)?;
        if entry.params.is_empty() {
            Some(entry.body.clone())
        } else {
            None // parameterized def — needs App to supply args
        }
    }

    /// Try to expand an `App` chain. Decomposes the chain, looks up the def,
    /// and performs beta-reduction if arity matches.
    pub fn expand_app(&self, expr: &IRExpr) -> Option<IRExpr> {
        let (name, args) = decompose_app_chain(expr)?;
        let entry = self.defs.get(&name)?;
        if entry.params.len() != args.len() {
            return None; // arity mismatch — not a full application
        }
        Some(substitute_all(&entry.body, &entry.params, &args))
    }

    /// Get the substituted preconditions for a function call.
    ///
    /// For `f(a, b)` where `f` has `requires P(x, y)`, returns `[P(a, b)]`
    /// with actual arguments substituted for formal parameters.
    /// Returns `None` if the expression is not a recognized call, or `Some(vec![])`
    /// if the function has no requires clauses.
    pub fn call_preconditions(&self, expr: &IRExpr) -> Option<Vec<IRExpr>> {
        let (name, args) = decompose_app_chain(expr)?;
        let entry = self.defs.get(&name)?;
        if entry.params.len() != args.len() {
            return None;
        }
        if entry.requires.is_empty() {
            return Some(vec![]);
        }
        let preconditions = entry
            .requires
            .iter()
            .map(|req| substitute_all(req, &entry.params, &args))
            .collect();
        Some(preconditions)
    }
}

/// extract the entity name from an expression's
/// embedded type, if the expression has an entity type. Used by the
/// derived field expansion to look up the entity's derived field map.
///
/// Handles the common cases: `Var { ty: Entity }`, `Field { ty: Entity }`,
/// chained field accesses, and other expression forms whose `ty` is an
/// `IRType::Entity`. Returns `None` for non-entity expressions.
fn entity_type_of(expr: &IRExpr) -> Option<String> {
    match expr {
        IRExpr::Var {
            ty: IRType::Entity { name },
            ..
        }
        | IRExpr::Field {
            ty: IRType::Entity { name },
            ..
        } => Some(name.clone()),
        _ => None,
    }
}

/// rewrite a derived field's body so that bare
/// `Var(name)` references to entity fields become `Field { expr: receiver, field: name,... }`.
///
/// Walks the expression tree exhaustively. A `Var(name)` is rewritten
/// only when `name` is in the entity's `field_names` set AND not
/// shadowed by an enclosing binder (lambda, let, forall/exists/one/lone,
/// match arm pattern). Other Vars (top-level fns, constants) stay
/// untouched. The walker preserves the existing `ty` annotation on the
/// Var since the body was already type-checked at elab time.
///
/// must track binders. A derived body like
/// `let status =... in status` (where the entity has a `status` field)
/// would otherwise be rewritten to `let status =... in receiver.status`,
/// changing the meaning. This walker mirrors `free_vars_inner`'s
/// binder-tracking pattern.
fn rewrite_self_field_refs(
    expr: IRExpr,
    receiver: &IRExpr,
    field_names: &HashSet<String>,
) -> IRExpr {
    let mut bound: HashSet<String> = HashSet::new();
    rewrite_self_field_refs_inner(expr, receiver, field_names, &mut bound)
}

fn rewrite_self_field_refs_inner(
    expr: IRExpr,
    receiver: &IRExpr,
    field_names: &HashSet<String>,
    bound: &mut HashSet<String>,
) -> IRExpr {
    match expr {
        IRExpr::Var { name, ty, span } if field_names.contains(&name) && !bound.contains(&name) => {
            IRExpr::Field {
                expr: Box::new(receiver.clone()),
                field: name,
                ty,
                span,
            }
        }
        IRExpr::Var { .. }
        | IRExpr::Lit { .. }
        | IRExpr::Ctor { .. }
        | IRExpr::Sorry { .. }
        | IRExpr::Todo { .. } => expr,
        IRExpr::Field {
            expr: inner,
            field,
            ty,
            ..
        } => IRExpr::Field {
            expr: Box::new(rewrite_self_field_refs_inner(
                *inner,
                receiver,
                field_names,
                bound,
            )),
            field,
            ty,
            span: None,
        },
        IRExpr::BinOp {
            op,
            left,
            right,
            ty,
            ..
        } => IRExpr::BinOp {
            op,
            left: Box::new(rewrite_self_field_refs_inner(
                *left,
                receiver,
                field_names,
                bound,
            )),
            right: Box::new(rewrite_self_field_refs_inner(
                *right,
                receiver,
                field_names,
                bound,
            )),
            ty,
            span: None,
        },
        IRExpr::UnOp {
            op, operand, ty, ..
        } => IRExpr::UnOp {
            op,
            operand: Box::new(rewrite_self_field_refs_inner(
                *operand,
                receiver,
                field_names,
                bound,
            )),
            ty,
            span: None,
        },
        IRExpr::App { func, arg, ty, .. } => IRExpr::App {
            func: Box::new(rewrite_self_field_refs_inner(
                *func,
                receiver,
                field_names,
                bound,
            )),
            arg: Box::new(rewrite_self_field_refs_inner(
                *arg,
                receiver,
                field_names,
                bound,
            )),
            ty,
            span: None,
        },
        // lambda parameter binds in body.
        IRExpr::Lam {
            param,
            param_type,
            body,
            ..
        } => {
            let was_new = bound.insert(param.clone());
            let new_body = rewrite_self_field_refs_inner(*body, receiver, field_names, bound);
            if was_new {
                bound.remove(&param);
            }
            IRExpr::Lam {
                param,
                param_type,
                body: Box::new(new_body),
                span: None,
            }
        }
        // each `let` binding's RHS sees
        // the prior scope; subsequent bindings and the body see the
        // new name as bound (shadowed).
        IRExpr::Let { bindings, body, .. } => {
            let mut added: Vec<String> = Vec::new();
            let new_bindings: Vec<crate::ir::types::LetBinding> = bindings
                .into_iter()
                .map(|b| {
                    let new_expr =
                        rewrite_self_field_refs_inner(b.expr, receiver, field_names, bound);
                    if bound.insert(b.name.clone()) {
                        added.push(b.name.clone());
                    }
                    crate::ir::types::LetBinding {
                        name: b.name,
                        ty: b.ty,
                        expr: new_expr,
                    }
                })
                .collect();
            let new_body = rewrite_self_field_refs_inner(*body, receiver, field_names, bound);
            for name in added {
                bound.remove(&name);
            }
            IRExpr::Let {
                bindings: new_bindings,
                body: Box::new(new_body),
                span: None,
            }
        }
        // quantifier variables bind in body.
        IRExpr::Forall {
            var, domain, body, ..
        } => {
            let was_new = bound.insert(var.clone());
            let new_body = rewrite_self_field_refs_inner(*body, receiver, field_names, bound);
            if was_new {
                bound.remove(&var);
            }
            IRExpr::Forall {
                var,
                domain,
                body: Box::new(new_body),
                span: None,
            }
        }
        IRExpr::Exists {
            var, domain, body, ..
        } => {
            let was_new = bound.insert(var.clone());
            let new_body = rewrite_self_field_refs_inner(*body, receiver, field_names, bound);
            if was_new {
                bound.remove(&var);
            }
            IRExpr::Exists {
                var,
                domain,
                body: Box::new(new_body),
                span: None,
            }
        }
        IRExpr::One {
            var, domain, body, ..
        } => {
            let was_new = bound.insert(var.clone());
            let new_body = rewrite_self_field_refs_inner(*body, receiver, field_names, bound);
            if was_new {
                bound.remove(&var);
            }
            IRExpr::One {
                var,
                domain,
                body: Box::new(new_body),
                span: None,
            }
        }
        IRExpr::Lone {
            var, domain, body, ..
        } => {
            let was_new = bound.insert(var.clone());
            let new_body = rewrite_self_field_refs_inner(*body, receiver, field_names, bound);
            if was_new {
                bound.remove(&var);
            }
            IRExpr::Lone {
                var,
                domain,
                body: Box::new(new_body),
                span: None,
            }
        }
        IRExpr::Always { body, .. } => IRExpr::Always {
            body: Box::new(rewrite_self_field_refs_inner(
                *body,
                receiver,
                field_names,
                bound,
            )),
            span: None,
        },
        IRExpr::Eventually { body, .. } => IRExpr::Eventually {
            body: Box::new(rewrite_self_field_refs_inner(
                *body,
                receiver,
                field_names,
                bound,
            )),
            span: None,
        },
        IRExpr::Until { left, right, .. } => IRExpr::Until {
            left: Box::new(rewrite_self_field_refs_inner(
                *left,
                receiver,
                field_names,
                bound,
            )),
            right: Box::new(rewrite_self_field_refs_inner(
                *right,
                receiver,
                field_names,
                bound,
            )),
            span: None,
        },
        // / — past-time temporal operators.
        IRExpr::Historically { body, .. } => IRExpr::Historically {
            body: Box::new(rewrite_self_field_refs_inner(
                *body,
                receiver,
                field_names,
                bound,
            )),
            span: None,
        },
        IRExpr::Once { body, .. } => IRExpr::Once {
            body: Box::new(rewrite_self_field_refs_inner(
                *body,
                receiver,
                field_names,
                bound,
            )),
            span: None,
        },
        IRExpr::Previously { body, .. } => IRExpr::Previously {
            body: Box::new(rewrite_self_field_refs_inner(
                *body,
                receiver,
                field_names,
                bound,
            )),
            span: None,
        },
        IRExpr::Since { left, right, .. } => IRExpr::Since {
            left: Box::new(rewrite_self_field_refs_inner(
                *left,
                receiver,
                field_names,
                bound,
            )),
            right: Box::new(rewrite_self_field_refs_inner(
                *right,
                receiver,
                field_names,
                bound,
            )),
            span: None,
        },
        IRExpr::Prime { expr: inner, .. } => IRExpr::Prime {
            expr: Box::new(rewrite_self_field_refs_inner(
                *inner,
                receiver,
                field_names,
                bound,
            )),
            span: None,
        },
        // match arm patterns introduce
        // new names that shadow outer references in the arm body and
        // guard.
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            let new_scrutinee = Box::new(rewrite_self_field_refs_inner(
                *scrutinee,
                receiver,
                field_names,
                bound,
            ));
            let new_arms: Vec<crate::ir::types::IRMatchArm> = arms
                .into_iter()
                .map(|arm| {
                    let mut pat_names: Vec<String> = Vec::new();
                    collect_ir_pattern_names(&arm.pattern, &mut pat_names);
                    let mut added: Vec<String> = Vec::new();
                    for name in &pat_names {
                        if bound.insert(name.clone()) {
                            added.push(name.clone());
                        }
                    }
                    let new_guard = arm
                        .guard
                        .map(|g| rewrite_self_field_refs_inner(g, receiver, field_names, bound));
                    let new_body =
                        rewrite_self_field_refs_inner(arm.body, receiver, field_names, bound);
                    for name in added {
                        bound.remove(&name);
                    }
                    crate::ir::types::IRMatchArm {
                        pattern: arm.pattern,
                        guard: new_guard,
                        body: new_body,
                    }
                })
                .collect();
            IRExpr::Match {
                scrutinee: new_scrutinee,
                arms: new_arms,
                span: None,
            }
        }
        // For other variants, fall back to a deep clone. If a new
        // IRExpr variant with field references is added later, the
        // compiler won't catch it here — but it will be caught by
        // the broader free_vars_inner walker which is exhaustive.
        other => other,
    }
}

/// walk an `IRPattern` and collect all
/// `PVar`-bound names that the pattern introduces. Used by the
/// binder-tracking rewriter so match arm pattern variables shadow
/// outer references.
fn collect_ir_pattern_names(pat: &crate::ir::types::IRPattern, into: &mut Vec<String>) {
    use crate::ir::types::IRPattern;
    match pat {
        IRPattern::PVar { name } => into.push(name.clone()),
        IRPattern::PWild => {}
        IRPattern::PCtor { fields, .. } => {
            for f in fields {
                collect_ir_pattern_names(&f.pattern, into);
            }
        }
        IRPattern::POr { left, right } => {
            collect_ir_pattern_names(left, into);
            collect_ir_pattern_names(right, into);
        }
    }
}

/// Peel off `Lam` wrappers to extract parameter list and innermost body.
///
/// `Lam(x, T, Lam(y, U, body))` → `[(x, T), (y, U)]`, `body`
fn uncurry(expr: &IRExpr) -> (Vec<(String, IRType)>, IRExpr) {
    let mut params = Vec::new();
    let mut current = expr;
    while let IRExpr::Lam {
        param,
        param_type,
        body,
        ..
    } = current
    {
        params.push((param.clone(), param_type.clone()));
        current = body;
    }
    (params, current.clone())
}

/// Extract the function name from an `App` chain (without decomposing args).
///
/// `App(App(Var("f"), a1), a2)` → `Some("f")`
pub fn decompose_app_chain_name(expr: &IRExpr) -> Option<String> {
    let mut current = expr;
    while let IRExpr::App { func, .. } = current {
        current = func.as_ref();
    }
    if let IRExpr::Var { name, .. } = current {
        Some(name.clone())
    } else {
        None
    }
}

/// Decompose a curried `App` chain into the function name and argument list (public).
///
/// `App(App(Var("p"), a1), a2)` → `Some(("p", [a1, a2]))`
pub fn decompose_app_chain_public(expr: &IRExpr) -> Option<(String, Vec<IRExpr>)> {
    decompose_app_chain(expr)
}

/// Classify a curried `App` chain as a pure definition call or a query call.
///
/// `current_system` is used to resolve bare query names in contexts where the
/// ambient system is known (for example slot-scoped guard encoding).
pub fn classify_app_chain_public(
    defs: &DefEnv,
    expr: &IRExpr,
    current_system: Option<&str>,
    system_queries: &HashMap<(String, String), IRQuery>,
) -> Option<(AppHeadKind, String, Vec<IRExpr>)> {
    let (head, args) = decompose_app_chain(expr)?;

    if let Some((system, query)) = head.split_once("::") {
        let full_name = format!("{system}::{query}");
        if system_queries.contains_key(&(system.to_owned(), query.to_owned())) {
            return Some((AppHeadKind::Query, full_name, args));
        }
        if defs.get(&full_name).is_some() {
            return Some((AppHeadKind::PureDef, full_name, args));
        }
        return None;
    }

    if let Some(system_name) = current_system {
        if system_queries.contains_key(&(system_name.to_owned(), head.clone())) {
            return Some((AppHeadKind::Query, format!("{system_name}::{head}"), args));
        }
    }

    if defs.get(&head).is_some() {
        return Some((AppHeadKind::PureDef, head, args));
    }

    None
}

/// Decompose a curried `App` chain into the function name and argument list.
///
/// `App(App(Var("p"), a1), a2)` → `Some(("p", [a1, a2]))`
fn decompose_app_chain(expr: &IRExpr) -> Option<(String, Vec<IRExpr>)> {
    let mut args = Vec::new();
    let mut current = expr;
    while let IRExpr::App { func, arg, .. } = current {
        args.push(arg.as_ref().clone());
        current = func.as_ref();
    }
    args.reverse();
    if let IRExpr::Var { name, .. } = current {
        if args.is_empty() {
            return None; // bare Var, not an App chain
        }
        Some((name.clone(), args))
    } else {
        None // head is not a Var
    }
}

/// Beta-reduce: substitute all parameters with arguments in body.
fn substitute_all(body: &IRExpr, params: &[(String, IRType)], args: &[IRExpr]) -> IRExpr {
    let mut result = body.clone();
    for (i, (param_name, _)) in params.iter().enumerate() {
        result = substitute_var(result, param_name, &args[i]);
    }
    result
}

/// Generate a fresh variable name that won't collide with existing names.
fn fresh_name(base: &str) -> String {
    let n = FRESH_COUNTER.fetch_add(1, Ordering::Relaxed);
    format!("{base}${n}")
}

/// Collect free variables in an expression (names not bound by any enclosing binder).
fn free_vars(expr: &IRExpr) -> HashSet<String> {
    let mut fv = HashSet::new();
    free_vars_inner(expr, &mut HashSet::new(), &mut fv);
    fv
}

#[allow(clippy::too_many_lines)]
fn free_vars_inner(expr: &IRExpr, bound: &mut HashSet<String>, fv: &mut HashSet<String>) {
    match expr {
        IRExpr::Var { name, .. } => {
            if !bound.contains(name) {
                fv.insert(name.clone());
            }
        }
        IRExpr::Lit { .. } | IRExpr::Ctor { .. } | IRExpr::Sorry { .. } | IRExpr::Todo { .. } => {}
        IRExpr::Field { expr, .. } | IRExpr::Card { expr, .. } => free_vars_inner(expr, bound, fv),
        IRExpr::BinOp { left, right, .. }
        | IRExpr::Until { left, right, .. }
        | IRExpr::Since { left, right, .. } => {
            free_vars_inner(left, bound, fv);
            free_vars_inner(right, bound, fv);
        }
        IRExpr::UnOp { operand, .. } => free_vars_inner(operand, bound, fv),
        IRExpr::App { func, arg, .. } => {
            free_vars_inner(func, bound, fv);
            free_vars_inner(arg, bound, fv);
        }
        IRExpr::Lam { param, body, .. } => {
            let was_new = bound.insert(param.clone());
            free_vars_inner(body, bound, fv);
            if was_new {
                bound.remove(param);
            }
        }
        IRExpr::Let { bindings, body, .. } => {
            let mut added = Vec::new();
            for b in bindings {
                free_vars_inner(&b.expr, bound, fv);
                if bound.insert(b.name.clone()) {
                    added.push(b.name.clone());
                }
            }
            free_vars_inner(body, bound, fv);
            for name in added {
                bound.remove(&name);
            }
        }
        IRExpr::Forall { var, body, .. }
        | IRExpr::Exists { var, body, .. }
        | IRExpr::One { var, body, .. }
        | IRExpr::Lone { var, body, .. } => {
            let was_new = bound.insert(var.clone());
            free_vars_inner(body, bound, fv);
            if was_new {
                bound.remove(var);
            }
        }
        IRExpr::Choose { var, predicate, .. } => {
            let was_new = bound.insert(var.clone());
            if let Some(pred) = predicate {
                free_vars_inner(pred, bound, fv);
            }
            if was_new {
                bound.remove(var);
            }
        }
        IRExpr::Always { body, .. }
        | IRExpr::Eventually { body, .. }
        | IRExpr::Historically { body, .. }
        | IRExpr::Once { body, .. }
        | IRExpr::Previously { body, .. }
        | IRExpr::Prime { expr: body, .. }
        | IRExpr::Assert { expr: body, .. }
        | IRExpr::Assume { expr: body, .. } => {
            free_vars_inner(body, bound, fv);
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            free_vars_inner(scrutinee, bound, fv);
            for arm in arms {
                let mut arm_bound = bound.clone();
                collect_pattern_vars(&arm.pattern, &mut arm_bound);
                if let Some(g) = &arm.guard {
                    free_vars_inner(g, &mut arm_bound, fv);
                }
                free_vars_inner(&arm.body, &mut arm_bound, fv);
            }
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            free_vars_inner(map, bound, fv);
            free_vars_inner(key, bound, fv);
            free_vars_inner(value, bound, fv);
        }
        IRExpr::Index { map, key, .. } => {
            free_vars_inner(map, bound, fv);
            free_vars_inner(key, bound, fv);
        }
        IRExpr::SetComp {
            var,
            filter,
            projection,
            ..
        } => {
            let was_new = bound.insert(var.clone());
            free_vars_inner(filter, bound, fv);
            if let Some(p) = projection {
                free_vars_inner(p, bound, fv);
            }
            if was_new {
                bound.remove(var);
            }
        }
        IRExpr::SetLit { elements, .. } | IRExpr::SeqLit { elements, .. } => {
            for e in elements {
                free_vars_inner(e, bound, fv);
            }
        }
        IRExpr::MapLit { entries, .. } => {
            for (k, v) in entries {
                free_vars_inner(k, bound, fv);
                free_vars_inner(v, bound, fv);
            }
        }
        IRExpr::Block { exprs, .. } => {
            for e in exprs {
                free_vars_inner(e, bound, fv);
            }
        }
        IRExpr::VarDecl {
            name, init, rest, ..
        } => {
            free_vars_inner(init, bound, fv);
            let was_new = bound.insert(name.clone());
            free_vars_inner(rest, bound, fv);
            if was_new {
                bound.remove(name);
            }
        }
        IRExpr::While {
            cond,
            invariants,
            body,
            ..
        } => {
            free_vars_inner(cond, bound, fv);
            for inv in invariants {
                free_vars_inner(inv, bound, fv);
            }
            free_vars_inner(body, bound, fv);
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            free_vars_inner(cond, bound, fv);
            free_vars_inner(then_body, bound, fv);
            if let Some(eb) = else_body {
                free_vars_inner(eb, bound, fv);
            }
        }
        // / — aggregate: var is bound in body.
        IRExpr::Aggregate {
            var,
            body,
            in_filter,
            ..
        } => {
            let was_new = bound.insert(var.clone());
            free_vars_inner(body, bound, fv);
            if let Some(f) = in_filter {
                free_vars_inner(f, bound, fv);
            }
            if was_new {
                bound.remove(var);
            }
        }
        // / — saw operator: recurse into non-wildcard args.
        IRExpr::Saw { args, .. } => {
            for e in args.iter().flatten() {
                free_vars_inner(e, bound, fv);
            }
        }
    }
}

/// Capture-avoiding substitution: replace all free occurrences of `Var(var_name)`
/// with `replacement` in `expr`. Alpha-renames binders when replacement contains
/// free variables that would be captured.
fn substitute_var(expr: IRExpr, var_name: &str, replacement: &IRExpr) -> IRExpr {
    // Cache free vars of replacement — needed for capture checks at binders.
    let repl_fv = free_vars(replacement);
    substitute_var_inner(expr, var_name, replacement, &repl_fv)
}

#[allow(clippy::too_many_lines)]
fn substitute_var_inner(
    expr: IRExpr,
    var_name: &str,
    replacement: &IRExpr,
    repl_fv: &HashSet<String>,
) -> IRExpr {
    match expr {
        IRExpr::Var { ref name, .. } if name == var_name => replacement.clone(),
        IRExpr::Var { .. }
        | IRExpr::Lit { .. }
        | IRExpr::Ctor { .. }
        | IRExpr::Sorry { .. }
        | IRExpr::Todo { .. } => expr,
        IRExpr::Field {
            expr: inner,
            field,
            ty,
            ..
        } => IRExpr::Field {
            expr: Box::new(substitute_var_inner(*inner, var_name, replacement, repl_fv)),
            field,
            ty,
            span: None,
        },
        IRExpr::BinOp {
            op,
            left,
            right,
            ty,
            ..
        } => IRExpr::BinOp {
            op,
            left: Box::new(substitute_var_inner(*left, var_name, replacement, repl_fv)),
            right: Box::new(substitute_var_inner(*right, var_name, replacement, repl_fv)),
            ty,
            span: None,
        },
        IRExpr::UnOp {
            op, operand, ty, ..
        } => IRExpr::UnOp {
            op,
            operand: Box::new(substitute_var_inner(
                *operand,
                var_name,
                replacement,
                repl_fv,
            )),
            ty,
            span: None,
        },
        IRExpr::App { func, arg, ty, .. } => IRExpr::App {
            func: Box::new(substitute_var_inner(*func, var_name, replacement, repl_fv)),
            arg: Box::new(substitute_var_inner(*arg, var_name, replacement, repl_fv)),
            ty,
            span: None,
        },
        IRExpr::Lam {
            param,
            param_type,
            body,
            ..
        } => {
            if param == var_name {
                // Shadowed — don't substitute into body
                IRExpr::Lam {
                    param,
                    param_type,
                    body,
                    span: None,
                }
            } else if repl_fv.contains(&param) {
                // Capture risk: binder name appears free in replacement.
                // Alpha-rename: Lam(x, body) → Lam(x', body[x:= Var(x')])
                let fresh = fresh_name(&param);
                let fresh_var = IRExpr::Var {
                    name: fresh.clone(),
                    ty: param_type.clone(),
                    span: None,
                };
                let renamed_body =
                    substitute_var_inner(*body, &param, &fresh_var, &free_vars(&fresh_var));
                IRExpr::Lam {
                    param: fresh,
                    param_type,
                    body: Box::new(substitute_var_inner(
                        renamed_body,
                        var_name,
                        replacement,
                        repl_fv,
                    )),
                    span: None,
                }
            } else {
                IRExpr::Lam {
                    param,
                    param_type,
                    body: Box::new(substitute_var_inner(*body, var_name, replacement, repl_fv)),
                    span: None,
                }
            }
        }
        IRExpr::Choose {
            var,
            domain,
            predicate,
            ty,
            ..
        } => {
            if var == var_name {
                IRExpr::Choose {
                    var,
                    domain,
                    predicate,
                    ty,
                    span: None,
                }
            } else if repl_fv.contains(&var) {
                let fresh = fresh_name(&var);
                let fresh_var = IRExpr::Var {
                    name: fresh.clone(),
                    ty: domain.clone(),
                    span: None,
                };
                let renamed_predicate = predicate.map(|pred| {
                    Box::new(substitute_var_inner(
                        *pred,
                        &var,
                        &fresh_var,
                        &free_vars(&fresh_var),
                    ))
                });
                IRExpr::Choose {
                    var: fresh,
                    domain,
                    predicate: renamed_predicate.map(|pred| {
                        Box::new(substitute_var_inner(*pred, var_name, replacement, repl_fv))
                    }),
                    ty,
                    span: None,
                }
            } else {
                IRExpr::Choose {
                    var,
                    domain,
                    predicate: predicate.map(|pred| {
                        Box::new(substitute_var_inner(*pred, var_name, replacement, repl_fv))
                    }),
                    ty,
                    span: None,
                }
            }
        }
        IRExpr::Let { bindings, body, .. } => {
            let mut shadowed = false;
            let mut needs_rename = false;
            // Check if any binding name appears free in replacement
            for b in &bindings {
                if b.name == var_name {
                    break; // will shadow before we need to worry about capture
                }
                if repl_fv.contains(&b.name) {
                    needs_rename = true;
                    break;
                }
            }
            if needs_rename {
                // Alpha-rename conflicting let bindings
                let mut renamed_bindings = Vec::new();
                let mut renames: Vec<(String, String)> = Vec::new();
                let mut current_body = *body;

                for b in bindings {
                    let new_name = if repl_fv.contains(&b.name) && b.name != var_name {
                        let fresh = fresh_name(&b.name);
                        renames.push((b.name.clone(), fresh.clone()));
                        fresh
                    } else {
                        b.name.clone()
                    };

                    let mut new_expr = b.expr;
                    // Apply prior renames to this binding's expr
                    for (old, new) in &renames {
                        if old != &b.name {
                            let fresh_var = IRExpr::Var {
                                name: new.clone(),
                                ty: b.ty.clone(),
                                span: None,
                            };
                            new_expr = substitute_var_inner(
                                new_expr,
                                old,
                                &fresh_var,
                                &free_vars(&fresh_var),
                            );
                        }
                    }

                    if !shadowed {
                        new_expr = substitute_var_inner(new_expr, var_name, replacement, repl_fv);
                    }
                    if b.name == var_name {
                        shadowed = true;
                    }

                    renamed_bindings.push(crate::ir::types::LetBinding {
                        name: new_name,
                        ty: b.ty,
                        expr: new_expr,
                    });
                }

                // Apply renames to body
                for (old, new) in &renames {
                    let fresh_var = IRExpr::Var {
                        name: new.clone(),
                        ty: IRType::Int, // type doesn't matter for name substitution
                        span: None,
                    };
                    current_body =
                        substitute_var_inner(current_body, old, &fresh_var, &free_vars(&fresh_var));
                }
                if !shadowed {
                    current_body =
                        substitute_var_inner(current_body, var_name, replacement, repl_fv);
                }

                IRExpr::Let {
                    bindings: renamed_bindings,
                    body: Box::new(current_body),
                    span: None,
                }
            } else {
                let new_bindings = bindings
                    .into_iter()
                    .map(|b| {
                        let new_expr = if shadowed {
                            b.expr
                        } else {
                            substitute_var_inner(b.expr, var_name, replacement, repl_fv)
                        };
                        if b.name == var_name {
                            shadowed = true;
                        }
                        crate::ir::types::LetBinding {
                            name: b.name,
                            ty: b.ty,
                            expr: new_expr,
                        }
                    })
                    .collect();
                IRExpr::Let {
                    bindings: new_bindings,
                    span: None,
                    body: if shadowed {
                        body
                    } else {
                        Box::new(substitute_var_inner(*body, var_name, replacement, repl_fv))
                    },
                }
            }
        }
        IRExpr::Forall {
            var, domain, body, ..
        } => subst_quantifier(
            var,
            domain,
            body,
            var_name,
            replacement,
            repl_fv,
            QuantTag::Forall,
        ),
        IRExpr::Exists {
            var, domain, body, ..
        } => subst_quantifier(
            var,
            domain,
            body,
            var_name,
            replacement,
            repl_fv,
            QuantTag::Exists,
        ),
        IRExpr::One {
            var, domain, body, ..
        } => subst_quantifier(
            var,
            domain,
            body,
            var_name,
            replacement,
            repl_fv,
            QuantTag::One,
        ),
        IRExpr::Lone {
            var, domain, body, ..
        } => subst_quantifier(
            var,
            domain,
            body,
            var_name,
            replacement,
            repl_fv,
            QuantTag::Lone,
        ),
        IRExpr::Always { body, .. } => IRExpr::Always {
            body: Box::new(substitute_var_inner(*body, var_name, replacement, repl_fv)),
            span: None,
        },
        IRExpr::Eventually { body, .. } => IRExpr::Eventually {
            body: Box::new(substitute_var_inner(*body, var_name, replacement, repl_fv)),
            span: None,
        },
        IRExpr::Until { left, right, .. } => IRExpr::Until {
            left: Box::new(substitute_var_inner(*left, var_name, replacement, repl_fv)),
            right: Box::new(substitute_var_inner(*right, var_name, replacement, repl_fv)),
            span: None,
        },
        // / — past-time temporal operators.
        IRExpr::Historically { body, .. } => IRExpr::Historically {
            body: Box::new(substitute_var_inner(*body, var_name, replacement, repl_fv)),
            span: None,
        },
        IRExpr::Once { body, .. } => IRExpr::Once {
            body: Box::new(substitute_var_inner(*body, var_name, replacement, repl_fv)),
            span: None,
        },
        IRExpr::Previously { body, .. } => IRExpr::Previously {
            body: Box::new(substitute_var_inner(*body, var_name, replacement, repl_fv)),
            span: None,
        },
        IRExpr::Since { left, right, .. } => IRExpr::Since {
            left: Box::new(substitute_var_inner(*left, var_name, replacement, repl_fv)),
            right: Box::new(substitute_var_inner(*right, var_name, replacement, repl_fv)),
            span: None,
        },
        IRExpr::Prime { expr, .. } => IRExpr::Prime {
            expr: Box::new(substitute_var_inner(*expr, var_name, replacement, repl_fv)),
            span: None,
        },
        IRExpr::Assert { expr, span } => IRExpr::Assert {
            expr: Box::new(substitute_var_inner(*expr, var_name, replacement, repl_fv)),
            span,
        },
        IRExpr::Assume { expr, span } => IRExpr::Assume {
            expr: Box::new(substitute_var_inner(*expr, var_name, replacement, repl_fv)),
            span,
        },
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            let new_scrutinee = substitute_var_inner(*scrutinee, var_name, replacement, repl_fv);
            let new_arms = arms
                .into_iter()
                .map(|a| {
                    let mut pat_vars = HashSet::new();
                    collect_ir_pattern_vars(&a.pattern, &mut pat_vars);
                    if pat_vars.contains(var_name) {
                        // Shadowed by pattern — don't substitute in guard/body
                        a
                    } else {
                        // Check for capture: pattern vars that collide with replacement free vars
                        let captures: Vec<String> = pat_vars
                            .iter()
                            .filter(|v| repl_fv.contains(v.as_str()))
                            .cloned()
                            .collect();
                        if captures.is_empty() {
                            // No capture risk — substitute directly
                            crate::ir::types::IRMatchArm {
                                pattern: a.pattern,
                                guard: a.guard.map(|g| {
                                    substitute_var_inner(g, var_name, replacement, repl_fv)
                                }),
                                body: substitute_var_inner(a.body, var_name, replacement, repl_fv),
                            }
                        } else {
                            // Alpha-rename capturing pattern vars in pattern + guard + body
                            let mut pattern = a.pattern;
                            let mut guard = a.guard;
                            let mut body = a.body;
                            for old_name in &captures {
                                let fresh = fresh_name(old_name);
                                pattern = rename_in_pattern(pattern, old_name, &fresh);
                                // Recover the type from the first occurrence in body/guard,
                                // falling back to Bool (pattern vars are typically entity/enum typed
                                // but the type is only carried structurally — not consumed by subst).
                                let ty = find_var_type(&body, old_name)
                                    .or_else(|| {
                                        guard.as_ref().and_then(|g| find_var_type(g, old_name))
                                    })
                                    .unwrap_or(IRType::Bool);
                                let fresh_var = IRExpr::Var {
                                    name: fresh.clone(),
                                    ty,
                                    span: None,
                                };
                                let fv_fresh = free_vars(&fresh_var);
                                if let Some(g) = guard {
                                    guard = Some(substitute_var_inner(
                                        g, old_name, &fresh_var, &fv_fresh,
                                    ));
                                }
                                body = substitute_var_inner(body, old_name, &fresh_var, &fv_fresh);
                            }
                            crate::ir::types::IRMatchArm {
                                pattern,
                                guard: guard.map(|g| {
                                    substitute_var_inner(g, var_name, replacement, repl_fv)
                                }),
                                body: substitute_var_inner(body, var_name, replacement, repl_fv),
                            }
                        }
                    }
                })
                .collect();
            IRExpr::Match {
                scrutinee: Box::new(new_scrutinee),
                arms: new_arms,
                span: None,
            }
        }
        IRExpr::MapUpdate {
            map,
            key,
            value,
            ty,
            ..
        } => IRExpr::MapUpdate {
            map: Box::new(substitute_var_inner(*map, var_name, replacement, repl_fv)),
            key: Box::new(substitute_var_inner(*key, var_name, replacement, repl_fv)),
            value: Box::new(substitute_var_inner(*value, var_name, replacement, repl_fv)),
            ty,
            span: None,
        },
        IRExpr::Index { map, key, ty, .. } => IRExpr::Index {
            map: Box::new(substitute_var_inner(*map, var_name, replacement, repl_fv)),
            key: Box::new(substitute_var_inner(*key, var_name, replacement, repl_fv)),
            ty,
            span: None,
        },
        IRExpr::SetComp {
            var,
            domain,
            filter,
            projection,
            ty,
            ..
        } => {
            if var == var_name {
                IRExpr::SetComp {
                    var,
                    domain,
                    filter,
                    projection,
                    ty,
                    span: None,
                }
            } else if repl_fv.contains(&var) {
                let fresh = fresh_name(&var);
                let fresh_var = IRExpr::Var {
                    name: fresh.clone(),
                    ty: domain.clone(),
                    span: None,
                };
                let fv_fresh = free_vars(&fresh_var);
                let renamed_filter = substitute_var_inner(*filter, &var, &fresh_var, &fv_fresh);
                let renamed_proj = projection
                    .map(|p| Box::new(substitute_var_inner(*p, &var, &fresh_var, &fv_fresh)));
                IRExpr::SetComp {
                    var: fresh,
                    domain,
                    span: None,
                    filter: Box::new(substitute_var_inner(
                        renamed_filter,
                        var_name,
                        replacement,
                        repl_fv,
                    )),
                    projection: renamed_proj.map(|p| {
                        Box::new(substitute_var_inner(*p, var_name, replacement, repl_fv))
                    }),
                    ty,
                }
            } else {
                IRExpr::SetComp {
                    var,
                    domain,
                    span: None,
                    filter: Box::new(substitute_var_inner(
                        *filter,
                        var_name,
                        replacement,
                        repl_fv,
                    )),
                    projection: projection.map(|p| {
                        Box::new(substitute_var_inner(*p, var_name, replacement, repl_fv))
                    }),
                    ty,
                }
            }
        }
        IRExpr::SetLit { elements, ty, .. } => IRExpr::SetLit {
            elements: elements
                .into_iter()
                .map(|e| substitute_var_inner(e, var_name, replacement, repl_fv))
                .collect(),
            ty,
            span: None,
        },
        IRExpr::SeqLit { elements, ty, .. } => IRExpr::SeqLit {
            elements: elements
                .into_iter()
                .map(|e| substitute_var_inner(e, var_name, replacement, repl_fv))
                .collect(),
            ty,
            span: None,
        },
        IRExpr::MapLit { entries, ty, .. } => IRExpr::MapLit {
            entries: entries
                .into_iter()
                .map(|(k, v)| {
                    (
                        substitute_var_inner(k, var_name, replacement, repl_fv),
                        substitute_var_inner(v, var_name, replacement, repl_fv),
                    )
                })
                .collect(),
            ty,
            span: None,
        },
        IRExpr::Card { expr, .. } => IRExpr::Card {
            expr: Box::new(substitute_var_inner(*expr, var_name, replacement, repl_fv)),
            span: None,
        },
        IRExpr::Block { exprs, .. } => IRExpr::Block {
            exprs: exprs
                .into_iter()
                .map(|e| substitute_var_inner(e, var_name, replacement, repl_fv))
                .collect(),
            span: None,
        },
        IRExpr::VarDecl {
            name,
            ty,
            init,
            rest,
            ..
        } => {
            let new_init = substitute_var_inner(*init, var_name, replacement, repl_fv);
            if name == var_name {
                // Shadowed — don't substitute into rest
                IRExpr::VarDecl {
                    name,
                    ty,
                    init: Box::new(new_init),
                    rest,
                    span: None,
                }
            } else {
                IRExpr::VarDecl {
                    name,
                    ty,
                    init: Box::new(new_init),
                    rest: Box::new(substitute_var_inner(*rest, var_name, replacement, repl_fv)),
                    span: None,
                }
            }
        }
        IRExpr::While {
            cond,
            invariants,
            decreases,
            body,
            ..
        } => IRExpr::While {
            cond: Box::new(substitute_var_inner(*cond, var_name, replacement, repl_fv)),
            invariants: invariants
                .into_iter()
                .map(|e| substitute_var_inner(e, var_name, replacement, repl_fv))
                .collect(),
            decreases,
            body: Box::new(substitute_var_inner(*body, var_name, replacement, repl_fv)),
            span: None,
        },
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => IRExpr::IfElse {
            cond: Box::new(substitute_var_inner(*cond, var_name, replacement, repl_fv)),
            then_body: Box::new(substitute_var_inner(
                *then_body,
                var_name,
                replacement,
                repl_fv,
            )),
            else_body: else_body
                .map(|e| Box::new(substitute_var_inner(*e, var_name, replacement, repl_fv))),
            span: None,
        },
        // / — aggregate: var is bound in body.
        IRExpr::Aggregate {
            kind,
            var,
            domain,
            body,
            in_filter,
            ..
        } => {
            if var == var_name {
                // Shadowed — don't substitute into body or in_filter
                IRExpr::Aggregate {
                    kind,
                    var,
                    domain,
                    body,
                    in_filter,
                    span: None,
                }
            } else if repl_fv.contains(&var) {
                // Capture risk: alpha-rename the aggregate variable
                let fresh = fresh_name(&var);
                let fresh_var = IRExpr::Var {
                    name: fresh.clone(),
                    ty: domain.clone(),
                    span: None,
                };
                let fv_fresh = free_vars(&fresh_var);
                let renamed_body = substitute_var_inner(*body, &var, &fresh_var, &fv_fresh);
                let renamed_filter = in_filter.map(|f| {
                    let renamed = substitute_var_inner(*f, &var, &fresh_var, &fv_fresh);
                    Box::new(substitute_var_inner(
                        renamed,
                        var_name,
                        replacement,
                        repl_fv,
                    ))
                });
                IRExpr::Aggregate {
                    kind,
                    var: fresh,
                    domain,
                    body: Box::new(substitute_var_inner(
                        renamed_body,
                        var_name,
                        replacement,
                        repl_fv,
                    )),
                    in_filter: renamed_filter,
                    span: None,
                }
            } else {
                let subst_filter = in_filter
                    .map(|f| Box::new(substitute_var_inner(*f, var_name, replacement, repl_fv)));
                IRExpr::Aggregate {
                    kind,
                    var,
                    domain,
                    body: Box::new(substitute_var_inner(*body, var_name, replacement, repl_fv)),
                    in_filter: subst_filter,
                    span: None,
                }
            }
        }
        // / — saw operator: substitute into non-wildcard args.
        IRExpr::Saw {
            system_name,
            event_name,
            args,
            span,
        } => IRExpr::Saw {
            system_name,
            event_name,
            args: args
                .into_iter()
                .map(|a| {
                    a.map(|e| Box::new(substitute_var_inner(*e, var_name, replacement, repl_fv)))
                })
                .collect(),
            span,
        },
    }
}

/// Find the type annotation of the first `Var` with the given name in an expression.
/// Used to recover types for alpha-renamed pattern variables.
fn find_var_type(expr: &IRExpr, name: &str) -> Option<IRType> {
    match expr {
        IRExpr::Var { name: n, ty, .. } if n == name => Some(ty.clone()),
        IRExpr::Field { expr, .. } | IRExpr::Prime { expr, .. } => find_var_type(expr, name),
        IRExpr::BinOp { left, right, .. } => {
            find_var_type(left, name).or_else(|| find_var_type(right, name))
        }
        IRExpr::UnOp { operand, .. } => find_var_type(operand, name),
        IRExpr::App { func, arg, .. } => {
            find_var_type(func, name).or_else(|| find_var_type(arg, name))
        }
        IRExpr::Lam { body, .. }
        | IRExpr::Forall { body, .. }
        | IRExpr::Exists { body, .. }
        | IRExpr::One { body, .. }
        | IRExpr::Lone { body, .. }
        | IRExpr::Always { body, .. }
        | IRExpr::Eventually { body, .. } => find_var_type(body, name),
        IRExpr::Let { bindings, body, .. } => bindings
            .iter()
            .find_map(|b| find_var_type(&b.expr, name))
            .or_else(|| find_var_type(body, name)),
        IRExpr::Match {
            scrutinee, arms, ..
        } => find_var_type(scrutinee, name).or_else(|| {
            arms.iter().find_map(|a| {
                a.guard
                    .as_ref()
                    .and_then(|g| find_var_type(g, name))
                    .or_else(|| find_var_type(&a.body, name))
            })
        }),
        _ => None,
    }
}

/// Collect variable names bound by an IR pattern.
fn collect_ir_pattern_vars(pat: &crate::ir::types::IRPattern, vars: &mut HashSet<String>) {
    match pat {
        crate::ir::types::IRPattern::PVar { name } => {
            vars.insert(name.clone());
        }
        crate::ir::types::IRPattern::PCtor { fields, .. } => {
            for f in fields {
                collect_ir_pattern_vars(&f.pattern, vars);
            }
        }
        crate::ir::types::IRPattern::PWild => {}
        crate::ir::types::IRPattern::POr { left, right } => {
            collect_ir_pattern_vars(left, vars);
            collect_ir_pattern_vars(right, vars);
        }
    }
}

/// Collect variable names bound by an IR pattern (for `free_vars` analysis).
fn collect_pattern_vars(pat: &crate::ir::types::IRPattern, bound: &mut HashSet<String>) {
    collect_ir_pattern_vars(pat, bound);
}

/// Rename a variable binding inside an IR pattern.
/// `PVar { name: old }` → `PVar { name: new }`, recurse into `PCtor` fields and `POr`.
fn rename_in_pattern(
    pat: crate::ir::types::IRPattern,
    old_name: &str,
    new_name: &str,
) -> crate::ir::types::IRPattern {
    use crate::ir::types::IRPattern;
    match pat {
        IRPattern::PVar { name } if name == old_name => IRPattern::PVar {
            name: new_name.to_owned(),
        },
        IRPattern::PVar { .. } | IRPattern::PWild => pat,
        IRPattern::PCtor { name, fields } => IRPattern::PCtor {
            name,
            fields: fields
                .into_iter()
                .map(|f| crate::ir::types::IRFieldPat {
                    name: f.name,
                    pattern: rename_in_pattern(f.pattern, old_name, new_name),
                })
                .collect(),
        },
        IRPattern::POr { left, right } => IRPattern::POr {
            left: Box::new(rename_in_pattern(*left, old_name, new_name)),
            right: Box::new(rename_in_pattern(*right, old_name, new_name)),
        },
    }
}

/// Tag for which quantifier variant to reconstruct after substitution.
#[derive(Clone, Copy)]
enum QuantTag {
    Forall,
    Exists,
    One,
    Lone,
}

/// Shared logic for Forall/Exists/One/Lone with capture-avoiding substitution.
fn subst_quantifier(
    var: String,
    domain: IRType,
    body: Box<IRExpr>,
    var_name: &str,
    replacement: &IRExpr,
    repl_fv: &HashSet<String>,
    tag: QuantTag,
) -> IRExpr {
    let make = |v: String, d: IRType, b: Box<IRExpr>| match tag {
        QuantTag::Forall => IRExpr::Forall {
            var: v,
            domain: d,
            body: b,
            span: None,
        },
        QuantTag::Exists => IRExpr::Exists {
            var: v,
            domain: d,
            body: b,
            span: None,
        },
        QuantTag::One => IRExpr::One {
            var: v,
            domain: d,
            body: b,
            span: None,
        },
        QuantTag::Lone => IRExpr::Lone {
            var: v,
            domain: d,
            body: b,
            span: None,
        },
    };

    if var == var_name {
        // Shadowed — don't substitute into body
        make(var, domain, body)
    } else if repl_fv.contains(&var) {
        // Capture risk: alpha-rename the quantifier variable
        let fresh = fresh_name(&var);
        let fresh_var = IRExpr::Var {
            name: fresh.clone(),
            ty: domain.clone(),
            span: None,
        };
        let fv_fresh = free_vars(&fresh_var);
        let renamed_body = substitute_var_inner(*body, &var, &fresh_var, &fv_fresh);
        make(
            fresh,
            domain,
            Box::new(substitute_var_inner(
                renamed_body,
                var_name,
                replacement,
                repl_fv,
            )),
        )
    } else {
        make(
            var,
            domain,
            Box::new(substitute_var_inner(*body, var_name, replacement, repl_fv)),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::types::*;

    fn bool_lit(value: bool) -> IRExpr {
        IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value },
            span: None,
        }
    }

    fn int_lit(value: i64) -> IRExpr {
        IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value },
            span: None,
        }
    }

    fn var(name: &str, ty: IRType) -> IRExpr {
        IRExpr::Var {
            name: name.to_owned(),
            ty,
            span: None,
        }
    }

    fn bin(op: &str, left: IRExpr, right: IRExpr, ty: IRType) -> IRExpr {
        IRExpr::BinOp {
            op: op.to_owned(),
            left: Box::new(left),
            right: Box::new(right),
            ty,
            span: None,
        }
    }

    fn order_ty() -> IRType {
        IRType::Entity {
            name: "Order".to_owned(),
        }
    }

    fn int_map_ty() -> IRType {
        IRType::Map {
            key: Box::new(IRType::Int),
            value: Box::new(IRType::Bool),
        }
    }

    #[test]
    fn rewrite_self_field_refs_covers_recursive_expression_shapes() {
        let receiver = var("self", order_ty());
        let field_names = HashSet::from(["status".to_owned(), "count".to_owned()]);
        let status_ref = var("status", IRType::Bool);
        let count_ref = var("count", IRType::Int);
        let map_ref = var("m", int_map_ty());

        let exprs = vec![
            status_ref.clone(),
            IRExpr::Field {
                expr: Box::new(status_ref.clone()),
                field: "inner".to_owned(),
                ty: IRType::Bool,
                span: None,
            },
            bin("OpAnd", status_ref.clone(), bool_lit(true), IRType::Bool),
            IRExpr::UnOp {
                op: "OpNot".to_owned(),
                operand: Box::new(status_ref.clone()),
                ty: IRType::Bool,
                span: None,
            },
            IRExpr::App {
                func: Box::new(var("pred", IRType::Bool)),
                arg: Box::new(status_ref.clone()),
                ty: IRType::Bool,
                span: None,
            },
            IRExpr::Lam {
                param: "status".to_owned(),
                param_type: IRType::Bool,
                body: Box::new(status_ref.clone()),
                span: None,
            },
            IRExpr::Let {
                bindings: vec![LetBinding {
                    name: "status".to_owned(),
                    ty: IRType::Bool,
                    expr: bool_lit(false),
                }],
                body: Box::new(status_ref.clone()),
                span: None,
            },
            IRExpr::Forall {
                var: "status".to_owned(),
                domain: IRType::Bool,
                body: Box::new(status_ref.clone()),
                span: None,
            },
            IRExpr::Exists {
                var: "x".to_owned(),
                domain: IRType::Int,
                body: Box::new(count_ref.clone()),
                span: None,
            },
            IRExpr::One {
                var: "x".to_owned(),
                domain: IRType::Int,
                body: Box::new(count_ref.clone()),
                span: None,
            },
            IRExpr::Lone {
                var: "x".to_owned(),
                domain: IRType::Int,
                body: Box::new(count_ref.clone()),
                span: None,
            },
            IRExpr::Always {
                body: Box::new(status_ref.clone()),
                span: None,
            },
            IRExpr::Eventually {
                body: Box::new(status_ref.clone()),
                span: None,
            },
            IRExpr::Until {
                left: Box::new(status_ref.clone()),
                right: Box::new(bool_lit(true)),
                span: None,
            },
            IRExpr::Historically {
                body: Box::new(status_ref.clone()),
                span: None,
            },
            IRExpr::Once {
                body: Box::new(status_ref.clone()),
                span: None,
            },
            IRExpr::Previously {
                body: Box::new(status_ref.clone()),
                span: None,
            },
            IRExpr::Since {
                left: Box::new(status_ref.clone()),
                right: Box::new(bool_lit(true)),
                span: None,
            },
            IRExpr::Prime {
                expr: Box::new(count_ref.clone()),
                span: None,
            },
            IRExpr::Match {
                scrutinee: Box::new(status_ref.clone()),
                arms: vec![IRMatchArm {
                    pattern: IRPattern::POr {
                        left: Box::new(IRPattern::PVar {
                            name: "status".to_owned(),
                        }),
                        right: Box::new(IRPattern::PVar {
                            name: "status".to_owned(),
                        }),
                    },
                    guard: Some(status_ref.clone()),
                    body: count_ref.clone(),
                }],
                span: None,
            },
            IRExpr::MapUpdate {
                map: Box::new(map_ref.clone()),
                key: Box::new(count_ref.clone()),
                value: Box::new(status_ref.clone()),
                ty: int_map_ty(),
                span: None,
            },
            IRExpr::Index {
                map: Box::new(map_ref.clone()),
                key: Box::new(count_ref.clone()),
                ty: IRType::Bool,
                span: None,
            },
            IRExpr::SetComp {
                var: "x".to_owned(),
                domain: IRType::Int,
                filter: Box::new(status_ref.clone()),
                projection: Some(Box::new(count_ref.clone())),
                ty: IRType::Set {
                    element: Box::new(IRType::Int),
                },
                span: None,
            },
            IRExpr::SetLit {
                elements: vec![count_ref.clone()],
                ty: IRType::Set {
                    element: Box::new(IRType::Int),
                },
                span: None,
            },
            IRExpr::SeqLit {
                elements: vec![count_ref.clone()],
                ty: IRType::Seq {
                    element: Box::new(IRType::Int),
                },
                span: None,
            },
            IRExpr::MapLit {
                entries: vec![(count_ref.clone(), status_ref.clone())],
                ty: int_map_ty(),
                span: None,
            },
            IRExpr::Card {
                expr: Box::new(IRExpr::SetLit {
                    elements: vec![count_ref.clone()],
                    ty: IRType::Set {
                        element: Box::new(IRType::Int),
                    },
                    span: None,
                }),
                span: None,
            },
            IRExpr::Assert {
                expr: Box::new(status_ref.clone()),
                span: None,
            },
            IRExpr::Assume {
                expr: Box::new(status_ref.clone()),
                span: None,
            },
            IRExpr::IfElse {
                cond: Box::new(status_ref.clone()),
                then_body: Box::new(count_ref.clone()),
                else_body: Some(Box::new(int_lit(0))),
                span: None,
            },
        ];

        let mut free = HashSet::new();
        for expr in exprs {
            free.extend(free_vars(&rewrite_self_field_refs(
                expr,
                &receiver,
                &field_names,
            )));
        }
        assert!(free.contains("self"));
    }

    #[test]
    fn substitute_var_covers_capture_avoidance_and_recursive_shapes() {
        let replacement = var("y", IRType::Int);
        let target = var("x", IRType::Int);
        let expr = IRExpr::Block {
            exprs: vec![
                target.clone(),
                IRExpr::Field {
                    expr: Box::new(target.clone()),
                    field: "value".to_owned(),
                    ty: IRType::Int,
                    span: None,
                },
                bin("OpEq", target.clone(), int_lit(1), IRType::Bool),
                IRExpr::UnOp {
                    op: "OpNeg".to_owned(),
                    operand: Box::new(target.clone()),
                    ty: IRType::Int,
                    span: None,
                },
                IRExpr::App {
                    func: Box::new(var("f", IRType::Bool)),
                    arg: Box::new(target.clone()),
                    ty: IRType::Bool,
                    span: None,
                },
                IRExpr::Lam {
                    param: "y".to_owned(),
                    param_type: IRType::Int,
                    body: Box::new(target.clone()),
                    span: None,
                },
                IRExpr::Choose {
                    var: "y".to_owned(),
                    domain: IRType::Int,
                    predicate: Some(Box::new(bin(
                        "OpEq",
                        target.clone(),
                        var("y", IRType::Int),
                        IRType::Bool,
                    ))),
                    ty: IRType::Int,
                    span: None,
                },
                IRExpr::Let {
                    bindings: vec![LetBinding {
                        name: "y".to_owned(),
                        ty: IRType::Int,
                        expr: target.clone(),
                    }],
                    body: Box::new(bin(
                        "OpEq",
                        target.clone(),
                        var("y", IRType::Int),
                        IRType::Bool,
                    )),
                    span: None,
                },
                IRExpr::Forall {
                    var: "y".to_owned(),
                    domain: IRType::Int,
                    body: Box::new(target.clone()),
                    span: None,
                },
                IRExpr::Exists {
                    var: "y".to_owned(),
                    domain: IRType::Int,
                    body: Box::new(target.clone()),
                    span: None,
                },
                IRExpr::One {
                    var: "y".to_owned(),
                    domain: IRType::Int,
                    body: Box::new(target.clone()),
                    span: None,
                },
                IRExpr::Lone {
                    var: "y".to_owned(),
                    domain: IRType::Int,
                    body: Box::new(target.clone()),
                    span: None,
                },
                IRExpr::Always {
                    body: Box::new(target.clone()),
                    span: None,
                },
                IRExpr::Eventually {
                    body: Box::new(target.clone()),
                    span: None,
                },
                IRExpr::Until {
                    left: Box::new(target.clone()),
                    right: Box::new(int_lit(2)),
                    span: None,
                },
                IRExpr::Historically {
                    body: Box::new(target.clone()),
                    span: None,
                },
                IRExpr::Once {
                    body: Box::new(target.clone()),
                    span: None,
                },
                IRExpr::Previously {
                    body: Box::new(target.clone()),
                    span: None,
                },
                IRExpr::Since {
                    left: Box::new(target.clone()),
                    right: Box::new(int_lit(2)),
                    span: None,
                },
                IRExpr::Prime {
                    expr: Box::new(target.clone()),
                    span: None,
                },
                IRExpr::Assert {
                    expr: Box::new(bin("OpEq", target.clone(), int_lit(1), IRType::Bool)),
                    span: None,
                },
                IRExpr::Assume {
                    expr: Box::new(bin("OpEq", target.clone(), int_lit(1), IRType::Bool)),
                    span: None,
                },
                IRExpr::Match {
                    scrutinee: Box::new(target.clone()),
                    arms: vec![IRMatchArm {
                        pattern: IRPattern::PCtor {
                            name: "Some".to_owned(),
                            fields: vec![IRFieldPat {
                                name: "value".to_owned(),
                                pattern: IRPattern::PVar {
                                    name: "y".to_owned(),
                                },
                            }],
                        },
                        guard: Some(bin(
                            "OpEq",
                            var("y", IRType::Int),
                            target.clone(),
                            IRType::Bool,
                        )),
                        body: bin("OpEq", target.clone(), var("y", IRType::Int), IRType::Bool),
                    }],
                    span: None,
                },
                IRExpr::MapUpdate {
                    map: Box::new(var("m", int_map_ty())),
                    key: Box::new(target.clone()),
                    value: Box::new(bool_lit(true)),
                    ty: int_map_ty(),
                    span: None,
                },
                IRExpr::Index {
                    map: Box::new(var("m", int_map_ty())),
                    key: Box::new(target.clone()),
                    ty: IRType::Bool,
                    span: None,
                },
                IRExpr::SetComp {
                    var: "y".to_owned(),
                    domain: IRType::Int,
                    filter: Box::new(bin(
                        "OpEq",
                        target.clone(),
                        var("y", IRType::Int),
                        IRType::Bool,
                    )),
                    projection: Some(Box::new(target.clone())),
                    ty: IRType::Set {
                        element: Box::new(IRType::Int),
                    },
                    span: None,
                },
                IRExpr::SetLit {
                    elements: vec![target.clone()],
                    ty: IRType::Set {
                        element: Box::new(IRType::Int),
                    },
                    span: None,
                },
                IRExpr::SeqLit {
                    elements: vec![target.clone()],
                    ty: IRType::Seq {
                        element: Box::new(IRType::Int),
                    },
                    span: None,
                },
                IRExpr::MapLit {
                    entries: vec![(target.clone(), bool_lit(true))],
                    ty: int_map_ty(),
                    span: None,
                },
                IRExpr::Card {
                    expr: Box::new(IRExpr::SetLit {
                        elements: vec![target.clone()],
                        ty: IRType::Set {
                            element: Box::new(IRType::Int),
                        },
                        span: None,
                    }),
                    span: None,
                },
                IRExpr::VarDecl {
                    name: "y".to_owned(),
                    ty: IRType::Int,
                    init: Box::new(target.clone()),
                    rest: Box::new(bin(
                        "OpEq",
                        target.clone(),
                        var("y", IRType::Int),
                        IRType::Bool,
                    )),
                    span: None,
                },
                IRExpr::While {
                    cond: Box::new(bool_lit(true)),
                    invariants: vec![bin("OpEq", target.clone(), int_lit(1), IRType::Bool)],
                    decreases: None,
                    body: Box::new(target.clone()),
                    span: None,
                },
                IRExpr::IfElse {
                    cond: Box::new(bool_lit(true)),
                    then_body: Box::new(target.clone()),
                    else_body: Some(Box::new(int_lit(0))),
                    span: None,
                },
                IRExpr::Aggregate {
                    kind: IRAggKind::Sum,
                    var: "y".to_owned(),
                    domain: IRType::Int,
                    body: Box::new(target.clone()),
                    in_filter: Some(Box::new(bin(
                        "OpEq",
                        target.clone(),
                        var("y", IRType::Int),
                        IRType::Bool,
                    ))),
                    span: None,
                },
                IRExpr::Saw {
                    system_name: "Audit".to_owned(),
                    event_name: "seen".to_owned(),
                    args: vec![Some(Box::new(target.clone())), None],
                    span: None,
                },
            ],
            span: None,
        };

        let substituted = substitute_var(expr, "x", &replacement);
        let free = free_vars(&substituted);
        assert!(free.contains("y"));
        assert!(!free.contains("x"));
    }

    #[test]
    fn uncurry_nullary() {
        let body = IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },

            span: None,
        };
        let (params, result) = uncurry(&body);
        assert!(params.is_empty());
        assert_eq!(result, body);
    }

    #[test]
    fn uncurry_two_params() {
        let body = IRExpr::Lam {
            param: "x".to_owned(),
            param_type: IRType::Int,
            body: Box::new(IRExpr::Lam {
                param: "y".to_owned(),
                param_type: IRType::Bool,
                body: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
                    ty: IRType::Int,

                    span: None,
                }),

                span: None,
            }),

            span: None,
        };
        let (params, result) = uncurry(&body);
        assert_eq!(params.len(), 2);
        assert_eq!(params[0].0, "x");
        assert_eq!(params[1].0, "y");
        assert!(matches!(result, IRExpr::Var { ref name, .. } if name == "x"));
    }

    #[test]
    fn decompose_app_chain_single_arg() {
        let expr = IRExpr::App {
            func: Box::new(IRExpr::Var {
                name: "p".to_owned(),
                ty: IRType::Bool,

                span: None,
            }),
            arg: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 42 },

                span: None,
            }),
            ty: IRType::Bool,

            span: None,
        };
        let (name, args) = decompose_app_chain(&expr).unwrap();
        assert_eq!(name, "p");
        assert_eq!(args.len(), 1);
    }

    #[test]
    fn decompose_app_chain_two_args() {
        let expr = IRExpr::App {
            func: Box::new(IRExpr::App {
                func: Box::new(IRExpr::Var {
                    name: "p".to_owned(),
                    ty: IRType::Bool,

                    span: None,
                }),
                arg: Box::new(IRExpr::Var {
                    name: "a".to_owned(),
                    ty: IRType::Int,

                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            }),
            arg: Box::new(IRExpr::Var {
                name: "b".to_owned(),
                ty: IRType::Int,

                span: None,
            }),
            ty: IRType::Bool,

            span: None,
        };
        let (name, args) = decompose_app_chain(&expr).unwrap();
        assert_eq!(name, "p");
        assert_eq!(args.len(), 2);
    }

    #[test]
    fn decompose_app_chain_public_and_name_helpers_match() {
        let expr = IRExpr::App {
            func: Box::new(IRExpr::App {
                func: Box::new(IRExpr::Var {
                    name: "f".to_owned(),
                    ty: IRType::Bool,
                    span: None,
                }),
                arg: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 1 },
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            arg: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 2 },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };

        assert_eq!(decompose_app_chain_name(&expr).as_deref(), Some("f"));
        let (name, args) = decompose_app_chain_public(&expr).expect("expected app chain");
        assert_eq!(name, "f");
        assert_eq!(args.len(), 2);

        assert!(decompose_app_chain_name(&IRExpr::Var {
            name: "f".to_owned(),
            ty: IRType::Bool,
            span: None,
        })
        .is_some());
        assert!(decompose_app_chain_public(&IRExpr::Var {
            name: "f".to_owned(),
            ty: IRType::Bool,
            span: None,
        })
        .is_none());
    }

    #[test]
    fn classify_app_chain_public_distinguishes_query_from_pure_def() {
        let query = IRQuery {
            name: "payable".to_owned(),
            params: vec![IRTransParam {
                name: "x".to_owned(),
                ty: IRType::Int,
            }],
            body: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
        };
        let program = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![IRFunction {
                name: "positive".to_owned(),
                ty: IRType::Fn {
                    param: Box::new(IRType::Int),
                    result: Box::new(IRType::Bool),
                },
                body: IRExpr::Lam {
                    param: "x".to_owned(),
                    param_type: IRType::Int,
                    body: Box::new(IRExpr::BinOp {
                        op: "OpGt".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "x".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        }),
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 0 },
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    span: None,
                },
                prop_target: None,
                requires: vec![],
                ensures: vec![],
                decreases: None,
                span: None,
                file: None,
            }],
            entities: vec![],
            systems: vec![IRSystem {
                name: "Billing".to_owned(),
                store_params: vec![],
                fields: vec![],
                entities: vec![],
                commands: vec![],
                actions: vec![],
                fsm_decls: vec![],
                derived_fields: vec![],
                invariants: vec![],
                queries: vec![query.clone()],
                preds: vec![],
                let_bindings: vec![],
                procs: vec![],
            }],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };
        let defs = DefEnv::from_ir(&program);
        let system_queries = HashMap::from([(("Billing".to_owned(), "payable".to_owned()), query)]);

        let bare_query = IRExpr::App {
            func: Box::new(IRExpr::Var {
                name: "payable".to_owned(),
                ty: IRType::Bool,
                span: None,
            }),
            arg: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 1 },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };
        let pure_def = IRExpr::App {
            func: Box::new(IRExpr::Var {
                name: "positive".to_owned(),
                ty: IRType::Bool,
                span: None,
            }),
            arg: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 1 },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };

        let (kind, head, args) =
            classify_app_chain_public(&defs, &bare_query, Some("Billing"), &system_queries)
                .expect("expected query classification");
        assert_eq!(kind, AppHeadKind::Query);
        assert_eq!(head, "Billing::payable");
        assert_eq!(args.len(), 1);

        let (kind, head, args) =
            classify_app_chain_public(&defs, &pure_def, Some("Billing"), &system_queries)
                .expect("expected pure def classification");
        assert_eq!(kind, AppHeadKind::PureDef);
        assert_eq!(head, "positive");
        assert_eq!(args.len(), 1);
    }

    #[test]
    fn expand_nullary_prop() {
        let program = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![IRFunction {
                name: "safe".to_owned(),
                ty: IRType::Bool,
                body: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                prop_target: None,
                requires: vec![],
                ensures: vec![],
                decreases: None,
                span: None,
                file: None,
            }],
            entities: vec![],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };
        let env = DefEnv::from_ir(&program);
        let expanded = env.expand_var("safe").unwrap();
        assert!(matches!(
            expanded,
            IRExpr::Lit {
                value: LitVal::Bool { value: true },
                ..
            }
        ));
    }

    #[test]
    fn expand_pred_app() {
        // pred positive(x: Int) = x > 0
        let program = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![IRFunction {
                name: "positive".to_owned(),
                ty: IRType::Fn {
                    param: Box::new(IRType::Int),
                    result: Box::new(IRType::Bool),
                },
                body: IRExpr::Lam {
                    param: "x".to_owned(),
                    param_type: IRType::Int,
                    body: Box::new(IRExpr::BinOp {
                        op: "OpGt".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "x".to_owned(),
                            ty: IRType::Int,

                            span: None,
                        }),
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 0 },

                            span: None,
                        }),
                        ty: IRType::Bool,

                        span: None,
                    }),

                    span: None,
                },
                prop_target: None,
                requires: vec![],
                ensures: vec![],
                decreases: None,
                span: None,
                file: None,
            }],
            entities: vec![],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };
        let env = DefEnv::from_ir(&program);

        // App(Var("positive"), Lit(5))
        let call = IRExpr::App {
            func: Box::new(IRExpr::Var {
                name: "positive".to_owned(),
                ty: IRType::Bool,

                span: None,
            }),
            arg: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 5 },

                span: None,
            }),
            ty: IRType::Bool,

            span: None,
        };

        let expanded = env.expand_app(&call).unwrap();
        // Should be: 5 > 0
        assert!(matches!(expanded, IRExpr::BinOp { ref op, .. } if op == "OpGt"));
    }

    #[test]
    fn expand_var_returns_none_for_parameterized() {
        let program = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![IRFunction {
                name: "positive".to_owned(),
                ty: IRType::Fn {
                    param: Box::new(IRType::Int),
                    result: Box::new(IRType::Bool),
                },
                body: IRExpr::Lam {
                    param: "x".to_owned(),
                    param_type: IRType::Int,
                    body: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    }),

                    span: None,
                },
                prop_target: None,
                requires: vec![],
                ensures: vec![],
                decreases: None,
                span: None,
                file: None,
            }],
            entities: vec![],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };
        let env = DefEnv::from_ir(&program);
        // Should return None — parameterized def needs App to supply args
        assert!(env.expand_var("positive").is_none());
    }

    #[test]
    fn call_preconditions_substitutes_actual_arguments() {
        let body = IRExpr::Lam {
            param: "x".to_owned(),
            param_type: IRType::Int,
            body: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
            span: None,
        };
        let req = IRExpr::BinOp {
            op: "OpGt".to_owned(),
            left: Box::new(IRExpr::Var {
                name: "x".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };
        let program = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![IRFunction {
                name: "positive".to_owned(),
                ty: IRType::Fn {
                    param: Box::new(IRType::Int),
                    result: Box::new(IRType::Bool),
                },
                body,
                prop_target: None,
                requires: vec![req],
                ensures: vec![],
                decreases: None,
                span: None,
                file: None,
            }],
            entities: vec![],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };

        let env = DefEnv::from_ir(&program);
        let call = IRExpr::App {
            func: Box::new(IRExpr::Var {
                name: "positive".to_owned(),
                ty: IRType::Bool,
                span: None,
            }),
            arg: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 5 },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };

        let preconditions = env
            .call_preconditions(&call)
            .expect("expected recognized function call");
        assert_eq!(preconditions.len(), 1);
        assert!(matches!(
            &preconditions[0],
            IRExpr::BinOp { left, .. }
                if matches!(
                    left.as_ref(),
                    IRExpr::Lit {
                        value: LitVal::Int { value: 5 },
                        ..
                    }
                )
        ));
    }

    #[test]
    fn add_lemma_fact_conjoins_multiple_expressions() {
        let program = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };

        let mut env = DefEnv::from_ir(&program);
        env.add_lemma_fact(
            "helper",
            &[
                IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: false },
                    span: None,
                },
            ],
        );

        let expanded = env
            .expand_var("helper")
            .expect("lemma fact should be added");
        assert!(matches!(expanded, IRExpr::BinOp { ref op, .. } if op == "OpAnd"));
    }

    #[test]
    fn substitute_respects_shadowing() {
        // Lam(x, _, x + y) with y:= 10 → Lam(x, _, x + 10)
        let expr = IRExpr::Lam {
            param: "x".to_owned(),
            param_type: IRType::Int,
            body: Box::new(IRExpr::BinOp {
                op: "OpAdd".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
                    ty: IRType::Int,

                    span: None,
                }),
                right: Box::new(IRExpr::Var {
                    name: "y".to_owned(),
                    ty: IRType::Int,

                    span: None,
                }),
                ty: IRType::Int,

                span: None,
            }),

            span: None,
        };
        let replacement = IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value: 10 },

            span: None,
        };
        let result = substitute_var(expr, "y", &replacement);
        // x should NOT be replaced, y SHOULD be replaced
        if let IRExpr::Lam { body, .. } = result {
            if let IRExpr::BinOp { left, right, .. } = *body {
                assert!(matches!(*left, IRExpr::Var { ref name, .. } if name == "x"));
                assert!(matches!(
                    *right,
                    IRExpr::Lit {
                        value: LitVal::Int { value: 10 },
                        ..
                    }
                ));
                return;
            }
        }
        panic!("unexpected structure");
    }

    #[test]
    fn match_pattern_shadows_substitution() {
        // match scrut { x => x + y }
        // Substituting y:= 42 should replace y but NOT x (pattern-bound).
        let expr = IRExpr::Match {
            scrutinee: Box::new(IRExpr::Var {
                name: "scrut".to_owned(),
                ty: IRType::Int,

                span: None,
            }),
            arms: vec![IRMatchArm {
                pattern: IRPattern::PVar {
                    name: "x".to_owned(),
                },
                guard: None,
                body: IRExpr::BinOp {
                    op: "OpAdd".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "y".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    ty: IRType::Int,

                    span: None,
                },
            }],

            span: None,
        };
        let replacement = IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value: 42 },

            span: None,
        };
        let result = substitute_var(expr, "y", &replacement);
        if let IRExpr::Match { arms, .. } = result {
            if let IRExpr::BinOp { left, right, .. } = &arms[0].body {
                // x should still be x (pattern-bound)
                assert!(matches!(left.as_ref(), IRExpr::Var { name, .. } if name == "x"));
                // y should be replaced with 42
                assert!(matches!(
                    right.as_ref(),
                    IRExpr::Lit {
                        value: LitVal::Int { value: 42 },
                        ..
                    }
                ));
                return;
            }
        }
        panic!("unexpected structure");
    }

    #[test]
    fn match_pattern_var_shadowed_stops_subst() {
        // match scrut { x => x + 1 }
        // Substituting x:= 99 should NOT replace x in body (shadowed by pattern).
        let expr = IRExpr::Match {
            scrutinee: Box::new(IRExpr::Var {
                name: "scrut".to_owned(),
                ty: IRType::Int,

                span: None,
            }),
            arms: vec![IRMatchArm {
                pattern: IRPattern::PVar {
                    name: "x".to_owned(),
                },
                guard: None,
                body: IRExpr::BinOp {
                    op: "OpAdd".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },

                        span: None,
                    }),
                    ty: IRType::Int,

                    span: None,
                },
            }],

            span: None,
        };
        let replacement = IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value: 99 },

            span: None,
        };
        let result = substitute_var(expr, "x", &replacement);
        if let IRExpr::Match { arms, .. } = result {
            if let IRExpr::BinOp { left, .. } = &arms[0].body {
                // x should still be x — shadowed by pattern
                assert!(
                    matches!(left.as_ref(), IRExpr::Var { name, .. } if name == "x"),
                    "expected x to remain (shadowed), got: {left:?}"
                );
                return;
            }
        }
        panic!("unexpected structure");
    }

    #[test]
    fn match_pattern_capture_avoidance() {
        // match scrut { x => x + y }
        // Substituting y:= (x + 1) — replacement has free var "x" that collides
        // with pattern var "x". Without alpha-rename, body would become (x + (x + 1))
        // where the first x is the pattern-bound one and the second x is the free one
        // from replacement — a capture bug.
        // With alpha-rename, pattern x should be renamed to x$N, so body becomes
        // (x$N + (x + 1)) — correct.
        let expr = IRExpr::Match {
            scrutinee: Box::new(IRExpr::Var {
                name: "scrut".to_owned(),
                ty: IRType::Int,

                span: None,
            }),
            arms: vec![IRMatchArm {
                pattern: IRPattern::PVar {
                    name: "x".to_owned(),
                },
                guard: None,
                body: IRExpr::BinOp {
                    op: "OpAdd".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "y".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    ty: IRType::Int,

                    span: None,
                },
            }],

            span: None,
        };
        // replacement: x + 1 (free var "x")
        let replacement = IRExpr::BinOp {
            op: "OpAdd".to_owned(),
            left: Box::new(IRExpr::Var {
                name: "x".to_owned(),
                ty: IRType::Int,

                span: None,
            }),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 1 },

                span: None,
            }),
            ty: IRType::Int,

            span: None,
        };
        let result = substitute_var(expr, "y", &replacement);
        if let IRExpr::Match { arms, .. } = result {
            // Pattern should be renamed from "x" to something fresh
            let IRPattern::PVar { name: pat_name } = &arms[0].pattern else {
                panic!("expected PVar pattern");
            };
            assert_ne!(pat_name, "x", "pattern var should be alpha-renamed");
            assert!(
                pat_name.starts_with("x$"),
                "expected fresh name like x$N, got: {pat_name}"
            );

            // Body left should reference the fresh name (was pattern-bound x)
            if let IRExpr::BinOp { left, right, .. } = &arms[0].body {
                assert!(
                    matches!(left.as_ref(), IRExpr::Var { name, .. } if name == pat_name),
                    "left should reference renamed pattern var {pat_name}, got: {left:?}"
                );
                // Right should be the replacement (x + 1) with the ORIGINAL "x"
                assert!(
                    matches!(right.as_ref(), IRExpr::BinOp { .. }),
                    "right should be the replacement BinOp, got: {right:?}"
                );
                return;
            }
        }
        panic!("unexpected structure");
    }

    #[test]
    fn free_vars_respects_match_pattern_binding() {
        // match scrut { x => x + y }
        // free vars should be {scrut, y} but NOT x (bound by pattern)
        let expr = IRExpr::Match {
            scrutinee: Box::new(IRExpr::Var {
                name: "scrut".to_owned(),
                ty: IRType::Int,

                span: None,
            }),
            arms: vec![IRMatchArm {
                pattern: IRPattern::PVar {
                    name: "x".to_owned(),
                },
                guard: None,
                body: IRExpr::BinOp {
                    op: "OpAdd".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "y".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    ty: IRType::Int,

                    span: None,
                },
            }],

            span: None,
        };
        let fv = free_vars(&expr);
        assert!(fv.contains("scrut"), "scrut should be free");
        assert!(fv.contains("y"), "y should be free");
        assert!(!fv.contains("x"), "x should NOT be free (pattern-bound)");
    }

    /// an entity-level derived field reference
    /// `o.is_done` (where `is_done = status == @Shipped`) expands to
    /// `o.status == @Shipped` — bare `status` Var in the body becomes
    /// `Field(o, "status")` in the expansion.
    #[test]
    fn expand_entity_derived_rewrites_field_refs() {
        use crate::ir::types::{IRDerivedField, IREntity, IRField};

        let entity = IREntity {
            name: "Order".to_owned(),
            fields: vec![IRField {
                name: "status".to_owned(),
                ty: IRType::Int,
                default: None,
                initial_constraint: None,
            }],
            transitions: vec![],
            derived_fields: vec![IRDerivedField {
                name: "is_done".to_owned(),
                // body: status == 1
                body: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "status".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                },
                ty: IRType::Bool,
            }],
            invariants: vec![],
            fsm_decls: vec![],
        };

        let program = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };

        let env = DefEnv::from_ir(&program);

        // Receiver: an Order-typed Var named "o"
        let receiver = IRExpr::Var {
            name: "o".to_owned(),
            ty: IRType::Entity {
                name: "Order".to_owned(),
            },
            span: None,
        };

        let expanded = env
            .expand_entity_derived(&receiver, "is_done")
            .expect("derived field should expand");

        // Expect: BinOp(OpEq, Field(o, "status"), Lit(1))
        let IRExpr::BinOp {
            op, left, right, ..
        } = expanded
        else {
            panic!("expected BinOp at top level, got: {expanded:?}");
        };
        assert_eq!(op, "OpEq");
        // Left side should now be o.status (a Field), not bare status (a Var)
        let IRExpr::Field {
            expr: receiver_box,
            field: ref field_name,
            ..
        } = *left
        else {
            panic!("expected Field on left, got: {left:?}");
        };
        assert_eq!(field_name, "status");
        let IRExpr::Var { ref name, .. } = *receiver_box else {
            panic!("expected Var as Field receiver");
        };
        assert_eq!(name, "o");
        // Right side should still be the Lit
        assert!(matches!(
            *right,
            IRExpr::Lit {
                value: LitVal::Int { value: 1 },
                ..
            }
        ));
    }

    /// a non-derived field name returns None from
    /// `expand_entity_derived` so the verifier falls through to normal
    /// field encoding.
    #[test]
    fn expand_entity_derived_returns_none_for_regular_field() {
        use crate::ir::types::{IREntity, IRField};

        let entity = IREntity {
            name: "Order".to_owned(),
            fields: vec![IRField {
                name: "status".to_owned(),
                ty: IRType::Int,
                default: None,
                initial_constraint: None,
            }],
            transitions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };

        let program = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };

        let env = DefEnv::from_ir(&program);
        let receiver = IRExpr::Var {
            name: "o".to_owned(),
            ty: IRType::Entity {
                name: "Order".to_owned(),
            },
            span: None,
        };

        // `status` is a regular field, not derived — must return None.
        assert!(env.expand_entity_derived(&receiver, "status").is_none());
    }

    /// a `let`-bound name inside a derived
    /// field body that shadows an entity field name must NOT be
    /// rewritten as `receiver.<name>` during expansion. Pre-fix the
    /// rewriter ignored binders and clobbered the `let` body's `status`
    /// reference.
    #[test]
    fn expand_entity_derived_respects_let_binder_shadowing() {
        use crate::ir::types::{IRDerivedField, IREntity, IRField, LetBinding};

        let entity = IREntity {
            name: "Order".to_owned(),
            fields: vec![IRField {
                name: "status".to_owned(),
                ty: IRType::Int,
                default: None,
                initial_constraint: None,
            }],
            transitions: vec![],
            derived_fields: vec![IRDerivedField {
                name: "shadowed".to_owned(),
                // body: let status = 5 in status
                body: IRExpr::Let {
                    bindings: vec![LetBinding {
                        name: "status".to_owned(),
                        ty: IRType::Int,
                        expr: IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 5 },
                            span: None,
                        },
                    }],
                    body: Box::new(IRExpr::Var {
                        name: "status".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    span: None,
                },
                ty: IRType::Int,
            }],
            invariants: vec![],
            fsm_decls: vec![],
        };

        let program = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };

        let env = DefEnv::from_ir(&program);
        let receiver = IRExpr::Var {
            name: "o".to_owned(),
            ty: IRType::Entity {
                name: "Order".to_owned(),
            },
            span: None,
        };

        let expanded = env
            .expand_entity_derived(&receiver, "shadowed")
            .expect("derived field should expand");

        // Expect `let status = 5 in status` — the inner Var must
        // remain a Var (referencing the let binding), NOT be rewritten
        // to `o.status` (which would change the meaning).
        let IRExpr::Let { body, .. } = expanded else {
            panic!("expected Let at top level");
        };
        let IRExpr::Var { name, .. } = *body else {
            panic!(
                "let body must remain a Var (the let-bound `status`), \
                 NOT be rewritten to a Field"
            );
        };
        assert_eq!(name, "status");
    }

    /// a quantifier-bound variable that
    /// shadows an entity field name must NOT be rewritten as
    /// `receiver.<name>` inside the quantifier body.
    #[test]
    fn expand_entity_derived_respects_quant_binder_shadowing() {
        use crate::ir::types::{IRDerivedField, IREntity, IRField};

        let entity = IREntity {
            name: "Order".to_owned(),
            fields: vec![IRField {
                name: "status".to_owned(),
                ty: IRType::Int,
                default: None,
                initial_constraint: None,
            }],
            transitions: vec![],
            derived_fields: vec![IRDerivedField {
                name: "any_pos".to_owned(),
                // body: forall status: Int. status > 0
                body: IRExpr::Forall {
                    var: "status".to_owned(),
                    domain: IRType::Int,
                    body: Box::new(IRExpr::BinOp {
                        op: "OpGt".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "status".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        }),
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 0 },
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    span: None,
                },
                ty: IRType::Bool,
            }],
            invariants: vec![],
            fsm_decls: vec![],
        };

        let program = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };

        let env = DefEnv::from_ir(&program);
        let receiver = IRExpr::Var {
            name: "o".to_owned(),
            ty: IRType::Entity {
                name: "Order".to_owned(),
            },
            span: None,
        };

        let expanded = env
            .expand_entity_derived(&receiver, "any_pos")
            .expect("derived field should expand");

        // Expect `forall status: Int. status > 0`. The `status` inside
        // the forall body must remain a Var (the quantifier binder),
        // NOT be rewritten to `o.status`.
        let IRExpr::Forall { body, .. } = expanded else {
            panic!("expected Forall at top level");
        };
        let IRExpr::BinOp { left, .. } = *body else {
            panic!("expected BinOp in forall body");
        };
        let IRExpr::Var { name, .. } = *left else {
            panic!(
                "left of comparison must remain a Var (the quantifier-bound \
                 `status`), NOT be rewritten to a Field"
            );
        };
        assert_eq!(name, "status");
    }

    /// a system-level derived field is registered
    /// in the existing `defs` map (as a nullary def, like `prop`) so
    /// that bare-`Var` references to it expand via `expand_var`.
    #[test]
    fn system_derived_field_expands_via_var() {
        use crate::ir::types::{IRDerivedField, IRSystem};

        let system = IRSystem {
            name: "Shop".to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: vec![],
            commands: vec![],
            actions: vec![],
            fsm_decls: vec![],
            derived_fields: vec![IRDerivedField {
                name: "always_true".to_owned(),
                body: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                ty: IRType::Bool,
            }],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        };

        let program = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![],
            systems: vec![system],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };

        let env = DefEnv::from_ir(&program);
        let expanded = env
            .expand_var("always_true")
            .expect("system derived should expand via expand_var");
        assert!(matches!(
            expanded,
            IRExpr::Lit {
                value: LitVal::Bool { value: true },
                ..
            }
        ));
    }

    #[test]
    fn rewrite_entity_invariant_body_rewrites_field_refs() {
        let program = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![IREntity {
                name: "Order".to_owned(),
                fields: vec![IRField {
                    name: "status".to_owned(),
                    ty: IRType::Int,
                    default: None,
                    initial_constraint: None,
                }],
                transitions: vec![],
                derived_fields: vec![],
                invariants: vec![],
                fsm_decls: vec![],
            }],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };

        let env = DefEnv::from_ir(&program);
        let receiver = IRExpr::Var {
            name: "o".to_owned(),
            ty: IRType::Entity {
                name: "Order".to_owned(),
            },
            span: None,
        };
        let body = IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::Var {
                name: "status".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 1 },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };

        let rewritten = env.rewrite_entity_invariant_body(body, &receiver, "Order");
        let IRExpr::BinOp { left, .. } = rewritten else {
            panic!("expected BinOp");
        };
        assert!(matches!(
            left.as_ref(),
            IRExpr::Field { expr, field, .. }
                if field == "status"
                    && matches!(expr.as_ref(), IRExpr::Var { name, .. } if name == "o")
        ));
    }
}
