//! Pass 2: Resolve names to fully-qualified references.
//!
//! Resolves `TyUnresolved` references to actual types from the environment.
//! Resolves constructor names (e.g., `EVar "Pending"` → constructor of `OrderStatus`).

use std::collections::HashMap;

use super::env::Env;
use super::error::{ElabError, ErrorKind};
use super::types::{
    BuiltinTy, EContract, EEventAction, EExpr, ELetBinding, EMatchArm, EMatchScrutinee, EProc,
    EProcDepCond, EProcEdge, EProcNode, EProcUse, ESceneWhen, EStoreDecl, ESystem, GenericTypeDef,
    Literal, Ty, VariantFieldsMap,
};
use crate::ast::UseDecl;

mod expr;
use expr::{collect_epattern_vars, resolve_ctor_type_from_context, resolve_expr};
mod monomorphize;
use monomorphize::{
    collect_all_param_uses, format_mono_name, monomorphize_generics, monomorphize_inline,
};
mod assumptions;
use assumptions::{resolve_assumption_sets, resolve_by_lemmas_subset_containment};
mod validate;
use validate::{
    validate_aggregate_bodies, validate_remaining_type_params, validate_saw_expressions,
    validate_set_comprehension_sources, validate_unresolved_types,
};

/// Immutable context for expression resolution, cloned once from Env.
pub(super) struct Ctx {
    types: HashMap<String, Ty>,
    entities: HashMap<String, crate::elab::types::EEntity>,
    /// Map from entity key (possibly alias) → canonical entity name.
    /// Used by `resolve_ty` to create `Ty::Entity` with canonical names.
    entity_canonical: HashMap<String, String>,
    /// Alias → canonical name map for rewriting aliased references.
    aliases: HashMap<String, String>,
    /// Constructor field info for enums with record variants.
    variant_fields: VariantFieldsMap,
    /// extern command parameter arities, keyed by
    /// `(extern_name, command_name)` → param count. Used to validate
    /// `saw Extern::command(args)` at resolution time.
    event_arities: HashMap<(String, String), usize>,
    /// generic type definitions for monomorphization in resolve_ty.
    generic_types: HashMap<String, GenericTypeDef>,
}

impl Ctx {
    fn from_env(env: &Env) -> Self {
        let entity_canonical: HashMap<String, String> = env
            .entities
            .iter()
            .map(|(key, entity)| (key.clone(), entity.name.clone()))
            .collect();
        let mut event_arities = HashMap::new();
        for ext in env.externs.values() {
            for cmd in &ext.commands {
                event_arities.insert((ext.name.clone(), cmd.name.clone()), cmd.params.len());
            }
        }
        Self {
            types: env.types.clone(),
            entities: env.entities.clone(),
            entity_canonical,
            aliases: env.aliases.clone(),
            variant_fields: env.variant_fields.clone(),
            event_arities,
            generic_types: env.generic_types.clone(),
        }
    }

    fn resolve_ty(&self, ty: &Ty) -> Ty {
        resolve_ty(&self.types, &self.entity_canonical, &self.generic_types, ty)
    }

    /// Resolve an alias to its canonical name, or return the name as-is.
    fn canonical_name<'a>(&'a self, name: &'a str) -> &'a str {
        self.aliases.get(name).map_or(name, String::as_str)
    }
}

fn expected_real_ty(ty: &Ty) -> bool {
    match ty {
        Ty::Builtin(BuiltinTy::Real) => true,
        Ty::Alias(_, inner) | Ty::Refinement(inner, _) => expected_real_ty(inner),
        _ => false,
    }
}

fn coerce_int_literal_to_real_if_expected(expr: &mut EExpr, expected: &Ty) {
    if !expected_real_ty(expected) {
        return;
    }
    if let EExpr::Lit(Ty::Builtin(BuiltinTy::Int), Literal::Int(value), span) = expr {
        *expr = EExpr::Lit(
            Ty::Builtin(BuiltinTy::Real),
            Literal::Real(*value as f64),
            *span,
        );
    }
}

/// Resolve all names in the collected environment.
pub fn resolve(env: &mut Env) {
    resolve_use_declarations(env);
    expand_proc_uses(env);
    resolve_all_types(env);
    monomorphize_generics(env);
    resolve_type_refinement_predicates(env);

    let ctx = Ctx::from_env(env);
    resolve_entities(env, &ctx);
    resolve_systems(env, &ctx);
    resolve_externs(env, &ctx);
    resolve_preds(env, &ctx);
    resolve_props(env, &ctx);
    resolve_verifies(env, &ctx);
    resolve_scenes(env, &ctx);
    resolve_theorems(env, &ctx);
    resolve_lemmas(env, &ctx);
    resolve_axioms(env, &ctx);
    resolve_consts(env, &ctx);
    resolve_fns(env, &ctx);

    // populate normalized `AssumptionSet` from each
    // verify/theorem/lemma's parsed `assume_block`. Runs late so all
    // systems are visible for event-path resolution.
    resolve_assumption_sets(env);

    // subset-containment check for `by L` lemma
    // references on theorems. Runs after `resolve_assumption_sets` so
    // every theorem and lemma has its effective assumption set.
    resolve_by_lemmas_subset_containment(env);

    // validate `saw Extern::command(args)` expressions —
    // check extern path resolves and arity matches.
    validate_saw_expressions(env, &ctx);

    // validate aggregate body types —
    // count body must be bool, sum/product/min/max body must be numeric.
    validate_aggregate_bodies(env);

    // validate source-less set comprehensions over non-enumerable domains.
    validate_set_comprehension_sources(env);

    // catch any Ty::Param that survived resolution — wrong-arity
    // generics or non-generic types used with type args in expression-level
    // positions (let bindings, lambda params, etc.) that the pre-pass missed.
    validate_remaining_type_params(env);

    validate_store_bounds(env);

    validate_unresolved_types(env);
}

fn validate_store_bounds(env: &mut Env) {
    let mut errors = Vec::new();

    for verify in &env.verifies {
        validate_store_decl_bounds("verify", &verify.name, &verify.stores, &mut errors);
        validate_store_binding_bounds(
            "verify",
            &verify.name,
            &verify.stores,
            &verify.let_bindings,
            env,
            &mut errors,
        );
    }
    for scene in &env.scenes {
        validate_store_decl_bounds("scene", &scene.name, &scene.stores, &mut errors);
        validate_store_binding_bounds(
            "scene",
            &scene.name,
            &scene.stores,
            &scene.let_bindings,
            env,
            &mut errors,
        );
    }
    for system in env.systems.values() {
        validate_store_param_binding_bounds(system, env, &mut errors);
    }

    env.errors.extend(errors);
}

fn validate_store_decl_bounds(
    owner_kind: &str,
    owner_name: &str,
    stores: &[EStoreDecl],
    errors: &mut Vec<ElabError>,
) {
    for store in stores {
        if store.lo < 0 || store.hi < 0 || store.lo > store.hi {
            errors.push(ElabError::new(
                ErrorKind::TypeMismatch,
                format!(
                    "{owner_kind} `{owner_name}` store `{}` has invalid finite bounds [{}..{}]",
                    store.name, store.lo, store.hi
                ),
                owner_kind,
            ));
        }
    }
}

fn validate_store_binding_bounds(
    owner_kind: &str,
    owner_name: &str,
    stores: &[EStoreDecl],
    let_bindings: &[ELetBinding],
    env: &Env,
    errors: &mut Vec<ElabError>,
) {
    for binding in let_bindings {
        let Some(system) = env.systems.get(&binding.system_type) else {
            continue;
        };
        for (param_name, store_name) in &binding.store_bindings {
            let Some(param) = system
                .store_params
                .iter()
                .find(|param| param.name == *param_name)
            else {
                continue;
            };
            let Some(store) = stores.iter().find(|store| store.name == *store_name) else {
                continue;
            };
            if let Some(min) = param.lo {
                if store.lo < min {
                    errors.push(ElabError::new(
                        ErrorKind::TypeMismatch,
                        format!(
                            "{owner_kind} `{owner_name}` binds store `{store_name}` with lower bound {} to `{}::{param_name}`, which requires at least {min} active entity slot(s)",
                            store.lo, system.name
                        ),
                        owner_kind,
                    ));
                }
            }
            if let Some(max) = param.hi {
                if store.hi > max {
                    errors.push(ElabError::new(
                        ErrorKind::TypeMismatch,
                        format!(
                            "{owner_kind} `{owner_name}` binds store `{store_name}` with upper bound {} to `{}::{param_name}`, which allows at most {max} slot(s)",
                            store.hi, system.name
                        ),
                        owner_kind,
                    ));
                }
            }
        }
    }
}

fn validate_store_param_binding_bounds(system: &ESystem, env: &Env, errors: &mut Vec<ElabError>) {
    if system.let_bindings.is_empty() {
        return;
    }

    for binding in &system.let_bindings {
        let Some(child_system) = env.systems.get(&binding.system_type) else {
            continue;
        };
        for (child_param_name, parent_param_name) in &binding.store_bindings {
            let Some(child_param) = child_system
                .store_params
                .iter()
                .find(|param| param.name == *child_param_name)
            else {
                continue;
            };
            let Some(parent_param) = system
                .store_params
                .iter()
                .find(|param| param.name == *parent_param_name)
            else {
                continue;
            };
            if let Some(min) = child_param.lo {
                match parent_param.lo {
                    Some(parent_min) if parent_min >= min => {}
                    Some(parent_min) => errors.push(ElabError::new(
                        ErrorKind::TypeMismatch,
                        format!(
                            "program/system `{}` binds store parameter `{parent_param_name}` with lower bound {parent_min} to `{}::{child_param_name}`, which requires at least {min} active entity slot(s)",
                            system.name, child_system.name
                        ),
                        "system store binding",
                    )),
                    None => errors.push(ElabError::new(
                        ErrorKind::TypeMismatch,
                        format!(
                            "program/system `{}` binds unbounded store parameter `{parent_param_name}` to `{}::{child_param_name}`, which requires at least {min} active entity slot(s)",
                            system.name, child_system.name
                        ),
                        "system store binding",
                    )),
                }
            }
            if let Some(max) = child_param.hi {
                match parent_param.hi {
                    Some(parent_max) if parent_max <= max => {}
                    Some(parent_max) => errors.push(ElabError::new(
                        ErrorKind::TypeMismatch,
                        format!(
                            "program/system `{}` binds store parameter `{parent_param_name}` with upper bound {parent_max} to `{}::{child_param_name}`, which allows at most {max} active entity slot(s)",
                            system.name, child_system.name
                        ),
                        "system store binding",
                    )),
                    None => errors.push(ElabError::new(
                        ErrorKind::TypeMismatch,
                        format!(
                            "program/system `{}` binds unbounded store parameter `{parent_param_name}` to `{}::{child_param_name}`, which allows at most {max} active entity slot(s)",
                            system.name, child_system.name
                        ),
                        "system store binding",
                    )),
                }
            }
        }
    }
}

fn expand_proc_uses(env: &mut Env) {
    let proc_defs = env.procs.clone();
    let mut errors = Vec::new();

    for system in env.systems.values_mut() {
        let let_bindings: HashMap<String, String> = system
            .let_bindings
            .iter()
            .map(|binding| (binding.name.clone(), binding.system_type.clone()))
            .collect();
        let mut expanded_program_uses = Vec::new();

        for proc_use in &system.proc_uses {
            let Some(proc_def) = proc_defs.get(&proc_use.proc_name).cloned() else {
                errors.push(ElabError::with_span(
                    ErrorKind::UndefinedRef,
                    format!(
                        "program `{}` uses unknown proc `{}`",
                        system.name, proc_use.proc_name
                    ),
                    "unknown proc",
                    proc_use
                        .span
                        .or(system.span)
                        .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                ));
                continue;
            };

            if proc_use.args.len() > proc_def.params.len() {
                errors.push(ElabError::with_span(
                    ErrorKind::ParamMismatch,
                    format!(
                        "proc `{}` exposes {} parameter(s) but program `{}` passed {} binding argument(s)",
                        proc_def.name,
                        proc_def.params.len(),
                        system.name,
                        proc_use.args.len()
                    ),
                    "proc use argument count mismatch",
                    proc_use
                        .span
                        .or(system.span)
                        .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                ));
                continue;
            }

            let mut binding_map = HashMap::new();
            let mut use_failed = false;
            for ((formal_name, formal_type), actual_name) in
                proc_def.params.iter().zip(proc_use.args.iter())
            {
                let Some(actual_type) = let_bindings.get(actual_name) else {
                    errors.push(ElabError::with_span(
                        ErrorKind::UndefinedRef,
                        format!(
                            "proc `{}` argument `{actual_name}` is not a let binding in program `{}`",
                            proc_def.name, system.name
                        ),
                        "unknown proc argument",
                        proc_use
                            .span
                            .or(system.span)
                            .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                    ));
                    use_failed = true;
                    continue;
                };

                if formal_type.name() != actual_type {
                    errors.push(ElabError::with_span(
                        ErrorKind::TypeMismatch,
                        format!(
                            "proc `{}` expects `{formal_name}: {}` but program `{}` passed let binding `{actual_name}` of type `{actual_type}`",
                            proc_def.name,
                            formal_type.name(),
                            system.name
                        ),
                        "proc argument type mismatch",
                        proc_use
                            .span
                            .or(system.span)
                            .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                    ));
                    use_failed = true;
                }

                binding_map.insert(formal_name.clone(), actual_name.clone());
            }

            if use_failed {
                continue;
            }

            let expanded_proc = instantiate_reusable_proc(
                &proc_def,
                &binding_map,
                None,
                &proc_defs,
                &let_bindings,
                system.span,
                &mut errors,
            );
            if let Some(expanded_proc) = expanded_proc {
                if system
                    .procs
                    .iter()
                    .chain(expanded_program_uses.iter())
                    .any(|existing: &EProc| existing.name == expanded_proc.name)
                {
                    errors.push(ElabError::with_span(
                        ErrorKind::DuplicateDecl,
                        format!(
                            "program `{}` already has a proc named `{}`; proc reuse would collide",
                            system.name, expanded_proc.name
                        ),
                        "duplicate proc after proc expansion",
                        proc_use
                            .span
                            .or(system.span)
                            .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                    ));
                    continue;
                }
                expanded_program_uses.push(expanded_proc);
            }
        }

        let original_procs = std::mem::take(&mut system.procs);
        let mut rewritten_procs = Vec::new();
        for proc_decl in original_procs {
            let proc_param_types: HashMap<String, Ty> = proc_decl.params.iter().cloned().collect();
            if let Some(expanded_proc) = expand_nested_proc_uses(
                proc_decl,
                &proc_defs,
                &let_bindings,
                &proc_param_types,
                system.span,
                &mut errors,
            ) {
                rewritten_procs.push(expanded_proc);
            }
        }

        rewritten_procs.extend(expanded_program_uses);
        system.procs = rewritten_procs;
        system.proc_uses.clear();
    }

    env.errors.extend(errors);
}

fn instantiate_reusable_proc(
    proc_def: &EProc,
    bindings: &HashMap<String, String>,
    alias_prefix: Option<&str>,
    proc_defs: &HashMap<String, EProc>,
    let_bindings: &HashMap<String, String>,
    fallback_span: Option<crate::span::Span>,
    errors: &mut Vec<ElabError>,
) -> Option<EProc> {
    let remaining_params = proc_def
        .params
        .iter()
        .filter(|(name, _)| !bindings.contains_key(name))
        .cloned()
        .collect::<Vec<_>>();

    let instantiated = EProc {
        name: proc_def.name.clone(),
        params: remaining_params,
        requires: proc_def
            .requires
            .as_ref()
            .map(|expr| substitute_expr(expr, bindings)),
        nodes: proc_def
            .nodes
            .iter()
            .map(|node| EProcNode {
                name: namespaced_node_name(alias_prefix, &node.name),
                instance: bindings
                    .get(&node.instance)
                    .cloned()
                    .unwrap_or_else(|| node.instance.clone()),
                command: node.command.clone(),
                args: node
                    .args
                    .iter()
                    .map(|arg| substitute_expr(arg, bindings))
                    .collect(),
            })
            .collect(),
        edges: proc_def
            .edges
            .iter()
            .map(|edge| EProcEdge {
                target: namespaced_node_name(alias_prefix, &edge.target),
                condition: namespace_dep_cond(
                    &substitute_proc_dep_cond(&edge.condition, bindings),
                    alias_prefix,
                ),
            })
            .collect(),
        proc_uses: proc_def
            .proc_uses
            .iter()
            .map(|proc_use| EProcUse {
                proc_name: proc_use.proc_name.clone(),
                args: proc_use
                    .args
                    .iter()
                    .map(|arg| bindings.get(arg).cloned().unwrap_or_else(|| arg.clone()))
                    .collect(),
                alias: proc_use
                    .alias
                    .as_ref()
                    .map(|alias| namespaced_node_name(alias_prefix, alias)),
                span: proc_use.span,
            })
            .collect(),
        span: proc_def.span,
    };

    let remaining_param_types: HashMap<String, Ty> = instantiated.params.iter().cloned().collect();

    expand_nested_proc_uses(
        instantiated,
        proc_defs,
        let_bindings,
        &remaining_param_types,
        fallback_span,
        errors,
    )
}

fn expand_nested_proc_uses(
    mut proc_decl: EProc,
    proc_defs: &HashMap<String, EProc>,
    let_bindings: &HashMap<String, String>,
    available_param_types: &HashMap<String, Ty>,
    fallback_span: Option<crate::span::Span>,
    errors: &mut Vec<ElabError>,
) -> Option<EProc> {
    if proc_decl.proc_uses.is_empty() {
        return Some(proc_decl);
    }

    let mut expanded_nodes = Vec::new();
    let mut expanded_edges = Vec::new();
    let use_items = std::mem::take(&mut proc_decl.proc_uses);
    for proc_use in use_items {
        let Some(alias) = proc_use.alias.as_ref() else {
            errors.push(ElabError::with_span(
                ErrorKind::ParamMismatch,
                format!(
                    "proc `{}` must use `as alias` when composing proc `{}`",
                    proc_decl.name, proc_use.proc_name
                ),
                "proc composition requires an alias",
                proc_use
                    .span
                    .or(proc_decl.span)
                    .or(fallback_span)
                    .unwrap_or(crate::span::Span { start: 0, end: 0 }),
            ));
            continue;
        };
        let Some(child_proc) = proc_defs.get(&proc_use.proc_name).cloned() else {
            errors.push(ElabError::with_span(
                ErrorKind::UndefinedRef,
                format!(
                    "proc `{}` composes unknown proc `{}`",
                    proc_decl.name, proc_use.proc_name
                ),
                "unknown proc",
                proc_use
                    .span
                    .or(proc_decl.span)
                    .or(fallback_span)
                    .unwrap_or(crate::span::Span { start: 0, end: 0 }),
            ));
            continue;
        };
        if proc_use.args.len() != child_proc.params.len() {
            errors.push(ElabError::with_span(
                ErrorKind::ParamMismatch,
                format!(
                    "proc `{}` composes `{}` with {} argument(s), but `{}` expects {}",
                    proc_decl.name,
                    proc_use.proc_name,
                    proc_use.args.len(),
                    proc_use.proc_name,
                    child_proc.params.len()
                ),
                "proc composition argument count mismatch",
                proc_use
                    .span
                    .or(proc_decl.span)
                    .or(fallback_span)
                    .unwrap_or(crate::span::Span { start: 0, end: 0 }),
            ));
            continue;
        }

        let mut child_bindings = HashMap::new();
        let mut bad_use = false;
        for ((formal_name, formal_ty), actual_name) in
            child_proc.params.iter().zip(proc_use.args.iter())
        {
            if let Some(actual_ty) = available_param_types.get(actual_name) {
                if !proc_param_types_compatible(formal_ty, actual_ty) {
                    errors.push(ElabError::with_span(
                        ErrorKind::TypeMismatch,
                        format!(
                            "proc `{}` expects `{formal_name}: {}` but composition passed parameter `{actual_name}: {}`",
                            proc_use.proc_name,
                            formal_ty.name(),
                            actual_ty.name()
                        ),
                        "proc composition argument type mismatch",
                        proc_use
                            .span
                            .or(proc_decl.span)
                            .or(fallback_span)
                            .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                    ));
                    bad_use = true;
                }
                child_bindings.insert(formal_name.clone(), actual_name.clone());
                continue;
            }
            if let Some(actual_system_type) = let_bindings.get(actual_name) {
                if formal_ty.name() != actual_system_type {
                    errors.push(ElabError::with_span(
                        ErrorKind::TypeMismatch,
                        format!(
                            "proc `{}` expects `{formal_name}: {}` but composition passed let binding `{actual_name}` of type `{actual_system_type}`",
                            proc_use.proc_name,
                            formal_ty.name()
                        ),
                        "proc composition argument type mismatch",
                        proc_use
                            .span
                            .or(proc_decl.span)
                            .or(fallback_span)
                            .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                    ));
                    bad_use = true;
                }
                child_bindings.insert(formal_name.clone(), actual_name.clone());
                continue;
            }
            errors.push(ElabError::with_span(
                ErrorKind::UndefinedRef,
                format!(
                    "proc `{}` composition argument `{actual_name}` is neither a proc parameter nor a let binding",
                    proc_use.proc_name
                ),
                "unknown proc composition argument",
                proc_use
                    .span
                    .or(proc_decl.span)
                    .or(fallback_span)
                    .unwrap_or(crate::span::Span { start: 0, end: 0 }),
            ));
            bad_use = true;
        }

        if bad_use {
            continue;
        }

        if let Some(child_expanded) = instantiate_reusable_proc(
            &child_proc,
            &child_bindings,
            Some(alias),
            proc_defs,
            let_bindings,
            proc_use.span.or(proc_decl.span).or(fallback_span),
            errors,
        ) {
            expanded_nodes.extend(child_expanded.nodes);
            expanded_edges.extend(child_expanded.edges);
        }
    }

    for edge in &mut proc_decl.edges {
        edge.condition = rewrite_composed_proc_refs(&edge.condition);
    }

    proc_decl.nodes.extend(expanded_nodes);
    proc_decl.edges.extend(expanded_edges);
    proc_decl.proc_uses.clear();
    Some(proc_decl)
}

fn namespaced_node_name(prefix: Option<&str>, name: &str) -> String {
    match prefix {
        Some(prefix) => format!("{prefix}__{name}"),
        None => name.to_string(),
    }
}

fn flatten_proc_ref(node: &str, prefix: Option<&str>) -> String {
    if let Some((alias, inner)) = node.split_once("::") {
        let alias = namespaced_node_name(prefix, alias);
        format!("{alias}__{inner}")
    } else {
        namespaced_node_name(prefix, node)
    }
}

fn namespace_dep_cond(cond: &EProcDepCond, prefix: Option<&str>) -> EProcDepCond {
    match cond {
        EProcDepCond::Fact { node, qualifier } => EProcDepCond::Fact {
            node: flatten_proc_ref(node, prefix),
            qualifier: qualifier.clone(),
        },
        EProcDepCond::Not(inner) => EProcDepCond::Not(Box::new(namespace_dep_cond(inner, prefix))),
        EProcDepCond::And(left, right) => EProcDepCond::And(
            Box::new(namespace_dep_cond(left, prefix)),
            Box::new(namespace_dep_cond(right, prefix)),
        ),
        EProcDepCond::Or(left, right) => EProcDepCond::Or(
            Box::new(namespace_dep_cond(left, prefix)),
            Box::new(namespace_dep_cond(right, prefix)),
        ),
    }
}

fn rewrite_composed_proc_refs(cond: &EProcDepCond) -> EProcDepCond {
    namespace_dep_cond(cond, None)
}

fn substitute_proc_dep_cond(
    cond: &EProcDepCond,
    _bindings: &HashMap<String, String>,
) -> EProcDepCond {
    cond.clone()
}

fn substitute_expr(expr: &EExpr, bindings: &HashMap<String, String>) -> EExpr {
    match expr {
        EExpr::Var(ty, name, span) => EExpr::Var(
            ty.clone(),
            bindings.get(name).cloned().unwrap_or_else(|| name.clone()),
            *span,
        ),
        EExpr::Field(ty, base, field, span) => EExpr::Field(
            ty.clone(),
            Box::new(substitute_expr(base, bindings)),
            field.clone(),
            *span,
        ),
        EExpr::Prime(ty, inner, span) => EExpr::Prime(
            ty.clone(),
            Box::new(substitute_expr(inner, bindings)),
            *span,
        ),
        EExpr::BinOp(ty, op, left, right, span) => EExpr::BinOp(
            ty.clone(),
            *op,
            Box::new(substitute_expr(left, bindings)),
            Box::new(substitute_expr(right, bindings)),
            *span,
        ),
        EExpr::UnOp(ty, op, inner, span) => EExpr::UnOp(
            ty.clone(),
            *op,
            Box::new(substitute_expr(inner, bindings)),
            *span,
        ),
        EExpr::Call(ty, func, args, span) => EExpr::Call(
            ty.clone(),
            Box::new(substitute_expr(func, bindings)),
            args.iter()
                .map(|arg| substitute_expr(arg, bindings))
                .collect(),
            *span,
        ),
        EExpr::CallR(ty, func, refs, args, span) => EExpr::CallR(
            ty.clone(),
            Box::new(substitute_expr(func, bindings)),
            refs.iter()
                .map(|arg| substitute_expr(arg, bindings))
                .collect(),
            args.iter()
                .map(|arg| substitute_expr(arg, bindings))
                .collect(),
            *span,
        ),
        EExpr::Quant(ty, quant, name, domain_ty, body, span) => EExpr::Quant(
            ty.clone(),
            *quant,
            name.clone(),
            domain_ty.clone(),
            Box::new(substitute_expr(
                body,
                &bindings_without(bindings, &[name.as_str()]),
            )),
            *span,
        ),
        EExpr::Always(ty, inner, span) => EExpr::Always(
            ty.clone(),
            Box::new(substitute_expr(inner, bindings)),
            *span,
        ),
        EExpr::Eventually(ty, inner, span) => EExpr::Eventually(
            ty.clone(),
            Box::new(substitute_expr(inner, bindings)),
            *span,
        ),
        EExpr::Until(ty, left, right, span) => EExpr::Until(
            ty.clone(),
            Box::new(substitute_expr(left, bindings)),
            Box::new(substitute_expr(right, bindings)),
            *span,
        ),
        EExpr::Historically(ty, inner, span) => EExpr::Historically(
            ty.clone(),
            Box::new(substitute_expr(inner, bindings)),
            *span,
        ),
        EExpr::Once(ty, inner, span) => EExpr::Once(
            ty.clone(),
            Box::new(substitute_expr(inner, bindings)),
            *span,
        ),
        EExpr::Previously(ty, inner, span) => EExpr::Previously(
            ty.clone(),
            Box::new(substitute_expr(inner, bindings)),
            *span,
        ),
        EExpr::Since(ty, left, right, span) => EExpr::Since(
            ty.clone(),
            Box::new(substitute_expr(left, bindings)),
            Box::new(substitute_expr(right, bindings)),
            *span,
        ),
        EExpr::Assert(ty, inner, span) => EExpr::Assert(
            ty.clone(),
            Box::new(substitute_expr(inner, bindings)),
            *span,
        ),
        EExpr::Assume(ty, inner, span) => EExpr::Assume(
            ty.clone(),
            Box::new(substitute_expr(inner, bindings)),
            *span,
        ),
        EExpr::Assign(ty, left, right, span) => EExpr::Assign(
            ty.clone(),
            Box::new(substitute_expr(left, bindings)),
            Box::new(substitute_expr(right, bindings)),
            *span,
        ),
        EExpr::NamedPair(ty, name, inner, span) => EExpr::NamedPair(
            ty.clone(),
            name.clone(),
            Box::new(substitute_expr(inner, bindings)),
            *span,
        ),
        EExpr::Seq(ty, left, right, span) => EExpr::Seq(
            ty.clone(),
            Box::new(substitute_expr(left, bindings)),
            Box::new(substitute_expr(right, bindings)),
            *span,
        ),
        EExpr::SameStep(ty, left, right, span) => EExpr::SameStep(
            ty.clone(),
            Box::new(substitute_expr(left, bindings)),
            Box::new(substitute_expr(right, bindings)),
            *span,
        ),
        EExpr::Let(bindings_decl, body, span) => EExpr::Let(
            bindings_decl
                .iter()
                .map(|(name, ty, value)| {
                    (name.clone(), ty.clone(), substitute_expr(value, bindings))
                })
                .collect(),
            Box::new(substitute_expr(
                body,
                &bindings_without(
                    bindings,
                    &bindings_decl
                        .iter()
                        .map(|(name, _, _)| name.as_str())
                        .collect::<Vec<_>>(),
                ),
            )),
            *span,
        ),
        EExpr::Lam(params, ret_ty, body, span) => EExpr::Lam(
            params.clone(),
            ret_ty.clone(),
            Box::new(substitute_expr(
                body,
                &bindings_without(
                    bindings,
                    &params
                        .iter()
                        .map(|(name, _)| name.as_str())
                        .collect::<Vec<_>>(),
                ),
            )),
            *span,
        ),
        EExpr::TupleLit(ty, items, span) => EExpr::TupleLit(
            ty.clone(),
            items
                .iter()
                .map(|item| substitute_expr(item, bindings))
                .collect(),
            *span,
        ),
        EExpr::In(ty, left, right, span) => EExpr::In(
            ty.clone(),
            Box::new(substitute_expr(left, bindings)),
            Box::new(substitute_expr(right, bindings)),
            *span,
        ),
        EExpr::Card(ty, inner, span) => EExpr::Card(
            ty.clone(),
            Box::new(substitute_expr(inner, bindings)),
            *span,
        ),
        EExpr::Pipe(ty, left, right, span) => EExpr::Pipe(
            ty.clone(),
            Box::new(substitute_expr(left, bindings)),
            Box::new(substitute_expr(right, bindings)),
            *span,
        ),
        EExpr::Match(scrutinee, arms, span) => EExpr::Match(
            Box::new(substitute_expr(scrutinee, bindings)),
            arms.iter()
                .map(|(pat, guard, body)| {
                    (
                        pat.clone(),
                        guard.as_ref().map(|g| substitute_expr(g, bindings)),
                        substitute_expr(body, bindings),
                    )
                })
                .collect(),
            *span,
        ),
        EExpr::Choose(ty, name, domain_ty, pred, span) => EExpr::Choose(
            ty.clone(),
            name.clone(),
            domain_ty.clone(),
            pred.as_ref().map(|expr| {
                Box::new(substitute_expr(
                    expr,
                    &bindings_without(bindings, &[name.as_str()]),
                ))
            }),
            *span,
        ),
        EExpr::MapUpdate(ty, map, key, value, span) => EExpr::MapUpdate(
            ty.clone(),
            Box::new(substitute_expr(map, bindings)),
            Box::new(substitute_expr(key, bindings)),
            Box::new(substitute_expr(value, bindings)),
            *span,
        ),
        EExpr::Index(ty, map, key, span) => EExpr::Index(
            ty.clone(),
            Box::new(substitute_expr(map, bindings)),
            Box::new(substitute_expr(key, bindings)),
            *span,
        ),
        EExpr::SetComp(ty, body, var, domain_ty, source, pred, span) => EExpr::SetComp(
            ty.clone(),
            body.as_ref().map(|expr| {
                Box::new(substitute_expr(
                    expr,
                    &bindings_without(bindings, &[var.as_str()]),
                ))
            }),
            var.clone(),
            domain_ty.clone(),
            source
                .as_ref()
                .map(|expr| Box::new(substitute_expr(expr, bindings))),
            Box::new(substitute_expr(
                pred,
                &bindings_without(bindings, &[var.as_str()]),
            )),
            *span,
        ),
        EExpr::RelComp(ty, projection, rel_bindings, filter, span) => {
            let bound_names = rel_bindings
                .iter()
                .map(|binding| binding.var.as_str())
                .collect::<Vec<_>>();
            let scoped_bindings = bindings_without(bindings, &bound_names);
            EExpr::RelComp(
                ty.clone(),
                Box::new(substitute_expr(projection, &scoped_bindings)),
                rel_bindings
                    .iter()
                    .map(|binding| crate::elab::types::ERelCompBinding {
                        var: binding.var.clone(),
                        domain: binding.domain.clone(),
                        source: binding
                            .source
                            .as_ref()
                            .map(|source| Box::new(substitute_expr(source, bindings))),
                    })
                    .collect(),
                Box::new(substitute_expr(filter, &scoped_bindings)),
                *span,
            )
        }
        EExpr::SetLit(ty, items, span) => EExpr::SetLit(
            ty.clone(),
            items
                .iter()
                .map(|item| substitute_expr(item, bindings))
                .collect(),
            *span,
        ),
        EExpr::SeqLit(ty, items, span) => EExpr::SeqLit(
            ty.clone(),
            items
                .iter()
                .map(|item| substitute_expr(item, bindings))
                .collect(),
            *span,
        ),
        EExpr::MapLit(ty, items, span) => EExpr::MapLit(
            ty.clone(),
            items
                .iter()
                .map(|(key, value)| {
                    (
                        substitute_expr(key, bindings),
                        substitute_expr(value, bindings),
                    )
                })
                .collect(),
            *span,
        ),
        EExpr::QualCall(ty, q, name, args, span) => EExpr::QualCall(
            ty.clone(),
            q.clone(),
            name.clone(),
            args.iter()
                .map(|arg| substitute_expr(arg, bindings))
                .collect(),
            *span,
        ),
        EExpr::Block(items, span) => EExpr::Block(
            items
                .iter()
                .map(|item| substitute_expr(item, bindings))
                .collect(),
            *span,
        ),
        EExpr::VarDecl(name, ty, init, rest, span) => EExpr::VarDecl(
            name.clone(),
            ty.clone(),
            Box::new(substitute_expr(init, bindings)),
            Box::new(substitute_expr(
                rest,
                &bindings_without(bindings, &[name.as_str()]),
            )),
            *span,
        ),
        EExpr::While(cond, contracts, body, span) => EExpr::While(
            Box::new(substitute_expr(cond, bindings)),
            contracts
                .iter()
                .map(|contract| match contract {
                    EContract::Requires(expr) => {
                        EContract::Requires(substitute_expr(expr, bindings))
                    }
                    EContract::Ensures(expr) => EContract::Ensures(substitute_expr(expr, bindings)),
                    EContract::Invariant(expr) => {
                        EContract::Invariant(substitute_expr(expr, bindings))
                    }
                    EContract::Decreases { measures, star } => EContract::Decreases {
                        measures: measures
                            .iter()
                            .map(|expr| substitute_expr(expr, bindings))
                            .collect(),
                        star: *star,
                    },
                })
                .collect(),
            Box::new(substitute_expr(body, bindings)),
            *span,
        ),
        EExpr::IfElse(cond, then_body, else_body, span) => EExpr::IfElse(
            Box::new(substitute_expr(cond, bindings)),
            Box::new(substitute_expr(then_body, bindings)),
            else_body
                .as_ref()
                .map(|expr| Box::new(substitute_expr(expr, bindings))),
            *span,
        ),
        EExpr::Aggregate(ty, kind, var, domain_ty, body, filter, span) => EExpr::Aggregate(
            ty.clone(),
            *kind,
            var.clone(),
            domain_ty.clone(),
            Box::new(substitute_expr(
                body,
                &bindings_without(bindings, &[var.as_str()]),
            )),
            filter.as_ref().map(|expr| {
                Box::new(substitute_expr(
                    expr,
                    &bindings_without(bindings, &[var.as_str()]),
                ))
            }),
            *span,
        ),
        EExpr::Saw(ty, system, event, args, span) => EExpr::Saw(
            ty.clone(),
            system.clone(),
            event.clone(),
            args.iter()
                .map(|arg| {
                    arg.as_ref()
                        .map(|expr| Box::new(substitute_expr(expr, bindings)))
                })
                .collect(),
            *span,
        ),
        EExpr::CtorRecord(ty, qualifier, ctor, fields, span) => EExpr::CtorRecord(
            ty.clone(),
            qualifier.clone(),
            ctor.clone(),
            fields
                .iter()
                .map(|(name, value)| (name.clone(), substitute_expr(value, bindings)))
                .collect(),
            *span,
        ),
        EExpr::StructCtor(ty, name, fields, span) => EExpr::StructCtor(
            ty.clone(),
            name.clone(),
            fields
                .iter()
                .map(|(field, value)| (field.clone(), substitute_expr(value, bindings)))
                .collect(),
            *span,
        ),
        other => other.clone(),
    }
}

fn bindings_without(bindings: &HashMap<String, String>, names: &[&str]) -> HashMap<String, String> {
    let mut filtered = bindings.clone();
    for name in names {
        filtered.remove(*name);
    }
    filtered
}

fn proc_param_types_compatible(formal: &Ty, actual: &Ty) -> bool {
    formal.name() == actual.name()
}

// ── Use declaration validation ──────────────────────────────────────

/// Validate use declarations and populate the working namespace.
///
/// For each `use` declaration:
/// 1. Validate the target module and names exist
/// 2. Check the target module and declaration exist
/// 3. Import declarations into the bare-name working namespace
///    (types, entities, systems, preds, props maps) so downstream
///    resolve/check/lower passes can find them by unqualified name.
#[allow(clippy::too_many_lines)]
fn resolve_use_declarations(env: &mut Env) {
    // Clear aliases from any prior resolve pass (idempotent reset).
    env.aliases.clear();

    let known_modules = env.known_modules.clone();
    let root_module = env.module_name.clone();

    // Check for circular use dependencies reachable from the root module.
    // Scoped so unrelated cycles in other workspace modules don't block
    // compilation of the target module.
    check_use_cycles(env, root_module.as_deref());

    // Only process use declarations from the current root module.
    // Use declarations from other loaded modules should not affect
    // the root module's namespace.
    let use_decls: Vec<_> = env
        .use_decls
        .iter()
        .filter(|entry| entry.source_module == root_module)
        .cloned()
        .collect();

    // Collect imports to apply: (local_name, source_module, source_name)
    let mut imports: Vec<(String, String, String)> = Vec::new();
    let mut errors: Vec<ElabError> = Vec::new();

    for entry in &use_decls {
        let ud = &entry.decl;
        let importing = entry.source_module.as_deref();
        let use_file = entry.source_file.as_deref();

        match ud {
            UseDecl::All { module, span } => {
                if !known_modules.contains(module) {
                    // In multi-module mode (at least one module declaration exists),
                    // an unknown module is likely a typo or missing file — warn.
                    // In single-file / no-module mode, skip silently.
                    if !known_modules.is_empty() {
                        let mut warn = ElabError::with_span(
                            ErrorKind::UndefinedRef,
                            format!("unknown module '{module}' in use declaration"),
                            "module not found".to_owned(),
                            *span,
                        )
                        .with_help(format!(
                            "no module '{module}' was loaded — check the module name or ensure the file is included"
                        ));
                        warn.severity = super::error::Severity::Warning;
                        if let Some(f) = use_file {
                            warn.file = Some(f.to_owned());
                        }
                        env.errors.push(warn);
                    }
                    continue;
                }
                let imported_decls: Vec<String> = env
                    .decls_in_module(module)
                    .iter()
                    .filter(|d| import_is_visible(d, importing))
                    .map(|d| d.name.clone())
                    .collect();
                for name in imported_decls {
                    imports.push((name.clone(), module.clone(), name));
                }
                let _ = span;
            }
            UseDecl::Single { module, name, span } => {
                if let Some(mut err) =
                    check_import_target(env, &known_modules, module, name, importing, *span)
                {
                    if err.file.is_none() {
                        err.file = use_file.map(str::to_owned);
                    }
                    errors.push(err);
                } else {
                    imports.push((name.clone(), module.clone(), name.clone()));
                }
            }
            UseDecl::Alias {
                module,
                name,
                alias,
                span,
            } => {
                if let Some(mut err) =
                    check_import_target(env, &known_modules, module, name, importing, *span)
                {
                    if err.file.is_none() {
                        err.file = use_file.map(str::to_owned);
                    }
                    errors.push(err);
                } else {
                    imports.push((alias.clone(), module.clone(), name.clone()));
                }
            }
            UseDecl::Items {
                module,
                items,
                span,
            } => {
                for item in items {
                    let (name, local, item_span) = match item {
                        crate::ast::UseItem::Name { name, span: s } => {
                            (name.as_str(), name.clone(), *s)
                        }
                        crate::ast::UseItem::Alias {
                            name,
                            alias,
                            span: s,
                        } => (name.as_str(), alias.clone(), *s),
                    };
                    if let Some(mut err) =
                        check_import_target(env, &known_modules, module, name, importing, item_span)
                    {
                        if err.file.is_none() {
                            err.file = use_file.map(str::to_owned);
                        }
                        errors.push(err);
                    } else {
                        imports.push((local, module.clone(), name.to_string()));
                    }
                }
                let _ = span;
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

fn import_is_visible(_decl: &super::env::DeclInfo, _importing_module: Option<&str>) -> bool {
    true
}

/// Check for circular dependencies in `use` declarations between modules.
///
/// Builds a module dependency graph (`source_module` → `target_module`) from all
/// use declarations and detects cycles reachable from the root module via DFS.
/// Scoped to the root so unrelated cycles elsewhere in the workspace don't
/// block compilation of unaffected modules.
///
/// Currently a **warning** — the flat qualified-store resolution does not
/// recurse and cannot loop. This will be upgraded to an error if/when
/// transitive re-export semantics are added.
fn check_use_cycles(env: &mut Env, root_module: Option<&str>) {
    use std::collections::{BTreeMap as Map, BTreeSet as Set};

    // When root_module is None (directory-load / QA / REPL), no use
    // declarations are actually materialized (the filter at line ~97
    // matches source_module == None, which no loaded module has).
    // Skip the check to stay consistent with resolution behavior.
    let Some(root) = root_module else {
        return;
    };

    // Build adjacency: module → sorted set of modules it imports from.
    // BTreeMap/BTreeSet for deterministic iteration order.
    let mut deps: Map<String, Set<String>> = Map::new();
    let mut first_span: Map<(String, String), (crate::span::Span, Option<String>)> = Map::new();

    for entry in &env.use_decls {
        let Some(ref src) = entry.source_module else {
            continue;
        };
        let target = match &entry.decl {
            UseDecl::All { module, .. }
            | UseDecl::Single { module, .. }
            | UseDecl::Alias { module, .. }
            | UseDecl::Items { module, .. } => module,
        };
        if src == target {
            continue; // same-module import, not a cross-module dependency
        }
        if !env.known_modules.contains(target) {
            continue; // unknown module, already warned about elsewhere
        }
        deps.entry(src.clone()).or_default().insert(target.clone());
        let edge_key = (src.clone(), target.clone());
        first_span.entry(edge_key).or_insert_with(|| {
            let span = match &entry.decl {
                UseDecl::All { span, .. }
                | UseDecl::Single { span, .. }
                | UseDecl::Alias { span, .. }
                | UseDecl::Items { span, .. } => *span,
            };
            (span, entry.source_file.clone())
        });
    }

    if deps.is_empty() {
        return;
    }

    // DFS cycle detection — only from the root module.
    let mut visited = Set::new();
    let mut in_stack = Set::new();

    if let Some(cycle) = dfs_use_cycle(root, &deps, &mut visited, &mut in_stack, &mut Vec::new()) {
        let chain = cycle.join(" → ");
        let (span, file) = if cycle.len() >= 2 {
            first_span
                .get(&(cycle[0].clone(), cycle[1].clone()))
                .cloned()
                .unwrap_or((crate::span::Span { start: 0, end: 0 }, None))
        } else {
            (crate::span::Span { start: 0, end: 0 }, None)
        };
        let mut warn = ElabError::with_span(
            ErrorKind::CyclicImport,
            format!("circular use dependency: {chain}"),
            "use declaration creates cycle".to_owned(),
            span,
        )
        .with_help(crate::messages::HELP_CIRCULAR_USE);
        warn.severity = super::error::Severity::Warning;
        if let Some(f) = file {
            warn.file = Some(f);
        }
        env.errors.push(warn);
    }
}

fn dfs_use_cycle(
    node: &str,
    deps: &std::collections::BTreeMap<String, std::collections::BTreeSet<String>>,
    visited: &mut std::collections::BTreeSet<String>,
    in_stack: &mut std::collections::BTreeSet<String>,
    path: &mut Vec<String>,
) -> Option<Vec<String>> {
    visited.insert(node.to_owned());
    in_stack.insert(node.to_owned());
    path.push(node.to_owned());

    if let Some(neighbors) = deps.get(node) {
        // BTreeSet iterates in sorted order — deterministic cycle reporting.
        for neighbor in neighbors {
            if in_stack.contains(neighbor.as_str()) {
                let pos = path.iter().position(|p| p == neighbor).unwrap_or(0);
                let mut cycle: Vec<String> = path[pos..].to_vec();
                cycle.push(neighbor.clone());
                return Some(cycle);
            }
            if !visited.contains(neighbor.as_str()) {
                if let Some(cycle) = dfs_use_cycle(neighbor, deps, visited, in_stack, path) {
                    return Some(cycle);
                }
            }
        }
    }

    path.pop();
    in_stack.remove(node);
    None
}

/// Check that an import target exists and belongs to the right module.
/// Returns `Some(error)` if validation fails, `None` if OK.
fn check_import_target(
    env: &Env,
    known_modules: &std::collections::HashSet<String>,
    target_module: &str,
    target_name: &str,
    _importing_module: Option<&str>,
    use_span: crate::span::Span,
) -> Option<ElabError> {
    if !known_modules.contains(target_module) {
        // In multi-module mode, warn about unknown module references.
        // In single-file / no-module mode, skip silently.
        // This is a warning (not error) because the module may simply
        // not be loaded in this compilation unit.
        if !known_modules.is_empty() {
            let mut warn = ElabError::with_span(
                ErrorKind::UndefinedRef,
                format!("unknown module '{target_module}' in use declaration"),
                "module not found".to_owned(),
                use_span,
            )
            .with_help(format!(
                "no module '{target_module}' was loaded — check the module name or ensure the file is included"
            ));
            warn.severity = super::error::Severity::Warning;
            return Some(warn);
        }
        return None;
    }

    if let Some(decl) = env.lookup_decl_qualified(target_module, target_name) {
        let _ = (decl, _importing_module);
        None
    } else {
        // Suggest closest name in the target module
        let module_names: Vec<String> = env
            .decls_in_module(target_module)
            .iter()
            .map(|d| d.name.clone())
            .collect();
        let mut err = ElabError::with_span(
            ErrorKind::UndefinedRef,
            format!("module '{target_module}' does not export '{target_name}'"),
            String::new(),
            use_span,
        );
        if let Some(closest) = super::check::find_closest_name(target_name, &module_names) {
            err = err.with_help(format!("did you mean '{closest}'?"));
        }
        Some(err)
    }
}

// ── Type resolution ──────────────────────────────────────────────────

fn resolve_all_types(env: &mut Env) {
    let snapshot = env.types.clone();
    let entity_canonical: HashMap<String, String> = env
        .entities
        .iter()
        .map(|(key, entity)| (key.clone(), entity.name.clone()))
        .collect();
    let generic_types = env.generic_types.clone();
    for ty in env.types.values_mut() {
        *ty = resolve_ty(&snapshot, &entity_canonical, &generic_types, ty);
    }
}

/// Resolve `$` in refinement predicates of type aliases.
/// For `type Positive = int { $ > 0 }`, binds `$` to `int` before resolving the predicate.
fn resolve_type_refinement_predicates(env: &mut Env) {
    let ctx = Ctx::from_env(env);
    for ty in env.types.values_mut() {
        if let Ty::Refinement(base, pred) = ty {
            let mut bound = HashMap::new();
            bound.insert("$".to_owned(), (**base).clone());
            **pred = resolve_expr(&ctx, &bound, pred);
        }
    }
}

fn resolve_ty(
    types: &HashMap<String, Ty>,
    entities: &HashMap<String, String>,
    generic_types: &HashMap<String, GenericTypeDef>,
    ty: &Ty,
) -> Ty {
    match ty {
        Ty::Named(n) => {
            if let Some(t) = types.get(n.as_str()) {
                t.clone()
            } else if let Some(canonical) = entities.get(n.as_str()) {
                // Use the entity's canonical name (from its declaration),
                // not the possibly-aliased import key.
                Ty::Entity(canonical.clone())
            } else {
                ty.clone()
            }
        }
        Ty::Record(n, fs) => Ty::Record(
            n.clone(),
            fs.iter()
                .map(|(fn_, ft)| (fn_.clone(), resolve_ty(types, entities, generic_types, ft)))
                .collect(),
        ),
        Ty::Param(n, args) => {
            let resolved_args: Vec<Ty> = args
                .iter()
                .map(|a| resolve_ty(types, entities, generic_types, a))
                .collect();
            // if this names a generic enum, monomorphize
            if let Some(gdef) = generic_types.get(n.as_str()) {
                if resolved_args.len() == gdef.type_params.len() {
                    let mono_name = format_mono_name(n, &resolved_args);
                    // If already registered from pre-pass, use it
                    if let Some(t) = types.get(&mono_name) {
                        return t.clone();
                    }
                    // Otherwise build inline (may happen during expression resolution)
                    return monomorphize_inline(gdef, &resolved_args);
                }
            }
            Ty::Param(n.clone(), resolved_args)
        }
        Ty::Alias(n, t) => Ty::Alias(
            n.clone(),
            Box::new(resolve_ty(types, entities, generic_types, t)),
        ),
        Ty::Newtype(n, t) => Ty::Newtype(
            n.clone(),
            Box::new(resolve_ty(types, entities, generic_types, t)),
        ),
        Ty::Fn(a, b) => Ty::Fn(
            Box::new(resolve_ty(types, entities, generic_types, a)),
            Box::new(resolve_ty(types, entities, generic_types, b)),
        ),
        Ty::Set(a) => Ty::Set(Box::new(resolve_ty(types, entities, generic_types, a))),
        Ty::Seq(a) => Ty::Seq(Box::new(resolve_ty(types, entities, generic_types, a))),
        Ty::Map(k, v) => Ty::Map(
            Box::new(resolve_ty(types, entities, generic_types, k)),
            Box::new(resolve_ty(types, entities, generic_types, v)),
        ),
        Ty::Store(entity) => Ty::Store(
            entities
                .get(entity.as_str())
                .cloned()
                .unwrap_or_else(|| entity.clone()),
        ),
        Ty::Relation(columns) => Ty::Relation(
            columns
                .iter()
                .map(|column| resolve_ty(types, entities, generic_types, column))
                .collect(),
        ),
        Ty::Tuple(ts) => Ty::Tuple(
            ts.iter()
                .map(|t| resolve_ty(types, entities, generic_types, t))
                .collect(),
        ),
        Ty::Refinement(base, pred) => {
            let resolved_base = resolve_ty(types, entities, generic_types, base);
            Ty::Refinement(Box::new(resolved_base), pred.clone())
        }
        _ => ty.clone(),
    }
}

// ── Entity resolution ────────────────────────────────────────────────

fn resolve_entities(env: &mut Env, ctx: &Ctx) {
    for entity in env.entities.values_mut() {
        for field in &mut entity.fields {
            field.ty = ctx.resolve_ty(&field.ty);
            match &mut field.default {
                Some(crate::elab::types::EFieldDefault::Value(ref mut e)) => {
                    *e = resolve_expr(ctx, &HashMap::new(), e);
                    resolve_ctor_type_from_context(e, &field.ty);
                    coerce_int_literal_to_real_if_expected(e, &field.ty);
                }
                Some(crate::elab::types::EFieldDefault::In(ref mut es)) => {
                    for e in es.iter_mut() {
                        *e = resolve_expr(ctx, &HashMap::new(), e);
                        coerce_int_literal_to_real_if_expected(e, &field.ty);
                    }
                }
                Some(crate::elab::types::EFieldDefault::Where(ref mut e)) => {
                    *e = resolve_expr(ctx, &HashMap::new(), e);
                }
                None => {}
            }
        }
        for action in &mut entity.actions {
            action.refs = action
                .refs
                .iter()
                .map(|(n, t)| (n.clone(), ctx.resolve_ty(t)))
                .collect();
            let ref_bound: HashMap<String, Ty> = action
                .refs
                .iter()
                .map(|(n, t)| (n.clone(), t.clone()))
                .collect();
            let (resolved_params, action_bound) = resolve_params_lr(ctx, &action.params, ref_bound);
            action.params = resolved_params;
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
        // resolve system flat state field types and defaults
        for field in &mut system.fields {
            field.ty = ctx.resolve_ty(&field.ty);
            match &mut field.default {
                Some(crate::elab::types::EFieldDefault::Value(ref mut e)) => {
                    *e = resolve_expr(ctx, &HashMap::new(), e);
                    resolve_ctor_type_from_context(e, &field.ty);
                    coerce_int_literal_to_real_if_expected(e, &field.ty);
                }
                Some(crate::elab::types::EFieldDefault::In(ref mut es)) => {
                    for e in es.iter_mut() {
                        *e = resolve_expr(ctx, &HashMap::new(), e);
                        coerce_int_literal_to_real_if_expected(e, &field.ty);
                    }
                }
                Some(crate::elab::types::EFieldDefault::Where(ref mut e)) => {
                    *e = resolve_expr(ctx, &HashMap::new(), e);
                }
                None => {}
            }
        }
        for cmd in &mut system.commands {
            let (resolved_params, _) = resolve_params_lr(ctx, &cmd.params, HashMap::new());
            cmd.params = resolved_params;
            // resolve command return type
            if let Some(ref mut rt) = cmd.return_type {
                *rt = ctx.resolve_ty(rt);
            }
        }
        for step in &mut system.actions {
            let (resolved_params, step_bound) =
                resolve_params_lr(ctx, &step.params, HashMap::new());
            step.params = resolved_params;
            step.requires = step
                .requires
                .iter()
                .map(|e| resolve_expr(ctx, &step_bound, e))
                .collect();
            step.body = step
                .body
                .iter()
                .map(|ea| resolve_event_action(ctx, &step_bound, ea))
                .collect();
            // resolve action return expression
            if let Some(ref mut re) = step.return_expr {
                *re = resolve_expr(ctx, &step_bound, re);
            }
        }
        for query in &mut system.queries {
            let (resolved_params, query_bound) =
                resolve_params_lr(ctx, &query.params, HashMap::new());
            query.params = resolved_params;
            query.body = resolve_expr(ctx, &query_bound, &query.body);
        }
        // resolve system-local preds
        for pred in &mut system.preds {
            let (resolved_params, pred_bound) =
                resolve_params_lr(ctx, &pred.params, HashMap::new());
            pred.params = resolved_params;
            pred.body = resolve_expr(ctx, &pred_bound, &pred.body);
        }
    }
}

fn resolve_externs(env: &mut Env, ctx: &Ctx) {
    for ext in env.externs.values_mut() {
        for cmd in &mut ext.commands {
            let (resolved_params, _) = resolve_params_lr(ctx, &cmd.params, HashMap::new());
            cmd.params = resolved_params;
            if let Some(ref mut rt) = cmd.return_type {
                *rt = ctx.resolve_ty(rt);
            }
        }

        let command_return_types: HashMap<String, Option<Ty>> = ext
            .commands
            .iter()
            .map(|cmd| (cmd.name.clone(), cmd.return_type.clone()))
            .collect();

        for may in &mut ext.mays {
            let expected_return = command_return_types
                .get(&may.command)
                .and_then(|ty| ty.as_ref());
            for ret in &mut may.returns {
                *ret = resolve_expr(ctx, &HashMap::new(), ret);
                if let Some(expected) = expected_return {
                    resolve_ctor_type_from_context(ret, expected);
                }
            }
        }

        for assume in &mut ext.assumes {
            if let crate::elab::types::EExternAssume::Expr(expr, _) = assume {
                *expr = resolve_expr(ctx, &HashMap::new(), expr);
            }
        }
    }
}

fn resolve_event_action(ctx: &Ctx, bound: &HashMap<String, Ty>, ea: &EEventAction) -> EEventAction {
    match ea {
        EEventAction::Choose(v, ty, guard, body) => {
            let resolved_ty = ctx.resolve_ty(ty);
            let mut inner_bound = bound.clone();
            inner_bound.insert(v.clone(), resolved_ty.clone());
            EEventAction::Choose(
                v.clone(),
                resolved_ty,
                resolve_expr(ctx, &inner_bound, guard),
                body.iter()
                    .map(|b| resolve_event_action(ctx, &inner_bound, b))
                    .collect(),
            )
        }
        EEventAction::ForAll(v, ty, body) => {
            let resolved_ty = ctx.resolve_ty(ty);
            let mut inner_bound = bound.clone();
            inner_bound.insert(v.clone(), resolved_ty.clone());
            EEventAction::ForAll(
                v.clone(),
                resolved_ty,
                body.iter()
                    .map(|b| resolve_event_action(ctx, &inner_bound, b))
                    .collect(),
            )
        }
        EEventAction::Create(entity, store, fields) => EEventAction::Create(
            entity.clone(),
            store.clone(),
            fields
                .iter()
                .map(|(n, e)| (n.clone(), resolve_expr(ctx, bound, e)))
                .collect(),
        ),
        EEventAction::LetCrossCall(name, sys, ev, args) => EEventAction::LetCrossCall(
            name.clone(),
            sys.clone(),
            ev.clone(),
            args.iter().map(|e| resolve_expr(ctx, bound, e)).collect(),
        ),
        EEventAction::CrossCall(sys, ev, args) => EEventAction::CrossCall(
            sys.clone(),
            ev.clone(),
            args.iter().map(|e| resolve_expr(ctx, bound, e)).collect(),
        ),
        EEventAction::Match(scrutinee, arms) => EEventAction::Match(
            match scrutinee {
                EMatchScrutinee::Var(name) => EMatchScrutinee::Var(name.clone()),
                EMatchScrutinee::CrossCall(sys, ev, args) => EMatchScrutinee::CrossCall(
                    sys.clone(),
                    ev.clone(),
                    args.iter().map(|e| resolve_expr(ctx, bound, e)).collect(),
                ),
            },
            arms.iter()
                .map(|arm| {
                    let mut arm_bound = bound.clone();
                    collect_epattern_vars(&arm.pattern, &mut arm_bound);
                    EMatchArm {
                        pattern: arm.pattern.clone(),
                        guard: arm.guard.as_ref().map(|g| resolve_expr(ctx, &arm_bound, g)),
                        body: arm
                            .body
                            .iter()
                            .map(|item| resolve_event_action(ctx, &arm_bound, item))
                            .collect(),
                    }
                })
                .collect(),
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
        let (resolved_params, bound) = resolve_params_lr(ctx, &pred.params, HashMap::new());
        pred.params = resolved_params;
        pred.body = resolve_expr(ctx, &bound, &pred.body);
    }
}

fn resolve_props(env: &mut Env, ctx: &Ctx) {
    for prop in env.props.values_mut() {
        prop.body = resolve_expr(ctx, &HashMap::new(), &prop.body);
    }
}

fn resolve_verifies(env: &mut Env, ctx: &Ctx) {
    for verify in &mut env.verifies {
        let bound = verify
            .stores
            .iter()
            .map(|store| (store.name.clone(), Ty::Store(store.entity_type.clone())))
            .collect::<HashMap<_, _>>();
        verify.asserts = verify
            .asserts
            .iter()
            .map(|e| resolve_expr(ctx, &bound, e))
            .collect();
    }
}

fn resolve_scenes(env: &mut Env, ctx: &Ctx) {
    for scene in &mut env.scenes {
        // Collect given variables as binders — they scope over when/then sections.
        // Given vars get Ty::Entity so that field accesses (o.status) carry the
        // entity type, enabling downstream checks like match exhaustiveness.
        let mut scene_bound: HashMap<String, Ty> = HashMap::new();
        for store in &scene.stores {
            scene_bound.insert(store.name.clone(), Ty::Store(store.entity_type.clone()));
        }
        for given in &mut scene.givens {
            let resolved_ty = ctx.resolve_ty(&Ty::Named(given.entity_type.clone()));
            scene_bound.insert(given.var.clone(), resolved_ty);
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
                    scene_bound.insert(var.clone(), Ty::Error);
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
            .map(|e| resolve_expr(ctx, &HashMap::new(), e))
            .collect();
        theorem.shows = theorem
            .shows
            .iter()
            .map(|e| resolve_expr(ctx, &HashMap::new(), e))
            .collect();
    }
}

fn resolve_lemmas(env: &mut Env, ctx: &Ctx) {
    for lemma in &mut env.lemmas {
        lemma.body = lemma
            .body
            .iter()
            .map(|e| resolve_expr(ctx, &HashMap::new(), e))
            .collect();
    }
}

/// Resolve a parsed event path to a `(system, event)` reference and a
/// flag indicating whether the event is parameterized (per ).
/// Emits a diagnostic and returns `None` on failure.
fn resolve_event_path(
    path: &crate::ast::EventPath,
    scope: &[String],
    system_events: &HashMap<String, HashMap<String, bool>>,
    let_bindings: &HashMap<String, String>,
    errors: &mut Vec<ElabError>,
    span: crate::span::Span,
) -> Option<(crate::elab::types::EventRef, bool)> {
    use crate::elab::types::EventRef;
    let segments: &[String] = &path.segments;
    match segments.len() {
        2 => {
            let first = &segments[0];
            let event = &segments[1];

            // Try type-level first: is `first` a system name in scope?
            let sys = if scope.iter().any(|s| s == first) {
                first.clone()
            } else if let Some(sys_type) = let_bindings.get(first) {
                // Instance-level: `first` is a let-binding name. Resolve
                // to the bound system type (e.g., `billing` → `Billing`).
                sys_type.clone()
            } else {
                errors.push(
                    ElabError::with_span(
                        ErrorKind::InvalidScope,
                        format!(
                            "{}: `{first}` is not a system name or let-binding instance in this verification site's scope (in scope: {})",
                            crate::messages::UNKNOWN_FAIR_EVENT,
                            if scope.is_empty() {
                                "<none>".to_owned()
                            } else {
                                scope.join(", ")
                            }
                        ),
                        "assumption set",
                        span,
                    )
                    .with_help(crate::messages::HINT_UNKNOWN_FAIR_EVENT),
                );
                return None;
            };

            if let Some(events) = system_events.get(&sys) {
                if let Some(&is_param) = events.get(event) {
                    return Some((EventRef::new(sys, event.clone()), is_param));
                }
            }
            errors.push(
                ElabError::with_span(
                    ErrorKind::UndefinedRef,
                    format!(
                        "{}: `{first}::{event}` is not a declared event in system `{sys}`",
                        crate::messages::UNKNOWN_FAIR_EVENT
                    ),
                    "assumption set",
                    span,
                )
                .with_help(crate::messages::HINT_UNKNOWN_FAIR_EVENT),
            );
            None
        }
        1 => {
            let event = &segments[0];
            // Search across the verification site's scope for any system
            // declaring this event. Each match also carries the
            // parameterized flag from the event's signature.
            let matches: Vec<(String, bool)> = scope
                .iter()
                .filter_map(|sys| {
                    system_events
                        .get(sys.as_str())
                        .and_then(|events| events.get(event))
                        .map(|&is_param| (sys.clone(), is_param))
                })
                .collect();
            match matches.len() {
                0 => {
                    errors.push(
                        ElabError::with_span(
                            ErrorKind::UndefinedRef,
                            format!(
                                "{}: `{event}` is not declared in any system in scope",
                                crate::messages::UNKNOWN_FAIR_EVENT
                            ),
                            "assumption set",
                            span,
                        )
                        .with_help(crate::messages::HINT_UNKNOWN_FAIR_EVENT),
                    );
                    None
                }
                1 => {
                    let (sys, is_param) = matches.into_iter().next().unwrap();
                    Some((EventRef::new(sys, event.clone()), is_param))
                }
                _ => {
                    let names: Vec<String> = matches.iter().map(|(s, _)| s.clone()).collect();
                    errors.push(
                        ElabError::with_span(
                            ErrorKind::AmbiguousRef,
                            format!(
                                "{}: `{event}` matches: {}",
                                crate::messages::AMBIGUOUS_FAIR_EVENT,
                                names.join(", ")
                            ),
                            "assumption set",
                            span,
                        )
                        .with_help(crate::messages::HINT_UNKNOWN_FAIR_EVENT),
                    );
                    None
                }
            }
        }
        _ => {
            errors.push(
                ElabError::with_span(
                    ErrorKind::UndefinedRef,
                    format!(
                        "{}: event path must be `Sys::event` or `event`, got {} segments",
                        crate::messages::UNKNOWN_FAIR_EVENT,
                        segments.len()
                    ),
                    "assumption set",
                    span,
                )
                .with_help(crate::messages::HINT_UNKNOWN_FAIR_EVENT),
            );
            None
        }
    }
}

fn resolve_axioms(env: &mut Env, ctx: &Ctx) {
    for axiom in &mut env.axioms {
        axiom.body = resolve_expr(ctx, &HashMap::new(), &axiom.body);
    }
}

fn resolve_consts(env: &mut Env, ctx: &Ctx) {
    for c in env.consts.values_mut() {
        c.body = resolve_expr(ctx, &HashMap::new(), &c.body);
    }
}

/// Resolve parameters left-to-right with refinement predicate binding.
/// Each param's refinement predicate can reference params declared to its left.
/// `$` and the param name are both bound to the base type inside predicates.
/// Returns (`resolved_params`, `bound_map`).
/// Unwrap `Ty::Alias` wrappers to get to the underlying type.
fn unwrap_alias_ty(ty: &Ty) -> &Ty {
    let mut current = ty;
    while let Ty::Alias(_, inner) | Ty::Newtype(_, inner) = current {
        current = inner;
    }
    current
}

fn resolve_params_lr(
    ctx: &Ctx,
    params: &[(String, Ty)],
    initial_bound: HashMap<String, Ty>,
) -> (Vec<(String, Ty)>, HashMap<String, Ty>) {
    let mut bound = initial_bound;
    let mut resolved_params = Vec::new();
    for (name, ty) in params {
        let resolved_ty = ctx.resolve_ty(ty);
        // Unwrap Alias wrappers so alias-based refinements like `x: Positive`
        // (where `type Positive = int { $ > 0 }`) are resolved correctly.
        let final_ty = match unwrap_alias_ty(&resolved_ty) {
            Ty::Refinement(base, pred) => {
                let mut pred_bound = bound.clone();
                pred_bound.insert("$".to_owned(), (**base).clone());
                pred_bound.insert(name.clone(), (**base).clone());
                let resolved_pred = resolve_expr(ctx, &pred_bound, pred);
                Ty::Refinement(base.clone(), Box::new(resolved_pred))
            }
            _ => resolved_ty.clone(),
        };
        let base_ty = match unwrap_alias_ty(&final_ty) {
            Ty::Refinement(base, _) => (**base).clone(),
            t => t.clone(),
        };
        bound.insert(name.clone(), base_ty);
        resolved_params.push((name.clone(), final_ty));
    }
    (resolved_params, bound)
}

fn resolve_fns(env: &mut Env, ctx: &Ctx) {
    for f in env.fns.values_mut() {
        let (resolved_params, bound) = resolve_params_lr(ctx, &f.params, HashMap::new());
        f.params = resolved_params;
        f.ret_ty = ctx.resolve_ty(&f.ret_ty);
        let mut bound_with_result = bound.clone();
        bound_with_result.insert("result".to_owned(), f.ret_ty.clone());
        f.contracts = f
            .contracts
            .iter()
            .map(|c| resolve_contract(ctx, &bound, &bound_with_result, c))
            .collect();
        f.body = resolve_expr(ctx, &bound, &f.body);
    }
}

fn resolve_contract(
    ctx: &Ctx,
    bound: &HashMap<String, Ty>,
    bound_with_result: &HashMap<String, Ty>,
    c: &EContract,
) -> EContract {
    match c {
        EContract::Requires(e) => EContract::Requires(resolve_expr(ctx, bound, e)),
        EContract::Ensures(e) => {
            // 'result' is already in bound_with_result with the correct return type,
            // so resolve_expr will pick it up via the bound map.
            EContract::Ensures(resolve_expr(ctx, bound_with_result, e))
        }
        EContract::Decreases { measures, star } => EContract::Decreases {
            measures: measures
                .iter()
                .map(|e| resolve_expr(ctx, bound, e))
                .collect(),
            star: *star,
        },
        EContract::Invariant(e) => EContract::Invariant(resolve_expr(ctx, bound, e)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Visibility;
    use crate::elab::collect;
    use crate::elab::types::{EExpr, EFieldDefault};
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

    fn elaborate_all(
        src: &str,
    ) -> (
        crate::elab::types::ElabResult,
        Vec<crate::elab::error::ElabError>,
    ) {
        let tokens = lex::lex(src).expect("lex error");
        let mut parser = Parser::new(tokens);
        let prog = parser.parse_program().expect("parse error");
        crate::elab::elaborate(&prog)
    }

    fn relation_columns(ty: &Ty) -> &[Ty] {
        let Ty::Relation(columns) = ty else {
            panic!("expected Relation result type, got {ty:?}");
        };
        columns
    }

    #[test]
    fn store_param_bounds_validate_bound_store_scopes() {
        let (_result, errors) = elaborate_all(
            "entity Order { status: int = 0 }\n\
             system Shop(orders: Store<Order>[1..2]) {}\n\
             verify too_many_orders {\n\
               assume {\n\
                 store orders: Order[3]\n\
                 let shop = Shop { orders: orders }\n\
               }\n\
               assert true\n\
             }",
        );

        assert!(
            errors.iter().any(|err| err.message.contains(
                "binds store `orders` with upper bound 3 to `Shop::orders`, which allows at most 2"
            )),
            "expected store parameter bound error, got: {errors:?}"
        );
    }

    #[test]
    fn store_param_min_bounds_reject_loose_store_scope() {
        let (_result, errors) = elaborate_all(
            "entity Order { status: int = 0 }\n\
             system Shop(orders: Store<Order>[1..4]) {}\n\
             verify maybe_empty_orders {\n\
               assume {\n\
                 store orders: Order[0..4]\n\
                 let shop = Shop { orders: orders }\n\
               }\n\
               assert true\n\
             }",
        );

        assert!(
            errors.iter().any(|err| err.message.contains(
                "binds store `orders` with lower bound 0 to `Shop::orders`, which requires at least 1 active entity slot"
            )),
            "expected store parameter lower-bound error, got: {errors:?}"
        );
    }

    #[test]
    fn store_param_exact_bounds_reject_loose_store_scope() {
        let (_result, errors) = elaborate_all(
            "entity Order { status: int = 0 }\n\
             system Shop(orders: Store<Order>[2]) {}\n\
             verify maybe_two_orders {\n\
               assume {\n\
                 store orders: Order[0..2]\n\
                 let shop = Shop { orders: orders }\n\
               }\n\
               assert true\n\
             }",
        );

        assert!(
            errors.iter().any(|err| err.message.contains(
                "binds store `orders` with lower bound 0 to `Shop::orders`, which requires at least 2 active entity slot"
            )),
            "expected exact store parameter lower-bound error, got: {errors:?}"
        );
    }

    #[test]
    fn store_param_exact_bounds_accept_matching_store_scope() {
        let (_result, errors) = elaborate_all(
            "entity Order { status: int = 0 }\n\
             system Shop(orders: Store<Order>[2]) {}\n\
             verify exact_orders {\n\
               assume {\n\
                 store orders: Order[2]\n\
                 let shop = Shop { orders: orders }\n\
               }\n\
               assert true\n\
             }",
        );

        assert!(errors.is_empty(), "expected no errors, got: {errors:?}");
    }

    #[test]
    fn program_store_params_must_satisfy_child_system_contracts() {
        let (_result, errors) = elaborate_all(
            "entity Order { status: int = 0 }\n\
             system Shop(orders: Store<Order>[2]) {}\n\
             program Demo(orders: Store<Order>[0..2]) {\n\
               let shop = Shop { orders: orders }\n\
             }",
        );

        assert!(
            errors.iter().any(|err| err.message.contains(
                "program/system `Demo` binds store parameter `orders` with lower bound 0 to `Shop::orders`, which requires at least 2 active entity slot"
            )),
            "expected program store parameter lower-bound error, got: {errors:?}"
        );
    }

    #[test]
    fn program_store_params_accept_matching_child_system_contracts() {
        let (_result, errors) = elaborate_all(
            "entity Order { status: int = 0 }\n\
             system Shop(orders: Store<Order>[2]) {}\n\
             program Demo(orders: Store<Order>[2]) {\n\
               let shop = Shop { orders: orders }\n\
             }",
        );

        assert!(errors.is_empty(), "expected no errors, got: {errors:?}");
    }

    #[test]
    fn cross_module_imports_are_allowed_without_visibility_gate() {
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
            crate::span::Span { start: 0, end: 0 },
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
            !env.errors
                .iter()
                .any(|e| e.message.contains("cannot import private")),
            "cross-module imports should not require explicit visibility, got: {:?}",
            env.errors
        );
    }

    #[test]
    fn import_no_error() {
        let env = elaborate_src("module TestMod\nenum Status = Active\nuse TestMod::Status");
        assert!(
            !env.errors
                .iter()
                .any(|e| e.message.contains("cannot import private")),
            "imports should not produce privacy errors, got: {:?}",
            env.errors
        );
    }

    #[test]
    fn unknown_named_type_becomes_poison_type_after_resolution() {
        let env = elaborate_src("entity User { status: MissingType }");
        assert!(
            env.errors
                .iter()
                .any(|e| e.message.contains("unknown type `MissingType`")),
            "expected unknown type diagnostic, got: {:?}",
            env.errors
        );
        let user = env.entities.get("User").expect("entity collected");
        assert!(
            matches!(user.fields[0].ty, Ty::Error),
            "unknown named types should be rewritten to poison, got: {:?}",
            user.fields[0].ty
        );
    }

    #[test]
    fn extern_command_return_type_and_may_returns_are_resolved() {
        let env = elaborate_src(
            "enum AuthorizationResult = Authorized | Denied\n\
             extern InsuranceGateway {\n\
               command authorize(patient_id: identity) -> AuthorizationResult\n\
               may authorize {\n\
                 return @Authorized\n\
                 return @Denied\n\
               }\n\
             }",
        );

        assert!(
            env.errors.is_empty(),
            "extern result fixture should resolve without errors: {:?}",
            env.errors
        );
        let gateway = env
            .externs
            .get("InsuranceGateway")
            .expect("extern collected");
        let command = gateway
            .commands
            .iter()
            .find(|command| command.name == "authorize")
            .expect("extern command collected");
        assert!(
            matches!(
                command.return_type,
                Some(Ty::Enum(ref name, _)) if name == "AuthorizationResult"
            ),
            "extern command result type should resolve to enum, got {:?}",
            command.return_type
        );
        let may = gateway.mays.first().expect("may block collected");
        assert!(may.returns.iter().all(|ret| matches!(
            ret,
            EExpr::Var(Ty::Enum(name, _), _, _) if name == "AuthorizationResult"
        )));
    }

    #[test]
    fn int_literal_field_default_is_coerced_to_real() {
        let (result, errors) = elaborate_all("entity Order { total: real = 0 }");
        assert!(
            errors.is_empty(),
            "real field defaults should accept int literals, got: {:?}",
            errors
        );

        let order = result
            .entities
            .iter()
            .find(|entity| entity.name == "Order")
            .expect("entity collected");
        let field = order
            .fields
            .iter()
            .find(|field| field.name == "total")
            .expect("total field present");
        match field.default.as_ref() {
            Some(EFieldDefault::Value(EExpr::Lit(
                Ty::Builtin(BuiltinTy::Real),
                Literal::Real(value),
                _,
            ))) => {
                assert_eq!(*value, 0.0);
            }
            other => panic!("expected real literal default after coercion, got {other:?}"),
        }
    }

    #[test]
    fn int_variable_field_default_still_errors_for_real() {
        let (_result, errors) = elaborate_all(
            "enum Outcome = Ok { value: real }\n\
             system Bank {\n\
               command open_account(initial_balance: int) -> Outcome {\n\
                 return @Ok { value: initial_balance }\n\
               }\n\
             }",
        );
        assert!(
            errors
                .iter()
                .any(|e| e.message.contains("field `value` of type `int`")
                    && e.message.contains("expects `real`")),
            "int variables should not be coerced to real return payloads, got: {:?}",
            errors
        );
    }

    #[test]
    fn end_to_end_cross_module_import_materializes() {
        // Full pipeline: two modules, one imports a type from the other.
        // After elaborate_env, the imported type should be usable in the
        // working namespace (bare-name types map).
        use crate::elab;
        use crate::elab::env::Env;

        let mut env = Env::new();

        // File 1: module Provider declares enum Status = Active | Inactive
        env.module_name = None;
        let tokens1 = lex::lex("module Provider\nenum Status = Active | Inactive").unwrap();
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
            "cross-module import should succeed, got: {import_errors:?}"
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
    fn end_to_end_use_all_imports_module_names() {
        use crate::elab;
        use crate::elab::env::Env;

        let mut env = Env::new();

        // File 1: module Lib with two ordinary declarations
        env.module_name = None;
        let tokens1 = lex::lex("module Lib\nenum Color = Red | Blue\nenum Secret = X | Y").unwrap();
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
            "use Lib::* should succeed: {import_errors:?}"
        );

        // Color should be imported
        let has_color = result.types.iter().any(|t| t.name == "Color");
        assert!(has_color, "Color should be imported via use Lib::*");

        // Secret should also be imported
        let has_secret = result.types.iter().any(|t| t.name == "Secret");
        assert!(has_secret, "Secret should be imported via use Lib::*");
    }

    #[test]
    fn end_to_end_cross_module_fn_import() {
        use crate::elab;
        use crate::elab::env::Env;

        let mut env = Env::new();

        // File 1: module MathLib with fn double
        env.module_name = None;
        let tokens1 = lex::lex("module MathLib\nfn double(x: int): int = x").unwrap();
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
            "fn import should succeed: {import_errors:?}"
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
        let source = &env.use_decls[0].source_module;
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

        // File 1: module Provider declares type Order
        env.module_name = None;
        let tokens1 = lex::lex("module Provider\nenum Order = Pending | Done").unwrap();
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
            "alias import should succeed: {import_errors:?}"
        );

        // The type's canonical name should be "Order" (from Ty::Enum("Order",...)),
        // NOT "O" (the alias). Aliases affect lookup scope, not declaration identity.
        let type_names: Vec<&str> = result.types.iter().map(|t| t.name.as_str()).collect();
        assert!(
            type_names.contains(&"Order"),
            "aliased type should keep canonical name 'Order' in result: {type_names:?}"
        );
        assert!(
            !type_names.contains(&"O"),
            "alias 'O' should NOT appear as canonical name in result: {type_names:?}"
        );
    }

    #[test]
    fn alias_rewriting_in_expressions() {
        // Verify that aliased variable references are rewritten to canonical
        // names during resolve, so lowering can find the right definitions.
        use crate::elab;
        use crate::elab::env::Env;

        let mut env = Env::new();

        // File 1: module MathLib with fn double
        env.module_name = None;
        let tokens1 = lex::lex("module MathLib\nfn double(x: int): int = x").unwrap();
        let mut p1 = Parser::new(tokens1);
        let prog1 = p1.parse_program().unwrap();
        collect::collect_into(&mut env, &prog1);
        env.module_name = None;

        // File 2: module App imports double as dbl, uses it in a const
        let tokens2 =
            lex::lex("module App\nuse MathLib::double as dbl\nconst val = dbl(5)").unwrap();
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
            "alias import should succeed: {import_errors:?}"
        );

        // The const's body should reference "double" (canonical), not "dbl" (alias).
        let val_const = result.consts.iter().find(|c| c.name == "val");
        assert!(val_const.is_some(), "const val should exist in result");
        let body = &val_const.unwrap().body;
        // The body is Call(Var("double"), [Int(5)]) — "double" not "dbl"
        if let EExpr::Call(_, func, _, _) = body {
            if let EExpr::Var(_, name, _) = func.as_ref() {
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

        // File 1: module Lib with fn foo
        env.module_name = None;
        let tokens1 = lex::lex("module Lib\nfn foo(x: int): int = x").unwrap();
        let mut p1 = Parser::new(tokens1);
        let prog1 = p1.parse_program().unwrap();
        collect::collect_into(&mut env, &prog1);
        env.module_name = None;

        // File 2: module App imports foo as f, then uses let f = 42 in f
        // The inner `f` should resolve to the local binding, not be rewritten to `foo`.
        let tokens2 =
            lex::lex("module App\nuse Lib::foo as f\nconst val = let f = 42 in f").unwrap();
        let mut p2 = Parser::new(tokens2);
        let prog2 = p2.parse_program().unwrap();
        collect::collect_into(&mut env, &prog2);

        let (result, _errors) = elab::elaborate_env(env);

        let val_const = result.consts.iter().find(|c| c.name == "val").unwrap();
        // The body is Let([(f, _, 42)], Var(f))
        // The inner Var should be "f" (bound), NOT "foo" (alias rewrite)
        if let EExpr::Let(_, body, _) = &val_const.body {
            if let EExpr::Var(_, name, _) = body.as_ref() {
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

        // File 1: module Lib, enum Color
        env.module_name = None;
        let tokens1 = lex::lex("module Lib\nenum Color = Red | Blue").unwrap();
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
        let tokens3 = lex::lex("module App\nenum Shape = Circle | Square").unwrap();
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
            "Other's import of Color should NOT leak into App's namespace: {type_names:?}"
        );
    }

    #[test]
    fn fn_param_not_alias_rewritten() {
        // fn double(x: int): int = x
        // If "x" is aliased to something, the param binding should prevent rewriting.
        use crate::elab;
        use crate::elab::env::Env;

        let mut env = Env::new();

        // File 1: module Lib with fn x (a function named "x")
        env.module_name = None;
        let tokens1 = lex::lex("module Lib\nfn x(n: int): int = n").unwrap();
        let mut p1 = Parser::new(tokens1);
        let prog1 = p1.parse_program().unwrap();
        collect::collect_into(&mut env, &prog1);
        env.module_name = None;

        // File 2: module App imports x from Lib, defines fn double(x: int) = x
        // The param "x" shadows the imported alias — should NOT be rewritten.
        let tokens2 = lex::lex("module App\nuse Lib::x\nfn double(x: int): int = x").unwrap();
        let mut p2 = Parser::new(tokens2);
        let prog2 = p2.parse_program().unwrap();
        collect::collect_into(&mut env, &prog2);

        let (result, _errors) = elab::elaborate_env(env);

        let double_fn = result.fns.iter().find(|f| f.name == "double").unwrap();
        // Body should be Var("x") — the param, not rewritten to anything else
        if let EExpr::Var(_, name, _) = &double_fn.body {
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
        let tokens1 = lex::lex("module Lib\nfn o(n: int): int = n").unwrap();
        let mut p1 = Parser::new(tokens1);
        let prog1 = p1.parse_program().unwrap();
        collect::collect_into(&mut env, &prog1);
        env.module_name = None;

        // App imports o from Lib, then defines pred check(o: Order) =...
        // "o" as pred param should not be rewritten.
        let tokens2 = lex::lex(
            "module App\nuse Lib::o\nenum Order = Pending\npred check(o: Order) = o == Pending",
        )
        .unwrap();
        let mut p2 = Parser::new(tokens2);
        let prog2 = p2.parse_program().unwrap();
        collect::collect_into(&mut env, &prog2);

        let (result, _errors) = elab::elaborate_env(env);

        let check_pred = result.preds.iter().find(|p| p.name == "check").unwrap();
        // Body is BinOp(OpEq, Var("o"), Var("Pending"))
        // Assert the left side is specifically Var with name "o"
        match &check_pred.body {
            EExpr::BinOp(_, _, lhs, _, _) => match lhs.as_ref() {
                EExpr::Var(_, name, _) => {
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
             enum Status = Active\n\
             entity Order { id: identity }\n\
             system S {\n\
               command noop() { }\n\
             }\n\
             scene test_scene {\n\
               given {\n\
                 store orders: Order[0..2]\n\
                 let s = S { }\n\
                 let o = one Order in orders\n\
               }\n\
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
        // axiom body containing `all b: Bed |...` should resolve
        // the domain Bed to Entity("Bed"), not leave it as Unresolved.
        let env = elaborate_src(
            "module Test\n\
             entity Bed { id: identity\n ward: int }\n\
             axiom bed_positive = all b: Bed | b.ward >= 0",
        );
        // Check the axiom body's quantifier domain type
        assert_eq!(env.axioms.len(), 1);
        let axiom = &env.axioms[0];
        match &axiom.body {
            EExpr::Quant(_, _, _, domain_ty, _, _) => {
                assert!(
                    matches!(domain_ty, Ty::Entity(n) if n == "Bed"),
                    "axiom quantifier domain should be Entity(\"Bed\"), got {domain_ty:?}"
                );
            }
            other => panic!("expected Quant in axiom body, got {other:?}"),
        }
    }

    #[test]
    fn relation_join_qualified_builtin_infers_tuple_set_type() {
        let env = elaborate_src(r#"const joined = Rel::join(Set((1, true)), Set((true, "ok")))"#);

        let body = &env.consts.get("joined").expect("joined const").body;
        let EExpr::QualCall(ty, namespace, name, _, _) = body else {
            panic!("expected relation builtin QualCall, got {body:?}");
        };
        assert_eq!(namespace, "Rel");
        assert_eq!(name, "join");
        assert!(matches!(
            relation_columns(ty),
            [
                Ty::Builtin(crate::elab::types::BuiltinTy::Int),
                Ty::Builtin(crate::elab::types::BuiltinTy::String),
            ]
        ));
    }

    #[test]
    fn relation_bare_join_is_not_a_builtin() {
        let (_result, errors) =
            elaborate_all(r#"const joined = join(Set((1, true)), Set((true, "ok")))"#);

        assert!(
            errors.iter().any(|error| error
                .message
                .contains("relation operation `join` must be called as `Rel::join`")),
            "bare relation function names should produce a qualified-call diagnostic: {errors:?}"
        );
    }

    #[test]
    fn relation_type_alias_resolves_to_first_class_relation() {
        let env = elaborate_src("type Edge = Rel<int, string>");

        let edge = env.types.get("Edge").expect("Edge alias");
        let Ty::Alias(_, inner) = edge else {
            panic!("expected type alias, got {edge:?}");
        };
        let Ty::Relation(columns) = inner.as_ref() else {
            panic!("expected Relation columns, got {inner:?}");
        };
        assert!(matches!(
            columns.as_slice(),
            [
                Ty::Builtin(crate::elab::types::BuiltinTy::Int),
                Ty::Builtin(crate::elab::types::BuiltinTy::String),
            ]
        ));
    }

    #[test]
    fn set_comprehension_infers_binder_type_from_set_source() {
        let env = elaborate_src("const doubled = { x * 2 | x in Set(1, 2, 3) where x > 0 }");

        let body = &env.consts.get("doubled").expect("doubled const").body;
        let EExpr::SetComp(ty, projection, var, domain, source, _, _) = body else {
            panic!("expected sourced set comprehension, got {body:?}");
        };
        assert_eq!(var, "x");
        assert!(source.is_some());
        assert!(matches!(
            domain,
            Ty::Builtin(crate::elab::types::BuiltinTy::Int)
        ));
        assert!(matches!(
            projection.as_deref().map(EExpr::ty),
            Some(Ty::Builtin(crate::elab::types::BuiltinTy::Int))
        ));
        assert!(matches!(
            ty,
            Ty::Set(inner) if matches!(inner.as_ref(), Ty::Builtin(crate::elab::types::BuiltinTy::Int))
        ));
    }

    #[test]
    fn set_comprehension_infers_binder_type_from_seq_source() {
        let env = elaborate_src("const positive = { x | x in Seq(1.0, 2.0) where x > 0.0 }");

        let body = &env.consts.get("positive").expect("positive const").body;
        let EExpr::SetComp(ty, projection, var, domain, source, _, _) = body else {
            panic!("expected sourced set comprehension, got {body:?}");
        };
        assert_eq!(var, "x");
        assert!(source.is_some());
        assert!(matches!(
            domain,
            Ty::Builtin(crate::elab::types::BuiltinTy::Real)
        ));
        assert!(matches!(
            projection.as_deref().map(EExpr::ty),
            Some(Ty::Builtin(crate::elab::types::BuiltinTy::Real))
        ));
        assert!(matches!(
            ty,
            Ty::Set(inner) if matches!(inner.as_ref(), Ty::Builtin(crate::elab::types::BuiltinTy::Real))
        ));
    }

    #[test]
    fn set_comprehension_over_real_domain_requires_finite_source() {
        let (_result, errors) =
            elaborate_all("const bad = { x | x: real where x >= 0.0 and x <= 1.0 }");

        assert!(
            errors.iter().any(|error| {
                error.message.contains("set comprehension")
                    && error.message.contains("real")
                    && error.message.contains("finite source")
                    && error
                        .help
                        .as_deref()
                        .is_some_and(|help| help.contains("Set(") && help.contains("real intervals"))
            }),
            "real set comprehensions should explain that real intervals are not enumerable: {errors:?}"
        );
    }

    #[test]
    fn set_comprehension_over_finite_real_source_is_allowed() {
        let env = elaborate_src("const good = { x | x in Set(0.0, 0.5, 1.0) where x >= 0.5 }");

        assert!(
            env.errors.is_empty(),
            "finite real source should not produce elaboration errors: {:?}",
            env.errors
        );
        let body = &env.consts.get("good").expect("good const").body;
        let EExpr::SetComp(ty, _, _, domain, source, _, _) = body else {
            panic!("expected sourced set comprehension, got {body:?}");
        };
        assert!(source.is_some());
        assert!(matches!(
            domain,
            Ty::Builtin(crate::elab::types::BuiltinTy::Real)
        ));
        assert!(matches!(
            ty,
            Ty::Set(inner) if matches!(inner.as_ref(), Ty::Builtin(crate::elab::types::BuiltinTy::Real))
        ));
    }

    #[test]
    fn relation_tuple_type_alias_resolves_to_nary_relation() {
        let env = elaborate_src("type EdgeFact = Rel<(int, string, bool)>");

        let edge = env.types.get("EdgeFact").expect("EdgeFact alias");
        let Ty::Alias(_, inner) = edge else {
            panic!("expected type alias, got {edge:?}");
        };
        let Ty::Relation(columns) = inner.as_ref() else {
            panic!("expected Relation columns, got {inner:?}");
        };
        assert_eq!(columns.len(), 3);
    }

    #[test]
    fn relation_literal_infers_first_class_relation_type() {
        let env = elaborate_src(r#"const edges = Rel((1, "ok"))"#);

        let body = &env.consts.get("edges").expect("edges const").body;
        let Ty::Relation(columns) = body.ty() else {
            panic!("expected Relation literal type, got {body:?}");
        };
        assert!(matches!(
            columns.as_slice(),
            [
                Ty::Builtin(crate::elab::types::BuiltinTy::Int),
                Ty::Builtin(crate::elab::types::BuiltinTy::String),
            ]
        ));
    }

    #[test]
    fn relation_field_infers_store_backed_field_relation_type() {
        let env = elaborate_src(
            "enum Status = Pending | Paid\n\
             entity Order { status: Status = @Pending }\n\
             verify status_relation {\n\
               assume { store orders: Order[0..2] }\n\
               assert Rel::field(orders, Order::status) == Rel::field(orders, Order::status)\n\
             }",
        );

        assert!(
            env.errors.is_empty(),
            "expected no errors, got {:?}",
            env.errors
        );
        let assert = &env.verifies[0].asserts[0];
        let EExpr::BinOp(_, _, left, _, _) = assert else {
            panic!("expected equality assertion, got {assert:?}");
        };
        let EExpr::QualCall(ty, namespace, name, _, _) = left.as_ref() else {
            panic!("expected Rel::field call, got {left:?}");
        };
        assert_eq!(namespace, "Rel");
        assert_eq!(name, "field");
        let Ty::Relation(columns) = ty else {
            panic!("expected Relation result type, got {ty:?}");
        };
        assert!(
            matches!(columns.as_slice(), [Ty::Entity(entity), Ty::Enum(status, _)] if entity == "Order" && status == "Status")
        );
    }

    #[test]
    fn relation_field_rejects_store_entity_mismatch() {
        let (_result, errors) = elaborate_all(
            "enum Status = Pending | Paid\n\
             entity Order { status: Status = @Pending }\n\
             entity Customer { status: Status = @Pending }\n\
             verify status_relation {\n\
               assume { store customers: Customer[0..2] }\n\
               assert Rel::field(customers, Order::status) == Rel::field(customers, Order::status)\n\
             }",
        );

        assert!(
            errors.iter().any(|error| error
                .message
                .contains("Rel::field store entity `Customer` does not match field owner `Order`")),
            "expected store/entity mismatch diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn relation_pipe_supports_qualified_associated_call() {
        let env = elaborate_src(r#"const joined = Set((1, true)) |> Rel::join(Set((true, "ok")))"#);

        let body = &env.consts.get("joined").expect("joined const").body;
        let EExpr::QualCall(ty, namespace, name, args, _) = body else {
            panic!("expected relation builtin QualCall, got {body:?}");
        };
        assert_eq!(namespace, "Rel");
        assert_eq!(name, "join");
        assert_eq!(args.len(), 2);
        assert!(matches!(
            relation_columns(ty),
            [
                Ty::Builtin(crate::elab::types::BuiltinTy::Int),
                Ty::Builtin(crate::elab::types::BuiltinTy::String),
            ]
        ));
    }

    #[test]
    fn relation_namespace_transpose_infers_swapped_tuple_set_type() {
        let env = elaborate_src(r#"const flipped = Rel::transpose(Set((1, "ok")))"#);

        let body = &env.consts.get("flipped").expect("flipped const").body;
        let EExpr::QualCall(ty, namespace, name, _, _) = body else {
            panic!("expected relation builtin QualCall, got {body:?}");
        };
        assert_eq!(namespace, "Rel");
        assert_eq!(name, "transpose");
        assert!(matches!(
            relation_columns(ty),
            [
                Ty::Builtin(crate::elab::types::BuiltinTy::String),
                Ty::Builtin(crate::elab::types::BuiltinTy::Int),
            ]
        ));
    }

    #[test]
    fn relation_closure_reports_non_homogeneous_binary_relation() {
        let (_result, errors) = elaborate_all(r#"const bad = Rel::closure(Set((1, "ok")))"#);

        assert!(
            errors.iter().any(|error| error
                .message
                .contains("Rel::closure requires a homogeneous binary relation")),
            "expected closure relation diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn relation_product_builds_tuple_relation_from_unary_relations() {
        let env = elaborate_src(r#"const pairs = Rel::product(Set(1), Set("ok"))"#);

        let body = &env.consts.get("pairs").expect("pairs const").body;
        let EExpr::QualCall(ty, namespace, name, _, _) = body else {
            panic!("expected relation builtin QualCall, got {body:?}");
        };
        assert_eq!(namespace, "Rel");
        assert_eq!(name, "product");
        assert!(matches!(
            relation_columns(ty),
            [
                Ty::Builtin(crate::elab::types::BuiltinTy::Int),
                Ty::Builtin(crate::elab::types::BuiltinTy::String),
            ]
        ));
    }

    #[test]
    fn relation_project_keeps_selected_tuple_columns() {
        let env = elaborate_src(r#"const projected = Rel::project(Set((1, true, "ok")), 0, 2)"#);

        let body = &env.consts.get("projected").expect("projected const").body;
        let EExpr::QualCall(ty, namespace, name, _, _) = body else {
            panic!("expected relation builtin QualCall, got {body:?}");
        };
        assert_eq!(namespace, "Rel");
        assert_eq!(name, "project");
        assert!(matches!(
            relation_columns(ty),
            [
                Ty::Builtin(crate::elab::types::BuiltinTy::Int),
                Ty::Builtin(crate::elab::types::BuiltinTy::String),
            ]
        ));
    }

    #[test]
    fn relation_project_requires_qualified_associated_call() {
        let (_result, errors) =
            elaborate_all(r#"const projected = project(Set((1, true, "ok")), 2)"#);

        assert!(
            errors.iter().any(|error| error
                .message
                .contains("relation operation `project` must be called as `Rel::project`")),
            "bare relation function names should produce a qualified-call diagnostic: {errors:?}"
        );
    }

    #[test]
    fn relation_cardinality_infers_int() {
        let env = elaborate_src(r#"const relation_size = #Set((1, true))"#);

        let body = &env
            .consts
            .get("relation_size")
            .expect("relation_size const")
            .body;
        assert!(matches!(
            body.ty(),
            Ty::Builtin(crate::elab::types::BuiltinTy::Int)
        ));
    }
}
