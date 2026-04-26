//! generic enum monomorphization.

use super::super::env::Env;
use super::super::error::{ElabError, ErrorKind};
use super::super::types::{EnumVariantFields, GenericTypeDef, Ty, VariantFieldsMap};
use std::collections::{HashMap, HashSet};

/// Build the display name for a monomorphized generic type.
/// E.g. `format_mono_name("Option", [Int])` → `"Option<Int>"`.
pub(super) fn format_mono_name(name: &str, args: &[Ty]) -> String {
    let arg_strs: Vec<String> = args.iter().map(mono_ty_name).collect();
    format!("{}<{}>", name, arg_strs.join(", "))
}

/// Display name for a type in monomorphized name context.
pub(super) fn mono_ty_name(ty: &Ty) -> String {
    match ty {
        Ty::Enum(n, _) | Ty::Record(n, _) | Ty::Entity(n) => n.clone(),
        Ty::Builtin(b) => b.name().to_string(),
        Ty::Alias(_, inner) => mono_ty_name(inner),
        Ty::Param(n, args) => format_mono_name(n, args),
        Ty::Set(a) => format!("Set<{}>", mono_ty_name(a)),
        Ty::Seq(a) => format!("Seq<{}>", mono_ty_name(a)),
        Ty::Map(k, v) => format!("Map<{}, {}>", mono_ty_name(k), mono_ty_name(v)),
        Ty::Named(n) => n.clone(),
        Ty::Error => "?".to_string(),
        _ => "?".to_string(),
    }
}

/// Apply type-parameter substitution to a type.
pub(super) fn substitute_ty(ty: &Ty, subst: &HashMap<String, Ty>) -> Ty {
    match ty {
        Ty::Named(n) => {
            if let Some(replacement) = subst.get(n.as_str()) {
                replacement.clone()
            } else {
                ty.clone()
            }
        }
        Ty::Param(n, args) => {
            let resolved_args: Vec<Ty> = args.iter().map(|a| substitute_ty(a, subst)).collect();
            Ty::Param(n.clone(), resolved_args)
        }
        Ty::Record(n, fs) => Ty::Record(
            n.clone(),
            fs.iter()
                .map(|(fn_, ft)| (fn_.clone(), substitute_ty(ft, subst)))
                .collect(),
        ),
        Ty::Set(a) => Ty::Set(Box::new(substitute_ty(a, subst))),
        Ty::Seq(a) => Ty::Seq(Box::new(substitute_ty(a, subst))),
        Ty::Map(k, v) => Ty::Map(
            Box::new(substitute_ty(k, subst)),
            Box::new(substitute_ty(v, subst)),
        ),
        Ty::Tuple(ts) => Ty::Tuple(ts.iter().map(|t| substitute_ty(t, subst)).collect()),
        Ty::Fn(a, b) => Ty::Fn(
            Box::new(substitute_ty(a, subst)),
            Box::new(substitute_ty(b, subst)),
        ),
        Ty::Alias(n, t) => Ty::Alias(n.clone(), Box::new(substitute_ty(t, subst))),
        Ty::Refinement(base, pred) => {
            Ty::Refinement(Box::new(substitute_ty(base, subst)), pred.clone())
        }
        _ => ty.clone(),
    }
}

/// Create a monomorphized Ty::Enum from a generic definition and concrete args.
pub(super) fn monomorphize_inline(gdef: &GenericTypeDef, args: &[Ty]) -> Ty {
    let mono_name = format_mono_name(&gdef.name, args);
    Ty::Enum(mono_name, gdef.variant_names.clone())
}

/// Build monomorphized variant_fields for a generic type instantiation.
/// After substituting type params, recursively resolves any nested `Ty::Param`
/// referencing other generic types (e.g., `enum Box<T> = Wrap(Option<T>)`
/// instantiated as `Box<Int>` → the `Option<T>` payload becomes `Option<Int>`).
pub(super) fn monomorphize_variant_fields(
    gdef: &GenericTypeDef,
    args: &[Ty],
    generic_types: &HashMap<String, GenericTypeDef>,
    types: &mut HashMap<String, Ty>,
    variant_fields: &mut VariantFieldsMap,
    registered: &mut HashSet<String>,
) -> EnumVariantFields {
    let subst: HashMap<String, Ty> = gdef
        .type_params
        .iter()
        .zip(args.iter())
        .map(|(p, a)| (p.clone(), a.clone()))
        .collect();
    gdef.variant_fields
        .iter()
        .map(|(vname, fields)| {
            let resolved = fields
                .iter()
                .map(|(fname, fty)| {
                    let substituted = substitute_ty(fty, &subst);
                    // Recursively resolve nested generic applications
                    let final_ty = resolve_nested_generics(
                        &substituted,
                        generic_types,
                        types,
                        variant_fields,
                        registered,
                    );
                    (fname.clone(), final_ty)
                })
                .collect();
            (vname.clone(), resolved)
        })
        .collect()
}

/// Recursively resolve `Ty::Param` references to generic types within a type,
/// monomorphizing and registering them as needed. This handles nested generics
/// like `Option<T>` appearing inside another generic's variant payload.
pub(super) fn resolve_nested_generics(
    ty: &Ty,
    generic_types: &HashMap<String, GenericTypeDef>,
    types: &mut HashMap<String, Ty>,
    variant_fields: &mut VariantFieldsMap,
    registered: &mut HashSet<String>,
) -> Ty {
    match ty {
        Ty::Param(n, args) => {
            // First resolve args recursively
            let resolved_args: Vec<Ty> = args
                .iter()
                .map(|a| {
                    resolve_nested_generics(a, generic_types, types, variant_fields, registered)
                })
                .collect();
            if let Some(gdef) = generic_types.get(n.as_str()) {
                if resolved_args.len() == gdef.type_params.len() {
                    let mono_name = format_mono_name(n, &resolved_args);
                    // Register if not already done
                    if !registered.contains(&mono_name) && !types.contains_key(&mono_name) {
                        registered.insert(mono_name.clone());
                        let mono_fields = monomorphize_variant_fields(
                            gdef,
                            &resolved_args,
                            generic_types,
                            types,
                            variant_fields,
                            registered,
                        );
                        let enum_ty = Ty::Enum(mono_name.clone(), gdef.variant_names.clone());
                        types.insert(mono_name.clone(), enum_ty);
                        if mono_fields.iter().any(|(_, fs)| !fs.is_empty()) {
                            variant_fields.insert(mono_name.clone(), mono_fields);
                        }
                    }
                    return Ty::Enum(mono_name, gdef.variant_names.clone());
                }
            }
            Ty::Param(n.clone(), resolved_args)
        }
        Ty::Set(a) => Ty::Set(Box::new(resolve_nested_generics(
            a,
            generic_types,
            types,
            variant_fields,
            registered,
        ))),
        Ty::Seq(a) => Ty::Seq(Box::new(resolve_nested_generics(
            a,
            generic_types,
            types,
            variant_fields,
            registered,
        ))),
        Ty::Map(k, v) => Ty::Map(
            Box::new(resolve_nested_generics(
                k,
                generic_types,
                types,
                variant_fields,
                registered,
            )),
            Box::new(resolve_nested_generics(
                v,
                generic_types,
                types,
                variant_fields,
                registered,
            )),
        ),
        Ty::Tuple(ts) => Ty::Tuple(
            ts.iter()
                .map(|t| {
                    resolve_nested_generics(t, generic_types, types, variant_fields, registered)
                })
                .collect(),
        ),
        Ty::Record(n, fs) => Ty::Record(
            n.clone(),
            fs.iter()
                .map(|(fn_, ft)| {
                    (
                        fn_.clone(),
                        resolve_nested_generics(
                            ft,
                            generic_types,
                            types,
                            variant_fields,
                            registered,
                        ),
                    )
                })
                .collect(),
        ),
        Ty::Fn(a, b) => Ty::Fn(
            Box::new(resolve_nested_generics(
                a,
                generic_types,
                types,
                variant_fields,
                registered,
            )),
            Box::new(resolve_nested_generics(
                b,
                generic_types,
                types,
                variant_fields,
                registered,
            )),
        ),
        Ty::Alias(n, t) => Ty::Alias(
            n.clone(),
            Box::new(resolve_nested_generics(
                t,
                generic_types,
                types,
                variant_fields,
                registered,
            )),
        ),
        Ty::Refinement(base, pred) => Ty::Refinement(
            Box::new(resolve_nested_generics(
                base,
                generic_types,
                types,
                variant_fields,
                registered,
            )),
            pred.clone(),
        ),
        _ => ty.clone(),
    }
}

/// Pre-pass: scan all type positions in the env, find Ty::Param references
/// to generic types, monomorphize them, and register in env.types / env.variant_fields.
/// Also emits diagnostics for wrong-arity uses and non-generic types used with type args.
pub(super) fn monomorphize_generics(env: &mut Env) {
    let generic_types = env.generic_types.clone();
    let known_types = env.types.clone();

    // Collect all Ty::Param occurrences from type positions across the env
    let mut all_params: Vec<(String, Vec<Ty>)> = Vec::new();

    // Walk entity field types
    for entity in env.entities.values() {
        for field in &entity.fields {
            collect_all_param_uses(&field.ty, &mut all_params);
        }
    }

    // Walk system fields, commands, steps, queries, system-local preds, derived fields
    for system in env.systems.values() {
        for field in &system.fields {
            collect_all_param_uses(&field.ty, &mut all_params);
        }
        for cmd in &system.commands {
            for (_, t) in &cmd.params {
                collect_all_param_uses(t, &mut all_params);
            }
            if let Some(rt) = &cmd.return_type {
                collect_all_param_uses(rt, &mut all_params);
            }
        }
        for step in &system.steps {
            for (_, t) in &step.params {
                collect_all_param_uses(t, &mut all_params);
            }
        }
        for query in &system.queries {
            for (_, t) in &query.params {
                collect_all_param_uses(t, &mut all_params);
            }
        }
        for pred in &system.preds {
            for (_, t) in &pred.params {
                collect_all_param_uses(t, &mut all_params);
            }
        }
        for derived in &system.derived_fields {
            collect_all_param_uses(&derived.ty, &mut all_params);
        }
    }

    // Walk fn param/return types
    for f in env.fns.values() {
        for (_, t) in &f.params {
            collect_all_param_uses(t, &mut all_params);
        }
        collect_all_param_uses(&f.ret_ty, &mut all_params);
    }

    // Walk pred param types
    for pred in env.preds.values() {
        for (_, t) in &pred.params {
            collect_all_param_uses(t, &mut all_params);
        }
    }

    // Walk type aliases
    for ty in env.types.values() {
        collect_all_param_uses(ty, &mut all_params);
    }

    // Validate and monomorphize
    let mut registered: HashSet<String> = HashSet::new();
    let mut reported: HashSet<String> = HashSet::new();
    for (name, args) in &all_params {
        // Skip builtins that already resolved (Set, Seq, Map, Store)
        if matches!(name.as_str(), "Set" | "Seq" | "Map" | "Store") {
            continue;
        }

        let report_key = format!("{}<{}>", name, args.len());
        if reported.contains(&report_key) {
            continue;
        }

        if let Some(gdef) = generic_types.get(name.as_str()) {
            // Generic type — validate arity
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
                continue;
            }
            // Monomorphize
            let mono_name = format_mono_name(name, args);
            if registered.contains(&mono_name) || env.types.contains_key(&mono_name) {
                continue;
            }
            registered.insert(mono_name.clone());
            let mono_fields = monomorphize_variant_fields(
                gdef,
                args,
                &generic_types,
                &mut env.types,
                &mut env.variant_fields,
                &mut registered,
            );
            let ty = Ty::Enum(mono_name.clone(), gdef.variant_names.clone());
            env.types.insert(mono_name.clone(), ty);
            if mono_fields.iter().any(|(_, fs)| !fs.is_empty()) {
                env.variant_fields.insert(mono_name.clone(), mono_fields);
            }
        } else if known_types.contains_key(name.as_str()) {
            // Non-generic type used with type arguments
            env.errors.push(ElabError::new(
                ErrorKind::TypeMismatch,
                crate::messages::not_a_generic_type(name),
                format!("`{name}` is a concrete type"),
            ));
            reported.insert(report_key);
        }
        // else: unknown type — will be caught by normal unresolved-type checks
    }
}

/// Recursively collect all Ty::Param references within a type (regardless of whether
/// they reference generic or non-generic types — validation happens later).
pub(super) fn collect_all_param_uses(ty: &Ty, out: &mut Vec<(String, Vec<Ty>)>) {
    match ty {
        Ty::Param(n, args) => {
            out.push((n.clone(), args.clone()));
            for a in args {
                collect_all_param_uses(a, out);
            }
        }
        Ty::Set(a) | Ty::Seq(a) => collect_all_param_uses(a, out),
        Ty::Map(k, v) | Ty::Fn(k, v) => {
            collect_all_param_uses(k, out);
            collect_all_param_uses(v, out);
        }
        Ty::Record(_, fs) => {
            for (_, ft) in fs {
                collect_all_param_uses(ft, out);
            }
        }
        Ty::Tuple(ts) => {
            for t in ts {
                collect_all_param_uses(t, out);
            }
        }
        Ty::Alias(_, t) | Ty::Refinement(t, _) => collect_all_param_uses(t, out),
        _ => {}
    }
}
