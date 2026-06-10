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
        Ty::Newtype(n, _) => n.clone(),
        Ty::Param(n, args) => format_mono_name(n, args),
        Ty::Set(a) => format!("Set<{}>", mono_ty_name(a)),
        Ty::Seq(a) => format!("Seq<{}>", mono_ty_name(a)),
        Ty::Map(k, v) => format!("Map<{}, {}>", mono_ty_name(k), mono_ty_name(v)),
        Ty::Store(entity) => format!("Store<{entity}>"),
        Ty::Relation(columns) => {
            let column_names: Vec<String> = columns.iter().map(mono_ty_name).collect();
            format!("Rel<{}>", column_names.join(", "))
        }
        Ty::Tuple(ts) => {
            let names: Vec<String> = ts.iter().map(mono_ty_name).collect();
            format!("({})", names.join(", "))
        }
        Ty::Fn(a, b) => format!("{} -> {}", mono_ty_name(a), mono_ty_name(b)),
        Ty::Refinement(base, _) => mono_ty_name(base),
        Ty::Named(n) => n.clone(),
        Ty::Error => "?".to_string(),
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
        Ty::Newtype(n, t) => Ty::Newtype(n.clone(), Box::new(substitute_ty(t, subst))),
        Ty::Relation(columns) => {
            Ty::Relation(columns.iter().map(|t| substitute_ty(t, subst)).collect())
        }
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
        Ty::Newtype(n, t) => Ty::Newtype(
            n.clone(),
            Box::new(resolve_nested_generics(
                t,
                generic_types,
                types,
                variant_fields,
                registered,
            )),
        ),
        Ty::Relation(columns) => Ty::Relation(
            columns
                .iter()
                .map(|column| {
                    resolve_nested_generics(
                        column,
                        generic_types,
                        types,
                        variant_fields,
                        registered,
                    )
                })
                .collect(),
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

    // Walk system fields, commands, actions, queries, system-local preds, derived fields
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
        for step in &system.actions {
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
        Ty::Relation(columns) => {
            for column in columns {
                collect_all_param_uses(column, out);
            }
        }
        Ty::Alias(_, t) | Ty::Newtype(_, t) | Ty::Refinement(t, _) => {
            collect_all_param_uses(t, out);
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Visibility;
    use crate::elab::types::{BuiltinTy, EExpr, Literal};
    use crate::span::Span;

    fn int_ty() -> Ty {
        Ty::Builtin(BuiltinTy::Int)
    }

    fn string_ty() -> Ty {
        Ty::Builtin(BuiltinTy::String)
    }

    fn param(name: &str, args: Vec<Ty>) -> Ty {
        Ty::Param(name.to_owned(), args)
    }

    fn generic_def(name: &str, type_params: &[&str], fields: EnumVariantFields) -> GenericTypeDef {
        GenericTypeDef {
            name: name.to_owned(),
            type_params: type_params
                .iter()
                .map(|param| (*param).to_owned())
                .collect(),
            variant_names: fields.iter().map(|(variant, _)| variant.clone()).collect(),
            variant_fields: fields,
            visibility: Visibility::Private,
            span: Span { start: 0, end: 0 },
        }
    }

    fn option_generic() -> GenericTypeDef {
        generic_def(
            "Option",
            &["T"],
            vec![
                (
                    "Some".to_owned(),
                    vec![("value".to_owned(), Ty::Named("T".to_owned()))],
                ),
                ("None".to_owned(), vec![]),
            ],
        )
    }

    fn box_generic() -> GenericTypeDef {
        generic_def(
            "Box",
            &["T"],
            vec![(
                "Boxed".to_owned(),
                vec![("value".to_owned(), Ty::Named("T".to_owned()))],
            )],
        )
    }

    fn assert_int(ty: &Ty, context: &str) {
        assert!(
            matches!(ty, Ty::Builtin(BuiltinTy::Int)),
            "{context} should be int, got {ty:?}"
        );
    }

    fn collected_names(ty: &Ty) -> Vec<String> {
        let mut uses = Vec::new();
        collect_all_param_uses(ty, &mut uses);
        uses.into_iter().map(|(name, _)| name).collect()
    }

    #[test]
    fn collect_all_param_uses_walks_newtype_inner() {
        let ty = Ty::Newtype(
            "Wrapper".to_owned(),
            Box::new(param("Option", vec![int_ty()])),
        );

        assert_eq!(collected_names(&ty), vec!["Option"]);
    }

    #[test]
    fn collect_all_param_uses_walks_relation_columns() {
        let ty = Ty::Relation(vec![
            param("Option", vec![int_ty()]),
            Ty::Map(
                Box::new(int_ty()),
                Box::new(param("Result", vec![int_ty(), int_ty()])),
            ),
        ]);

        assert_eq!(collected_names(&ty), vec!["Option", "Result"]);
    }

    #[test]
    fn collect_all_param_uses_walks_nested_newtype_relation_combinations() {
        let ty = Ty::Newtype(
            "Facts".to_owned(),
            Box::new(Ty::Relation(vec![
                Ty::Alias(
                    "Alias".to_owned(),
                    Box::new(param("Box", vec![param("Option", vec![int_ty()])])),
                ),
                Ty::Refinement(
                    Box::new(param("Result", vec![int_ty(), int_ty()])),
                    Box::new(crate::elab::types::EExpr::Lit(
                        Ty::Builtin(BuiltinTy::Bool),
                        crate::elab::types::Literal::Bool(true),
                        None,
                    )),
                ),
            ])),
        );

        assert_eq!(
            collected_names(&ty),
            vec!["Box", "Option", "Result"],
            "new wrapper forms must not hide nested generic uses"
        );
    }

    #[test]
    fn collect_all_param_uses_walks_set_seq_record_and_tuple_shapes() {
        let ty = Ty::Tuple(vec![
            Ty::Set(Box::new(param("SetItem", vec![int_ty()]))),
            Ty::Seq(Box::new(param("SeqItem", vec![int_ty()]))),
            Ty::Record(
                "Pair".to_owned(),
                vec![("left".to_owned(), param("RecordItem", vec![int_ty()]))],
            ),
        ]);

        assert_eq!(
            collected_names(&ty),
            vec!["SetItem", "SeqItem", "RecordItem"]
        );
    }

    #[test]
    fn mono_ty_name_preserves_nominal_newtype_identity() {
        let user_id = Ty::Newtype(
            "UserId".to_owned(),
            Box::new(Ty::Builtin(BuiltinTy::String)),
        );
        let order_id = Ty::Newtype(
            "OrderId".to_owned(),
            Box::new(Ty::Builtin(BuiltinTy::String)),
        );

        assert_eq!(mono_ty_name(&user_id), "UserId");
        assert_eq!(mono_ty_name(&order_id), "OrderId");
        assert_eq!(format_mono_name("Box", &[user_id]), "Box<UserId>");
        assert_eq!(format_mono_name("Box", &[order_id]), "Box<OrderId>");
    }

    #[test]
    fn substitute_ty_walks_every_composite_type_shape() {
        let subst = HashMap::from([("T".to_owned(), int_ty()), ("U".to_owned(), string_ty())]);
        let unresolved = Ty::Tuple(vec![
            Ty::Named("T".to_owned()),
            param("Box", vec![Ty::Named("T".to_owned())]),
            Ty::Record(
                "Pair".to_owned(),
                vec![("left".to_owned(), Ty::Named("T".to_owned()))],
            ),
            Ty::Set(Box::new(Ty::Named("T".to_owned()))),
            Ty::Seq(Box::new(Ty::Named("T".to_owned()))),
            Ty::Map(
                Box::new(Ty::Named("T".to_owned())),
                Box::new(Ty::Named("U".to_owned())),
            ),
            Ty::Fn(
                Box::new(Ty::Named("T".to_owned())),
                Box::new(Ty::Named("U".to_owned())),
            ),
            Ty::Alias("Alias".to_owned(), Box::new(Ty::Named("T".to_owned()))),
            Ty::Newtype("New".to_owned(), Box::new(Ty::Named("T".to_owned()))),
            Ty::Relation(vec![Ty::Named("T".to_owned()), Ty::Named("U".to_owned())]),
            Ty::Refinement(
                Box::new(Ty::Named("T".to_owned())),
                Box::new(EExpr::Lit(
                    Ty::Builtin(BuiltinTy::Bool),
                    Literal::Bool(true),
                    None,
                )),
            ),
        ]);

        let Ty::Tuple(items) = substitute_ty(&unresolved, &subst) else {
            panic!("expected tuple after substitution");
        };

        assert_int(&items[0], "named replacement");
        assert!(
            matches!(&items[1], Ty::Param(_, args) if matches!(args.as_slice(), [Ty::Builtin(BuiltinTy::Int)]))
        );
        let Ty::Record(_, fields) = &items[2] else {
            panic!("expected record, got {:?}", items[2]);
        };
        assert_int(&fields[0].1, "record field");
        let Ty::Set(set_inner) = &items[3] else {
            panic!("expected set, got {:?}", items[3]);
        };
        assert_int(set_inner, "set inner");
        let Ty::Seq(seq_inner) = &items[4] else {
            panic!("expected seq, got {:?}", items[4]);
        };
        assert_int(seq_inner, "seq inner");
        let Ty::Map(map_key, map_value) = &items[5] else {
            panic!("expected map, got {:?}", items[5]);
        };
        assert_int(map_key, "map key");
        assert!(matches!(map_value.as_ref(), Ty::Builtin(BuiltinTy::String)));
        let Ty::Fn(arg, ret) = &items[6] else {
            panic!("expected fn, got {:?}", items[6]);
        };
        assert_int(arg, "fn arg");
        assert!(matches!(ret.as_ref(), Ty::Builtin(BuiltinTy::String)));
        let Ty::Alias(_, alias_inner) = &items[7] else {
            panic!("expected alias, got {:?}", items[7]);
        };
        assert_int(alias_inner, "alias inner");
        let Ty::Newtype(_, newtype_inner) = &items[8] else {
            panic!("expected newtype, got {:?}", items[8]);
        };
        assert_int(newtype_inner, "newtype inner");
        let Ty::Relation(columns) = &items[9] else {
            panic!("expected relation, got {:?}", items[9]);
        };
        assert_int(&columns[0], "relation first column");
        assert!(matches!(&columns[1], Ty::Builtin(BuiltinTy::String)));
        let Ty::Refinement(base, _) = &items[10] else {
            panic!("expected refinement, got {:?}", items[10]);
        };
        assert_int(base, "refinement base");
    }

    #[test]
    fn monomorphize_variant_fields_substitutes_payloads_and_registers_nested_generics() {
        let option = option_generic();
        let wrapper = generic_def(
            "Wrapper",
            &["T"],
            vec![(
                "Wrap".to_owned(),
                vec![(
                    "inner".to_owned(),
                    param("Option", vec![Ty::Named("T".to_owned())]),
                )],
            )],
        );
        let generic_types = HashMap::from([
            ("Option".to_owned(), option),
            ("Wrapper".to_owned(), wrapper.clone()),
        ]);
        let mut types = HashMap::new();
        let mut variant_fields = HashMap::new();
        let mut registered = HashSet::new();

        let fields = monomorphize_variant_fields(
            &wrapper,
            &[int_ty()],
            &generic_types,
            &mut types,
            &mut variant_fields,
            &mut registered,
        );

        assert_eq!(fields.len(), 1);
        assert!(
            matches!(&fields[0].1[0].1, Ty::Enum(name, _) if name == "Option<int>"),
            "nested Option<T> payload should become Option<int>, got {:?}",
            fields
        );
        assert!(
            types.contains_key("Option<int>"),
            "nested generic should be registered in types"
        );
        assert!(
            variant_fields.contains_key("Option<int>"),
            "non-empty nested variant fields should be registered"
        );
    }

    #[test]
    fn resolve_nested_generics_walks_wrappers_and_does_not_overwrite_registered_types() {
        let option = option_generic();
        let generic_types = HashMap::from([("Option".to_owned(), option)]);
        let mut types = HashMap::from([(
            "Option<int>".to_owned(),
            Ty::Enum("Option<int>".to_owned(), vec!["Existing".to_owned()]),
        )]);
        let mut variant_fields = HashMap::new();
        let mut registered = HashSet::new();
        let ty = Ty::Tuple(vec![
            Ty::Set(Box::new(param("Option", vec![int_ty()]))),
            Ty::Seq(Box::new(param("Option", vec![int_ty()]))),
            Ty::Map(
                Box::new(param("Option", vec![int_ty()])),
                Box::new(param("Option", vec![int_ty()])),
            ),
            Ty::Record(
                "Record".to_owned(),
                vec![("field".to_owned(), param("Option", vec![int_ty()]))],
            ),
            Ty::Fn(
                Box::new(param("Option", vec![int_ty()])),
                Box::new(param("Option", vec![int_ty()])),
            ),
            Ty::Alias(
                "Alias".to_owned(),
                Box::new(param("Option", vec![int_ty()])),
            ),
            Ty::Newtype("New".to_owned(), Box::new(param("Option", vec![int_ty()]))),
            Ty::Relation(vec![param("Option", vec![int_ty()])]),
            Ty::Refinement(
                Box::new(param("Option", vec![int_ty()])),
                Box::new(EExpr::Lit(
                    Ty::Builtin(BuiltinTy::Bool),
                    Literal::Bool(true),
                    None,
                )),
            ),
        ]);

        let resolved = resolve_nested_generics(
            &ty,
            &generic_types,
            &mut types,
            &mut variant_fields,
            &mut registered,
        );

        let Ty::Tuple(items) = resolved else {
            panic!("expected tuple after nested generic resolution");
        };
        assert!(
            matches!(&items[0], Ty::Set(inner) if matches!(inner.as_ref(), Ty::Enum(name, _) if name == "Option<int>"))
        );
        assert!(
            matches!(&items[1], Ty::Seq(inner) if matches!(inner.as_ref(), Ty::Enum(name, _) if name == "Option<int>"))
        );
        assert!(
            matches!(&items[2], Ty::Map(key, value) if matches!(key.as_ref(), Ty::Enum(name, _) if name == "Option<int>") && matches!(value.as_ref(), Ty::Enum(name, _) if name == "Option<int>"))
        );
        assert!(
            matches!(&items[3], Ty::Record(_, fields) if matches!(&fields[0].1, Ty::Enum(name, _) if name == "Option<int>"))
        );
        assert!(
            matches!(&items[4], Ty::Fn(arg, ret) if matches!(arg.as_ref(), Ty::Enum(name, _) if name == "Option<int>") && matches!(ret.as_ref(), Ty::Enum(name, _) if name == "Option<int>"))
        );
        assert!(
            matches!(&items[5], Ty::Alias(_, inner) if matches!(inner.as_ref(), Ty::Enum(name, _) if name == "Option<int>"))
        );
        assert!(
            matches!(&items[6], Ty::Newtype(_, inner) if matches!(inner.as_ref(), Ty::Enum(name, _) if name == "Option<int>"))
        );
        assert!(
            matches!(&items[7], Ty::Relation(columns) if matches!(&columns[0], Ty::Enum(name, _) if name == "Option<int>"))
        );
        assert!(
            matches!(&items[8], Ty::Refinement(base, _) if matches!(base.as_ref(), Ty::Enum(name, _) if name == "Option<int>"))
        );
        assert!(
            matches!(types.get("Option<int>"), Some(Ty::Enum(_, variants)) if variants == &vec!["Existing".to_owned()]),
            "pre-existing monomorphized type should not be overwritten"
        );
        assert!(
            variant_fields.is_empty(),
            "pre-existing monomorphized type should not be re-registered"
        );
    }

    #[test]
    fn resolve_nested_generics_registers_variant_fields_when_all_variants_have_payloads() {
        let boxed = box_generic();
        let generic_types = HashMap::from([("Box".to_owned(), boxed)]);
        let mut types = HashMap::new();
        let mut variant_fields = HashMap::new();
        let mut registered = HashSet::new();

        let resolved = resolve_nested_generics(
            &param("Box", vec![int_ty()]),
            &generic_types,
            &mut types,
            &mut variant_fields,
            &mut registered,
        );

        assert!(matches!(resolved, Ty::Enum(name, _) if name == "Box<int>"));
        assert!(
            variant_fields.contains_key("Box<int>"),
            "all-non-empty variant payloads must still be registered"
        );
    }

    #[test]
    fn monomorphize_generics_registers_valid_uses_and_reports_wrong_arity() {
        let mut env = Env::new();
        env.generic_types
            .insert("Option".to_owned(), option_generic());
        env.generic_types.insert("Box".to_owned(), box_generic());
        env.types
            .insert("UsesOption".to_owned(), param("Option", vec![int_ty()]));
        env.types
            .insert("UsesBox".to_owned(), param("Box", vec![int_ty()]));
        env.types.insert(
            "BadOption".to_owned(),
            param("Option", vec![int_ty(), string_ty()]),
        );

        monomorphize_generics(&mut env);

        assert!(
            matches!(env.types.get("Option<int>"), Some(Ty::Enum(name, _)) if name == "Option<int>"),
            "valid generic use should register Option<int>, got {:?}",
            env.types.get("Option<int>")
        );
        assert!(
            env.variant_fields.contains_key("Option<int>"),
            "non-empty Option<int> variant fields should be retained"
        );
        assert!(
            env.variant_fields.contains_key("Box<int>"),
            "all-non-empty Box<int> variant fields should be retained"
        );
        assert!(
            env.errors
                .iter()
                .any(|error| error.message.contains("expects 1 type argument(s)")
                    && error.message.contains("2 were provided")),
            "wrong arity should be reported exactly once, got {:?}",
            env.errors
        );
    }

    #[test]
    fn monomorphize_generics_does_not_overwrite_preexisting_monomorphized_type() {
        let mut env = Env::new();
        env.generic_types
            .insert("Option".to_owned(), option_generic());
        env.types.insert(
            "Option<int>".to_owned(),
            Ty::Enum("Option<int>".to_owned(), vec!["Existing".to_owned()]),
        );
        env.types
            .insert("UsesOption".to_owned(), param("Option", vec![int_ty()]));

        monomorphize_generics(&mut env);

        assert!(
            matches!(env.types.get("Option<int>"), Some(Ty::Enum(_, variants)) if variants == &vec!["Existing".to_owned()]),
            "pre-existing monomorphized type should not be overwritten, got {:?}",
            env.types.get("Option<int>")
        );
        assert!(
            !env.variant_fields.contains_key("Option<int>"),
            "pre-existing monomorphized type should not have fields re-registered"
        );
    }
}
