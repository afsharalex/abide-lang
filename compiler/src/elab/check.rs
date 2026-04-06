//! Pass 3: Type-check expressions and validate well-formedness.
//!
//! Validates: field defaults match types, requires is Bool,
//! primed assignments target known fields, system uses reference known entities.

use std::collections::{HashMap, HashSet};

use super::env::Env;
use super::error::{ElabError, ErrorKind};
use super::types::{
    BuiltinTy, EAction, EContract, EEntity, EExpr, EField, EFn, EPattern, ESceneWhen, ESystem,
    EType, EVariant, ElabResult, Ty,
};
use crate::messages;

/// Type-check the resolved environment.
/// Returns an `ElabResult` with all elaborated declarations + any errors.
pub fn check(env: &Env) -> (ElabResult, Vec<ElabError>) {
    let mut errors = Vec::new();

    // Build comprehensive list of known names for "did you mean?" suggestions.
    // Includes type names, constructors, entity names, pred/fn/const names.
    let mut all_known_names: Vec<String> = Vec::new();
    for (name, ty) in &env.types {
        all_known_names.push(name.clone());
        if let Ty::Enum(_, ctors) = ty {
            all_known_names.extend(ctors.iter().cloned());
        }
    }
    all_known_names.extend(env.entities.keys().cloned());
    all_known_names.extend(env.preds.keys().cloned());
    all_known_names.extend(env.fns.keys().cloned());
    all_known_names.extend(env.consts.keys().cloned());

    for (name, ty) in &env.types {
        let decl_span = env.lookup_decl(name).and_then(|d| d.span);
        errors.extend(check_type(ty, decl_span));
        // Check refinement predicates in type aliases
        if let Ty::Refinement(_, pred) = ty {
            if let Some(pred_ty) = expr_type(pred) {
                if !matches!(pred_ty, Ty::Builtin(BuiltinTy::Bool) | Ty::Unresolved(_)) {
                    let mut err = ElabError::new(
                        ErrorKind::TypeMismatch,
                        format!(
                            "{} (type alias '{}')",
                            messages::REFINEMENT_PREDICATE_NOT_BOOL,
                            name
                        ),
                        name.clone(),
                    );
                    err.span = expr_span(pred);
                    err.help = Some(messages::HELP_REFINEMENT_BOOL.into());
                    errors.push(err);
                }
            }
        }
    }
    for entity in env.entities.values() {
        errors.extend(check_entity(entity, &all_known_names));
    }
    for system in env.systems.values() {
        errors.extend(check_system(env, system));
    }

    // Check fn contracts and refinement predicates
    for f in env.fns.values() {
        errors.extend(check_fn_contracts(f));
        errors.extend(check_refinement_predicates(f));
    }

    // Check constructor record well-formedness (unknown/missing/duplicate fields)
    for f in env.fns.values() {
        check_ctor_records_in_expr(&f.body, &env.variant_fields, &mut errors);
        for c in &f.contracts {
            match c {
                EContract::Requires(e)
                | EContract::Ensures(e)
                | EContract::Invariant(e) => {
                    check_ctor_records_in_expr(e, &env.variant_fields, &mut errors);
                }
                EContract::Decreases { measures, .. } => {
                    for m in measures {
                        check_ctor_records_in_expr(m, &env.variant_fields, &mut errors);
                    }
                }
            }
        }
    }
    for pred in env.preds.values() {
        check_ctor_records_in_expr(&pred.body, &env.variant_fields, &mut errors);
    }
    for prop in env.props.values() {
        check_ctor_records_in_expr(&prop.body, &env.variant_fields, &mut errors);
    }

    // Check for cyclic pred/prop definitions
    errors.extend(check_pred_prop_cycles(env));

    // Check match expression exhaustiveness and collection literal homogeneity
    for f in env.fns.values() {
        let fn_ctx = format!("fn {}", f.name);
        check_match_exhaustiveness(&f.body, &env.types, &env.entities, &mut errors);
        check_collection_homogeneity(&f.body, &fn_ctx, &mut errors);
        for c in &f.contracts {
            match c {
                EContract::Requires(e) | EContract::Ensures(e) | EContract::Invariant(e) => {
                    check_match_exhaustiveness(e, &env.types, &env.entities, &mut errors);
                    check_collection_homogeneity(e, &fn_ctx, &mut errors);
                }
                EContract::Decreases { measures, .. } => {
                    for m in measures {
                        check_match_exhaustiveness(m, &env.types, &env.entities, &mut errors);
                    }
                }
            }
        }
    }
    for pred in env.preds.values() {
        check_match_exhaustiveness(&pred.body, &env.types, &env.entities, &mut errors);
        check_collection_homogeneity(&pred.body, &format!("pred {}", pred.name), &mut errors);
    }
    for prop in env.props.values() {
        check_match_exhaustiveness(&prop.body, &env.types, &env.entities, &mut errors);
        check_collection_homogeneity(&prop.body, &format!("prop {}", prop.name), &mut errors);
    }
    for verify in &env.verifies {
        for a in &verify.asserts {
            check_match_exhaustiveness(a, &env.types, &env.entities, &mut errors);
            check_collection_homogeneity(a, &format!("verify {}", verify.name), &mut errors);
        }
    }
    for theorem in &env.theorems {
        for a in &theorem.shows {
            check_match_exhaustiveness(a, &env.types, &env.entities, &mut errors);
            check_collection_homogeneity(a, &format!("theorem {}", theorem.name), &mut errors);
        }
    }
    for lemma in &env.lemmas {
        for a in &lemma.body {
            check_match_exhaustiveness(a, &env.types, &env.entities, &mut errors);
            check_collection_homogeneity(a, &format!("lemma {}", lemma.name), &mut errors);
        }
    }
    for c in env.consts.values() {
        check_match_exhaustiveness(&c.body, &env.types, &env.entities, &mut errors);
        check_collection_homogeneity(&c.body, &format!("const {}", c.name), &mut errors);
    }
    for a in &env.axioms {
        check_match_exhaustiveness(&a.body, &env.types, &env.entities, &mut errors);
        check_collection_homogeneity(&a.body, &format!("axiom {}", a.name), &mut errors);
    }
    for scene in &env.scenes {
        for given in &scene.givens {
            if let Some(cond) = &given.condition {
                check_match_exhaustiveness(cond, &env.types, &env.entities, &mut errors);
            }
        }
        for when in &scene.whens {
            match when {
                ESceneWhen::Action { args, .. } => {
                    for arg in args {
                        check_match_exhaustiveness(arg, &env.types, &env.entities, &mut errors);
                    }
                }
                ESceneWhen::Assume(e) => {
                    check_match_exhaustiveness(e, &env.types, &env.entities, &mut errors);
                }
            }
        }
        for then_expr in &scene.thens {
            check_match_exhaustiveness(then_expr, &env.types, &env.entities, &mut errors);
        }
    }

    let result = ElabResult {
        module_name: env.module_name.clone(),
        includes: env.includes.clone(),
        use_decls: env.use_decls.iter().map(|e| e.decl.clone()).collect(),
        aliases: env.aliases.clone(),
        types: env
            .types
            .iter()
            .map(|(name, ty)| mk_etype(name, ty, &env.variant_fields))
            .collect(),
        entities: env.entities.values().cloned().collect(),
        systems: env.systems.values().cloned().collect(),
        preds: env.preds.values().cloned().collect(),
        props: env.props.values().cloned().collect(),
        verifies: env.verifies.clone(),
        scenes: env.scenes.clone(),
        theorems: env.theorems.clone(),
        axioms: env.axioms.clone(),
        lemmas: env.lemmas.clone(),
        consts: env.consts.values().cloned().collect(),
        fns: env.fns.values().cloned().collect(),
    };

    (result, errors)
}

fn mk_etype(
    _map_key: &str,
    ty: &Ty,
    variant_fields: &std::collections::HashMap<String, Vec<(String, Vec<(String, Ty)>)>>,
) -> EType {
    let canonical = ty.name().to_owned();
    match ty {
        Ty::Enum(name, vs) => {
            let variants = if let Some(field_info) = variant_fields.get(name) {
                // Has field info from collection — use Record variants where applicable
                field_info
                    .iter()
                    .map(|(vname, fields)| {
                        if fields.is_empty() {
                            EVariant::Simple(vname.clone())
                        } else {
                            EVariant::Record(vname.clone(), fields.clone())
                        }
                    })
                    .collect()
            } else {
                vs.iter().map(|v| EVariant::Simple(v.clone())).collect()
            };
            EType {
                name: canonical,
                variants,
                ty: ty.clone(),
                span: None,
            }
        }
        Ty::Record(_, fs) => EType {
            name: canonical.clone(),
            variants: vec![EVariant::Record(canonical, fs.clone())],
            ty: ty.clone(),
            span: None,
        },
        _ => EType {
            name: canonical,
            variants: Vec::new(),
            ty: ty.clone(),
            span: None,
        },
    }
}

// ── Type well-formedness ─────────────────────────────────────────────

fn check_type(ty: &Ty, decl_span: Option<crate::span::Span>) -> Vec<ElabError> {
    match ty {
        Ty::Enum(name, ctors) => {
            let dups = find_duplicates(ctors);
            dups.iter()
                .map(|d| {
                    let ctx = format!("type {name}");
                    if let Some(span) = decl_span {
                        ElabError::with_span(
                            ErrorKind::DuplicateDecl,
                            format!("duplicate constructor {d} in type {name}"),
                            &ctx,
                            span,
                        )
                    } else {
                        ElabError::new(
                            ErrorKind::DuplicateDecl,
                            format!("duplicate constructor {d} in type {name}"),
                            &ctx,
                        )
                    }
                })
                .collect()
        }
        Ty::Record(name, fields) => {
            let field_names: Vec<&String> = fields.iter().map(|(n, _)| n).collect();
            let dups = find_duplicates(&field_names);
            dups.iter()
                .map(|d| {
                    let ctx = format!("type {name}");
                    if let Some(span) = decl_span {
                        ElabError::with_span(
                            ErrorKind::DuplicateDecl,
                            format!("duplicate field {d} in record {name}"),
                            &ctx,
                            span,
                        )
                    } else {
                        ElabError::new(
                            ErrorKind::DuplicateDecl,
                            format!("duplicate field {d} in record {name}"),
                            &ctx,
                        )
                    }
                })
                .collect()
        }
        _ => Vec::new(),
    }
}

// ── Entity well-formedness ───────────────────────────────────────────

fn check_entity(entity: &EEntity, all_known_names: &[String]) -> Vec<ElabError> {
    let mut errors = Vec::new();

    for field in &entity.fields {
        errors.extend(check_field(&entity.name, field));
    }
    for action in &entity.actions {
        errors.extend(check_action(entity, action, all_known_names));
    }

    errors
}

fn check_field(entity_name: &str, field: &EField) -> Vec<ElabError> {
    use crate::elab::types::EFieldDefault;

    let ctx_str = format!("entity {entity_name}, field {}", field.name);

    let def_expr = match &field.default {
        Some(EFieldDefault::Value(e)) => e,
        Some(EFieldDefault::In(es)) => {
            let mut errors = Vec::new();
            for e in es {
                // For enum fields: each value must be a valid constructor
                if let Ty::Enum(_, ctors) = &field.ty {
                    match e {
                        EExpr::Var(_, v, _) => {
                            if !ctors.iter().any(|c| c == v) {
                                errors.push(ElabError::new(
                                    ErrorKind::InvalidDefault,
                                    format!("{v} is not a constructor of {}", field.ty.name()),
                                    &ctx_str,
                                ));
                            }
                        }
                        _ => {
                            errors.push(ElabError::new(
                                ErrorKind::InvalidDefault,
                                messages::in_value_not_constructor(&field.ty.name()),
                                &ctx_str,
                            ));
                        }
                    }
                }
                // For non-enum fields: check type compatibility
                if let Ty::Builtin(expected_bt) = &field.ty {
                    let ok = match e.ty() {
                        Ty::Builtin(actual_bt) => actual_bt == *expected_bt,
                        Ty::Unresolved(_) => true, // not yet resolved, skip
                        _ => false,
                    };
                    if !ok {
                        errors.push(ElabError::new(
                            ErrorKind::InvalidDefault,
                            format!(
                                "`in` value has type {}, expected {}",
                                e.ty().name(),
                                field.ty.name()
                            ),
                            &ctx_str,
                        ));
                    }
                }
            }
            return errors;
        }
        Some(EFieldDefault::Where(pred)) => {
            // `where` predicate must have Bool type
            let pred_ty = pred.ty();
            if !matches!(pred_ty, Ty::Builtin(BuiltinTy::Bool) | Ty::Unresolved(_)) {
                return vec![ElabError::new(
                    ErrorKind::InvalidDefault,
                    messages::where_predicate_not_bool(&pred_ty.name()),
                    &ctx_str,
                )];
            }
            return Vec::new();
        }
        None => return Vec::new(),
    };

    match (&field.ty, def_expr) {
        (Ty::Enum(_, ctors), EExpr::Var(_, v, _)) if !ctors.iter().any(|c| c == v) => {
            let err = if let Some(span) = field.span {
                ElabError::with_span(
                    ErrorKind::InvalidDefault,
                    format!("{v} is not a constructor of {}", field.ty.name()),
                    &ctx_str,
                    span,
                )
            } else {
                ElabError::new(
                    ErrorKind::InvalidDefault,
                    format!("{v} is not a constructor of {}", field.ty.name()),
                    &ctx_str,
                )
            };
            let help = if let Some(closest) = find_closest_name(v, ctors) {
                format!(
                    "did you mean '@{closest}'? Valid constructors: {}",
                    ctors.join(", ")
                )
            } else {
                format!("valid constructors: {}", ctors.join(", "))
            };
            vec![err.with_help(help)]
        }
        // Enum field with non-constructor expression (e.g., numeric literal)
        (Ty::Enum(name, ctors), _) if !matches!(def_expr, EExpr::Var(_, _, _)) => {
            vec![ElabError::new(
                ErrorKind::InvalidDefault,
                messages::enum_default_not_constructor(name, &ctors.join(", ")),
                &ctx_str,
            )]
        }
        // Builtin type mismatch (e.g., Int literal for Bool field)
        (Ty::Builtin(expected_bt), _) => {
            let ok = match def_expr.ty() {
                Ty::Builtin(actual_bt) => actual_bt == *expected_bt,
                Ty::Unresolved(_) => true,
                _ => false,
            };
            if ok {
                Vec::new()
            } else {
                vec![ElabError::new(
                    ErrorKind::InvalidDefault,
                    format!(
                        "default value has type {}, expected {}",
                        def_expr.ty().name(),
                        field.ty.name()
                    ),
                    &ctx_str,
                )]
            }
        }
        _ => Vec::new(),
    }
}

fn check_action(entity: &EEntity, action: &EAction, all_known_names: &[String]) -> Vec<ElabError> {
    let ctx = format!("entity {}, action {}", entity.name, action.name);
    let mut errors = Vec::new();

    // Check requires are boolean-typed
    for req in &action.requires {
        if !is_bool_expr(req) {
            let err = if let Some(span) = action.span {
                ElabError::with_span(
                    ErrorKind::TypeMismatch,
                    crate::messages::MSG_REQUIRES_SHOULD_BE_BOOL,
                    &ctx,
                    span,
                )
            } else {
                ElabError::new(
                    ErrorKind::TypeMismatch,
                    crate::messages::MSG_REQUIRES_SHOULD_BE_BOOL,
                    &ctx,
                )
            };
            errors.push(err);
        }
    }

    // Check for unresolved uppercase names that might be missing @ prefix.
    // Known names include entity fields + all global names (types, constructors,
    // entities, preds, fns, consts) for broad "did you mean?" suggestions.
    let mut known: Vec<String> = entity.fields.iter().map(|f| f.name.clone()).collect();
    known.extend_from_slice(all_known_names);
    for req in &action.requires {
        check_unresolved_constructors(req, &ctx, action.span, &known, &mut errors);
    }

    // Check primed assignments target known fields
    for expr in &action.body {
        errors.extend(check_assignment(entity, action, &ctx, expr));
    }

    errors
}

fn check_assignment(entity: &EEntity, action: &EAction, ctx: &str, expr: &EExpr) -> Vec<ElabError> {
    if let EExpr::Assign(_, lhs, _, _) = expr {
        if let EExpr::Prime(_, inner, _) = lhs.as_ref() {
            if let EExpr::Var(_, field_name, _) = inner.as_ref() {
                let field_names: Vec<String> =
                    entity.fields.iter().map(|f| f.name.clone()).collect();
                let field_strs: Vec<&str> = field_names.iter().map(String::as_str).collect();
                if !field_strs.contains(&field_name.as_str()) {
                    let err = if let Some(span) = action.span {
                        ElabError::with_span(
                            ErrorKind::InvalidPrime,
                            format!("'{field_name}' is not a field of {}", entity.name),
                            ctx,
                            span,
                        )
                    } else {
                        ElabError::new(
                            ErrorKind::InvalidPrime,
                            format!("'{field_name}' is not a field of {}", entity.name),
                            ctx,
                        )
                    };
                    let help = if let Some(closest) = find_closest_name(field_name, &field_names) {
                        format!("did you mean '{closest}'?")
                    } else {
                        crate::messages::HELP_PRIME_FIELDS_ONLY.to_owned()
                    };
                    return vec![err.with_help(help)];
                }
            }
        }
    }
    Vec::new()
}

// ── System well-formedness ───────────────────────────────────────────

fn check_system(env: &Env, system: &ESystem) -> Vec<ElabError> {
    let mut errors = Vec::new();
    let sys_ctx = format!("system {}", system.name);

    let entity_names: Vec<String> = env.entities.keys().cloned().collect();
    // Also accept canonical entity names (the entity's declared name may differ
    // from the working namespace key when imported via alias).
    let canonical_names: std::collections::HashSet<String> = env
        .entities
        .values()
        .map(|e| e.name.clone())
        .collect();
    for entity_name in &system.uses {
        if env.lookup_entity(entity_name).is_none() && !canonical_names.contains(entity_name) {
            let mut err = if let Some(span) = system.span {
                ElabError::with_span(
                    ErrorKind::UndefinedRef,
                    format!("system {} uses unknown entity '{entity_name}'", system.name),
                    &sys_ctx,
                    span,
                )
            } else {
                ElabError::new(
                    ErrorKind::UndefinedRef,
                    format!("system {} uses unknown entity '{entity_name}'", system.name),
                    &sys_ctx,
                )
            };
            if let Some(closest) = find_closest_name(entity_name, &entity_names) {
                err = err.with_help(format!("did you mean '{closest}'?"));
            }
            errors.push(err);
        }
    }

    for scope in &system.scopes {
        if scope.lo < 0 || scope.hi < scope.lo {
            let err = if let Some(span) = system.span {
                ElabError::with_span(
                    ErrorKind::InvalidScope,
                    format!(
                        "scope {} has invalid range {}..{}",
                        scope.entity, scope.lo, scope.hi
                    ),
                    &sys_ctx,
                    span,
                )
            } else {
                ElabError::new(
                    ErrorKind::InvalidScope,
                    format!(
                        "scope {} has invalid range {}..{}",
                        scope.entity, scope.lo, scope.hi
                    ),
                    &sys_ctx,
                )
            };
            errors.push(err);
        }
    }

    errors
}

// ── Helpers ──────────────────────────────────────────────────────────

/// Check for unresolved uppercase names in an expression that might be
/// missing an `@` prefix. Produces a hint when a name looks like a
/// constructor but was not resolved.
#[allow(clippy::too_many_lines)]
/// Check that collection literals have homogeneous element types.
/// Called recursively on all expressions.
fn check_collection_homogeneity(
    expr: &EExpr,
    ctx: &str,
    errors: &mut Vec<ElabError>,
) {
    match expr {
        EExpr::SetLit(_, elems, _) if elems.len() > 1 => {
            let first_ty = elems[0].ty();
            for (i, e) in elems.iter().enumerate().skip(1) {
                let e_ty = e.ty();
                if !types_compatible(&first_ty, &e_ty) {
                    errors.push(ElabError::new(
                        ErrorKind::TypeMismatch,
                        format!(
                            "Set literal element {} has type {}, expected {} (matching first element)",
                            i, e_ty.name(), first_ty.name()
                        ),
                        ctx,
                    ));
                }
            }
        }
        EExpr::SeqLit(_, elems, _) if elems.len() > 1 => {
            let first_ty = elems[0].ty();
            for (i, e) in elems.iter().enumerate().skip(1) {
                let e_ty = e.ty();
                if !types_compatible(&first_ty, &e_ty) {
                    errors.push(ElabError::new(
                        ErrorKind::TypeMismatch,
                        format!(
                            "Seq literal element {} has type {}, expected {} (matching first element)",
                            i, e_ty.name(), first_ty.name()
                        ),
                        ctx,
                    ));
                }
            }
        }
        EExpr::MapLit(_, entries, _) if entries.len() > 1 => {
            let first_k_ty = entries[0].0.ty();
            let first_v_ty = entries[0].1.ty();
            for (i, (k, v)) in entries.iter().enumerate().skip(1) {
                let k_ty = k.ty();
                let v_ty = v.ty();
                if !types_compatible(&first_k_ty, &k_ty) {
                    errors.push(ElabError::new(
                        ErrorKind::TypeMismatch,
                        format!(
                            "Map literal key {} has type {}, expected {} (matching first key)",
                            i, k_ty.name(), first_k_ty.name()
                        ),
                        ctx,
                    ));
                }
                if !types_compatible(&first_v_ty, &v_ty) {
                    errors.push(ElabError::new(
                        ErrorKind::TypeMismatch,
                        format!(
                            "Map literal value {} has type {}, expected {} (matching first value)",
                            i, v_ty.name(), first_v_ty.name()
                        ),
                        ctx,
                    ));
                }
            }
        }
        _ => {}
    }
    // Recurse into sub-expressions
    match expr {
        EExpr::BinOp(_, _, a, b, _) => {
            check_collection_homogeneity(a, ctx, errors);
            check_collection_homogeneity(b, ctx, errors);
        }
        EExpr::UnOp(_, _, e, _) | EExpr::Prime(_, e, _) | EExpr::Field(_, e, _, _) => {
            check_collection_homogeneity(e, ctx, errors);
        }
        EExpr::Call(_, f, args, _) => {
            check_collection_homogeneity(f, ctx, errors);
            for a in args { check_collection_homogeneity(a, ctx, errors); }
        }
        EExpr::QualCall(_, _, _, args, _) => {
            for a in args { check_collection_homogeneity(a, ctx, errors); }
        }
        EExpr::SetLit(_, elems, _) | EExpr::SeqLit(_, elems, _) => {
            for e in elems { check_collection_homogeneity(e, ctx, errors); }
        }
        EExpr::MapLit(_, entries, _) => {
            for (k, v) in entries {
                check_collection_homogeneity(k, ctx, errors);
                check_collection_homogeneity(v, ctx, errors);
            }
        }
        _ => {}
    }
}

/// Check if two types are compatible (same kind, ignoring unresolved).
fn types_compatible(a: &Ty, b: &Ty) -> bool {
    match (a, b) {
        (Ty::Unresolved(_), _) | (_, Ty::Unresolved(_)) => true,
        (Ty::Builtin(a), Ty::Builtin(b)) => a == b,
        (Ty::Enum(na, _), Ty::Enum(nb, _)) => na == nb,
        (Ty::Set(a), Ty::Set(b)) => types_compatible(a, b),
        (Ty::Seq(a), Ty::Seq(b)) => types_compatible(a, b),
        (Ty::Map(ka, va), Ty::Map(kb, vb)) => types_compatible(ka, kb) && types_compatible(va, vb),
        (Ty::Entity(a), Ty::Entity(b)) => a == b,
        (Ty::Alias(a, _), Ty::Alias(b, _)) => a == b,
        _ => false,
    }
}

fn check_unresolved_constructors(
    expr: &EExpr,
    ctx: &str,
    span: Option<crate::span::Span>,
    known_names: &[String],
    errors: &mut Vec<ElabError>,
) {
    match expr {
        EExpr::Var(Ty::Unresolved(_), name, _)
            if !name.is_empty() && name.chars().next().unwrap().is_uppercase() =>
        {
            let err = if let Some(s) = span {
                ElabError::with_span(
                    ErrorKind::UndefinedRef,
                    format!("unresolved name '{name}'"),
                    ctx,
                    s,
                )
            } else {
                ElabError::new(
                    ErrorKind::UndefinedRef,
                    format!("unresolved name '{name}'"),
                    ctx,
                )
            };
            // Try name suggestion first, fall back to constructor hint
            let help = if let Some(closest) = find_closest_name(name, known_names) {
                format!("did you mean '{closest}'?")
            } else {
                format!("if '{name}' is a state constructor, write '@{name}'")
            };
            errors.push(err.with_help(help));
        }
        EExpr::BinOp(_, _, l, r, _)
        | EExpr::Assign(_, l, r, _)
        | EExpr::Seq(_, l, r, _)
        | EExpr::SameStep(_, l, r, _)
        | EExpr::Pipe(_, l, r, _)
        | EExpr::In(_, l, r, _) => {
            check_unresolved_constructors(l, ctx, span, known_names, errors);
            check_unresolved_constructors(r, ctx, span, known_names, errors);
        }
        EExpr::CtorRecord(_, _, _, fields, _) => {
            for (_, e) in fields {
                check_unresolved_constructors(e, ctx, span, known_names, errors);
            }
        }
        EExpr::UnOp(_, _, e, _)
        | EExpr::Always(_, e, _)
        | EExpr::Eventually(_, e, _)
        | EExpr::Assert(_, e, _)
        | EExpr::Assume(_, e, _)
        | EExpr::Prime(_, e, _)
        | EExpr::Card(_, e, _)
        | EExpr::Field(_, e, _, _)
        | EExpr::NamedPair(_, _, e, _) => {
            check_unresolved_constructors(e, ctx, span, known_names, errors);
        }
        EExpr::Until(_, l, r, _) => {
            check_unresolved_constructors(l, ctx, span, known_names, errors);
            check_unresolved_constructors(r, ctx, span, known_names, errors);
        }
        EExpr::Call(_, f, args, _) => {
            check_unresolved_constructors(f, ctx, span, known_names, errors);
            for arg in args {
                check_unresolved_constructors(arg, ctx, span, known_names, errors);
            }
        }
        EExpr::QualCall(_, _, _, args, _) => {
            for arg in args {
                check_unresolved_constructors(arg, ctx, span, known_names, errors);
            }
        }
        EExpr::Quant(_, _, _, _, body, _) | EExpr::Lam(_, _, body, _) => {
            check_unresolved_constructors(body, ctx, span, known_names, errors);
        }
        EExpr::Match(scrut, arms, _) => {
            check_unresolved_constructors(scrut, ctx, span, known_names, errors);
            for (_, guard, body) in arms {
                if let Some(g) = guard {
                    check_unresolved_constructors(g, ctx, span, known_names, errors);
                }
                check_unresolved_constructors(body, ctx, span, known_names, errors);
            }
        }
        EExpr::Let(binds, body, _) => {
            for (_, _, e) in binds {
                check_unresolved_constructors(e, ctx, span, known_names, errors);
            }
            check_unresolved_constructors(body, ctx, span, known_names, errors);
        }
        EExpr::TupleLit(_, es, _) | EExpr::SetLit(_, es, _) | EExpr::SeqLit(_, es, _) => {
            for e in es {
                check_unresolved_constructors(e, ctx, span, known_names, errors);
            }
        }
        EExpr::CallR(_, f, refs, args, _) => {
            check_unresolved_constructors(f, ctx, span, known_names, errors);
            for r in refs {
                check_unresolved_constructors(r, ctx, span, known_names, errors);
            }
            for a in args {
                check_unresolved_constructors(a, ctx, span, known_names, errors);
            }
        }
        EExpr::MapUpdate(_, m, k, v, _) => {
            check_unresolved_constructors(m, ctx, span, known_names, errors);
            check_unresolved_constructors(k, ctx, span, known_names, errors);
            check_unresolved_constructors(v, ctx, span, known_names, errors);
        }
        EExpr::Index(_, m, k, _) => {
            check_unresolved_constructors(m, ctx, span, known_names, errors);
            check_unresolved_constructors(k, ctx, span, known_names, errors);
        }
        EExpr::SetComp(_, proj, _, _, filter, _) => {
            if let Some(p) = proj {
                check_unresolved_constructors(p, ctx, span, known_names, errors);
            }
            check_unresolved_constructors(filter, ctx, span, known_names, errors);
        }
        EExpr::MapLit(_, entries, _) => {
            for (k, v) in entries {
                check_unresolved_constructors(k, ctx, span, known_names, errors);
                check_unresolved_constructors(v, ctx, span, known_names, errors);
            }
        }
        // True leaf nodes: Lit, Qual, Unresolved (lowercase), Sorry, Todo
        _ => {}
    }
}

fn is_bool_expr(e: &EExpr) -> bool {
    match e.ty() {
        Ty::Builtin(BuiltinTy::Bool) | Ty::Unresolved(_) => true, // might be Bool; don't error
        _ => false,
    }
}

/// Find the closest matching name by edit distance (Levenshtein).
/// Returns `Some(closest)` if there's a match within distance 3, else `None`.
pub(crate) fn find_closest_name<'a>(target: &str, candidates: &'a [String]) -> Option<&'a str> {
    let mut best: Option<(&str, usize)> = None;
    for candidate in candidates {
        let dist = levenshtein(target, candidate);
        if dist <= 3 && dist > 0 && (best.is_none() || dist < best.unwrap().1) {
            best = Some((candidate, dist));
        }
    }
    best.map(|(name, _)| name)
}

/// Simple Levenshtein distance between two strings.
fn levenshtein(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    let m = a.len();
    let n = b.len();
    let mut dp = vec![vec![0usize; n + 1]; m + 1];
    for (i, row) in dp.iter_mut().enumerate().take(m + 1) {
        row[0] = i;
    }
    #[allow(clippy::needless_range_loop)]
    for j in 0..=n {
        dp[0][j] = j;
    }
    for i in 1..=m {
        for j in 1..=n {
            let cost = usize::from(a[i - 1] != b[j - 1]);
            dp[i][j] = (dp[i - 1][j] + 1)
                .min(dp[i][j - 1] + 1)
                .min(dp[i - 1][j - 1] + cost);
        }
    }
    dp[m][n]
}

fn find_duplicates<T: PartialEq>(items: &[T]) -> Vec<&T> {
    let mut dups = Vec::new();
    for (i, item) in items.iter().enumerate() {
        if items[..i].contains(item) && !dups.contains(&item) {
            dups.push(item);
        }
    }
    dups
}

// ── Fn contract checking ────────────────────────────────────────────

/// Check that fn contracts are well-typed:
/// - requires/ensures must be Bool
/// - decreases measures must be Int
/// - decreases * emits a warning
fn check_fn_contracts(f: &EFn) -> Vec<ElabError> {
    let mut errors = Vec::new();
    for c in &f.contracts {
        match c {
            EContract::Requires(e) => {
                if let Some(ty) = expr_type(e) {
                    if !matches!(ty, Ty::Builtin(BuiltinTy::Bool)) {
                        let mut err = ElabError::new(
                            ErrorKind::TypeMismatch,
                            messages::REQUIRES_NOT_BOOL.to_owned(),
                            f.name.clone(),
                        );
                        err.span = expr_span(e);
                        err.help = Some(messages::HELP_REQUIRES_BOOL.into());
                        errors.push(err);
                    }
                }
            }
            EContract::Ensures(e) => {
                if let Some(ty) = expr_type(e) {
                    if !matches!(ty, Ty::Builtin(BuiltinTy::Bool)) {
                        let mut err = ElabError::new(
                            ErrorKind::TypeMismatch,
                            messages::ENSURES_NOT_BOOL.to_owned(),
                            f.name.clone(),
                        );
                        err.span = expr_span(e);
                        err.help = Some(messages::HELP_ENSURES_BOOL.into());
                        errors.push(err);
                    }
                }
            }
            EContract::Decreases { measures, star } => {
                if *star {
                    let mut w = ElabError::warning(
                        messages::DECREASES_STAR_WARNING.to_owned(),
                        f.name.clone(),
                    );
                    w.span = f.span;
                    w.file.clone_from(&f.file);
                    errors.push(w);
                }
                for m in measures {
                    if let Some(ty) = expr_type(m) {
                        if !matches!(ty, Ty::Builtin(BuiltinTy::Int)) {
                            let mut err = ElabError::new(
                                ErrorKind::TypeMismatch,
                                messages::DECREASES_MEASURE_NOT_INT.to_owned(),
                                f.name.clone(),
                            );
                            err.span = expr_span(m);
                            err.help = Some(messages::HELP_DECREASES_INT.into());
                            errors.push(err);
                        }
                    }
                }
            }
            EContract::Invariant(e) => {
                if let Some(ty) = expr_type(e) {
                    if !matches!(ty, Ty::Builtin(BuiltinTy::Bool)) {
                        let mut err = ElabError::new(
                            ErrorKind::TypeMismatch,
                            "invariant clause must have type Bool".to_owned(),
                            f.name.clone(),
                        );
                        err.span = expr_span(e);
                        err.help = Some("invariant clauses must evaluate to Bool".into());
                        errors.push(err);
                    }
                }
            }
        }
    }
    errors
}

/// Check that refinement predicates on fn parameters are Bool.
fn check_refinement_predicates(f: &EFn) -> Vec<ElabError> {
    let mut errors = Vec::new();
    for (param_name, param_ty) in &f.params {
        if let Ty::Refinement(_, pred) = param_ty {
            if let Some(ty) = expr_type(pred) {
                if !matches!(ty, Ty::Builtin(BuiltinTy::Bool) | Ty::Unresolved(_)) {
                    let mut err = ElabError::new(
                        ErrorKind::TypeMismatch,
                        format!(
                            "{} (parameter '{}')",
                            messages::REFINEMENT_PREDICATE_NOT_BOOL,
                            param_name
                        ),
                        f.name.clone(),
                    );
                    err.span = expr_span(pred);
                    err.help = Some(messages::HELP_REFINEMENT_BOOL.into());
                    errors.push(err);
                }
            }
        }
    }
    errors
}

/// Extract the type annotation from an elaborated expression (if available).
fn expr_type(e: &EExpr) -> Option<&Ty> {
    match e {
        EExpr::Lit(ty, _, _)
        | EExpr::Var(ty, _, _)
        | EExpr::BinOp(ty, _, _, _, _)
        | EExpr::UnOp(ty, _, _, _)
        | EExpr::Call(ty, _, _, _)
        | EExpr::QualCall(ty, _, _, _, _)
        | EExpr::Field(ty, _, _, _)
        | EExpr::Quant(ty, _, _, _, _, _)
        | EExpr::Always(ty, _, _)
        | EExpr::Eventually(ty, _, _) => Some(ty),
        _ => None,
    }
}

/// Extract span from an elaborated expression.
fn expr_span(e: &EExpr) -> Option<crate::span::Span> {
    match e {
        EExpr::Lit(_, _, sp)
        | EExpr::Var(_, _, sp)
        | EExpr::BinOp(_, _, _, _, sp)
        | EExpr::UnOp(_, _, _, sp)
        | EExpr::Call(_, _, _, sp)
        | EExpr::QualCall(_, _, _, _, sp)
        | EExpr::Field(_, _, _, sp) => *sp,
        _ => None,
    }
}

// ── Cycle detection for fn/pred/prop definitions ────────────────────

/// Detect cyclic definitions in fn, pred, and prop declarations.
///
/// All three are definitional abstractions that get expanded during
/// verification. Recursive definitions would cause non-termination.
/// Examples:
/// - `pred p(x) = p(x)` — direct self-reference
/// - `pred p(x) = q(x)` + `pred q(x) = p(x)` — mutual recursion
/// - `prop a = p(x)` + `pred p(x) = a` — prop-pred cycle
/// - `fn f(x) = g(x)` + `fn g(x) = f(x)` — fn-fn cycle
fn check_pred_prop_cycles(env: &Env) -> Vec<ElabError> {
    let mut errors = Vec::new();

    // Build dependency graph: name → set of fn/pred/prop names referenced in body
    let mut deps: HashMap<String, HashSet<String>> = HashMap::new();

    // All fn, pred, and prop names
    let mut all_names: HashSet<String> = HashSet::new();
    for name in env.preds.keys() {
        all_names.insert(name.clone());
    }
    for name in env.props.keys() {
        all_names.insert(name.clone());
    }
    for name in env.fns.keys() {
        all_names.insert(name.clone());
    }

    // Extract dependencies from pred bodies
    for (name, pred) in &env.preds {
        let mut referenced = HashSet::new();
        let bound: HashSet<String> = pred.params.iter().map(|(n, _)| n.clone()).collect();
        collect_name_refs(&pred.body, &all_names, &bound, &mut referenced);
        deps.insert(name.clone(), referenced);
    }

    // Extract dependencies from prop bodies
    for (name, prop) in &env.props {
        let mut referenced = HashSet::new();
        collect_name_refs(&prop.body, &all_names, &HashSet::new(), &mut referenced);
        deps.insert(name.clone(), referenced);
    }

    // Extract dependencies from fn bodies.
    // Functions with a `decreases` clause may reference themselves (self-recursion
    // is guarded by the termination measure), so remove the self-edge.
    for (name, f) in &env.fns {
        let mut referenced = HashSet::new();
        let bound: HashSet<String> = f.params.iter().map(|(n, _)| n.clone()).collect();
        collect_name_refs(&f.body, &all_names, &bound, &mut referenced);
        let has_decreases = f
            .contracts
            .iter()
            .any(|c| matches!(c, super::types::EContract::Decreases { .. }));
        if has_decreases {
            referenced.remove(name);
        }
        deps.insert(name.clone(), referenced);
    }

    // DFS cycle detection
    let mut visited = HashSet::new();
    let mut in_stack = HashSet::new();

    for name in all_names {
        if !visited.contains(&name) {
            if let Some(cycle) = dfs_find_cycle(&name, &deps, &mut visited, &mut in_stack) {
                let is_self_recursive = cycle.len() == 2 && cycle.first() == cycle.last();
                // Check if all names in the cycle are fns (decreases is applicable)
                let cycle_names: Vec<&str> = cycle.iter().map(String::as_str).collect();
                let all_fns = cycle_names
                    .iter()
                    .filter(|n| **n != cycle_names[0] || !is_self_recursive)
                    .all(|n| env.fns.contains_key(*n));
                let mut err = ElabError::new(
                    ErrorKind::CyclicDefinition,
                    format!("circular definition detected: {}", cycle.join(" → ")),
                    name.clone(),
                );
                err.help = Some(if is_self_recursive && env.fns.contains_key(&name) {
                    messages::HELP_SELF_RECURSION_DECREASES.into()
                } else if all_fns {
                    messages::HELP_MUTUAL_FN_DECREASES.into()
                } else {
                    messages::HELP_CIRCULAR_DEFINITION.into()
                });
                errors.push(err);
            }
        }
    }

    errors
}

/// Collect fn/pred/prop name references from an elaborated expression.
///
/// Respects variable scoping: a `Var` that is shadowed by a parameter,
/// quantifier binding, let binding, or lambda parameter is NOT counted
/// as a dependency reference.
#[allow(clippy::match_same_arms, clippy::too_many_lines)]
fn collect_name_refs(
    expr: &EExpr,
    known_names: &HashSet<String>,
    bound: &HashSet<String>,
    refs: &mut HashSet<String>,
) {
    match expr {
        EExpr::Var(_, name, _) => {
            if !bound.contains(name) && known_names.contains(name.as_str()) {
                refs.insert(name.clone());
            }
        }
        EExpr::Call(_, func, args, _) => {
            collect_name_refs(func, known_names, bound, refs);
            for arg in args {
                collect_name_refs(arg, known_names, bound, refs);
            }
        }
        EExpr::QualCall(_, _, _, args, _) => {
            for arg in args {
                collect_name_refs(arg, known_names, bound, refs);
            }
        }
        EExpr::CallR(_, func, ref_args, args, _) => {
            collect_name_refs(func, known_names, bound, refs);
            for arg in ref_args {
                collect_name_refs(arg, known_names, bound, refs);
            }
            for arg in args {
                collect_name_refs(arg, known_names, bound, refs);
            }
        }
        EExpr::BinOp(_, _, l, r, _) => {
            collect_name_refs(l, known_names, bound, refs);
            collect_name_refs(r, known_names, bound, refs);
        }
        EExpr::UnOp(_, _, e, _) => collect_name_refs(e, known_names, bound, refs),
        EExpr::Field(_, e, _, _) => collect_name_refs(e, known_names, bound, refs),
        EExpr::Prime(_, e, _) => collect_name_refs(e, known_names, bound, refs),
        EExpr::Quant(_, _, var, _, body, _) => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.clone());
            collect_name_refs(body, known_names, &inner_bound, refs);
        }
        EExpr::Always(_, e, _) => collect_name_refs(e, known_names, bound, refs),
        EExpr::Eventually(_, e, _) => collect_name_refs(e, known_names, bound, refs),
        EExpr::Until(_, l, r, _) => {
            collect_name_refs(l, known_names, bound, refs);
            collect_name_refs(r, known_names, bound, refs);
        }
        EExpr::Assert(_, e, _) => collect_name_refs(e, known_names, bound, refs),
        EExpr::Assume(_, e, _) => collect_name_refs(e, known_names, bound, refs),
        EExpr::Assign(_, l, r, _) => {
            collect_name_refs(l, known_names, bound, refs);
            collect_name_refs(r, known_names, bound, refs);
        }
        EExpr::Seq(_, l, r, _)
        | EExpr::SameStep(_, l, r, _)
        | EExpr::Pipe(_, l, r, _)
        | EExpr::In(_, l, r, _) => {
            collect_name_refs(l, known_names, bound, refs);
            collect_name_refs(r, known_names, bound, refs);
        }
        EExpr::Let(binds, body, _) => {
            let mut inner_bound = bound.clone();
            for (name, _, e) in binds {
                collect_name_refs(e, known_names, &inner_bound, refs);
                inner_bound.insert(name.clone());
            }
            collect_name_refs(body, known_names, &inner_bound, refs);
        }
        EExpr::Lam(params, _, body, _) => {
            let mut inner_bound = bound.clone();
            for (name, _) in params {
                inner_bound.insert(name.clone());
            }
            collect_name_refs(body, known_names, &inner_bound, refs);
        }
        EExpr::Match(scrut, arms, _) => {
            collect_name_refs(scrut, known_names, bound, refs);
            for (pat, guard, body) in arms {
                let mut arm_bound = bound.clone();
                collect_epattern_vars(pat, &mut arm_bound);
                if let Some(g) = guard {
                    collect_name_refs(g, known_names, &arm_bound, refs);
                }
                collect_name_refs(body, known_names, &arm_bound, refs);
            }
        }
        EExpr::NamedPair(_, _, e, _) => collect_name_refs(e, known_names, bound, refs),
        EExpr::TupleLit(_, elems, _) => {
            for e in elems {
                collect_name_refs(e, known_names, bound, refs);
            }
        }
        EExpr::Card(_, e, _) => collect_name_refs(e, known_names, bound, refs),
        EExpr::MapUpdate(_, m, k, v, _) => {
            collect_name_refs(m, known_names, bound, refs);
            collect_name_refs(k, known_names, bound, refs);
            collect_name_refs(v, known_names, bound, refs);
        }
        EExpr::Index(_, m, k, _) => {
            collect_name_refs(m, known_names, bound, refs);
            collect_name_refs(k, known_names, bound, refs);
        }
        EExpr::SetComp(_, proj, var, _, filter, _) => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.clone());
            if let Some(p) = proj {
                collect_name_refs(p, known_names, &inner_bound, refs);
            }
            collect_name_refs(filter, known_names, &inner_bound, refs);
        }
        EExpr::Block(items, _) => {
            for item in items {
                collect_name_refs(item, known_names, bound, refs);
            }
        }
        EExpr::VarDecl(name, _, init, rest, _) => {
            collect_name_refs(init, known_names, bound, refs);
            let mut inner_bound = bound.clone();
            inner_bound.insert(name.clone());
            collect_name_refs(rest, known_names, &inner_bound, refs);
        }
        EExpr::While(cond, _, body, _) => {
            collect_name_refs(cond, known_names, bound, refs);
            collect_name_refs(body, known_names, bound, refs);
        }
        EExpr::IfElse(cond, then_body, else_body, _) => {
            collect_name_refs(cond, known_names, bound, refs);
            collect_name_refs(then_body, known_names, bound, refs);
            if let Some(e) = else_body {
                collect_name_refs(e, known_names, bound, refs);
            }
        }
        EExpr::CtorRecord(_, _, _, fields, _) => {
            for (_, e) in fields {
                collect_name_refs(e, known_names, bound, refs);
            }
        }
        // Leaf nodes — no references
        EExpr::Lit(..)
        | EExpr::Qual(..)
        | EExpr::Unresolved(..)
        | EExpr::Sorry(_)
        | EExpr::Todo(_)
        | EExpr::SetLit(..)
        | EExpr::SeqLit(..)
        | EExpr::MapLit(..) => {}
    }
}

/// DFS cycle detection. Returns the cycle path if one is found.
fn dfs_find_cycle(
    node: &str,
    deps: &HashMap<String, HashSet<String>>,
    visited: &mut HashSet<String>,
    in_stack: &mut HashSet<String>,
) -> Option<Vec<String>> {
    visited.insert(node.to_owned());
    in_stack.insert(node.to_owned());

    if let Some(neighbors) = deps.get(node) {
        for neighbor in neighbors {
            if !visited.contains(neighbor.as_str()) {
                if let Some(mut cycle) = dfs_find_cycle(neighbor, deps, visited, in_stack) {
                    cycle.insert(0, node.to_owned());
                    return Some(cycle);
                }
            } else if in_stack.contains(neighbor.as_str()) {
                // Found a back edge — cycle detected
                return Some(vec![node.to_owned(), neighbor.clone()]);
            }
        }
    }

    in_stack.remove(node);
    None
}

/// Collect variable names bound by an elaborated pattern.
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

// ── Constructor record well-formedness ──────────────────────────────

/// Walk an expression tree and check all `EExpr::CtorRecord` for:
/// - unknown fields (not declared in the constructor)
/// - duplicate fields
/// - missing fields (arity mismatch)
/// Reports errors via `ElabError`.
fn check_ctor_records_in_expr(
    expr: &EExpr,
    variant_fields: &HashMap<String, Vec<(String, Vec<(String, Ty)>)>>,
    errors: &mut Vec<ElabError>,
) {
    match expr {
        EExpr::CtorRecord(ty, qual, ctor_name, fields, span) => {
            // Recurse into field value expressions
            for (_, e) in fields {
                check_ctor_records_in_expr(e, variant_fields, errors);
            }
            // Find the declared fields for this constructor.
            // Type-directed resolution priority:
            // 1. Qualifier (@Enum::Ctor) — most specific
            // 2. Resolved type (Ty::Enum) — set during resolution
            // 3. Global search — fallback for unresolved types
            let mut declared: Option<&[(String, Ty)]> = None;
            let mut enum_name_found: Option<&str> = None;

            // Determine which enum to search
            let target_enum: Option<&str> = if let Some(q) = qual {
                Some(q.as_str())
            } else if let Ty::Enum(en, _) = ty {
                Some(en.as_str())
            } else {
                None
            };

            if let Some(target) = target_enum {
                // Scoped search: only check the target enum
                if let Some(variants) = variant_fields.get(target) {
                    for (vname, vfields) in variants {
                        if vname == ctor_name {
                            declared = Some(vfields);
                            enum_name_found = Some(target);
                            break;
                        }
                    }
                }
            } else {
                // Global search fallback — find all enums with this constructor,
                // then disambiguate by field names to avoid nondeterministic
                // HashMap iteration order.
                let user_field_names: Vec<&str> =
                    fields.iter().map(|(n, _)| n.as_str()).collect();

                // Collect ALL enums that have a constructor with this name
                let mut all_matches: Vec<(&str, &[(String, Ty)])> = Vec::new();
                for (ename, variants) in variant_fields {
                    for (vname, vfields) in variants {
                        if vname == ctor_name {
                            all_matches.push((ename.as_str(), vfields.as_slice()));
                        }
                    }
                }

                if all_matches.len() == 1 {
                    // Unique constructor name — use it (validates unknown fields)
                    declared = Some(all_matches[0].1);
                    enum_name_found = Some(all_matches[0].0);
                } else if all_matches.len() > 1 {
                    // Ambiguous: disambiguate by field names
                    let field_matched: Vec<_> = all_matches
                        .iter()
                        .filter(|(_, vfields)| {
                            let decl_names: Vec<&str> =
                                vfields.iter().map(|(n, _)| n.as_str()).collect();
                            user_field_names.iter().all(|f| decl_names.contains(f))
                        })
                        .collect();
                    if field_matched.len() == 1 {
                        declared = Some(field_matched[0].1);
                        enum_name_found = Some(field_matched[0].0);
                    } else {
                        // Genuinely ambiguous — reject and require qualification
                        let mut enum_names: Vec<&str> =
                            all_matches.iter().map(|(n, _)| *n).collect();
                        enum_names.sort();
                        let mut err = ElabError::new(
                            ErrorKind::AmbiguousRef,
                            format!(
                                "ambiguous constructor '{ctor_name}' — found in enums: {}",
                                enum_names.join(", "),
                            ),
                            ctor_name.clone(),
                        );
                        err.span = *span;
                        err.help = Some(messages::HELP_AMBIGUOUS_CTOR.into());
                        errors.push(err);
                        return;
                    }
                }
            }
            let Some(declared_fields) = declared else {
                // Constructor not found in any known variant_fields — could be
                // a fieldless enum (not in variant_fields map) or genuinely unknown.
                // Skip — the verifier will catch this if verification runs.
                return;
            };
            let enum_name = enum_name_found.unwrap_or("?");
            let decl_names: Vec<&str> = declared_fields.iter().map(|(n, _)| n.as_str()).collect();

            // Check for unknown fields
            for (field_name, _) in fields {
                if !decl_names.contains(&field_name.as_str()) {
                    let mut err = ElabError::new(
                        ErrorKind::TypeMismatch,
                        format!(
                            "unknown field '{field_name}' in constructor '{ctor_name}' \
                             of '{enum_name}' — declared fields: {}",
                            decl_names.join(", ")
                        ),
                        ctor_name.clone(),
                    );
                    err.span = *span;
                    errors.push(err);
                }
            }

            // Check for duplicates
            let mut seen = HashSet::new();
            for (field_name, _) in fields {
                if !seen.insert(field_name.as_str()) {
                    let mut err = ElabError::new(
                        ErrorKind::DuplicateDecl,
                        format!("duplicate field '{field_name}' in constructor '{ctor_name}'"),
                        ctor_name.clone(),
                    );
                    err.span = *span;
                    errors.push(err);
                }
            }

            // Check arity
            let user_names: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
            let missing: Vec<&str> = decl_names
                .iter()
                .filter(|d| !user_names.contains(d))
                .copied()
                .collect();
            if !missing.is_empty() {
                let mut err = ElabError::new(
                    ErrorKind::TypeMismatch,
                    format!(
                        "constructor '{ctor_name}' of '{enum_name}' requires {} \
                         field(s) but got {} — missing: {}",
                        decl_names.len(),
                        fields.len(),
                        missing.join(", ")
                    ),
                    ctor_name.clone(),
                );
                err.span = *span;
                errors.push(err);
            }
        }
        // Recurse into all child expressions
        EExpr::BinOp(_, _, l, r, _)
        | EExpr::Assign(_, l, r, _)
        | EExpr::Seq(_, l, r, _)
        | EExpr::SameStep(_, l, r, _)
        | EExpr::Pipe(_, l, r, _)
        | EExpr::In(_, l, r, _)
        | EExpr::Until(_, l, r, _) => {
            check_ctor_records_in_expr(l, variant_fields, errors);
            check_ctor_records_in_expr(r, variant_fields, errors);
        }
        EExpr::UnOp(_, _, e, _)
        | EExpr::Always(_, e, _)
        | EExpr::Eventually(_, e, _)
        | EExpr::Assert(_, e, _)
        | EExpr::Assume(_, e, _)
        | EExpr::Prime(_, e, _)
        | EExpr::Card(_, e, _)
        | EExpr::Field(_, e, _, _)
        | EExpr::NamedPair(_, _, e, _) => {
            check_ctor_records_in_expr(e, variant_fields, errors);
        }
        EExpr::Call(_, f, args, _) | EExpr::CallR(_, f, _, args, _) => {
            check_ctor_records_in_expr(f, variant_fields, errors);
            for a in args {
                check_ctor_records_in_expr(a, variant_fields, errors);
            }
        }
        EExpr::QualCall(_, _, _, args, _) => {
            for a in args {
                check_ctor_records_in_expr(a, variant_fields, errors);
            }
        }
        EExpr::Quant(_, _, _, _, body, _)
        | EExpr::Lam(_, _, body, _) => {
            check_ctor_records_in_expr(body, variant_fields, errors);
        }
        EExpr::Let(binds, body, _) => {
            for (_, _, e) in binds {
                check_ctor_records_in_expr(e, variant_fields, errors);
            }
            check_ctor_records_in_expr(body, variant_fields, errors);
        }
        EExpr::Match(scrut, arms, _) => {
            check_ctor_records_in_expr(scrut, variant_fields, errors);
            for (_, guard, body) in arms {
                if let Some(g) = guard {
                    check_ctor_records_in_expr(g, variant_fields, errors);
                }
                check_ctor_records_in_expr(body, variant_fields, errors);
            }
        }
        EExpr::Block(items, _) => {
            for e in items {
                check_ctor_records_in_expr(e, variant_fields, errors);
            }
        }
        EExpr::VarDecl(_, _, init, rest, _) => {
            check_ctor_records_in_expr(init, variant_fields, errors);
            check_ctor_records_in_expr(rest, variant_fields, errors);
        }
        EExpr::While(cond, _, body, _) => {
            check_ctor_records_in_expr(cond, variant_fields, errors);
            check_ctor_records_in_expr(body, variant_fields, errors);
        }
        EExpr::IfElse(cond, then_body, else_body, _) => {
            check_ctor_records_in_expr(cond, variant_fields, errors);
            check_ctor_records_in_expr(then_body, variant_fields, errors);
            if let Some(eb) = else_body {
                check_ctor_records_in_expr(eb, variant_fields, errors);
            }
        }
        EExpr::MapUpdate(_, m, k, v, _) => {
            check_ctor_records_in_expr(m, variant_fields, errors);
            check_ctor_records_in_expr(k, variant_fields, errors);
            check_ctor_records_in_expr(v, variant_fields, errors);
        }
        EExpr::Index(_, m, k, _) => {
            check_ctor_records_in_expr(m, variant_fields, errors);
            check_ctor_records_in_expr(k, variant_fields, errors);
        }
        EExpr::SetComp(_, proj, _, _, filter, _) => {
            if let Some(p) = proj {
                check_ctor_records_in_expr(p, variant_fields, errors);
            }
            check_ctor_records_in_expr(filter, variant_fields, errors);
        }
        EExpr::TupleLit(_, elems, _) | EExpr::SetLit(_, elems, _) | EExpr::SeqLit(_, elems, _) => {
            for e in elems {
                check_ctor_records_in_expr(e, variant_fields, errors);
            }
        }
        EExpr::MapLit(_, entries, _) => {
            for (k, v) in entries {
                check_ctor_records_in_expr(k, variant_fields, errors);
                check_ctor_records_in_expr(v, variant_fields, errors);
            }
        }
        // Leaf nodes — no CtorRecord possible
        EExpr::Lit(..)
        | EExpr::Var(..)
        | EExpr::Qual(..)
        | EExpr::Unresolved(..)
        | EExpr::Sorry(_)
        | EExpr::Todo(_) => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::elab::types::{EExpr, Literal, Ty};

    /// Helper: make an unresolved uppercase Var that should trigger the hint.
    fn unresolved_var(name: &str) -> EExpr {
        EExpr::Var(Ty::Unresolved("?".to_string()), name.to_string(), None)
    }

    /// Helper: make a resolved Int literal (should NOT trigger the hint).
    fn int_lit(n: i64) -> EExpr {
        EExpr::Lit(Ty::Builtin(BuiltinTy::Int), Literal::Int(n), None)
    }

    fn collect_hints(expr: &EExpr) -> Vec<ElabError> {
        let mut errors = Vec::new();
        check_unresolved_constructors(expr, "test context", None, &[], &mut errors);
        errors
    }

    #[test]
    fn unresolved_uppercase_var_triggers_hint() {
        let hints = collect_hints(&unresolved_var("Pending"));
        assert_eq!(hints.len(), 1);
        assert!(hints[0].message.contains("Pending"));
        assert!(hints[0].help.as_ref().unwrap().contains("@Pending"));
    }

    #[test]
    fn resolved_var_no_hint() {
        let expr = EExpr::Var(Ty::Builtin(BuiltinTy::Int), "x".to_string(), None);
        let hints = collect_hints(&expr);
        assert!(hints.is_empty());
    }

    #[test]
    fn lowercase_unresolved_no_hint() {
        let expr = EExpr::Var(Ty::Unresolved("?".to_string()), "pending".to_string(), None);
        let hints = collect_hints(&expr);
        assert!(hints.is_empty(), "lowercase names should not trigger hint");
    }

    #[test]
    fn setlit_traversal() {
        let expr = EExpr::SetLit(
            Ty::Unresolved("?".to_string()),
            vec![int_lit(1), unresolved_var("Unknown"), int_lit(3)],
            None,
        );
        let hints = collect_hints(&expr);
        assert_eq!(hints.len(), 1, "should find hint inside SetLit");
        assert!(hints[0].message.contains("Unknown"));
    }

    #[test]
    fn seqlit_traversal() {
        let expr = EExpr::SeqLit(
            Ty::Unresolved("?".to_string()),
            vec![unresolved_var("First"), unresolved_var("Second")],
            None,
        );
        let hints = collect_hints(&expr);
        assert_eq!(hints.len(), 2, "should find hints in all SeqLit elements");
    }

    #[test]
    fn maplit_traversal() {
        let expr = EExpr::MapLit(
            Ty::Unresolved("?".to_string()),
            vec![
                (int_lit(1), unresolved_var("ValA")),
                (unresolved_var("KeyB"), int_lit(2)),
            ],
            None,
        );
        let hints = collect_hints(&expr);
        assert_eq!(
            hints.len(),
            2,
            "should find hints in MapLit keys and values"
        );
    }

    #[test]
    fn nested_binop_traversal() {
        let expr = EExpr::BinOp(
            Ty::Builtin(BuiltinTy::Bool),
            crate::elab::types::BinOp::Eq,
            Box::new(EExpr::Var(
                Ty::Unresolved("?".to_string()),
                "status".to_string(),
                None,
            )),
            Box::new(unresolved_var("Active")),
            None,
        );
        let hints = collect_hints(&expr);
        assert_eq!(hints.len(), 1, "should find hint in binop rhs");
        assert!(hints[0].help.as_ref().unwrap().contains("@Active"));
    }
}

// ── Match exhaustiveness checking ───────────────────────────────────

/// Walk an expression tree and check every match expression for exhaustiveness.
///
/// For each match whose scrutinee has an enum type, verifies that the arms
/// cover all constructors. Wildcards (`_`) and variable patterns cover all
/// remaining constructors. Guarded arms are treated conservatively — a guard
/// does not guarantee coverage (what if the guard is false?).
fn check_match_exhaustiveness(
    expr: &EExpr,
    types: &HashMap<String, Ty>,
    entities: &HashMap<String, EEntity>,
    errors: &mut Vec<ElabError>,
) {
    match expr {
        EExpr::Match(scrut, arms, span) => {
            // Recurse into scrutinee and arm bodies first
            check_match_exhaustiveness(scrut, types, entities, errors);
            for (_, guard, body) in arms {
                if let Some(g) = guard {
                    check_match_exhaustiveness(g, types, entities, errors);
                }
                check_match_exhaustiveness(body, types, entities, errors);
            }

            // Check exhaustiveness for enum scrutinee types.
            // Follow alias chains (type A = B; type B = Enum) to find the
            // underlying enum, using the types map for named aliases.
            // For field access scrutinees (e.g., o.status), resolve the field
            // type from the entity definition when the base has an entity type.
            let scrut_ty = scrut.ty();
            let resolved_field_ty = if matches!(scrut_ty, Ty::Unresolved(_)) {
                resolve_field_type(scrut, types, entities)
            } else {
                None
            };
            let ty_to_check = resolved_field_ty.as_ref().unwrap_or(&scrut_ty);
            let constructors = match resolve_to_enum(ty_to_check, types) {
                Some(ctors) => ctors,
                None => return,
            };

            // Collect covered constructors from unguarded arms.
            // An unguarded wildcard/variable covers everything.
            let mut covered: HashSet<&str> = HashSet::new();
            let mut has_catchall = false;

            for (pat, guard, _) in arms {
                if guard.is_some() {
                    // Guarded arms are conservative — the guard might be false,
                    // so this arm doesn't guarantee coverage.
                    continue;
                }
                if pattern_is_catchall(pat, constructors) {
                    has_catchall = true;
                    break;
                }
                collect_covered_ctors(pat, constructors, &mut covered);
            }

            if has_catchall {
                return; // Wildcard or variable covers all remaining
            }

            let missing: Vec<&str> = constructors
                .iter()
                .filter(|c| !covered.contains(c.as_str()))
                .map(String::as_str)
                .collect();

            if !missing.is_empty() {
                let mut err = ElabError::new(
                    ErrorKind::NonExhaustiveMatch,
                    messages::non_exhaustive_match(&missing),
                    String::new(),
                );
                err.span = *span;
                err.help = Some(messages::HELP_NON_EXHAUSTIVE_MATCH.into());
                errors.push(err);
            }
        }

        // Recurse into all sub-expressions
        EExpr::BinOp(_, _, l, r, _)
        | EExpr::Assign(_, l, r, _)
        | EExpr::Seq(_, l, r, _)
        | EExpr::SameStep(_, l, r, _)
        | EExpr::Pipe(_, l, r, _)
        | EExpr::In(_, l, r, _)
        | EExpr::Until(_, l, r, _) => {
            check_match_exhaustiveness(l, types, entities, errors);
            check_match_exhaustiveness(r, types, entities, errors);
        }
        EExpr::UnOp(_, _, e, _)
        | EExpr::Always(_, e, _)
        | EExpr::Eventually(_, e, _)
        | EExpr::Assert(_, e, _)
        | EExpr::Assume(_, e, _)
        | EExpr::Prime(_, e, _)
        | EExpr::Card(_, e, _)
        | EExpr::Field(_, e, _, _)
        | EExpr::NamedPair(_, _, e, _) => {
            check_match_exhaustiveness(e, types, entities, errors);
        }
        EExpr::Call(_, f, args, _) | EExpr::CallR(_, f, _, args, _) => {
            check_match_exhaustiveness(f, types, entities, errors);
            for a in args {
                check_match_exhaustiveness(a, types, entities, errors);
            }
        }
        EExpr::QualCall(_, _, _, args, _) => {
            for a in args {
                check_match_exhaustiveness(a, types, entities, errors);
            }
        }
        EExpr::Quant(_, _, _, _, body, _) | EExpr::Lam(_, _, body, _) => {
            check_match_exhaustiveness(body, types, entities, errors);
        }
        EExpr::Let(binds, body, _) => {
            for (_, _, e) in binds {
                check_match_exhaustiveness(e, types, entities, errors);
            }
            check_match_exhaustiveness(body, types, entities, errors);
        }
        EExpr::IfElse(cond, then_e, else_e, _) => {
            check_match_exhaustiveness(cond, types, entities, errors);
            check_match_exhaustiveness(then_e, types, entities, errors);
            if let Some(el) = else_e {
                check_match_exhaustiveness(el, types, entities, errors);
            }
        }
        EExpr::Block(items, _) => {
            for e in items {
                check_match_exhaustiveness(e, types, entities, errors);
            }
        }
        EExpr::VarDecl(_, _, init, rest, _) => {
            check_match_exhaustiveness(init, types, entities, errors);
            check_match_exhaustiveness(rest, types, entities, errors);
        }
        EExpr::While(cond, _, body, _) => {
            check_match_exhaustiveness(cond, types, entities, errors);
            check_match_exhaustiveness(body, types, entities, errors);
        }
        EExpr::CtorRecord(_, _, _, args, _) => {
            for (_, e) in args {
                check_match_exhaustiveness(e, types, entities, errors);
            }
        }
        EExpr::MapUpdate(_, m, k, v, _) => {
            check_match_exhaustiveness(m, types, entities, errors);
            check_match_exhaustiveness(k, types, entities, errors);
            check_match_exhaustiveness(v, types, entities, errors);
        }
        EExpr::Index(_, m, k, _) => {
            check_match_exhaustiveness(m, types, entities, errors);
            check_match_exhaustiveness(k, types, entities, errors);
        }
        EExpr::SetComp(_, proj, _, _, filter, _) => {
            if let Some(p) = proj {
                check_match_exhaustiveness(p, types, entities, errors);
            }
            check_match_exhaustiveness(filter, types, entities, errors);
        }
        EExpr::SetLit(_, elems, _) | EExpr::SeqLit(_, elems, _) | EExpr::TupleLit(_, elems, _) => {
            for e in elems {
                check_match_exhaustiveness(e, types, entities, errors);
            }
        }
        EExpr::MapLit(_, entries, _) => {
            for (k, v) in entries {
                check_match_exhaustiveness(k, types, entities, errors);
                check_match_exhaustiveness(v, types, entities, errors);
            }
        }
        // Leaves — no sub-expressions to recurse into
        EExpr::Lit(..)
        | EExpr::Var(..)
        | EExpr::Qual(..)
        | EExpr::Sorry(_)
        | EExpr::Todo(_)
        | EExpr::Unresolved(..) => {}
    }
}

/// Check if a pattern is a catch-all (covers any value regardless of constructor).
/// Wildcards, bare variables (not constructors), and or-patterns where either
/// side is a catch-all all qualify.
fn pattern_is_catchall(pat: &EPattern, constructors: &[String]) -> bool {
    match pat {
        EPattern::Wild => true,
        EPattern::Var(name) => !constructors.iter().any(|c| c == name),
        EPattern::Or(left, right) => {
            pattern_is_catchall(left, constructors)
                || pattern_is_catchall(right, constructors)
        }
        EPattern::Ctor(..) => false,
    }
}

/// Collect constructor names covered by an unguarded pattern.
fn collect_covered_ctors<'a>(
    pat: &'a EPattern,
    constructors: &'a [String],
    covered: &mut HashSet<&'a str>,
) {
    match pat {
        EPattern::Var(name) => {
            // A Var that matches a constructor name covers that constructor
            if let Some(ctor) = constructors.iter().find(|c| c.as_str() == name) {
                covered.insert(ctor);
            }
            // Otherwise it's a variable binding (catch-all) — handled by pattern_is_catchall
        }
        EPattern::Ctor(name, _) => {
            if let Some(ctor) = constructors.iter().find(|c| c.as_str() == name) {
                covered.insert(ctor);
            }
        }
        EPattern::Or(left, right) => {
            collect_covered_ctors(left, constructors, covered);
            collect_covered_ctors(right, constructors, covered);
        }
        EPattern::Wild => {
            // Catch-all — handled by pattern_is_catchall
        }
    }
}

/// Follow alias chains to find the underlying enum constructors.
/// Handles `type A = Enum`, `type A = B` where `B = Enum`, etc.
/// Returns `None` if the type is not an enum (or alias chain to one).
fn resolve_to_enum<'a>(
    ty: &'a Ty,
    types: &'a HashMap<String, Ty>,
) -> Option<&'a Vec<String>> {
    let mut current = ty;
    // Limit iterations to prevent infinite loops on cyclic aliases
    for _ in 0..20 {
        match current {
            Ty::Enum(_, ctors) => return Some(ctors),
            Ty::Alias(_, inner) => {
                current = inner.as_ref();
            }
            Ty::Unresolved(name) | Ty::Entity(name) => {
                // Look up named type in the types map
                match types.get(name.as_str()) {
                    Some(resolved) => {
                        current = resolved;
                    }
                    None => return None,
                }
            }
            _ => return None,
        }
    }
    None
}

/// Resolve the type of a field-access scrutinee from entity definitions.
///
/// When a match scrutinee is `o.status` and `o` has type `Ty::Entity("Order")`,
/// looks up the `status` field on the `Order` entity to recover the field's type.
/// This enables exhaustiveness checking for matches on entity fields in contexts
/// where the field type annotation is unresolved (e.g., scene given variables).
fn resolve_field_type(
    expr: &EExpr,
    types: &HashMap<String, Ty>,
    entities: &HashMap<String, EEntity>,
) -> Option<Ty> {
    if let EExpr::Field(_, base, field_name, _) = expr {
        let base_ty = base.ty();
        // Resolve entity name from the base expression's type
        let entity_name = match &base_ty {
            Ty::Entity(name) => Some(name.as_str()),
            Ty::Unresolved(name) if entities.contains_key(name.as_str()) => {
                Some(name.as_str())
            }
            // Follow aliases/type names that resolve to entities
            _ => {
                let name = base_ty.name();
                if entities.contains_key(name) {
                    Some(name)
                } else {
                    None
                }
            }
        };
        if let Some(ent_name) = entity_name {
            if let Some(entity) = entities.get(ent_name) {
                if let Some(field) = entity.fields.iter().find(|f| f.name == *field_name) {
                    return Some(field.ty.clone());
                }
            }
        }
        // Recursive: resolve nested field access (o.inner.status)
        if matches!(base.as_ref(), EExpr::Field(..)) {
            if let Some(inner_ty) = resolve_field_type(base, types, entities) {
                // inner_ty might be an entity — look up the field on it
                let inner_name = inner_ty.name();
                if let Some(entity) = entities.get(inner_name) {
                    if let Some(field) = entity.fields.iter().find(|f| f.name == *field_name) {
                        return Some(field.ty.clone());
                    }
                }
            }
        }
    }
    None
}
