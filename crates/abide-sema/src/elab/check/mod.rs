//! Pass 3: Type-check expressions and validate well-formedness.
//!
//! Validates: field defaults match types, requires is Bool,
//! primed assignments target known fields, system uses reference known entities.

mod ctors;
mod entity;
mod matches;
mod system;

use ctors::{check_ctor_records_in_expr, walk_event_action_for_ctor_check};
use entity::{check_entity, check_invariant_body_no_liveness};
use matches::check_match_exhaustiveness;
use system::{check_extern, check_system};

use std::collections::{HashMap, HashSet};

use super::env::Env;
use super::error::{ElabError, ErrorKind};
use super::types::{
    BuiltinTy, EContract, EExpr, EFn, EPattern, ESceneWhen, EType, EVariant, ElabResult, Literal,
    Ty, VariantFieldsMap,
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
    all_known_names.extend(env.interfaces.keys().cloned());
    all_known_names.extend(env.externs.keys().cloned());
    all_known_names.extend(env.preds.keys().cloned());
    all_known_names.extend(env.fns.keys().cloned());
    all_known_names.extend(env.consts.keys().cloned());

    for (name, ty) in &env.types {
        let decl_span = env.lookup_decl(name).and_then(|d| d.span);
        errors.extend(check_type(ty, decl_span));
        // Check refinement predicates in type aliases
        if let Ty::Refinement(_, pred) = ty {
            if let Some(pred_ty) = expr_type(pred) {
                if !matches!(pred_ty, Ty::Builtin(BuiltinTy::Bool) | Ty::Error) {
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
    for ext in env.externs.values() {
        errors.extend(check_extern(env, ext));
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
                EContract::Requires(e) | EContract::Ensures(e) | EContract::Invariant(e) => {
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
    // walk system action guards/bodies and query bodies for
    // StructCtor (and CtorRecord) well-formedness.
    for system in env.systems.values() {
        for step in &system.actions {
            for req in &step.requires {
                check_ctor_records_in_expr(req, &env.variant_fields, &mut errors);
            }
            for ea in &step.body {
                walk_event_action_for_ctor_check(ea, &env.variant_fields, &mut errors);
            }
            // walk return expression for ctor checks
            if let Some(ref re) = step.return_expr {
                check_ctor_records_in_expr(re, &env.variant_fields, &mut errors);
            }
        }
        for query in &system.queries {
            check_ctor_records_in_expr(&query.body, &env.variant_fields, &mut errors);
        }
        for inv in &system.invariants {
            check_ctor_records_in_expr(&inv.body, &env.variant_fields, &mut errors);
        }
        for d in &system.derived_fields {
            check_ctor_records_in_expr(&d.body, &env.variant_fields, &mut errors);
        }
    }

    // Check for cyclic pred/prop definitions
    errors.extend(check_pred_prop_cycles(env));

    // Check match expression exhaustiveness and collection literal homogeneity
    for f in env.fns.values() {
        let fn_ctx = format!("fn {}", f.name);
        check_match_exhaustiveness(
            &f.body,
            &env.types,
            &env.entities,
            &env.variant_fields,
            &mut errors,
        );
        check_collection_homogeneity(&f.body, &fn_ctx, &mut errors);
        for c in &f.contracts {
            match c {
                EContract::Requires(e) | EContract::Ensures(e) | EContract::Invariant(e) => {
                    check_match_exhaustiveness(
                        e,
                        &env.types,
                        &env.entities,
                        &env.variant_fields,
                        &mut errors,
                    );
                    check_collection_homogeneity(e, &fn_ctx, &mut errors);
                }
                EContract::Decreases { measures, .. } => {
                    for m in measures {
                        check_match_exhaustiveness(
                            m,
                            &env.types,
                            &env.entities,
                            &env.variant_fields,
                            &mut errors,
                        );
                    }
                }
            }
        }
    }
    for pred in env.preds.values() {
        check_match_exhaustiveness(
            &pred.body,
            &env.types,
            &env.entities,
            &env.variant_fields,
            &mut errors,
        );
        check_collection_homogeneity(&pred.body, &format!("pred {}", pred.name), &mut errors);
    }
    for prop in env.props.values() {
        check_verifier_surface_expr(&prop.body, &format!("prop {}", prop.name), &mut errors);
        check_match_exhaustiveness(
            &prop.body,
            &env.types,
            &env.entities,
            &env.variant_fields,
            &mut errors,
        );
        check_collection_homogeneity(&prop.body, &format!("prop {}", prop.name), &mut errors);
    }
    for verify in &env.verifies {
        for constraint in &verify.initial_constraints {
            check_verifier_surface_expr(
                constraint,
                &format!("verify {} assume constraint", verify.name),
                &mut errors,
            );
            if !is_bool_expr(constraint) {
                let mut err = ElabError::new(
                    ErrorKind::TypeMismatch,
                    "assume constraint must have type bool",
                    verify.name.clone(),
                );
                err.span = expr_span(constraint);
                err.help = Some("bare expressions in assume blocks constrain the initial state and must evaluate to bool".into());
                errors.push(err);
            }
            check_match_exhaustiveness(
                constraint,
                &env.types,
                &env.entities,
                &env.variant_fields,
                &mut errors,
            );
            check_collection_homogeneity(
                constraint,
                &format!("verify {}", verify.name),
                &mut errors,
            );
        }
        for a in &verify.asserts {
            check_verifier_surface_expr(
                a,
                &format!("verify {} assertion", verify.name),
                &mut errors,
            );
            check_match_exhaustiveness(
                a,
                &env.types,
                &env.entities,
                &env.variant_fields,
                &mut errors,
            );
            check_collection_homogeneity(a, &format!("verify {}", verify.name), &mut errors);
        }
    }
    for theorem in &env.theorems {
        for a in &theorem.shows {
            check_verifier_surface_expr(
                a,
                &format!("theorem {} show expression", theorem.name),
                &mut errors,
            );
            check_match_exhaustiveness(
                a,
                &env.types,
                &env.entities,
                &env.variant_fields,
                &mut errors,
            );
            check_collection_homogeneity(a, &format!("theorem {}", theorem.name), &mut errors);
        }
    }
    for lemma in &env.lemmas {
        for a in &lemma.body {
            check_match_exhaustiveness(
                a,
                &env.types,
                &env.entities,
                &env.variant_fields,
                &mut errors,
            );
            check_collection_homogeneity(a, &format!("lemma {}", lemma.name), &mut errors);
        }
    }
    for c in env.consts.values() {
        check_match_exhaustiveness(
            &c.body,
            &env.types,
            &env.entities,
            &env.variant_fields,
            &mut errors,
        );
        check_collection_homogeneity(&c.body, &format!("const {}", c.name), &mut errors);
    }
    for a in &env.axioms {
        check_match_exhaustiveness(
            &a.body,
            &env.types,
            &env.entities,
            &env.variant_fields,
            &mut errors,
        );
        check_collection_homogeneity(&a.body, &format!("axiom {}", a.name), &mut errors);
    }
    for scene in &env.scenes {
        for given in &scene.givens {
            if let Some(cond) = &given.condition {
                check_verifier_surface_expr(
                    cond,
                    &format!("scene {} given condition", scene.name),
                    &mut errors,
                );
                check_match_exhaustiveness(
                    cond,
                    &env.types,
                    &env.entities,
                    &env.variant_fields,
                    &mut errors,
                );
            }
        }
        for constraint in &scene.given_constraints {
            check_verifier_surface_expr(
                constraint,
                &format!("scene {} given constraint", scene.name),
                &mut errors,
            );
        }
        for when in &scene.whens {
            match when {
                ESceneWhen::Action { args, .. } => {
                    for arg in args {
                        check_verifier_surface_expr(
                            arg,
                            &format!("scene {} event argument", scene.name),
                            &mut errors,
                        );
                        check_match_exhaustiveness(
                            arg,
                            &env.types,
                            &env.entities,
                            &env.variant_fields,
                            &mut errors,
                        );
                    }
                }
                ESceneWhen::Assume(e) => {
                    check_verifier_surface_expr_allowing_sequence(
                        e,
                        &format!("scene {} when assumption", scene.name),
                        &mut errors,
                    );
                    check_match_exhaustiveness(
                        e,
                        &env.types,
                        &env.entities,
                        &env.variant_fields,
                        &mut errors,
                    );
                }
            }
        }
        for then_expr in &scene.thens {
            check_verifier_surface_expr(
                then_expr,
                &format!("scene {} then assertion", scene.name),
                &mut errors,
            );
            check_match_exhaustiveness(
                then_expr,
                &env.types,
                &env.entities,
                &env.variant_fields,
                &mut errors,
            );
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
        interfaces: env.interfaces.values().cloned().collect(),
        externs: env.externs.values().cloned().collect(),
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
        under_blocks: env.under_blocks.clone(),
    };

    (result, errors)
}

fn mk_etype(_map_key: &str, ty: &Ty, variant_fields: &VariantFieldsMap) -> EType {
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

// ── Helpers ──────────────────────────────────────────────────────────

/// Check that collection literals have homogeneous element types.
/// Called recursively on all expressions.
fn check_collection_homogeneity(expr: &EExpr, ctx: &str, errors: &mut Vec<ElabError>) {
    match expr {
        EExpr::SetLit(_, elems, _) => {
            let [first, rest @ ..] = elems.as_slice() else {
                return;
            };
            for (offset, e) in rest.iter().enumerate() {
                let i = offset + 1;
                let first_ty = first.ty();
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
        EExpr::SeqLit(_, elems, _) => {
            let [first, rest @ ..] = elems.as_slice() else {
                return;
            };
            for (offset, e) in rest.iter().enumerate() {
                let i = offset + 1;
                let first_ty = first.ty();
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
        EExpr::MapLit(_, entries, _) => {
            let [first, rest @ ..] = entries.as_slice() else {
                return;
            };
            for (offset, (k, v)) in rest.iter().enumerate() {
                let i = offset + 1;
                let first_k_ty = first.0.ty();
                let first_v_ty = first.1.ty();
                let k_ty = k.ty();
                let v_ty = v.ty();
                if !types_compatible(&first_k_ty, &k_ty) {
                    errors.push(ElabError::new(
                        ErrorKind::TypeMismatch,
                        format!(
                            "Map literal key {} has type {}, expected {} (matching first key)",
                            i,
                            k_ty.name(),
                            first_k_ty.name()
                        ),
                        ctx,
                    ));
                }
                if !types_compatible(&first_v_ty, &v_ty) {
                    errors.push(ElabError::new(
                        ErrorKind::TypeMismatch,
                        format!(
                            "Map literal value {} has type {}, expected {} (matching first value)",
                            i,
                            v_ty.name(),
                            first_v_ty.name()
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
        EExpr::Pipe(_, left, right, _) => {
            check_collection_homogeneity(left, ctx, errors);
            check_collection_homogeneity(right, ctx, errors);
        }
        EExpr::Call(_, f, args, span) => {
            if let EExpr::Var(_, name, _) = f.as_ref() {
                if is_relation_operation_name(name) {
                    push_relation_error(
                        errors,
                        ctx,
                        *span,
                        format!("relation operation `{name}` must be called as `Rel::{name}`"),
                    );
                }
            }
            check_collection_homogeneity(f, ctx, errors);
            for a in args {
                check_collection_homogeneity(a, ctx, errors);
            }
        }
        EExpr::QualCall(_, namespace, name, args, span) => {
            check_relation_builtin(namespace, name, args, ctx, *span, errors);
            for a in args {
                check_collection_homogeneity(a, ctx, errors);
            }
        }
        EExpr::SetLit(_, elems, _) | EExpr::SeqLit(_, elems, _) => {
            for e in elems {
                check_collection_homogeneity(e, ctx, errors);
            }
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

/// Check if two types are compatible (same kind, ignoring poison).
pub(super) fn types_compatible(a: &Ty, b: &Ty) -> bool {
    match (a, b) {
        (Ty::Error, _) | (_, Ty::Error) => true,
        (Ty::Builtin(a), Ty::Builtin(b)) => a == b,
        (Ty::Enum(na, _), Ty::Enum(nb, _)) => na == nb,
        (Ty::Set(a), Ty::Set(b)) => types_compatible(a, b),
        (Ty::Seq(a), Ty::Seq(b)) => types_compatible(a, b),
        (Ty::Map(ka, va), Ty::Map(kb, vb)) => types_compatible(ka, kb) && types_compatible(va, vb),
        (Ty::Store(a), Ty::Store(b)) => a == b,
        (Ty::Relation(a), Ty::Relation(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(a, b)| types_compatible(a, b))
        }
        (Ty::Relation(columns), Ty::Set(element)) | (Ty::Set(element), Ty::Relation(columns)) => {
            match element.as_ref() {
                Ty::Tuple(elements) => {
                    columns.len() == elements.len()
                        && columns
                            .iter()
                            .zip(elements.iter())
                            .all(|(a, b)| types_compatible(a, b))
                }
                single => {
                    columns.len() == 1
                        && columns
                            .first()
                            .is_some_and(|column| types_compatible(column, single))
                }
            }
        }
        (Ty::Entity(a), Ty::Entity(b)) => a == b,
        (Ty::Tuple(a), Ty::Tuple(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(a, b)| types_compatible(a, b))
        }
        (Ty::Alias(a, _), Ty::Alias(b, _)) => a == b,
        (Ty::Alias(_, a), b) | (b, Ty::Alias(_, a)) => types_compatible(a, b),
        (Ty::Refinement(a, _), b) | (b, Ty::Refinement(a, _)) => types_compatible(a, b),
        (Ty::Entity(a), Ty::Named(b)) | (Ty::Named(a), Ty::Entity(b)) => a == b,
        _ => false,
    }
}

fn relation_columns(ty: &Ty) -> Option<Vec<Ty>> {
    match ty {
        Ty::Relation(columns) => Some(columns.clone()),
        Ty::Set(element) => match element.as_ref() {
            Ty::Tuple(columns) => Some(columns.clone()),
            column => Some(vec![column.clone()]),
        },
        _ => None,
    }
}

fn relation_arg_columns(args: &[EExpr], index: usize) -> Option<Vec<Ty>> {
    args.get(index).and_then(|arg| relation_columns(&arg.ty()))
}

fn push_relation_error(
    errors: &mut Vec<ElabError>,
    ctx: &str,
    span: Option<crate::span::Span>,
    message: impl Into<String>,
) {
    let mut err = ElabError::new(ErrorKind::TypeMismatch, message.into(), ctx.to_owned());
    err.span = span;
    errors.push(err);
}

fn is_relation_operation_name(name: &str) -> bool {
    matches!(
        name,
        "join" | "transpose" | "closure" | "reach" | "product" | "project" | "field"
    )
}

fn check_relation_builtin(
    namespace: &str,
    name: &str,
    args: &[EExpr],
    ctx: &str,
    span: Option<crate::span::Span>,
    errors: &mut Vec<ElabError>,
) {
    if namespace != "Rel" {
        return;
    }
    match name {
        "join" => {
            let Some(left) = relation_arg_columns(args, 0) else {
                push_relation_error(
                    errors,
                    ctx,
                    span,
                    "Rel::join requires a relation as its first argument",
                );
                return;
            };
            let Some(right) = relation_arg_columns(args, 1) else {
                push_relation_error(
                    errors,
                    ctx,
                    span,
                    "Rel::join requires a relation as its second argument",
                );
                return;
            };
            let Some(left_join) = left.last() else {
                return;
            };
            let Some(right_join) = right.first() else {
                return;
            };
            if !types_compatible(left_join, right_join) {
                push_relation_error(
                    errors,
                    ctx,
                    span,
                    format!(
                        "Rel::join requires matching join columns, got {} and {}",
                        left_join.name(),
                        right_join.name()
                    ),
                );
            }
        }
        "product" => {
            if relation_arg_columns(args, 0).is_none() {
                push_relation_error(
                    errors,
                    ctx,
                    span,
                    "Rel::product requires a relation as its first argument",
                );
            }
            if relation_arg_columns(args, 1).is_none() {
                push_relation_error(
                    errors,
                    ctx,
                    span,
                    "Rel::product requires a relation as its second argument",
                );
            }
        }
        "project" => {
            let Some(columns) = relation_arg_columns(args, 0) else {
                push_relation_error(
                    errors,
                    ctx,
                    span,
                    "Rel::project requires a relation as its first argument",
                );
                return;
            };
            if args.len() < 2 {
                push_relation_error(
                    errors,
                    ctx,
                    span,
                    "Rel::project requires at least one column index",
                );
            }
            for arg in &args[1..] {
                match arg {
                    EExpr::Lit(_, Literal::Int(value), _) if *value >= 0 => {
                        if *value as usize >= columns.len() {
                            push_relation_error(
                                errors,
                                ctx,
                                span,
                                format!(
                                    "Rel::project column {value} is out of bounds for arity {}",
                                    columns.len()
                                ),
                            );
                        }
                    }
                    _ => push_relation_error(
                        errors,
                        ctx,
                        span,
                        "Rel::project column indexes must be non-negative integer literals",
                    ),
                }
            }
        }
        "transpose" if !matches!(relation_arg_columns(args, 0).as_deref(), Some([_, _])) => {
            push_relation_error(
                errors,
                ctx,
                span,
                "Rel::transpose requires a binary relation",
            );
        }
        "transpose" => {}
        "closure" | "reach" => {
            let Some(columns) = relation_arg_columns(args, 0) else {
                push_relation_error(
                    errors,
                    ctx,
                    span,
                    format!("Rel::{name} requires a homogeneous binary relation"),
                );
                return;
            };
            let [left, right] = columns.as_slice() else {
                push_relation_error(
                    errors,
                    ctx,
                    span,
                    format!("Rel::{name} requires a homogeneous binary relation"),
                );
                return;
            };
            if !types_compatible(left, right) {
                push_relation_error(
                    errors,
                    ctx,
                    span,
                    format!("Rel::{name} requires a homogeneous binary relation"),
                );
            }
        }
        "field" => {
            if args.len() != 2 {
                push_relation_error(
                    errors,
                    ctx,
                    span,
                    "Rel::field requires a store and an Entity::field selector",
                );
                return;
            }
            let store_entity = match args.first().map(EExpr::ty) {
                Some(Ty::Store(entity)) => entity,
                Some(Ty::Error) => return,
                _ => {
                    push_relation_error(
                        errors,
                        ctx,
                        span,
                        "Rel::field requires a store as its first argument",
                    );
                    return;
                }
            };
            let Some(EExpr::Qual(_, owner, field, _)) = args.get(1) else {
                push_relation_error(
                    errors,
                    ctx,
                    span,
                    "Rel::field requires an Entity::field selector as its second argument",
                );
                return;
            };
            let owner = owner.rsplit("::").next().unwrap_or(owner);
            if owner != store_entity {
                push_relation_error(
                    errors,
                    ctx,
                    span,
                    format!(
                        "Rel::field store entity `{store_entity}` does not match field owner `{owner}`"
                    ),
                );
            }
            if field.is_empty() {
                push_relation_error(
                    errors,
                    ctx,
                    span,
                    "Rel::field requires a non-empty field selector",
                );
            }
        }
        _ => {}
    }
}

fn unwrap_real_target(ty: &Ty) -> Option<BuiltinTy> {
    match ty {
        Ty::Builtin(bt) => Some(*bt),
        Ty::Alias(_, inner) | Ty::Refinement(inner, _) => unwrap_real_target(inner),
        _ => None,
    }
}

pub(super) fn expr_compatible_with_ty(expr: &EExpr, expected: &Ty) -> bool {
    if types_compatible(&expr.ty(), expected) {
        return true;
    }

    matches!(
        (expr, unwrap_real_target(expected)),
        (
            EExpr::Lit(Ty::Builtin(BuiltinTy::Int), Literal::Int(_), _),
            Some(BuiltinTy::Real)
        )
    )
}

fn check_unresolved_constructors(
    expr: &EExpr,
    ctx: &str,
    span: Option<crate::span::Span>,
    known_names: &[String],
    errors: &mut Vec<ElabError>,
) {
    match expr {
        EExpr::Var(Ty::Error, name, _)
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
        | EExpr::Historically(_, e, _)
        | EExpr::Once(_, e, _)
        | EExpr::Previously(_, e, _)
        | EExpr::Assert(_, e, _)
        | EExpr::Assume(_, e, _)
        | EExpr::Prime(_, e, _)
        | EExpr::Card(_, e, _)
        | EExpr::Field(_, e, _, _)
        | EExpr::NamedPair(_, _, e, _) => {
            check_unresolved_constructors(e, ctx, span, known_names, errors);
        }
        EExpr::Until(_, l, r, _) | EExpr::Since(_, l, r, _) => {
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
        EExpr::Choose(_, _, _, predicate, _) => {
            if let Some(predicate) = predicate {
                check_unresolved_constructors(predicate, ctx, span, known_names, errors);
            }
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
        EExpr::SetComp(_, proj, _, _, source, filter, _) => {
            if let Some(p) = proj {
                check_unresolved_constructors(p, ctx, span, known_names, errors);
            }
            if let Some(source) = source {
                check_unresolved_constructors(source, ctx, span, known_names, errors);
            }
            check_unresolved_constructors(filter, ctx, span, known_names, errors);
        }
        EExpr::RelComp(_, projection, bindings, filter, _) => {
            check_unresolved_constructors(projection, ctx, span, known_names, errors);
            for binding in bindings {
                if let Some(source) = &binding.source {
                    check_unresolved_constructors(source, ctx, span, known_names, errors);
                }
            }
            check_unresolved_constructors(filter, ctx, span, known_names, errors);
        }
        EExpr::MapLit(_, entries, _) => {
            for (k, v) in entries {
                check_unresolved_constructors(k, ctx, span, known_names, errors);
                check_unresolved_constructors(v, ctx, span, known_names, errors);
            }
        }
        EExpr::IfElse(cond, then_body, else_body, _) => {
            check_unresolved_constructors(cond, ctx, span, known_names, errors);
            check_unresolved_constructors(then_body, ctx, span, known_names, errors);
            if let Some(else_body) = else_body {
                check_unresolved_constructors(else_body, ctx, span, known_names, errors);
            }
        }
        EExpr::Block(items, _) => {
            for item in items {
                check_unresolved_constructors(item, ctx, span, known_names, errors);
            }
        }
        EExpr::VarDecl(_, _, init, rest, _) => {
            check_unresolved_constructors(init, ctx, span, known_names, errors);
            check_unresolved_constructors(rest, ctx, span, known_names, errors);
        }
        EExpr::While(cond, contracts, body, _) => {
            check_unresolved_constructors(cond, ctx, span, known_names, errors);
            for contract in contracts {
                match contract {
                    EContract::Requires(expr)
                    | EContract::Ensures(expr)
                    | EContract::Invariant(expr) => {
                        check_unresolved_constructors(expr, ctx, span, known_names, errors);
                    }
                    EContract::Decreases { measures, .. } => {
                        for measure in measures {
                            check_unresolved_constructors(measure, ctx, span, known_names, errors);
                        }
                    }
                }
            }
            check_unresolved_constructors(body, ctx, span, known_names, errors);
        }
        EExpr::Aggregate(_, _, _, _, body, in_filter, _) => {
            check_unresolved_constructors(body, ctx, span, known_names, errors);
            if let Some(in_filter) = in_filter {
                check_unresolved_constructors(in_filter, ctx, span, known_names, errors);
            }
        }
        EExpr::Saw(_, _, _, args, _) => {
            for arg in args.iter().flatten() {
                check_unresolved_constructors(arg, ctx, span, known_names, errors);
            }
        }
        EExpr::StructCtor(_, _, fields, _) => {
            for (_, e) in fields {
                check_unresolved_constructors(e, ctx, span, known_names, errors);
            }
        }
        EExpr::Lit(_, _, _)
        | EExpr::Var(_, _, _)
        | EExpr::Qual(_, _, _, _)
        | EExpr::Unresolved(_, _)
        | EExpr::Sorry(_)
        | EExpr::Todo(_) => {}
    }
}

fn is_bool_expr(e: &EExpr) -> bool {
    matches!(e.ty(), Ty::Builtin(BuiltinTy::Bool) | Ty::Error)
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
/// - requires/ensures must be bool
/// - decreases measures must be int
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
                            "invariant clause must have type bool".to_owned(),
                            f.name.clone(),
                        );
                        err.span = expr_span(e);
                        err.help = Some("invariant clauses must evaluate to bool".into());
                        errors.push(err);
                    }
                }
            }
        }
    }
    errors
}

/// Check that refinement predicates on fn parameters are bool.
fn check_refinement_predicates(f: &EFn) -> Vec<ElabError> {
    let mut errors = Vec::new();
    for (param_name, param_ty) in &f.params {
        if let Ty::Refinement(_, pred) = param_ty {
            if let Some(ty) = expr_type(pred) {
                if !matches!(ty, Ty::Builtin(BuiltinTy::Bool) | Ty::Error) {
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
        | EExpr::CallR(_, _, _, _, sp)
        | EExpr::Qual(_, _, _, sp)
        | EExpr::QualCall(_, _, _, _, sp)
        | EExpr::Field(_, _, _, sp)
        | EExpr::Prime(_, _, sp)
        | EExpr::Quant(_, _, _, _, _, sp)
        | EExpr::Always(_, _, sp)
        | EExpr::Eventually(_, _, sp)
        | EExpr::Until(_, _, _, sp)
        | EExpr::Historically(_, _, sp)
        | EExpr::Once(_, _, sp)
        | EExpr::Previously(_, _, sp)
        | EExpr::Since(_, _, _, sp)
        | EExpr::Assert(_, _, sp)
        | EExpr::Assume(_, _, sp)
        | EExpr::Assign(_, _, _, sp)
        | EExpr::NamedPair(_, _, _, sp)
        | EExpr::Seq(_, _, _, sp)
        | EExpr::SameStep(_, _, _, sp)
        | EExpr::Let(_, _, sp)
        | EExpr::Lam(_, _, _, sp)
        | EExpr::Unresolved(_, sp)
        | EExpr::TupleLit(_, _, sp)
        | EExpr::In(_, _, _, sp)
        | EExpr::Card(_, _, sp)
        | EExpr::Pipe(_, _, _, sp)
        | EExpr::Match(_, _, sp)
        | EExpr::Choose(_, _, _, _, sp)
        | EExpr::MapUpdate(_, _, _, _, sp)
        | EExpr::Index(_, _, _, sp)
        | EExpr::SetComp(_, _, _, _, _, _, sp)
        | EExpr::RelComp(_, _, _, _, sp)
        | EExpr::SetLit(_, _, sp)
        | EExpr::SeqLit(_, _, sp)
        | EExpr::MapLit(_, _, sp)
        | EExpr::Sorry(sp)
        | EExpr::Todo(sp)
        | EExpr::Block(_, sp)
        | EExpr::VarDecl(_, _, _, _, sp)
        | EExpr::While(_, _, _, sp)
        | EExpr::IfElse(_, _, _, sp)
        | EExpr::Aggregate(_, _, _, _, _, _, sp)
        | EExpr::Saw(_, _, _, _, sp)
        | EExpr::CtorRecord(_, _, _, _, sp)
        | EExpr::StructCtor(_, _, _, sp) => *sp,
    }
}

fn check_verifier_surface_expr(expr: &EExpr, ctx: &str, errors: &mut Vec<ElabError>) {
    if let Some(span) = find_sequence_composition_span(expr) {
        errors.push(
            ElabError::with_span(
                ErrorKind::TypeMismatch,
                "`->` is sequence composition, not implication",
                ctx,
                span,
            )
            .with_help("use `implies` for logical implication in boolean/property expressions"),
        );
    }
    if let Some(kind) = find_unsupported_verifier_expr(expr) {
        let mut err = ElabError::new(
            ErrorKind::InvalidScope,
            format!(
                "{}: `{kind}` is not allowed in {ctx}",
                messages::VERIFIER_EXPR_NOT_ALLOWED
            ),
            ctx,
        )
        .with_help(messages::HINT_VERIFIER_EXPR_NOT_ALLOWED);
        err.span = expr_span(expr);
        errors.push(err);
    }
}

fn check_verifier_surface_expr_allowing_sequence(
    expr: &EExpr,
    ctx: &str,
    errors: &mut Vec<ElabError>,
) {
    if let Some(kind) = find_unsupported_verifier_expr(expr) {
        let mut err = ElabError::new(
            ErrorKind::InvalidScope,
            format!(
                "{}: `{kind}` is not allowed in {ctx}",
                messages::VERIFIER_EXPR_NOT_ALLOWED
            ),
            ctx,
        )
        .with_help(messages::HINT_VERIFIER_EXPR_NOT_ALLOWED);
        err.span = expr_span(expr);
        errors.push(err);
    }
}

fn find_sequence_composition_span(expr: &EExpr) -> Option<crate::span::Span> {
    match expr {
        EExpr::Seq(_, _, _, span) => *span,
        EExpr::Lit(_, _, _)
        | EExpr::Var(_, _, _)
        | EExpr::Qual(_, _, _, _)
        | EExpr::Unresolved(_, _)
        | EExpr::Sorry(_)
        | EExpr::Todo(_) => None,
        EExpr::Field(_, expr, _, _)
        | EExpr::Prime(_, expr, _)
        | EExpr::UnOp(_, _, expr, _)
        | EExpr::Always(_, expr, _)
        | EExpr::Eventually(_, expr, _)
        | EExpr::Historically(_, expr, _)
        | EExpr::Once(_, expr, _)
        | EExpr::Previously(_, expr, _)
        | EExpr::Card(_, expr, _)
        | EExpr::Assert(_, expr, _)
        | EExpr::Assume(_, expr, _)
        | EExpr::NamedPair(_, _, expr, _) => find_sequence_composition_span(expr),
        EExpr::BinOp(_, _, left, right, _)
        | EExpr::Until(_, left, right, _)
        | EExpr::Since(_, left, right, _)
        | EExpr::Assign(_, left, right, _)
        | EExpr::SameStep(_, left, right, _)
        | EExpr::In(_, left, right, _)
        | EExpr::Pipe(_, left, right, _) => {
            find_sequence_composition_span(left).or_else(|| find_sequence_composition_span(right))
        }
        EExpr::Call(_, func, args, _) => find_sequence_composition_span(func)
            .or_else(|| args.iter().find_map(find_sequence_composition_span)),
        EExpr::CallR(_, func, args, rets, _) => find_sequence_composition_span(func)
            .or_else(|| args.iter().find_map(find_sequence_composition_span))
            .or_else(|| rets.iter().find_map(find_sequence_composition_span)),
        EExpr::Quant(_, _, _, _, body, _) => find_sequence_composition_span(body),
        EExpr::Let(bindings, body, _) => bindings
            .iter()
            .find_map(|(_, _, binding_expr)| find_sequence_composition_span(binding_expr))
            .or_else(|| find_sequence_composition_span(body)),
        EExpr::TupleLit(_, exprs, _) | EExpr::SetLit(_, exprs, _) | EExpr::SeqLit(_, exprs, _) => {
            exprs.iter().find_map(find_sequence_composition_span)
        }
        EExpr::Match(scrutinee, arms, _) => {
            find_sequence_composition_span(scrutinee).or_else(|| {
                arms.iter().find_map(|(_, guard, body)| {
                    guard
                        .as_ref()
                        .and_then(find_sequence_composition_span)
                        .or_else(|| find_sequence_composition_span(body))
                })
            })
        }
        EExpr::Choose(_, _, _, predicate, _) => predicate
            .as_deref()
            .and_then(find_sequence_composition_span),
        EExpr::MapUpdate(_, map, key, value, _) => find_sequence_composition_span(map)
            .or_else(|| find_sequence_composition_span(key))
            .or_else(|| find_sequence_composition_span(value)),
        EExpr::Index(_, map, key, _) => {
            find_sequence_composition_span(map).or_else(|| find_sequence_composition_span(key))
        }
        EExpr::SetComp(_, source, _, _, filter, projection, _) => source
            .as_deref()
            .and_then(find_sequence_composition_span)
            .or_else(|| filter.as_deref().and_then(find_sequence_composition_span))
            .or_else(|| find_sequence_composition_span(projection)),
        EExpr::RelComp(_, projection, bindings, filter, _) => {
            find_sequence_composition_span(projection)
                .or_else(|| {
                    bindings
                        .iter()
                        .filter_map(|binding| binding.source.as_deref())
                        .find_map(find_sequence_composition_span)
                })
                .or_else(|| find_sequence_composition_span(filter))
        }
        EExpr::MapLit(_, entries, _) => entries.iter().find_map(|(key, value)| {
            find_sequence_composition_span(key).or_else(|| find_sequence_composition_span(value))
        }),
        EExpr::QualCall(_, _, _, args, _) => args.iter().find_map(find_sequence_composition_span),
        EExpr::Block(expressions, _) => expressions.iter().find_map(find_sequence_composition_span),
        EExpr::VarDecl(_, _, init, rest, _) => {
            find_sequence_composition_span(init).or_else(|| find_sequence_composition_span(rest))
        }
        EExpr::While(cond, contracts, body, _) => find_sequence_composition_span(cond)
            .or_else(|| {
                contracts
                    .iter()
                    .find_map(find_sequence_composition_span_in_contract)
            })
            .or_else(|| find_sequence_composition_span(body)),
        EExpr::IfElse(cond, then_body, else_body, _) => find_sequence_composition_span(cond)
            .or_else(|| find_sequence_composition_span(then_body))
            .or_else(|| {
                else_body
                    .as_ref()
                    .and_then(|expr| find_sequence_composition_span(expr))
            }),
        EExpr::Aggregate(_, _, _, _, body, in_filter, _) => find_sequence_composition_span(body)
            .or_else(|| {
                in_filter
                    .as_ref()
                    .and_then(|expr| find_sequence_composition_span(expr))
            }),
        EExpr::Saw(_, _, _, args, _) => args
            .iter()
            .filter_map(|arg| arg.as_ref())
            .find_map(|expr| find_sequence_composition_span(expr)),
        EExpr::CtorRecord(_, _, _, fields, _) | EExpr::StructCtor(_, _, fields, _) => fields
            .iter()
            .find_map(|(_, value)| find_sequence_composition_span(value)),
        EExpr::Lam(_, _, body, _) => find_sequence_composition_span(body),
    }
}

fn find_sequence_composition_span_in_contract(contract: &EContract) -> Option<crate::span::Span> {
    match contract {
        EContract::Requires(expr) | EContract::Ensures(expr) | EContract::Invariant(expr) => {
            find_sequence_composition_span(expr)
        }
        EContract::Decreases { measures, .. } => {
            measures.iter().find_map(find_sequence_composition_span)
        }
    }
}

fn find_unsupported_verifier_expr(expr: &EExpr) -> Option<&'static str> {
    match expr {
        EExpr::Lam(_, _, _, _) => Some("lambda"),
        EExpr::Choose(_, _, _, predicate, _) => predicate
            .as_deref()
            .and_then(find_unsupported_verifier_expr),
        EExpr::Block(_, _) => Some("block"),
        EExpr::VarDecl(_, _, _, _, _) => Some("var declaration"),
        EExpr::While(_, _, _, _) => Some("while loop"),
        EExpr::Lit(_, _, _)
        | EExpr::Var(_, _, _)
        | EExpr::Qual(_, _, _, _)
        | EExpr::Unresolved(_, _)
        | EExpr::Sorry(_)
        | EExpr::Todo(_) => None,
        EExpr::Field(_, expr, _, _)
        | EExpr::Prime(_, expr, _)
        | EExpr::UnOp(_, _, expr, _)
        | EExpr::Always(_, expr, _)
        | EExpr::Eventually(_, expr, _)
        | EExpr::Historically(_, expr, _)
        | EExpr::Once(_, expr, _)
        | EExpr::Previously(_, expr, _)
        | EExpr::Card(_, expr, _)
        | EExpr::Assert(_, expr, _)
        | EExpr::Assume(_, expr, _) => find_unsupported_verifier_expr(expr),
        EExpr::BinOp(_, _, left, right, _)
        | EExpr::Until(_, left, right, _)
        | EExpr::Since(_, left, right, _)
        | EExpr::Assign(_, left, right, _)
        | EExpr::Seq(_, left, right, _)
        | EExpr::SameStep(_, left, right, _)
        | EExpr::In(_, left, right, _)
        | EExpr::Pipe(_, left, right, _) => {
            find_unsupported_verifier_expr(left).or_else(|| find_unsupported_verifier_expr(right))
        }
        EExpr::Call(_, func, args, _) => find_unsupported_verifier_expr(func)
            .or_else(|| args.iter().find_map(find_unsupported_verifier_expr)),
        EExpr::CallR(_, func, args, rets, _) => find_unsupported_verifier_expr(func)
            .or_else(|| args.iter().find_map(find_unsupported_verifier_expr))
            .or_else(|| rets.iter().find_map(find_unsupported_verifier_expr)),
        EExpr::Quant(_, _, _, _, body, _) => find_unsupported_verifier_expr(body),
        EExpr::NamedPair(_, _, expr, _) => find_unsupported_verifier_expr(expr),
        EExpr::Let(bindings, body, _) => bindings
            .iter()
            .find_map(|(_, _, binding_expr)| find_unsupported_verifier_expr(binding_expr))
            .or_else(|| find_unsupported_verifier_expr(body)),
        EExpr::TupleLit(_, exprs, _) | EExpr::SetLit(_, exprs, _) | EExpr::SeqLit(_, exprs, _) => {
            exprs.iter().find_map(find_unsupported_verifier_expr)
        }
        EExpr::Match(scrutinee, arms, _) => {
            find_unsupported_verifier_expr(scrutinee).or_else(|| {
                arms.iter().find_map(|(_, guard, body)| {
                    guard
                        .as_ref()
                        .and_then(find_unsupported_verifier_expr)
                        .or_else(|| find_unsupported_verifier_expr(body))
                })
            })
        }
        EExpr::MapUpdate(_, map, key, value, _) => find_unsupported_verifier_expr(map)
            .or_else(|| find_unsupported_verifier_expr(key))
            .or_else(|| find_unsupported_verifier_expr(value)),
        EExpr::Index(_, map, key, _) => {
            find_unsupported_verifier_expr(map).or_else(|| find_unsupported_verifier_expr(key))
        }
        EExpr::SetComp(_, projection, _, _, source, filter, _) => projection
            .as_ref()
            .and_then(|expr| find_unsupported_verifier_expr(expr))
            .or_else(|| source.as_deref().and_then(find_unsupported_verifier_expr))
            .or_else(|| find_unsupported_verifier_expr(filter)),
        EExpr::RelComp(_, projection, bindings, filter, _) => {
            find_unsupported_verifier_expr(projection)
                .or_else(|| {
                    bindings
                        .iter()
                        .filter_map(|binding| binding.source.as_deref())
                        .find_map(find_unsupported_verifier_expr)
                })
                .or_else(|| find_unsupported_verifier_expr(filter))
        }
        EExpr::MapLit(_, entries, _) => entries.iter().find_map(|(key, value)| {
            find_unsupported_verifier_expr(key).or_else(|| find_unsupported_verifier_expr(value))
        }),
        EExpr::QualCall(_, _, _, args, _) => args.iter().find_map(find_unsupported_verifier_expr),
        EExpr::IfElse(cond, then_body, else_body, _) => find_unsupported_verifier_expr(cond)
            .or_else(|| find_unsupported_verifier_expr(then_body))
            .or_else(|| {
                else_body
                    .as_ref()
                    .and_then(|expr| find_unsupported_verifier_expr(expr))
            }),
        EExpr::Aggregate(_, _, _, _, body, in_filter, _) => find_unsupported_verifier_expr(body)
            .or_else(|| {
                in_filter
                    .as_ref()
                    .and_then(|expr| find_unsupported_verifier_expr(expr))
            }),
        EExpr::Saw(_, _, _, args, _) => args
            .iter()
            .filter_map(|arg| arg.as_ref())
            .find_map(|expr| find_unsupported_verifier_expr(expr)),
        EExpr::CtorRecord(_, _, _, fields, _) | EExpr::StructCtor(_, _, fields, _) => fields
            .iter()
            .find_map(|(_, value)| find_unsupported_verifier_expr(value)),
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
                let all_fns = cycle_names.iter().all(|n| env.fns.contains_key(*n));
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
#[allow(clippy::match_same_arms)]
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
        EExpr::Choose(_, binder, _, predicate, _) => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(binder.clone());
            if let Some(pred) = predicate {
                collect_name_refs(pred, known_names, &inner_bound, refs);
            }
        }
        EExpr::Always(_, e, _) => collect_name_refs(e, known_names, bound, refs),
        EExpr::Eventually(_, e, _) => collect_name_refs(e, known_names, bound, refs),
        EExpr::Until(_, l, r, _) => {
            collect_name_refs(l, known_names, bound, refs);
            collect_name_refs(r, known_names, bound, refs);
        }
        EExpr::Historically(_, e, _) => collect_name_refs(e, known_names, bound, refs),
        EExpr::Once(_, e, _) => collect_name_refs(e, known_names, bound, refs),
        EExpr::Previously(_, e, _) => collect_name_refs(e, known_names, bound, refs),
        EExpr::Since(_, l, r, _) => {
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
        EExpr::SetComp(_, proj, binder, _, source, filter, _) => {
            let mut inner_bound = bound.clone();
            for name in binder.bound_names() {
                inner_bound.insert(name.to_owned());
            }
            if let Some(source) = source {
                collect_name_refs(source, known_names, bound, refs);
            }
            if let Some(p) = proj {
                collect_name_refs(p, known_names, &inner_bound, refs);
            }
            collect_name_refs(filter, known_names, &inner_bound, refs);
        }
        EExpr::RelComp(_, projection, bindings, filter, _) => {
            let mut inner_bound = bound.clone();
            for binding in bindings {
                if let Some(source) = &binding.source {
                    collect_name_refs(source, known_names, bound, refs);
                }
                inner_bound.insert(binding.var.clone());
            }
            collect_name_refs(projection, known_names, &inner_bound, refs);
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
        EExpr::CtorRecord(_, _, _, fields, _) | EExpr::StructCtor(_, _, fields, _) => {
            for (_, e) in fields {
                collect_name_refs(e, known_names, bound, refs);
            }
        }
        EExpr::Saw(_, _, _, args, _) => {
            for e in args.iter().flatten() {
                collect_name_refs(e, known_names, bound, refs);
            }
        }
        EExpr::Aggregate(_, _, var, _, body, in_filter, _) => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.clone());
            collect_name_refs(body, known_names, &inner_bound, refs);
            if let Some(f) = in_filter {
                collect_name_refs(f, known_names, &inner_bound, refs);
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::elab::types::{EExpr, EPred, EProp, Literal, Ty};

    /// Helper: make an unknown uppercase Var that should trigger the hint.
    fn unresolved_var(name: &str) -> EExpr {
        EExpr::Var(Ty::Error, name.to_string(), None)
    }

    /// Helper: make a resolved Int literal (should NOT trigger the hint).
    fn int_lit(n: i64) -> EExpr {
        EExpr::Lit(Ty::Builtin(BuiltinTy::Int), Literal::Int(n), None)
    }

    fn bool_lit(value: bool) -> EExpr {
        EExpr::Lit(Ty::Builtin(BuiltinTy::Bool), Literal::Bool(value), None)
    }

    fn collect_hints(expr: &EExpr) -> Vec<ElabError> {
        let mut errors = Vec::new();
        check_unresolved_constructors(expr, "test context", None, &[], &mut errors);
        errors
    }

    fn collect_homogeneity_errors(expr: &EExpr) -> Vec<ElabError> {
        let mut errors = Vec::new();
        check_collection_homogeneity(expr, "test collection", &mut errors);
        errors
    }

    fn fn_decl(contracts: Vec<EContract>, params: Vec<(String, Ty)>) -> EFn {
        EFn {
            name: "f".to_string(),
            params,
            ret_ty: Ty::Builtin(BuiltinTy::Int),
            contracts,
            body: int_lit(1),
            span: Some(crate::span::Span { start: 1, end: 2 }),
            file: Some("test.ab".to_string()),
        }
    }

    fn pred_decl(name: &str, body: EExpr) -> EPred {
        EPred {
            name: name.to_string(),
            params: vec![],
            body,
            span: None,
            file: None,
        }
    }

    fn prop_decl(name: &str, body: EExpr) -> EProp {
        EProp {
            name: name.to_string(),
            target: None,
            body,
            span: None,
            file: None,
        }
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
        let expr = EExpr::Var(Ty::Error, "pending".to_string(), None);
        let hints = collect_hints(&expr);
        assert!(hints.is_empty(), "lowercase names should not trigger hint");
    }

    #[test]
    fn setlit_traversal() {
        let expr = EExpr::SetLit(
            Ty::Error,
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
            Ty::Error,
            vec![unresolved_var("First"), unresolved_var("Second")],
            None,
        );
        let hints = collect_hints(&expr);
        assert_eq!(hints.len(), 2, "should find hints in all SeqLit elements");
    }

    #[test]
    fn maplit_traversal() {
        let expr = EExpr::MapLit(
            Ty::Error,
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
            Box::new(EExpr::Var(Ty::Error, "status".to_string(), None)),
            Box::new(unresolved_var("Active")),
            None,
        );
        let hints = collect_hints(&expr);
        assert_eq!(hints.len(), 1, "should find hint in binop rhs");
        assert!(hints[0].help.as_ref().unwrap().contains("@Active"));
    }

    #[test]
    fn unresolved_constructor_walker_covers_imperative_and_composite_variants() {
        let expr = EExpr::Block(
            vec![
                EExpr::IfElse(
                    Box::new(EExpr::Var(
                        Ty::Builtin(BuiltinTy::Bool),
                        "ok".to_string(),
                        None,
                    )),
                    Box::new(unresolved_var("ThenState")),
                    Some(Box::new(unresolved_var("ElseState"))),
                    None,
                ),
                EExpr::While(
                    Box::new(EExpr::Var(
                        Ty::Builtin(BuiltinTy::Bool),
                        "keep".to_string(),
                        None,
                    )),
                    vec![
                        EContract::Invariant(unresolved_var("InvariantState")),
                        EContract::Decreases {
                            measures: vec![unresolved_var("MeasureState")],
                            star: false,
                        },
                    ],
                    Box::new(EExpr::StructCtor(
                        Ty::Error,
                        "Record".to_string(),
                        vec![("field".to_string(), unresolved_var("FieldState"))],
                        None,
                    )),
                    None,
                ),
                EExpr::Aggregate(
                    Ty::Builtin(BuiltinTy::Int),
                    crate::ast::AggKind::Sum,
                    "x".to_string(),
                    Ty::Builtin(BuiltinTy::Int),
                    Box::new(unresolved_var("AggregateState")),
                    Some(Box::new(unresolved_var("FilterState"))),
                    None,
                ),
                EExpr::Saw(
                    Ty::Builtin(BuiltinTy::Bool),
                    "Ext".to_string(),
                    "event".to_string(),
                    vec![Some(Box::new(unresolved_var("SawState")))],
                    None,
                ),
            ],
            None,
        );

        let hints = collect_hints(&expr);
        assert_eq!(
            hints.len(),
            8,
            "walker should find constructor hints inside every covered variant: {hints:?}"
        );
    }

    #[test]
    fn check_type_reports_duplicate_enum_constructors_and_record_fields() {
        let enum_errors = check_type(
            &Ty::Enum(
                "Status".to_string(),
                vec![
                    "Open".to_string(),
                    "Closed".to_string(),
                    "Open".to_string(),
                    "Closed".to_string(),
                ],
            ),
            Some(crate::span::Span { start: 10, end: 16 }),
        );
        assert_eq!(enum_errors.len(), 2);
        assert!(enum_errors
            .iter()
            .any(|error| error.message.contains("duplicate constructor Open")));
        assert!(enum_errors
            .iter()
            .any(|error| error.message.contains("duplicate constructor Closed")));
        assert!(enum_errors.iter().all(|error| error.span.is_some()));

        let record_errors = check_type(
            &Ty::Record(
                "Point".to_string(),
                vec![
                    ("x".to_string(), Ty::Builtin(BuiltinTy::Int)),
                    ("y".to_string(), Ty::Builtin(BuiltinTy::Int)),
                    ("x".to_string(), Ty::Builtin(BuiltinTy::Real)),
                ],
            ),
            None,
        );
        assert_eq!(record_errors.len(), 1);
        assert!(record_errors[0].message.contains("duplicate field x"));
        assert!(record_errors[0].span.is_none());
    }

    #[test]
    fn collection_homogeneity_checks_sets_sequences_maps_and_recurses() {
        let set_mismatch = EExpr::SetLit(Ty::Error, vec![int_lit(1), bool_lit(true)], None);
        let seq_mismatch = EExpr::SeqLit(Ty::Error, vec![int_lit(1), bool_lit(false)], None);
        let map_key_and_value_mismatch = EExpr::MapLit(
            Ty::Error,
            vec![(int_lit(1), bool_lit(true)), (bool_lit(false), int_lit(2))],
            None,
        );
        let set_errors = collect_homogeneity_errors(&set_mismatch);
        let seq_errors = collect_homogeneity_errors(&seq_mismatch);
        let map_errors = collect_homogeneity_errors(&map_key_and_value_mismatch);
        assert_eq!(set_errors.len(), 1);
        assert!(set_errors[0].message.contains("element 1"));
        assert_eq!(seq_errors.len(), 1);
        assert!(seq_errors[0].message.contains("element 1"));
        assert_eq!(map_errors.len(), 2);
        assert!(map_errors
            .iter()
            .any(|error| error.message.contains("key 1")));
        assert!(map_errors
            .iter()
            .any(|error| error.message.contains("value 1")));

        let singleton_set = EExpr::SetLit(Ty::Error, vec![int_lit(1)], None);
        let singleton_seq = EExpr::SeqLit(Ty::Error, vec![int_lit(1)], None);
        let singleton_map = EExpr::MapLit(Ty::Error, vec![(int_lit(1), bool_lit(true))], None);
        assert!(collect_homogeneity_errors(&singleton_set).is_empty());
        assert!(collect_homogeneity_errors(&singleton_seq).is_empty());
        assert!(collect_homogeneity_errors(&singleton_map).is_empty());
        assert!(collect_homogeneity_errors(&EExpr::SetLit(Ty::Error, vec![], None)).is_empty());
        assert!(collect_homogeneity_errors(&EExpr::SeqLit(Ty::Error, vec![], None)).is_empty());
        assert!(collect_homogeneity_errors(&EExpr::MapLit(Ty::Error, vec![], None)).is_empty());

        let nested = EExpr::Pipe(
            Ty::Error,
            Box::new(EExpr::Field(
                Ty::Error,
                Box::new(EExpr::UnOp(
                    Ty::Error,
                    crate::elab::types::UnOp::Not,
                    Box::new(set_mismatch),
                    None,
                )),
                "items".to_string(),
                None,
            )),
            Box::new(EExpr::BinOp(
                Ty::Error,
                crate::elab::types::BinOp::Add,
                Box::new(seq_mismatch),
                Box::new(map_key_and_value_mismatch),
                None,
            )),
            None,
        );
        assert_eq!(collect_homogeneity_errors(&nested).len(), 4);
    }

    #[test]
    fn collection_homogeneity_recurses_through_calls_and_nested_collections() {
        let nested_set = EExpr::SetLit(
            Ty::Error,
            vec![EExpr::SetLit(
                Ty::Error,
                vec![int_lit(1), bool_lit(false)],
                None,
            )],
            None,
        );
        assert_eq!(collect_homogeneity_errors(&nested_set).len(), 1);

        let nested_map = EExpr::MapLit(
            Ty::Error,
            vec![(
                int_lit(0),
                EExpr::MapLit(
                    Ty::Error,
                    vec![(int_lit(1), bool_lit(true)), (bool_lit(false), int_lit(2))],
                    None,
                ),
            )],
            None,
        );
        assert_eq!(collect_homogeneity_errors(&nested_map).len(), 2);

        let bare_relation_call = EExpr::Call(
            Ty::Error,
            Box::new(EExpr::Var(
                Ty::Error,
                "join".to_string(),
                Some(crate::span::Span { start: 1, end: 5 }),
            )),
            vec![EExpr::SeqLit(
                Ty::Error,
                vec![int_lit(1), bool_lit(true)],
                None,
            )],
            Some(crate::span::Span { start: 1, end: 10 }),
        );
        let call_errors = collect_homogeneity_errors(&bare_relation_call);
        assert_eq!(call_errors.len(), 2);
        assert!(call_errors
            .iter()
            .any(|error| error.message.contains("must be called as `Rel::join`")));
        assert!(call_errors
            .iter()
            .any(|error| error.message.contains("Seq literal element 1")));

        let qualified_relation_call = EExpr::QualCall(
            Ty::Error,
            "Rel".to_string(),
            "project".to_string(),
            vec![EExpr::MapLit(
                Ty::Error,
                vec![(int_lit(1), bool_lit(true)), (bool_lit(false), int_lit(2))],
                None,
            )],
            Some(crate::span::Span { start: 11, end: 20 }),
        );
        let qual_errors = collect_homogeneity_errors(&qualified_relation_call);
        assert_eq!(qual_errors.len(), 3);
        assert!(qual_errors
            .iter()
            .any(|error| error.message.contains("Rel::project requires")));
        assert!(qual_errors
            .iter()
            .any(|error| error.message.contains("Map literal key 1")));
        assert!(qual_errors
            .iter()
            .any(|error| error.message.contains("Map literal value 1")));
    }

    #[test]
    fn types_compatible_covers_error_wrappers_entities_and_collections() {
        let int = Ty::Builtin(BuiltinTy::Int);
        let bool_ty = Ty::Builtin(BuiltinTy::Bool);
        let real = Ty::Builtin(BuiltinTy::Real);
        let int_set = Ty::Set(Box::new(int.clone()));
        let bool_set = Ty::Set(Box::new(bool_ty.clone()));
        let int_seq = Ty::Seq(Box::new(int.clone()));
        let bool_seq = Ty::Seq(Box::new(bool_ty.clone()));

        assert!(types_compatible(&Ty::Error, &int));
        assert!(types_compatible(&int_set, &Ty::Set(Box::new(int.clone()))));
        assert!(!types_compatible(&int_set, &bool_set));
        assert!(types_compatible(&int_seq, &Ty::Seq(Box::new(int.clone()))));
        assert!(!types_compatible(&int_seq, &bool_seq));

        assert!(types_compatible(
            &Ty::Map(Box::new(int.clone()), Box::new(bool_ty.clone())),
            &Ty::Map(Box::new(int.clone()), Box::new(bool_ty.clone()))
        ));
        assert!(!types_compatible(
            &Ty::Map(Box::new(int.clone()), Box::new(bool_ty.clone())),
            &Ty::Map(Box::new(bool_ty.clone()), Box::new(bool_ty.clone()))
        ));
        assert!(!types_compatible(
            &Ty::Map(Box::new(int.clone()), Box::new(bool_ty.clone())),
            &Ty::Map(Box::new(int.clone()), Box::new(int.clone()))
        ));

        assert!(types_compatible(
            &Ty::Store("Account".to_string()),
            &Ty::Store("Account".to_string())
        ));
        assert!(!types_compatible(
            &Ty::Store("Account".to_string()),
            &Ty::Store("Order".to_string())
        ));
        assert!(types_compatible(
            &Ty::Entity("Account".to_string()),
            &Ty::Entity("Account".to_string())
        ));
        assert!(!types_compatible(
            &Ty::Entity("Account".to_string()),
            &Ty::Entity("Order".to_string())
        ));
        assert!(types_compatible(
            &Ty::Entity("Account".to_string()),
            &Ty::Named("Account".to_string())
        ));
        assert!(!types_compatible(
            &Ty::Entity("Account".to_string()),
            &Ty::Named("Order".to_string())
        ));

        let relation = Ty::Relation(vec![int.clone(), bool_ty.clone()]);
        assert!(types_compatible(
            &relation,
            &Ty::Relation(vec![int.clone(), bool_ty.clone()])
        ));
        assert!(!types_compatible(
            &relation,
            &Ty::Relation(vec![int.clone(), real.clone()])
        ));
        assert!(!types_compatible(
            &relation,
            &Ty::Relation(vec![int.clone()])
        ));
        assert!(types_compatible(
            &Ty::Relation(vec![int.clone()]),
            &Ty::Set(Box::new(int.clone()))
        ));
        assert!(types_compatible(
            &Ty::Set(Box::new(Ty::Tuple(vec![int.clone(), bool_ty.clone()]))),
            &relation
        ));
        assert!(!types_compatible(
            &Ty::Set(Box::new(Ty::Tuple(vec![int.clone(), real.clone()]))),
            &relation
        ));
        assert!(!types_compatible(
            &Ty::Relation(vec![int.clone(), bool_ty.clone()]),
            &Ty::Set(Box::new(int.clone()))
        ));

        assert!(types_compatible(
            &Ty::Tuple(vec![int.clone(), bool_ty.clone()]),
            &Ty::Tuple(vec![int.clone(), bool_ty.clone()])
        ));
        assert!(!types_compatible(
            &Ty::Tuple(vec![int.clone(), bool_ty.clone()]),
            &Ty::Tuple(vec![int.clone()])
        ));
        assert!(types_compatible(
            &Ty::Alias("Count".to_string(), Box::new(int.clone())),
            &Ty::Alias("Count".to_string(), Box::new(real.clone()))
        ));
        assert!(!types_compatible(
            &Ty::Alias("Count".to_string(), Box::new(int.clone())),
            &Ty::Alias("Other".to_string(), Box::new(int.clone()))
        ));
        assert!(types_compatible(
            &Ty::Alias("Count".to_string(), Box::new(int.clone())),
            &int
        ));
        assert!(types_compatible(
            &Ty::Refinement(Box::new(int.clone()), Box::new(bool_lit(true))),
            &int
        ));
        assert!(!types_compatible(
            &Ty::Refinement(Box::new(int), Box::new(bool_lit(true))),
            &bool_ty
        ));
    }

    #[test]
    fn expr_compatible_with_ty_allows_int_literals_for_real_targets_only() {
        assert!(expr_compatible_with_ty(
            &int_lit(1),
            &Ty::Builtin(BuiltinTy::Real)
        ));
        assert!(expr_compatible_with_ty(
            &bool_lit(true),
            &Ty::Builtin(BuiltinTy::Bool)
        ));
        assert!(!expr_compatible_with_ty(
            &bool_lit(true),
            &Ty::Builtin(BuiltinTy::Real)
        ));
        assert!(!expr_compatible_with_ty(
            &EExpr::Var(Ty::Builtin(BuiltinTy::Int), "x".to_string(), None),
            &Ty::Builtin(BuiltinTy::Real)
        ));
    }

    #[test]
    fn fn_contract_checker_accepts_valid_contracts_and_reports_invalid_ones() {
        let valid = fn_decl(
            vec![
                EContract::Requires(bool_lit(true)),
                EContract::Ensures(bool_lit(true)),
                EContract::Decreases {
                    measures: vec![int_lit(1)],
                    star: false,
                },
                EContract::Invariant(bool_lit(true)),
            ],
            vec![],
        );
        assert!(check_fn_contracts(&valid).is_empty());

        let invalid = fn_decl(
            vec![
                EContract::Requires(int_lit(1)),
                EContract::Ensures(int_lit(2)),
                EContract::Decreases {
                    measures: vec![bool_lit(false)],
                    star: true,
                },
                EContract::Invariant(int_lit(3)),
            ],
            vec![],
        );
        let errors = check_fn_contracts(&invalid);
        assert_eq!(errors.len(), 5);
        assert!(errors
            .iter()
            .any(|error| error.message == messages::REQUIRES_NOT_BOOL));
        assert!(errors
            .iter()
            .any(|error| error.message == messages::ENSURES_NOT_BOOL));
        assert!(errors
            .iter()
            .any(|error| error.message == messages::DECREASES_MEASURE_NOT_INT));
        assert!(errors
            .iter()
            .any(|error| error.message == messages::DECREASES_STAR_WARNING));
        assert!(errors
            .iter()
            .any(|error| error.message.contains("invariant clause")));
    }

    #[test]
    fn refinement_predicate_checker_accepts_bool_or_error_and_rejects_other_types() {
        let valid = fn_decl(
            vec![],
            vec![
                (
                    "ok".to_string(),
                    Ty::Refinement(
                        Box::new(Ty::Builtin(BuiltinTy::Int)),
                        Box::new(bool_lit(true)),
                    ),
                ),
                (
                    "poison".to_string(),
                    Ty::Refinement(
                        Box::new(Ty::Builtin(BuiltinTy::Int)),
                        Box::new(EExpr::Var(Ty::Error, "Bad".to_string(), None)),
                    ),
                ),
            ],
        );
        assert!(check_refinement_predicates(&valid).is_empty());

        let invalid = fn_decl(
            vec![],
            vec![(
                "n".to_string(),
                Ty::Refinement(Box::new(Ty::Builtin(BuiltinTy::Int)), Box::new(int_lit(1))),
            )],
        );
        let errors = check_refinement_predicates(&invalid);
        assert_eq!(errors.len(), 1);
        assert!(errors[0]
            .message
            .contains(messages::REFINEMENT_PREDICATE_NOT_BOOL));
    }

    #[test]
    fn verifier_surface_checks_sequence_composition_and_unsupported_forms() {
        let seq = EExpr::Seq(
            Ty::Builtin(BuiltinTy::Bool),
            Box::new(bool_lit(true)),
            Box::new(bool_lit(false)),
            Some(crate::span::Span { start: 20, end: 22 }),
        );
        let mut errors = Vec::new();
        check_verifier_surface_expr(&seq, "prop p", &mut errors);
        assert_eq!(errors.len(), 1);
        assert!(errors[0].message.contains("sequence composition"));

        let mut allowing_sequence_errors = Vec::new();
        check_verifier_surface_expr_allowing_sequence(
            &EExpr::Block(
                vec![bool_lit(true)],
                Some(crate::span::Span { start: 30, end: 35 }),
            ),
            "scene s when assumption",
            &mut allowing_sequence_errors,
        );
        assert_eq!(allowing_sequence_errors.len(), 1);
        assert!(allowing_sequence_errors[0].message.contains("block"));

        let while_with_sequence_contract = EExpr::While(
            Box::new(bool_lit(true)),
            vec![EContract::Invariant(seq)],
            Box::new(bool_lit(true)),
            Some(crate::span::Span { start: 40, end: 55 }),
        );
        let mut nested_errors = Vec::new();
        check_verifier_surface_expr(
            &while_with_sequence_contract,
            "theorem t show expression",
            &mut nested_errors,
        );
        assert_eq!(nested_errors.len(), 2);
        assert!(nested_errors
            .iter()
            .any(|error| error.message.contains("sequence composition")));
        assert!(nested_errors
            .iter()
            .any(|error| error.message.contains("while loop")));
    }

    #[test]
    fn pred_prop_cycle_checker_reports_cycles_and_respects_fn_decreases() {
        let mut pred_env = Env::new();
        pred_env.preds.insert(
            "p".to_string(),
            pred_decl(
                "p",
                EExpr::Var(Ty::Builtin(BuiltinTy::Bool), "p".to_string(), None),
            ),
        );
        let pred_errors = check_pred_prop_cycles(&pred_env);
        assert_eq!(pred_errors.len(), 1);
        assert!(pred_errors[0]
            .message
            .contains("circular definition detected"));
        assert_eq!(
            pred_errors[0].help.as_deref(),
            Some(messages::HELP_CIRCULAR_DEFINITION)
        );

        let mut self_recursive_fn = fn_decl(vec![], vec![]);
        self_recursive_fn.body = EExpr::Var(
            Ty::Builtin(BuiltinTy::Int),
            self_recursive_fn.name.clone(),
            None,
        );
        let mut fn_env = Env::new();
        fn_env
            .fns
            .insert(self_recursive_fn.name.clone(), self_recursive_fn.clone());
        let fn_errors = check_pred_prop_cycles(&fn_env);
        assert_eq!(fn_errors.len(), 1);
        assert_eq!(
            fn_errors[0].help.as_deref(),
            Some(messages::HELP_SELF_RECURSION_DECREASES)
        );

        self_recursive_fn.contracts = vec![EContract::Decreases {
            measures: vec![int_lit(1)],
            star: false,
        }];
        let mut decreasing_fn_env = Env::new();
        decreasing_fn_env
            .fns
            .insert(self_recursive_fn.name.clone(), self_recursive_fn);
        assert!(check_pred_prop_cycles(&decreasing_fn_env).is_empty());

        let mut f = fn_decl(vec![], vec![]);
        f.name = "f".to_string();
        f.body = EExpr::Var(Ty::Builtin(BuiltinTy::Int), "g".to_string(), None);
        let mut g = fn_decl(vec![], vec![]);
        g.name = "g".to_string();
        g.body = EExpr::Var(Ty::Builtin(BuiltinTy::Int), "f".to_string(), None);
        let mut mutual_env = Env::new();
        mutual_env.fns.insert("f".to_string(), f);
        mutual_env.fns.insert("g".to_string(), g);
        let mutual_errors = check_pred_prop_cycles(&mutual_env);
        assert_eq!(mutual_errors.len(), 1);
        assert_eq!(
            mutual_errors[0].help.as_deref(),
            Some(messages::HELP_MUTUAL_FN_DECREASES)
        );
    }

    #[test]
    fn collect_name_refs_respects_bindings_and_pattern_variables() {
        let known = HashSet::from(["p".to_string(), "q".to_string(), "x".to_string()]);
        let mut refs = HashSet::new();
        collect_name_refs(
            &EExpr::Var(Ty::Builtin(BuiltinTy::Bool), "p".to_string(), None),
            &known,
            &HashSet::new(),
            &mut refs,
        );
        assert_eq!(refs, HashSet::from(["p".to_string()]));

        let match_expr = EExpr::Match(
            Box::new(EExpr::Var(
                Ty::Builtin(BuiltinTy::Bool),
                "q".to_string(),
                None,
            )),
            vec![(
                EPattern::Ctor(
                    "Some".to_string(),
                    vec![("value".to_string(), EPattern::Var("p".to_string()))],
                ),
                Some(EExpr::Var(
                    Ty::Builtin(BuiltinTy::Bool),
                    "p".to_string(),
                    None,
                )),
                EExpr::Var(Ty::Builtin(BuiltinTy::Bool), "p".to_string(), None),
            )],
            None,
        );
        let mut match_refs = HashSet::new();
        collect_name_refs(&match_expr, &known, &HashSet::new(), &mut match_refs);
        assert_eq!(
            match_refs,
            HashSet::from(["q".to_string()]),
            "pattern-bound p should not be collected from guard/body"
        );

        let let_expr = EExpr::Let(
            vec![(
                "x".to_string(),
                Some(Ty::Builtin(BuiltinTy::Bool)),
                bool_lit(true),
            )],
            Box::new(EExpr::Var(
                Ty::Builtin(BuiltinTy::Bool),
                "x".to_string(),
                None,
            )),
            None,
        );
        let mut let_refs = HashSet::new();
        collect_name_refs(&let_expr, &known, &HashSet::new(), &mut let_refs);
        assert!(let_refs.is_empty());
    }

    #[test]
    fn dfs_find_cycle_distinguishes_cycles_from_acyclic_graphs() {
        let cyclic = HashMap::from([
            ("a".to_string(), HashSet::from(["b".to_string()])),
            ("b".to_string(), HashSet::from(["c".to_string()])),
            ("c".to_string(), HashSet::from(["a".to_string()])),
        ]);
        let mut visited = HashSet::new();
        let mut in_stack = HashSet::new();
        let cycle = dfs_find_cycle("a", &cyclic, &mut visited, &mut in_stack)
            .expect("expected back-edge cycle");
        assert_eq!(cycle.first(), cycle.last());
        assert_eq!(cycle, vec!["a", "b", "c", "a"]);

        let acyclic = HashMap::from([
            ("a".to_string(), HashSet::from(["b".to_string()])),
            ("b".to_string(), HashSet::new()),
        ]);
        let mut visited = HashSet::new();
        let mut in_stack = HashSet::new();
        assert!(dfs_find_cycle("a", &acyclic, &mut visited, &mut in_stack).is_none());
    }

    #[test]
    fn prop_pred_cycle_checker_uses_prop_dependencies() {
        let mut env = Env::new();
        env.props.insert(
            "p".to_string(),
            prop_decl(
                "p",
                EExpr::Var(Ty::Builtin(BuiltinTy::Bool), "q".to_string(), None),
            ),
        );
        env.preds.insert(
            "q".to_string(),
            pred_decl(
                "q",
                EExpr::Var(Ty::Builtin(BuiltinTy::Bool), "p".to_string(), None),
            ),
        );
        let errors = check_pred_prop_cycles(&env);
        assert_eq!(errors.len(), 1);
        assert_eq!(
            errors[0].help.as_deref(),
            Some(messages::HELP_CIRCULAR_DEFINITION)
        );
    }
}
