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
    BuiltinTy, EContract, EExpr, EFn, EPattern, ESceneWhen, EType, EVariant, ElabResult, Ty,
    VariantFieldsMap,
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
    // walk system step guards/bodies and query bodies for
    // StructCtor (and CtorRecord) well-formedness.
    for system in env.systems.values() {
        for step in &system.steps {
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
            check_verifier_surface_expr(
                a,
                &format!("verify {} assertion", verify.name),
                &mut errors,
            );
            check_match_exhaustiveness(a, &env.types, &env.entities, &mut errors);
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
                check_verifier_surface_expr(
                    cond,
                    &format!("scene {} given condition", scene.name),
                    &mut errors,
                );
                check_match_exhaustiveness(cond, &env.types, &env.entities, &mut errors);
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
                        check_match_exhaustiveness(arg, &env.types, &env.entities, &mut errors);
                    }
                }
                ESceneWhen::Assume(e) => {
                    check_verifier_surface_expr(
                        e,
                        &format!("scene {} when assumption", scene.name),
                        &mut errors,
                    );
                    check_match_exhaustiveness(e, &env.types, &env.entities, &mut errors);
                }
            }
        }
        for then_expr in &scene.thens {
            check_verifier_surface_expr(
                then_expr,
                &format!("scene {} then assertion", scene.name),
                &mut errors,
            );
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
        EExpr::Call(_, f, args, _) => {
            check_collection_homogeneity(f, ctx, errors);
            for a in args {
                check_collection_homogeneity(a, ctx, errors);
            }
        }
        EExpr::QualCall(_, _, _, args, _) => {
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
fn types_compatible(a: &Ty, b: &Ty) -> bool {
    match (a, b) {
        (Ty::Error, _) | (_, Ty::Error) => true,
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
        | EExpr::SetComp(_, _, _, _, _, sp)
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
        _ => None,
    }
}

fn check_verifier_surface_expr(expr: &EExpr, ctx: &str, errors: &mut Vec<ElabError>) {
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
        EExpr::SetComp(_, projection, _, _, filter, _) => projection
            .as_ref()
            .and_then(|expr| find_unsupported_verifier_expr(expr))
            .or_else(|| find_unsupported_verifier_expr(filter)),
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
    use crate::elab::types::{EExpr, Literal, Ty};

    /// Helper: make an unknown uppercase Var that should trigger the hint.
    fn unresolved_var(name: &str) -> EExpr {
        EExpr::Var(Ty::Error, name.to_string(), None)
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
}
