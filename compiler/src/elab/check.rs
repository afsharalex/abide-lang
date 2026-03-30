//! Pass 3: Type-check expressions and validate well-formedness.
//!
//! Validates: field defaults match types, requires is Bool,
//! primed assignments target known fields, system uses reference known entities.

use std::collections::{HashMap, HashSet};

use super::env::Env;
use super::error::{ElabError, ErrorKind};
use super::types::{
    BuiltinTy, EAction, EContract, EEntity, EExpr, EField, EFn, EPattern, ESystem, EType, EVariant,
    ElabResult, Ty,
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
    }
    for entity in env.entities.values() {
        errors.extend(check_entity(entity, &all_known_names));
    }
    for system in env.systems.values() {
        errors.extend(check_system(env, system));
    }

    // Check fn contracts
    for f in env.fns.values() {
        errors.extend(check_fn_contracts(f));
    }

    // Check for cyclic pred/prop definitions
    errors.extend(check_pred_prop_cycles(env));

    let result = ElabResult {
        module_name: env.module_name.clone(),
        includes: env.includes.clone(),
        use_decls: env.use_decls.iter().map(|e| e.decl.clone()).collect(),
        types: env
            .types
            .iter()
            .map(|(name, ty)| mk_etype(name, ty))
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

fn mk_etype(_map_key: &str, ty: &Ty) -> EType {
    let canonical = ty.name().to_owned();
    match ty {
        Ty::Enum(_, vs) => EType {
            name: canonical,
            variants: vs.iter().map(|v| EVariant::Simple(v.clone())).collect(),
            ty: ty.clone(),
            span: None, // Type spans not yet tracked in Ty
        },
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
    let Some(ref def_expr) = field.default else {
        return Vec::new();
    };

    match (&field.ty, def_expr) {
        (Ty::Enum(_, ctors), EExpr::Var(_, v, _)) if !ctors.iter().any(|c| c == v) => {
            let ctx = format!("entity {entity_name}, field {}", field.name);
            let err = if let Some(span) = field.span {
                ElabError::with_span(
                    ErrorKind::InvalidDefault,
                    format!("{v} is not a constructor of {}", field.ty.name()),
                    &ctx,
                    span,
                )
            } else {
                ElabError::new(
                    ErrorKind::InvalidDefault,
                    format!("{v} is not a constructor of {}", field.ty.name()),
                    &ctx,
                )
            };
            // Suggest closest matching constructor
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
    for entity_name in &system.uses {
        if env.lookup_entity(entity_name).is_none() {
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
        EExpr::UnOp(_, _, e, _)
        | EExpr::Always(_, e, _)
        | EExpr::Eventually(_, e, _)
        | EExpr::Assert(_, e, _)
        | EExpr::Prime(_, e, _)
        | EExpr::Card(_, e, _)
        | EExpr::Field(_, e, _, _)
        | EExpr::NamedPair(_, _, e, _) => {
            check_unresolved_constructors(e, ctx, span, known_names, errors);
        }
        EExpr::Call(_, f, args, _) => {
            check_unresolved_constructors(f, ctx, span, known_names, errors);
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

/// Extract the type annotation from an elaborated expression (if available).
fn expr_type(e: &EExpr) -> Option<&Ty> {
    match e {
        EExpr::Lit(ty, _, _)
        | EExpr::Var(ty, _, _)
        | EExpr::BinOp(ty, _, _, _, _)
        | EExpr::UnOp(ty, _, _, _)
        | EExpr::Call(ty, _, _, _)
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
                errors.push(ElabError::new(
                    ErrorKind::CyclicDefinition,
                    format!("circular definition detected: {}", cycle.join(" → ")),
                    name.clone(),
                ));
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
        EExpr::Assert(_, e, _) => collect_name_refs(e, known_names, bound, refs),
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
