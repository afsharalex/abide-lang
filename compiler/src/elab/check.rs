//! Pass 3: Type-check expressions and validate well-formedness.
//!
//! Validates: field defaults match types, requires is Bool,
//! primed assignments target known fields, system uses reference known entities.

use std::collections::{HashMap, HashSet};

use super::env::Env;
use super::error::{ElabError, ErrorKind};
use super::types::{
    BuiltinTy, EAction, EEntity, EExpr, EField, EPattern, ESystem, EType, EVariant, ElabResult, Ty,
};

/// Type-check the resolved environment.
/// Returns an `ElabResult` with all elaborated declarations + any errors.
pub fn check(env: &Env) -> (ElabResult, Vec<ElabError>) {
    let mut errors = Vec::new();

    for (name, ty) in &env.types {
        let decl_span = env.lookup_decl(name).and_then(|d| d.span);
        errors.extend(check_type(ty, decl_span));
    }
    for entity in env.entities.values() {
        errors.extend(check_entity(entity));
    }
    for system in env.systems.values() {
        errors.extend(check_system(env, system));
    }

    // Check for cyclic pred/prop definitions
    errors.extend(check_pred_prop_cycles(env));

    let result = ElabResult {
        module_name: env.module_name.clone(),
        includes: env.includes.clone(),
        use_decls: env.use_decls.iter().map(|(ud, _)| ud.clone()).collect(),
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

fn check_entity(entity: &EEntity) -> Vec<ElabError> {
    let mut errors = Vec::new();

    for field in &entity.fields {
        errors.extend(check_field(&entity.name, field));
    }
    for action in &entity.actions {
        errors.extend(check_action(entity, action));
    }

    errors
}

fn check_field(entity_name: &str, field: &EField) -> Vec<ElabError> {
    let Some(ref def_expr) = field.default else {
        return Vec::new();
    };

    match (&field.ty, def_expr) {
        (Ty::Enum(_, ctors), EExpr::Var(_, v)) if !ctors.iter().any(|c| c == v) => {
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

fn check_action(entity: &EEntity, action: &EAction) -> Vec<ElabError> {
    let ctx = format!("entity {}, action {}", entity.name, action.name);
    let mut errors = Vec::new();

    // Check requires are boolean-typed
    for req in &action.requires {
        if !is_bool_expr(req) {
            let err = if let Some(span) = action.span {
                ElabError::with_span(
                    ErrorKind::TypeMismatch,
                    "requires expression should be Bool",
                    &ctx,
                    span,
                )
            } else {
                ElabError::new(
                    ErrorKind::TypeMismatch,
                    "requires expression should be Bool",
                    &ctx,
                )
            };
            errors.push(err);
        }
    }

    // Check for unresolved uppercase names that might be missing @ prefix
    for req in &action.requires {
        check_unresolved_constructors(req, &ctx, action.span, &mut errors);
    }

    // Check primed assignments target known fields
    for expr in &action.body {
        errors.extend(check_assignment(entity, action, &ctx, expr));
    }

    errors
}

fn check_assignment(entity: &EEntity, action: &EAction, ctx: &str, expr: &EExpr) -> Vec<ElabError> {
    if let EExpr::Assign(_, lhs, _) = expr {
        if let EExpr::Prime(_, inner) = lhs.as_ref() {
            if let EExpr::Var(_, field_name) = inner.as_ref() {
                let field_names: Vec<&str> =
                    entity.fields.iter().map(|f| f.name.as_str()).collect();
                if !field_names.contains(&field_name.as_str()) {
                    let err = if let Some(span) = action.span {
                        ElabError::with_span(
                            ErrorKind::InvalidPrime,
                            format!("{field_name} is not a field of {}", entity.name),
                            ctx,
                            span,
                        )
                    } else {
                        ElabError::new(
                            ErrorKind::InvalidPrime,
                            format!("{field_name} is not a field of {}", entity.name),
                            ctx,
                        )
                    };
                    return vec![err.with_help("only entity fields can be primed")];
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

    for entity_name in &system.uses {
        if env.lookup_entity(entity_name).is_none() {
            let err = if let Some(span) = system.span {
                ElabError::with_span(
                    ErrorKind::UndefinedRef,
                    format!("system {} uses unknown entity {entity_name}", system.name),
                    &sys_ctx,
                    span,
                )
            } else {
                ElabError::new(
                    ErrorKind::UndefinedRef,
                    format!("system {} uses unknown entity {entity_name}", system.name),
                    &sys_ctx,
                )
            };
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
    errors: &mut Vec<ElabError>,
) {
    match expr {
        EExpr::Var(Ty::Unresolved(_), name)
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
            errors.push(err.with_help(format!(
                "if '{name}' is a state constructor, write '@{name}'"
            )));
        }
        EExpr::BinOp(_, _, l, r)
        | EExpr::Assign(_, l, r)
        | EExpr::Seq(_, l, r)
        | EExpr::SameStep(_, l, r)
        | EExpr::Pipe(_, l, r)
        | EExpr::In(_, l, r) => {
            check_unresolved_constructors(l, ctx, span, errors);
            check_unresolved_constructors(r, ctx, span, errors);
        }
        EExpr::UnOp(_, _, e)
        | EExpr::Always(_, e)
        | EExpr::Eventually(_, e)
        | EExpr::Assert(_, e)
        | EExpr::Prime(_, e)
        | EExpr::Card(_, e)
        | EExpr::Field(_, e, _)
        | EExpr::NamedPair(_, _, e) => {
            check_unresolved_constructors(e, ctx, span, errors);
        }
        EExpr::Call(_, f, args) => {
            check_unresolved_constructors(f, ctx, span, errors);
            for arg in args {
                check_unresolved_constructors(arg, ctx, span, errors);
            }
        }
        EExpr::Quant(_, _, _, _, body) | EExpr::Lam(_, _, body) => {
            check_unresolved_constructors(body, ctx, span, errors);
        }
        EExpr::Match(scrut, arms) => {
            check_unresolved_constructors(scrut, ctx, span, errors);
            for (_, guard, body) in arms {
                if let Some(g) = guard {
                    check_unresolved_constructors(g, ctx, span, errors);
                }
                check_unresolved_constructors(body, ctx, span, errors);
            }
        }
        EExpr::Let(binds, body) => {
            for (_, _, e) in binds {
                check_unresolved_constructors(e, ctx, span, errors);
            }
            check_unresolved_constructors(body, ctx, span, errors);
        }
        EExpr::TupleLit(_, es) | EExpr::SetLit(_, es) | EExpr::SeqLit(_, es) => {
            for e in es {
                check_unresolved_constructors(e, ctx, span, errors);
            }
        }
        EExpr::CallR(_, f, refs, args) => {
            check_unresolved_constructors(f, ctx, span, errors);
            for r in refs {
                check_unresolved_constructors(r, ctx, span, errors);
            }
            for a in args {
                check_unresolved_constructors(a, ctx, span, errors);
            }
        }
        EExpr::MapUpdate(_, m, k, v) => {
            check_unresolved_constructors(m, ctx, span, errors);
            check_unresolved_constructors(k, ctx, span, errors);
            check_unresolved_constructors(v, ctx, span, errors);
        }
        EExpr::Index(_, m, k) => {
            check_unresolved_constructors(m, ctx, span, errors);
            check_unresolved_constructors(k, ctx, span, errors);
        }
        EExpr::SetComp(_, proj, _, _, filter) => {
            if let Some(p) = proj {
                check_unresolved_constructors(p, ctx, span, errors);
            }
            check_unresolved_constructors(filter, ctx, span, errors);
        }
        EExpr::MapLit(_, entries) => {
            for (k, v) in entries {
                check_unresolved_constructors(k, ctx, span, errors);
                check_unresolved_constructors(v, ctx, span, errors);
            }
        }
        // True leaf nodes: Lit, Qual, Unresolved, Sorry, Todo
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
fn find_closest_name<'a>(target: &str, candidates: &'a [String]) -> Option<&'a str> {
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

    // Extract dependencies from fn bodies
    for (name, f) in &env.fns {
        let mut referenced = HashSet::new();
        let bound: HashSet<String> = f.params.iter().map(|(n, _)| n.clone()).collect();
        collect_name_refs(&f.body, &all_names, &bound, &mut referenced);
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
        EExpr::Var(_, name) => {
            if !bound.contains(name) && known_names.contains(name.as_str()) {
                refs.insert(name.clone());
            }
        }
        EExpr::Call(_, func, args) => {
            collect_name_refs(func, known_names, bound, refs);
            for arg in args {
                collect_name_refs(arg, known_names, bound, refs);
            }
        }
        EExpr::CallR(_, func, ref_args, args) => {
            collect_name_refs(func, known_names, bound, refs);
            for arg in ref_args {
                collect_name_refs(arg, known_names, bound, refs);
            }
            for arg in args {
                collect_name_refs(arg, known_names, bound, refs);
            }
        }
        EExpr::BinOp(_, _, l, r) => {
            collect_name_refs(l, known_names, bound, refs);
            collect_name_refs(r, known_names, bound, refs);
        }
        EExpr::UnOp(_, _, e) => collect_name_refs(e, known_names, bound, refs),
        EExpr::Field(_, e, _) => collect_name_refs(e, known_names, bound, refs),
        EExpr::Prime(_, e) => collect_name_refs(e, known_names, bound, refs),
        EExpr::Quant(_, _, var, _, body) => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.clone());
            collect_name_refs(body, known_names, &inner_bound, refs);
        }
        EExpr::Always(_, e) => collect_name_refs(e, known_names, bound, refs),
        EExpr::Eventually(_, e) => collect_name_refs(e, known_names, bound, refs),
        EExpr::Assert(_, e) => collect_name_refs(e, known_names, bound, refs),
        EExpr::Assign(_, l, r) => {
            collect_name_refs(l, known_names, bound, refs);
            collect_name_refs(r, known_names, bound, refs);
        }
        EExpr::Seq(_, l, r)
        | EExpr::SameStep(_, l, r)
        | EExpr::Pipe(_, l, r)
        | EExpr::In(_, l, r) => {
            collect_name_refs(l, known_names, bound, refs);
            collect_name_refs(r, known_names, bound, refs);
        }
        EExpr::Let(binds, body) => {
            let mut inner_bound = bound.clone();
            for (name, _, e) in binds {
                collect_name_refs(e, known_names, &inner_bound, refs);
                inner_bound.insert(name.clone());
            }
            collect_name_refs(body, known_names, &inner_bound, refs);
        }
        EExpr::Lam(params, _, body) => {
            let mut inner_bound = bound.clone();
            for (name, _) in params {
                inner_bound.insert(name.clone());
            }
            collect_name_refs(body, known_names, &inner_bound, refs);
        }
        EExpr::Match(scrut, arms) => {
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
        EExpr::NamedPair(_, _, e) => collect_name_refs(e, known_names, bound, refs),
        EExpr::TupleLit(_, elems) => {
            for e in elems {
                collect_name_refs(e, known_names, bound, refs);
            }
        }
        EExpr::Card(_, e) => collect_name_refs(e, known_names, bound, refs),
        EExpr::MapUpdate(_, m, k, v) => {
            collect_name_refs(m, known_names, bound, refs);
            collect_name_refs(k, known_names, bound, refs);
            collect_name_refs(v, known_names, bound, refs);
        }
        EExpr::Index(_, m, k) => {
            collect_name_refs(m, known_names, bound, refs);
            collect_name_refs(k, known_names, bound, refs);
        }
        EExpr::SetComp(_, proj, var, _, filter) => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.clone());
            if let Some(p) = proj {
                collect_name_refs(p, known_names, &inner_bound, refs);
            }
            collect_name_refs(filter, known_names, &inner_bound, refs);
        }
        // Leaf nodes — no references
        EExpr::Lit(..)
        | EExpr::Qual(..)
        | EExpr::Unresolved(_)
        | EExpr::Sorry
        | EExpr::Todo
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
        EExpr::Var(Ty::Unresolved("?".to_string()), name.to_string())
    }

    /// Helper: make a resolved Int literal (should NOT trigger the hint).
    fn int_lit(n: i64) -> EExpr {
        EExpr::Lit(Ty::Builtin(BuiltinTy::Int), Literal::Int(n))
    }

    fn collect_hints(expr: &EExpr) -> Vec<ElabError> {
        let mut errors = Vec::new();
        check_unresolved_constructors(expr, "test context", None, &mut errors);
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
        let expr = EExpr::Var(Ty::Builtin(BuiltinTy::Int), "x".to_string());
        let hints = collect_hints(&expr);
        assert!(hints.is_empty());
    }

    #[test]
    fn lowercase_unresolved_no_hint() {
        let expr = EExpr::Var(Ty::Unresolved("?".to_string()), "pending".to_string());
        let hints = collect_hints(&expr);
        assert!(hints.is_empty(), "lowercase names should not trigger hint");
    }

    #[test]
    fn setlit_traversal() {
        let expr = EExpr::SetLit(
            Ty::Unresolved("?".to_string()),
            vec![int_lit(1), unresolved_var("Unknown"), int_lit(3)],
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
            )),
            Box::new(unresolved_var("Active")),
        );
        let hints = collect_hints(&expr);
        assert_eq!(hints.len(), 1, "should find hint in binop rhs");
        assert!(hints[0].help.as_ref().unwrap().contains("@Active"));
    }
}
