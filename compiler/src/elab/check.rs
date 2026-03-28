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

    for ty in env.types.values() {
        errors.extend(check_type(ty));
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
        consts: env.consts.clone(),
        fns: env.fns.clone(),
    };

    (result, errors)
}

fn mk_etype(name: &str, ty: &Ty) -> EType {
    match ty {
        Ty::Enum(_, vs) => EType {
            name: name.to_owned(),
            variants: vs.iter().map(|v| EVariant::Simple(v.clone())).collect(),
            ty: ty.clone(),
        },
        Ty::Record(_, fs) => EType {
            name: name.to_owned(),
            variants: vec![EVariant::Record(name.to_owned(), fs.clone())],
            ty: ty.clone(),
        },
        _ => EType {
            name: name.to_owned(),
            variants: Vec::new(),
            ty: ty.clone(),
        },
    }
}

// ── Type well-formedness ─────────────────────────────────────────────

fn check_type(ty: &Ty) -> Vec<ElabError> {
    match ty {
        Ty::Enum(name, ctors) => {
            let dups = find_duplicates(ctors);
            dups.iter()
                .map(|d| {
                    ElabError::new(
                        ErrorKind::DuplicateDecl,
                        format!("duplicate constructor {d} in type {name}"),
                        format!("type {name}"),
                    )
                })
                .collect()
        }
        Ty::Record(name, fields) => {
            let field_names: Vec<&String> = fields.iter().map(|(n, _)| n).collect();
            let dups = find_duplicates(&field_names);
            dups.iter()
                .map(|d| {
                    ElabError::new(
                        ErrorKind::DuplicateDecl,
                        format!("duplicate field {d} in record {name}"),
                        format!("type {name}"),
                    )
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
            vec![ElabError::new(
                ErrorKind::InvalidDefault,
                format!("{v} is not a constructor of {}", field.ty.name()),
                format!("entity {entity_name}, field {}", field.name),
            )]
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
            errors.push(ElabError::new(
                ErrorKind::TypeMismatch,
                "requires expression should be Bool",
                &ctx,
            ));
        }
    }

    // Check primed assignments target known fields
    for expr in &action.body {
        errors.extend(check_assignment(entity, &ctx, expr));
    }

    errors
}

fn check_assignment(entity: &EEntity, ctx: &str, expr: &EExpr) -> Vec<ElabError> {
    if let EExpr::Assign(_, lhs, _) = expr {
        if let EExpr::Prime(_, inner) = lhs.as_ref() {
            if let EExpr::Var(_, field_name) = inner.as_ref() {
                let field_names: Vec<&str> =
                    entity.fields.iter().map(|f| f.name.as_str()).collect();
                if !field_names.contains(&field_name.as_str()) {
                    return vec![ElabError::new(
                        ErrorKind::InvalidPrime,
                        format!("{field_name} is not a field of {}", entity.name),
                        ctx,
                    )];
                }
            }
        }
    }
    Vec::new()
}

// ── System well-formedness ───────────────────────────────────────────

fn check_system(env: &Env, system: &ESystem) -> Vec<ElabError> {
    let mut errors = Vec::new();

    for entity_name in &system.uses {
        if env.lookup_entity(entity_name).is_none() {
            errors.push(ElabError::new(
                ErrorKind::UndefinedRef,
                format!("system {} uses unknown entity {entity_name}", system.name),
                format!("system {}", system.name),
            ));
        }
    }

    for scope in &system.scopes {
        if scope.lo < 0 || scope.hi < scope.lo {
            errors.push(ElabError::new(
                ErrorKind::InvalidScope,
                format!(
                    "scope {} has invalid range {}..{}",
                    scope.entity, scope.lo, scope.hi
                ),
                format!("system {}", system.name),
            ));
        }
    }

    errors
}

// ── Helpers ──────────────────────────────────────────────────────────

fn is_bool_expr(e: &EExpr) -> bool {
    match e.ty() {
        Ty::Builtin(BuiltinTy::Bool) | Ty::Unresolved(_) => true, // might be Bool; don't error
        _ => false,
    }
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
    for f in &env.fns {
        all_names.insert(f.name.clone());
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
    for f in &env.fns {
        let mut referenced = HashSet::new();
        let bound: HashSet<String> = f.params.iter().map(|(n, _)| n.clone()).collect();
        collect_name_refs(&f.body, &all_names, &bound, &mut referenced);
        deps.insert(f.name.clone(), referenced);
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
