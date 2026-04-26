//! Match expression exhaustiveness checking.

use std::collections::{HashMap, HashSet};

use super::super::error::{ElabError, ErrorKind};
use super::super::types::{EEntity, EExpr, EPattern, Ty};

/// Walk an expression tree and check every match expression for exhaustiveness.
///
/// For each match whose scrutinee has an enum type, verifies that the arms
/// cover all constructors. Wildcards (`_`) and variable patterns cover all
/// remaining constructors. Guarded arms are treated conservatively — a guard
/// does not guarantee coverage (what if the guard is false?).
pub(super) fn check_match_exhaustiveness(
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
            let resolved_field_ty = if matches!(scrut_ty, Ty::Error | Ty::Named(_)) {
                resolve_field_type(scrut, types, entities)
            } else {
                None
            };
            let ty_to_check = resolved_field_ty.as_ref().unwrap_or(&scrut_ty);
            let Some(constructors) = resolve_to_enum(ty_to_check, types) else {
                return;
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
                    crate::messages::non_exhaustive_match(&missing),
                    String::new(),
                );
                err.span = *span;
                err.help = Some(crate::messages::HELP_NON_EXHAUSTIVE_MATCH.into());
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
        | EExpr::Until(_, l, r, _)
        | EExpr::Since(_, l, r, _) => {
            check_match_exhaustiveness(l, types, entities, errors);
            check_match_exhaustiveness(r, types, entities, errors);
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
        EExpr::Choose(_, _, _, predicate, _) => {
            if let Some(pred) = predicate {
                check_match_exhaustiveness(pred, types, entities, errors);
            }
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
        EExpr::CtorRecord(_, _, _, args, _) | EExpr::StructCtor(_, _, args, _) => {
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
        EExpr::Saw(_, _, _, args, _) => {
            for e in args.iter().flatten() {
                check_match_exhaustiveness(e, types, entities, errors);
            }
        }
        EExpr::Aggregate(_, _, _, _, body, in_filter, _) => {
            check_match_exhaustiveness(body, types, entities, errors);
            if let Some(f) = in_filter {
                check_match_exhaustiveness(f, types, entities, errors);
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
pub(super) fn pattern_is_catchall(pat: &EPattern, constructors: &[String]) -> bool {
    match pat {
        EPattern::Wild => true,
        EPattern::Var(name) => !constructors.iter().any(|c| c == name),
        EPattern::Or(left, right) => {
            pattern_is_catchall(left, constructors) || pattern_is_catchall(right, constructors)
        }
        EPattern::Ctor(..) => false,
    }
}

/// Collect constructor names covered by an unguarded pattern.
pub(super) fn collect_covered_ctors<'a>(
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
pub(super) fn resolve_to_enum<'a>(
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
            Ty::Named(name) | Ty::Entity(name) => {
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
#[allow(clippy::only_used_in_recursion)]
pub(super) fn resolve_field_type(
    expr: &EExpr,
    types: &HashMap<String, Ty>,
    entities: &HashMap<String, EEntity>,
) -> Option<Ty> {
    if let EExpr::Field(_, base, field_name, _) = expr {
        let base_ty = base.ty();
        // Resolve entity name from the base expression's type
        let entity_name = match &base_ty {
            Ty::Entity(name) => Some(name.as_str()),
            Ty::Named(name) if entities.contains_key(name.as_str()) => Some(name.as_str()),
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
