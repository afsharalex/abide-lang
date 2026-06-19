//! Match expression exhaustiveness checking.

use std::collections::HashMap;

use super::super::error::{ElabError, ErrorKind};
use super::super::types::{EEntity, EExpr, EPattern, Ty, VariantFieldsMap};

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
    variant_fields: &VariantFieldsMap,
    errors: &mut Vec<ElabError>,
) {
    match expr {
        EExpr::Match(scrut, arms, span) => {
            // Recurse into scrutinee and arm bodies first
            check_match_exhaustiveness(scrut, types, entities, variant_fields, errors);
            for (_, guard, body) in arms {
                if let Some(g) = guard {
                    check_match_exhaustiveness(g, types, entities, variant_fields, errors);
                }
                check_match_exhaustiveness(body, types, entities, variant_fields, errors);
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
            let Some((enum_name, constructors)) = resolve_to_enum_info(ty_to_check, types) else {
                return;
            };

            for (pat, _, _) in arms {
                check_pattern_shape(
                    pat,
                    enum_name,
                    constructors,
                    variant_fields,
                    span.unwrap_or(crate::span::Span { start: 0, end: 0 }),
                    errors,
                );
            }

            // Determine which constructors are not fully covered by the
            // unguarded arms. A top-level wildcard/variable covers everything;
            // otherwise a constructor is covered only when the arms matching it
            // exhaustively cover its *nested* field patterns (recursively), so a
            // partial nested pattern like `A { inner: X }` no longer over-covers
            // the whole `A` variant. Guarded arms are conservative — the guard
            // might be false — so they never contribute to coverage.
            let mut has_catchall = false;
            let mut unguarded: Vec<Vec<EPattern>> = Vec::new();
            for (pat, guard, _) in arms {
                if guard.is_some() {
                    continue;
                }
                if pattern_is_catchall(pat, constructors) {
                    has_catchall = true;
                    break;
                }
                unguarded.push(vec![pat.clone()]);
            }

            if has_catchall {
                return; // Wildcard or variable covers all remaining
            }

            let missing: Vec<&str> = constructors
                .iter()
                .filter(|ctor| {
                    let field_types = variant_field_types(enum_name, ctor, variant_fields);
                    let mut specialized = Vec::new();
                    specialize(
                        &unguarded,
                        constructors,
                        ctor,
                        &field_types,
                        &mut specialized,
                    );
                    let sub_types: Vec<Ty> = field_types.iter().map(|(_, t)| t.clone()).collect();
                    !matrix_exhaustive(&sub_types, &specialized, types, variant_fields)
                })
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
            check_match_exhaustiveness(l, types, entities, variant_fields, errors);
            check_match_exhaustiveness(r, types, entities, variant_fields, errors);
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
            check_match_exhaustiveness(e, types, entities, variant_fields, errors);
        }
        EExpr::Call(_, f, args, _) | EExpr::CallR(_, f, _, args, _) => {
            check_match_exhaustiveness(f, types, entities, variant_fields, errors);
            for a in args {
                check_match_exhaustiveness(a, types, entities, variant_fields, errors);
            }
        }
        EExpr::QualCall(_, _, _, args, _) => {
            for a in args {
                check_match_exhaustiveness(a, types, entities, variant_fields, errors);
            }
        }
        EExpr::Quant(_, _, _, _, body, _) | EExpr::Lam(_, _, body, _) => {
            check_match_exhaustiveness(body, types, entities, variant_fields, errors);
        }
        EExpr::Choose(_, _, _, predicate, _) => {
            if let Some(pred) = predicate {
                check_match_exhaustiveness(pred, types, entities, variant_fields, errors);
            }
        }
        EExpr::Let(binds, body, _) => {
            for (_, _, e) in binds {
                check_match_exhaustiveness(e, types, entities, variant_fields, errors);
            }
            check_match_exhaustiveness(body, types, entities, variant_fields, errors);
        }
        EExpr::IfElse(cond, then_e, else_e, _) => {
            check_match_exhaustiveness(cond, types, entities, variant_fields, errors);
            check_match_exhaustiveness(then_e, types, entities, variant_fields, errors);
            if let Some(el) = else_e {
                check_match_exhaustiveness(el, types, entities, variant_fields, errors);
            }
        }
        EExpr::Block(items, _) => {
            for e in items {
                check_match_exhaustiveness(e, types, entities, variant_fields, errors);
            }
        }
        EExpr::VarDecl(_, _, init, rest, _) => {
            check_match_exhaustiveness(init, types, entities, variant_fields, errors);
            check_match_exhaustiveness(rest, types, entities, variant_fields, errors);
        }
        EExpr::While(cond, _, body, _) => {
            check_match_exhaustiveness(cond, types, entities, variant_fields, errors);
            check_match_exhaustiveness(body, types, entities, variant_fields, errors);
        }
        EExpr::CtorRecord(_, _, _, args, _) | EExpr::StructCtor(_, _, args, _) => {
            for (_, e) in args {
                check_match_exhaustiveness(e, types, entities, variant_fields, errors);
            }
        }
        EExpr::MapUpdate(_, m, k, v, _) => {
            check_match_exhaustiveness(m, types, entities, variant_fields, errors);
            check_match_exhaustiveness(k, types, entities, variant_fields, errors);
            check_match_exhaustiveness(v, types, entities, variant_fields, errors);
        }
        EExpr::Index(_, m, k, _) => {
            check_match_exhaustiveness(m, types, entities, variant_fields, errors);
            check_match_exhaustiveness(k, types, entities, variant_fields, errors);
        }
        EExpr::SetComp(_, proj, _, _, source, filter, _) => {
            if let Some(p) = proj {
                check_match_exhaustiveness(p, types, entities, variant_fields, errors);
            }
            if let Some(source) = source {
                check_match_exhaustiveness(source, types, entities, variant_fields, errors);
            }
            check_match_exhaustiveness(filter, types, entities, variant_fields, errors);
        }
        EExpr::RelComp(_, projection, bindings, filter, _) => {
            check_match_exhaustiveness(projection, types, entities, variant_fields, errors);
            for binding in bindings {
                if let Some(source) = &binding.source {
                    check_match_exhaustiveness(source, types, entities, variant_fields, errors);
                }
            }
            check_match_exhaustiveness(filter, types, entities, variant_fields, errors);
        }
        EExpr::SetLit(_, elems, _) | EExpr::SeqLit(_, elems, _) | EExpr::TupleLit(_, elems, _) => {
            for e in elems {
                check_match_exhaustiveness(e, types, entities, variant_fields, errors);
            }
        }
        EExpr::MapLit(_, entries, _) => {
            for (k, v) in entries {
                check_match_exhaustiveness(k, types, entities, variant_fields, errors);
                check_match_exhaustiveness(v, types, entities, variant_fields, errors);
            }
        }
        EExpr::Saw(_, _, _, args, _) => {
            for e in args.iter().flatten() {
                check_match_exhaustiveness(e, types, entities, variant_fields, errors);
            }
        }
        EExpr::Aggregate(_, _, _, _, body, in_filter, _) => {
            check_match_exhaustiveness(body, types, entities, variant_fields, errors);
            if let Some(f) = in_filter {
                check_match_exhaustiveness(f, types, entities, variant_fields, errors);
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

/// Field declarations `(name, type)` for one constructor, in declared order.
///
/// A constructor that is registered in `variant_fields` always returns
/// `Some`: a nullary one yields the empty field list, a record one yields its
/// declared fields. The empty fallback below is reached only if the
/// enum/constructor is *absent* from `variant_fields`, which cannot occur for
/// an enum resolved from a declaration during elaboration — `variant_fields`
/// is populated for every declared enum. It is therefore purely defensive: it
/// never panics and never approximates coverage for well-formed input.
pub(super) fn variant_field_types(
    enum_name: &str,
    ctor: &str,
    variant_fields: &VariantFieldsMap,
) -> Vec<(String, Ty)> {
    variant_fields
        .get(enum_name)
        .and_then(|variants| {
            variants
                .iter()
                .find(|(variant, _)| variant == ctor)
                .map(|(_, fields)| fields.clone())
        })
        // abide-audit: allow-silent-fallback -- defensive empty for an enum/constructor absent from variant_fields; unreachable for declared enums, so no coverage is approximated for well-formed input
        .unwrap_or_default()
}

/// Specialize a pattern matrix on constructor `ctor`: each row whose head
/// (column 0, a value of the enum with constructors `head_ctors`) can match
/// `ctor` contributes a row where the head is replaced by `ctor`'s field
/// sub-patterns (in `field_types` order, defaulting to wildcard) followed by
/// the row's remaining columns. Rows that cannot match `ctor` are dropped.
pub(super) fn specialize(
    matrix: &[Vec<EPattern>],
    head_ctors: &[String],
    ctor: &str,
    field_types: &[(String, Ty)],
    out: &mut Vec<Vec<EPattern>>,
) {
    for row in matrix {
        let Some((head, rest)) = row.split_first() else {
            continue;
        };
        specialize_head(head, rest, head_ctors, ctor, field_types, out);
    }
}

fn specialize_head(
    head: &EPattern,
    rest: &[EPattern],
    head_ctors: &[String],
    ctor: &str,
    field_types: &[(String, Ty)],
    out: &mut Vec<Vec<EPattern>>,
) {
    match head {
        EPattern::Wild => push_wildcard_expansion(rest, field_types, out),
        EPattern::Var(name) => {
            if head_ctors.iter().any(|c| c == name) {
                // A bare constructor reference (nullary) only matches its own
                // constructor.
                if name == ctor {
                    push_wildcard_expansion(rest, field_types, out);
                }
            } else {
                // A binding catches everything, covering this constructor.
                push_wildcard_expansion(rest, field_types, out);
            }
        }
        EPattern::Ctor(name, fields) => {
            if name == ctor {
                let mut expanded: Vec<EPattern> = field_types
                    .iter()
                    .map(|(fname, _)| {
                        fields
                            .iter()
                            .find(|(pf, _)| pf == fname)
                            .map(|(_, p)| p.clone())
                            .unwrap_or(EPattern::Wild)
                    })
                    .collect();
                expanded.extend_from_slice(rest);
                out.push(expanded);
            }
        }
        EPattern::Or(left, right) => {
            specialize_head(left, rest, head_ctors, ctor, field_types, out);
            specialize_head(right, rest, head_ctors, ctor, field_types, out);
        }
    }
}

fn push_wildcard_expansion(
    rest: &[EPattern],
    field_types: &[(String, Ty)],
    out: &mut Vec<Vec<EPattern>>,
) {
    let mut row: Vec<EPattern> = field_types.iter().map(|_| EPattern::Wild).collect();
    row.extend_from_slice(rest);
    out.push(row);
}

/// Standard constructor-specialization exhaustiveness over a pattern matrix:
/// does `matrix` (rows of column patterns aligned with `col_types`) cover every
/// value of the column tuple? Abide patterns have no literal patterns, so a
/// non-enum column (int/bool/string/entity/…) admits only catch-alls, each of
/// which covers the whole column.
pub(super) fn matrix_exhaustive(
    col_types: &[Ty],
    matrix: &[Vec<EPattern>],
    types: &HashMap<String, Ty>,
    variant_fields: &VariantFieldsMap,
) -> bool {
    let Some((head_ty, rest_types)) = col_types.split_first() else {
        // No columns remain: covered iff at least one row survived.
        return !matrix.is_empty();
    };

    if let Some((enum_name, ctors)) = resolve_to_enum_info(head_ty, types) {
        ctors.iter().all(|ctor| {
            let field_types = variant_field_types(enum_name, ctor, variant_fields);
            let mut sub = Vec::new();
            specialize(matrix, ctors, ctor, &field_types, &mut sub);
            let mut sub_types: Vec<Ty> = field_types.iter().map(|(_, t)| t.clone()).collect();
            sub_types.extend_from_slice(rest_types);
            matrix_exhaustive(&sub_types, &sub, types, variant_fields)
        })
    } else {
        // Non-enum column: keep only catch-all rows (the sole possibility),
        // drop the column from each, and recurse on the remaining columns.
        let mut sub = Vec::new();
        for row in matrix {
            if let Some((head, rest)) = row.split_first() {
                if pattern_is_catchall(head, &[]) {
                    sub.push(rest.to_vec());
                }
            }
        }
        matrix_exhaustive(rest_types, &sub, types, variant_fields)
    }
}

pub(super) fn check_pattern_shape(
    pat: &EPattern,
    enum_name: &str,
    constructors: &[String],
    variant_fields: &VariantFieldsMap,
    span: crate::span::Span,
    errors: &mut Vec<ElabError>,
) {
    match pat {
        EPattern::Ctor(name, fields) => {
            if !constructors.iter().any(|ctor| ctor == name) {
                return;
            }
            let declared_fields = variant_fields
                .get(enum_name)
                .and_then(|variants| {
                    variants
                        .iter()
                        .find(|(variant, _)| variant == name)
                        .map(|(_, fields)| fields.as_slice())
                })
                .unwrap_or(&[]);
            if fields.is_empty() && declared_fields.is_empty() {
                errors.push(ElabError::with_span(
                    ErrorKind::TypeMismatch,
                    format!(
                        "unit constructor pattern `{name} {{}}` should be written `{name}`; \
                         braces are only for destructuring constructor fields"
                    ),
                    String::new(),
                    span,
                ));
            }
        }
        EPattern::Or(left, right) => {
            check_pattern_shape(left, enum_name, constructors, variant_fields, span, errors);
            check_pattern_shape(right, enum_name, constructors, variant_fields, span, errors);
        }
        EPattern::Var(_) | EPattern::Wild => {}
    }
}

pub(super) fn resolve_to_enum_info<'a>(
    ty: &'a Ty,
    types: &'a HashMap<String, Ty>,
) -> Option<(&'a str, &'a Vec<String>)> {
    let mut current = ty;
    // Limit iterations to prevent infinite loops on cyclic aliases
    for _ in 0..20 {
        match current {
            Ty::Enum(name, ctors) => return Some((name, ctors)),
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
        if let Some(entity) = entities.get(base_ty.name()) {
            if let Some(field) = entity.fields.iter().find(|f| f.name == *field_name) {
                return Some(field.ty.clone());
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::elab::types::{BuiltinTy, EAction, EField, EInvariant, Literal};

    fn bool_lit(value: bool) -> EExpr {
        EExpr::Lit(Ty::Builtin(BuiltinTy::Bool), Literal::Bool(value), None)
    }

    fn status_ty() -> Ty {
        Ty::Enum(
            "Status".to_string(),
            vec!["Open".to_string(), "Closed".to_string()],
        )
    }

    fn constructors() -> Vec<String> {
        vec!["Open".to_string(), "Closed".to_string()]
    }

    fn entity(name: &str, fields: Vec<EField>) -> EEntity {
        EEntity {
            name: name.to_string(),
            fields,
            actions: Vec::<EAction>::new(),
            derived_fields: vec![],
            invariants: Vec::<EInvariant>::new(),
            fsm_decls: vec![],
            span: None,
        }
    }

    fn field(name: &str, ty: Ty) -> EField {
        EField {
            name: name.to_string(),
            ty,
            default: None,
            span: None,
        }
    }

    #[test]
    fn pattern_is_catchall_distinguishes_bindings_from_constructors() {
        let ctors = constructors();
        assert!(pattern_is_catchall(&EPattern::Wild, &ctors));
        assert!(pattern_is_catchall(
            &EPattern::Var("binding".to_string()),
            &ctors
        ));
        assert!(!pattern_is_catchall(
            &EPattern::Var("Open".to_string()),
            &ctors
        ));
        assert!(pattern_is_catchall(
            &EPattern::Or(
                Box::new(EPattern::Ctor("Open".to_string(), vec![])),
                Box::new(EPattern::Wild),
            ),
            &ctors
        ));
        assert!(!pattern_is_catchall(
            &EPattern::Ctor("Open".to_string(), vec![]),
            &ctors
        ));
    }

    #[test]
    fn check_pattern_shape_rejects_braces_for_unit_constructor_patterns() {
        let mut variant_fields = VariantFieldsMap::new();
        variant_fields.insert(
            "Status".to_string(),
            vec![
                ("Open".to_string(), vec![]),
                (
                    "Closed".to_string(),
                    vec![("reason".to_string(), Ty::Builtin(BuiltinTy::String))],
                ),
            ],
        );
        let mut errors = Vec::new();
        check_pattern_shape(
            &EPattern::Or(
                Box::new(EPattern::Ctor("Open".to_string(), vec![])),
                Box::new(EPattern::Ctor(
                    "Closed".to_string(),
                    vec![("reason".to_string(), EPattern::Var("r".to_string()))],
                )),
            ),
            "Status",
            &constructors(),
            &variant_fields,
            crate::span::Span { start: 1, end: 2 },
            &mut errors,
        );
        assert_eq!(errors.len(), 1);
        assert!(errors[0].message.contains("unit constructor pattern"));

        check_pattern_shape(
            &EPattern::Ctor("Missing".to_string(), vec![]),
            "Status",
            &constructors(),
            &variant_fields,
            crate::span::Span { start: 3, end: 4 },
            &mut errors,
        );
        assert_eq!(
            errors.len(),
            1,
            "unknown constructors should be ignored by shape checks"
        );

        check_pattern_shape(
            &EPattern::Ctor("Closed".to_string(), vec![]),
            "Status",
            &constructors(),
            &variant_fields,
            crate::span::Span { start: 5, end: 6 },
            &mut errors,
        );
        assert_eq!(
            errors.len(),
            1,
            "record constructors with declared fields should not be treated as unit constructors"
        );
    }

    #[test]
    fn resolve_to_enum_info_follows_inline_alias_named_and_entity_types() {
        let mut types = HashMap::new();
        types.insert("Status".to_string(), status_ty());
        types.insert(
            "TicketStatus".to_string(),
            Ty::Alias(
                "TicketStatus".to_string(),
                Box::new(Ty::Named("Status".to_string())),
            ),
        );

        let direct_status = status_ty();
        let (name, ctors) = resolve_to_enum_info(&direct_status, &types).unwrap();
        assert_eq!(name, "Status");
        assert_eq!(ctors, &constructors());

        let inline_alias = Ty::Alias(
            "Inline".to_string(),
            Box::new(Ty::Named("TicketStatus".to_string())),
        );
        let (name, ctors) = resolve_to_enum_info(&inline_alias, &types).unwrap();
        assert_eq!(name, "Status");
        assert_eq!(ctors, &constructors());

        let entity_status = Ty::Entity("Status".to_string());
        let (name, _) = resolve_to_enum_info(&entity_status, &types).unwrap();
        assert_eq!(name, "Status");
        assert!(resolve_to_enum_info(&Ty::Named("Missing".to_string()), &types).is_none());
    }

    #[test]
    fn resolve_field_type_handles_entity_named_and_nested_field_access() {
        let mut entities = HashMap::new();
        entities.insert(
            "Ticket".to_string(),
            entity(
                "Ticket",
                vec![
                    field("status", status_ty()),
                    field("owner", Ty::Entity("User".to_string())),
                ],
            ),
        );
        entities.insert(
            "User".to_string(),
            entity("User", vec![field("status", status_ty())]),
        );

        let status = EExpr::Field(
            Ty::Error,
            Box::new(EExpr::Var(
                Ty::Entity("Ticket".to_string()),
                "ticket".to_string(),
                None,
            )),
            "status".to_string(),
            None,
        );
        let resolved = resolve_field_type(&status, &HashMap::new(), &entities).unwrap();
        assert_eq!(resolved.name(), "Status");

        let named_status = EExpr::Field(
            Ty::Error,
            Box::new(EExpr::Var(
                Ty::Named("Ticket".to_string()),
                "ticket".to_string(),
                None,
            )),
            "status".to_string(),
            None,
        );
        let resolved = resolve_field_type(&named_status, &HashMap::new(), &entities).unwrap();
        assert_eq!(resolved.name(), "Status");

        let nested_status = EExpr::Field(
            Ty::Error,
            Box::new(EExpr::Field(
                Ty::Error,
                Box::new(EExpr::Var(
                    Ty::Entity("Ticket".to_string()),
                    "ticket".to_string(),
                    None,
                )),
                "owner".to_string(),
                None,
            )),
            "status".to_string(),
            None,
        );
        let resolved = resolve_field_type(&nested_status, &HashMap::new(), &entities).unwrap();
        assert_eq!(resolved.name(), "Status");
        assert!(resolve_field_type(&bool_lit(true), &HashMap::new(), &entities).is_none());
    }

    #[test]
    fn check_match_exhaustiveness_reports_missing_constructors_and_recurses() {
        let types = HashMap::from([("Status".to_string(), status_ty())]);
        let scrutinee = EExpr::Var(status_ty(), "status".to_string(), None);
        let nested_non_exhaustive = EExpr::Match(
            Box::new(scrutinee.clone()),
            vec![(EPattern::Var("Open".to_string()), None, bool_lit(true))],
            Some(crate::span::Span { start: 10, end: 20 }),
        );
        let expr = EExpr::Match(
            Box::new(scrutinee),
            vec![(
                EPattern::Var("Open".to_string()),
                Some(bool_lit(true)),
                nested_non_exhaustive,
            )],
            Some(crate::span::Span { start: 1, end: 9 }),
        );
        let mut errors = Vec::new();
        check_match_exhaustiveness(
            &expr,
            &types,
            &HashMap::new(),
            &VariantFieldsMap::new(),
            &mut errors,
        );
        assert_eq!(errors.len(), 2);
        assert!(errors.iter().all(|error| error.message.contains("Closed")));
    }

    #[test]
    fn nested_constructor_pattern_does_not_over_cover_outer_variant() {
        // enum Inner = X | Y
        // enum Outer = A { inner: Inner } | B
        let inner_ty = Ty::Enum("Inner".to_string(), vec!["X".to_string(), "Y".to_string()]);
        let outer_ty = Ty::Enum("Outer".to_string(), vec!["A".to_string(), "B".to_string()]);
        let types = HashMap::from([
            ("Inner".to_string(), inner_ty),
            ("Outer".to_string(), outer_ty.clone()),
        ]);
        let mut variant_fields = VariantFieldsMap::new();
        variant_fields.insert(
            "Outer".to_string(),
            vec![
                (
                    "A".to_string(),
                    vec![("inner".to_string(), Ty::Named("Inner".to_string()))],
                ),
                ("B".to_string(), vec![]),
            ],
        );
        variant_fields.insert(
            "Inner".to_string(),
            vec![("X".to_string(), vec![]), ("Y".to_string(), vec![])],
        );

        let scrut = || EExpr::Var(outer_ty.clone(), "o".to_string(), None);
        // Nullary constructors are written bare (parsed as `Var`); a record
        // constructor like `A { inner: ... }` keeps its field sub-patterns.
        let a_inner = |inner_ctor: &str| {
            EPattern::Ctor(
                "A".to_string(),
                vec![("inner".to_string(), EPattern::Var(inner_ctor.to_string()))],
            )
        };
        let b_pat = || EPattern::Var("B".to_string());
        let check = |expr: &EExpr| {
            let mut errors = Vec::new();
            check_match_exhaustiveness(expr, &types, &HashMap::new(), &variant_fields, &mut errors);
            errors
        };

        // match o { A { inner: X } => _; B => _ } is NOT exhaustive: A { inner: Y }
        // is uncovered, so a nested constructor pattern must not over-cover A.
        let non_exhaustive = EExpr::Match(
            Box::new(scrut()),
            vec![
                (a_inner("X"), None, bool_lit(true)),
                (b_pat(), None, bool_lit(false)),
            ],
            Some(crate::span::Span { start: 1, end: 2 }),
        );
        let errors = check(&non_exhaustive);
        assert_eq!(
            errors.len(),
            1,
            "nested non-exhaustive match must report A as uncovered: {errors:?}"
        );
        assert!(matches!(errors[0].kind, ErrorKind::NonExhaustiveMatch));

        // Adding A { inner: Y } makes it exhaustive (X | Y covers Inner).
        let exhaustive = EExpr::Match(
            Box::new(scrut()),
            vec![
                (a_inner("X"), None, bool_lit(true)),
                (a_inner("Y"), None, bool_lit(false)),
                (b_pat(), None, bool_lit(false)),
            ],
            Some(crate::span::Span { start: 1, end: 2 }),
        );
        assert!(
            check(&exhaustive).is_empty(),
            "nested exhaustive match must not error"
        );

        // A binding at the nested field fully covers the whole A variant.
        let binding_covers = EExpr::Match(
            Box::new(scrut()),
            vec![
                (
                    EPattern::Ctor(
                        "A".to_string(),
                        vec![("inner".to_string(), EPattern::Var("i".to_string()))],
                    ),
                    None,
                    bool_lit(true),
                ),
                (b_pat(), None, bool_lit(false)),
            ],
            Some(crate::span::Span { start: 1, end: 2 }),
        );
        assert!(
            check(&binding_covers).is_empty(),
            "a binding at a nested field must cover the entire variant"
        );
    }
}
