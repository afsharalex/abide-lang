//! Constructor record well-formedness validation.

use std::collections::HashSet;

use super::super::error::{ElabError, ErrorKind};
use super::super::types::{EExpr, Ty, VariantFieldsMap};

/// Walk an `EEventAction` tree for ctor/struct-ctor well-formedness checks.
pub(super) fn walk_event_action_for_ctor_check(
    ea: &super::super::types::EEventAction,
    variant_fields: &VariantFieldsMap,
    errors: &mut Vec<ElabError>,
) {
    use super::super::types::EEventAction;
    match ea {
        EEventAction::Choose(_, _, guard, body) => {
            check_ctor_records_in_expr(guard, variant_fields, errors);
            for child in body {
                walk_event_action_for_ctor_check(child, variant_fields, errors);
            }
        }
        EEventAction::ForAll(_, _, body) => {
            for child in body {
                walk_event_action_for_ctor_check(child, variant_fields, errors);
            }
        }
        EEventAction::Create(_, _store, fields) => {
            for (_, e) in fields {
                check_ctor_records_in_expr(e, variant_fields, errors);
            }
        }
        EEventAction::CrossCall(_, _, args) => {
            for a in args {
                check_ctor_records_in_expr(a, variant_fields, errors);
            }
        }
        EEventAction::LetCrossCall(_, _, _, args) => {
            for a in args {
                check_ctor_records_in_expr(a, variant_fields, errors);
            }
        }
        EEventAction::Match(scrutinee, arms) => {
            if let super::super::types::EMatchScrutinee::CrossCall(_, _, args) = scrutinee {
                for a in args {
                    check_ctor_records_in_expr(a, variant_fields, errors);
                }
            }
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    check_ctor_records_in_expr(guard, variant_fields, errors);
                }
                for child in &arm.body {
                    walk_event_action_for_ctor_check(child, variant_fields, errors);
                }
            }
        }
        EEventAction::Apply(target, _, refs, args) => {
            check_ctor_records_in_expr(target, variant_fields, errors);
            for r in refs {
                check_ctor_records_in_expr(r, variant_fields, errors);
            }
            for a in args {
                check_ctor_records_in_expr(a, variant_fields, errors);
            }
        }
        EEventAction::Expr(e) => {
            check_ctor_records_in_expr(e, variant_fields, errors);
        }
    }
}

/// Walk an expression tree and check all `EExpr::CtorRecord` for:
/// - unknown fields (not declared in the constructor)
/// - duplicate fields
/// - missing fields (arity mismatch)
///   Reports errors via `ElabError`.
pub(super) fn check_ctor_records_in_expr(
    expr: &EExpr,
    variant_fields: &VariantFieldsMap,
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
                let user_field_names: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();

                // Collect ALL enums that have a constructor with this name
                let mut all_matches: Vec<(&str, &[(String, Ty)])> = Vec::new();
                for (ename, variants) in variant_fields {
                    for (vname, vfields) in variants {
                        if vname == ctor_name {
                            all_matches.push((ename.as_str(), vfields.as_slice()));
                        }
                    }
                }

                match all_matches.as_slice() {
                    // Unique constructor name — use it (validates unknown fields)
                    [single] => {
                        declared = Some(single.1);
                        enum_name_found = Some(single.0);
                    }
                    // Ambiguous: disambiguate by field names
                    [_, ..] => {
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
                            enum_names.sort_unstable();
                            let mut err = ElabError::new(
                                ErrorKind::AmbiguousRef,
                                format!(
                                    "ambiguous constructor '{ctor_name}' — found in enums: {}",
                                    enum_names.join(", "),
                                ),
                                ctor_name.clone(),
                            );
                            err.span = *span;
                            err.help = Some(crate::messages::HELP_AMBIGUOUS_CTOR.into());
                            errors.push(err);
                            return;
                        }
                    }
                    [] => {}
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
        | EExpr::Until(_, l, r, _)
        | EExpr::Since(_, l, r, _) => {
            check_ctor_records_in_expr(l, variant_fields, errors);
            check_ctor_records_in_expr(r, variant_fields, errors);
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
        EExpr::Quant(_, _, _, _, body, _) | EExpr::Lam(_, _, body, _) => {
            check_ctor_records_in_expr(body, variant_fields, errors);
        }
        EExpr::Choose(_, _, _, predicate, _) => {
            if let Some(pred) = predicate {
                check_ctor_records_in_expr(pred, variant_fields, errors);
            }
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
        EExpr::SetComp(_, proj, _, _, source, filter, _) => {
            if let Some(p) = proj {
                check_ctor_records_in_expr(p, variant_fields, errors);
            }
            if let Some(source) = source {
                check_ctor_records_in_expr(source, variant_fields, errors);
            }
            check_ctor_records_in_expr(filter, variant_fields, errors);
        }
        EExpr::RelComp(_, projection, bindings, filter, _) => {
            check_ctor_records_in_expr(projection, variant_fields, errors);
            for binding in bindings {
                if let Some(source) = &binding.source {
                    check_ctor_records_in_expr(source, variant_fields, errors);
                }
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
        EExpr::Saw(_, _, _, args, _) => {
            for e in args.iter().flatten() {
                check_ctor_records_in_expr(e, variant_fields, errors);
            }
        }
        EExpr::Aggregate(_, _, _, _, body, in_filter, _) => {
            check_ctor_records_in_expr(body, variant_fields, errors);
            if let Some(f) = in_filter {
                check_ctor_records_in_expr(f, variant_fields, errors);
            }
        }
        EExpr::StructCtor(_, name, fields, span) => {
            // Struct constructors are only valid as system field defaults.
            // In general expression positions they're rejected.
            errors.push(if let Some(sp) = span {
                ElabError::with_span(
                    ErrorKind::TypeMismatch,
                    format!(
                        "struct constructor `{name} {{ ... }}` is not supported as a general expression; \
                         it can only be used as a system field default"
                    ),
                    "",
                    *sp,
                )
            } else {
                ElabError::new(
                    ErrorKind::TypeMismatch,
                    format!(
                        "struct constructor `{name} {{ ... }}` is not supported as a general expression; \
                         it can only be used as a system field default"
                    ),
                    "",
                )
            });
            // Still recurse to catch nested issues
            for (_, e) in fields {
                check_ctor_records_in_expr(e, variant_fields, errors);
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
    use crate::elab::types::{
        BuiltinTy, EEventAction, EMatchArm, EMatchScrutinee, EPattern, Literal,
    };

    fn int_lit(value: i64) -> EExpr {
        EExpr::Lit(Ty::Builtin(BuiltinTy::Int), Literal::Int(value), None)
    }

    fn bool_lit(value: bool) -> EExpr {
        EExpr::Lit(Ty::Builtin(BuiltinTy::Bool), Literal::Bool(value), None)
    }

    fn variant_fields() -> VariantFieldsMap {
        VariantFieldsMap::from([
            (
                "Result".to_string(),
                vec![
                    (
                        "Ok".to_string(),
                        vec![
                            ("value".to_string(), Ty::Builtin(BuiltinTy::Int)),
                            ("code".to_string(), Ty::Builtin(BuiltinTy::Int)),
                        ],
                    ),
                    (
                        "Err".to_string(),
                        vec![("message".to_string(), Ty::Builtin(BuiltinTy::String))],
                    ),
                ],
            ),
            (
                "Other".to_string(),
                vec![(
                    "Ok".to_string(),
                    vec![("reason".to_string(), Ty::Builtin(BuiltinTy::String))],
                )],
            ),
            (
                "Left".to_string(),
                vec![(
                    "Shared".to_string(),
                    vec![("a".to_string(), Ty::Builtin(BuiltinTy::Int))],
                )],
            ),
            (
                "Right".to_string(),
                vec![(
                    "Shared".to_string(),
                    vec![("b".to_string(), Ty::Builtin(BuiltinTy::Bool))],
                )],
            ),
        ])
    }

    fn ctor(ty: Ty, qual: Option<&str>, name: &str, fields: Vec<(&str, EExpr)>) -> EExpr {
        EExpr::CtorRecord(
            ty,
            qual.map(str::to_string),
            name.to_string(),
            fields
                .into_iter()
                .map(|(field, expr)| (field.to_string(), expr))
                .collect(),
            Some(crate::span::Span { start: 1, end: 2 }),
        )
    }

    fn collect_ctor_errors(expr: &EExpr) -> Vec<ElabError> {
        let mut errors = Vec::new();
        check_ctor_records_in_expr(expr, &variant_fields(), &mut errors);
        errors
    }

    #[test]
    fn ctor_record_checker_validates_scoped_typed_global_and_ambiguous_records() {
        let typed_ok = ctor(
            Ty::Enum(
                "Result".to_string(),
                vec!["Ok".to_string(), "Err".to_string()],
            ),
            None,
            "Ok",
            vec![("value", int_lit(1)), ("code", int_lit(200))],
        );
        assert!(collect_ctor_errors(&typed_ok).is_empty());

        let scoped_ok = ctor(
            Ty::Error,
            Some("Other"),
            "Ok",
            vec![(
                "reason",
                EExpr::Lit(
                    Ty::Builtin(BuiltinTy::String),
                    Literal::Str("x".to_string()),
                    None,
                ),
            )],
        );
        assert!(collect_ctor_errors(&scoped_ok).is_empty());

        let disambiguated = ctor(Ty::Error, None, "Shared", vec![("b", bool_lit(true))]);
        assert!(collect_ctor_errors(&disambiguated).is_empty());

        let ambiguous = ctor(Ty::Error, None, "Shared", vec![]);
        let ambiguous_errors = collect_ctor_errors(&ambiguous);
        assert_eq!(ambiguous_errors.len(), 1);
        assert_eq!(ambiguous_errors[0].kind, ErrorKind::AmbiguousRef);

        let unknown = ctor(
            Ty::Enum(
                "Result".to_string(),
                vec!["Ok".to_string(), "Err".to_string()],
            ),
            None,
            "Ok",
            vec![("extra", int_lit(1))],
        );
        let unknown_errors = collect_ctor_errors(&unknown);
        assert!(unknown_errors
            .iter()
            .any(|error| error.message.contains("unknown field 'extra'")));
        assert!(unknown_errors
            .iter()
            .any(|error| error.message.contains("missing")));

        let duplicate = ctor(
            Ty::Enum(
                "Result".to_string(),
                vec!["Ok".to_string(), "Err".to_string()],
            ),
            None,
            "Ok",
            vec![
                ("value", int_lit(1)),
                ("value", int_lit(2)),
                ("code", int_lit(3)),
            ],
        );
        let duplicate_errors = collect_ctor_errors(&duplicate);
        assert_eq!(duplicate_errors.len(), 1);
        assert_eq!(duplicate_errors[0].kind, ErrorKind::DuplicateDecl);

        let missing = ctor(
            Ty::Enum(
                "Result".to_string(),
                vec!["Ok".to_string(), "Err".to_string()],
            ),
            None,
            "Ok",
            vec![("value", int_lit(1))],
        );
        let missing_errors = collect_ctor_errors(&missing);
        assert_eq!(missing_errors.len(), 1);
        assert!(missing_errors[0].message.contains("missing: code"));

        let unknown_ctor = ctor(Ty::Error, None, "NotKnown", vec![("field", int_lit(1))]);
        assert!(collect_ctor_errors(&unknown_ctor).is_empty());
    }

    #[test]
    fn ctor_record_checker_recurses_into_struct_constructors_and_event_actions() {
        let nested_bad = ctor(
            Ty::Enum(
                "Result".to_string(),
                vec!["Ok".to_string(), "Err".to_string()],
            ),
            None,
            "Ok",
            vec![("extra", int_lit(1))],
        );
        let struct_expr = EExpr::StructCtor(
            Ty::Error,
            "Payload".to_string(),
            vec![("inner".to_string(), nested_bad.clone())],
            Some(crate::span::Span { start: 3, end: 4 }),
        );
        let struct_errors = collect_ctor_errors(&struct_expr);
        assert!(struct_errors
            .iter()
            .any(|error| error.message.contains("struct constructor")));
        assert!(struct_errors
            .iter()
            .any(|error| error.message.contains("unknown field 'extra'")));

        let event_action = EEventAction::Choose(
            "x".to_string(),
            Ty::Builtin(BuiltinTy::Int),
            nested_bad.clone(),
            vec![
                EEventAction::Create(
                    "Ticket".to_string(),
                    None,
                    vec![("status".to_string(), nested_bad.clone())],
                ),
                EEventAction::Match(
                    EMatchScrutinee::CrossCall(
                        "Sys".to_string(),
                        "cmd".to_string(),
                        vec![nested_bad.clone()],
                    ),
                    vec![EMatchArm {
                        pattern: EPattern::Wild,
                        guard: Some(nested_bad.clone()),
                        body: vec![EEventAction::Apply(
                            nested_bad.clone(),
                            "advance".to_string(),
                            vec![nested_bad.clone()],
                            vec![nested_bad],
                        )],
                    }],
                ),
            ],
        );
        let mut action_errors = Vec::new();
        walk_event_action_for_ctor_check(&event_action, &variant_fields(), &mut action_errors);
        assert!(
            action_errors.len() >= 6,
            "expected constructor errors from guard, create, match arg, arm guard, target, refs, and args: {action_errors:?}"
        );
    }
}
