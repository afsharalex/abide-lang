//! Entity well-formedness checking.

use super::super::error::{ElabError, ErrorKind};
use super::super::types::{BuiltinTy, EAction, EEntity, EExpr, EField, Ty};

pub(super) fn check_entity(entity: &EEntity, all_known_names: &[String]) -> Vec<ElabError> {
    let mut errors = Vec::new();

    for field in &entity.fields {
        errors.extend(check_field(&entity.name, field));
    }
    for action in &entity.actions {
        errors.extend(check_action(entity, action, all_known_names));
    }
    // Invariants are restricted to the state-only safety fragment: no
    // liveness/past-time temporal operators and no primed (next-state)
    // expressions.
    for inv in &entity.invariants {
        check_invariant_body_state_only(&inv.body, &mut errors);
    }

    errors
}

/// Walk an invariant body and emit a diagnostic for any construct outside the
/// state-only safety fragment. Invariants are single-state predicates, so the
/// forbidden set is:
///
/// - **Future-time liveness:** `eventually`, `until` (and `next`, `releases`
///   once those are added to the expression language) →
///   `INVARIANT_LIVENESS_NOT_ALLOWED`.
/// - **Past-time liveness:** `previously`, `since` →
///   `INVARIANT_LIVENESS_NOT_ALLOWED`; the `saw` event observation →
///   `SAW_NOT_ALLOWED_IN_INVARIANT`.
/// - **Two-state forms:** a primed `'` (next-state) expression →
///   `INVARIANT_PRIME_NOT_ALLOWED`.
///
/// Safety operators (`always`, `historically`, `once`) are allowed and recurse
/// normally. Each rejection still walks its operands so nested violations are
/// surfaced too.
pub(super) fn check_invariant_body_state_only(expr: &EExpr, errors: &mut Vec<ElabError>) {
    fn walk(e: &EExpr, errors: &mut Vec<ElabError>) {
        match e {
            EExpr::Eventually(_, _, sp)
            | EExpr::Until(_, _, _, sp)
            | EExpr::Previously(_, _, sp)
            | EExpr::Since(_, _, _, sp) => {
                let kind = match e {
                    EExpr::Eventually(_, _, _) => "eventually",
                    EExpr::Until(_, _, _, _) => "until",
                    EExpr::Previously(_, _, _) => "previously",
                    EExpr::Since(_, _, _, _) => "since",
                    _ => unreachable!(),
                };
                let mut err = if let Some(span) = sp {
                    ElabError::with_span(
                        ErrorKind::InvalidScope,
                        format!(
                            "{}: `{kind}` is a liveness operator",
                            crate::messages::INVARIANT_LIVENESS_NOT_ALLOWED
                        ),
                        "invariant body".to_owned(),
                        *span,
                    )
                } else {
                    ElabError::new(
                        ErrorKind::InvalidScope,
                        format!(
                            "{}: `{kind}` is a liveness operator",
                            crate::messages::INVARIANT_LIVENESS_NOT_ALLOWED
                        ),
                        "invariant body".to_owned(),
                    )
                };
                err.help = Some(crate::messages::HINT_INVARIANT_LIVENESS_NOT_ALLOWED.into());
                errors.push(err);
                // Continue walking to surface multiple violations.
                match e {
                    EExpr::Eventually(_, body, _) | EExpr::Previously(_, body, _) => {
                        walk(body, errors);
                    }
                    EExpr::Until(_, l, r, _) | EExpr::Since(_, l, r, _) => {
                        walk(l, errors);
                        walk(r, errors);
                    }
                    _ => unreachable!(),
                }
            }
            // Primed (next-state) expressions are a two-state form; invariants
            // are state-only, so reject them. Recurse to surface nested
            // violations.
            EExpr::Prime(_, body, sp) => {
                let mut err = if let Some(span) = sp {
                    ElabError::with_span(
                        ErrorKind::InvalidPrime,
                        crate::messages::INVARIANT_PRIME_NOT_ALLOWED.to_owned(),
                        "invariant body".to_owned(),
                        *span,
                    )
                } else {
                    ElabError::new(
                        ErrorKind::InvalidPrime,
                        crate::messages::INVARIANT_PRIME_NOT_ALLOWED.to_owned(),
                        "invariant body".to_owned(),
                    )
                };
                err.help = Some(crate::messages::HINT_INVARIANT_PRIME_NOT_ALLOWED.into());
                errors.push(err);
                walk(body, errors);
            }
            // Recurse through all other forms.
            EExpr::Always(_, body, _)
            | EExpr::Historically(_, body, _)
            | EExpr::Once(_, body, _)
            | EExpr::UnOp(_, _, body, _)
            | EExpr::Field(_, body, _, _)
            | EExpr::Card(_, body, _)
            | EExpr::Assert(_, body, _)
            | EExpr::Assume(_, body, _)
            | EExpr::NamedPair(_, _, body, _)
            | EExpr::Quant(_, _, _, _, body, _)
            | EExpr::Lam(_, _, body, _) => walk(body, errors),
            EExpr::Choose(_, _, _, predicate, _) => {
                if let Some(pred) = predicate {
                    walk(pred, errors);
                }
            }
            EExpr::BinOp(_, _, l, r, _)
            | EExpr::Assign(_, l, r, _)
            | EExpr::Seq(_, l, r, _)
            | EExpr::SameStep(_, l, r, _)
            | EExpr::In(_, l, r, _)
            | EExpr::Pipe(_, l, r, _)
            | EExpr::Index(_, l, r, _)
            | EExpr::MapUpdate(_, l, _, r, _) => {
                walk(l, errors);
                walk(r, errors);
            }
            EExpr::Call(_, callee, args, _) => {
                walk(callee, errors);
                for a in args {
                    walk(a, errors);
                }
            }
            EExpr::CallR(_, callee, refs, args, _) => {
                walk(callee, errors);
                for a in refs {
                    walk(a, errors);
                }
                for a in args {
                    walk(a, errors);
                }
            }
            EExpr::QualCall(_, _, _, args, _) => {
                for a in args {
                    walk(a, errors);
                }
            }
            EExpr::TupleLit(_, elems, _)
            | EExpr::SetLit(_, elems, _)
            | EExpr::SeqLit(_, elems, _) => {
                for el in elems {
                    walk(el, errors);
                }
            }
            EExpr::MapLit(_, entries, _) => {
                for (k, v) in entries {
                    walk(k, errors);
                    walk(v, errors);
                }
            }
            EExpr::SetComp(_, proj, _, _, source, body, _) => {
                if let Some(p) = proj {
                    walk(p, errors);
                }
                if let Some(source) = source {
                    walk(source, errors);
                }
                walk(body, errors);
            }
            EExpr::RelComp(_, projection, bindings, filter, _) => {
                walk(projection, errors);
                for binding in bindings {
                    if let Some(source) = &binding.source {
                        walk(source, errors);
                    }
                }
                walk(filter, errors);
            }
            EExpr::Match(scrut, arms, _) => {
                walk(scrut, errors);
                for (_, guard, body) in arms {
                    if let Some(g) = guard {
                        walk(g, errors);
                    }
                    walk(body, errors);
                }
            }
            EExpr::Let(bindings, body, _) => {
                for (_, _, init) in bindings {
                    walk(init, errors);
                }
                walk(body, errors);
            }
            EExpr::Saw(_, _, _, args, sp) => {
                let mut err = if let Some(span) = sp {
                    ElabError::with_span(
                        ErrorKind::InvalidScope,
                        format!(
                            "{}: `saw` is a past-time temporal operator",
                            crate::messages::SAW_NOT_ALLOWED_IN_INVARIANT
                        ),
                        "invariant body".to_owned(),
                        *span,
                    )
                } else {
                    ElabError::new(
                        ErrorKind::InvalidScope,
                        format!(
                            "{}: `saw` is a past-time temporal operator",
                            crate::messages::SAW_NOT_ALLOWED_IN_INVARIANT
                        ),
                        "invariant body".to_owned(),
                    )
                };
                err.help = Some(crate::messages::HINT_INVARIANT_LIVENESS_NOT_ALLOWED.into());
                errors.push(err);
                // Recurse into args to surface nested violations.
                for e in args.iter().flatten() {
                    walk(e, errors);
                }
            }
            EExpr::CtorRecord(_, _, _, fields, _) | EExpr::StructCtor(_, _, fields, _) => {
                for (_, fv) in fields {
                    walk(fv, errors);
                }
            }
            EExpr::Block(exprs, _) => {
                for ex in exprs {
                    walk(ex, errors);
                }
            }
            EExpr::VarDecl(_, _, init, rest, _) => {
                walk(init, errors);
                walk(rest, errors);
            }
            EExpr::While(cond, _contracts, body, _) => {
                walk(cond, errors);
                walk(body, errors);
            }
            EExpr::IfElse(cond, then_b, else_b, _) => {
                walk(cond, errors);
                walk(then_b, errors);
                if let Some(eb) = else_b {
                    walk(eb, errors);
                }
            }
            EExpr::Aggregate(_, _, _, _, body, in_filter, _) => {
                walk(body, errors);
                if let Some(f) = in_filter {
                    walk(f, errors);
                }
            }
            // Leaves: nothing to recurse into.
            EExpr::Lit(_, _, _)
            | EExpr::Var(_, _, _)
            | EExpr::Qual(_, _, _, _)
            | EExpr::Unresolved(_, _)
            | EExpr::Sorry(_)
            | EExpr::Todo(_) => {}
        }
    }
    walk(expr, errors);
}

pub(super) fn check_field(entity_name: &str, field: &EField) -> Vec<ElabError> {
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
                                crate::messages::in_value_not_constructor(field.ty.name()),
                                &ctx_str,
                            ));
                        }
                    }
                }
                // For non-enum fields: check type compatibility
                if let Ty::Builtin(_) = &field.ty {
                    let ok = super::expr_compatible_with_ty(e, &field.ty);
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
            if !matches!(pred_ty, Ty::Builtin(BuiltinTy::Bool) | Ty::Error) {
                return vec![ElabError::new(
                    ErrorKind::InvalidDefault,
                    crate::messages::where_predicate_not_bool(pred_ty.name()),
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
            let help = if let Some(closest) = super::find_closest_name(v, ctors) {
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
                crate::messages::enum_default_not_constructor(name, &ctors.join(", ")),
                &ctx_str,
            )]
        }
        // Builtin type mismatch (e.g., Int literal for Bool field)
        (Ty::Builtin(_), _) => {
            let ok = super::expr_compatible_with_ty(def_expr, &field.ty);
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

pub(super) fn check_action(
    entity: &EEntity,
    action: &EAction,
    all_known_names: &[String],
) -> Vec<ElabError> {
    let ctx = format!("entity {}, action {}", entity.name, action.name);
    let mut errors = Vec::new();

    // Check requires are boolean-typed
    for req in &action.requires {
        if !super::is_bool_expr(req) {
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
        super::check_unresolved_constructors(req, &ctx, action.span, &known, &mut errors);
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
                    let help =
                        if let Some(closest) = super::find_closest_name(field_name, &field_names) {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::elab::types::{EFieldDefault, EInvariant, Literal};

    fn int_lit(value: i64) -> EExpr {
        EExpr::Lit(Ty::Builtin(BuiltinTy::Int), Literal::Int(value), None)
    }

    fn bool_lit(value: bool) -> EExpr {
        EExpr::Lit(Ty::Builtin(BuiltinTy::Bool), Literal::Bool(value), None)
    }

    fn var(ty: Ty, name: &str) -> EExpr {
        EExpr::Var(ty, name.to_string(), None)
    }

    fn field(name: &str, ty: Ty, default: Option<EFieldDefault>) -> EField {
        EField {
            name: name.to_string(),
            ty,
            default,
            span: Some(crate::span::Span { start: 1, end: 2 }),
        }
    }

    fn action(requires: Vec<EExpr>, body: Vec<EExpr>) -> EAction {
        EAction {
            name: "advance".to_string(),
            refs: vec![],
            params: vec![],
            requires,
            ensures: vec![],
            body,
            span: Some(crate::span::Span { start: 3, end: 4 }),
        }
    }

    fn entity(fields: Vec<EField>, actions: Vec<EAction>, invariants: Vec<EInvariant>) -> EEntity {
        EEntity {
            name: "Ticket".to_string(),
            fields,
            actions,
            derived_fields: vec![],
            invariants,
            fsm_decls: vec![],
            span: None,
        }
    }

    fn enum_ty() -> Ty {
        Ty::Enum(
            "Status".to_string(),
            vec!["Open".to_string(), "Closed".to_string()],
        )
    }

    fn invalid_assignment(field_name: &str) -> EExpr {
        EExpr::Assign(
            Ty::Error,
            Box::new(EExpr::Prime(
                Ty::Error,
                Box::new(var(Ty::Error, field_name)),
                None,
            )),
            Box::new(var(Ty::Error, "Closed")),
            None,
        )
    }

    #[test]
    fn invariant_checker_rejects_liveness_and_recurses_into_liveness_operands() {
        let expr = EExpr::Eventually(
            Ty::Builtin(BuiltinTy::Bool),
            Box::new(EExpr::Until(
                Ty::Builtin(BuiltinTy::Bool),
                Box::new(EExpr::Previously(
                    Ty::Builtin(BuiltinTy::Bool),
                    Box::new(bool_lit(true)),
                    None,
                )),
                Box::new(EExpr::Since(
                    Ty::Builtin(BuiltinTy::Bool),
                    Box::new(bool_lit(true)),
                    Box::new(bool_lit(false)),
                    None,
                )),
                None,
            )),
            None,
        );
        let mut errors = Vec::new();
        check_invariant_body_state_only(&expr, &mut errors);
        assert_eq!(errors.len(), 4);
        for kind in ["eventually", "until", "previously", "since"] {
            assert!(
                errors.iter().any(|error| error.message.contains(kind)),
                "expected invariant liveness error for {kind}: {errors:?}"
            );
        }
    }

    #[test]
    fn invariant_checker_rejects_primed_expressions() {
        let primed = |span| {
            EExpr::Prime(
                Ty::Builtin(BuiltinTy::Bool),
                Box::new(var(Ty::Builtin(BuiltinTy::Bool), "ready")),
                span,
            )
        };

        // Direct: an invariant body of `ready'` is a two-state expression.
        let mut errors = Vec::new();
        check_invariant_body_state_only(
            &primed(Some(crate::span::Span { start: 1, end: 2 })),
            &mut errors,
        );
        assert_eq!(errors.len(), 1, "primed invariant must error: {errors:?}");
        assert!(matches!(errors[0].kind, ErrorKind::InvalidPrime));
        assert!(errors[0].message.contains("primed"));

        // Nested under an allowed form (`always (ready')`) must still be caught.
        let nested = EExpr::Always(Ty::Builtin(BuiltinTy::Bool), Box::new(primed(None)), None);
        let mut errors = Vec::new();
        check_invariant_body_state_only(&nested, &mut errors);
        assert_eq!(
            errors.len(),
            1,
            "nested primed invariant must error: {errors:?}"
        );
        assert!(matches!(errors[0].kind, ErrorKind::InvalidPrime));
    }

    #[test]
    fn field_checker_validates_value_in_and_where_defaults() {
        assert!(check_field(
            "Ticket",
            &field(
                "status",
                enum_ty(),
                Some(EFieldDefault::Value(var(Ty::Error, "Open")))
            )
        )
        .is_empty());
        assert!(check_field(
            "Ticket",
            &field(
                "amount",
                Ty::Builtin(BuiltinTy::Real),
                Some(EFieldDefault::Value(int_lit(1)))
            )
        )
        .is_empty());
        assert!(check_field(
            "Ticket",
            &field(
                "status",
                enum_ty(),
                Some(EFieldDefault::In(vec![var(Ty::Error, "Open")]))
            )
        )
        .is_empty());
        assert!(check_field(
            "Ticket",
            &field(
                "amount",
                Ty::Builtin(BuiltinTy::Int),
                Some(EFieldDefault::In(vec![int_lit(1), int_lit(2)]))
            )
        )
        .is_empty());
        assert!(check_field(
            "Ticket",
            &field(
                "amount",
                Ty::Builtin(BuiltinTy::Int),
                Some(EFieldDefault::Where(bool_lit(true)))
            )
        )
        .is_empty());

        let bad_enum = check_field(
            "Ticket",
            &field(
                "status",
                enum_ty(),
                Some(EFieldDefault::Value(var(Ty::Error, "Missing"))),
            ),
        );
        assert_eq!(bad_enum.len(), 1);
        assert!(bad_enum[0].message.contains("not a constructor"));

        let bad_enum_literal = check_field(
            "Ticket",
            &field("status", enum_ty(), Some(EFieldDefault::Value(int_lit(1)))),
        );
        assert_eq!(bad_enum_literal.len(), 1);
        assert!(bad_enum_literal[0]
            .message
            .contains("must be a constructor"));

        let bad_in_enum = check_field(
            "Ticket",
            &field(
                "status",
                enum_ty(),
                Some(EFieldDefault::In(vec![
                    var(Ty::Error, "Missing"),
                    int_lit(1),
                ])),
            ),
        );
        assert_eq!(bad_in_enum.len(), 2);

        let bad_builtin = check_field(
            "Ticket",
            &field(
                "flag",
                Ty::Builtin(BuiltinTy::Bool),
                Some(EFieldDefault::Value(int_lit(1))),
            ),
        );
        assert_eq!(bad_builtin.len(), 1);
        assert!(bad_builtin[0]
            .message
            .contains("default value has type int"));

        let bad_in_builtin = check_field(
            "Ticket",
            &field(
                "count",
                Ty::Builtin(BuiltinTy::Int),
                Some(EFieldDefault::In(vec![int_lit(1), bool_lit(false)])),
            ),
        );
        assert_eq!(bad_in_builtin.len(), 1);
        assert!(bad_in_builtin[0]
            .message
            .contains("`in` value has type bool"));

        let bad_where = check_field(
            "Ticket",
            &field(
                "count",
                Ty::Builtin(BuiltinTy::Int),
                Some(EFieldDefault::Where(int_lit(1))),
            ),
        );
        assert_eq!(bad_where.len(), 1);
        assert!(bad_where[0].message.contains("where"));
    }

    #[test]
    fn action_checker_validates_boolean_requires_and_primed_field_targets() {
        let ticket = entity(
            vec![
                field("status", enum_ty(), None),
                field("count", Ty::Builtin(BuiltinTy::Int), None),
            ],
            vec![],
            vec![],
        );
        assert!(check_action(&ticket, &action(vec![bool_lit(true)], vec![]), &[]).is_empty());

        let errors = check_action(
            &ticket,
            &action(vec![int_lit(1)], vec![invalid_assignment("statsu")]),
            &["Status".to_string(), "Closed".to_string()],
        );
        assert_eq!(errors.len(), 2);
        assert!(errors
            .iter()
            .any(|error| error.message == crate::messages::MSG_REQUIRES_SHOULD_BE_BOOL));
        assert!(errors
            .iter()
            .any(|error| error.message.contains("is not a field")));

        assert!(check_action(
            &ticket,
            &action(vec![bool_lit(true)], vec![invalid_assignment("status")]),
            &[],
        )
        .is_empty());
    }

    #[test]
    fn entity_checker_aggregates_field_action_and_invariant_errors() {
        let invariant = EInvariant {
            name: "eventual_close".to_string(),
            body: EExpr::Eventually(Ty::Builtin(BuiltinTy::Bool), Box::new(bool_lit(true)), None),
            span: None,
        };
        let ticket = entity(
            vec![field(
                "status",
                enum_ty(),
                Some(EFieldDefault::Value(var(Ty::Error, "Missing"))),
            )],
            vec![action(
                vec![int_lit(1)],
                vec![invalid_assignment("missing")],
            )],
            vec![invariant],
        );

        let errors = check_entity(&ticket, &["Closed".to_string()]);
        assert_eq!(errors.len(), 4);
        assert!(errors
            .iter()
            .any(|error| error.message.contains("not a constructor")));
        assert!(errors
            .iter()
            .any(|error| error.message == crate::messages::MSG_REQUIRES_SHOULD_BE_BOOL));
        assert!(errors
            .iter()
            .any(|error| error.message.contains("not a field")));
        assert!(errors
            .iter()
            .any(|error| error.message.contains("eventually")));
    }
}
