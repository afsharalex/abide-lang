use crate::ir::types::{IRAction, IRExpr, IRType};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum VerifierContext {
    PureExpression,
    PropertyExpression,
    SlotExpression,
    ActionEncoding,
    ExplicitStateEvaluation,
    Ic3Encoding,
    SceneVerification,
    TheoremLemmaVerification,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum SupportClassification {
    Supported,
    Unsupported(&'static str),
    Contextual(&'static str),
}

impl SupportClassification {
    pub(super) fn is_supported(self) -> bool {
        matches!(self, Self::Supported)
    }
}

pub(super) fn classify_expr_support(
    context: VerifierContext,
    expr: &IRExpr,
) -> SupportClassification {
    use SupportClassification::{Contextual, Supported, Unsupported};

    match expr {
        IRExpr::Lit { .. } | IRExpr::Var { .. } | IRExpr::Ctor { .. } => Supported,
        IRExpr::BinOp { .. }
        | IRExpr::UnOp { .. }
        | IRExpr::App { .. }
        | IRExpr::Let { .. }
        | IRExpr::Field { .. }
        | IRExpr::Choose { .. }
        | IRExpr::MapUpdate { .. }
        | IRExpr::Index { .. }
        | IRExpr::SetLit { .. }
        | IRExpr::SeqLit { .. }
        | IRExpr::Tuple { .. }
        | IRExpr::MapLit { .. }
        | IRExpr::RelComp { .. }
        | IRExpr::Card { .. }
        | IRExpr::IfElse { .. }
        | IRExpr::Match { .. } => Contextual("depends on types, operators, bindings, and backend"),
        IRExpr::Forall { domain, .. }
        | IRExpr::Exists { domain, .. }
        | IRExpr::One { domain, .. }
        | IRExpr::Lone { domain, .. } => classify_quantifier(context, domain),
        IRExpr::SetComp { domain, source, .. } => {
            if source.is_some()
                || is_finite_domain(domain)
                || matches!(domain, IRType::Entity { .. })
            {
                Contextual("set comprehension support depends on source and domain finiteness")
            } else {
                Unsupported("set comprehension has no finite verifier source")
            }
        }
        IRExpr::Aggregate { domain, .. } => {
            if is_finite_domain(domain) || matches!(domain, IRType::Entity { .. }) {
                Contextual("aggregate support depends on finite domain and body encoding")
            } else {
                Unsupported("aggregate has no finite verifier domain")
            }
        }
        IRExpr::Prime { .. } => match context {
            VerifierContext::PropertyExpression
            | VerifierContext::Ic3Encoding
            | VerifierContext::TheoremLemmaVerification => {
                Contextual("primed expressions are only legal in transition-aware properties")
            }
            VerifierContext::PureExpression
            | VerifierContext::SlotExpression
            | VerifierContext::ActionEncoding
            | VerifierContext::ExplicitStateEvaluation
            | VerifierContext::SceneVerification => {
                Unsupported("primed expressions require a transition-aware verifier context")
            }
        },
        IRExpr::Always { .. }
        | IRExpr::Eventually { .. }
        | IRExpr::Until { .. }
        | IRExpr::Historically { .. }
        | IRExpr::Once { .. }
        | IRExpr::Previously { .. }
        | IRExpr::Since { .. }
        | IRExpr::Saw { .. } => match context {
            VerifierContext::PropertyExpression
            | VerifierContext::Ic3Encoding
            | VerifierContext::TheoremLemmaVerification => {
                Contextual("temporal expressions require property-specific encoding")
            }
            VerifierContext::PureExpression
            | VerifierContext::SlotExpression
            | VerifierContext::ActionEncoding
            | VerifierContext::ExplicitStateEvaluation
            | VerifierContext::SceneVerification => {
                Unsupported("temporal expressions are not value expressions in this context")
            }
        },
        IRExpr::Lam { .. } => {
            Unsupported("lambda expressions are not encoded by verifier backends")
        }
        IRExpr::Sorry { .. } => Unsupported("sorry must be handled by admission preflight"),
        IRExpr::Todo { .. } => Unsupported("todo must be handled by admission preflight"),
        IRExpr::Assert { .. } => {
            Unsupported("assert is an imperative statement, not a verifier value expression")
        }
        IRExpr::Assume { .. } => {
            Unsupported("assume is an imperative statement, not a verifier value expression")
        }
        IRExpr::Block { .. } | IRExpr::VarDecl { .. } | IRExpr::While { .. } => {
            Unsupported("imperative function-body expression is not valid in this verifier context")
        }
    }
}

pub(super) fn classify_action_support(
    context: VerifierContext,
    action: &IRAction,
) -> SupportClassification {
    use SupportClassification::{Contextual, Unsupported};

    match action {
        IRAction::Choose { .. }
        | IRAction::ForAll { .. }
        | IRAction::Create { .. }
        | IRAction::LetCrossCall { .. }
        | IRAction::Apply { .. }
        | IRAction::CrossCall { .. }
        | IRAction::Match { .. } => match context {
            VerifierContext::ActionEncoding
            | VerifierContext::ExplicitStateEvaluation
            | VerifierContext::SceneVerification => {
                Contextual("action support depends on system/entity resolution and nested bodies")
            }
            VerifierContext::PureExpression
            | VerifierContext::PropertyExpression
            | VerifierContext::SlotExpression
            | VerifierContext::Ic3Encoding
            | VerifierContext::TheoremLemmaVerification => {
                Unsupported("operational action is not valid in expression-only verifier context")
            }
        },
        IRAction::ExprStmt { .. } => Unsupported(
            "bare expression statements cannot be silently dropped by verifier backends",
        ),
    }
}

fn classify_quantifier(context: VerifierContext, domain: &IRType) -> SupportClassification {
    use SupportClassification::{Contextual, Unsupported};

    match context {
        VerifierContext::PureExpression
        | VerifierContext::PropertyExpression
        | VerifierContext::SlotExpression
        | VerifierContext::ExplicitStateEvaluation
        | VerifierContext::Ic3Encoding
        | VerifierContext::SceneVerification
        | VerifierContext::TheoremLemmaVerification => {
            if is_finite_domain(domain) || matches!(domain, IRType::Entity { .. }) {
                Contextual("quantifier support depends on finite domain enumeration")
            } else {
                Unsupported("quantifier has no finite verifier domain")
            }
        }
        VerifierContext::ActionEncoding => {
            Unsupported("quantifier expression is not an action encoder entry point")
        }
    }
}

fn is_finite_domain(domain: &IRType) -> bool {
    match domain {
        IRType::Bool | IRType::Enum { .. } => true,
        IRType::Int
        | IRType::String
        | IRType::Identity
        | IRType::Real
        | IRType::Float
        | IRType::Record { .. }
        | IRType::Fn { .. }
        | IRType::Entity { .. }
        | IRType::Set { .. }
        | IRType::Seq { .. }
        | IRType::Map { .. }
        | IRType::Tuple { .. }
        | IRType::Refinement { .. } => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::types::{
        IRAction, IRActionMatchScrutinee, IRAggKind, IRExpr, IRRelCompBinding, IRType, IRVariant,
        LitVal,
    };
    use crate::verify::unsupported_corpus;

    const EXPR_CONTEXTS: &[VerifierContext] = &[
        VerifierContext::PureExpression,
        VerifierContext::PropertyExpression,
        VerifierContext::SlotExpression,
        VerifierContext::ExplicitStateEvaluation,
        VerifierContext::Ic3Encoding,
        VerifierContext::SceneVerification,
        VerifierContext::TheoremLemmaVerification,
    ];

    #[test]
    fn unsupported_expr_corpus_is_never_classified_as_supported() {
        for case in unsupported_corpus::unsupported_expr_cases() {
            for context in EXPR_CONTEXTS {
                let classification = classify_expr_support(*context, &case.expr);
                assert!(
                    !classification.is_supported(),
                    "{} must not be supported in {context:?}; expected {}",
                    case.name,
                    case.expected_kind
                );
            }
        }
    }

    #[test]
    fn bare_expression_action_is_never_classified_as_supported_for_action_contexts() {
        let expr_stmt = IRAction::ExprStmt {
            expr: unsupported_corpus::statement_like_expr_cases()
                .remove(0)
                .expr,
        };

        for context in [
            VerifierContext::ActionEncoding,
            VerifierContext::ExplicitStateEvaluation,
            VerifierContext::SceneVerification,
        ] {
            let classification = classify_action_support(context, &expr_stmt);
            assert!(
                !classification.is_supported(),
                "bare expression action must not be supported in {context:?}"
            );
        }
    }

    #[test]
    fn every_action_variant_receives_a_non_panicking_classification() {
        let actions = vec![
            IRAction::Choose {
                var: "x".to_owned(),
                entity: "Thing".to_owned(),
                filter: Box::new(
                    unsupported_corpus::statement_like_expr_cases()
                        .remove(0)
                        .expr,
                ),
                ops: Vec::new(),
            },
            IRAction::ForAll {
                var: "x".to_owned(),
                entity: "Thing".to_owned(),
                ops: Vec::new(),
            },
            IRAction::Create {
                entity: "Thing".to_owned(),
                fields: Vec::new(),
            },
            IRAction::LetCrossCall {
                name: "result".to_owned(),
                system: "Other".to_owned(),
                command: "do_it".to_owned(),
                args: Vec::new(),
            },
            IRAction::Apply {
                target: "x".to_owned(),
                transition: "step".to_owned(),
                refs: Vec::new(),
                args: Vec::new(),
            },
            IRAction::CrossCall {
                system: "Other".to_owned(),
                command: "do_it".to_owned(),
                args: Vec::new(),
            },
            IRAction::Match {
                scrutinee: IRActionMatchScrutinee::Var {
                    name: "result".to_owned(),
                },
                arms: Vec::new(),
            },
            IRAction::ExprStmt {
                expr: IRExpr::Var {
                    name: "x".to_owned(),
                    ty: IRType::Bool,
                    span: None,
                },
            },
        ];

        for action in &actions {
            let _classification = classify_action_support(VerifierContext::ActionEncoding, action);
        }
    }

    #[test]
    fn every_expr_variant_receives_a_non_panicking_classification_in_every_context() {
        let exprs = representative_expr_variants();

        for expr in &exprs {
            for context in EXPR_CONTEXTS {
                let _classification = classify_expr_support(*context, expr);
            }
        }
    }

    #[test]
    fn set_comprehension_support_distinguishes_source_finite_entity_and_infinite_domains() {
        let finite_enum = status_enum_ty();
        let sourced_int = set_comp(IRType::Int, Some(int_set_lit()));
        let finite_bool = set_comp(IRType::Bool, None);
        let finite_enum_comp = set_comp(finite_enum, None);
        let entity_comp = set_comp(
            IRType::Entity {
                name: "Task".to_owned(),
            },
            None,
        );
        let unsourced_int = set_comp(IRType::Int, None);

        for expr in [sourced_int, finite_bool, finite_enum_comp, entity_comp] {
            assert_eq!(
                classify_expr_support(VerifierContext::PropertyExpression, &expr),
                SupportClassification::Contextual(
                    "set comprehension support depends on source and domain finiteness"
                )
            );
        }
        assert_eq!(
            classify_expr_support(VerifierContext::PropertyExpression, &unsourced_int),
            SupportClassification::Unsupported("set comprehension has no finite verifier source")
        );
    }

    #[test]
    fn aggregate_and_quantifier_support_distinguish_finite_entity_and_infinite_domains() {
        let finite_enum = status_enum_ty();

        for domain in [
            IRType::Bool,
            finite_enum,
            IRType::Entity {
                name: "Task".to_owned(),
            },
        ] {
            let aggregate = aggregate(domain.clone());
            let quantifier = forall(domain);
            assert_eq!(
                classify_expr_support(VerifierContext::PropertyExpression, &aggregate),
                SupportClassification::Contextual(
                    "aggregate support depends on finite domain and body encoding"
                )
            );
            assert_eq!(
                classify_expr_support(VerifierContext::PropertyExpression, &quantifier),
                SupportClassification::Contextual(
                    "quantifier support depends on finite domain enumeration"
                )
            );
        }

        let aggregate = aggregate(IRType::Int);
        let quantifier = forall(IRType::Int);
        assert_eq!(
            classify_expr_support(VerifierContext::PropertyExpression, &aggregate),
            SupportClassification::Unsupported("aggregate has no finite verifier domain")
        );
        assert_eq!(
            classify_expr_support(VerifierContext::PropertyExpression, &quantifier),
            SupportClassification::Unsupported("quantifier has no finite verifier domain")
        );
    }

    fn status_enum_ty() -> IRType {
        IRType::Enum {
            name: "Status".to_owned(),
            variants: vec![IRVariant::simple("Open"), IRVariant::simple("Closed")],
        }
    }

    fn bool_lit(value: bool) -> IRExpr {
        IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value },
            span: None,
        }
    }

    fn int_lit(value: i64) -> IRExpr {
        IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value },
            span: None,
        }
    }

    fn int_set_lit() -> IRExpr {
        IRExpr::SetLit {
            elements: vec![int_lit(1), int_lit(2)],
            ty: IRType::Set {
                element: Box::new(IRType::Int),
            },
            span: None,
        }
    }

    fn set_comp(domain: IRType, source: Option<IRExpr>) -> IRExpr {
        IRExpr::SetComp {
            var: "x".to_owned(),
            domain: domain.clone(),
            source: source.map(Box::new),
            filter: Box::new(bool_lit(true)),
            projection: None,
            ty: IRType::Set {
                element: Box::new(domain),
            },
            span: None,
        }
    }

    fn aggregate(domain: IRType) -> IRExpr {
        IRExpr::Aggregate {
            kind: IRAggKind::Sum,
            var: "x".to_owned(),
            domain,
            body: Box::new(int_lit(1)),
            in_filter: None,
            span: None,
        }
    }

    fn forall(domain: IRType) -> IRExpr {
        IRExpr::Forall {
            var: "x".to_owned(),
            domain,
            body: Box::new(bool_lit(true)),
            span: None,
        }
    }

    fn representative_expr_variants() -> Vec<IRExpr> {
        let bool_ty = IRType::Bool;
        let int_ty = IRType::Int;
        let finite_enum = IRType::Enum {
            name: "Status".to_owned(),
            variants: vec![IRVariant::simple("Open"), IRVariant::simple("Closed")],
        };
        let bool_lit = || IRExpr::Lit {
            ty: bool_ty.clone(),
            value: LitVal::Bool { value: true },
            span: None,
        };
        let int_lit = || IRExpr::Lit {
            ty: int_ty.clone(),
            value: LitVal::Int { value: 1 },
            span: None,
        };
        let bool_var = || IRExpr::Var {
            name: "flag".to_owned(),
            ty: bool_ty.clone(),
            span: None,
        };
        let int_var = || IRExpr::Var {
            name: "n".to_owned(),
            ty: int_ty.clone(),
            span: None,
        };
        let enum_ctor = || IRExpr::Ctor {
            enum_name: "Status".to_owned(),
            ctor: "Open".to_owned(),
            args: Vec::new(),
            span: None,
        };

        vec![
            bool_lit(),
            bool_var(),
            enum_ctor(),
            IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(int_lit()),
                right: Box::new(int_lit()),
                ty: bool_ty.clone(),
                span: None,
            },
            IRExpr::UnOp {
                op: "OpNot".to_owned(),
                operand: Box::new(bool_lit()),
                ty: bool_ty.clone(),
                span: None,
            },
            IRExpr::App {
                func: Box::new(IRExpr::Var {
                    name: "p".to_owned(),
                    ty: IRType::Fn {
                        param: Box::new(int_ty.clone()),
                        result: Box::new(bool_ty.clone()),
                    },
                    span: None,
                }),
                arg: Box::new(int_lit()),
                ty: bool_ty.clone(),
                span: None,
            },
            IRExpr::Lam {
                param: "x".to_owned(),
                param_type: int_ty.clone(),
                body: Box::new(bool_lit()),
                span: None,
            },
            IRExpr::Let {
                bindings: Vec::new(),
                body: Box::new(bool_lit()),
                span: None,
            },
            IRExpr::Forall {
                var: "s".to_owned(),
                domain: finite_enum.clone(),
                body: Box::new(bool_lit()),
                span: None,
            },
            IRExpr::Exists {
                var: "s".to_owned(),
                domain: finite_enum.clone(),
                body: Box::new(bool_lit()),
                span: None,
            },
            IRExpr::One {
                var: "s".to_owned(),
                domain: finite_enum.clone(),
                body: Box::new(bool_lit()),
                span: None,
            },
            IRExpr::Lone {
                var: "s".to_owned(),
                domain: finite_enum.clone(),
                body: Box::new(bool_lit()),
                span: None,
            },
            IRExpr::Field {
                expr: Box::new(IRExpr::Var {
                    name: "self".to_owned(),
                    ty: IRType::Entity {
                        name: "Thing".to_owned(),
                    },
                    span: None,
                }),
                field: "id".to_owned(),
                ty: IRType::Identity,
                span: None,
            },
            IRExpr::Prime {
                expr: Box::new(bool_var()),
                span: None,
            },
            IRExpr::Always {
                body: Box::new(bool_lit()),
                span: None,
            },
            IRExpr::Eventually {
                body: Box::new(bool_lit()),
                span: None,
            },
            IRExpr::Until {
                left: Box::new(bool_lit()),
                right: Box::new(bool_lit()),
                span: None,
            },
            IRExpr::Historically {
                body: Box::new(bool_lit()),
                span: None,
            },
            IRExpr::Once {
                body: Box::new(bool_lit()),
                span: None,
            },
            IRExpr::Previously {
                body: Box::new(bool_lit()),
                span: None,
            },
            IRExpr::Since {
                left: Box::new(bool_lit()),
                right: Box::new(bool_lit()),
                span: None,
            },
            IRExpr::Aggregate {
                kind: IRAggKind::Sum,
                var: "s".to_owned(),
                domain: finite_enum.clone(),
                body: Box::new(int_lit()),
                in_filter: None,
                span: None,
            },
            IRExpr::Saw {
                system_name: "System".to_owned(),
                event_name: "event".to_owned(),
                args: Vec::new(),
                span: None,
            },
            IRExpr::Match {
                scrutinee: Box::new(enum_ctor()),
                arms: Vec::new(),
                span: None,
            },
            IRExpr::Choose {
                var: "s".to_owned(),
                domain: finite_enum.clone(),
                predicate: Some(Box::new(bool_lit())),
                ty: finite_enum.clone(),
                span: None,
            },
            IRExpr::MapUpdate {
                map: Box::new(IRExpr::MapLit {
                    entries: Vec::new(),
                    ty: IRType::Map {
                        key: Box::new(int_ty.clone()),
                        value: Box::new(int_ty.clone()),
                    },
                    span: None,
                }),
                key: Box::new(int_lit()),
                value: Box::new(int_lit()),
                ty: IRType::Map {
                    key: Box::new(int_ty.clone()),
                    value: Box::new(int_ty.clone()),
                },
                span: None,
            },
            IRExpr::Index {
                map: Box::new(IRExpr::MapLit {
                    entries: Vec::new(),
                    ty: IRType::Map {
                        key: Box::new(int_ty.clone()),
                        value: Box::new(int_ty.clone()),
                    },
                    span: None,
                }),
                key: Box::new(int_lit()),
                ty: int_ty.clone(),
                span: None,
            },
            IRExpr::SetLit {
                elements: Vec::new(),
                ty: IRType::Set {
                    element: Box::new(int_ty.clone()),
                },
                span: None,
            },
            IRExpr::SeqLit {
                elements: Vec::new(),
                ty: IRType::Seq {
                    element: Box::new(int_ty.clone()),
                },
                span: None,
            },
            IRExpr::Tuple {
                elements: vec![int_lit(), bool_lit()],
                ty: IRType::Tuple {
                    elements: vec![int_ty.clone(), bool_ty.clone()],
                },
                span: None,
            },
            IRExpr::MapLit {
                entries: vec![(int_lit(), int_lit())],
                ty: IRType::Map {
                    key: Box::new(int_ty.clone()),
                    value: Box::new(int_ty.clone()),
                },
                span: None,
            },
            IRExpr::SetComp {
                var: "s".to_owned(),
                domain: finite_enum.clone(),
                source: None,
                filter: Box::new(bool_lit()),
                projection: None,
                ty: IRType::Set {
                    element: Box::new(finite_enum.clone()),
                },
                span: None,
            },
            IRExpr::RelComp {
                projection: Box::new(IRExpr::Tuple {
                    elements: vec![int_var()],
                    ty: IRType::Tuple {
                        elements: vec![int_ty.clone()],
                    },
                    span: None,
                }),
                bindings: vec![IRRelCompBinding {
                    var: "s".to_owned(),
                    domain: finite_enum.clone(),
                    source: None,
                }],
                filter: Box::new(bool_lit()),
                ty: IRType::Set {
                    element: Box::new(IRType::Tuple {
                        elements: vec![int_ty.clone()],
                    }),
                },
                span: None,
            },
            IRExpr::Card {
                expr: Box::new(IRExpr::SetLit {
                    elements: Vec::new(),
                    ty: IRType::Set {
                        element: Box::new(int_ty.clone()),
                    },
                    span: None,
                }),
                span: None,
            },
            IRExpr::Sorry { span: None },
            IRExpr::Todo { span: None },
            IRExpr::Assert {
                expr: Box::new(bool_lit()),
                span: None,
            },
            IRExpr::Assume {
                expr: Box::new(bool_lit()),
                span: None,
            },
            IRExpr::Block {
                exprs: vec![bool_lit()],
                span: None,
            },
            IRExpr::VarDecl {
                name: "local".to_owned(),
                ty: int_ty.clone(),
                init: Box::new(int_lit()),
                rest: Box::new(bool_lit()),
                span: None,
            },
            IRExpr::While {
                cond: Box::new(bool_lit()),
                invariants: Vec::new(),
                decreases: None,
                body: Box::new(bool_lit()),
                span: None,
            },
            IRExpr::IfElse {
                cond: Box::new(bool_lit()),
                then_body: Box::new(bool_lit()),
                else_body: Some(Box::new(bool_lit())),
                span: None,
            },
        ]
    }
}
