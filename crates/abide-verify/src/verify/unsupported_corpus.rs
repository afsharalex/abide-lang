use crate::ir::types::{IRAggKind, IRExpr, IRType, LitVal};

#[derive(Clone)]
pub(super) struct UnsupportedExprCase {
    pub(super) name: &'static str,
    pub(super) expr: IRExpr,
    pub(super) expected_kind: &'static str,
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

pub(super) fn statement_like_expr_cases() -> Vec<UnsupportedExprCase> {
    vec![
        UnsupportedExprCase {
            name: "assert_true",
            expr: IRExpr::Assert {
                expr: Box::new(bool_lit(true)),
                span: None,
            },
            expected_kind: "Assert",
        },
        UnsupportedExprCase {
            name: "assume_true",
            expr: IRExpr::Assume {
                expr: Box::new(bool_lit(true)),
                span: None,
            },
            expected_kind: "Assume",
        },
    ]
}

pub(super) fn pure_expression_rejection_cases() -> Vec<UnsupportedExprCase> {
    let mut cases = statement_like_expr_cases();
    cases.extend([
        UnsupportedExprCase {
            name: "sorry",
            expr: IRExpr::Sorry { span: None },
            expected_kind: "Sorry",
        },
        UnsupportedExprCase {
            name: "todo",
            expr: IRExpr::Todo { span: None },
            expected_kind: "Todo",
        },
    ]);
    cases
}

/// Unsupported cases for property-position checks — theorem `show`, lemma
/// bodies, and scene `then` assertions. These positions DO support
/// transparent `assert`/`assume` wrappers (`assert e` is the property `e`),
/// so the statement-like cases are excluded; everything else (bare lambda,
/// sorry/todo, imperative block/var-decl, etc.) is still unsupported.
pub(super) fn property_position_unsupported_cases() -> Vec<UnsupportedExprCase> {
    unsupported_expr_cases()
        .into_iter()
        .filter(|case| case.name != "assert_true" && case.name != "assume_true")
        .collect()
}

pub(super) fn unsupported_expr_cases() -> Vec<UnsupportedExprCase> {
    let mut cases = statement_like_expr_cases();
    cases.extend([
        UnsupportedExprCase {
            name: "lambda",
            expr: IRExpr::Lam {
                param: "x".to_owned(),
                param_type: IRType::Int,
                body: Box::new(bool_lit(true)),
                span: None,
            },
            expected_kind: "Lam",
        },
        UnsupportedExprCase {
            name: "sorry",
            expr: IRExpr::Sorry { span: None },
            expected_kind: "Sorry",
        },
        UnsupportedExprCase {
            name: "todo",
            expr: IRExpr::Todo { span: None },
            expected_kind: "Todo",
        },
        UnsupportedExprCase {
            name: "imperative_block",
            expr: IRExpr::Block {
                exprs: vec![bool_lit(true)],
                span: None,
            },
            expected_kind: "Block",
        },
        UnsupportedExprCase {
            name: "var_decl",
            expr: IRExpr::VarDecl {
                name: "x".to_owned(),
                ty: IRType::Int,
                init: Box::new(int_lit(0)),
                rest: Box::new(bool_lit(true)),
                span: None,
            },
            expected_kind: "VarDecl",
        },
        UnsupportedExprCase {
            name: "while_loop",
            expr: IRExpr::While {
                cond: Box::new(bool_lit(true)),
                invariants: Vec::new(),
                decreases: None,
                body: Box::new(bool_lit(true)),
                span: None,
            },
            expected_kind: "While",
        },
        UnsupportedExprCase {
            name: "integer_set_comprehension",
            expr: IRExpr::SetComp {
                var: "x".to_owned(),
                domain: IRType::Int,
                source: None,
                filter: Box::new(bool_lit(true)),
                projection: None,
                ty: IRType::Set {
                    element: Box::new(IRType::Int),
                },
                span: None,
            },
            expected_kind: "SetComp with non-entity domain",
        },
        UnsupportedExprCase {
            name: "infinite_aggregate",
            expr: IRExpr::Aggregate {
                kind: IRAggKind::Sum,
                var: "x".to_owned(),
                domain: IRType::Int,
                body: Box::new(int_lit(1)),
                in_filter: None,
                span: None,
            },
            expected_kind: "Aggregate with non-finite domain",
        },
    ]);
    cases
}
