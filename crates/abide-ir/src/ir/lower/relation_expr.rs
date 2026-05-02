//! Lower elaborated relation-valued expressions into backend-neutral relation IR.

use super::{lower_ty, LowerCtx};
use crate::elab::types as E;
use crate::ir::relation::{
    IRRelationColumn, IRRelationExpr, IRRelationSource, IRRelationSymbol, IRRelationType,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RelationLowerError {
    NonRelationExpression {
        shape: &'static str,
    },
    UnsupportedOperator {
        type_name: String,
        func_name: String,
    },
    WrongArity {
        op: String,
        expected: usize,
        found: usize,
    },
    InvalidProjectColumn,
    NegativeProjectColumn {
        value: i64,
    },
    RelationType {
        message: String,
    },
}

pub fn lower_relation_expr(
    expr: &E::EExpr,
    ctx: &LowerCtx<'_>,
) -> Result<IRRelationExpr, RelationLowerError> {
    match expr {
        E::EExpr::Var(ty, name, _) => Ok(IRRelationExpr::Symbol(IRRelationSymbol {
            name: name.clone(),
            relation_type: relation_type_from_ty(ty, ctx)?,
            mutable: false,
            source: IRRelationSource::UserRelation { name: name.clone() },
        })),
        E::EExpr::QualCall(ty, type_name, func_name, args, _) if type_name == "Rel" => {
            lower_relation_qual_call(ty, type_name, func_name, args, ctx)
        }
        E::EExpr::BinOp(ty, op, left, right, _) if is_relation_ty(ty) => {
            let left = Box::new(lower_relation_expr(left, ctx)?);
            let right = Box::new(lower_relation_expr(right, ctx)?);
            match op {
                E::BinOp::Add => Ok(IRRelationExpr::Union(left, right)),
                E::BinOp::Mul => Ok(IRRelationExpr::Intersection(left, right)),
                E::BinOp::Sub => Ok(IRRelationExpr::Difference(left, right)),
                _ => Err(RelationLowerError::UnsupportedOperator {
                    type_name: "relation".to_owned(),
                    func_name: format!("{op:?}"),
                }),
            }
        }
        E::EExpr::SetLit(ty, elems, _) if is_relation_ty(ty) => {
            let relation_ty = relation_type_from_ty(ty, ctx)?;
            let mut lowered = elems
                .iter()
                .map(|elem| tuple_relation_literal(elem, &relation_ty))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter();
            let Some(first) = lowered.next() else {
                return Ok(IRRelationExpr::Empty(relation_ty));
            };
            Ok(lowered.fold(first, |acc, elem| {
                IRRelationExpr::Union(Box::new(acc), Box::new(elem))
            }))
        }
        E::EExpr::RelComp(..) => Err(RelationLowerError::NonRelationExpression {
            shape: "relation comprehension",
        }),
        _ => Err(RelationLowerError::NonRelationExpression {
            shape: expr_shape(expr),
        }),
    }
}

fn lower_relation_qual_call(
    result_ty: &E::Ty,
    type_name: &str,
    func_name: &str,
    args: &[E::EExpr],
    ctx: &LowerCtx<'_>,
) -> Result<IRRelationExpr, RelationLowerError> {
    match func_name {
        "join" => {
            let [left, right] = two_args(func_name, args)?;
            Ok(IRRelationExpr::Join(
                Box::new(lower_relation_expr(left, ctx)?),
                Box::new(lower_relation_expr(right, ctx)?),
            ))
        }
        "product" => {
            let [left, right] = two_args(func_name, args)?;
            Ok(IRRelationExpr::Product(
                Box::new(lower_relation_expr(left, ctx)?),
                Box::new(lower_relation_expr(right, ctx)?),
            ))
        }
        "transpose" => {
            let arg = one_arg(func_name, args)?;
            Ok(IRRelationExpr::Transpose(Box::new(lower_relation_expr(
                arg, ctx,
            )?)))
        }
        "closure" => {
            let arg = one_arg(func_name, args)?;
            Ok(IRRelationExpr::TransitiveClosure(Box::new(
                lower_relation_expr(arg, ctx)?,
            )))
        }
        "reach" => {
            let arg = one_arg(func_name, args)?;
            Ok(IRRelationExpr::ReflexiveTransitiveClosure(Box::new(
                lower_relation_expr(arg, ctx)?,
            )))
        }
        "project" => {
            let Some((relation, columns)) = args.split_first() else {
                return Err(RelationLowerError::WrongArity {
                    op: func_name.to_owned(),
                    expected: 2,
                    found: 0,
                });
            };
            let columns = columns
                .iter()
                .map(project_column)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(IRRelationExpr::Project {
                expr: Box::new(lower_relation_expr(relation, ctx)?),
                columns,
            })
        }
        "field" => {
            let [store, selector] = two_args(func_name, args)?;
            let (store_name, entity) = store_relation_ref(store)?;
            let (field_owner, field_name) = field_selector(selector)?;
            if entity != field_owner {
                return Err(RelationLowerError::RelationType {
                    message: format!(
                        "Rel::field store entity `{entity}` does not match field owner `{field_owner}`"
                    ),
                });
            }
            Ok(IRRelationExpr::Symbol(IRRelationSymbol {
                name: format!("{store_name}.{field_name}"),
                relation_type: relation_type_from_ty(result_ty, ctx)?,
                mutable: true,
                source: IRRelationSource::EntityField {
                    entity,
                    field: field_name,
                },
            }))
        }
        _ => Err(RelationLowerError::UnsupportedOperator {
            type_name: type_name.to_owned(),
            func_name: func_name.to_owned(),
        }),
    }
}

fn one_arg<'a>(op: &str, args: &'a [E::EExpr]) -> Result<&'a E::EExpr, RelationLowerError> {
    match args {
        [arg] => Ok(arg),
        _ => Err(RelationLowerError::WrongArity {
            op: op.to_owned(),
            expected: 1,
            found: args.len(),
        }),
    }
}

fn project_column(expr: &E::EExpr) -> Result<usize, RelationLowerError> {
    match expr {
        E::EExpr::Lit(_, E::Literal::Int(value), _) if *value >= 0 => Ok(*value as usize),
        E::EExpr::Lit(_, E::Literal::Int(value), _) => {
            Err(RelationLowerError::NegativeProjectColumn { value: *value })
        }
        _ => Err(RelationLowerError::InvalidProjectColumn),
    }
}

fn two_args<'a>(op: &str, args: &'a [E::EExpr]) -> Result<[&'a E::EExpr; 2], RelationLowerError> {
    match args {
        [left, right] => Ok([left, right]),
        _ => Err(RelationLowerError::WrongArity {
            op: op.to_owned(),
            expected: 2,
            found: args.len(),
        }),
    }
}

fn store_relation_ref(expr: &E::EExpr) -> Result<(String, String), RelationLowerError> {
    match expr {
        E::EExpr::Var(E::Ty::Store(entity), name, _) => Ok((name.clone(), entity.clone())),
        E::EExpr::Prime(_, inner, _) => store_relation_ref(inner),
        _ => Err(RelationLowerError::NonRelationExpression {
            shape: expr_shape(expr),
        }),
    }
}

fn field_selector(expr: &E::EExpr) -> Result<(String, String), RelationLowerError> {
    match expr {
        E::EExpr::Qual(_, owner, field, _) => Ok((
            owner.rsplit("::").next().unwrap_or(owner).to_owned(),
            field.clone(),
        )),
        _ => Err(RelationLowerError::NonRelationExpression {
            shape: expr_shape(expr),
        }),
    }
}

fn relation_type_from_ty(
    ty: &E::Ty,
    ctx: &LowerCtx<'_>,
) -> Result<IRRelationType, RelationLowerError> {
    match ty {
        E::Ty::Alias(_, inner) | E::Ty::Newtype(_, inner) => relation_type_from_ty(inner, ctx),
        E::Ty::Refinement(base, _) => relation_type_from_ty(base, ctx),
        E::Ty::Relation(elements) => IRRelationType::new(
            elements
                .iter()
                .map(|element_ty| IRRelationColumn::unnamed(lower_ty(element_ty, ctx)))
                .collect(),
        )
        .map_err(|err| RelationLowerError::RelationType {
            message: format!("{err:?}"),
        }),
        E::Ty::Set(element) => match element.as_ref() {
            E::Ty::Tuple(elements) => IRRelationType::new(
                elements
                    .iter()
                    .map(|element_ty| IRRelationColumn::unnamed(lower_ty(element_ty, ctx)))
                    .collect(),
            )
            .map_err(|err| RelationLowerError::RelationType {
                message: format!("{err:?}"),
            }),
            element_ty => Ok(IRRelationType::unary(lower_ty(element_ty, ctx))),
        },
        _ => Err(RelationLowerError::NonRelationExpression {
            shape: "non-relation type",
        }),
    }
}

fn tuple_relation_literal(
    expr: &E::EExpr,
    relation_ty: &IRRelationType,
) -> Result<IRRelationExpr, RelationLowerError> {
    match expr {
        E::EExpr::TupleLit(_, elems, _) if elems.len() == relation_ty.arity() => {
            Ok(IRRelationExpr::SingletonTuple {
                tuple_type: relation_ty.clone(),
                values: elems
                    .iter()
                    .map(relation_literal_atom)
                    .collect::<Result<Vec<_>, _>>()?,
            })
        }
        _ if relation_ty.arity() == 1 => Ok(IRRelationExpr::SingletonTuple {
            tuple_type: relation_ty.clone(),
            values: vec![relation_literal_atom(expr)?],
        }),
        _ => Err(RelationLowerError::NonRelationExpression {
            shape: expr_shape(expr),
        }),
    }
}

fn relation_literal_atom(expr: &E::EExpr) -> Result<String, RelationLowerError> {
    match expr {
        E::EExpr::Lit(_, E::Literal::Int(value), _) => Ok(value.to_string()),
        E::EExpr::Lit(_, E::Literal::Real(value), _) => Ok(value.to_string()),
        E::EExpr::Lit(_, E::Literal::Float(value), _) => Ok(value.to_string()),
        E::EExpr::Lit(_, E::Literal::Str(value), _) => Ok(value.clone()),
        E::EExpr::Lit(_, E::Literal::Bool(value), _) => Ok(value.to_string()),
        E::EExpr::Var(_, name, _) => Ok(name.clone()),
        E::EExpr::Qual(_, qualifier, name, _) => Ok(format!("{qualifier}::{name}")),
        _ => Err(RelationLowerError::NonRelationExpression {
            shape: expr_shape(expr),
        }),
    }
}

fn is_relation_ty(ty: &E::Ty) -> bool {
    match ty {
        E::Ty::Alias(_, inner) | E::Ty::Newtype(_, inner) => is_relation_ty(inner),
        E::Ty::Refinement(base, _) => is_relation_ty(base),
        E::Ty::Relation(_) | E::Ty::Set(_) => true,
        _ => false,
    }
}

fn expr_shape(expr: &E::EExpr) -> &'static str {
    match expr {
        E::EExpr::Lit(..) => "literal",
        E::EExpr::Var(..) => "variable",
        E::EExpr::Field(..) => "field",
        E::EExpr::Prime(..) => "prime",
        E::EExpr::BinOp(..) => "binary operator",
        E::EExpr::UnOp(..) => "unary operator",
        E::EExpr::Call(..) => "call",
        E::EExpr::CallR(..) => "ref call",
        E::EExpr::Qual(..) => "qualified name",
        E::EExpr::Quant(..) => "quantifier",
        E::EExpr::Always(..) => "always",
        E::EExpr::Eventually(..) => "eventually",
        E::EExpr::Until(..) => "until",
        E::EExpr::Historically(..) => "historically",
        E::EExpr::Once(..) => "once",
        E::EExpr::Previously(..) => "previously",
        E::EExpr::Since(..) => "since",
        E::EExpr::Assert(..) => "assert",
        E::EExpr::Assume(..) => "assume",
        E::EExpr::Assign(..) => "assign",
        E::EExpr::NamedPair(..) => "named pair",
        E::EExpr::Seq(..) => "sequence",
        E::EExpr::SameStep(..) => "same-step",
        E::EExpr::Let(..) => "let",
        E::EExpr::Lam(..) => "lambda",
        E::EExpr::Unresolved(..) => "unresolved",
        E::EExpr::TupleLit(..) => "tuple literal",
        E::EExpr::In(..) => "membership",
        E::EExpr::Card(..) => "cardinality",
        E::EExpr::Pipe(..) => "pipe",
        E::EExpr::Match(..) => "match",
        E::EExpr::Choose(..) => "choose",
        E::EExpr::MapUpdate(..) => "map update",
        E::EExpr::Index(..) => "index",
        E::EExpr::SetComp(..) => "set comprehension",
        E::EExpr::RelComp(..) => "relation comprehension",
        E::EExpr::SetLit(..) => "set literal",
        E::EExpr::SeqLit(..) => "seq literal",
        E::EExpr::MapLit(..) => "map literal",
        E::EExpr::QualCall(..) => "qualified call",
        E::EExpr::Sorry(..) => "sorry",
        E::EExpr::Todo(..) => "todo",
        E::EExpr::Block(..) => "block",
        E::EExpr::VarDecl(..) => "var declaration",
        E::EExpr::While(..) => "while",
        E::EExpr::IfElse(..) => "if/else",
        E::EExpr::Aggregate(..) => "aggregate",
        E::EExpr::Saw(..) => "saw",
        E::EExpr::CtorRecord(..) => "constructor record",
        E::EExpr::StructCtor(..) => "struct constructor",
    }
}
