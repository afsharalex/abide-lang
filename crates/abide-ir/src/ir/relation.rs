//! Backend-neutral bounded relation expressions.
//!
//! This module records the typed relational surface that bounded backends can
//! lower to SAT. It is intentionally independent from any one solver encoding.

use serde::Serialize;

use super::types::{IREntity, IRStoreDecl, IRType};

/// One column in an [`IRRelationType`]. `name` is optional —
/// store-extent relations carry unnamed columns.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRRelationColumn {
    pub name: Option<String>,
    #[serde(rename = "type")]
    pub ty: IRType,
}

impl IRRelationColumn {
    pub fn unnamed(ty: IRType) -> Self {
        Self { name: None, ty }
    }

    pub fn named(name: impl Into<String>, ty: IRType) -> Self {
        Self {
            name: Some(name.into()),
            ty,
        }
    }
}

/// Type of a relation expression: an ordered list of columns. Arity
/// is `columns.len()`; zero-arity relations are rejected.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRRelationType {
    pub columns: Vec<IRRelationColumn>,
}

impl IRRelationType {
    pub fn new(columns: Vec<IRRelationColumn>) -> Result<Self, IRRelationTypeError> {
        if columns.is_empty() {
            return Err(IRRelationTypeError::ZeroArityRelation);
        }
        Ok(Self { columns })
    }

    pub fn unary(ty: IRType) -> Self {
        Self {
            columns: vec![IRRelationColumn::unnamed(ty)],
        }
    }

    pub fn binary(left: IRType, right: IRType) -> Self {
        Self {
            columns: vec![
                IRRelationColumn::unnamed(left),
                IRRelationColumn::unnamed(right),
            ],
        }
    }

    pub fn arity(&self) -> usize {
        self.columns.len()
    }

    pub fn tuple_type(&self) -> IRType {
        IRType::Tuple {
            elements: self
                .columns
                .iter()
                .map(|column| column.ty.clone())
                .collect(),
        }
    }
}

/// Origin of a relation symbol — informs the backend whether the
/// relation is mutable (extents, fields) or read-only (user / derived).
#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum IRRelationSource {
    /// Membership of a `Store<E>`.
    StoreExtent { store: String, entity: String },
    /// `Entity.field` lifted to a binary relation.
    EntityField { entity: String, field: String },
    /// Top-level `Rel<...>` declaration.
    UserRelation { name: String },
    /// Result of a `derived` relation expression.
    Derived,
}

/// A named relation handle the backend can address.
///
/// `mutable` is `true` for store extents and entity fields (rewritten
/// by transitions), `false` for user and derived relations.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRRelationSymbol {
    pub name: String,
    #[serde(rename = "type")]
    pub relation_type: IRRelationType,
    pub mutable: bool,
    pub source: IRRelationSource,
}

impl IRRelationSymbol {
    pub fn store_extent(store: impl Into<String>, entity: impl Into<String>) -> Self {
        let store = store.into();
        let entity = entity.into();
        Self {
            name: store.clone(),
            relation_type: IRRelationType::unary(IRType::Entity {
                name: entity.clone(),
            }),
            mutable: true,
            source: IRRelationSource::StoreExtent { store, entity },
        }
    }

    pub fn entity_field(
        entity: impl Into<String>,
        field: impl Into<String>,
        field_type: IRType,
    ) -> Self {
        let entity = entity.into();
        let field = field.into();
        Self {
            name: format!("{entity}.{field}"),
            relation_type: IRRelationType::binary(
                IRType::Entity {
                    name: entity.clone(),
                },
                field_type,
            ),
            mutable: true,
            source: IRRelationSource::EntityField { entity, field },
        }
    }
}

pub fn relation_symbol_for_store(store: &IRStoreDecl) -> IRRelationSymbol {
    IRRelationSymbol::store_extent(&store.name, &store.entity_type)
}

pub fn relation_symbols_for_entity_fields(entity: &IREntity) -> Vec<IRRelationSymbol> {
    entity
        .fields
        .iter()
        .map(|field| IRRelationSymbol::entity_field(&entity.name, &field.name, field.ty.clone()))
        .collect()
}

/// Bounded relation-algebra expression.
///
/// This is the IR consumed by the SAT-backed relational fragment of
/// the verifier. Each variant mirrors a surface `Rel::*` operation or
/// a literal; [`Self::relation_type`] performs structural type checking
/// to confirm join/transpose/closure operands are well-shaped.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum IRRelationExpr {
    /// Reference to a named relation symbol.
    Symbol(IRRelationSymbol),
    /// Empty relation of the given type.
    Empty(IRRelationType),
    /// `{ (v1, v2, …) }` literal — a single tuple.
    SingletonTuple {
        tuple_type: IRRelationType,
        values: Vec<String>,
    },
    /// Set union.
    Union(Box<IRRelationExpr>, Box<IRRelationExpr>),
    /// Set intersection.
    Intersection(Box<IRRelationExpr>, Box<IRRelationExpr>),
    /// Set difference (`left \ right`).
    Difference(Box<IRRelationExpr>, Box<IRRelationExpr>),
    /// Cartesian product — concatenates column lists.
    Product(Box<IRRelationExpr>, Box<IRRelationExpr>),
    /// Natural join on `left`'s last column and `right`'s first
    /// column. Drops the joined columns from the result.
    Join(Box<IRRelationExpr>, Box<IRRelationExpr>),
    /// Column projection by ordered index list.
    Project {
        expr: Box<IRRelationExpr>,
        columns: Vec<usize>,
    },
    /// Swap columns of a binary relation.
    Transpose(Box<IRRelationExpr>),
    /// `R^+` — transitive closure of a homogeneous binary relation.
    TransitiveClosure(Box<IRRelationExpr>),
    /// `R^*` — reflexive transitive closure of a homogeneous binary relation.
    ReflexiveTransitiveClosure(Box<IRRelationExpr>),
}

impl IRRelationExpr {
    pub fn relation_type(&self) -> Result<IRRelationType, IRRelationTypeError> {
        match self {
            Self::Symbol(symbol) => Ok(symbol.relation_type.clone()),
            Self::Empty(ty) | Self::SingletonTuple { tuple_type: ty, .. } => Ok(ty.clone()),
            Self::Union(left, right)
            | Self::Intersection(left, right)
            | Self::Difference(left, right) => {
                let left_ty = left.relation_type()?;
                let right_ty = right.relation_type()?;
                if left_ty == right_ty {
                    Ok(left_ty)
                } else {
                    Err(IRRelationTypeError::MismatchedRelationTypes {
                        left: left_ty,
                        right: right_ty,
                    })
                }
            }
            Self::Product(left, right) => {
                let mut columns = left.relation_type()?.columns;
                columns.extend(right.relation_type()?.columns);
                IRRelationType::new(columns)
            }
            Self::Join(left, right) => {
                let left_ty = left.relation_type()?;
                let right_ty = right.relation_type()?;
                let Some(left_join) = left_ty.columns.last() else {
                    return Err(IRRelationTypeError::ZeroArityRelation);
                };
                let Some(right_join) = right_ty.columns.first() else {
                    return Err(IRRelationTypeError::ZeroArityRelation);
                };
                if left_join.ty != right_join.ty {
                    return Err(IRRelationTypeError::JoinTypeMismatch {
                        left: left_join.ty.clone(),
                        right: right_join.ty.clone(),
                    });
                }
                let mut columns = left_ty.columns[..left_ty.columns.len() - 1].to_vec();
                columns.extend(right_ty.columns[1..].iter().cloned());
                IRRelationType::new(columns)
            }
            Self::Project { expr, columns } => {
                let source_ty = expr.relation_type()?;
                let mut projected = Vec::with_capacity(columns.len());
                for &idx in columns {
                    let Some(column) = source_ty.columns.get(idx) else {
                        return Err(IRRelationTypeError::ColumnOutOfBounds {
                            column: idx,
                            arity: source_ty.arity(),
                        });
                    };
                    projected.push(column.clone());
                }
                IRRelationType::new(projected)
            }
            Self::Transpose(expr) => {
                let source_ty = expr.relation_type()?;
                if source_ty.arity() != 2 {
                    return Err(IRRelationTypeError::RequiresBinaryRelation {
                        found: source_ty.arity(),
                    });
                }
                IRRelationType::new(vec![
                    source_ty.columns[1].clone(),
                    source_ty.columns[0].clone(),
                ])
            }
            Self::TransitiveClosure(expr) | Self::ReflexiveTransitiveClosure(expr) => {
                let source_ty = expr.relation_type()?;
                if source_ty.arity() != 2 {
                    return Err(IRRelationTypeError::RequiresBinaryRelation {
                        found: source_ty.arity(),
                    });
                }
                if source_ty.columns[0].ty != source_ty.columns[1].ty {
                    return Err(IRRelationTypeError::ClosureTypeMismatch {
                        left: source_ty.columns[0].ty.clone(),
                        right: source_ty.columns[1].ty.clone(),
                    });
                }
                Ok(source_ty)
            }
        }
    }
}

/// Errors produced by structural typing of [`IRRelationExpr`].
#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum IRRelationTypeError {
    /// A relation type was constructed with zero columns.
    ZeroArityRelation,
    /// Union/intersection/difference operands had different shapes.
    MismatchedRelationTypes {
        left: IRRelationType,
        right: IRRelationType,
    },
    /// Join: left's last column type ≠ right's first column type.
    JoinTypeMismatch { left: IRType, right: IRType },
    /// `Project` referenced a column index past the source arity.
    ColumnOutOfBounds { column: usize, arity: usize },
    /// Transpose/closure was applied to a non-binary relation.
    RequiresBinaryRelation { found: usize },
    /// Closure operand wasn't homogeneous (both columns same type).
    ClosureTypeMismatch { left: IRType, right: IRType },
}

#[cfg(test)]
mod tests {
    use super::*;

    fn entity(name: &str) -> IRType {
        IRType::Entity {
            name: name.to_owned(),
        }
    }

    #[test]
    fn store_extent_symbol_records_unary_mutable_entity_relation() {
        let orders = IRRelationSymbol::store_extent("orders", "Order");

        assert_eq!(orders.name, "orders");
        assert!(orders.mutable);
        assert_eq!(orders.relation_type, IRRelationType::unary(entity("Order")));
        assert_eq!(
            orders.source,
            IRRelationSource::StoreExtent {
                store: "orders".to_owned(),
                entity: "Order".to_owned()
            }
        );
    }

    #[test]
    fn entity_field_symbol_records_binary_source_projection() {
        let status = IRRelationSymbol::entity_field("Order", "status", IRType::String);

        assert_eq!(status.name, "Order.status");
        assert_eq!(
            status.relation_type,
            IRRelationType::binary(entity("Order"), IRType::String)
        );
        assert_eq!(
            status.source,
            IRRelationSource::EntityField {
                entity: "Order".to_owned(),
                field: "status".to_owned()
            }
        );
    }

    #[test]
    fn join_type_removes_matching_middle_columns() {
        let left = IRRelationExpr::Empty(
            IRRelationType::new(vec![
                IRRelationColumn::named("order", entity("Order")),
                IRRelationColumn::named("customer", entity("Customer")),
            ])
            .expect("binary relation type"),
        );
        let right = IRRelationExpr::Empty(
            IRRelationType::new(vec![
                IRRelationColumn::named("customer", entity("Customer")),
                IRRelationColumn::named("segment", IRType::String),
            ])
            .expect("binary relation type"),
        );

        let joined = IRRelationExpr::Join(Box::new(left), Box::new(right))
            .relation_type()
            .expect("join should typecheck");

        assert_eq!(
            joined,
            IRRelationType::new(vec![
                IRRelationColumn::named("order", entity("Order")),
                IRRelationColumn::named("segment", IRType::String),
            ])
            .expect("binary relation type")
        );
    }

    #[test]
    fn closure_requires_homogeneous_binary_relation() {
        let edge = IRRelationExpr::Empty(IRRelationType::binary(entity("Node"), entity("Node")));
        assert_eq!(
            IRRelationExpr::TransitiveClosure(Box::new(edge))
                .relation_type()
                .expect("homogeneous binary closure"),
            IRRelationType::binary(entity("Node"), entity("Node"))
        );

        let bad =
            IRRelationExpr::Empty(IRRelationType::binary(entity("Order"), entity("Customer")));
        assert!(matches!(
            IRRelationExpr::TransitiveClosure(Box::new(bad)).relation_type(),
            Err(IRRelationTypeError::ClosureTypeMismatch { .. })
        ));
    }

    #[test]
    fn relation_symbols_lower_store_and_entity_fields() {
        let store = IRStoreDecl {
            name: "orders".to_owned(),
            entity_type: "Order".to_owned(),
            lo: 0,
            hi: 3,
        };
        assert_eq!(
            relation_symbol_for_store(&store),
            IRRelationSymbol::store_extent("orders", "Order")
        );

        let order = IREntity {
            name: "Order".to_owned(),
            fields: vec![super::super::types::IRField {
                name: "status".to_owned(),
                ty: IRType::String,
                default: None,
                initial_constraint: None,
            }],
            transitions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };

        assert_eq!(
            relation_symbols_for_entity_fields(&order),
            vec![IRRelationSymbol::entity_field(
                "Order",
                "status",
                IRType::String
            )]
        );
    }
}
