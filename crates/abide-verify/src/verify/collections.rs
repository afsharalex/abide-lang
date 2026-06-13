//! Shared finite collection encoding helpers for verifier backends.

use std::collections::HashSet;

use crate::ir::types::{IRExpr, IRType};
use crate::verify::smt::{self, SmtValue};

pub(super) fn encode_set_literal<F>(
    elements: &[IRExpr],
    ty: &IRType,
    mut encode_expr: F,
) -> Result<SmtValue, String>
where
    F: FnMut(&IRExpr) -> Result<SmtValue, String>,
{
    let IRType::Set { element } = ty else {
        return Err(format!("SetLit with non-Set type: {ty:?}"));
    };
    let elem_sort = smt::ir_type_to_sort(element);
    let false_val = smt::bool_val(false).to_dynamic();
    let true_val = smt::bool_val(true).to_dynamic();
    let mut arr = smt::const_array(&elem_sort, &false_val);
    for elem in elements {
        let encoded = encode_expr(elem)?;
        arr = arr.store(&encoded.to_dynamic(), &true_val);
    }
    Ok(SmtValue::Array(arr))
}

pub(super) fn encode_seq_literal<F>(
    elements: &[IRExpr],
    ty: &IRType,
    mut encode_expr: F,
) -> Result<SmtValue, String>
where
    F: FnMut(&IRExpr) -> Result<SmtValue, String>,
{
    let IRType::Seq { element } = ty else {
        return Err(format!("SeqLit with non-Seq type: {ty:?}"));
    };
    let encoded = elements
        .iter()
        .map(&mut encode_expr)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(smt::seq_literal(element, &encoded))
}

pub(super) fn encode_map_literal<F>(
    entries: &[(IRExpr, IRExpr)],
    ty: &IRType,
    mut encode_expr: F,
) -> Result<SmtValue, String>
where
    F: FnMut(&IRExpr) -> Result<SmtValue, String>,
{
    let IRType::Map { key, value } = ty else {
        return Err(format!("MapLit with non-Map type: {ty:?}"));
    };
    let key_sort = smt::ir_type_to_sort(key);
    let default_val = smt::map_none_dynamic(value);
    let mut arr = smt::const_array(&key_sort, &default_val);
    for (key_expr, value_expr) in entries {
        let key_val = encode_expr(key_expr)?;
        let value_val = encode_expr(value_expr)?;
        arr = arr.store(
            &key_val.to_dynamic(),
            &smt::map_some_dynamic(value, &value_val),
        );
    }
    Ok(SmtValue::Array(arr))
}

pub(super) fn encode_collection_index(
    collection: &SmtValue,
    key: &SmtValue,
    collection_ty: Option<&IRType>,
    result_ty: &IRType,
) -> Result<SmtValue, String> {
    match collection_ty {
        Some(IRType::Map { value, .. }) => smt::map_lookup(collection, key, value),
        Some(IRType::Seq { element }) => smt::seq_index(collection, key, element),
        _ => Ok(smt::dynamic_to_typed_value(
            collection.as_array()?.select(&key.to_dynamic()),
            result_ty,
        )),
    }
}

pub(super) fn encode_collection_update(
    collection: &SmtValue,
    key: &SmtValue,
    value: &SmtValue,
    collection_ty: Option<&IRType>,
) -> Result<SmtValue, String> {
    if let Some(IRType::Map {
        value: value_ty, ..
    }) = collection_ty
    {
        return smt::map_store(collection, key, value, value_ty);
    }
    Ok(SmtValue::Array(
        collection
            .as_array()?
            .store(&key.to_dynamic(), &value.to_dynamic()),
    ))
}

pub(super) fn finite_literal_cardinality(expr: &IRExpr) -> Option<usize> {
    match expr {
        IRExpr::SetLit { elements, .. } => Some(unique_expr_count(elements.iter())),
        IRExpr::SeqLit { elements, .. } => Some(elements.len()),
        IRExpr::MapLit { entries, .. } => {
            Some(unique_expr_count(entries.iter().map(|(key, _)| key)))
        }
        _ => None,
    }
}

pub(super) fn encode_unique_projected_cardinality<I, T, F>(
    candidates: I,
    mut encode_candidate: F,
) -> Result<SmtValue, String>
where
    I: IntoIterator<Item = T>,
    F: FnMut(T) -> Result<(smt::Bool, SmtValue), String>,
{
    let one = smt::int_lit(1);
    let zero = smt::int_lit(0);
    let mut terms = Vec::new();
    let mut prior_counted_keys: Vec<(SmtValue, smt::Bool)> = Vec::new();

    for candidate in candidates {
        let (include_raw, key) = encode_candidate(candidate)?;
        let mut include_once = include_raw.clone();
        for (prior_key, prior_counted) in &prior_counted_keys {
            let same_key = smt::smt_eq(&key, prior_key)?;
            let prior_counted_same_key = smt::bool_and(&[prior_counted, &same_key]);
            include_once = smt::bool_and(&[&include_once, &smt::bool_not(&prior_counted_same_key)]);
        }
        terms.push(smt::int_ite(&include_once, &one, &zero));
        prior_counted_keys.push((key, include_once));
    }

    Ok(int_sum_or_zero(terms))
}

pub(super) fn int_sum_or_zero(terms: Vec<smt::Int>) -> SmtValue {
    if terms.is_empty() {
        smt::int_val(0)
    } else {
        let refs: Vec<&smt::Int> = terms.iter().collect();
        SmtValue::Int(smt::int_add(&refs))
    }
}

fn unique_expr_count<'a>(exprs: impl IntoIterator<Item = &'a IRExpr>) -> usize {
    exprs
        .into_iter()
        .map(|expr| format!("{expr:?}"))
        .collect::<HashSet<_>>()
        .len()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::types::{IRExpr, IRType, LitVal};
    use crate::verify::smt::{self, AbideSolver, SatResult, SmtValue};

    fn int_lit(value: i64) -> IRExpr {
        IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value },
            span: None,
        }
    }

    fn assert_bool_value(value: SmtValue, expected: bool) {
        let actual = value.to_bool().expect("boolean value");
        let solver = AbideSolver::new();
        solver.assert(smt::bool_not(
            &smt::smt_eq(&SmtValue::Bool(actual), &smt::bool_val(expected)).expect("bool equality"),
        ));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    fn assert_value_eq(actual: &SmtValue, expected: &SmtValue) {
        let solver = AbideSolver::new();
        solver.assert(smt::bool_not(
            &smt::smt_eq(actual, expected).expect("value equality"),
        ));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn finite_collection_helpers_cover_literals_lookup_update_and_cardinality() {
        let set_ty = IRType::Set {
            element: Box::new(IRType::Int),
        };
        let set = encode_set_literal(&[int_lit(1), int_lit(2)], &set_ty, |expr| match expr {
            IRExpr::Lit {
                value: LitVal::Int { value },
                ..
            } => Ok(smt::int_val(*value)),
            other => Err(format!("unexpected test expression: {other:?}")),
        })
        .expect("set literal");
        assert_bool_value(
            smt::binop("OpSetMember", &smt::int_val(2), &set).expect("set membership"),
            true,
        );

        let map_ty = IRType::Map {
            key: Box::new(IRType::Int),
            value: Box::new(IRType::Bool),
        };
        let map = encode_map_literal(
            &[(
                int_lit(1),
                IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
            )],
            &map_ty,
            |expr| match expr {
                IRExpr::Lit {
                    value: LitVal::Int { value },
                    ..
                } => Ok(smt::int_val(*value)),
                IRExpr::Lit {
                    value: LitVal::Bool { value },
                    ..
                } => Ok(smt::bool_val(*value)),
                other => Err(format!("unexpected test expression: {other:?}")),
            },
        )
        .expect("map literal");
        assert_bool_value(
            encode_collection_index(&map, &smt::int_val(1), Some(&map_ty), &IRType::Bool)
                .expect("map lookup"),
            true,
        );

        let updated =
            encode_collection_update(&map, &smt::int_val(2), &smt::bool_val(true), Some(&map_ty))
                .expect("map update");
        assert_bool_value(
            encode_collection_index(&updated, &smt::int_val(2), Some(&map_ty), &IRType::Bool)
                .expect("updated map lookup"),
            true,
        );

        let seq_ty = IRType::Seq {
            element: Box::new(IRType::Int),
        };
        let seq = encode_seq_literal(&[int_lit(3), int_lit(4)], &seq_ty, |expr| match expr {
            IRExpr::Lit {
                value: LitVal::Int { value },
                ..
            } => Ok(smt::int_val(*value)),
            other => Err(format!("unexpected test expression: {other:?}")),
        })
        .expect("seq literal");
        assert_value_eq(
            &encode_collection_index(&seq, &smt::int_val(1), Some(&seq_ty), &IRType::Int)
                .expect("seq index"),
            &smt::int_val(4),
        );

        assert_eq!(
            finite_literal_cardinality(&IRExpr::SetLit {
                elements: vec![int_lit(1), int_lit(1), int_lit(2)],
                ty: set_ty,
                span: None,
            }),
            Some(2)
        );
    }

    #[test]
    fn finite_collection_helpers_count_unique_projected_candidates() {
        let candidates = vec![
            (smt::bool_val(true).to_bool().unwrap(), smt::int_val(1)),
            (smt::bool_val(true).to_bool().unwrap(), smt::int_val(1)),
            (smt::bool_val(false).to_bool().unwrap(), smt::int_val(2)),
            (smt::bool_val(true).to_bool().unwrap(), smt::int_val(3)),
        ];
        assert_value_eq(
            &encode_unique_projected_cardinality(candidates, Ok).expect("unique cardinality"),
            &smt::int_val(2),
        );
    }
}
