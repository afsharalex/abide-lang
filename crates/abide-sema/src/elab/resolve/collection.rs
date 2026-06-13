//! Collection expression and comprehension helpers.

use std::collections::HashMap;

use crate::elab::types::{ESetCompBinder, Ty};

pub(super) fn set_source_element_type(source_ty: &Ty) -> Ty {
    match source_ty {
        Ty::Set(element) | Ty::Seq(element) => element.as_ref().clone(),
        Ty::Map(key, value) => Ty::Tuple(vec![key.as_ref().clone(), value.as_ref().clone()]),
        Ty::Store(entity) => Ty::Entity(entity.clone()),
        _ => Ty::Error,
    }
}

pub(super) fn bind_set_comp_binder(
    bound: &mut HashMap<String, Ty>,
    binder: &ESetCompBinder,
    binder_ty: &Ty,
) {
    match binder {
        ESetCompBinder::Var(name) => {
            bound.insert(name.clone(), binder_ty.clone());
        }
        ESetCompBinder::Wild => {}
        ESetCompBinder::Tuple(items) => {
            if let Ty::Tuple(columns) = binder_ty {
                for (item, item_ty) in items.iter().zip(columns) {
                    bind_set_comp_binder(bound, item, item_ty);
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct SetCompBinderShapeError {
    actual: usize,
    expected: usize,
}

impl SetCompBinderShapeError {
    pub(super) fn message(&self) -> String {
        format!(
            "set comprehension tuple binder has {} item(s), but source element type has {} component(s)",
            self.actual, self.expected
        )
    }
}

pub(super) fn validate_set_comp_binder_shape(
    binder: &ESetCompBinder,
    binder_ty: &Ty,
) -> Option<SetCompBinderShapeError> {
    match binder {
        ESetCompBinder::Var(_) | ESetCompBinder::Wild => None,
        ESetCompBinder::Tuple(items) => {
            let Ty::Tuple(columns) = binder_ty else {
                return Some(SetCompBinderShapeError {
                    actual: items.len(),
                    expected: 1,
                });
            };
            if items.len() != columns.len() {
                return Some(SetCompBinderShapeError {
                    actual: items.len(),
                    expected: columns.len(),
                });
            }
            items
                .iter()
                .zip(columns.iter())
                .find_map(|(item, column_ty)| validate_set_comp_binder_shape(item, column_ty))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::elab::types::BuiltinTy;

    fn int_ty() -> Ty {
        Ty::Builtin(BuiltinTy::Int)
    }

    fn string_ty() -> Ty {
        Ty::Builtin(BuiltinTy::String)
    }

    #[test]
    fn source_element_type_treats_maps_as_key_value_tuples() {
        let element_ty =
            set_source_element_type(&Ty::Map(Box::new(int_ty()), Box::new(string_ty())));

        assert!(
            matches!(
                element_ty,
                Ty::Tuple(items)
                    if matches!(items.as_slice(), [Ty::Builtin(BuiltinTy::Int), Ty::Builtin(BuiltinTy::String)])
            ),
            "map sources should expose key/value tuple elements"
        );
    }

    #[test]
    fn bind_set_comp_binder_binds_tuple_items_and_ignores_wildcards() {
        let mut bound = HashMap::new();
        let binder = ESetCompBinder::Tuple(vec![
            ESetCompBinder::Var("k".to_owned()),
            ESetCompBinder::Wild,
        ]);
        bind_set_comp_binder(&mut bound, &binder, &Ty::Tuple(vec![int_ty(), string_ty()]));

        assert!(
            matches!(bound.get("k"), Some(Ty::Builtin(BuiltinTy::Int))),
            "key binder should have int type, got {:?}",
            bound.get("k")
        );
        assert!(
            !bound.contains_key("_"),
            "wildcard binders must not enter expression scope"
        );
    }

    #[test]
    fn validate_set_comp_binder_shape_rejects_wrong_tuple_arity() {
        let binder = ESetCompBinder::Tuple(vec![
            ESetCompBinder::Var("k".to_owned()),
            ESetCompBinder::Wild,
            ESetCompBinder::Wild,
        ]);
        let error =
            validate_set_comp_binder_shape(&binder, &Ty::Tuple(vec![int_ty(), string_ty()]))
                .expect("shape error");

        assert_eq!(
            error.message(),
            "set comprehension tuple binder has 3 item(s), but source element type has 2 component(s)"
        );
    }
}
