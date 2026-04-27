use super::*;

pub(in crate::verify::ic3) fn ic3_match_pattern_cond(
    scrut: &str,
    pattern: &crate::ir::types::IRPattern,
    vctx: &VerifyContext,
) -> Result<String, String> {
    use crate::ir::types::IRPattern;
    match pattern {
        IRPattern::PWild | IRPattern::PVar { .. } => Ok("true".to_owned()),
        IRPattern::PCtor { name, fields } => {
            if let Some(variant) = ic3_lookup_ctor_variant(name, vctx) {
                if fields.is_empty() && variant.accessor_names.is_empty() {
                    return Ok(format!("((_ is {}) {scrut})", variant.ctor_name));
                }
                for field in fields {
                    if !variant
                        .accessor_names
                        .iter()
                        .any(|accessor| accessor == &field.name)
                    {
                        return Err(format!(
                            "unknown field '{}' in IC3 match pattern for constructor '{name}'",
                            field.name
                        ));
                    }
                }
                return Ok(format!("((_ is {}) {scrut})", variant.ctor_name));
            }
            for ((type_name, variant_name), id) in &vctx.variants.to_id {
                if variant_name == name || format!("{type_name}::{variant_name}") == *name {
                    return Ok(format!("(= {scrut} {id})"));
                }
            }
            Err(format!(
                "unknown constructor pattern in IC3 encoding: {name}"
            ))
        }
        IRPattern::POr { left, right } => {
            let l = ic3_match_pattern_cond(scrut, left, vctx)?;
            let r = ic3_match_pattern_cond(scrut, right, vctx)?;
            Ok(format!("(or {l} {r})"))
        }
    }
}

pub(in crate::verify::ic3) fn ic3_match_pattern_bindings(
    scrut: &str,
    pattern: &crate::ir::types::IRPattern,
    vctx: &VerifyContext,
) -> Result<Vec<(String, String)>, String> {
    use crate::ir::types::IRPattern;
    match pattern {
        IRPattern::PWild => Ok(Vec::new()),
        IRPattern::PVar { name } => Ok(vec![(name.clone(), scrut.to_owned())]),
        IRPattern::PCtor { name, fields } => {
            if fields.is_empty() {
                return Ok(Vec::new());
            }
            let Some(variant) = ic3_lookup_ctor_variant(name, vctx) else {
                return Err(format!(
                    "unknown constructor pattern in IC3 encoding: {name}"
                ));
            };
            let mut bindings = Vec::new();
            for field in fields {
                if !variant
                    .accessor_names
                    .iter()
                    .any(|accessor| accessor == &field.name)
                {
                    return Err(format!(
                        "unknown field '{}' in IC3 match pattern for constructor '{name}'",
                        field.name
                    ));
                }
                let field_term = format!("({} {scrut})", field.name);
                bindings.extend(ic3_match_pattern_bindings(
                    &field_term,
                    &field.pattern,
                    vctx,
                )?);
            }
            Ok(bindings)
        }
        IRPattern::POr { .. } => ic3_or_pattern_bindings(scrut, pattern, vctx),
    }
}

pub(in crate::verify::ic3) fn ic3_or_pattern_bindings(
    scrut: &str,
    pattern: &crate::ir::types::IRPattern,
    vctx: &VerifyContext,
) -> Result<Vec<(String, String)>, String> {
    use crate::ir::types::IRPattern;
    let IRPattern::POr { left, right } = pattern else {
        return Ok(Vec::new());
    };

    let left_bindings = ic3_match_pattern_bindings(scrut, left, vctx)?;
    let right_bindings = ic3_match_pattern_bindings(scrut, right, vctx)?;
    if left_bindings.is_empty() && right_bindings.is_empty() {
        return Ok(Vec::new());
    }

    let left_map: HashMap<_, _> = left_bindings.into_iter().collect();
    let right_map: HashMap<_, _> = right_bindings.into_iter().collect();

    let mut left_names: Vec<_> = left_map.keys().cloned().collect();
    let mut right_names: Vec<_> = right_map.keys().cloned().collect();
    left_names.sort();
    right_names.sort();
    if left_names != right_names {
        return Err(
            "or-pattern bindings in IC3 require both alternatives to bind the same names"
                .to_owned(),
        );
    }

    let left_cond = ic3_match_pattern_cond(scrut, left, vctx)?;
    let mut merged = Vec::new();
    for name in left_names {
        let left_value = left_map
            .get(&name)
            .expect("name comes from left_names collection");
        let right_value = right_map
            .get(&name)
            .expect("name comes from right_names collection");
        merged.push((
            name,
            format!("(ite {left_cond} {left_value} {right_value})"),
        ));
    }
    Ok(merged)
}

struct Ic3CtorVariant {
    ctor_name: String,
    accessor_names: Vec<String>,
}

fn ic3_lookup_ctor_variant(name: &str, vctx: &VerifyContext) -> Option<Ic3CtorVariant> {
    for (enum_name, dt) in &vctx.adt_sorts {
        for variant in &dt.variants {
            let ctor_name = smt::func_decl_name(&variant.constructor);
            if ctor_name == name || format!("{enum_name}::{ctor_name}") == name {
                return Some(Ic3CtorVariant {
                    ctor_name,
                    accessor_names: variant.accessors.iter().map(smt::func_decl_name).collect(),
                });
            }
        }
    }
    None
}

pub(in crate::verify::ic3) fn ic3_match_has_final_catch_all(
    arms: &[crate::ir::types::IRMatchArm],
) -> bool {
    use crate::ir::types::IRPattern;
    arms.last().is_some_and(|arm| {
        arm.guard.is_none() && matches!(arm.pattern, IRPattern::PWild | IRPattern::PVar { .. })
    })
}

pub(in crate::verify::ic3) fn ic3_ctor_term_with<F>(
    enum_name: &str,
    ctor: &str,
    args: &[(String, IRExpr)],
    vctx: &VerifyContext,
    mut encode_arg: F,
) -> Result<String, String>
where
    F: FnMut(&IRExpr) -> Result<String, String>,
{
    if let Some(variant) = ic3_lookup_ctor_variant(ctor, vctx) {
        if args.is_empty() {
            if !variant.accessor_names.is_empty() {
                return Err(format!(
                    "constructor '{ctor}' of '{enum_name}' requires {} field argument(s)",
                    variant.accessor_names.len()
                ));
            }
            return Ok(variant.ctor_name);
        }

        let mut args_by_name = HashMap::new();
        for (field_name, field_expr) in args {
            if !variant
                .accessor_names
                .iter()
                .any(|accessor| accessor == field_name)
            {
                return Err(format!(
                    "unknown field '{field_name}' for constructor '{ctor}' in IC3 encoding"
                ));
            }
            args_by_name.insert(field_name.as_str(), field_expr);
        }

        let mut ordered_args = Vec::new();
        for accessor in &variant.accessor_names {
            let Some(field_expr) = args_by_name.get(accessor.as_str()) else {
                return Err(format!(
                    "missing field '{accessor}' for constructor '{ctor}' in IC3 encoding"
                ));
            };
            ordered_args.push(encode_arg(field_expr)?);
        }

        return Ok(format!(
            "({} {})",
            variant.ctor_name,
            ordered_args.join(" ")
        ));
    }

    Ok(vctx.variants.try_id_of(enum_name, ctor)?.to_string())
}
