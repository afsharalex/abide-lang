//! Definition environment for fn/pred/prop lookup during Z3 encoding.
//!
//! After lowering, all definitions (fn, pred, prop) are stored uniformly as
//! `IRFunction` in `IRProgram.functions`. This module provides on-demand
//! expansion of definition references during verification encoding.
//!
//! - Props (nullary, return Bool) are expanded when a `Var` reference matches.
//! - Preds (parameterized, return Bool) are expanded when an `App` chain matches.
//! - Fns (general) are expanded the same way as preds.

use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicU64, Ordering};

use crate::ir::types::{IRExpr, IRProgram, IRType};

/// Global counter for generating fresh variable names during alpha-renaming.
static FRESH_COUNTER: AtomicU64 = AtomicU64::new(0);

/// A single definition entry: parameters + body.
#[derive(Debug, Clone)]
pub struct DefEntry {
    pub params: Vec<(String, IRType)>,
    pub body: IRExpr,
}

/// Definition environment built from `IRProgram.functions`.
#[derive(Debug)]
pub struct DefEnv {
    defs: HashMap<String, DefEntry>,
}

impl DefEnv {
    /// Build a definition environment from all functions in the IR program.
    pub fn from_ir(program: &IRProgram) -> Self {
        let mut defs = HashMap::new();
        for f in &program.functions {
            let (params, body) = uncurry(&f.body);
            defs.insert(f.name.clone(), DefEntry { params, body });
        }
        Self { defs }
    }

    /// Look up a definition by name.
    pub fn get(&self, name: &str) -> Option<&DefEntry> {
        self.defs.get(name)
    }

    /// Try to expand a `Var` reference. Returns `Some(body)` for nullary defs (props).
    pub fn expand_var(&self, name: &str) -> Option<IRExpr> {
        let entry = self.defs.get(name)?;
        if entry.params.is_empty() {
            Some(entry.body.clone())
        } else {
            None // parameterized def — needs App to supply args
        }
    }

    /// Try to expand an `App` chain. Decomposes the chain, looks up the def,
    /// and performs beta-reduction if arity matches.
    pub fn expand_app(&self, expr: &IRExpr) -> Option<IRExpr> {
        let (name, args) = decompose_app_chain(expr)?;
        let entry = self.defs.get(&name)?;
        if entry.params.len() != args.len() {
            return None; // arity mismatch — not a full application
        }
        Some(substitute_all(&entry.body, &entry.params, &args))
    }
}

/// Peel off `Lam` wrappers to extract parameter list and innermost body.
///
/// `Lam(x, T, Lam(y, U, body))` → `[(x, T), (y, U)]`, `body`
fn uncurry(expr: &IRExpr) -> (Vec<(String, IRType)>, IRExpr) {
    let mut params = Vec::new();
    let mut current = expr;
    while let IRExpr::Lam {
        param,
        param_type,
        body,
    } = current
    {
        params.push((param.clone(), param_type.clone()));
        current = body;
    }
    (params, current.clone())
}

/// Decompose a curried `App` chain into the function name and argument list.
///
/// `App(App(Var("p"), a1), a2)` → `Some(("p", [a1, a2]))`
fn decompose_app_chain(expr: &IRExpr) -> Option<(String, Vec<IRExpr>)> {
    let mut args = Vec::new();
    let mut current = expr;
    while let IRExpr::App { func, arg, .. } = current {
        args.push(arg.as_ref().clone());
        current = func.as_ref();
    }
    args.reverse();
    if let IRExpr::Var { name, .. } = current {
        if args.is_empty() {
            return None; // bare Var, not an App chain
        }
        Some((name.clone(), args))
    } else {
        None // head is not a Var
    }
}

/// Beta-reduce: substitute all parameters with arguments in body.
fn substitute_all(body: &IRExpr, params: &[(String, IRType)], args: &[IRExpr]) -> IRExpr {
    let mut result = body.clone();
    for (i, (param_name, _)) in params.iter().enumerate() {
        result = substitute_var(result, param_name, &args[i]);
    }
    result
}

/// Generate a fresh variable name that won't collide with existing names.
fn fresh_name(base: &str) -> String {
    let n = FRESH_COUNTER.fetch_add(1, Ordering::Relaxed);
    format!("{base}${n}")
}

/// Collect free variables in an expression (names not bound by any enclosing binder).
fn free_vars(expr: &IRExpr) -> HashSet<String> {
    let mut fv = HashSet::new();
    free_vars_inner(expr, &mut HashSet::new(), &mut fv);
    fv
}

fn free_vars_inner(expr: &IRExpr, bound: &mut HashSet<String>, fv: &mut HashSet<String>) {
    match expr {
        IRExpr::Var { name, .. } => {
            if !bound.contains(name) {
                fv.insert(name.clone());
            }
        }
        IRExpr::Lit { .. } | IRExpr::Ctor { .. } | IRExpr::Sorry | IRExpr::Todo => {}
        IRExpr::Field { expr, .. } => free_vars_inner(expr, bound, fv),
        IRExpr::BinOp { left, right, .. } => {
            free_vars_inner(left, bound, fv);
            free_vars_inner(right, bound, fv);
        }
        IRExpr::UnOp { operand, .. } => free_vars_inner(operand, bound, fv),
        IRExpr::App { func, arg, .. } => {
            free_vars_inner(func, bound, fv);
            free_vars_inner(arg, bound, fv);
        }
        IRExpr::Lam { param, body, .. } => {
            let was_new = bound.insert(param.clone());
            free_vars_inner(body, bound, fv);
            if was_new {
                bound.remove(param);
            }
        }
        IRExpr::Let { bindings, body } => {
            let mut added = Vec::new();
            for b in bindings {
                free_vars_inner(&b.expr, bound, fv);
                if bound.insert(b.name.clone()) {
                    added.push(b.name.clone());
                }
            }
            free_vars_inner(body, bound, fv);
            for name in added {
                bound.remove(&name);
            }
        }
        IRExpr::Forall { var, body, .. } | IRExpr::Exists { var, body, .. } => {
            let was_new = bound.insert(var.clone());
            free_vars_inner(body, bound, fv);
            if was_new {
                bound.remove(var);
            }
        }
        IRExpr::Always { body } | IRExpr::Eventually { body } | IRExpr::Prime { expr: body } => {
            free_vars_inner(body, bound, fv);
        }
        IRExpr::Match { scrutinee, arms } => {
            free_vars_inner(scrutinee, bound, fv);
            for arm in arms {
                let mut arm_bound = bound.clone();
                collect_pattern_vars(&arm.pattern, &mut arm_bound);
                if let Some(g) = &arm.guard {
                    free_vars_inner(g, &mut arm_bound, fv);
                }
                free_vars_inner(&arm.body, &mut arm_bound, fv);
            }
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            free_vars_inner(map, bound, fv);
            free_vars_inner(key, bound, fv);
            free_vars_inner(value, bound, fv);
        }
        IRExpr::Index { map, key, .. } => {
            free_vars_inner(map, bound, fv);
            free_vars_inner(key, bound, fv);
        }
        IRExpr::SetComp {
            var,
            filter,
            projection,
            ..
        } => {
            let was_new = bound.insert(var.clone());
            free_vars_inner(filter, bound, fv);
            if let Some(p) = projection {
                free_vars_inner(p, bound, fv);
            }
            if was_new {
                bound.remove(var);
            }
        }
        IRExpr::SetLit { elements, .. } | IRExpr::SeqLit { elements, .. } => {
            for e in elements {
                free_vars_inner(e, bound, fv);
            }
        }
        IRExpr::MapLit { entries, .. } => {
            for (k, v) in entries {
                free_vars_inner(k, bound, fv);
                free_vars_inner(v, bound, fv);
            }
        }
    }
}

/// Capture-avoiding substitution: replace all free occurrences of `Var(var_name)`
/// with `replacement` in `expr`. Alpha-renames binders when replacement contains
/// free variables that would be captured.
fn substitute_var(expr: IRExpr, var_name: &str, replacement: &IRExpr) -> IRExpr {
    // Cache free vars of replacement — needed for capture checks at binders.
    let repl_fv = free_vars(replacement);
    substitute_var_inner(expr, var_name, replacement, &repl_fv)
}

#[allow(clippy::too_many_lines)]
fn substitute_var_inner(
    expr: IRExpr,
    var_name: &str,
    replacement: &IRExpr,
    repl_fv: &HashSet<String>,
) -> IRExpr {
    match expr {
        IRExpr::Var { ref name, .. } if name == var_name => replacement.clone(),
        IRExpr::Var { .. }
        | IRExpr::Lit { .. }
        | IRExpr::Ctor { .. }
        | IRExpr::Sorry
        | IRExpr::Todo => expr,
        IRExpr::Field {
            expr: inner,
            field,
            ty,
        } => IRExpr::Field {
            expr: Box::new(substitute_var_inner(*inner, var_name, replacement, repl_fv)),
            field,
            ty,
        },
        IRExpr::BinOp {
            op,
            left,
            right,
            ty,
        } => IRExpr::BinOp {
            op,
            left: Box::new(substitute_var_inner(*left, var_name, replacement, repl_fv)),
            right: Box::new(substitute_var_inner(*right, var_name, replacement, repl_fv)),
            ty,
        },
        IRExpr::UnOp { op, operand, ty } => IRExpr::UnOp {
            op,
            operand: Box::new(substitute_var_inner(
                *operand,
                var_name,
                replacement,
                repl_fv,
            )),
            ty,
        },
        IRExpr::App { func, arg, ty } => IRExpr::App {
            func: Box::new(substitute_var_inner(*func, var_name, replacement, repl_fv)),
            arg: Box::new(substitute_var_inner(*arg, var_name, replacement, repl_fv)),
            ty,
        },
        IRExpr::Lam {
            param,
            param_type,
            body,
        } => {
            if param == var_name {
                // Shadowed — don't substitute into body
                IRExpr::Lam {
                    param,
                    param_type,
                    body,
                }
            } else if repl_fv.contains(&param) {
                // Capture risk: binder name appears free in replacement.
                // Alpha-rename: Lam(x, body) → Lam(x', body[x := Var(x')])
                let fresh = fresh_name(&param);
                let fresh_var = IRExpr::Var {
                    name: fresh.clone(),
                    ty: param_type.clone(),
                };
                let renamed_body =
                    substitute_var_inner(*body, &param, &fresh_var, &free_vars(&fresh_var));
                IRExpr::Lam {
                    param: fresh,
                    param_type,
                    body: Box::new(substitute_var_inner(
                        renamed_body,
                        var_name,
                        replacement,
                        repl_fv,
                    )),
                }
            } else {
                IRExpr::Lam {
                    param,
                    param_type,
                    body: Box::new(substitute_var_inner(*body, var_name, replacement, repl_fv)),
                }
            }
        }
        IRExpr::Let { bindings, body } => {
            let mut shadowed = false;
            let mut needs_rename = false;
            // Check if any binding name appears free in replacement
            for b in &bindings {
                if b.name == var_name {
                    break; // will shadow before we need to worry about capture
                }
                if repl_fv.contains(&b.name) {
                    needs_rename = true;
                    break;
                }
            }
            if needs_rename {
                // Alpha-rename conflicting let bindings
                let mut renamed_bindings = Vec::new();
                let mut renames: Vec<(String, String)> = Vec::new();
                let mut current_body = *body;

                for b in bindings {
                    let new_name = if repl_fv.contains(&b.name) && b.name != var_name {
                        let fresh = fresh_name(&b.name);
                        renames.push((b.name.clone(), fresh.clone()));
                        fresh
                    } else {
                        b.name.clone()
                    };

                    let mut new_expr = b.expr;
                    // Apply prior renames to this binding's expr
                    for (old, new) in &renames {
                        if old != &b.name {
                            let fresh_var = IRExpr::Var {
                                name: new.clone(),
                                ty: b.ty.clone(),
                            };
                            new_expr = substitute_var_inner(
                                new_expr,
                                old,
                                &fresh_var,
                                &free_vars(&fresh_var),
                            );
                        }
                    }

                    if !shadowed {
                        new_expr = substitute_var_inner(new_expr, var_name, replacement, repl_fv);
                    }
                    if b.name == var_name {
                        shadowed = true;
                    }

                    renamed_bindings.push(crate::ir::types::LetBinding {
                        name: new_name,
                        ty: b.ty,
                        expr: new_expr,
                    });
                }

                // Apply renames to body
                for (old, new) in &renames {
                    let fresh_var = IRExpr::Var {
                        name: new.clone(),
                        ty: IRType::Int, // type doesn't matter for name substitution
                    };
                    current_body =
                        substitute_var_inner(current_body, old, &fresh_var, &free_vars(&fresh_var));
                }
                if !shadowed {
                    current_body =
                        substitute_var_inner(current_body, var_name, replacement, repl_fv);
                }

                IRExpr::Let {
                    bindings: renamed_bindings,
                    body: Box::new(current_body),
                }
            } else {
                let new_bindings = bindings
                    .into_iter()
                    .map(|b| {
                        let new_expr = if shadowed {
                            b.expr
                        } else {
                            substitute_var_inner(b.expr, var_name, replacement, repl_fv)
                        };
                        if b.name == var_name {
                            shadowed = true;
                        }
                        crate::ir::types::LetBinding {
                            name: b.name,
                            ty: b.ty,
                            expr: new_expr,
                        }
                    })
                    .collect();
                IRExpr::Let {
                    bindings: new_bindings,
                    body: if shadowed {
                        body
                    } else {
                        Box::new(substitute_var_inner(*body, var_name, replacement, repl_fv))
                    },
                }
            }
        }
        IRExpr::Forall { var, domain, body } => {
            subst_quantifier(var, domain, body, var_name, replacement, repl_fv, true)
        }
        IRExpr::Exists { var, domain, body } => {
            subst_quantifier(var, domain, body, var_name, replacement, repl_fv, false)
        }
        IRExpr::Always { body } => IRExpr::Always {
            body: Box::new(substitute_var_inner(*body, var_name, replacement, repl_fv)),
        },
        IRExpr::Eventually { body } => IRExpr::Eventually {
            body: Box::new(substitute_var_inner(*body, var_name, replacement, repl_fv)),
        },
        IRExpr::Prime { expr } => IRExpr::Prime {
            expr: Box::new(substitute_var_inner(*expr, var_name, replacement, repl_fv)),
        },
        IRExpr::Match { scrutinee, arms } => {
            let new_scrutinee = substitute_var_inner(*scrutinee, var_name, replacement, repl_fv);
            let new_arms = arms
                .into_iter()
                .map(|a| {
                    let mut pat_vars = HashSet::new();
                    collect_ir_pattern_vars(&a.pattern, &mut pat_vars);
                    if pat_vars.contains(var_name) {
                        // Shadowed by pattern — don't substitute in guard/body
                        a
                    } else {
                        // Check for capture: pattern vars that collide with replacement free vars
                        let captures: Vec<String> = pat_vars
                            .iter()
                            .filter(|v| repl_fv.contains(v.as_str()))
                            .cloned()
                            .collect();
                        if captures.is_empty() {
                            // No capture risk — substitute directly
                            crate::ir::types::IRMatchArm {
                                pattern: a.pattern,
                                guard: a.guard.map(|g| {
                                    substitute_var_inner(g, var_name, replacement, repl_fv)
                                }),
                                body: substitute_var_inner(a.body, var_name, replacement, repl_fv),
                            }
                        } else {
                            // Alpha-rename capturing pattern vars in pattern + guard + body
                            let mut pattern = a.pattern;
                            let mut guard = a.guard;
                            let mut body = a.body;
                            for old_name in &captures {
                                let fresh = fresh_name(old_name);
                                pattern = rename_in_pattern(pattern, old_name, &fresh);
                                // Recover the type from the first occurrence in body/guard,
                                // falling back to Bool (pattern vars are typically entity/enum typed
                                // but the type is only carried structurally — not consumed by subst).
                                let ty = find_var_type(&body, old_name)
                                    .or_else(|| {
                                        guard.as_ref().and_then(|g| find_var_type(g, old_name))
                                    })
                                    .unwrap_or(IRType::Bool);
                                let fresh_var = IRExpr::Var {
                                    name: fresh.clone(),
                                    ty,
                                };
                                let fv_fresh = free_vars(&fresh_var);
                                if let Some(g) = guard {
                                    guard = Some(substitute_var_inner(
                                        g, old_name, &fresh_var, &fv_fresh,
                                    ));
                                }
                                body = substitute_var_inner(body, old_name, &fresh_var, &fv_fresh);
                            }
                            crate::ir::types::IRMatchArm {
                                pattern,
                                guard: guard.map(|g| {
                                    substitute_var_inner(g, var_name, replacement, repl_fv)
                                }),
                                body: substitute_var_inner(body, var_name, replacement, repl_fv),
                            }
                        }
                    }
                })
                .collect();
            IRExpr::Match {
                scrutinee: Box::new(new_scrutinee),
                arms: new_arms,
            }
        }
        IRExpr::MapUpdate {
            map,
            key,
            value,
            ty,
        } => IRExpr::MapUpdate {
            map: Box::new(substitute_var_inner(*map, var_name, replacement, repl_fv)),
            key: Box::new(substitute_var_inner(*key, var_name, replacement, repl_fv)),
            value: Box::new(substitute_var_inner(*value, var_name, replacement, repl_fv)),
            ty,
        },
        IRExpr::Index { map, key, ty } => IRExpr::Index {
            map: Box::new(substitute_var_inner(*map, var_name, replacement, repl_fv)),
            key: Box::new(substitute_var_inner(*key, var_name, replacement, repl_fv)),
            ty,
        },
        IRExpr::SetComp {
            var,
            domain,
            filter,
            projection,
            ty,
        } => {
            if var == var_name {
                IRExpr::SetComp {
                    var,
                    domain,
                    filter,
                    projection,
                    ty,
                }
            } else if repl_fv.contains(&var) {
                let fresh = fresh_name(&var);
                let fresh_var = IRExpr::Var {
                    name: fresh.clone(),
                    ty: domain.clone(),
                };
                let fv_fresh = free_vars(&fresh_var);
                let renamed_filter = substitute_var_inner(*filter, &var, &fresh_var, &fv_fresh);
                let renamed_proj = projection
                    .map(|p| Box::new(substitute_var_inner(*p, &var, &fresh_var, &fv_fresh)));
                IRExpr::SetComp {
                    var: fresh,
                    domain,
                    filter: Box::new(substitute_var_inner(
                        renamed_filter,
                        var_name,
                        replacement,
                        repl_fv,
                    )),
                    projection: renamed_proj.map(|p| {
                        Box::new(substitute_var_inner(*p, var_name, replacement, repl_fv))
                    }),
                    ty,
                }
            } else {
                IRExpr::SetComp {
                    var,
                    domain,
                    filter: Box::new(substitute_var_inner(
                        *filter,
                        var_name,
                        replacement,
                        repl_fv,
                    )),
                    projection: projection.map(|p| {
                        Box::new(substitute_var_inner(*p, var_name, replacement, repl_fv))
                    }),
                    ty,
                }
            }
        }
        IRExpr::SetLit { elements, ty } => IRExpr::SetLit {
            elements: elements
                .into_iter()
                .map(|e| substitute_var_inner(e, var_name, replacement, repl_fv))
                .collect(),
            ty,
        },
        IRExpr::SeqLit { elements, ty } => IRExpr::SeqLit {
            elements: elements
                .into_iter()
                .map(|e| substitute_var_inner(e, var_name, replacement, repl_fv))
                .collect(),
            ty,
        },
        IRExpr::MapLit { entries, ty } => IRExpr::MapLit {
            entries: entries
                .into_iter()
                .map(|(k, v)| {
                    (
                        substitute_var_inner(k, var_name, replacement, repl_fv),
                        substitute_var_inner(v, var_name, replacement, repl_fv),
                    )
                })
                .collect(),
            ty,
        },
    }
}

/// Find the type annotation of the first `Var` with the given name in an expression.
/// Used to recover types for alpha-renamed pattern variables.
fn find_var_type(expr: &IRExpr, name: &str) -> Option<IRType> {
    match expr {
        IRExpr::Var { name: n, ty, .. } if n == name => Some(ty.clone()),
        IRExpr::Field { expr, .. } | IRExpr::Prime { expr } => find_var_type(expr, name),
        IRExpr::BinOp { left, right, .. } => {
            find_var_type(left, name).or_else(|| find_var_type(right, name))
        }
        IRExpr::UnOp { operand, .. } => find_var_type(operand, name),
        IRExpr::App { func, arg, .. } => {
            find_var_type(func, name).or_else(|| find_var_type(arg, name))
        }
        IRExpr::Lam { body, .. }
        | IRExpr::Forall { body, .. }
        | IRExpr::Exists { body, .. }
        | IRExpr::Always { body }
        | IRExpr::Eventually { body } => find_var_type(body, name),
        IRExpr::Let { bindings, body } => bindings
            .iter()
            .find_map(|b| find_var_type(&b.expr, name))
            .or_else(|| find_var_type(body, name)),
        IRExpr::Match { scrutinee, arms } => find_var_type(scrutinee, name).or_else(|| {
            arms.iter().find_map(|a| {
                a.guard
                    .as_ref()
                    .and_then(|g| find_var_type(g, name))
                    .or_else(|| find_var_type(&a.body, name))
            })
        }),
        _ => None,
    }
}

/// Collect variable names bound by an IR pattern.
fn collect_ir_pattern_vars(pat: &crate::ir::types::IRPattern, vars: &mut HashSet<String>) {
    match pat {
        crate::ir::types::IRPattern::PVar { name } => {
            vars.insert(name.clone());
        }
        crate::ir::types::IRPattern::PCtor { fields, .. } => {
            for f in fields {
                collect_ir_pattern_vars(&f.pattern, vars);
            }
        }
        crate::ir::types::IRPattern::PWild => {}
        crate::ir::types::IRPattern::POr { left, right } => {
            collect_ir_pattern_vars(left, vars);
            collect_ir_pattern_vars(right, vars);
        }
    }
}

/// Collect variable names bound by an IR pattern (for `free_vars` analysis).
fn collect_pattern_vars(pat: &crate::ir::types::IRPattern, bound: &mut HashSet<String>) {
    collect_ir_pattern_vars(pat, bound);
}

/// Rename a variable binding inside an IR pattern.
/// `PVar { name: old }` → `PVar { name: new }`, recurse into `PCtor` fields and `POr`.
fn rename_in_pattern(
    pat: crate::ir::types::IRPattern,
    old_name: &str,
    new_name: &str,
) -> crate::ir::types::IRPattern {
    use crate::ir::types::IRPattern;
    match pat {
        IRPattern::PVar { name } if name == old_name => IRPattern::PVar {
            name: new_name.to_owned(),
        },
        IRPattern::PVar { .. } | IRPattern::PWild => pat,
        IRPattern::PCtor { name, fields } => IRPattern::PCtor {
            name,
            fields: fields
                .into_iter()
                .map(|f| crate::ir::types::IRFieldPat {
                    name: f.name,
                    pattern: rename_in_pattern(f.pattern, old_name, new_name),
                })
                .collect(),
        },
        IRPattern::POr { left, right } => IRPattern::POr {
            left: Box::new(rename_in_pattern(*left, old_name, new_name)),
            right: Box::new(rename_in_pattern(*right, old_name, new_name)),
        },
    }
}

/// Shared logic for Forall/Exists with capture-avoiding substitution.
fn subst_quantifier(
    var: String,
    domain: IRType,
    body: Box<IRExpr>,
    var_name: &str,
    replacement: &IRExpr,
    repl_fv: &HashSet<String>,
    is_forall: bool,
) -> IRExpr {
    let make = |v: String, d: IRType, b: Box<IRExpr>| {
        if is_forall {
            IRExpr::Forall {
                var: v,
                domain: d,
                body: b,
            }
        } else {
            IRExpr::Exists {
                var: v,
                domain: d,
                body: b,
            }
        }
    };

    if var == var_name {
        // Shadowed — don't substitute into body
        make(var, domain, body)
    } else if repl_fv.contains(&var) {
        // Capture risk: alpha-rename the quantifier variable
        let fresh = fresh_name(&var);
        let fresh_var = IRExpr::Var {
            name: fresh.clone(),
            ty: domain.clone(),
        };
        let fv_fresh = free_vars(&fresh_var);
        let renamed_body = substitute_var_inner(*body, &var, &fresh_var, &fv_fresh);
        make(
            fresh,
            domain,
            Box::new(substitute_var_inner(
                renamed_body,
                var_name,
                replacement,
                repl_fv,
            )),
        )
    } else {
        make(
            var,
            domain,
            Box::new(substitute_var_inner(*body, var_name, replacement, repl_fv)),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::types::*;

    #[test]
    fn uncurry_nullary() {
        let body = IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
        };
        let (params, result) = uncurry(&body);
        assert!(params.is_empty());
        assert_eq!(result, body);
    }

    #[test]
    fn uncurry_two_params() {
        let body = IRExpr::Lam {
            param: "x".to_owned(),
            param_type: IRType::Int,
            body: Box::new(IRExpr::Lam {
                param: "y".to_owned(),
                param_type: IRType::Bool,
                body: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
                    ty: IRType::Int,
                }),
            }),
        };
        let (params, result) = uncurry(&body);
        assert_eq!(params.len(), 2);
        assert_eq!(params[0].0, "x");
        assert_eq!(params[1].0, "y");
        assert!(matches!(result, IRExpr::Var { ref name, .. } if name == "x"));
    }

    #[test]
    fn decompose_app_chain_single_arg() {
        let expr = IRExpr::App {
            func: Box::new(IRExpr::Var {
                name: "p".to_owned(),
                ty: IRType::Bool,
            }),
            arg: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 42 },
            }),
            ty: IRType::Bool,
        };
        let (name, args) = decompose_app_chain(&expr).unwrap();
        assert_eq!(name, "p");
        assert_eq!(args.len(), 1);
    }

    #[test]
    fn decompose_app_chain_two_args() {
        let expr = IRExpr::App {
            func: Box::new(IRExpr::App {
                func: Box::new(IRExpr::Var {
                    name: "p".to_owned(),
                    ty: IRType::Bool,
                }),
                arg: Box::new(IRExpr::Var {
                    name: "a".to_owned(),
                    ty: IRType::Int,
                }),
                ty: IRType::Bool,
            }),
            arg: Box::new(IRExpr::Var {
                name: "b".to_owned(),
                ty: IRType::Int,
            }),
            ty: IRType::Bool,
        };
        let (name, args) = decompose_app_chain(&expr).unwrap();
        assert_eq!(name, "p");
        assert_eq!(args.len(), 2);
    }

    #[test]
    fn expand_nullary_prop() {
        let program = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![IRFunction {
                name: "safe".to_owned(),
                ty: IRType::Bool,
                body: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                },
            }],
            entities: vec![],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        };
        let env = DefEnv::from_ir(&program);
        let expanded = env.expand_var("safe").unwrap();
        assert!(matches!(
            expanded,
            IRExpr::Lit {
                value: LitVal::Bool { value: true },
                ..
            }
        ));
    }

    #[test]
    fn expand_pred_app() {
        // pred positive(x: Int) = x > 0
        let program = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![IRFunction {
                name: "positive".to_owned(),
                ty: IRType::Fn {
                    param: Box::new(IRType::Int),
                    result: Box::new(IRType::Bool),
                },
                body: IRExpr::Lam {
                    param: "x".to_owned(),
                    param_type: IRType::Int,
                    body: Box::new(IRExpr::BinOp {
                        op: "OpGt".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "x".to_owned(),
                            ty: IRType::Int,
                        }),
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 0 },
                        }),
                        ty: IRType::Bool,
                    }),
                },
            }],
            entities: vec![],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        };
        let env = DefEnv::from_ir(&program);

        // App(Var("positive"), Lit(5))
        let call = IRExpr::App {
            func: Box::new(IRExpr::Var {
                name: "positive".to_owned(),
                ty: IRType::Bool,
            }),
            arg: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 5 },
            }),
            ty: IRType::Bool,
        };

        let expanded = env.expand_app(&call).unwrap();
        // Should be: 5 > 0
        assert!(matches!(expanded, IRExpr::BinOp { ref op, .. } if op == "OpGt"));
    }

    #[test]
    fn expand_var_returns_none_for_parameterized() {
        let program = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![IRFunction {
                name: "positive".to_owned(),
                ty: IRType::Fn {
                    param: Box::new(IRType::Int),
                    result: Box::new(IRType::Bool),
                },
                body: IRExpr::Lam {
                    param: "x".to_owned(),
                    param_type: IRType::Int,
                    body: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                    }),
                },
            }],
            entities: vec![],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            scenes: vec![],
        };
        let env = DefEnv::from_ir(&program);
        // Should return None — parameterized def needs App to supply args
        assert!(env.expand_var("positive").is_none());
    }

    #[test]
    fn substitute_respects_shadowing() {
        // Lam(x, _, x + y) with y := 10 → Lam(x, _, x + 10)
        let expr = IRExpr::Lam {
            param: "x".to_owned(),
            param_type: IRType::Int,
            body: Box::new(IRExpr::BinOp {
                op: "OpAdd".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
                    ty: IRType::Int,
                }),
                right: Box::new(IRExpr::Var {
                    name: "y".to_owned(),
                    ty: IRType::Int,
                }),
                ty: IRType::Int,
            }),
        };
        let replacement = IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value: 10 },
        };
        let result = substitute_var(expr, "y", &replacement);
        // x should NOT be replaced, y SHOULD be replaced
        if let IRExpr::Lam { body, .. } = result {
            if let IRExpr::BinOp { left, right, .. } = *body {
                assert!(matches!(*left, IRExpr::Var { ref name, .. } if name == "x"));
                assert!(matches!(
                    *right,
                    IRExpr::Lit {
                        value: LitVal::Int { value: 10 },
                        ..
                    }
                ));
                return;
            }
        }
        panic!("unexpected structure");
    }

    #[test]
    fn match_pattern_shadows_substitution() {
        // match scrut { x => x + y }
        // Substituting y := 42 should replace y but NOT x (pattern-bound).
        let expr = IRExpr::Match {
            scrutinee: Box::new(IRExpr::Var {
                name: "scrut".to_owned(),
                ty: IRType::Int,
            }),
            arms: vec![IRMatchArm {
                pattern: IRPattern::PVar {
                    name: "x".to_owned(),
                },
                guard: None,
                body: IRExpr::BinOp {
                    op: "OpAdd".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "y".to_owned(),
                        ty: IRType::Int,
                    }),
                    ty: IRType::Int,
                },
            }],
        };
        let replacement = IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value: 42 },
        };
        let result = substitute_var(expr, "y", &replacement);
        if let IRExpr::Match { arms, .. } = result {
            if let IRExpr::BinOp { left, right, .. } = &arms[0].body {
                // x should still be x (pattern-bound)
                assert!(matches!(left.as_ref(), IRExpr::Var { name, .. } if name == "x"));
                // y should be replaced with 42
                assert!(matches!(
                    right.as_ref(),
                    IRExpr::Lit {
                        value: LitVal::Int { value: 42 },
                        ..
                    }
                ));
                return;
            }
        }
        panic!("unexpected structure");
    }

    #[test]
    fn match_pattern_var_shadowed_stops_subst() {
        // match scrut { x => x + 1 }
        // Substituting x := 99 should NOT replace x in body (shadowed by pattern).
        let expr = IRExpr::Match {
            scrutinee: Box::new(IRExpr::Var {
                name: "scrut".to_owned(),
                ty: IRType::Int,
            }),
            arms: vec![IRMatchArm {
                pattern: IRPattern::PVar {
                    name: "x".to_owned(),
                },
                guard: None,
                body: IRExpr::BinOp {
                    op: "OpAdd".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },
                    }),
                    ty: IRType::Int,
                },
            }],
        };
        let replacement = IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value: 99 },
        };
        let result = substitute_var(expr, "x", &replacement);
        if let IRExpr::Match { arms, .. } = result {
            if let IRExpr::BinOp { left, .. } = &arms[0].body {
                // x should still be x — shadowed by pattern
                assert!(
                    matches!(left.as_ref(), IRExpr::Var { name, .. } if name == "x"),
                    "expected x to remain (shadowed), got: {left:?}"
                );
                return;
            }
        }
        panic!("unexpected structure");
    }

    #[test]
    fn match_pattern_capture_avoidance() {
        // match scrut { x => x + y }
        // Substituting y := (x + 1) — replacement has free var "x" that collides
        // with pattern var "x". Without alpha-rename, body would become (x + (x + 1))
        // where the first x is the pattern-bound one and the second x is the free one
        // from replacement — a capture bug.
        // With alpha-rename, pattern x should be renamed to x$N, so body becomes
        // (x$N + (x + 1)) — correct.
        let expr = IRExpr::Match {
            scrutinee: Box::new(IRExpr::Var {
                name: "scrut".to_owned(),
                ty: IRType::Int,
            }),
            arms: vec![IRMatchArm {
                pattern: IRPattern::PVar {
                    name: "x".to_owned(),
                },
                guard: None,
                body: IRExpr::BinOp {
                    op: "OpAdd".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "y".to_owned(),
                        ty: IRType::Int,
                    }),
                    ty: IRType::Int,
                },
            }],
        };
        // replacement: x + 1 (free var "x")
        let replacement = IRExpr::BinOp {
            op: "OpAdd".to_owned(),
            left: Box::new(IRExpr::Var {
                name: "x".to_owned(),
                ty: IRType::Int,
            }),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 1 },
            }),
            ty: IRType::Int,
        };
        let result = substitute_var(expr, "y", &replacement);
        if let IRExpr::Match { arms, .. } = result {
            // Pattern should be renamed from "x" to something fresh
            let IRPattern::PVar { name: pat_name } = &arms[0].pattern else {
                panic!("expected PVar pattern");
            };
            assert_ne!(pat_name, "x", "pattern var should be alpha-renamed");
            assert!(
                pat_name.starts_with("x$"),
                "expected fresh name like x$N, got: {pat_name}"
            );

            // Body left should reference the fresh name (was pattern-bound x)
            if let IRExpr::BinOp { left, right, .. } = &arms[0].body {
                assert!(
                    matches!(left.as_ref(), IRExpr::Var { name, .. } if name == pat_name),
                    "left should reference renamed pattern var {pat_name}, got: {left:?}"
                );
                // Right should be the replacement (x + 1) with the ORIGINAL "x"
                assert!(
                    matches!(right.as_ref(), IRExpr::BinOp { .. }),
                    "right should be the replacement BinOp, got: {right:?}"
                );
                return;
            }
        }
        panic!("unexpected structure");
    }

    #[test]
    fn free_vars_respects_match_pattern_binding() {
        // match scrut { x => x + y }
        // free vars should be {scrut, y} but NOT x (bound by pattern)
        let expr = IRExpr::Match {
            scrutinee: Box::new(IRExpr::Var {
                name: "scrut".to_owned(),
                ty: IRType::Int,
            }),
            arms: vec![IRMatchArm {
                pattern: IRPattern::PVar {
                    name: "x".to_owned(),
                },
                guard: None,
                body: IRExpr::BinOp {
                    op: "OpAdd".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "y".to_owned(),
                        ty: IRType::Int,
                    }),
                    ty: IRType::Int,
                },
            }],
        };
        let fv = free_vars(&expr);
        assert!(fv.contains("scrut"), "scrut should be free");
        assert!(fv.contains("y"), "y should be free");
        assert!(!fv.contains("x"), "x should NOT be free (pattern-bound)");
    }
}
