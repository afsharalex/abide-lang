use std::collections::HashSet;

use super::*;

struct PooledSyGuSCtx<'a> {
    slots_per_entity: &'a HashMap<String, usize>,
    active_vars: &'a HashMap<String, HashMap<usize, Cvc5Term>>,
    slot_fields: &'a HashMap<String, Cvc5Term>,
    store_param_types: &'a HashMap<String, String>,
}

#[derive(Clone, Copy)]
struct PooledFrameVars<'a> {
    active_curr: &'a HashMap<String, HashMap<usize, Cvc5Term>>,
    active_next: &'a HashMap<String, HashMap<usize, Cvc5Term>>,
    slot_curr: &'a HashMap<String, Cvc5Term>,
    slot_next: &'a HashMap<String, Cvc5Term>,
}

#[derive(Clone, Copy)]
struct PooledExprEnv<'a> {
    vars: &'a HashMap<String, Cvc5Term>,
    entity_bindings: &'a PooledEntityBindings,
    pool_ctx: &'a PooledSyGuSCtx<'a>,
    enum_catalog: &'a EnumCatalog,
}

#[derive(Clone, Copy)]
struct PooledSlotTransitionCtx<'a> {
    vars: &'a HashMap<String, Cvc5Term>,
    entity_bindings: &'a PooledEntityBindings,
    frames: PooledFrameVars<'a>,
    enum_catalog: &'a EnumCatalog,
    pool_ctx: &'a PooledSyGuSCtx<'a>,
}

#[derive(Clone, Copy)]
struct PooledTargetSlot<'a> {
    var: &'a str,
    entity: &'a IREntity,
    slot: usize,
}

#[derive(Clone, Copy)]
struct PooledNestedOpsCtx<'a> {
    systems_by_name: &'a HashMap<String, &'a IRSystem>,
    entities_by_name: &'a HashMap<String, &'a IREntity>,
    slots_per_entity: &'a HashMap<String, usize>,
    vars: &'a HashMap<String, Cvc5Term>,
    next_vars: &'a HashMap<String, Cvc5Term>,
    entity_bindings: &'a PooledEntityBindings,
    frames: PooledFrameVars<'a>,
    enum_catalog: &'a EnumCatalog,
    pool_ctx: &'a PooledSyGuSCtx<'a>,
    call_stack: &'a [String],
}

#[derive(Clone, Copy)]
struct PooledEntityPoolTarget<'a> {
    entity: &'a IREntity,
    n_slots: usize,
}

#[derive(Clone, Copy)]
struct PooledActionCtx<'a> {
    system: &'a IRSystem,
    systems_by_name: &'a HashMap<String, &'a IRSystem>,
    entities_by_name: &'a HashMap<String, &'a IREntity>,
    slots_per_entity: &'a HashMap<String, usize>,
    vars: &'a HashMap<String, Cvc5Term>,
    next_vars: &'a HashMap<String, Cvc5Term>,
    entity_bindings: &'a PooledEntityBindings,
    frames: PooledFrameVars<'a>,
    enum_catalog: &'a EnumCatalog,
    call_stack: &'a [String],
}

#[derive(Clone, Copy)]
struct PooledStepCtx<'a> {
    system: &'a IRSystem,
    systems_by_name: &'a HashMap<String, &'a IRSystem>,
    entities_by_name: &'a HashMap<String, &'a IREntity>,
    slots_per_entity: &'a HashMap<String, usize>,
    curr_vars: &'a HashMap<String, Cvc5Term>,
    next_vars: &'a HashMap<String, Cvc5Term>,
    frames: PooledFrameVars<'a>,
    enum_catalog: &'a EnumCatalog,
    call_stack: &'a [String],
}

#[derive(Clone, Copy)]
struct PooledCrossCallCtx<'a> {
    systems_by_name: &'a HashMap<String, &'a IRSystem>,
    entities_by_name: &'a HashMap<String, &'a IREntity>,
    slots_per_entity: &'a HashMap<String, usize>,
    curr_vars: &'a HashMap<String, Cvc5Term>,
    next_vars: &'a HashMap<String, Cvc5Term>,
    entity_bindings: &'a PooledEntityBindings,
    frames: PooledFrameVars<'a>,
    enum_catalog: &'a EnumCatalog,
    call_stack: &'a [String],
}

type PooledEntityBindings = HashMap<String, (String, usize)>;

#[derive(Clone, Default)]
struct PooledParamEnv {
    terms: HashMap<String, Cvc5Term>,
    entity_bindings: PooledEntityBindings,
}

struct PooledCrossCallCapture {
    formula: Cvc5Term,
    return_value: Option<Cvc5Term>,
    return_type: Option<IRType>,
}

#[derive(Clone)]
struct PooledLocalBinding {
    term: Cvc5Term,
    ty: Option<IRType>,
}

type PooledLocalBindings = HashMap<String, PooledLocalBinding>;

struct PooledActionResult {
    formula: Cvc5Term,
    locals: PooledLocalBindings,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct PooledSyGuSUnsupportedExpr {
    pub backend: &'static str,
    pub feature: &'static str,
    pub reason: String,
    pub span: Option<crate::span::Span>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum PooledSyGuSExprSupport {
    Supported,
    Unsupported(PooledSyGuSUnsupportedExpr),
}

impl PooledSyGuSExprSupport {
    pub(super) fn is_supported(&self) -> bool {
        matches!(self, Self::Supported)
    }

    pub(super) fn diagnostic(&self) -> Option<&PooledSyGuSUnsupportedExpr> {
        match self {
            Self::Supported => None,
            Self::Unsupported(diagnostic) => Some(diagnostic),
        }
    }
}

pub(super) fn diagnose_pooled_sygus_expr_support(expr: &IRExpr) -> PooledSyGuSExprSupport {
    diagnose_pooled_sygus_expr_support_inner(expr).map_or(
        PooledSyGuSExprSupport::Supported,
        PooledSyGuSExprSupport::Unsupported,
    )
}

fn unsupported_expr(
    expr: &IRExpr,
    feature: &'static str,
    reason: impl Into<String>,
) -> PooledSyGuSUnsupportedExpr {
    PooledSyGuSUnsupportedExpr {
        backend: "cvc5 SyGuS pooled",
        feature,
        reason: reason.into(),
        span: crate::verify::expr_span(expr),
    }
}

fn diagnose_pooled_sygus_expr_support_inner(expr: &IRExpr) -> Option<PooledSyGuSUnsupportedExpr> {
    match expr {
        IRExpr::Lit { value, .. } => match value {
            LitVal::Int { .. } | LitVal::Real { .. } | LitVal::Bool { .. } => None,
            LitVal::Float { .. } | LitVal::Str { .. } => Some(unsupported_expr(
                expr,
                "literal",
                "pooled SyGuS supports integer, real, and boolean literals today",
            )),
        },
        IRExpr::Sorry { .. } => None,
        IRExpr::Todo { .. } => Some(unsupported_expr(
            expr,
            "todo",
            "todo expressions are not admitted in pooled SyGuS verification",
        )),
        IRExpr::Var { .. } => None,
        IRExpr::Ctor { args, .. } => args
            .iter()
            .find_map(|(_, arg)| diagnose_pooled_sygus_expr_support_inner(arg)),
        IRExpr::App { func, arg, .. } => {
            if !matches!(func.as_ref(), IRExpr::Lam { .. }) {
                return Some(unsupported_expr(
                    expr,
                    "application",
                    "pooled SyGuS only supports inline lambda application today",
                ));
            }
            diagnose_pooled_sygus_expr_support_inner(func)
                .or_else(|| diagnose_pooled_sygus_expr_support_inner(arg))
        }
        IRExpr::Lam { body, .. } => diagnose_pooled_sygus_expr_support_inner(body),
        IRExpr::Field { expr: recv, .. } | IRExpr::Prime { expr: recv, .. } => {
            diagnose_pooled_sygus_expr_support_inner(recv)
        }
        IRExpr::Index { map, key, .. } => diagnose_pooled_sygus_expr_support_inner(map)
            .or_else(|| diagnose_pooled_sygus_expr_support_inner(key)),
        IRExpr::MapUpdate {
            map, key, value, ..
        } => diagnose_pooled_sygus_expr_support_inner(map)
            .or_else(|| diagnose_pooled_sygus_expr_support_inner(key))
            .or_else(|| diagnose_pooled_sygus_expr_support_inner(value)),
        IRExpr::UnOp { op, operand, .. } => {
            if !matches!(op.as_str(), "OpNot" | "not" | "!" | "OpNeg" | "-") {
                return Some(unsupported_expr(
                    expr,
                    "unary operator",
                    format!("unsupported unary op `{op}` in pooled SyGuS"),
                ));
            }
            diagnose_pooled_sygus_expr_support_inner(operand)
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            if !matches!(
                op.as_str(),
                "OpSetSubset"
                    | "OpDisjoint"
                    | "disjoint"
                    | "OpSetUnion"
                    | "OpSetIntersect"
                    | "OpSetDiff"
                    | "OpAnd"
                    | "and"
                    | "&&"
                    | "OpOr"
                    | "or"
                    | "||"
                    | "OpImplies"
                    | "implies"
                    | "=>"
                    | "OpXor"
                    | "xor"
                    | "OpEq"
                    | "=="
                    | "OpNEq"
                    | "!="
                    | "OpLt"
                    | "<"
                    | "OpLe"
                    | "<="
                    | "OpGt"
                    | ">"
                    | "OpGe"
                    | ">="
                    | "OpAdd"
                    | "+"
                    | "OpSub"
                    | "-"
                    | "OpMul"
                    | "*"
                    | "OpDiv"
                    | "/"
                    | "OpMod"
                    | "%"
            ) {
                return Some(unsupported_expr(
                    expr,
                    "binary operator",
                    format!("unsupported binary op `{op}` in pooled SyGuS"),
                ));
            }
            diagnose_pooled_sygus_expr_support_inner(left)
                .or_else(|| diagnose_pooled_sygus_expr_support_inner(right))
        }
        IRExpr::Let { bindings, body, .. } => bindings
            .iter()
            .find_map(|binding| diagnose_pooled_sygus_expr_support_inner(&binding.expr))
            .or_else(|| diagnose_pooled_sygus_expr_support_inner(body)),
        IRExpr::Block { exprs, .. } => exprs
            .iter()
            .find_map(diagnose_pooled_sygus_expr_support_inner),
        IRExpr::VarDecl { init, rest, .. } => diagnose_pooled_sygus_expr_support_inner(init)
            .or_else(|| diagnose_pooled_sygus_expr_support_inner(rest)),
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            diagnose_pooled_sygus_expr_support_inner(expr)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            if else_body.is_none() {
                return Some(unsupported_expr(
                    expr,
                    "if/else",
                    "pooled SyGuS requires an explicit else branch",
                ));
            }
            diagnose_pooled_sygus_expr_support_inner(cond)
                .or_else(|| diagnose_pooled_sygus_expr_support_inner(then_body))
                .or_else(|| {
                    else_body
                        .as_deref()
                        .and_then(diagnose_pooled_sygus_expr_support_inner)
                })
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => diagnose_pooled_sygus_expr_support_inner(scrutinee).or_else(|| {
            arms.iter().find_map(|arm| {
                arm.guard
                    .as_ref()
                    .and_then(diagnose_pooled_sygus_expr_support_inner)
                    .or_else(|| diagnose_pooled_sygus_expr_support_inner(&arm.body))
            })
        }),
        IRExpr::Choose {
            domain, predicate, ..
        } => {
            if !is_pooled_sygus_finite_scalar_domain(domain) {
                return Some(unsupported_expr(
                    expr,
                    "choose",
                    "pooled SyGuS only supports finite Bool/enum domains for choose",
                ));
            }
            predicate
                .as_deref()
                .and_then(diagnose_pooled_sygus_expr_support_inner)
        }
        IRExpr::Aggregate {
            domain,
            body,
            in_filter,
            ..
        } => {
            if !is_pooled_sygus_finite_scalar_domain(domain) {
                return Some(unsupported_expr(
                    expr,
                    "aggregate",
                    "pooled SyGuS only supports finite Bool/enum domains for finite aggregates",
                ));
            }
            in_filter
                .as_deref()
                .and_then(diagnose_pooled_sygus_expr_support_inner)
                .or_else(|| diagnose_pooled_sygus_expr_support_inner(body))
        }
        IRExpr::Forall { domain, body, .. }
        | IRExpr::Exists { domain, body, .. }
        | IRExpr::One { domain, body, .. }
        | IRExpr::Lone { domain, body, .. } => {
            if !matches!(domain, IRType::Entity { .. } | IRType::Int)
                && !is_pooled_sygus_finite_scalar_domain(domain)
            {
                return Some(unsupported_expr(
                    expr,
                    "quantifier",
                    "pooled SyGuS only supports entity, store-slot Int, or finite Bool/enum quantifier domains",
                ));
            }
            diagnose_pooled_sygus_expr_support_inner(body)
        }
        IRExpr::Card { expr: inner, .. } => diagnose_pooled_sygus_expr_support_inner(inner),
        IRExpr::SetLit { elements, .. } | IRExpr::SeqLit { elements, .. } => elements
            .iter()
            .find_map(diagnose_pooled_sygus_expr_support_inner),
        IRExpr::MapLit { entries, .. } => entries.iter().find_map(|(key, value)| {
            diagnose_pooled_sygus_expr_support_inner(key)
                .or_else(|| diagnose_pooled_sygus_expr_support_inner(value))
        }),
        IRExpr::SetComp {
            source,
            filter,
            projection,
            domain,
            ..
        } => {
            if source.is_none() && !is_pooled_sygus_finite_scalar_domain(domain) {
                return Some(unsupported_expr(
                    expr,
                    "set comprehension",
                    "pooled SyGuS only supports sourced comprehensions or finite Bool/enum domains",
                ));
            }
            source
                .as_deref()
                .and_then(diagnose_pooled_sygus_expr_support_inner)
                .or_else(|| diagnose_pooled_sygus_expr_support_inner(filter))
                .or_else(|| {
                    projection
                        .as_deref()
                        .and_then(diagnose_pooled_sygus_expr_support_inner)
                })
        }
        IRExpr::Tuple { elements, .. } => elements
            .iter()
            .find_map(diagnose_pooled_sygus_expr_support_inner),
        IRExpr::Always { body, .. }
        | IRExpr::Eventually { body, .. }
        | IRExpr::Historically { body, .. }
        | IRExpr::Once { body, .. }
        | IRExpr::Previously { body, .. } => diagnose_pooled_sygus_expr_support_inner(body),
        IRExpr::Until { left, right, .. } | IRExpr::Since { left, right, .. } => {
            diagnose_pooled_sygus_expr_support_inner(left)
                .or_else(|| diagnose_pooled_sygus_expr_support_inner(right))
        }
        IRExpr::RelComp { .. } => Some(unsupported_expr(
            expr,
            "relation comprehension",
            "relation comprehensions are not supported in pooled SyGuS",
        )),
        IRExpr::While { .. } => Some(unsupported_expr(
            expr,
            "while",
            "imperative while expressions are not supported in pooled SyGuS expression encoding",
        )),
        IRExpr::Saw { .. } => Some(unsupported_expr(
            expr,
            "saw",
            "saw expressions are not supported in pooled SyGuS",
        )),
    }
}

fn is_pooled_sygus_finite_scalar_domain(domain: &IRType) -> bool {
    matches!(domain, IRType::Bool | IRType::Enum { .. })
}

fn ensure_pooled_sygus_expr_supported(expr: &IRExpr, context: &str) -> Result<(), String> {
    let support = diagnose_pooled_sygus_expr_support(expr);
    if support.is_supported() {
        return Ok(());
    }
    let diagnostic = support
        .diagnostic()
        .expect("unsupported support result should carry a diagnostic");
    Err(format!(
        "{} expression unsupported in {context}: feature `{}`: {}{}",
        diagnostic.backend,
        diagnostic.feature,
        diagnostic.reason,
        diagnostic
            .span
            .map(|span| format!(" at {}..{}", span.start, span.end))
            .unwrap_or_default()
    ))
}

fn ensure_pooled_sygus_action_supported(action: &IRAction, context: &str) -> Result<(), String> {
    match action {
        IRAction::Choose { filter, ops, .. } => {
            ensure_pooled_sygus_expr_supported(filter, context)?;
            ensure_pooled_sygus_actions_supported(ops, context)
        }
        IRAction::ForAll { ops, .. } => ensure_pooled_sygus_actions_supported(ops, context),
        IRAction::Create { fields, .. } => fields
            .iter()
            .try_for_each(|field| ensure_pooled_sygus_expr_supported(&field.value, context)),
        IRAction::LetCrossCall { args, .. }
        | IRAction::Apply { args, .. }
        | IRAction::CrossCall { args, .. } => args
            .iter()
            .try_for_each(|arg| ensure_pooled_sygus_expr_supported(arg, context)),
        IRAction::Match { scrutinee, arms } => {
            if let crate::ir::types::IRActionMatchScrutinee::CrossCall { args, .. } = scrutinee {
                args.iter()
                    .try_for_each(|arg| ensure_pooled_sygus_expr_supported(arg, context))?;
            }
            arms.iter().try_for_each(|arm| {
                if let Some(guard) = &arm.guard {
                    ensure_pooled_sygus_expr_supported(guard, context)?;
                }
                ensure_pooled_sygus_actions_supported(&arm.body, context)
            })
        }
        IRAction::ExprStmt { expr } => ensure_pooled_sygus_expr_supported(expr, context),
    }
}

fn ensure_pooled_sygus_actions_supported(
    actions: &[IRAction],
    context: &str,
) -> Result<(), String> {
    actions
        .iter()
        .try_for_each(|action| ensure_pooled_sygus_action_supported(action, context))
}

fn ensure_pooled_sygus_system_supported(
    root_system: &IRSystem,
    systems: &[IRSystem],
    entities: &[IREntity],
    property: &IRExpr,
) -> Result<(), String> {
    ensure_pooled_sygus_expr_supported(property, "pooled safety property")?;
    for entity in entities {
        for field in &entity.fields {
            if let Some(default) = &field.default {
                ensure_pooled_sygus_expr_supported(
                    default,
                    &format!("default for {}.{}", entity.name, field.name),
                )?;
            }
        }
        for derived in &entity.derived_fields {
            ensure_pooled_sygus_expr_supported(
                &derived.body,
                &format!("derived field {}.{}", entity.name, derived.name),
            )?;
        }
        for transition in &entity.transitions {
            ensure_pooled_sygus_expr_supported(
                &transition.guard,
                &format!("transition {}.{}", entity.name, transition.name),
            )?;
            for update in &transition.updates {
                ensure_pooled_sygus_expr_supported(
                    &update.value,
                    &format!(
                        "transition update {}.{}.{}",
                        entity.name, transition.name, update.field
                    ),
                )?;
            }
        }
        for invariant in &entity.invariants {
            ensure_pooled_sygus_expr_supported(
                &invariant.body,
                &format!("entity invariant {}.{}", entity.name, invariant.name),
            )?;
        }
    }
    for system in systems {
        for field in &system.fields {
            if let Some(default) = &field.default {
                ensure_pooled_sygus_expr_supported(
                    default,
                    &format!("default for {}.{}", system.name, field.name),
                )?;
            }
        }
        for derived in &system.derived_fields {
            ensure_pooled_sygus_expr_supported(
                &derived.body,
                &format!("derived field {}.{}", system.name, derived.name),
            )?;
        }
        for invariant in &system.invariants {
            ensure_pooled_sygus_expr_supported(
                &invariant.body,
                &format!("system invariant {}.{}", system.name, invariant.name),
            )?;
        }
        for action in &system.actions {
            ensure_pooled_sygus_expr_supported(
                &action.guard,
                &format!("action {}.{}", system.name, action.name),
            )?;
            ensure_pooled_sygus_actions_supported(
                &action.body,
                &format!("action {}.{}", system.name, action.name),
            )?;
            if let Some(return_expr) = &action.return_expr {
                ensure_pooled_sygus_expr_supported(
                    return_expr,
                    &format!("action return {}.{}", system.name, action.name),
                )?;
            }
        }
    }
    if !systems.iter().any(|system| system.name == root_system.name) {
        for action in &root_system.actions {
            ensure_pooled_sygus_expr_supported(
                &action.guard,
                &format!("action {}.{}", root_system.name, action.name),
            )?;
            ensure_pooled_sygus_actions_supported(
                &action.body,
                &format!("action {}.{}", root_system.name, action.name),
            )?;
        }
    }
    Ok(())
}

#[cfg(test)]
pub(super) fn try_cvc5_sygus_multi_pooled_system_safety(
    system: &IRSystem,
    entities: &[IREntity],
    slots_per_entity: &HashMap<String, usize>,
    property: &IRExpr,
    timeout_ms: u64,
) -> Ic3Result {
    if !cvc5_sygus_enabled() {
        return Ic3Result::Unknown(cvc5_sygus_disabled_reason());
    }
    match try_cvc5_sygus_multi_pooled_system_safety_inner(
        system,
        entities,
        slots_per_entity,
        property,
        timeout_ms,
    ) {
        Ok(()) => Ic3Result::Proved,
        Err(err) => Ic3Result::Unknown(err),
    }
}

#[cfg(test)]
pub fn try_cvc5_sygus_multi_system_pooled_safety(
    root_system: &IRSystem,
    systems: &[IRSystem],
    entities: &[IREntity],
    slots_per_entity: &HashMap<String, usize>,
    property: &IRExpr,
    timeout_ms: u64,
) -> Ic3Result {
    if !cvc5_sygus_enabled() {
        return Ic3Result::Unknown(cvc5_sygus_disabled_reason());
    }
    match try_cvc5_sygus_multi_system_pooled_safety_inner(
        root_system,
        systems,
        entities,
        slots_per_entity,
        property,
        timeout_ms,
    ) {
        Ok(()) => Ic3Result::Proved,
        Err(err) => Ic3Result::Unknown(err),
    }
}

#[cfg(test)]
pub(super) fn try_cvc5_sygus_pooled_system_safety_inner(
    system: &IRSystem,
    entity: &IREntity,
    n_slots: usize,
    property: &IRExpr,
    timeout_ms: u64,
) -> Result<(), String> {
    let mut slots_per_entity = HashMap::new();
    slots_per_entity.insert(entity.name.clone(), n_slots);
    try_cvc5_sygus_multi_pooled_system_safety_inner(
        system,
        std::slice::from_ref(entity),
        &slots_per_entity,
        property,
        timeout_ms,
    )
}

#[cfg(test)]
pub(super) fn try_cvc5_sygus_multi_pooled_system_safety_inner(
    system: &IRSystem,
    entities: &[IREntity],
    slots_per_entity: &HashMap<String, usize>,
    property: &IRExpr,
    timeout_ms: u64,
) -> Result<(), String> {
    try_cvc5_sygus_multi_system_pooled_safety_inner(
        system,
        std::slice::from_ref(system),
        entities,
        slots_per_entity,
        property,
        timeout_ms,
    )
}

pub(super) fn try_cvc5_sygus_multi_system_pooled_safety_inner(
    root_system: &IRSystem,
    systems: &[IRSystem],
    entities: &[IREntity],
    slots_per_entity: &HashMap<String, usize>,
    property: &IRExpr,
    timeout_ms: u64,
) -> Result<(), String> {
    let entities_by_name: HashMap<_, _> = entities.iter().map(|e| (e.name.clone(), e)).collect();
    let systems_by_name: HashMap<_, _> = systems.iter().map(|s| (s.name.clone(), s)).collect();
    ensure_pooled_sygus_system_supported(root_system, systems, entities, property)?;
    if root_system.entities.is_empty() {
        return Err(
            "cvc5 SyGuS pooled system safety needs at least one pooled entity type".to_owned(),
        );
    }
    for entity_name in &root_system.entities {
        if !entities_by_name.contains_key(entity_name) {
            return Err(format!(
                "cvc5 SyGuS pooled system safety is missing pooled entity metadata for `{entity_name}`"
            ));
        }
        if !slots_per_entity.contains_key(entity_name) {
            return Err(format!(
                "cvc5 SyGuS pooled system safety is missing slot scope for `{entity_name}`"
            ));
        }
    }
    for system in systems {
        for store_param in &system.store_params {
            if !entities_by_name.contains_key(&store_param.entity_type) {
                return Err(format!(
                    "cvc5 SyGuS pooled system safety is missing pooled entity metadata for store param `{}` -> `{}` in `{}`",
                    store_param.name, store_param.entity_type, system.name
                ));
            }
            if !slots_per_entity.contains_key(&store_param.entity_type) {
                return Err(format!(
                    "cvc5 SyGuS pooled system safety is missing slot scope for store param `{}` -> `{}` in `{}`",
                    store_param.name, store_param.entity_type, system.name
                ));
            }
        }
    }
    for system in systems {
        for entity_name in &system.entities {
            if !entities_by_name.contains_key(entity_name) {
                return Err(format!(
                    "cvc5 SyGuS pooled system safety is missing pooled entity metadata for `{entity_name}`"
                ));
            }
            if !slots_per_entity.contains_key(entity_name) {
                return Err(format!(
                    "cvc5 SyGuS pooled system safety is missing slot scope for `{entity_name}`"
                ));
            }
        }
    }
    if entities.iter().any(|entity| {
        entity
            .fields
            .iter()
            .any(|field| field.initial_constraint.is_some())
    }) {
        return Err(
            "cvc5 SyGuS pooled system safety does not support entity initial constraints yet"
                .to_owned(),
        );
    }
    if slots_per_entity.values().any(|n_slots| *n_slots == 0) {
        return Err(
            "cvc5 SyGuS pooled system safety needs at least one slot for every pooled entity type"
                .to_owned(),
        );
    }

    let tm = Cvc5Tm::new();
    let mut solver = Cvc5Solver::new(&tm);
    solver.set_option("sygus", "true");
    solver.set_option("incremental", "false");
    if timeout_ms > 0 {
        solver.set_option("tlimit-per", &timeout_ms.to_string());
    }
    let ordered_system_fields = collect_unique_system_fields(systems)?;
    let all_fields: Vec<IRField> = ordered_system_fields
        .iter()
        .map(|(_, field)| (*field).clone())
        .chain(
            entities
                .iter()
                .flat_map(|entity| entity.fields.iter().cloned()),
        )
        .collect();
    let mut enum_catalog = build_enum_catalog(&tm, &all_fields)?;
    for system in systems {
        for derived in &system.derived_fields {
            enum_catalog.register_type(&tm, &derived.ty)?;
        }
        register_system_signature_types(&tm, &mut enum_catalog, system)?;
    }
    for entity in entities {
        for derived in &entity.derived_fields {
            enum_catalog.register_type(&tm, &derived.ty)?;
        }
    }
    solver.set_logic(if requires_all_logic(&enum_catalog, &all_fields, &[]) {
        "ALL"
    } else {
        "LIA"
    });

    let mut curr_vars = HashMap::new();
    let mut next_vars = HashMap::new();
    let mut curr_order = Vec::new();
    let mut next_order = Vec::new();

    for (_, field) in &ordered_system_fields {
        let sort = sort_for_field(&tm, field, &enum_catalog)?;
        let curr = tm.mk_var(sort.clone(), &field.name);
        let next = tm.mk_var(sort, &format!("{}_next", field.name));
        curr_vars.insert(field.name.clone(), curr.clone());
        next_vars.insert(field.name.clone(), next.clone());
        curr_order.push(curr);
        next_order.push(next);
    }
    for system in systems {
        extend_with_derived_fields(&tm, &mut curr_vars, &system.derived_fields, &enum_catalog)?;
        extend_with_derived_fields(&tm, &mut next_vars, &system.derived_fields, &enum_catalog)?;
    }

    let mut active_curr: HashMap<String, HashMap<usize, Cvc5Term>> = HashMap::new();
    let mut active_next: HashMap<String, HashMap<usize, Cvc5Term>> = HashMap::new();
    let mut slot_curr = HashMap::new();
    let mut slot_next = HashMap::new();
    for entity_name in slots_per_entity.keys() {
        let entity = entities_by_name
            .get(entity_name)
            .ok_or_else(|| format!("missing pooled entity `{entity_name}`"))?;
        let n_slots = *slots_per_entity
            .get(entity_name)
            .ok_or_else(|| format!("missing slot count for pooled entity `{entity_name}`"))?;
        let mut entity_active_curr = HashMap::new();
        let mut entity_active_next = HashMap::new();
        for slot in 0..n_slots {
            let active = tm.mk_var(
                tm.boolean_sort(),
                &format!("{}_{}_active", entity.name, slot),
            );
            let active_n = tm.mk_var(
                tm.boolean_sort(),
                &format!("{}_{}_active_next", entity.name, slot),
            );
            entity_active_curr.insert(slot, active.clone());
            entity_active_next.insert(slot, active_n.clone());
            curr_order.push(active);
            next_order.push(active_n);

            for field in &entity.fields {
                let sort = sort_for_field(&tm, field, &enum_catalog)?;
                let curr = tm.mk_var(
                    sort.clone(),
                    &format!("{}_{}_{}", entity.name, slot, field.name),
                );
                let next = tm.mk_var(
                    sort,
                    &format!("{}_{}_{}_next", entity.name, slot, field.name),
                );
                slot_curr.insert(
                    pool_slot_field_key(&entity.name, slot, &field.name),
                    curr.clone(),
                );
                slot_next.insert(
                    pool_slot_field_key(&entity.name, slot, &field.name),
                    next.clone(),
                );
                curr_order.push(curr);
                next_order.push(next);
            }
            extend_pooled_slot_with_derived_fields(
                &tm,
                entity,
                slot,
                &mut slot_curr,
                &enum_catalog,
            )?;
            extend_pooled_slot_with_derived_fields(
                &tm,
                entity,
                slot,
                &mut slot_next,
                &enum_catalog,
            )?;
        }
        active_curr.insert(entity.name.clone(), entity_active_curr);
        active_next.insert(entity.name.clone(), entity_active_next);
    }

    let store_param_types = system_store_param_types(root_system);

    let pre_ctx = PooledSyGuSCtx {
        slots_per_entity,
        active_vars: &active_curr,
        slot_fields: &slot_curr,
        store_param_types: &store_param_types,
    };
    let mut pre_conjuncts = ordered_system_fields
        .iter()
        .map(|(_, field)| encode_initial_field(&tm, field, &curr_vars, &enum_catalog))
        .collect::<Result<Vec<_>, _>>()?;
    for entity_name in slots_per_entity.keys() {
        let entity = entities_by_name
            .get(entity_name)
            .ok_or_else(|| format!("missing pooled entity `{entity_name}`"))?;
        let n_slots = *slots_per_entity
            .get(entity_name)
            .ok_or_else(|| format!("missing slot count for pooled entity `{entity_name}`"))?;
        for slot in 0..n_slots {
            pre_conjuncts.push(
                tm.mk_term(
                    Cvc5Kind::CVC5_KIND_NOT,
                    &[active_curr
                        .get(entity_name)
                        .and_then(|slots| slots.get(&slot))
                        .ok_or_else(|| {
                            format!("missing active variable for {entity_name} slot {slot}")
                        })?
                        .clone()],
                ),
            );
            for field in &entity.fields {
                if let Some(default) = &field.default {
                    let next = slot_curr
                        .get(&pool_slot_field_key(&entity.name, slot, &field.name))
                        .ok_or_else(|| {
                            format!(
                                "missing pooled field `{}` for {entity_name} slot {slot}",
                                field.name
                            )
                        })?;
                    let encoded = encode_pooled_expr(
                        &tm,
                        default,
                        &curr_vars,
                        &HashMap::new(),
                        &pre_ctx,
                        &enum_catalog,
                    )?;
                    pre_conjuncts
                        .push(tm.mk_term(Cvc5Kind::CVC5_KIND_EQUAL, &[next.clone(), encoded]));
                }
            }
        }
    }
    let pre_body = mk_and(&tm, &pre_conjuncts);

    let trans_clauses = root_system
        .actions
        .iter()
        .map(|step| {
            encode_pooled_system_step(
                &tm,
                step,
                PooledStepCtx {
                    system: root_system,
                    systems_by_name: &systems_by_name,
                    entities_by_name: &entities_by_name,
                    slots_per_entity,
                    curr_vars: &curr_vars,
                    next_vars: &next_vars,
                    frames: PooledFrameVars {
                        active_curr: &active_curr,
                        active_next: &active_next,
                        slot_curr: &slot_curr,
                        slot_next: &slot_next,
                    },
                    enum_catalog: &enum_catalog,
                    call_stack: std::slice::from_ref(&root_system.name),
                },
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    if trans_clauses.is_empty() {
        return Err("cvc5 SyGuS pooled system safety requires at least one step".to_owned());
    }
    let trans_body = mk_or(&tm, &trans_clauses);

    let prop_ctx = PooledSyGuSCtx {
        slots_per_entity,
        active_vars: &active_curr,
        slot_fields: &slot_curr,
        store_param_types: &store_param_types,
    };
    let property_body = encode_pooled_expr(
        &tm,
        &safety_obligation_expr(property, &root_system.invariants),
        &curr_vars,
        &HashMap::new(),
        &prop_ctx,
        &enum_catalog,
    )?;

    let bool_sort = tm.boolean_sort();
    let mut trans_params = curr_order.clone();
    trans_params.extend(next_order.iter().cloned());

    let pre_fun = solver.define_fun("pre_abide", &curr_order, bool_sort.clone(), pre_body, false);
    let trans_fun = solver.define_fun(
        "trans_abide",
        &trans_params,
        bool_sort.clone(),
        trans_body,
        false,
    );
    let post_fun = solver.define_fun(
        "post_abide",
        &curr_order,
        bool_sort.clone(),
        property_body,
        false,
    );
    let inv_fun = solver.synth_fun("inv_abide", &curr_order, bool_sort);

    solver.add_sygus_inv_constraint(inv_fun.clone(), pre_fun, trans_fun, post_fun);

    let result = solver.check_synth();
    if result.has_solution() {
        let _solution = solver.get_synth_solution(inv_fun);
        Ok(())
    } else if result.is_unknown() {
        Err(format!(
            "cvc5 SyGuS returned Unknown for pooled system safety ({result})"
        ))
    } else if result.has_no_solution() {
        Err(
            "cvc5 SyGuS found no invariant solution for the supported pooled-system safety slice"
                .to_owned(),
        )
    } else {
        Err(format!(
            "cvc5 SyGuS returned an unrecognized result: {result}"
        ))
    }
}

fn pool_slot_field_key(entity: &str, slot: usize, field: &str) -> String {
    format!("{entity}:{slot}:{field}")
}

fn extend_pooled_slot_with_derived_fields(
    tm: &Cvc5Tm,
    entity: &IREntity,
    slot: usize,
    slot_fields: &mut HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
) -> Result<(), String> {
    let mut vars = HashMap::new();
    for field in &entity.fields {
        vars.insert(
            field.name.clone(),
            slot_fields
                .get(&pool_slot_field_key(&entity.name, slot, &field.name))
                .ok_or_else(|| format!("missing pooled field `{}`", field.name))?
                .clone(),
        );
    }
    for derived in &entity.derived_fields {
        let value = encode_expr(tm, &derived.body, &vars, enum_catalog)?;
        vars.insert(derived.name.clone(), value.clone());
        slot_fields.insert(
            pool_slot_field_key(&entity.name, slot, &derived.name),
            value,
        );
    }
    Ok(())
}

#[cfg(test)]
pub(super) fn encode_pooled_transition_at_slot_for_test(
    tm: &Cvc5Tm,
    trans: &IRTransition,
    entity: &IREntity,
    enum_catalog: &EnumCatalog,
) -> Result<Cvc5Term, String> {
    let mut active_curr = HashMap::new();
    let mut active_next = HashMap::new();
    active_curr.insert(
        entity.name.clone(),
        HashMap::from([(0usize, tm.mk_boolean(true))]),
    );
    active_next.insert(
        entity.name.clone(),
        HashMap::from([(0usize, tm.mk_boolean(true))]),
    );

    let mut slot_curr = HashMap::new();
    let mut slot_next = HashMap::new();
    for field in &entity.fields {
        let sort = sort_for_field(tm, field, enum_catalog)?;
        slot_curr.insert(
            pool_slot_field_key(&entity.name, 0, &field.name),
            tm.mk_var(sort.clone(), &format!("{}_0_{}", entity.name, field.name)),
        );
        slot_next.insert(
            pool_slot_field_key(&entity.name, 0, &field.name),
            tm.mk_var(sort, &format!("{}_0_{}_next", entity.name, field.name)),
        );
    }
    extend_pooled_slot_with_derived_fields(tm, entity, 0, &mut slot_curr, enum_catalog)?;
    extend_pooled_slot_with_derived_fields(tm, entity, 0, &mut slot_next, enum_catalog)?;
    let slots_per_entity = HashMap::from([(entity.name.clone(), 1usize)]);
    let store_param_types = HashMap::new();
    let pool_ctx = PooledSyGuSCtx {
        slots_per_entity: &slots_per_entity,
        active_vars: &active_curr,
        slot_fields: &slot_curr,
        store_param_types: &store_param_types,
    };

    encode_pooled_transition_at_slot(
        tm,
        trans,
        entity,
        0,
        &[],
        PooledSlotTransitionCtx {
            vars: &HashMap::new(),
            entity_bindings: &HashMap::new(),
            frames: PooledFrameVars {
                active_curr: &active_curr,
                active_next: &active_next,
                slot_curr: &slot_curr,
                slot_next: &slot_next,
            },
            enum_catalog,
            pool_ctx: &pool_ctx,
        },
    )
}

#[cfg(test)]
pub(super) fn encode_pooled_system_step_for_test(
    tm: &Cvc5Tm,
    step: &IRSystemAction,
    system: &IRSystem,
    entities: &[IREntity],
    slots_per_entity: &HashMap<String, usize>,
    enum_catalog: &EnumCatalog,
) -> Result<Cvc5Term, String> {
    encode_pooled_system_step_for_systems_test(
        tm,
        step,
        system,
        std::slice::from_ref(system),
        entities,
        slots_per_entity,
        enum_catalog,
    )
}

#[cfg(test)]
pub(super) fn encode_pooled_system_step_for_systems_test(
    tm: &Cvc5Tm,
    step: &IRSystemAction,
    system: &IRSystem,
    systems: &[IRSystem],
    entities: &[IREntity],
    slots_per_entity: &HashMap<String, usize>,
    enum_catalog: &EnumCatalog,
) -> Result<Cvc5Term, String> {
    let systems_by_name: HashMap<_, _> = systems
        .iter()
        .map(|system| (system.name.clone(), system))
        .collect();
    let entities_by_name: HashMap<_, _> = entities
        .iter()
        .map(|entity| (entity.name.clone(), entity))
        .collect();
    let mut curr_vars = HashMap::new();
    let mut next_vars = HashMap::new();
    for field in &system.fields {
        let sort = sort_for_field(tm, field, enum_catalog)?;
        curr_vars.insert(field.name.clone(), tm.mk_var(sort.clone(), &field.name));
        next_vars.insert(
            field.name.clone(),
            tm.mk_var(sort, &format!("{}_next", field.name)),
        );
    }
    extend_with_derived_fields(tm, &mut curr_vars, &system.derived_fields, enum_catalog)?;
    extend_with_derived_fields(tm, &mut next_vars, &system.derived_fields, enum_catalog)?;

    let mut active_curr = HashMap::new();
    let mut active_next = HashMap::new();
    let mut slot_curr = HashMap::new();
    let mut slot_next = HashMap::new();
    for entity in entities {
        let n_slots = *slots_per_entity
            .get(&entity.name)
            .ok_or_else(|| format!("missing slot scope for `{}`", entity.name))?;
        let mut per_active_curr = HashMap::new();
        let mut per_active_next = HashMap::new();
        for slot in 0..n_slots {
            per_active_curr.insert(
                slot,
                tm.mk_var(
                    tm.boolean_sort(),
                    &format!("{}_{}_active", entity.name, slot),
                ),
            );
            per_active_next.insert(
                slot,
                tm.mk_var(
                    tm.boolean_sort(),
                    &format!("{}_{}_active_next", entity.name, slot),
                ),
            );
            for field in &entity.fields {
                let sort = sort_for_field(tm, field, enum_catalog)?;
                slot_curr.insert(
                    pool_slot_field_key(&entity.name, slot, &field.name),
                    tm.mk_var(
                        sort.clone(),
                        &format!("{}_{}_{}", entity.name, slot, field.name),
                    ),
                );
                slot_next.insert(
                    pool_slot_field_key(&entity.name, slot, &field.name),
                    tm.mk_var(
                        sort,
                        &format!("{}_{}_{}_next", entity.name, slot, field.name),
                    ),
                );
            }
            extend_pooled_slot_with_derived_fields(tm, entity, slot, &mut slot_curr, enum_catalog)?;
            extend_pooled_slot_with_derived_fields(tm, entity, slot, &mut slot_next, enum_catalog)?;
        }
        active_curr.insert(entity.name.clone(), per_active_curr);
        active_next.insert(entity.name.clone(), per_active_next);
    }

    encode_pooled_system_step(
        tm,
        step,
        PooledStepCtx {
            system,
            systems_by_name: &systems_by_name,
            entities_by_name: &entities_by_name,
            slots_per_entity,
            curr_vars: &curr_vars,
            next_vars: &next_vars,
            frames: PooledFrameVars {
                active_curr: &active_curr,
                active_next: &active_next,
                slot_curr: &slot_curr,
                slot_next: &slot_next,
            },
            enum_catalog,
            call_stack: std::slice::from_ref(&system.name),
        },
    )
}

fn frame_pooled_slot(
    tm: &Cvc5Tm,
    entity: &IREntity,
    slot: usize,
    active_curr: &HashMap<String, HashMap<usize, Cvc5Term>>,
    active_next: &HashMap<String, HashMap<usize, Cvc5Term>>,
    slot_curr: &HashMap<String, Cvc5Term>,
    slot_next: &HashMap<String, Cvc5Term>,
) -> Result<Cvc5Term, String> {
    let mut conjuncts = vec![tm.mk_term(
        Cvc5Kind::CVC5_KIND_EQUAL,
        &[
            active_next
                .get(&entity.name)
                .and_then(|slots| slots.get(&slot))
                .ok_or_else(|| {
                    format!(
                        "missing next active variable for {} slot {slot}",
                        entity.name
                    )
                })?
                .clone(),
            active_curr
                .get(&entity.name)
                .and_then(|slots| slots.get(&slot))
                .ok_or_else(|| {
                    format!(
                        "missing current active variable for {} slot {slot}",
                        entity.name
                    )
                })?
                .clone(),
        ],
    )];
    for field in &entity.fields {
        conjuncts.push(
            tm.mk_term(
                Cvc5Kind::CVC5_KIND_EQUAL,
                &[
                    slot_next
                        .get(&pool_slot_field_key(&entity.name, slot, &field.name))
                        .ok_or_else(|| format!("missing next pooled field `{}`", field.name))?
                        .clone(),
                    slot_curr
                        .get(&pool_slot_field_key(&entity.name, slot, &field.name))
                        .ok_or_else(|| format!("missing current pooled field `{}`", field.name))?
                        .clone(),
                ],
            ),
        );
    }
    Ok(mk_and(tm, &conjuncts))
}

fn frame_other_pooled_slots(
    tm: &Cvc5Tm,
    entity: &IREntity,
    excluded_slot: usize,
    frame_vars: PooledFrameVars<'_>,
    n_slots: usize,
) -> Result<Vec<Cvc5Term>, String> {
    let mut frames = Vec::new();
    for slot in 0..n_slots {
        if slot == excluded_slot {
            continue;
        }
        frames.push(frame_pooled_slot(
            tm,
            entity,
            slot,
            frame_vars.active_curr,
            frame_vars.active_next,
            frame_vars.slot_curr,
            frame_vars.slot_next,
        )?);
    }
    Ok(frames)
}

fn frame_other_pooled_entities(
    tm: &Cvc5Tm,
    entities_by_name: &HashMap<String, &IREntity>,
    slots_per_entity: &HashMap<String, usize>,
    excluded_entity: &str,
    frame_vars: PooledFrameVars<'_>,
) -> Result<Vec<Cvc5Term>, String> {
    let mut frames = Vec::new();
    for (entity_name, n_slots) in slots_per_entity {
        if entity_name == excluded_entity {
            continue;
        }
        let entity = entities_by_name
            .get(entity_name)
            .ok_or_else(|| format!("missing pooled entity `{entity_name}`"))?;
        for slot in 0..*n_slots {
            frames.push(frame_pooled_slot(
                tm,
                entity,
                slot,
                frame_vars.active_curr,
                frame_vars.active_next,
                frame_vars.slot_curr,
                frame_vars.slot_next,
            )?);
        }
    }
    Ok(frames)
}

fn frame_all_system_fields(
    tm: &Cvc5Tm,
    systems_by_name: &HashMap<String, &IRSystem>,
    curr_vars: &HashMap<String, Cvc5Term>,
    next_vars: &HashMap<String, Cvc5Term>,
) -> Result<Vec<Cvc5Term>, String> {
    let mut frames = Vec::new();
    for system in systems_by_name.values() {
        for field in &system.fields {
            let curr = curr_vars.get(&field.name).ok_or_else(|| {
                format!(
                    "missing current system field `{}` for `{}`",
                    field.name, system.name
                )
            })?;
            let next = next_vars.get(&field.name).ok_or_else(|| {
                format!(
                    "missing next system field `{}` for `{}`",
                    field.name, system.name
                )
            })?;
            frames.push(tm.mk_term(Cvc5Kind::CVC5_KIND_EQUAL, &[next.clone(), curr.clone()]));
        }
    }
    Ok(frames)
}

fn frame_system_fields_except(
    tm: &Cvc5Tm,
    systems_by_name: &HashMap<String, &IRSystem>,
    curr_vars: &HashMap<String, Cvc5Term>,
    next_vars: &HashMap<String, Cvc5Term>,
    touched: &HashSet<String>,
) -> Result<Vec<Cvc5Term>, String> {
    let mut frames = Vec::new();
    for system in systems_by_name.values() {
        for field in &system.fields {
            if touched.contains(&field.name) {
                continue;
            }
            let curr = curr_vars.get(&field.name).ok_or_else(|| {
                format!(
                    "missing current system field `{}` for `{}`",
                    field.name, system.name
                )
            })?;
            let next = next_vars.get(&field.name).ok_or_else(|| {
                format!(
                    "missing next system field `{}` for `{}`",
                    field.name, system.name
                )
            })?;
            frames.push(tm.mk_term(Cvc5Kind::CVC5_KIND_EQUAL, &[next.clone(), curr.clone()]));
        }
    }
    Ok(frames)
}

fn frame_all_pooled_entities(
    tm: &Cvc5Tm,
    entities_by_name: &HashMap<String, &IREntity>,
    slots_per_entity: &HashMap<String, usize>,
    active_curr: &HashMap<String, HashMap<usize, Cvc5Term>>,
    active_next: &HashMap<String, HashMap<usize, Cvc5Term>>,
    slot_curr: &HashMap<String, Cvc5Term>,
    slot_next: &HashMap<String, Cvc5Term>,
) -> Result<Vec<Cvc5Term>, String> {
    let mut frames = Vec::new();
    for (entity_name, n_slots) in slots_per_entity {
        let entity = entities_by_name
            .get(entity_name)
            .ok_or_else(|| format!("missing pooled entity `{entity_name}`"))?;
        for slot in 0..*n_slots {
            frames.push(frame_pooled_slot(
                tm,
                entity,
                slot,
                active_curr,
                active_next,
                slot_curr,
                slot_next,
            )?);
        }
    }
    Ok(frames)
}

fn enumerate_pooled_param_envs(
    tm: &Cvc5Tm,
    step: &IRSystemAction,
    params: &[IRTransParam],
    slots_per_entity: &HashMap<String, usize>,
    enum_catalog: &EnumCatalog,
) -> Result<Vec<PooledParamEnv>, String> {
    let mut envs = vec![PooledParamEnv::default()];
    for param in params {
        let mut next_envs = Vec::new();
        let entity_name = entity_type_name(&param.ty).map(str::to_owned).or_else(|| {
            infer_entity_param_entity(&param.name, &param.ty, &step.body, slots_per_entity)
        });
        if let Some(name) = entity_name.as_deref() {
            let n_slots = *slots_per_entity.get(name).ok_or_else(|| {
                    format!("cvc5 SyGuS pooled system safety is missing slot scope for entity param `{}` -> `{name}`", param.name)
                })?;
            for env in &envs {
                for slot in 0..n_slots {
                    let mut extended = env.clone();
                    extended
                        .terms
                        .insert(param.name.clone(), tm.mk_integer(slot as i64));
                    extended
                        .entity_bindings
                        .insert(param.name.clone(), (name.to_owned(), slot));
                    next_envs.push(extended);
                }
            }
        } else {
            let values = finite_param_values(tm, param, enum_catalog)?;
            for env in &envs {
                for value in &values {
                    let mut extended = env.clone();
                    extended.terms.insert(param.name.clone(), value.clone());
                    next_envs.push(extended);
                }
            }
        }
        envs = next_envs;
    }
    Ok(envs)
}

fn entity_type_name(ty: &IRType) -> Option<&str> {
    match ty {
        IRType::Entity { name } => Some(name),
        IRType::Refinement { base, .. } => entity_type_name(base),
        _ => None,
    }
}

fn infer_entity_param_entity(
    param: &str,
    ty: &IRType,
    actions: &[IRAction],
    slots_per_entity: &HashMap<String, usize>,
) -> Option<String> {
    if !matches!(ty, IRType::Int) || !actions_use_entity_param(actions, param) {
        return None;
    }
    slots_per_entity
        .keys()
        .filter(|name| !name.starts_with("__abide_procinst__"))
        .find(|name| name.eq_ignore_ascii_case(param))
        .cloned()
}

fn actions_use_entity_param(actions: &[IRAction], param: &str) -> bool {
    actions.iter().any(|action| match action {
        IRAction::Apply {
            target, refs, args, ..
        } => {
            target == param
                || refs.iter().any(|reference| reference == param)
                || args.iter().any(|arg| expr_uses_entity_param(arg, param))
        }
        IRAction::ExprStmt { expr } => expr_uses_entity_param(expr, param),
        IRAction::Choose { filter, ops, .. } => {
            expr_uses_entity_param(filter, param) || actions_use_entity_param(ops, param)
        }
        IRAction::ForAll { ops, .. } => actions_use_entity_param(ops, param),
        IRAction::CrossCall { args, .. } | IRAction::LetCrossCall { args, .. } => {
            args.iter().any(|arg| expr_uses_entity_param(arg, param))
        }
        IRAction::Match { arms, .. } => arms.iter().any(|arm| {
            arm.guard
                .as_ref()
                .is_some_and(|guard| expr_uses_entity_param(guard, param))
                || actions_use_entity_param(&arm.body, param)
        }),
        IRAction::Create { fields, .. } => fields
            .iter()
            .any(|field| expr_uses_entity_param(&field.value, param)),
    })
}

fn expr_uses_entity_param(expr: &IRExpr, param: &str) -> bool {
    match expr {
        IRExpr::Var { name, .. } => name == param,
        IRExpr::Field { expr, .. } | IRExpr::Prime { expr, .. } => {
            expr_uses_entity_param(expr, param)
        }
        IRExpr::BinOp { left, right, .. } => {
            expr_uses_entity_param(left, param) || expr_uses_entity_param(right, param)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            expr_uses_entity_param(cond, param)
                || expr_uses_entity_param(then_body, param)
                || else_body
                    .as_ref()
                    .is_some_and(|body| expr_uses_entity_param(body, param))
        }
        IRExpr::Ctor { args, .. } => args
            .iter()
            .any(|(_, arg)| expr_uses_entity_param(arg, param)),
        IRExpr::Block { exprs, .. } => exprs.iter().any(|stmt| expr_uses_entity_param(stmt, param)),
        _ => false,
    }
}

fn pooled_entity_binding_active_constraints(
    active_vars: &HashMap<String, HashMap<usize, Cvc5Term>>,
    entity_bindings: &PooledEntityBindings,
) -> Result<Vec<Cvc5Term>, String> {
    entity_bindings
        .values()
        .map(|(entity, slot)| {
            active_vars
                .get(entity)
                .and_then(|slots| slots.get(slot))
                .cloned()
                .ok_or_else(|| format!("missing active variable for {entity} slot {slot}"))
        })
        .collect()
}

fn resolve_pooled_ref_bindings(
    trans: &IRTransition,
    apply_refs: &[String],
    available_bindings: &PooledEntityBindings,
) -> Result<PooledEntityBindings, String> {
    if trans.refs.len() != apply_refs.len() {
        return Err(format!(
            "cvc5 SyGuS pooled system safety expected {} refs for transition `{}`, got {}",
            trans.refs.len(),
            trans.name,
            apply_refs.len()
        ));
    }

    let mut resolved = HashMap::new();
    for (ref_decl, apply_ref_name) in trans.refs.iter().zip(apply_refs.iter()) {
        let binding = available_bindings.get(apply_ref_name).ok_or_else(|| {
            format!(
                "unknown pooled ref binding `{apply_ref_name}` for transition `{}`",
                trans.name
            )
        })?;
        if binding.0 != ref_decl.entity {
            return Err(format!(
                "cvc5 SyGuS pooled system safety expected ref `{}` on transition `{}` to bind entity `{}`, got `{}`",
                ref_decl.name, trans.name, ref_decl.entity, binding.0
            ));
        }
        resolved.insert(ref_decl.name.clone(), binding.clone());
    }
    Ok(resolved)
}

fn override_pooled_slot_fields(
    base: &HashMap<String, Cvc5Term>,
    entity: &IREntity,
    slot: usize,
    overrides: &HashMap<String, Cvc5Term>,
) -> HashMap<String, Cvc5Term> {
    let mut map = base.clone();
    for field in &entity.fields {
        if let Some(value) = overrides.get(&field.name) {
            map.insert(
                pool_slot_field_key(&entity.name, slot, &field.name),
                value.clone(),
            );
        }
    }
    map
}

fn mk_exists(tm: &Cvc5Tm, vars: &[Cvc5Term], body: Cvc5Term) -> Cvc5Term {
    if vars.is_empty() {
        body
    } else {
        let var_list = tm.mk_term(Cvc5Kind::CVC5_KIND_VARIABLE_LIST, vars);
        tm.mk_term(Cvc5Kind::CVC5_KIND_EXISTS, &[var_list, body])
    }
}

fn encode_pooled_ops_for_target(
    tm: &Cvc5Tm,
    ops: &[IRAction],
    target: PooledTargetSlot<'_>,
    ctx: PooledNestedOpsCtx<'_>,
) -> Result<Cvc5Term, String> {
    let target_var = target.var;
    let target_entity = target.entity;
    let target_slot = target.slot;
    let entities_by_name = ctx.entities_by_name;
    let slots_per_entity = ctx.slots_per_entity;
    let vars = ctx.vars;
    let next_vars = ctx.next_vars;
    let entity_bindings = ctx.entity_bindings;
    let active_curr = ctx.frames.active_curr;
    let active_next = ctx.frames.active_next;
    let slot_curr = ctx.frames.slot_curr;
    let slot_next = ctx.frames.slot_next;
    let enum_catalog = ctx.enum_catalog;
    let pool_ctx = ctx.pool_ctx;
    if ops.is_empty() {
        return Err("cvc5 SyGuS pooled system safety requires at least one nested op".to_owned());
    }
    if ops.len() > 1 {
        let mut intermediates = Vec::new();
        let mut bound = Vec::new();
        for stage in 0..(ops.len() - 1) {
            let mut fields = HashMap::new();
            for field in &target_entity.fields {
                let sort = sort_for_field(tm, field, enum_catalog)?;
                let name = format!(
                    "__abide_sygus_{}_slot{}_{}_inter{}",
                    target_entity.name, target_slot, field.name, stage
                );
                let term = tm.mk_var(sort, &name);
                bound.push(term.clone());
                fields.insert(field.name.clone(), term);
            }
            intermediates.push(fields);
        }

        let mut conjuncts = Vec::new();
        for (idx, op) in ops.iter().enumerate() {
            let read_target_fields = if idx == 0 {
                None
            } else {
                Some(&intermediates[idx - 1])
            };
            let write_target_fields = if idx + 1 == ops.len() {
                None
            } else {
                Some(&intermediates[idx])
            };

            let stage_read_fields = if let Some(overrides) = read_target_fields {
                override_pooled_slot_fields(slot_curr, target_entity, target_slot, overrides)
            } else {
                slot_curr.clone()
            };
            let stage_write_fields = if let Some(overrides) = write_target_fields {
                override_pooled_slot_fields(slot_next, target_entity, target_slot, overrides)
            } else {
                slot_next.clone()
            };
            let stage_pool_ctx = PooledSyGuSCtx {
                slots_per_entity: pool_ctx.slots_per_entity,
                active_vars: pool_ctx.active_vars,
                slot_fields: &stage_read_fields,
                store_param_types: pool_ctx.store_param_types,
            };
            let stage_active_next = if idx + 1 == ops.len() {
                active_next
            } else {
                active_curr
            };
            conjuncts.push(encode_pooled_ops_for_target(
                tm,
                std::slice::from_ref(op),
                target,
                PooledNestedOpsCtx {
                    frames: PooledFrameVars {
                        active_curr,
                        active_next: stage_active_next,
                        slot_curr: &stage_read_fields,
                        slot_next: &stage_write_fields,
                    },
                    pool_ctx: &stage_pool_ctx,
                    ..ctx
                },
            )?);
        }
        return Ok(mk_exists(tm, &bound, mk_and(tm, &conjuncts)));
    }
    match &ops[0] {
        IRAction::Apply {
            target,
            transition,
            refs,
            args,
        } => {
            if target != target_var {
                return Err(
                    "cvc5 SyGuS pooled system safety only supports apply on the selected target variable"
                        .to_owned(),
                );
            }
            let trans = target_entity
                .transitions
                .iter()
                .find(|trans| trans.name == *transition)
                .ok_or_else(|| {
                    format!(
                        "unknown transition `{transition}` on `{}`",
                        target_entity.name
                    )
                })?;
            let mut resolved_bindings = entity_bindings.clone();
            resolved_bindings.extend(resolve_pooled_ref_bindings(trans, refs, entity_bindings)?);
            encode_pooled_transition_at_slot(
                tm,
                trans,
                target_entity,
                target_slot,
                args,
                PooledSlotTransitionCtx {
                    vars,
                    entity_bindings: &resolved_bindings,
                    frames: PooledFrameVars {
                        active_curr,
                        active_next,
                        slot_curr,
                        slot_next,
                    },
                    enum_catalog,
                    pool_ctx,
                },
            )
        }
        IRAction::Choose {
            var,
            entity: choose_entity,
            filter,
            ops: inner_ops,
        } => {
            let choose_target = entities_by_name
                .get(choose_entity)
                .ok_or_else(|| format!("unknown pooled entity `{choose_entity}`"))?;
            let n_slots = *slots_per_entity
                .get(choose_entity)
                .ok_or_else(|| format!("missing slot scope for `{choose_entity}`"))?;
            let mut branches = Vec::new();
            for slot in 0..n_slots {
                let mut bindings = entity_bindings.clone();
                bindings.insert(var.clone(), (choose_entity.clone(), slot));
                let scoped_vars = pooled_target_scoped_vars(choose_target, slot, vars, slot_curr)?;
                branches.push(mk_and(
                    tm,
                    &[
                        active_curr
                            .get(choose_entity)
                            .and_then(|slots| slots.get(&slot))
                            .ok_or_else(|| {
                                format!(
                                    "missing current active variable for {choose_entity} slot {slot}"
                                )
                            })?
                            .clone(),
                        encode_pooled_expr(
                            tm,
                            filter,
                            &scoped_vars,
                            &bindings,
                            pool_ctx,
                            enum_catalog,
                        )?,
                        encode_pooled_ops_for_target(
                            tm,
                            inner_ops,
                            target,
                            PooledNestedOpsCtx {
                                vars: &scoped_vars,
                                entity_bindings: &bindings,
                                ..ctx
                            },
                        )?,
                    ],
                ));
            }
            Ok(mk_or(tm, &branches))
        }
        IRAction::ForAll {
            var,
            entity: forall_entity,
            ops: inner_ops,
        } => encode_pooled_ops_forall_for_target(tm, var, forall_entity, inner_ops, target, ctx),
        IRAction::Match { scrutinee, arms } => {
            encode_pooled_ops_match_for_target(tm, scrutinee, arms, target, ctx)
        }
        IRAction::ExprStmt { expr } => encode_pooled_entity_exprstmt_at_slot(
            tm,
            expr,
            target,
            PooledSlotTransitionCtx {
                vars,
                entity_bindings,
                frames: PooledFrameVars {
                    active_curr,
                    active_next,
                    slot_curr,
                    slot_next,
                },
                enum_catalog,
                pool_ctx,
            },
        ),
        IRAction::CrossCall {
            system: target_system_name,
            command,
            args,
        } => encode_pooled_crosscall_capture(
            tm,
            target_system_name,
            command,
            args,
            PooledCrossCallCtx {
                systems_by_name: ctx.systems_by_name,
                entities_by_name,
                slots_per_entity,
                curr_vars: vars,
                next_vars,
                entity_bindings,
                frames: PooledFrameVars {
                    active_curr,
                    active_next,
                    slot_curr,
                    slot_next,
                },
                enum_catalog,
                call_stack: ctx.call_stack,
            },
        )
        .map(|capture| capture.formula),
        other => Err(format!(
            "cvc5 SyGuS pooled system safety does not support nested op `{other:?}` yet"
        )),
    }
}

fn encode_pooled_ops_forall_for_target(
    tm: &Cvc5Tm,
    var: &str,
    forall_entity: &str,
    ops: &[IRAction],
    target: PooledTargetSlot<'_>,
    ctx: PooledNestedOpsCtx<'_>,
) -> Result<Cvc5Term, String> {
    ctx.entities_by_name
        .get(forall_entity)
        .ok_or_else(|| format!("unknown pooled entity `{forall_entity}`"))?;
    let n_slots = *ctx
        .slots_per_entity
        .get(forall_entity)
        .ok_or_else(|| format!("missing slot scope for `{forall_entity}`"))?;
    let mut conjuncts = Vec::with_capacity(n_slots);
    for slot in 0..n_slots {
        let active = ctx
            .frames
            .active_curr
            .get(forall_entity)
            .and_then(|slots| slots.get(&slot))
            .ok_or_else(|| {
                format!("missing current active variable for {forall_entity} slot {slot}")
            })?
            .clone();
        let mut bindings = ctx.entity_bindings.clone();
        bindings.insert(var.to_owned(), (forall_entity.to_owned(), slot));
        let body = encode_pooled_ops_for_target(
            tm,
            ops,
            target,
            PooledNestedOpsCtx {
                entity_bindings: &bindings,
                ..ctx
            },
        )?;
        conjuncts.push(tm.mk_term(Cvc5Kind::CVC5_KIND_IMPLIES, &[active, body]));
    }
    Ok(mk_and(tm, &conjuncts))
}

fn pooled_target_scoped_vars(
    entity: &IREntity,
    slot: usize,
    vars: &HashMap<String, Cvc5Term>,
    slot_curr: &HashMap<String, Cvc5Term>,
) -> Result<HashMap<String, Cvc5Term>, String> {
    let mut scoped = vars.clone();
    for field in &entity.fields {
        scoped.insert(
            field.name.clone(),
            slot_curr
                .get(&pool_slot_field_key(&entity.name, slot, &field.name))
                .ok_or_else(|| format!("missing current pooled field `{}`", field.name))?
                .clone(),
        );
    }
    for derived in &entity.derived_fields {
        scoped.insert(
            derived.name.clone(),
            slot_curr
                .get(&pool_slot_field_key(&entity.name, slot, &derived.name))
                .ok_or_else(|| format!("missing current pooled derived field `{}`", derived.name))?
                .clone(),
        );
    }
    Ok(scoped)
}

fn pooled_target_var_type(entity: &IREntity, name: &str) -> Option<IRType> {
    entity
        .fields
        .iter()
        .find(|field| field.name == name)
        .map(|field| field.ty.clone())
        .or_else(|| {
            entity
                .derived_fields
                .iter()
                .find(|field| field.name == name)
                .map(|field| field.ty.clone())
        })
}

fn encode_pooled_ops_match_for_target(
    tm: &Cvc5Tm,
    scrutinee: &crate::ir::types::IRActionMatchScrutinee,
    arms: &[crate::ir::types::IRActionMatchArm],
    target: PooledTargetSlot<'_>,
    ctx: PooledNestedOpsCtx<'_>,
) -> Result<Cvc5Term, String> {
    let target_entity = target.entity;
    let target_slot = target.slot;
    let vars = ctx.vars;
    let entity_bindings = ctx.entity_bindings;
    let slot_curr = ctx.frames.slot_curr;
    let enum_catalog = ctx.enum_catalog;
    let pool_ctx = ctx.pool_ctx;
    if arms.is_empty() {
        return Err("cvc5 SyGuS pooled nested action match requires at least one arm".to_owned());
    }
    let base_vars = pooled_target_scoped_vars(target_entity, target_slot, vars, slot_curr)?;
    let (scrut_term, scrut_ty) = match scrutinee {
        crate::ir::types::IRActionMatchScrutinee::Var { name } => {
            let term = base_vars.get(name).cloned().ok_or_else(|| {
                format!(
                    "cvc5 SyGuS pooled nested action match requires a bound scrutinee (`{name}`)"
                )
            })?;
            (term, pooled_target_var_type(target_entity, name))
        }
        crate::ir::types::IRActionMatchScrutinee::CrossCall { .. } => {
            return Err(
                "cvc5 SyGuS pooled nested action match does not support cross-call scrutinees yet"
                    .to_owned(),
            );
        }
    };

    let mut fallback = None;
    for arm in arms.iter().rev() {
        let mut arm_vars = base_vars.clone();
        bind_pattern_vars(
            tm,
            &arm.pattern,
            &scrut_term,
            scrut_ty.as_ref(),
            &mut arm_vars,
            enum_catalog,
        )?;
        let pat_cond = encode_pattern_cond(
            tm,
            &arm.pattern,
            &scrut_term,
            scrut_ty.as_ref(),
            enum_catalog,
        )?;
        let guard_cond = if let Some(guard) = &arm.guard {
            encode_pooled_expr(
                tm,
                guard,
                &arm_vars,
                entity_bindings,
                pool_ctx,
                enum_catalog,
            )?
        } else {
            tm.mk_boolean(true)
        };
        let arm_cond = mk_and(tm, &[pat_cond, guard_cond]);
        let arm_body = encode_pooled_ops_for_target(
            tm,
            &arm.body,
            target,
            PooledNestedOpsCtx {
                vars: &arm_vars,
                ..ctx
            },
        )?;
        fallback = Some(match fallback {
            None => {
                if arm.guard.is_none()
                    && matches!(
                        arm.pattern,
                        crate::ir::types::IRPattern::PWild
                            | crate::ir::types::IRPattern::PVar { .. }
                    )
                {
                    arm_body
                } else {
                    return Err(
                        "cvc5 SyGuS pooled nested action match requires a final wildcard or var fallback arm"
                            .to_owned(),
                    );
                }
            }
            Some(else_term) => {
                tm.mk_term(Cvc5Kind::CVC5_KIND_ITE, &[arm_cond, arm_body, else_term])
            }
        });
    }

    fallback
        .ok_or_else(|| "cvc5 SyGuS pooled nested action match required at least one arm".to_owned())
}

fn encode_pooled_transition_at_slot(
    tm: &Cvc5Tm,
    trans: &IRTransition,
    entity: &IREntity,
    slot: usize,
    apply_args: &[IRExpr],
    ctx: PooledSlotTransitionCtx<'_>,
) -> Result<Cvc5Term, String> {
    let vars = ctx.vars;
    let entity_bindings = ctx.entity_bindings;
    let active_next = ctx.frames.active_next;
    let slot_curr = ctx.frames.slot_curr;
    let slot_next = ctx.frames.slot_next;
    let enum_catalog = ctx.enum_catalog;
    let pool_ctx = ctx.pool_ctx;
    if trans.params.len() != apply_args.len() {
        return Err(format!(
            "cvc5 SyGuS pooled system safety expected {} args for transition `{}`, got {}",
            trans.params.len(),
            trans.name,
            apply_args.len()
        ));
    }
    let mut scoped = vars.clone();
    for field in &entity.fields {
        scoped.insert(
            field.name.clone(),
            slot_curr
                .get(&pool_slot_field_key(&entity.name, slot, &field.name))
                .ok_or_else(|| format!("missing current pooled field `{}`", field.name))?
                .clone(),
        );
    }
    for derived in &entity.derived_fields {
        scoped.insert(
            derived.name.clone(),
            slot_curr
                .get(&pool_slot_field_key(&entity.name, slot, &derived.name))
                .ok_or_else(|| format!("missing current pooled derived field `{}`", derived.name))?
                .clone(),
        );
    }
    for (param, arg) in trans.params.iter().zip(apply_args.iter()) {
        let arg_term =
            encode_pooled_expr(tm, arg, &scoped, entity_bindings, pool_ctx, enum_catalog)?;
        scoped.insert(param.name.clone(), arg_term);
    }

    let mut conjuncts = vec![encode_pooled_expr(
        tm,
        &trans.guard,
        &scoped,
        entity_bindings,
        pool_ctx,
        enum_catalog,
    )?];
    conjuncts.push(
        active_next
            .get(&entity.name)
            .and_then(|slots| slots.get(&slot))
            .ok_or_else(|| {
                format!(
                    "missing next active variable for {} slot {slot}",
                    entity.name
                )
            })?
            .clone(),
    );
    let update_map: HashMap<_, _> = trans
        .updates
        .iter()
        .map(|upd| (upd.field.as_str(), &upd.value))
        .collect();
    for field in &entity.fields {
        let rhs = if let Some(expr) = update_map.get(field.name.as_str()) {
            encode_pooled_expr(tm, expr, &scoped, entity_bindings, pool_ctx, enum_catalog)?
        } else {
            slot_curr
                .get(&pool_slot_field_key(&entity.name, slot, &field.name))
                .ok_or_else(|| format!("missing current pooled field `{}`", field.name))?
                .clone()
        };
        conjuncts.push(
            tm.mk_term(
                Cvc5Kind::CVC5_KIND_EQUAL,
                &[
                    slot_next
                        .get(&pool_slot_field_key(&entity.name, slot, &field.name))
                        .ok_or_else(|| format!("missing next pooled field `{}`", field.name))?
                        .clone(),
                    rhs,
                ],
            ),
        );
    }
    let mut next_scoped = HashMap::new();
    for field in &entity.fields {
        next_scoped.insert(
            field.name.clone(),
            slot_next
                .get(&pool_slot_field_key(&entity.name, slot, &field.name))
                .ok_or_else(|| format!("missing next pooled field `{}`", field.name))?
                .clone(),
        );
    }
    conjuncts.extend(encode_fsm_constraints(
        tm,
        &entity.fsm_decls,
        |field| update_map.contains_key(field),
        &scoped,
        &next_scoped,
        enum_catalog,
    )?);
    if let Some(postcondition) = &trans.postcondition {
        let mut post_scoped = scoped.clone();
        for field in &entity.fields {
            post_scoped.insert(
                field.name.clone(),
                slot_next
                    .get(&pool_slot_field_key(&entity.name, slot, &field.name))
                    .ok_or_else(|| format!("missing next pooled field `{}`", field.name))?
                    .clone(),
            );
        }
        for derived in &entity.derived_fields {
            post_scoped.insert(
                derived.name.clone(),
                slot_next
                    .get(&pool_slot_field_key(&entity.name, slot, &derived.name))
                    .ok_or_else(|| format!("missing next pooled derived field `{}`", derived.name))?
                    .clone(),
            );
        }
        let next_pool_ctx = PooledSyGuSCtx {
            slots_per_entity: pool_ctx.slots_per_entity,
            active_vars: active_next,
            slot_fields: slot_next,
            store_param_types: pool_ctx.store_param_types,
        };
        conjuncts.push(encode_pooled_expr(
            tm,
            postcondition,
            &post_scoped,
            entity_bindings,
            &next_pool_ctx,
            enum_catalog,
        )?);
    }

    Ok(mk_and(tm, &conjuncts))
}

fn exprstmt_target_field<'a>(expr: &'a IRExpr, target_var: &str) -> Result<&'a str, String> {
    let IRExpr::BinOp {
        op, left, right: _, ..
    } = expr
    else {
        return Err(
            "cvc5 SyGuS pooled system safety expects primed equality statements in nested ExprStmt"
                .to_owned(),
        );
    };
    if op != "OpEq" && op != "==" {
        return Err(
            "cvc5 SyGuS pooled system safety expects primed equality statements in nested ExprStmt"
                .to_owned(),
        );
    }
    let IRExpr::Prime { expr: primed, .. } = left.as_ref() else {
        return Err(
            "cvc5 SyGuS pooled system safety expects a primed lhs in nested ExprStmt".to_owned(),
        );
    };
    match primed.as_ref() {
        IRExpr::Field {
            expr: receiver,
            field,
            ..
        } => {
            let IRExpr::Var { name, .. } = receiver.as_ref() else {
                return Err(
                    "cvc5 SyGuS pooled system safety only supports field updates on the selected entity variable"
                        .to_owned(),
                );
            };
            if name != target_var {
                return Err(format!(
                    "cvc5 SyGuS pooled system safety only supports nested ExprStmt updates on selected target `{target_var}`"
                ));
            }
            Ok(field)
        }
        IRExpr::Var { name, .. } => Ok(name),
        _ => Err(
            "cvc5 SyGuS pooled system safety only supports primed entity fields in nested ExprStmt"
                .to_owned(),
        ),
    }
}

fn encode_pooled_entity_exprstmt_at_slot(
    tm: &Cvc5Tm,
    expr: &IRExpr,
    target: PooledTargetSlot<'_>,
    ctx: PooledSlotTransitionCtx<'_>,
) -> Result<Cvc5Term, String> {
    let target_var = target.var;
    let entity = target.entity;
    let slot = target.slot;
    let vars = ctx.vars;
    let entity_bindings = ctx.entity_bindings;
    let active_next = ctx.frames.active_next;
    let slot_curr = ctx.frames.slot_curr;
    let slot_next = ctx.frames.slot_next;
    let enum_catalog = ctx.enum_catalog;
    let pool_ctx = ctx.pool_ctx;
    let update_field = exprstmt_target_field(expr, target_var)?;
    if !entity.fields.iter().any(|field| field.name == update_field) {
        return Err(format!(
            "cvc5 SyGuS pooled system safety cannot update unknown field `{update_field}` on `{}`",
            entity.name
        ));
    }
    let IRExpr::BinOp { right, .. } = expr else {
        unreachable!("exprstmt_target_field checked nested ExprStmt shape");
    };

    let mut scoped = vars.clone();
    for field in &entity.fields {
        scoped.insert(
            field.name.clone(),
            slot_curr
                .get(&pool_slot_field_key(&entity.name, slot, &field.name))
                .ok_or_else(|| format!("missing current pooled field `{}`", field.name))?
                .clone(),
        );
    }
    for derived in &entity.derived_fields {
        scoped.insert(
            derived.name.clone(),
            slot_curr
                .get(&pool_slot_field_key(&entity.name, slot, &derived.name))
                .ok_or_else(|| format!("missing current pooled derived field `{}`", derived.name))?
                .clone(),
        );
    }

    let rhs = encode_pooled_expr(tm, right, &scoped, entity_bindings, pool_ctx, enum_catalog)?;
    let mut conjuncts = vec![active_next
        .get(&entity.name)
        .and_then(|slots| slots.get(&slot))
        .ok_or_else(|| {
            format!(
                "missing next active variable for {} slot {slot}",
                entity.name
            )
        })?
        .clone()];
    let mut next_scoped = HashMap::new();
    for field in &entity.fields {
        let next = slot_next
            .get(&pool_slot_field_key(&entity.name, slot, &field.name))
            .ok_or_else(|| format!("missing next pooled field `{}`", field.name))?
            .clone();
        let value = if field.name == update_field {
            rhs.clone()
        } else {
            slot_curr
                .get(&pool_slot_field_key(&entity.name, slot, &field.name))
                .ok_or_else(|| format!("missing current pooled field `{}`", field.name))?
                .clone()
        };
        conjuncts.push(tm.mk_term(Cvc5Kind::CVC5_KIND_EQUAL, &[next.clone(), value]));
        next_scoped.insert(field.name.clone(), next);
    }
    conjuncts.extend(encode_fsm_constraints(
        tm,
        &entity.fsm_decls,
        |field| field == update_field,
        &scoped,
        &next_scoped,
        enum_catalog,
    )?);
    Ok(mk_and(tm, &conjuncts))
}

fn encode_pooled_create_action(
    tm: &Cvc5Tm,
    create_entity: &str,
    create_fields: &[IRCreateField],
    target: PooledEntityPoolTarget<'_>,
    ctx: PooledActionCtx<'_>,
) -> Result<Cvc5Term, String> {
    let entity = target.entity;
    let n_slots = target.n_slots;
    let vars = ctx.vars;
    let active_curr = ctx.frames.active_curr;
    let active_next = ctx.frames.active_next;
    let slot_curr = ctx.frames.slot_curr;
    let slot_next = ctx.frames.slot_next;
    let enum_catalog = ctx.enum_catalog;
    if create_entity != entity.name {
        return Err(format!(
            "cvc5 SyGuS pooled system safety only supports creates for `{}`",
            entity.name
        ));
    }

    let create_map: HashMap<_, _> = create_fields
        .iter()
        .map(|field| (field.name.as_str(), &field.value))
        .collect();
    let local_slots_per_entity = HashMap::from([(entity.name.clone(), n_slots)]);
    let local_store_param_types = system_store_param_types(ctx.system);
    let pre_ctx = PooledSyGuSCtx {
        slots_per_entity: &local_slots_per_entity,
        active_vars: active_curr,
        slot_fields: slot_curr,
        store_param_types: &local_store_param_types,
    };
    let mut branches = Vec::new();
    for slot in 0..n_slots {
        let mut conjuncts = vec![tm.mk_term(
            Cvc5Kind::CVC5_KIND_NOT,
            &[active_curr
                .get(&entity.name)
                .and_then(|slots| slots.get(&slot))
                .ok_or_else(|| {
                    format!(
                        "missing current active variable for {} slot {slot}",
                        entity.name
                    )
                })?
                .clone()],
        )];
        conjuncts.push(
            active_next
                .get(&entity.name)
                .and_then(|slots| slots.get(&slot))
                .ok_or_else(|| {
                    format!(
                        "missing next active variable for {} slot {slot}",
                        entity.name
                    )
                })?
                .clone(),
        );
        for field in &entity.fields {
            let rhs = if let Some(expr) = create_map.get(field.name.as_str()) {
                encode_pooled_expr(tm, expr, vars, &HashMap::new(), &pre_ctx, enum_catalog)?
            } else {
                encode_pooled_expr(
                    tm,
                    field
                        .default
                        .as_ref()
                        .expect("checked deterministic default"),
                    vars,
                    &HashMap::new(),
                    &pre_ctx,
                    enum_catalog,
                )?
            };
            conjuncts.push(
                tm.mk_term(
                    Cvc5Kind::CVC5_KIND_EQUAL,
                    &[
                        slot_next
                            .get(&pool_slot_field_key(&entity.name, slot, &field.name))
                            .ok_or_else(|| format!("missing next pooled field `{}`", field.name))?
                            .clone(),
                        rhs,
                    ],
                ),
            );
        }
        conjuncts.extend(frame_other_pooled_slots(
            tm,
            entity,
            slot,
            PooledFrameVars {
                active_curr,
                active_next,
                slot_curr,
                slot_next,
            },
            n_slots,
        )?);
        branches.push(mk_and(tm, &conjuncts));
    }
    Ok(mk_or(tm, &branches))
}

fn encode_pooled_choose_action(
    tm: &Cvc5Tm,
    var: &str,
    choose_entity: &str,
    filter: &IRExpr,
    ops: &[IRAction],
    target: PooledEntityPoolTarget<'_>,
    ctx: PooledActionCtx<'_>,
) -> Result<Cvc5Term, String> {
    let entity = target.entity;
    let n_slots = target.n_slots;
    let vars = ctx.vars;
    let next_vars = ctx.next_vars;
    let entity_bindings = ctx.entity_bindings;
    let active_curr = ctx.frames.active_curr;
    let active_next = ctx.frames.active_next;
    let slot_curr = ctx.frames.slot_curr;
    let slot_next = ctx.frames.slot_next;
    let enum_catalog = ctx.enum_catalog;
    if choose_entity != entity.name {
        return Err(format!(
            "cvc5 SyGuS pooled system safety only supports chooses over `{}`",
            entity.name
        ));
    }
    if !ctx.system.fields.is_empty() {
        // system fields remain framed for this slice
    }
    let store_param_types = system_store_param_types(ctx.system);
    let pool_ctx = PooledSyGuSCtx {
        slots_per_entity: ctx.slots_per_entity,
        active_vars: active_curr,
        slot_fields: slot_curr,
        store_param_types: &store_param_types,
    };
    let mut branches = Vec::new();
    for slot in 0..n_slots {
        let mut bindings = entity_bindings.clone();
        bindings.insert(var.to_owned(), (entity.name.clone(), slot));
        let scoped_vars = pooled_target_scoped_vars(entity, slot, vars, slot_curr)?;
        let mut conjuncts = vec![
            active_curr
                .get(&entity.name)
                .and_then(|slots| slots.get(&slot))
                .ok_or_else(|| {
                    format!(
                        "missing current active variable for {} slot {slot}",
                        entity.name
                    )
                })?
                .clone(),
            encode_pooled_expr(tm, filter, &scoped_vars, &bindings, &pool_ctx, enum_catalog)?,
            encode_pooled_ops_for_target(
                tm,
                ops,
                PooledTargetSlot { var, entity, slot },
                PooledNestedOpsCtx {
                    systems_by_name: ctx.systems_by_name,
                    entities_by_name: ctx.entities_by_name,
                    slots_per_entity: ctx.slots_per_entity,
                    vars: &scoped_vars,
                    next_vars,
                    entity_bindings: &bindings,
                    frames: PooledFrameVars {
                        active_curr,
                        active_next,
                        slot_curr,
                        slot_next,
                    },
                    enum_catalog,
                    pool_ctx: &pool_ctx,
                    call_stack: ctx.call_stack,
                },
            )?,
        ];
        conjuncts.extend(frame_other_pooled_slots(
            tm,
            entity,
            slot,
            PooledFrameVars {
                active_curr,
                active_next,
                slot_curr,
                slot_next,
            },
            n_slots,
        )?);
        branches.push(mk_and(tm, &conjuncts));
    }
    Ok(mk_or(tm, &branches))
}

fn encode_pooled_forall_action(
    tm: &Cvc5Tm,
    var: &str,
    forall_entity: &str,
    ops: &[IRAction],
    target: PooledEntityPoolTarget<'_>,
    ctx: PooledActionCtx<'_>,
) -> Result<Cvc5Term, String> {
    let entity = target.entity;
    let n_slots = target.n_slots;
    let vars = ctx.vars;
    let next_vars = ctx.next_vars;
    let entity_bindings = ctx.entity_bindings;
    let active_curr = ctx.frames.active_curr;
    let active_next = ctx.frames.active_next;
    let slot_curr = ctx.frames.slot_curr;
    let slot_next = ctx.frames.slot_next;
    let enum_catalog = ctx.enum_catalog;
    if forall_entity != entity.name {
        return Err(format!(
            "cvc5 SyGuS pooled system safety only supports forall over `{}`",
            entity.name
        ));
    }
    let store_param_types = system_store_param_types(ctx.system);
    let pool_ctx = PooledSyGuSCtx {
        slots_per_entity: ctx.slots_per_entity,
        active_vars: active_curr,
        slot_fields: slot_curr,
        store_param_types: &store_param_types,
    };
    let mut conjuncts = Vec::new();
    for slot in 0..n_slots {
        let active = active_curr
            .get(&entity.name)
            .and_then(|slots| slots.get(&slot))
            .ok_or_else(|| {
                format!(
                    "missing current active variable for {} slot {slot}",
                    entity.name
                )
            })?
            .clone();
        let mut bindings = entity_bindings.clone();
        bindings.insert(var.to_owned(), (entity.name.clone(), slot));
        let active_branch = mk_and(
            tm,
            &[
                active.clone(),
                encode_pooled_ops_for_target(
                    tm,
                    ops,
                    PooledTargetSlot { var, entity, slot },
                    PooledNestedOpsCtx {
                        systems_by_name: ctx.systems_by_name,
                        entities_by_name: ctx.entities_by_name,
                        slots_per_entity: ctx.slots_per_entity,
                        vars,
                        next_vars,
                        entity_bindings: &bindings,
                        frames: PooledFrameVars {
                            active_curr,
                            active_next,
                            slot_curr,
                            slot_next,
                        },
                        enum_catalog,
                        pool_ctx: &pool_ctx,
                        call_stack: ctx.call_stack,
                    },
                )?,
            ],
        );
        let inactive_branch = mk_and(
            tm,
            &[
                tm.mk_term(Cvc5Kind::CVC5_KIND_NOT, &[active]),
                frame_pooled_slot(
                    tm,
                    entity,
                    slot,
                    active_curr,
                    active_next,
                    slot_curr,
                    slot_next,
                )?,
            ],
        );
        conjuncts.push(mk_or(tm, &[active_branch, inactive_branch]));
    }
    Ok(mk_and(tm, &conjuncts))
}

fn encode_pooled_system_exprstmt_update(
    tm: &Cvc5Tm,
    expr: &IRExpr,
    system: &IRSystem,
    vars: &HashMap<String, Cvc5Term>,
    next_vars: &HashMap<String, Cvc5Term>,
    pool_ctx: &PooledSyGuSCtx<'_>,
    enum_catalog: &EnumCatalog,
) -> Result<(String, Cvc5Term), String> {
    let IRExpr::BinOp {
        op, left, right, ..
    } = expr
    else {
        return Err(format!(
            "cvc5 SyGuS pooled system safety expects primed equality statements (`{}`)",
            system.name
        ));
    };
    if op != "OpEq" && op != "==" {
        return Err(format!(
            "cvc5 SyGuS pooled system safety expects primed equality statements (`{}`)",
            system.name
        ));
    }
    let IRExpr::Prime { expr: primed, .. } = left.as_ref() else {
        return Err(format!(
            "cvc5 SyGuS pooled system safety expects a primed lhs in ExprStmt (`{}`)",
            system.name
        ));
    };
    let IRExpr::Var { name, .. } = primed.as_ref() else {
        return Err(format!(
            "cvc5 SyGuS pooled system safety only supports primed system field vars on the lhs (`{}`)",
            system.name
        ));
    };
    if !system.fields.iter().any(|field| field.name == *name) {
        return Err(format!(
            "cvc5 SyGuS pooled system safety can only update root system fields in `{}` (`{name}`)",
            system.name
        ));
    }
    let next = next_vars
        .get(name)
        .ok_or_else(|| format!("missing next system field `{name}` for `{}`", system.name))?;
    let rhs = encode_pooled_expr(tm, right, vars, &HashMap::new(), pool_ctx, enum_catalog)?;
    Ok((
        name.clone(),
        tm.mk_term(Cvc5Kind::CVC5_KIND_EQUAL, &[next.clone(), rhs]),
    ))
}

fn encode_pooled_system_exprstmt_formula(
    tm: &Cvc5Tm,
    expr: &IRExpr,
    ctx: PooledActionCtx<'_>,
    pool_ctx: &PooledSyGuSCtx<'_>,
) -> Result<Cvc5Term, String> {
    let system = ctx.system;
    let curr_vars = ctx.vars;
    let next_vars = ctx.next_vars;
    let entity_bindings = ctx.entity_bindings;
    let active_curr = ctx.frames.active_curr;
    let active_next = ctx.frames.active_next;
    let slot_curr = ctx.frames.slot_curr;
    let slot_next = ctx.frames.slot_next;
    let enum_catalog = ctx.enum_catalog;
    if let Some((target_var, entity_name, slot)) =
        exprstmt_bound_entity_target(expr, entity_bindings)?
    {
        let entity = ctx
            .entities_by_name
            .get(&entity_name)
            .ok_or_else(|| format!("unknown pooled entity `{entity_name}`"))?;
        let mut conjuncts = vec![encode_pooled_entity_exprstmt_at_slot(
            tm,
            expr,
            PooledTargetSlot {
                var: &target_var,
                entity,
                slot,
            },
            PooledSlotTransitionCtx {
                vars: curr_vars,
                entity_bindings,
                frames: PooledFrameVars {
                    active_curr,
                    active_next,
                    slot_curr,
                    slot_next,
                },
                enum_catalog,
                pool_ctx,
            },
        )?];
        conjuncts.extend(frame_all_system_fields(
            tm,
            ctx.systems_by_name,
            curr_vars,
            next_vars,
        )?);
        conjuncts.extend(frame_other_pooled_entities(
            tm,
            ctx.entities_by_name,
            ctx.slots_per_entity,
            &entity_name,
            PooledFrameVars {
                active_curr,
                active_next,
                slot_curr,
                slot_next,
            },
        )?);
        conjuncts.extend(frame_other_pooled_slots(
            tm,
            entity,
            slot,
            PooledFrameVars {
                active_curr,
                active_next,
                slot_curr,
                slot_next,
            },
            *ctx.slots_per_entity
                .get(&entity_name)
                .ok_or_else(|| format!("missing slot scope for `{entity_name}`"))?,
        )?);
        return Ok(mk_and(tm, &conjuncts));
    }
    let (field_name, update) = encode_pooled_system_exprstmt_update(
        tm,
        expr,
        system,
        curr_vars,
        next_vars,
        pool_ctx,
        enum_catalog,
    )?;
    let touched = HashSet::from([field_name]);
    let mut conjuncts = vec![update];
    conjuncts.extend(frame_system_fields_except(
        tm,
        ctx.systems_by_name,
        curr_vars,
        next_vars,
        &touched,
    )?);
    conjuncts.extend(encode_fsm_constraints(
        tm,
        &system.fsm_decls,
        |field| touched.contains(field),
        curr_vars,
        next_vars,
        enum_catalog,
    )?);
    conjuncts.extend(frame_all_pooled_entities(
        tm,
        ctx.entities_by_name,
        ctx.slots_per_entity,
        active_curr,
        active_next,
        slot_curr,
        slot_next,
    )?);
    Ok(mk_and(tm, &conjuncts))
}

fn exprstmt_bound_entity_target(
    expr: &IRExpr,
    entity_bindings: &PooledEntityBindings,
) -> Result<Option<(String, String, usize)>, String> {
    let IRExpr::BinOp { left, .. } = expr else {
        return Ok(None);
    };
    let IRExpr::Prime { expr: primed, .. } = left.as_ref() else {
        return Ok(None);
    };
    let IRExpr::Field { expr: receiver, .. } = primed.as_ref() else {
        return Ok(None);
    };
    let IRExpr::Var { name, .. } = receiver.as_ref() else {
        return Ok(None);
    };
    Ok(entity_bindings
        .get(name)
        .map(|(entity, slot)| (name.clone(), entity.clone(), *slot)))
}

fn encode_pooled_system_action(
    tm: &Cvc5Tm,
    action: &IRAction,
    ctx: PooledActionCtx<'_>,
    local_bindings: &PooledLocalBindings,
) -> Result<PooledActionResult, String> {
    let mut merged_vars = ctx.vars.clone();
    merged_vars.extend(
        local_bindings
            .iter()
            .map(|(name, binding)| (name.clone(), binding.term.clone())),
    );
    let merged_ctx = PooledActionCtx {
        vars: &merged_vars,
        ..ctx
    };
    match action {
        IRAction::ExprStmt { expr } => {
            let store_param_types = system_store_param_types(ctx.system);
            let pool_ctx = PooledSyGuSCtx {
                slots_per_entity: ctx.slots_per_entity,
                active_vars: ctx.frames.active_curr,
                slot_fields: ctx.frames.slot_curr,
                store_param_types: &store_param_types,
            };
            Ok(PooledActionResult {
                formula: encode_pooled_system_exprstmt_formula(tm, expr, merged_ctx, &pool_ctx)?,
                locals: local_bindings.clone(),
            })
        }
        IRAction::Create {
            entity: create_entity,
            fields,
        } => {
            let create_target = ctx
                .entities_by_name
                .get(create_entity)
                .ok_or_else(|| format!("unknown pooled entity `{create_entity}`"))?;
            let n_slots = *ctx
                .slots_per_entity
                .get(create_entity)
                .ok_or_else(|| format!("missing slot scope for `{create_entity}`"))?;
            let mut conjuncts_local = vec![encode_pooled_create_action(
                tm,
                create_entity,
                fields,
                PooledEntityPoolTarget {
                    entity: create_target,
                    n_slots,
                },
                ctx,
            )?];
            conjuncts_local.extend(frame_other_pooled_entities(
                tm,
                ctx.entities_by_name,
                ctx.slots_per_entity,
                create_entity,
                ctx.frames,
            )?);
            Ok(PooledActionResult {
                formula: mk_and(tm, &conjuncts_local),
                locals: local_bindings.clone(),
            })
        }
        IRAction::Choose {
            var,
            entity: choose_entity,
            filter,
            ops,
        } => {
            let choose_target = ctx
                .entities_by_name
                .get(choose_entity)
                .ok_or_else(|| format!("unknown pooled entity `{choose_entity}`"))?;
            let n_slots = *ctx
                .slots_per_entity
                .get(choose_entity)
                .ok_or_else(|| format!("missing slot scope for `{choose_entity}`"))?;
            let mut conjuncts_local = vec![encode_pooled_choose_action(
                tm,
                var,
                choose_entity,
                filter,
                ops,
                PooledEntityPoolTarget {
                    entity: choose_target,
                    n_slots,
                },
                merged_ctx,
            )?];
            conjuncts_local.extend(frame_other_pooled_entities(
                tm,
                ctx.entities_by_name,
                ctx.slots_per_entity,
                choose_entity,
                ctx.frames,
            )?);
            Ok(PooledActionResult {
                formula: mk_and(tm, &conjuncts_local),
                locals: local_bindings.clone(),
            })
        }
        IRAction::ForAll {
            var,
            entity: forall_entity,
            ops,
        } => {
            let forall_target = ctx
                .entities_by_name
                .get(forall_entity)
                .ok_or_else(|| format!("unknown pooled entity `{forall_entity}`"))?;
            let n_slots = *ctx
                .slots_per_entity
                .get(forall_entity)
                .ok_or_else(|| format!("missing slot scope for `{forall_entity}`"))?;
            let mut conjuncts_local = vec![encode_pooled_forall_action(
                tm,
                var,
                forall_entity,
                ops,
                PooledEntityPoolTarget {
                    entity: forall_target,
                    n_slots,
                },
                merged_ctx,
            )?];
            conjuncts_local.extend(frame_other_pooled_entities(
                tm,
                ctx.entities_by_name,
                ctx.slots_per_entity,
                forall_entity,
                ctx.frames,
            )?);
            Ok(PooledActionResult {
                formula: mk_and(tm, &conjuncts_local),
                locals: local_bindings.clone(),
            })
        }
        IRAction::CrossCall {
            system: target_system_name,
            command,
            args,
        } => encode_pooled_crosscall_capture(
            tm,
            target_system_name,
            command,
            args,
            PooledCrossCallCtx {
                systems_by_name: ctx.systems_by_name,
                entities_by_name: ctx.entities_by_name,
                slots_per_entity: ctx.slots_per_entity,
                curr_vars: &merged_vars,
                next_vars: ctx.next_vars,
                entity_bindings: ctx.entity_bindings,
                frames: ctx.frames,
                enum_catalog: ctx.enum_catalog,
                call_stack: ctx.call_stack,
            },
        )
        .map(|capture| PooledActionResult {
            formula: capture.formula,
            locals: local_bindings.clone(),
        }),
        IRAction::LetCrossCall {
            name,
            system: target_system_name,
            command,
            args,
        } => {
            let capture = encode_pooled_crosscall_capture(
                tm,
                target_system_name,
                command,
                args,
                PooledCrossCallCtx {
                    systems_by_name: ctx.systems_by_name,
                    entities_by_name: ctx.entities_by_name,
                    slots_per_entity: ctx.slots_per_entity,
                    curr_vars: &merged_vars,
                    next_vars: ctx.next_vars,
                    entity_bindings: ctx.entity_bindings,
                    frames: ctx.frames,
                    enum_catalog: ctx.enum_catalog,
                    call_stack: ctx.call_stack,
                },
            )?;
            let ret = capture.return_value.ok_or_else(|| {
                format!(
                    "cvc5 SyGuS pooled LetCrossCall requires `{target_system_name}::{command}` to return a value"
                )
            })?;
            let mut locals = local_bindings.clone();
            locals.insert(
                name.clone(),
                PooledLocalBinding {
                    term: ret,
                    ty: capture.return_type,
                },
            );
            Ok(PooledActionResult {
                formula: capture.formula,
                locals,
            })
        }
        IRAction::Match { scrutinee, arms } => encode_pooled_action_match(
            tm,
            scrutinee,
            arms,
            PooledActionCtx {
                vars: &merged_vars,
                ..ctx
            },
            local_bindings,
        )
        .map(|formula| PooledActionResult {
            formula,
            locals: local_bindings.clone(),
        }),
        other => Err(format!(
            "cvc5 SyGuS pooled system safety does not support action `{other:?}` yet"
        )),
    }
}

fn encode_pooled_system_step(
    tm: &Cvc5Tm,
    step: &IRSystemAction,
    ctx: PooledStepCtx<'_>,
) -> Result<Cvc5Term, String> {
    let param_envs = enumerate_pooled_param_envs(
        tm,
        step,
        &step.params,
        ctx.slots_per_entity,
        ctx.enum_catalog,
    )?;
    encode_pooled_system_step_with_param_envs(tm, step, ctx, param_envs)
}

fn encode_pooled_system_step_with_bound_params(
    tm: &Cvc5Tm,
    step: &IRSystemAction,
    param_env: PooledParamEnv,
    ctx: PooledStepCtx<'_>,
) -> Result<Cvc5Term, String> {
    encode_pooled_system_step_with_param_envs(tm, step, ctx, vec![param_env])
}

fn encode_pooled_system_step_with_param_envs(
    tm: &Cvc5Tm,
    step: &IRSystemAction,
    ctx: PooledStepCtx<'_>,
    param_envs: Vec<PooledParamEnv>,
) -> Result<Cvc5Term, String> {
    let system = ctx.system;
    let systems_by_name = ctx.systems_by_name;
    let entities_by_name = ctx.entities_by_name;
    let slots_per_entity = ctx.slots_per_entity;
    let curr_vars = ctx.curr_vars;
    let next_vars = ctx.next_vars;
    let active_curr = ctx.frames.active_curr;
    let active_next = ctx.frames.active_next;
    let slot_curr = ctx.frames.slot_curr;
    let slot_next = ctx.frames.slot_next;
    let enum_catalog = ctx.enum_catalog;
    let call_stack = ctx.call_stack;
    let mut branches = Vec::new();
    for param_env in param_envs {
        let mut vars = curr_vars.clone();
        vars.extend(param_env.terms.clone());
        let store_param_types = system_store_param_types(system);
        let pool_ctx = PooledSyGuSCtx {
            slots_per_entity,
            active_vars: active_curr,
            slot_fields: slot_curr,
            store_param_types: &store_param_types,
        };
        let mut conjuncts = vec![encode_pooled_expr(
            tm,
            &step.guard,
            &vars,
            &param_env.entity_bindings,
            &pool_ctx,
            enum_catalog,
        )?];
        conjuncts.extend(pooled_entity_binding_active_constraints(
            active_curr,
            &param_env.entity_bindings,
        )?);
        let body_term = if step.body.is_empty() {
            conjuncts.extend(frame_all_system_fields(
                tm,
                systems_by_name,
                curr_vars,
                next_vars,
            )?);
            mk_and(
                tm,
                &frame_all_pooled_entities(
                    tm,
                    entities_by_name,
                    slots_per_entity,
                    active_curr,
                    active_next,
                    slot_curr,
                    slot_next,
                )?,
            )
        } else if step.body.len() == 1 {
            if let IRAction::ExprStmt { expr } = &step.body[0] {
                encode_pooled_system_exprstmt_formula(
                    tm,
                    expr,
                    PooledActionCtx {
                        system,
                        systems_by_name,
                        entities_by_name,
                        slots_per_entity,
                        vars: &vars,
                        next_vars,
                        entity_bindings: &param_env.entity_bindings,
                        frames: PooledFrameVars {
                            active_curr,
                            active_next,
                            slot_curr,
                            slot_next,
                        },
                        enum_catalog,
                        call_stack,
                    },
                    &pool_ctx,
                )?
            } else {
                conjuncts.extend(frame_all_system_fields(
                    tm,
                    systems_by_name,
                    curr_vars,
                    next_vars,
                )?);
                encode_pooled_system_action(
                    tm,
                    &step.body[0],
                    PooledActionCtx {
                        system,
                        systems_by_name,
                        entities_by_name,
                        slots_per_entity,
                        vars: &vars,
                        next_vars,
                        entity_bindings: &param_env.entity_bindings,
                        frames: PooledFrameVars {
                            active_curr,
                            active_next,
                            slot_curr,
                            slot_next,
                        },
                        enum_catalog,
                        call_stack,
                    },
                    &HashMap::new(),
                )?
                .formula
            }
        } else {
            let param_only_vars: HashMap<_, _> = vars
                .iter()
                .filter(|(name, _)| !curr_vars.contains_key(*name))
                .map(|(name, term)| (name.clone(), term.clone()))
                .collect();
            let param_entity_bindings = param_env.entity_bindings.clone();
            let mut intermediate_active = Vec::new();
            let mut intermediate_slots = Vec::new();
            let mut intermediate_system_vars = Vec::new();
            let mut bound = Vec::new();
            for stage in 0..(step.body.len() - 1) {
                let mut system_vars = HashMap::new();
                for system in systems_by_name.values() {
                    for field in &system.fields {
                        let sort = sort_for_field(tm, field, enum_catalog)?;
                        let name = format!(
                            "__abide_sygus_{}_{}_inter{}",
                            system.name, field.name, stage
                        );
                        let term = tm.mk_var(sort, &name);
                        bound.push(term.clone());
                        system_vars.insert(field.name.clone(), term);
                    }
                }
                for system in systems_by_name.values() {
                    extend_with_derived_fields(
                        tm,
                        &mut system_vars,
                        &system.derived_fields,
                        enum_catalog,
                    )?;
                }
                let mut active_map = HashMap::new();
                let mut slot_map = HashMap::new();
                for (entity_name, n_slots) in slots_per_entity {
                    let entity = entities_by_name
                        .get(entity_name)
                        .ok_or_else(|| format!("missing pooled entity `{entity_name}`"))?;
                    let mut per_slot = HashMap::new();
                    for slot in 0..*n_slots {
                        let active_name = format!(
                            "__abide_sygus_{}_slot{}_active_inter{}",
                            entity_name, slot, stage
                        );
                        let active_term = tm.mk_var(tm.boolean_sort(), &active_name);
                        bound.push(active_term.clone());
                        per_slot.insert(slot, active_term);
                        for field in &entity.fields {
                            let sort = sort_for_field(tm, field, enum_catalog)?;
                            let name = format!(
                                "__abide_sygus_{}_slot{}_{}_inter{}",
                                entity_name, slot, field.name, stage
                            );
                            let term = tm.mk_var(sort, &name);
                            bound.push(term.clone());
                            slot_map
                                .insert(pool_slot_field_key(entity_name, slot, &field.name), term);
                        }
                    }
                    active_map.insert(entity_name.clone(), per_slot);
                }
                intermediate_system_vars.push(system_vars);
                intermediate_active.push(active_map);
                intermediate_slots.push(slot_map);
            }
            let mut action_terms = Vec::new();
            let mut locals: PooledLocalBindings = HashMap::new();
            for (idx, action) in step.body.iter().enumerate() {
                let stage_active_curr = if idx == 0 {
                    active_curr
                } else {
                    &intermediate_active[idx - 1]
                };
                let stage_slot_curr = if idx == 0 {
                    slot_curr
                } else {
                    &intermediate_slots[idx - 1]
                };
                let stage_active_next = if idx + 1 == step.body.len() {
                    active_next
                } else {
                    &intermediate_active[idx]
                };
                let stage_slot_next = if idx + 1 == step.body.len() {
                    slot_next
                } else {
                    &intermediate_slots[idx]
                };
                let stage_system_curr = if idx == 0 {
                    curr_vars
                } else {
                    &intermediate_system_vars[idx - 1]
                };
                let stage_system_next = if idx + 1 == step.body.len() {
                    next_vars
                } else {
                    &intermediate_system_vars[idx]
                };
                let mut stage_vars = stage_system_curr.clone();
                stage_vars.extend(param_only_vars.clone());
                match action {
                    IRAction::ExprStmt { expr } => {
                        stage_vars.extend(
                            locals
                                .iter()
                                .map(|(name, binding)| (name.clone(), binding.term.clone())),
                        );
                        let stage_store_param_types = system_store_param_types(system);
                        let stage_pool_ctx = PooledSyGuSCtx {
                            slots_per_entity,
                            active_vars: stage_active_curr,
                            slot_fields: stage_slot_curr,
                            store_param_types: &stage_store_param_types,
                        };
                        action_terms.push(encode_pooled_system_exprstmt_formula(
                            tm,
                            expr,
                            PooledActionCtx {
                                system,
                                systems_by_name,
                                entities_by_name,
                                slots_per_entity,
                                vars: &stage_vars,
                                next_vars: stage_system_next,
                                entity_bindings: &param_entity_bindings,
                                frames: PooledFrameVars {
                                    active_curr: stage_active_curr,
                                    active_next: stage_active_next,
                                    slot_curr: stage_slot_curr,
                                    slot_next: stage_slot_next,
                                },
                                enum_catalog,
                                call_stack,
                            },
                            &stage_pool_ctx,
                        )?);
                    }
                    _ => {
                        let action_result = encode_pooled_system_action(
                            tm,
                            action,
                            PooledActionCtx {
                                system,
                                systems_by_name,
                                entities_by_name,
                                slots_per_entity,
                                vars: &stage_vars,
                                next_vars: stage_system_next,
                                entity_bindings: &param_entity_bindings,
                                frames: PooledFrameVars {
                                    active_curr: stage_active_curr,
                                    active_next: stage_active_next,
                                    slot_curr: stage_slot_curr,
                                    slot_next: stage_slot_next,
                                },
                                enum_catalog,
                                call_stack,
                            },
                            &locals,
                        )?;
                        let mut framed = frame_all_system_fields(
                            tm,
                            systems_by_name,
                            &stage_vars,
                            stage_system_next,
                        )?;
                        framed.push(action_result.formula);
                        action_terms.push(mk_and(tm, &framed));
                        locals = action_result.locals;
                    }
                }
            }
            mk_exists(tm, &bound, mk_and(tm, &action_terms))
        };
        conjuncts.push(body_term);
        branches.push(mk_and(tm, &conjuncts));
    }
    Ok(mk_or(tm, &branches))
}

fn encode_pooled_system_action_sequence(
    tm: &Cvc5Tm,
    actions: &[IRAction],
    ctx: PooledActionCtx<'_>,
    local_bindings: &PooledLocalBindings,
) -> Result<PooledActionResult, String> {
    let system = ctx.system;
    let systems_by_name = ctx.systems_by_name;
    let entities_by_name = ctx.entities_by_name;
    let slots_per_entity = ctx.slots_per_entity;
    let curr_vars = ctx.vars;
    let next_vars = ctx.next_vars;
    let active_curr = ctx.frames.active_curr;
    let active_next = ctx.frames.active_next;
    let slot_curr = ctx.frames.slot_curr;
    let slot_next = ctx.frames.slot_next;
    let enum_catalog = ctx.enum_catalog;
    let call_stack = ctx.call_stack;
    if actions.is_empty() {
        let mut framed = frame_all_system_fields(tm, systems_by_name, curr_vars, next_vars)?;
        framed.extend(frame_all_pooled_entities(
            tm,
            entities_by_name,
            slots_per_entity,
            active_curr,
            active_next,
            slot_curr,
            slot_next,
        )?);
        return Ok(PooledActionResult {
            formula: mk_and(tm, &framed),
            locals: local_bindings.clone(),
        });
    }
    if actions.len() == 1 {
        return encode_pooled_system_action(tm, &actions[0], ctx, local_bindings);
    }

    let non_state_vars: HashMap<_, _> = curr_vars
        .iter()
        .filter(|(name, _)| !next_vars.contains_key(*name))
        .map(|(name, term)| (name.clone(), term.clone()))
        .collect();
    let mut intermediate_active = Vec::new();
    let mut intermediate_slots = Vec::new();
    let mut intermediate_system_vars = Vec::new();
    let mut bound = Vec::new();
    for stage in 0..(actions.len() - 1) {
        let mut system_vars = HashMap::new();
        for system in systems_by_name.values() {
            for field in &system.fields {
                let sort = sort_for_field(tm, field, enum_catalog)?;
                let name = format!(
                    "__abide_sygus_{}_{}_arm_inter{}",
                    system.name, field.name, stage
                );
                let term = tm.mk_var(sort, &name);
                bound.push(term.clone());
                system_vars.insert(field.name.clone(), term);
            }
        }
        for system in systems_by_name.values() {
            extend_with_derived_fields(tm, &mut system_vars, &system.derived_fields, enum_catalog)?;
        }

        let mut active_map = HashMap::new();
        let mut slot_map = HashMap::new();
        for (entity_name, n_slots) in slots_per_entity {
            let entity = entities_by_name
                .get(entity_name)
                .ok_or_else(|| format!("missing pooled entity `{entity_name}`"))?;
            let mut per_slot = HashMap::new();
            for slot in 0..*n_slots {
                let active_name = format!(
                    "__abide_sygus_{}_slot{}_active_arm_inter{}",
                    entity_name, slot, stage
                );
                let active_term = tm.mk_var(tm.boolean_sort(), &active_name);
                bound.push(active_term.clone());
                per_slot.insert(slot, active_term);
                for field in &entity.fields {
                    let sort = sort_for_field(tm, field, enum_catalog)?;
                    let name = format!(
                        "__abide_sygus_{}_slot{}_{}_arm_inter{}",
                        entity_name, slot, field.name, stage
                    );
                    let term = tm.mk_var(sort, &name);
                    bound.push(term.clone());
                    slot_map.insert(pool_slot_field_key(entity_name, slot, &field.name), term);
                }
            }
            active_map.insert(entity_name.clone(), per_slot);
        }
        intermediate_system_vars.push(system_vars);
        intermediate_active.push(active_map);
        intermediate_slots.push(slot_map);
    }

    let mut action_terms = Vec::new();
    let mut locals = local_bindings.clone();
    for (idx, action) in actions.iter().enumerate() {
        let stage_active_curr = if idx == 0 {
            active_curr
        } else {
            &intermediate_active[idx - 1]
        };
        let stage_slot_curr = if idx == 0 {
            slot_curr
        } else {
            &intermediate_slots[idx - 1]
        };
        let stage_active_next = if idx + 1 == actions.len() {
            active_next
        } else {
            &intermediate_active[idx]
        };
        let stage_slot_next = if idx + 1 == actions.len() {
            slot_next
        } else {
            &intermediate_slots[idx]
        };
        let stage_system_curr = if idx == 0 {
            curr_vars
        } else {
            &intermediate_system_vars[idx - 1]
        };
        let stage_system_next = if idx + 1 == actions.len() {
            next_vars
        } else {
            &intermediate_system_vars[idx]
        };
        let mut stage_vars = stage_system_curr.clone();
        stage_vars.extend(non_state_vars.clone());
        match action {
            IRAction::ExprStmt { expr } => {
                stage_vars.extend(
                    locals
                        .iter()
                        .map(|(name, binding)| (name.clone(), binding.term.clone())),
                );
                let stage_store_param_types = system_store_param_types(system);
                let stage_pool_ctx = PooledSyGuSCtx {
                    slots_per_entity,
                    active_vars: stage_active_curr,
                    slot_fields: stage_slot_curr,
                    store_param_types: &stage_store_param_types,
                };
                action_terms.push(encode_pooled_system_exprstmt_formula(
                    tm,
                    expr,
                    PooledActionCtx {
                        system,
                        systems_by_name,
                        entities_by_name,
                        slots_per_entity,
                        vars: &stage_vars,
                        next_vars: stage_system_next,
                        entity_bindings: ctx.entity_bindings,
                        frames: PooledFrameVars {
                            active_curr: stage_active_curr,
                            active_next: stage_active_next,
                            slot_curr: stage_slot_curr,
                            slot_next: stage_slot_next,
                        },
                        enum_catalog,
                        call_stack,
                    },
                    &stage_pool_ctx,
                )?);
            }
            _ => {
                let action_result = encode_pooled_system_action(
                    tm,
                    action,
                    PooledActionCtx {
                        system,
                        systems_by_name,
                        entities_by_name,
                        slots_per_entity,
                        vars: &stage_vars,
                        next_vars: stage_system_next,
                        entity_bindings: ctx.entity_bindings,
                        frames: PooledFrameVars {
                            active_curr: stage_active_curr,
                            active_next: stage_active_next,
                            slot_curr: stage_slot_curr,
                            slot_next: stage_slot_next,
                        },
                        enum_catalog,
                        call_stack,
                    },
                    &locals,
                )?;
                let mut framed =
                    frame_all_system_fields(tm, systems_by_name, &stage_vars, stage_system_next)?;
                framed.push(action_result.formula);
                action_terms.push(mk_and(tm, &framed));
                locals = action_result.locals;
            }
        }
    }

    Ok(PooledActionResult {
        formula: mk_exists(tm, &bound, mk_and(tm, &action_terms)),
        locals,
    })
}

fn encode_pooled_match_expr(
    tm: &Cvc5Tm,
    scrutinee: &IRExpr,
    arms: &[crate::ir::types::IRMatchArm],
    vars: &HashMap<String, Cvc5Term>,
    entity_bindings: &PooledEntityBindings,
    pool_ctx: &PooledSyGuSCtx<'_>,
    enum_catalog: &EnumCatalog,
) -> Result<Cvc5Term, String> {
    if arms.is_empty() {
        return Err("cvc5 SyGuS match requires at least one arm".to_owned());
    }
    let scrut_term =
        encode_pooled_expr(tm, scrutinee, vars, entity_bindings, pool_ctx, enum_catalog)?;
    let scrut_ty = sygus_match_scrutinee_type(scrutinee);
    let mut fallback = None;
    for arm in arms.iter().rev() {
        let mut arm_vars = vars.clone();
        bind_pattern_vars(
            tm,
            &arm.pattern,
            &scrut_term,
            scrut_ty.as_ref(),
            &mut arm_vars,
            enum_catalog,
        )?;
        let pat_cond = encode_pattern_cond(
            tm,
            &arm.pattern,
            &scrut_term,
            scrut_ty.as_ref(),
            enum_catalog,
        )?;
        let guard_cond = if let Some(guard) = &arm.guard {
            encode_pooled_expr(
                tm,
                guard,
                &arm_vars,
                entity_bindings,
                pool_ctx,
                enum_catalog,
            )?
        } else {
            tm.mk_boolean(true)
        };
        let arm_cond = mk_and(tm, &[pat_cond, guard_cond]);
        let arm_body = encode_pooled_expr(
            tm,
            &arm.body,
            &arm_vars,
            entity_bindings,
            pool_ctx,
            enum_catalog,
        )?;
        fallback = Some(match fallback {
            None => {
                if arm.guard.is_none()
                    && matches!(
                        arm.pattern,
                        crate::ir::types::IRPattern::PWild
                            | crate::ir::types::IRPattern::PVar { .. }
                    )
                {
                    arm_body
                } else {
                    return Err(
                        "cvc5 SyGuS match requires a final wildcard or var fallback arm".to_owned(),
                    );
                }
            }
            Some(else_term) => {
                tm.mk_term(Cvc5Kind::CVC5_KIND_ITE, &[arm_cond, arm_body, else_term])
            }
        });
    }
    fallback.ok_or_else(|| "cvc5 SyGuS match required at least one arm".to_owned())
}

fn encode_pooled_finite_choose_expr(
    tm: &Cvc5Tm,
    var: &str,
    domain: &IRType,
    predicate: Option<&IRExpr>,
    env: PooledExprEnv<'_>,
) -> Result<Cvc5Term, String> {
    let vars = env.vars;
    let entity_bindings = env.entity_bindings;
    let pool_ctx = env.pool_ctx;
    let enum_catalog = env.enum_catalog;
    let Some(candidates) = finite_domain_values(tm, domain, enum_catalog) else {
        return Err(
            "cvc5 SyGuS pooled system safety only supports finite Bool/enum domains for choose"
                .to_owned(),
        );
    };
    let Some(default) = candidates.first().cloned() else {
        return Err("cvc5 SyGuS pooled choose requires a non-empty finite domain".to_owned());
    };

    let mut choice = default;
    for candidate in candidates.iter().rev() {
        let mut scoped = vars.clone();
        scoped.insert(var.to_owned(), candidate.clone());
        let cond = if let Some(predicate) = predicate {
            encode_pooled_expr(
                tm,
                predicate,
                &scoped,
                entity_bindings,
                pool_ctx,
                enum_catalog,
            )?
        } else {
            tm.mk_boolean(true)
        };
        choice = tm.mk_term(Cvc5Kind::CVC5_KIND_ITE, &[cond, candidate.clone(), choice]);
    }
    Ok(choice)
}

fn encode_pooled_finite_aggregate_expr(
    tm: &Cvc5Tm,
    kind: crate::ir::types::IRAggKind,
    var: &str,
    domain: &IRType,
    body: &IRExpr,
    in_filter: Option<&IRExpr>,
    env: PooledExprEnv<'_>,
) -> Result<Cvc5Term, String> {
    let vars = env.vars;
    let entity_bindings = env.entity_bindings;
    let pool_ctx = env.pool_ctx;
    let enum_catalog = env.enum_catalog;
    let Some(candidates) = finite_domain_values(tm, domain, enum_catalog) else {
        return Err(
            "cvc5 SyGuS pooled system safety only supports finite Bool/enum domains for finite aggregates"
                .to_owned(),
        );
    };
    if candidates.is_empty() {
        return match kind {
            crate::ir::types::IRAggKind::Sum | crate::ir::types::IRAggKind::Count => {
                Ok(tm.mk_integer(0))
            }
            crate::ir::types::IRAggKind::Product => Ok(tm.mk_integer(1)),
            crate::ir::types::IRAggKind::Min | crate::ir::types::IRAggKind::Max => Err(format!(
                "cvc5 SyGuS pooled {kind:?} aggregate requires a non-empty finite domain"
            )),
        };
    }

    let mut slot_data = Vec::with_capacity(candidates.len());
    for candidate in candidates {
        let mut scoped = vars.clone();
        scoped.insert(var.to_owned(), candidate);
        let mut active = tm.mk_boolean(true);
        if let Some(filter) = in_filter {
            active =
                encode_pooled_expr(tm, filter, &scoped, entity_bindings, pool_ctx, enum_catalog)?;
        }
        if kind == crate::ir::types::IRAggKind::Count {
            let pred =
                encode_pooled_expr(tm, body, &scoped, entity_bindings, pool_ctx, enum_catalog)?;
            active = mk_and(tm, &[active, pred]);
            slot_data.push((active, tm.mk_integer(1)));
        } else {
            let value =
                encode_pooled_expr(tm, body, &scoped, entity_bindings, pool_ctx, enum_catalog)?;
            slot_data.push((active, value));
        }
    }

    match kind {
        crate::ir::types::IRAggKind::Sum | crate::ir::types::IRAggKind::Count => {
            let sample = &slot_data[0].1;
            let zero = zero_like(tm, sample);
            let mut acc = zero.clone();
            for (active, value) in &slot_data {
                let contribution = tm.mk_term(
                    Cvc5Kind::CVC5_KIND_ITE,
                    &[active.clone(), value.clone(), zero.clone()],
                );
                acc = tm.mk_term(Cvc5Kind::CVC5_KIND_ADD, &[acc, contribution]);
            }
            Ok(acc)
        }
        crate::ir::types::IRAggKind::Product => {
            let sample = &slot_data[0].1;
            let one = one_like(tm, sample);
            let mut acc = one.clone();
            for (active, value) in &slot_data {
                let contribution = tm.mk_term(
                    Cvc5Kind::CVC5_KIND_ITE,
                    &[active.clone(), value.clone(), one.clone()],
                );
                acc = tm.mk_term(Cvc5Kind::CVC5_KIND_MULT, &[acc, contribution]);
            }
            Ok(acc)
        }
        crate::ir::types::IRAggKind::Min | crate::ir::types::IRAggKind::Max => {
            let is_min = kind == crate::ir::types::IRAggKind::Min;
            let mut acc = slot_data[0].1.clone();
            let mut any_active = slot_data[0].0.clone();
            for (active, value) in slot_data.iter().skip(1) {
                let better_kind = if is_min {
                    Cvc5Kind::CVC5_KIND_LT
                } else {
                    Cvc5Kind::CVC5_KIND_GT
                };
                let better = tm.mk_term(better_kind, &[value.clone(), acc.clone()]);
                let first_active = mk_and(
                    tm,
                    &[
                        active.clone(),
                        tm.mk_term(Cvc5Kind::CVC5_KIND_NOT, &[any_active.clone()]),
                    ],
                );
                let take = mk_or(tm, &[first_active, mk_and(tm, &[active.clone(), better])]);
                acc = tm.mk_term(Cvc5Kind::CVC5_KIND_ITE, &[take, value.clone(), acc]);
                any_active = mk_or(tm, &[any_active, active.clone()]);
            }
            let undef = tm.mk_var(acc.sort(), &format!("__sygus_pooled_{kind:?}_{var}_undef"));
            Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_ITE, &[any_active, acc, undef]))
        }
    }
}

fn infer_pooled_store_quant_entity(
    var: &str,
    body: &IRExpr,
    store_param_types: &HashMap<String, String>,
) -> Option<String> {
    match body {
        IRExpr::Index { map, key, .. } => match (map.as_ref(), key.as_ref()) {
            (
                IRExpr::Var {
                    name: store_name, ..
                },
                IRExpr::Var { name: key_name, .. },
            ) if key_name == var => store_param_types.get(store_name).cloned(),
            _ => None,
        },
        IRExpr::BinOp { left, right, .. } => {
            infer_pooled_store_quant_entity(var, left, store_param_types)
                .or_else(|| infer_pooled_store_quant_entity(var, right, store_param_types))
        }
        IRExpr::UnOp { operand, .. } => {
            infer_pooled_store_quant_entity(var, operand, store_param_types)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => infer_pooled_store_quant_entity(var, cond, store_param_types)
            .or_else(|| infer_pooled_store_quant_entity(var, then_body, store_param_types))
            .or_else(|| {
                else_body
                    .as_deref()
                    .and_then(|expr| infer_pooled_store_quant_entity(var, expr, store_param_types))
            }),
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            infer_pooled_store_quant_entity(var, expr, store_param_types)
        }
        _ => None,
    }
}

fn encode_pooled_expr(
    tm: &Cvc5Tm,
    expr: &IRExpr,
    vars: &HashMap<String, Cvc5Term>,
    entity_bindings: &PooledEntityBindings,
    pool_ctx: &PooledSyGuSCtx<'_>,
    enum_catalog: &EnumCatalog,
) -> Result<Cvc5Term, String> {
    match expr {
        IRExpr::Lit { value, .. } => match value {
            LitVal::Int { value } => Ok(tm.mk_integer(*value)),
            LitVal::Real { value } => real_lit_term(tm, *value),
            LitVal::Bool { value } => Ok(tm.mk_boolean(*value)),
            LitVal::Float { .. } | LitVal::Str { .. } => Err(
                "cvc5 SyGuS pooled system safety only supports integer, real, and boolean literals today"
                    .to_owned(),
            ),
        },
        IRExpr::Sorry { .. } => Ok(tm.mk_boolean(true)),
        IRExpr::Todo { .. } => Err("todo expression in cvc5 SyGuS pooled slice".to_owned()),
        IRExpr::Ctor {
            enum_name,
            ctor,
            args,
            ..
        } => {
            if let Some(term) =
                encode_payload_ctor_expr(tm, enum_name, ctor, args, enum_catalog, |arg| {
                    encode_pooled_expr(tm, arg, vars, entity_bindings, pool_ctx, enum_catalog)
                })?
            {
                return Ok(term);
            }
            if !args.is_empty() {
                return Err(format!(
                    "cvc5 SyGuS pooled system safety does not support payload constructors yet (`{enum_name}::{ctor}`)"
                ));
            }
            let idx = lookup_enum_ctor_index(enum_catalog, enum_name, ctor).ok_or_else(|| {
                format!("unsupported enum constructor `{enum_name}::{ctor}` in pooled SyGuS slice")
            })?;
            Ok(tm.mk_integer(*idx))
        }
        IRExpr::Var { name, ty, .. } => vars
            .get(name)
            .cloned()
            .or_else(|| encode_enum_atom_var(tm, name, ty, enum_catalog))
            .ok_or_else(|| {
                if entity_bindings.contains_key(name) {
                    format!("bare entity variable `{name}` is not supported in pooled SyGuS slice")
                } else {
                    format!("unsupported free variable `{name}` in pooled SyGuS slice")
                }
            }),
        IRExpr::App { func, arg, .. } => {
            let IRExpr::Lam { param, body, .. } = func.as_ref() else {
                return Err(
                    "cvc5 SyGuS pooled system safety only supports inline lambda application today"
                        .to_owned(),
                );
            };
            let arg_term =
                encode_pooled_expr(tm, arg, vars, entity_bindings, pool_ctx, enum_catalog)?;
            let mut scoped = vars.clone();
            scoped.insert(param.clone(), arg_term);
            encode_pooled_expr(tm, body, &scoped, entity_bindings, pool_ctx, enum_catalog)
        }
        IRExpr::Field {
            expr: recv, field, ..
        } => {
            if let IRExpr::Ctor { args, .. } = recv.as_ref() {
                if let Some(term) =
                    encode_static_payload_field_projection(field, args, |arg| {
                        encode_pooled_expr(
                            tm,
                            arg,
                            vars,
                            entity_bindings,
                            pool_ctx,
                            enum_catalog,
                        )
                    })?
                {
                    return Ok(term);
                }
            }
            let IRExpr::Var { name, .. } = recv.as_ref() else {
                return Err(
                    "cvc5 SyGuS pooled system safety only supports field access on bound entity vars"
                        .to_owned(),
                );
            };
            if !entity_bindings.contains_key(name) {
                let receiver = encode_pooled_expr(
                    tm,
                    recv,
                    vars,
                    entity_bindings,
                    pool_ctx,
                    enum_catalog,
                )?;
                if let Some(term) = encode_dynamic_payload_field_projection(
                    tm,
                    field,
                    receiver,
                    sygus_expr_type(recv),
                    enum_catalog,
                )? {
                    return Ok(term);
                }
            }
            let slot = entity_bindings
                .get(name)
                .ok_or_else(|| format!("unknown entity binding `{name}` in pooled SyGuS slice"))?;
            let (entity_name, slot) = slot;
            pool_ctx
                .slot_fields
                .get(&pool_slot_field_key(entity_name, *slot, field))
                .cloned()
                .ok_or_else(|| {
                    format!("unknown pooled field `{field}` on {entity_name} slot {slot}")
                })
        }
        IRExpr::Index { map, key, .. } => {
            if let Some(term) =
                encode_finite_map_lookup_expr(tm, map, key, vars, enum_catalog, |expr, scoped| {
                    encode_pooled_expr(
                        tm,
                        expr,
                        scoped,
                        entity_bindings,
                        pool_ctx,
                        enum_catalog,
                    )
                })?
            {
                return Ok(term);
            }
            if let Some(term) =
                encode_finite_seq_index_expr(tm, map, key, vars, enum_catalog, |expr, scoped| {
                    encode_pooled_expr(
                        tm,
                        expr,
                        scoped,
                        entity_bindings,
                        pool_ctx,
                        enum_catalog,
                    )
                })?
            {
                return Ok(term);
            }
            let is_finite_set_membership_shape =
                matches!(map.as_ref(), IRExpr::SetLit { .. } | IRExpr::SetComp { .. })
                    || matches!(
                        map.as_ref(),
                        IRExpr::BinOp { op, .. }
                            if matches!(
                                op.as_str(),
                                "OpSetUnion" | "OpSetIntersect" | "OpSetDiff"
                            )
                    );
            if is_finite_set_membership_shape {
                return encode_finite_set_membership_expr(
                    tm,
                    map,
                    key,
                    vars,
                    enum_catalog,
                    |expr, scoped| {
                        encode_pooled_expr(
                            tm,
                            expr,
                            scoped,
                            entity_bindings,
                            pool_ctx,
                            enum_catalog,
                        )
                    },
                );
            }
            if let IRExpr::Var {
                name: store_name, ..
            } = map.as_ref()
            {
                if let Some(entity_name) = pool_ctx.store_param_types.get(store_name.as_str()) {
                    let key_term =
                        encode_pooled_expr(tm, key, vars, entity_bindings, pool_ctx, enum_catalog)?;
                    let n_slots = *pool_ctx
                        .slots_per_entity
                        .get(entity_name)
                        .ok_or_else(|| format!("unknown pooled store entity `{entity_name}`"))?;
                    let mut disjuncts = Vec::new();
                    for slot in 0..n_slots {
                        let active = pool_ctx
                            .active_vars
                            .get(entity_name)
                            .and_then(|slots| slots.get(&slot))
                            .ok_or_else(|| {
                                format!("missing active variable for {entity_name} slot {slot}")
                            })?
                            .clone();
                        let slot_eq = tm.mk_term(
                            Cvc5Kind::CVC5_KIND_EQUAL,
                            &[key_term.clone(), tm.mk_integer(slot as i64)],
                        );
                        disjuncts.push(mk_and(tm, &[slot_eq, active]));
                    }
                    return Ok(mk_or(tm, &disjuncts));
                }
            }
            Err("cvc5 SyGuS pooled system safety only supports index on store params".to_owned())
        }
        IRExpr::UnOp { op, operand, .. } => {
            let inner =
                encode_pooled_expr(tm, operand, vars, entity_bindings, pool_ctx, enum_catalog)?;
            match op.as_str() {
                "OpNot" | "not" | "!" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_NOT, &[inner])),
                "OpNeg" | "-" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_NEG, &[inner])),
                _ => Err(format!(
                    "unsupported unary op `{op}` in pooled cvc5 SyGuS slice"
                )),
            }
        }
        IRExpr::BinOp {
            op,
            left,
            right,
            ty,
            ..
        } => {
            if matches!(op.as_str(), "OpSetSubset") {
                if let Some(term) = encode_finite_set_subset_expr(
                    tm,
                    left,
                    right,
                    vars,
                    enum_catalog,
                    |expr, scoped| {
                        encode_pooled_expr(
                            tm,
                            expr,
                            scoped,
                            entity_bindings,
                            pool_ctx,
                            enum_catalog,
                        )
                    },
                )? {
                    return Ok(term);
                }
            }
            if matches!(op.as_str(), "OpDisjoint" | "disjoint") {
                if let Some(term) = encode_finite_set_disjoint_expr(
                    tm,
                    left,
                    right,
                    vars,
                    enum_catalog,
                    |expr, scoped| {
                        encode_pooled_expr(
                            tm,
                            expr,
                            scoped,
                            entity_bindings,
                            pool_ctx,
                            enum_catalog,
                        )
                    },
                )? {
                    return Ok(term);
                }
            }
            let lhs = encode_pooled_expr(tm, left, vars, entity_bindings, pool_ctx, enum_catalog)?;
            let rhs = encode_pooled_expr(tm, right, vars, entity_bindings, pool_ctx, enum_catalog)?;
            match op.as_str() {
                "OpAnd" | "and" | "&&" => Ok(mk_and(tm, &[lhs, rhs])),
                "OpOr" | "or" | "||" => Ok(mk_or(tm, &[lhs, rhs])),
                "OpImplies" | "implies" | "=>" => {
                    Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_IMPLIES, &[lhs, rhs]))
                }
                "OpXor" | "xor" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_XOR, &[lhs, rhs])),
                "OpEq" | "==" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_EQUAL, &[lhs, rhs])),
                "OpNEq" | "!=" => Ok(tm.mk_term(
                    Cvc5Kind::CVC5_KIND_NOT,
                    &[tm.mk_term(Cvc5Kind::CVC5_KIND_EQUAL, &[lhs, rhs])],
                )),
                "OpLt" | "<" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_LT, &[lhs, rhs])),
                "OpLe" | "<=" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_LEQ, &[lhs, rhs])),
                "OpGt" | ">" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_GT, &[lhs, rhs])),
                "OpGe" | ">=" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_GEQ, &[lhs, rhs])),
                "OpAdd" | "+" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_ADD, &[lhs, rhs])),
                "OpSub" | "-" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_SUB, &[lhs, rhs])),
                "OpMul" | "*" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_MULT, &[lhs, rhs])),
                "OpDiv" | "/" if matches!(ty, IRType::Real) => {
                    Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_DIVISION, &[lhs, rhs]))
                }
                "OpDiv" | "/" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_INTS_DIVISION, &[lhs, rhs])),
                "OpMod" | "%" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_INTS_MODULUS, &[lhs, rhs])),
                _ => Err(format!(
                    "unsupported binary op `{op}` in pooled cvc5 SyGuS slice"
                )),
            }
        }
        IRExpr::Let { bindings, body, .. } => {
            let mut local = vars.clone();
            for binding in bindings {
                let value = encode_pooled_expr(
                    tm,
                    &binding.expr,
                    &local,
                    entity_bindings,
                    pool_ctx,
                    enum_catalog,
                )?;
                local.insert(binding.name.clone(), value);
            }
            encode_pooled_expr(tm, body, &local, entity_bindings, pool_ctx, enum_catalog)
        }
        IRExpr::Block { exprs, .. } => {
            let mut last = tm.mk_boolean(true);
            for expr in exprs {
                last = encode_pooled_expr(
                    tm,
                    expr,
                    vars,
                    entity_bindings,
                    pool_ctx,
                    enum_catalog,
                )?;
            }
            Ok(last)
        }
        IRExpr::VarDecl {
            name, init, rest, ..
        } => {
            let value = encode_pooled_expr(
                tm,
                init,
                vars,
                entity_bindings,
                pool_ctx,
                enum_catalog,
            )?;
            let mut local = vars.clone();
            local.insert(name.clone(), value);
            encode_pooled_expr(tm, rest, &local, entity_bindings, pool_ctx, enum_catalog)
        }
        IRExpr::Prime { expr, .. } => {
            encode_pooled_expr(tm, expr, vars, entity_bindings, pool_ctx, enum_catalog)
        }
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            encode_pooled_expr(tm, expr, vars, entity_bindings, pool_ctx, enum_catalog)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond = encode_pooled_expr(tm, cond, vars, entity_bindings, pool_ctx, enum_catalog)?;
            let then_term =
                encode_pooled_expr(tm, then_body, vars, entity_bindings, pool_ctx, enum_catalog)?;
            let else_term = encode_pooled_expr(
                tm,
                else_body.as_deref().ok_or_else(|| {
                    "cvc5 SyGuS pooled slice requires an explicit else branch".to_owned()
                })?,
                vars,
                entity_bindings,
                pool_ctx,
                enum_catalog,
            )?;
            Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_ITE, &[cond, then_term, else_term]))
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => encode_pooled_match_expr(
            tm,
            scrutinee,
            arms,
            vars,
            entity_bindings,
            pool_ctx,
            enum_catalog,
        ),
        IRExpr::Choose {
            var,
            domain,
            predicate,
            ..
        } => encode_pooled_finite_choose_expr(
            tm,
            var,
            domain,
            predicate.as_deref(),
            PooledExprEnv {
                vars,
                entity_bindings,
                pool_ctx,
                enum_catalog,
            },
        ),
        IRExpr::Aggregate {
            kind,
            var,
            domain,
            body,
            in_filter,
            ..
        } => encode_pooled_finite_aggregate_expr(
            tm,
            *kind,
            var,
            domain,
            body,
            in_filter.as_deref(),
            PooledExprEnv {
                vars,
                entity_bindings,
                pool_ctx,
                enum_catalog,
            },
        ),
        IRExpr::Card { expr: inner, .. } => {
            encode_finite_card_expr(tm, inner, vars, enum_catalog, |expr, scoped| {
                encode_pooled_expr(tm, expr, scoped, entity_bindings, pool_ctx, enum_catalog)
            })
        }
        IRExpr::Forall {
            var, domain, body, ..
        }
        | IRExpr::Exists {
            var, domain, body, ..
        }
        | IRExpr::One {
            var, domain, body, ..
        }
        | IRExpr::Lone {
            var, domain, body, ..
        } => {
            let kind = match expr {
                IRExpr::Forall { .. } => "forall",
                IRExpr::Exists { .. } => "exists",
                IRExpr::One { .. } => "one",
                IRExpr::Lone { .. } => "lone",
                _ => unreachable!(),
            };
            if let IRType::Entity { name } = domain {
                let n_slots = *pool_ctx
                    .slots_per_entity
                    .get(name)
                    .ok_or_else(|| format!("unknown pooled entity domain `{name}`"))?;
                let mut bodies = Vec::new();
                for slot in 0..n_slots {
                    let active = pool_ctx
                        .active_vars
                        .get(name)
                        .and_then(|slots| slots.get(&slot))
                        .ok_or_else(|| format!("missing active variable for {name} slot {slot}"))?
                        .clone();
                    let mut inner_bindings = entity_bindings.clone();
                    inner_bindings.insert(var.clone(), (name.clone(), slot));
                    let body_term = encode_pooled_expr(
                        tm,
                        body,
                        vars,
                        &inner_bindings,
                        pool_ctx,
                        enum_catalog,
                    )?;
                    bodies.push(match kind {
                        "forall" => tm.mk_term(Cvc5Kind::CVC5_KIND_IMPLIES, &[active, body_term]),
                        "exists" | "one" | "lone" => mk_and(tm, &[active, body_term]),
                        _ => unreachable!(),
                    });
                }
                return match kind {
                    "forall" => Ok(mk_and(tm, &bodies)),
                    "exists" => Ok(mk_or(tm, &bodies)),
                    "one" => {
                        if bodies.is_empty() {
                            Ok(tm.mk_boolean(false))
                        } else {
                            let mut disjuncts = Vec::new();
                            for i in 0..bodies.len() {
                                let mut conjuncts = vec![bodies[i].clone()];
                                for (j, body_j) in bodies.iter().enumerate() {
                                    if i != j {
                                        conjuncts.push(tm.mk_term(
                                            Cvc5Kind::CVC5_KIND_NOT,
                                            std::slice::from_ref(body_j),
                                        ));
                                    }
                                }
                                disjuncts.push(mk_and(tm, &conjuncts));
                            }
                            Ok(mk_or(tm, &disjuncts))
                        }
                    }
                    "lone" => {
                        if bodies.len() <= 1 {
                            Ok(tm.mk_boolean(true))
                        } else {
                            let mut conjuncts = Vec::new();
                            for i in 0..bodies.len() {
                                for j in (i + 1)..bodies.len() {
                                    conjuncts.push(tm.mk_term(
                                        Cvc5Kind::CVC5_KIND_NOT,
                                        &[mk_and(tm, &[bodies[i].clone(), bodies[j].clone()])],
                                    ));
                                }
                            }
                            Ok(mk_and(tm, &conjuncts))
                        }
                    }
                    _ => unreachable!(),
                };
            }

            if *domain == IRType::Int {
                let Some(entity_name) =
                    infer_pooled_store_quant_entity(var, body, pool_ctx.store_param_types)
                else {
                    return Err(
                        "cvc5 SyGuS pooled system safety only supports Int quantifiers when they range over store param slots"
                            .to_owned(),
                    );
                };
                let n_slots = *pool_ctx
                    .slots_per_entity
                    .get(&entity_name)
                    .ok_or_else(|| format!("unknown pooled store entity `{entity_name}`"))?;
                let mut bodies = Vec::new();
                for slot in 0..n_slots {
                    let mut scoped = vars.clone();
                    scoped.insert(var.clone(), tm.mk_integer(slot as i64));
                    let mut inner_bindings = entity_bindings.clone();
                    inner_bindings.insert(var.clone(), (entity_name.clone(), slot));
                    bodies.push(encode_pooled_expr(
                        tm,
                        body,
                        &scoped,
                        &inner_bindings,
                        pool_ctx,
                        enum_catalog,
                    )?);
                }
                return match kind {
                    "forall" => Ok(mk_and(tm, &bodies)),
                    "exists" => Ok(mk_or(tm, &bodies)),
                    "one" => {
                        if bodies.is_empty() {
                            Ok(tm.mk_boolean(false))
                        } else {
                            let mut disjuncts = Vec::new();
                            for i in 0..bodies.len() {
                                let mut conjuncts = vec![bodies[i].clone()];
                                for (j, body_j) in bodies.iter().enumerate() {
                                    if i != j {
                                        conjuncts.push(tm.mk_term(
                                            Cvc5Kind::CVC5_KIND_NOT,
                                            std::slice::from_ref(body_j),
                                        ));
                                    }
                                }
                                disjuncts.push(mk_and(tm, &conjuncts));
                            }
                            Ok(mk_or(tm, &disjuncts))
                        }
                    }
                    "lone" => {
                        if bodies.len() <= 1 {
                            Ok(tm.mk_boolean(true))
                        } else {
                            let mut conjuncts = Vec::new();
                            for i in 0..bodies.len() {
                                for j in (i + 1)..bodies.len() {
                                    conjuncts.push(tm.mk_term(
                                        Cvc5Kind::CVC5_KIND_NOT,
                                        &[mk_and(tm, &[bodies[i].clone(), bodies[j].clone()])],
                                    ));
                                }
                            }
                            Ok(mk_and(tm, &conjuncts))
                        }
                    }
                    _ => unreachable!(),
                };
            }

            let Some(candidates) = finite_domain_values(tm, domain, enum_catalog) else {
                return Err(
                    "cvc5 SyGuS pooled system safety only supports finite Bool/enum domains for finite quantifiers"
                        .to_owned(),
                );
            };
            let mut bodies = Vec::new();
            for candidate in candidates {
                let mut scoped = vars.clone();
                scoped.insert(var.clone(), candidate);
                bodies.push(encode_pooled_expr(
                    tm,
                    body,
                    &scoped,
                    entity_bindings,
                    pool_ctx,
                    enum_catalog,
                )?);
            }
            match kind {
                "forall" => Ok(mk_and(tm, &bodies)),
                "exists" => Ok(mk_or(tm, &bodies)),
                "one" => {
                    if bodies.is_empty() {
                        Ok(tm.mk_boolean(false))
                    } else {
                        let mut disjuncts = Vec::new();
                        for i in 0..bodies.len() {
                            let mut conjuncts = vec![bodies[i].clone()];
                            for (j, body_j) in bodies.iter().enumerate() {
                                if i != j {
                                    conjuncts.push(tm.mk_term(
                                        Cvc5Kind::CVC5_KIND_NOT,
                                        std::slice::from_ref(body_j),
                                    ));
                                }
                            }
                            disjuncts.push(mk_and(tm, &conjuncts));
                        }
                        Ok(mk_or(tm, &disjuncts))
                    }
                }
                "lone" => {
                    if bodies.len() <= 1 {
                        Ok(tm.mk_boolean(true))
                    } else {
                        let mut conjuncts = Vec::new();
                        for i in 0..bodies.len() {
                            for j in (i + 1)..bodies.len() {
                                conjuncts.push(tm.mk_term(
                                    Cvc5Kind::CVC5_KIND_NOT,
                                    &[mk_and(tm, &[bodies[i].clone(), bodies[j].clone()])],
                                ));
                            }
                        }
                        Ok(mk_and(tm, &conjuncts))
                    }
                }
                _ => unreachable!(),
            }
        }
        _ => Err(format!(
            "unsupported expression kind in cvc5 SyGuS pooled system safety slice: {expr:?}"
        )),
    }
}

fn bind_explicit_params(
    tm: &Cvc5Tm,
    params: &[IRTransParam],
    args: &[IRExpr],
    env: PooledExprEnv<'_>,
    context: &str,
) -> Result<PooledParamEnv, String> {
    let vars = env.vars;
    let entity_bindings = env.entity_bindings;
    let pool_ctx = env.pool_ctx;
    let enum_catalog = env.enum_catalog;
    if params.len() != args.len() {
        return Err(format!(
            "cvc5 SyGuS pooled cross-call safety expected {} args for `{context}`, got {}",
            params.len(),
            args.len()
        ));
    }
    let mut bound = PooledParamEnv::default();
    let mut scoped = vars.clone();
    for (param, arg) in params.iter().zip(args.iter()) {
        let arg_term =
            encode_pooled_expr(tm, arg, &scoped, entity_bindings, pool_ctx, enum_catalog)?;
        if let Some(name) = entity_type_name(&param.ty) {
            let IRExpr::Var { name: arg_name, .. } = arg else {
                return Err(format!(
                    "cvc5 SyGuS pooled cross-call safety requires entity argument `{}` for `{context}` to be a bound entity variable",
                    param.name
                ));
            };
            let (entity_name, slot) = entity_bindings.get(arg_name).cloned().ok_or_else(|| {
                format!(
                    "cvc5 SyGuS pooled cross-call safety could not bind entity argument `{arg_name}` for `{context}`"
                )
            })?;
            if entity_name != *name {
                return Err(format!(
                    "cvc5 SyGuS pooled cross-call safety expected entity argument `{}` to bind `{name}`, got `{entity_name}`",
                    param.name
                ));
            }
            bound
                .entity_bindings
                .insert(param.name.clone(), (entity_name, slot));
        }
        scoped.insert(param.name.clone(), arg_term.clone());
        bound.terms.insert(param.name.clone(), arg_term);
    }
    Ok(bound)
}

fn extend_call_stack(call_stack: &[String], target_system_name: &str) -> Vec<String> {
    let mut next = call_stack.to_vec();
    next.push(target_system_name.to_owned());
    next
}

fn encode_pooled_crosscall_capture(
    tm: &Cvc5Tm,
    target_system_name: &str,
    command: &str,
    args: &[IRExpr],
    ctx: PooledCrossCallCtx<'_>,
) -> Result<PooledCrossCallCapture, String> {
    let systems_by_name = ctx.systems_by_name;
    let entities_by_name = ctx.entities_by_name;
    let slots_per_entity = ctx.slots_per_entity;
    let curr_vars = ctx.curr_vars;
    let next_vars = ctx.next_vars;
    let entity_bindings = ctx.entity_bindings;
    let active_curr = ctx.frames.active_curr;
    let active_next = ctx.frames.active_next;
    let slot_curr = ctx.frames.slot_curr;
    let slot_next = ctx.frames.slot_next;
    let enum_catalog = ctx.enum_catalog;
    let call_stack = ctx.call_stack;
    if call_stack.iter().any(|name| name == target_system_name) {
        return Err(format!(
            "cvc5 SyGuS pooled cross-call safety does not support recursive cross-call cycles (`{}::{}`)",
            target_system_name, command
        ));
    }
    let target_system = systems_by_name.get(target_system_name).ok_or_else(|| {
        format!(
            "cvc5 SyGuS pooled cross-call safety could not find target system `{target_system_name}`"
        )
    })?;
    let target_step = target_system
        .actions
        .iter()
        .find(|step| step.name == *command)
        .ok_or_else(|| {
            format!(
                "cvc5 SyGuS pooled cross-call safety could not find target command `{target_system_name}::{command}`"
            )
        })?;
    let bound_params = bind_explicit_params(
        tm,
        &target_step.params,
        args,
        PooledExprEnv {
            vars: curr_vars,
            entity_bindings,
            pool_ctx: &PooledSyGuSCtx {
                slots_per_entity,
                active_vars: active_curr,
                slot_fields: slot_curr,
                store_param_types: &system_store_param_types(target_system),
            },
            enum_catalog,
        },
        &format!("{target_system_name}::{command}"),
    )?;
    let formula = encode_pooled_system_step_with_bound_params(
        tm,
        target_step,
        bound_params.clone(),
        PooledStepCtx {
            system: target_system,
            systems_by_name,
            entities_by_name,
            slots_per_entity,
            curr_vars,
            next_vars,
            frames: PooledFrameVars {
                active_curr,
                active_next,
                slot_curr,
                slot_next,
            },
            enum_catalog,
            call_stack: &extend_call_stack(call_stack, target_system_name),
        },
    )?;
    let return_value = if let Some(ret) = &target_step.return_expr {
        let mut ret_vars = curr_vars.clone();
        ret_vars.extend(bound_params.terms);
        let next_ctx = PooledSyGuSCtx {
            slots_per_entity,
            active_vars: active_next,
            slot_fields: slot_next,
            store_param_types: &system_store_param_types(target_system),
        };
        Some(encode_pooled_expr(
            tm,
            ret,
            &ret_vars,
            &bound_params.entity_bindings,
            &next_ctx,
            enum_catalog,
        )?)
    } else {
        None
    };
    Ok(PooledCrossCallCapture {
        formula,
        return_value,
        return_type: command_return_type(target_system, command).or_else(|| {
            target_step
                .return_expr
                .as_ref()
                .and_then(sygus_match_scrutinee_type)
        }),
    })
}

fn encode_pooled_action_match(
    tm: &Cvc5Tm,
    scrutinee: &crate::ir::types::IRActionMatchScrutinee,
    arms: &[crate::ir::types::IRActionMatchArm],
    ctx: PooledActionCtx<'_>,
    local_bindings: &PooledLocalBindings,
) -> Result<Cvc5Term, String> {
    let system = ctx.system;
    let vars = ctx.vars;
    let next_vars = ctx.next_vars;
    let active_curr = ctx.frames.active_curr;
    let active_next = ctx.frames.active_next;
    let slot_curr = ctx.frames.slot_curr;
    let slot_next = ctx.frames.slot_next;
    let enum_catalog = ctx.enum_catalog;
    if arms.is_empty() {
        return Err("cvc5 SyGuS pooled action match requires at least one arm".to_owned());
    }
    let (prefix_formula, scrut_term, scrut_ty) = match scrutinee {
        crate::ir::types::IRActionMatchScrutinee::Var { name } => {
            if let Some(binding) = local_bindings.get(name) {
                (
                    tm.mk_boolean(true),
                    binding.term.clone(),
                    binding.ty.clone(),
                )
            } else {
                let scrut_term = vars.get(name).cloned().ok_or_else(|| {
                    format!(
                        "cvc5 SyGuS pooled action match only supports bound var scrutinees today (`{name}`)"
                    )
                })?;
                let scrut_ty = system
                    .fields
                    .iter()
                    .find(|field| field.name == *name)
                    .map(|field| field.ty.clone())
                    .or_else(|| {
                        system
                            .derived_fields
                            .iter()
                            .find(|field| field.name == *name)
                            .map(|field| field.ty.clone())
                    });
                (tm.mk_boolean(true), scrut_term, scrut_ty)
            }
        }
        crate::ir::types::IRActionMatchScrutinee::CrossCall {
            system: target_system_name,
            command,
            args,
        } => {
            let capture = encode_pooled_crosscall_capture(
                tm,
                target_system_name,
                command,
                args,
                PooledCrossCallCtx {
                    systems_by_name: ctx.systems_by_name,
                    entities_by_name: ctx.entities_by_name,
                    slots_per_entity: ctx.slots_per_entity,
                    curr_vars: vars,
                    next_vars,
                    entity_bindings: &HashMap::new(),
                    frames: ctx.frames,
                    enum_catalog,
                    call_stack: ctx.call_stack,
                },
            )?;
            let scrut_term = capture.return_value.ok_or_else(|| {
                format!(
                    "cvc5 SyGuS pooled action match requires `{target_system_name}::{command}` to return a value"
                )
            })?;
            (capture.formula, scrut_term, capture.return_type)
        }
    };

    let guard_store_param_types = system_store_param_types(system);
    let guard_ctx = PooledSyGuSCtx {
        slots_per_entity: ctx.slots_per_entity,
        active_vars: active_curr,
        slot_fields: slot_curr,
        store_param_types: &guard_store_param_types,
    };
    let mut fallback = None;
    for arm in arms.iter().rev() {
        let mut arm_vars = vars.clone();
        arm_vars.extend(
            local_bindings
                .iter()
                .map(|(name, binding)| (name.clone(), binding.term.clone())),
        );
        bind_pattern_vars(
            tm,
            &arm.pattern,
            &scrut_term,
            scrut_ty.as_ref(),
            &mut arm_vars,
            enum_catalog,
        )?;
        let pat_cond = encode_pattern_cond(
            tm,
            &arm.pattern,
            &scrut_term,
            scrut_ty.as_ref(),
            enum_catalog,
        )?;
        let guard_cond = if let Some(guard) = &arm.guard {
            encode_pooled_expr(
                tm,
                guard,
                &arm_vars,
                &HashMap::new(),
                &guard_ctx,
                enum_catalog,
            )?
        } else {
            tm.mk_boolean(true)
        };
        let arm_cond = mk_and(tm, &[pat_cond, guard_cond]);
        let arm_body = encode_pooled_system_action_sequence(
            tm,
            &arm.body,
            PooledActionCtx {
                system,
                systems_by_name: ctx.systems_by_name,
                entities_by_name: ctx.entities_by_name,
                slots_per_entity: ctx.slots_per_entity,
                vars: &arm_vars,
                next_vars,
                entity_bindings: &HashMap::new(),
                frames: PooledFrameVars {
                    active_curr,
                    active_next,
                    slot_curr,
                    slot_next,
                },
                enum_catalog,
                call_stack: ctx.call_stack,
            },
            local_bindings,
        )?
        .formula;
        fallback = Some(match fallback {
            None => {
                if arm.guard.is_none()
                    && matches!(
                        arm.pattern,
                        crate::ir::types::IRPattern::PWild
                            | crate::ir::types::IRPattern::PVar { .. }
                    )
                {
                    arm_body
                } else {
                    return Err(
                        "cvc5 SyGuS pooled action match requires a final wildcard or var fallback arm"
                            .to_owned(),
                    );
                }
            }
            Some(else_term) => {
                tm.mk_term(Cvc5Kind::CVC5_KIND_ITE, &[arm_cond, arm_body, else_term])
            }
        });
    }

    Ok(mk_and(
        tm,
        &[
            prefix_formula,
            fallback.ok_or_else(|| {
                "cvc5 SyGuS pooled action match required at least one arm".to_owned()
            })?,
        ],
    ))
}
