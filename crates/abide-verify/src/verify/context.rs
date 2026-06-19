//! Verification context — metadata extracted from IR for Z3 encoding.
//!
//! Built once per verification run, shared across all checks.
//!
//! ADT construction uses `DatatypeBuilder`, `DatatypeAccessor`, and
//! `DatatypeSort` via the `smt` facade re-exports.

use std::collections::HashMap;

use super::defenv::DefEnv;
use super::smt::{self, DatatypeAccessor, DatatypeSort};

use crate::ir::types::{
    IRAction, IRDecreases, IRExpr, IRMatchArm, IRPattern, IRProgram, IRQuery, IRType, LitVal,
};

// ── Variant ID mapping ──────────────────────────────────────────────

/// Maps enum variant names to sequential integer IDs for Z3 encoding.
///
/// Enum types are encoded as Z3 Int values where each variant is a
/// unique integer. This enables efficient equality checking and
/// domain constraints (`min_id` <= var <= `max_id`).
#[derive(Debug, Default)]
pub struct VariantMap {
    /// (`type_name`, `variant_name`) → unique i64 ID
    pub to_id: HashMap<(String, String), i64>,
    /// i64 ID → (`type_name`, `variant_name`) — for counterexample display
    pub from_id: HashMap<i64, (String, String)>,
    /// Next available ID
    next_id: i64,
}

impl VariantMap {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register all variants of an enum type. Returns (`min_id`, `max_id`).
    pub fn register_enum(&mut self, type_name: &str, variants: &[String]) -> (i64, i64) {
        let min_id = self.next_id;
        for v in variants {
            self.to_id
                .insert((type_name.to_owned(), v.clone()), self.next_id);
            self.from_id
                .insert(self.next_id, (type_name.to_owned(), v.clone()));
            self.next_id += 1;
        }
        let max_id = self.next_id - 1;
        (min_id, max_id)
    }

    /// Look up the ID for a variant.
    pub fn try_id_of(&self, type_name: &str, variant_name: &str) -> Result<i64, String> {
        self.to_id
            .get(&(type_name.to_owned(), variant_name.to_owned()))
            .copied()
            .ok_or_else(|| format!("unknown variant: {type_name}::{variant_name}"))
    }

    /// Look up the ID for a variant.
    ///
    /// Test-only convenience wrapper around `try_id_of`; production paths
    /// should route through the fallible API and surface encoding errors.
    #[cfg(test)]
    pub fn id_of(&self, type_name: &str, variant_name: &str) -> i64 {
        self.try_id_of(type_name, variant_name)
            .unwrap_or_else(|msg| panic!("{msg}"))
    }

    /// Look up the variant name for an ID. Returns None if not found.
    pub fn name_of(&self, id: i64) -> Option<&(String, String)> {
        self.from_id.get(&id)
    }
}

// ── Entity field metadata ───────────────────────────────────────────

/// Metadata about a single entity field for Z3 encoding.
#[derive(Debug, Clone)]
pub struct FieldInfo {
    pub name: String,
    pub ty: IRType,
    pub default: Option<IRExpr>,
}

impl FieldInfo {
    pub fn default_expr(&self) -> Option<&IRExpr> {
        self.default.as_ref()
    }

    pub fn default_display(&self) -> Option<String> {
        self.default.as_ref().and_then(default_expr_to_string)
    }
}

/// Metadata about an entity for Z3 encoding.
#[derive(Debug)]
pub struct EntityInfo {
    pub name: String,
    pub fields: Vec<FieldInfo>,
    pub actions: Vec<ActionInfo>,
}

/// Metadata about an entity action for Z3 encoding.
#[derive(Debug)]
pub struct ActionInfo {
    pub name: String,
    pub entity: String,
    /// Number of ref params + value params
    pub param_count: usize,
}

fn register_enum_type(
    ty: &IRType,
    variants: &mut VariantMap,
    enum_ranges: &mut HashMap<String, (i64, i64)>,
    adt_sorts: &mut HashMap<String, DatatypeSort>,
) {
    let IRType::Enum { name, variants: vs } = ty else {
        return;
    };
    if enum_ranges.contains_key(name) {
        return;
    }

    let ctor_names: Vec<String> = vs.iter().map(|v| v.name.clone()).collect();
    let (min, max) = variants.register_enum(name, &ctor_names);
    enum_ranges.insert(name.clone(), (min, max));

    if vs.iter().any(|v| !v.fields.is_empty()) {
        let mut builder = smt::datatype_builder(name.as_str());
        for v in vs {
            let fields: Vec<(&str, DatatypeAccessor)> = v
                .fields
                .iter()
                .map(|f| {
                    (
                        f.name.as_str(),
                        smt::datatype_accessor_sort(crate::verify::smt::ir_type_to_sort(&f.ty)),
                    )
                })
                .collect();
            builder = smt::datatype_builder_variant(builder, &v.name, fields);
        }
        let dt = smt::datatype_builder_finish(builder);
        adt_sorts.insert(name.clone(), dt);
    }
}

fn collect_program_enum_types<'a>(ir: &'a IRProgram, out: &mut Vec<&'a IRType>) {
    for ty_entry in &ir.types {
        collect_enum_types_from_ty(&ty_entry.ty, out);
    }
    for constant in &ir.constants {
        collect_enum_types_from_ty(&constant.ty, out);
        collect_enum_types_from_expr(&constant.value, out);
    }
    for function in &ir.functions {
        collect_enum_types_from_ty(&function.ty, out);
        collect_enum_types_from_expr(&function.body, out);
        for requires in &function.requires {
            collect_enum_types_from_expr(requires, out);
        }
        for ensures in &function.ensures {
            collect_enum_types_from_expr(ensures, out);
        }
        if let Some(decreases) = &function.decreases {
            collect_enum_types_from_decreases(decreases, out);
        }
    }
    for entity in &ir.entities {
        collect_enum_types_from_fields(&entity.fields, out);
        for transition in &entity.transitions {
            for param in &transition.params {
                collect_enum_types_from_ty(&param.ty, out);
            }
            collect_enum_types_from_expr(&transition.guard, out);
            for update in &transition.updates {
                collect_enum_types_from_expr(&update.value, out);
            }
            if let Some(postcondition) = &transition.postcondition {
                collect_enum_types_from_expr(postcondition, out);
            }
        }
        for derived in &entity.derived_fields {
            collect_enum_types_from_ty(&derived.ty, out);
            collect_enum_types_from_expr(&derived.body, out);
        }
        for invariant in &entity.invariants {
            collect_enum_types_from_expr(&invariant.body, out);
        }
    }
    for interface in &ir.interfaces {
        for command in &interface.commands {
            for param in &command.params {
                collect_enum_types_from_ty(&param.ty, out);
            }
            if let Some(return_type) = &command.return_type {
                collect_enum_types_from_ty(return_type, out);
            }
        }
        for query in &interface.queries {
            for param in &query.params {
                collect_enum_types_from_ty(&param.ty, out);
            }
            collect_enum_types_from_ty(&query.return_type, out);
        }
    }
    for system in &ir.systems {
        collect_enum_types_from_fields(&system.fields, out);
        for command in &system.commands {
            for param in &command.params {
                collect_enum_types_from_ty(&param.ty, out);
            }
            if let Some(return_type) = &command.return_type {
                collect_enum_types_from_ty(return_type, out);
            }
        }
        for action in &system.actions {
            for param in &action.params {
                collect_enum_types_from_ty(&param.ty, out);
            }
            collect_enum_types_from_expr(&action.guard, out);
            for op in &action.body {
                collect_enum_types_from_action(op, out);
            }
            if let Some(return_expr) = &action.return_expr {
                collect_enum_types_from_expr(return_expr, out);
            }
        }
        for derived in &system.derived_fields {
            collect_enum_types_from_ty(&derived.ty, out);
            collect_enum_types_from_expr(&derived.body, out);
        }
        for invariant in &system.invariants {
            collect_enum_types_from_expr(&invariant.body, out);
        }
        for query in &system.queries {
            for param in &query.params {
                collect_enum_types_from_ty(&param.ty, out);
            }
            for requires in &query.requires {
                collect_enum_types_from_expr(requires, out);
            }
            collect_enum_types_from_expr(&query.body, out);
        }
        for pred in &system.preds {
            collect_enum_types_from_ty(&pred.ty, out);
            collect_enum_types_from_expr(&pred.body, out);
        }
        for proc in &system.procs {
            for param in &proc.params {
                collect_enum_types_from_ty(&param.ty, out);
            }
            if let Some(requires) = &proc.requires {
                collect_enum_types_from_expr(requires, out);
            }
            for node in &proc.nodes {
                for arg in &node.args {
                    collect_enum_types_from_expr(arg, out);
                }
            }
        }
    }
    for verify in &ir.verifies {
        for constraint in &verify.initial_constraints {
            collect_enum_types_from_expr(constraint, out);
        }
        for assert in &verify.asserts {
            collect_enum_types_from_expr(assert, out);
        }
    }
    for theorem in &ir.theorems {
        for invariant in &theorem.invariants {
            collect_enum_types_from_expr(invariant, out);
        }
        for show in &theorem.shows {
            collect_enum_types_from_expr(show, out);
        }
    }
    for axiom in &ir.axioms {
        collect_enum_types_from_expr(&axiom.body, out);
    }
    for lemma in &ir.lemmas {
        for body in &lemma.body {
            collect_enum_types_from_expr(body, out);
        }
    }
    for scene in &ir.scenes {
        for given in &scene.givens {
            collect_enum_types_from_expr(&given.constraint, out);
        }
        for event in &scene.events {
            for arg in &event.args {
                collect_enum_types_from_expr(arg, out);
            }
        }
        for ordering in &scene.ordering {
            collect_enum_types_from_expr(ordering, out);
        }
        for assertion in &scene.assertions {
            collect_enum_types_from_expr(assertion, out);
        }
        for constraint in &scene.given_constraints {
            collect_enum_types_from_expr(constraint, out);
        }
    }
}

fn collect_enum_types_from_fields<'a>(
    fields: &'a [crate::ir::types::IRField],
    out: &mut Vec<&'a IRType>,
) {
    for field in fields {
        collect_enum_types_from_ty(&field.ty, out);
        if let Some(default) = &field.default {
            collect_enum_types_from_expr(default, out);
        }
        if let Some(initial_constraint) = &field.initial_constraint {
            collect_enum_types_from_expr(initial_constraint, out);
        }
    }
}

fn collect_enum_types_from_ty<'a>(ty: &'a IRType, out: &mut Vec<&'a IRType>) {
    match ty {
        IRType::Enum { variants, .. } => {
            out.push(ty);
            for variant in variants {
                for field in &variant.fields {
                    collect_enum_types_from_ty(&field.ty, out);
                }
            }
        }
        IRType::Record { fields, .. } => {
            for field in fields {
                collect_enum_types_from_ty(&field.ty, out);
            }
        }
        IRType::Fn { param, result } => {
            collect_enum_types_from_ty(param, out);
            collect_enum_types_from_ty(result, out);
        }
        IRType::Set { element } | IRType::Seq { element } => {
            collect_enum_types_from_ty(element, out);
        }
        IRType::Map { key, value } => {
            collect_enum_types_from_ty(key, out);
            collect_enum_types_from_ty(value, out);
        }
        IRType::Tuple { elements } => {
            for element in elements {
                collect_enum_types_from_ty(element, out);
            }
        }
        IRType::Refinement { base, predicate } => {
            collect_enum_types_from_ty(base, out);
            collect_enum_types_from_expr(predicate, out);
        }
        IRType::Int
        | IRType::Bool
        | IRType::String
        | IRType::Identity
        | IRType::Real
        | IRType::Float
        | IRType::Entity { .. } => {}
    }
}

fn collect_enum_types_from_expr<'a>(expr: &'a IRExpr, out: &mut Vec<&'a IRType>) {
    match expr {
        IRExpr::Lit { ty, .. } | IRExpr::Var { ty, .. } => {
            collect_enum_types_from_ty(ty, out);
        }
        IRExpr::Ctor { args, .. } => {
            for (_, arg) in args {
                collect_enum_types_from_expr(arg, out);
            }
        }
        IRExpr::BinOp {
            left, right, ty, ..
        } => {
            collect_enum_types_from_ty(ty, out);
            collect_enum_types_from_expr(left, out);
            collect_enum_types_from_expr(right, out);
        }
        IRExpr::Until { left, right, .. } | IRExpr::Since { left, right, .. } => {
            collect_enum_types_from_expr(left, out);
            collect_enum_types_from_expr(right, out);
        }
        IRExpr::UnOp { operand, ty, .. } => {
            collect_enum_types_from_ty(ty, out);
            collect_enum_types_from_expr(operand, out);
        }
        IRExpr::App { func, arg, ty, .. } => {
            collect_enum_types_from_ty(ty, out);
            collect_enum_types_from_expr(func, out);
            collect_enum_types_from_expr(arg, out);
        }
        IRExpr::Lam {
            param_type, body, ..
        } => {
            collect_enum_types_from_ty(param_type, out);
            collect_enum_types_from_expr(body, out);
        }
        IRExpr::Let { bindings, body, .. } => {
            for binding in bindings {
                collect_enum_types_from_ty(&binding.ty, out);
                collect_enum_types_from_expr(&binding.expr, out);
            }
            collect_enum_types_from_expr(body, out);
        }
        IRExpr::Forall { domain, body, .. }
        | IRExpr::Exists { domain, body, .. }
        | IRExpr::One { domain, body, .. }
        | IRExpr::Lone { domain, body, .. } => {
            collect_enum_types_from_ty(domain, out);
            collect_enum_types_from_expr(body, out);
        }
        IRExpr::Field { expr, ty, .. } => {
            collect_enum_types_from_ty(ty, out);
            collect_enum_types_from_expr(expr, out);
        }
        IRExpr::Prime { expr, .. }
        | IRExpr::Always { body: expr, .. }
        | IRExpr::Eventually { body: expr, .. }
        | IRExpr::Historically { body: expr, .. }
        | IRExpr::Once { body: expr, .. }
        | IRExpr::Previously { body: expr, .. }
        | IRExpr::Card { expr, .. }
        | IRExpr::Assert { expr, .. }
        | IRExpr::Assume { expr, .. } => {
            collect_enum_types_from_expr(expr, out);
        }
        IRExpr::Aggregate {
            domain,
            body,
            in_filter,
            ..
        } => {
            collect_enum_types_from_ty(domain, out);
            collect_enum_types_from_expr(body, out);
            if let Some(in_filter) = in_filter {
                collect_enum_types_from_expr(in_filter, out);
            }
        }
        IRExpr::Saw { args, .. } => {
            for arg in args.iter().flatten() {
                collect_enum_types_from_expr(arg, out);
            }
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            collect_enum_types_from_expr(scrutinee, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_enum_types_from_expr(guard, out);
                }
                collect_enum_types_from_expr(&arm.body, out);
            }
        }
        IRExpr::Choose {
            domain,
            predicate,
            ty,
            ..
        } => {
            collect_enum_types_from_ty(domain, out);
            collect_enum_types_from_ty(ty, out);
            if let Some(predicate) = predicate {
                collect_enum_types_from_expr(predicate, out);
            }
        }
        IRExpr::MapUpdate {
            map,
            key,
            value,
            ty,
            ..
        } => {
            collect_enum_types_from_ty(ty, out);
            collect_enum_types_from_expr(map, out);
            collect_enum_types_from_expr(key, out);
            collect_enum_types_from_expr(value, out);
        }
        IRExpr::Index { map, key, ty, .. } => {
            collect_enum_types_from_ty(ty, out);
            collect_enum_types_from_expr(map, out);
            collect_enum_types_from_expr(key, out);
        }
        IRExpr::SetLit { elements, ty, .. }
        | IRExpr::SeqLit { elements, ty, .. }
        | IRExpr::Tuple { elements, ty, .. } => {
            collect_enum_types_from_ty(ty, out);
            for element in elements {
                collect_enum_types_from_expr(element, out);
            }
        }
        IRExpr::MapLit { entries, ty, .. } => {
            collect_enum_types_from_ty(ty, out);
            for (key, value) in entries {
                collect_enum_types_from_expr(key, out);
                collect_enum_types_from_expr(value, out);
            }
        }
        IRExpr::SetComp {
            domain,
            source,
            filter,
            projection,
            ty,
            ..
        } => {
            collect_enum_types_from_ty(domain, out);
            collect_enum_types_from_ty(ty, out);
            if let Some(source) = source {
                collect_enum_types_from_expr(source, out);
            }
            collect_enum_types_from_expr(filter, out);
            if let Some(projection) = projection {
                collect_enum_types_from_expr(projection, out);
            }
        }
        IRExpr::RelComp {
            projection,
            bindings,
            filter,
            ty,
            ..
        } => {
            collect_enum_types_from_ty(ty, out);
            collect_enum_types_from_expr(projection, out);
            for binding in bindings {
                collect_enum_types_from_ty(&binding.domain, out);
                if let Some(source) = &binding.source {
                    collect_enum_types_from_expr(source, out);
                }
            }
            collect_enum_types_from_expr(filter, out);
        }
        IRExpr::Block { exprs, .. } => {
            for expr in exprs {
                collect_enum_types_from_expr(expr, out);
            }
        }
        IRExpr::VarDecl { ty, init, rest, .. } => {
            collect_enum_types_from_ty(ty, out);
            collect_enum_types_from_expr(init, out);
            collect_enum_types_from_expr(rest, out);
        }
        IRExpr::While {
            cond,
            invariants,
            decreases,
            body,
            ..
        } => {
            collect_enum_types_from_expr(cond, out);
            for invariant in invariants {
                collect_enum_types_from_expr(invariant, out);
            }
            if let Some(decreases) = decreases {
                collect_enum_types_from_decreases(decreases, out);
            }
            collect_enum_types_from_expr(body, out);
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            collect_enum_types_from_expr(cond, out);
            collect_enum_types_from_expr(then_body, out);
            if let Some(else_body) = else_body {
                collect_enum_types_from_expr(else_body, out);
            }
        }
        IRExpr::Sorry { .. } | IRExpr::Todo { .. } => {}
    }
}

fn collect_enum_types_from_action<'a>(action: &'a IRAction, out: &mut Vec<&'a IRType>) {
    match action {
        IRAction::Choose { filter, ops, .. } => {
            collect_enum_types_from_expr(filter, out);
            for op in ops {
                collect_enum_types_from_action(op, out);
            }
        }
        IRAction::ForAll { ops, .. } => {
            for op in ops {
                collect_enum_types_from_action(op, out);
            }
        }
        IRAction::Create { fields, .. } => {
            for field in fields {
                collect_enum_types_from_expr(&field.value, out);
            }
        }
        IRAction::LetCrossCall { args, .. } | IRAction::CrossCall { args, .. } => {
            for arg in args {
                collect_enum_types_from_expr(arg, out);
            }
        }
        IRAction::Apply { args, .. } => {
            for arg in args {
                collect_enum_types_from_expr(arg, out);
            }
        }
        IRAction::Match { arms, .. } => {
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_enum_types_from_expr(guard, out);
                }
                for op in &arm.body {
                    collect_enum_types_from_action(op, out);
                }
            }
        }
        IRAction::ExprStmt { expr } => collect_enum_types_from_expr(expr, out),
    }
}

fn collect_enum_types_from_decreases<'a>(decreases: &'a IRDecreases, out: &mut Vec<&'a IRType>) {
    for measure in &decreases.measures {
        collect_enum_types_from_expr(measure, out);
    }
}

// ── Verification context ────────────────────────────────────────────

/// All metadata needed for Z3 encoding, extracted from the IR.
///
/// Built once per verification run. Shared across all verify/scene/theorem checks.
pub struct VerifyContext {
    /// Enum variant → integer ID mapping (for fieldless enums)
    pub variants: VariantMap,
    /// Enum type → (`min_id`, `max_id`) for domain constraints
    pub enum_ranges: HashMap<String, (i64, i64)>,
    /// Entity name → field/action metadata
    pub entities: HashMap<String, EntityInfo>,
    /// Z3 algebraic datatypes for enums with constructor fields.
    /// Maps enum name → `DatatypeSort` (sort + variant constructors/testers/accessors).
    pub adt_sorts: HashMap<String, DatatypeSort>,
    /// command parameter metadata for `saw` encoding.
    /// Maps `(system_name, command_name)` → parameter list.
    /// Populated from executable command clauses (`IRSystemAction` after
    /// elaboration/lowering). Deduplicated by command name within each
    /// system because repeated guarded clauses share the same command
    /// signature.
    pub command_params: HashMap<(String, String), Vec<crate::ir::types::IRTransParam>>,
    /// System query declarations for slot-scoped guard encoding.
    /// Maps `(system_name, query_name)` → query declaration.
    pub system_queries: HashMap<(String, String), IRQuery>,
    /// Shared pure-definition environment.
    pub defs: DefEnv,
}

impl VerifyContext {
    /// Build a `VerifyContext` from an IR program.
    pub fn from_ir(ir: &IRProgram) -> Self {
        let mut variants = VariantMap::new();
        let mut enum_ranges = HashMap::new();
        let mut entities = HashMap::new();
        let mut adt_sorts = HashMap::new();

        // Register all enum types. Most lowered programs list named enums in
        // `ir.types`, but verifier tests and some generated IR paths can carry
        // enum definitions structurally on fields, params, or expression type
        // annotations. Treat those structural definitions as authoritative
        // metadata too, so every encoder sees the same variant map.
        let mut enum_types = Vec::new();
        collect_program_enum_types(ir, &mut enum_types);
        for ty in enum_types {
            register_enum_type(ty, &mut variants, &mut enum_ranges, &mut adt_sorts);
        }

        // Register all entities
        for entity in &ir.entities {
            let fields = entity
                .fields
                .iter()
                .map(|f| FieldInfo {
                    name: f.name.clone(),
                    ty: f.ty.clone(),
                    default: f.default.clone(),
                })
                .collect();

            let actions = entity
                .transitions
                .iter()
                .map(|t| ActionInfo {
                    name: t.name.clone(),
                    entity: entity.name.clone(),
                    param_count: t.refs.len() + t.params.len(),
                })
                .collect();

            entities.insert(
                entity.name.clone(),
                EntityInfo {
                    name: entity.name.clone(),
                    fields,
                    actions,
                },
            );
        }

        // Collect command parameter metadata from executable clauses.
        // Deduplicate by command name within each system.
        let mut command_params = HashMap::new();
        let mut system_queries = HashMap::new();
        let mut seen = std::collections::HashSet::new();
        for system in &ir.systems {
            seen.clear();
            for step in &system.actions {
                if seen.insert(step.name.clone()) {
                    command_params.insert(
                        (system.name.clone(), step.name.clone()),
                        step.params.clone(),
                    );
                }
            }
            for query in &system.queries {
                system_queries.insert((system.name.clone(), query.name.clone()), query.clone());
            }
        }

        Self {
            variants,
            enum_ranges,
            entities,
            adt_sorts,
            command_params,
            system_queries,
            defs: DefEnv::from_ir(ir),
        }
    }
}

fn default_expr_to_string(expr: &IRExpr) -> Option<String> {
    match expr {
        IRExpr::Lit { value, .. } => Some(lit_value_to_string(value)),
        IRExpr::Ctor { ctor, args, .. } => {
            if args.is_empty() {
                Some(format!("@{ctor}"))
            } else {
                let fields = args
                    .iter()
                    .map(|(name, value)| {
                        default_expr_to_string(value).map(|value| format!("{name}: {value}"))
                    })
                    .collect::<Option<Vec<_>>>()?
                    .join(", ");
                Some(format!("@{ctor} {{ {fields} }}"))
            }
        }
        IRExpr::Var { name, .. } => Some(name.clone()),
        IRExpr::Field { expr, field, .. } => {
            default_expr_to_string(expr).map(|expr| format!("{expr}.{field}"))
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => Some(format!(
            "({} {} {})",
            default_expr_to_string(left)?,
            default_binop_symbol(op),
            default_expr_to_string(right)?
        )),
        IRExpr::UnOp { op, operand, .. } => {
            let operand = default_expr_to_string(operand)?;
            match default_unop_symbol(op) {
                "not" => Some(format!("not {operand}")),
                "-" => Some(format!("-{operand}")),
                symbol => Some(format!("{symbol}{operand}")),
            }
        }
        IRExpr::Let { bindings, body, .. } => {
            let bindings = bindings
                .iter()
                .map(|binding| {
                    default_expr_to_string(&binding.expr)
                        .map(|expr| format!("{} = {expr}", binding.name))
                })
                .collect::<Option<Vec<_>>>()?
                .join("; ");
            Some(format!(
                "let {bindings} in {}",
                default_expr_to_string(body)?
            ))
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let else_body = else_body.as_ref()?;
            Some(format!(
                "if {} {{ {} }} else {{ {} }}",
                default_expr_to_string(cond)?,
                default_expr_to_string(then_body)?,
                default_expr_to_string(else_body)?
            ))
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            let arms = arms
                .iter()
                .map(default_match_arm_to_string)
                .collect::<Option<Vec<_>>>()?
                .join("; ");
            Some(format!(
                "match {} {{ {arms} }}",
                default_expr_to_string(scrutinee)?
            ))
        }
        IRExpr::SetLit { elements, .. } => {
            default_expr_list_to_string(elements).map(|elements| format!("Set({elements})"))
        }
        IRExpr::SeqLit { elements, .. } => {
            default_expr_list_to_string(elements).map(|elements| format!("[{elements}]"))
        }
        IRExpr::MapLit { entries, .. } => entries
            .iter()
            .map(|(key, value)| {
                Some(format!(
                    "{}: {}",
                    default_expr_to_string(key)?,
                    default_expr_to_string(value)?
                ))
            })
            .collect::<Option<Vec<_>>>()
            .map(|entries| format!("Map({})", entries.join(", "))),
        _ => None,
    }
}

fn default_expr_list_to_string(elements: &[IRExpr]) -> Option<String> {
    elements
        .iter()
        .map(default_expr_to_string)
        .collect::<Option<Vec<_>>>()
        .map(|elements| elements.join(", "))
}

fn default_match_arm_to_string(arm: &IRMatchArm) -> Option<String> {
    let pattern = default_pattern_to_string(&arm.pattern)?;
    let guard = match &arm.guard {
        Some(guard) => format!(" if {}", default_expr_to_string(guard)?),
        None => String::new(),
    };
    Some(format!(
        "{pattern}{guard} => {}",
        default_expr_to_string(&arm.body)?
    ))
}

fn default_pattern_to_string(pattern: &IRPattern) -> Option<String> {
    match pattern {
        IRPattern::PVar { name } => Some(name.clone()),
        IRPattern::PWild => Some("_".to_owned()),
        IRPattern::PCtor { name, fields } => {
            if fields.is_empty() {
                return Some(name.clone());
            }
            let fields = fields
                .iter()
                .map(|field| {
                    default_pattern_to_string(&field.pattern)
                        .map(|pattern| format!("{}: {pattern}", field.name))
                })
                .collect::<Option<Vec<_>>>()?
                .join(", ");
            Some(format!("{name} {{ {fields} }}"))
        }
        IRPattern::POr { left, right } => Some(format!(
            "{} | {}",
            default_pattern_to_string(left)?,
            default_pattern_to_string(right)?
        )),
    }
}

fn lit_value_to_string(value: &LitVal) -> String {
    match value {
        LitVal::Int { value } => value.to_string(),
        LitVal::Real { value } | LitVal::Float { value } => value.to_string(),
        LitVal::Bool { value } => value.to_string(),
        LitVal::Str { value } => format!("{value:?}"),
    }
}

fn default_binop_symbol(op: &str) -> &str {
    match op {
        "OpEq" => "==",
        "OpNeq" => "!=",
        "OpAnd" => "and",
        "OpOr" => "or",
        "OpImplies" => "implies",
        "OpLt" => "<",
        "OpLe" => "<=",
        "OpGt" => ">",
        "OpGe" => ">=",
        "OpAdd" => "+",
        "OpSub" => "-",
        "OpMul" => "*",
        "OpDiv" => "/",
        "OpMod" => "%",
        other => other,
    }
}

fn default_unop_symbol(op: &str) -> &str {
    match op {
        "OpNot" => "not",
        "OpNeg" => "-",
        other => other,
    }
}

#[cfg(test)]
mod default_tests {
    use super::*;
    use crate::ir::types::{
        IREntity, IRExpr, IRField, IRProgram, IRType, IRTypeEntry, IRVariant, LitVal,
    };

    #[test]
    fn pure_scene_from_ir_preserves_entity_field_defaults() {
        let status_ty = IRType::Enum {
            name: "Status".to_owned(),
            variants: vec![IRVariant::simple("Open"), IRVariant::simple("Closed")],
        };
        let ir = IRProgram {
            interfaces: vec![],
            types: vec![IRTypeEntry {
                name: "Status".to_owned(),
                ty: status_ty.clone(),
            }],
            constants: vec![],
            functions: vec![],
            entities: vec![IREntity {
                name: "Ticket".to_owned(),
                fields: vec![
                    IRField {
                        name: "status".to_owned(),
                        ty: status_ty,
                        default: Some(IRExpr::Ctor {
                            enum_name: "Status".to_owned(),
                            ctor: "Open".to_owned(),
                            args: vec![],
                            span: None,
                        }),
                        initial_constraint: None,
                    },
                    IRField {
                        name: "active".to_owned(),
                        ty: IRType::Bool,
                        default: Some(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        }),
                        initial_constraint: None,
                    },
                    IRField {
                        name: "count".to_owned(),
                        ty: IRType::Int,
                        default: Some(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 3 },
                            span: None,
                        }),
                        initial_constraint: None,
                    },
                ],
                transitions: vec![],
                derived_fields: vec![],
                invariants: vec![],
                fsm_decls: vec![],
            }],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };

        let vctx = VerifyContext::from_ir(&ir);
        let ticket = vctx.entities.get("Ticket").expect("Ticket metadata");
        let default_for = |field_name: &str| {
            ticket
                .fields
                .iter()
                .find(|field| field.name == field_name)
                .and_then(FieldInfo::default_display)
        };

        assert_eq!(default_for("status"), Some("@Open".to_owned()));
        assert_eq!(default_for("active"), Some("true".to_owned()));
        assert_eq!(default_for("count"), Some("3".to_owned()));
        assert!(matches!(
            ticket
                .fields
                .iter()
                .find(|field| field.name == "status")
                .and_then(FieldInfo::default_expr),
            Some(IRExpr::Ctor { ctor, .. }) if ctor == "Open"
        ));
    }

    #[test]
    fn pure_scene_default_display_covers_structured_exprs_without_debug_fallback() {
        let bool_lit = IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        };
        let var = IRExpr::Var {
            name: "order".to_owned(),
            ty: IRType::Entity {
                name: "Order".to_owned(),
            },
            span: None,
        };
        assert_eq!(
            default_expr_to_string(&IRExpr::Field {
                expr: Box::new(var),
                field: "status".to_owned(),
                ty: IRType::Bool,
                span: None,
            }),
            Some("order.status".to_owned())
        );
        assert_eq!(
            default_expr_to_string(&IRExpr::UnOp {
                op: "OpNot".to_owned(),
                operand: Box::new(bool_lit.clone()),
                ty: IRType::Bool,
                span: None,
            }),
            Some("not true".to_owned())
        );
        assert_eq!(
            default_expr_to_string(&IRExpr::BinOp {
                op: "OpAnd".to_owned(),
                left: Box::new(bool_lit.clone()),
                right: Box::new(bool_lit.clone()),
                ty: IRType::Bool,
                span: None,
            }),
            Some("(true and true)".to_owned())
        );
        assert_eq!(
            default_expr_to_string(&IRExpr::Let {
                bindings: vec![crate::ir::types::LetBinding {
                    name: "ok".to_owned(),
                    ty: IRType::Bool,
                    expr: bool_lit.clone(),
                }],
                body: Box::new(IRExpr::Var {
                    name: "ok".to_owned(),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            Some("let ok = true in ok".to_owned())
        );
        assert_eq!(
            default_expr_to_string(&IRExpr::IfElse {
                cond: Box::new(bool_lit.clone()),
                then_body: Box::new(bool_lit.clone()),
                else_body: Some(Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: false },
                    span: None,
                })),
                span: None,
            }),
            Some("if true { true } else { false }".to_owned())
        );
        assert_eq!(
            default_expr_to_string(&IRExpr::Match {
                scrutinee: Box::new(IRExpr::Ctor {
                    enum_name: "Decision".to_owned(),
                    ctor: "Accept".to_owned(),
                    args: vec![("allowed".to_owned(), bool_lit.clone())],
                    span: None,
                }),
                arms: vec![
                    IRMatchArm {
                        pattern: IRPattern::PCtor {
                            name: "Accept".to_owned(),
                            fields: vec![crate::ir::types::IRFieldPat {
                                name: "allowed".to_owned(),
                                pattern: IRPattern::PVar {
                                    name: "accepted".to_owned(),
                                },
                            }],
                        },
                        guard: None,
                        body: IRExpr::Var {
                            name: "accepted".to_owned(),
                            ty: IRType::Bool,
                            span: None,
                        },
                    },
                    IRMatchArm {
                        pattern: IRPattern::PCtor {
                            name: "Reject".to_owned(),
                            fields: vec![],
                        },
                        guard: None,
                        body: IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: false },
                            span: None,
                        },
                    },
                ],
                span: None,
            }),
            Some(
                "match @Accept { allowed: true } { Accept { allowed: accepted } => accepted; Reject => false }"
                    .to_owned()
            )
        );
        assert_eq!(
            default_expr_to_string(&IRExpr::Ctor {
                enum_name: "Decision".to_owned(),
                ctor: "Accept".to_owned(),
                args: vec![("allowed".to_owned(), bool_lit.clone())],
                span: None,
            }),
            Some("@Accept { allowed: true }".to_owned())
        );
        assert_eq!(
            default_expr_to_string(&IRExpr::SetLit {
                elements: vec![bool_lit.clone()],
                ty: IRType::Set {
                    element: Box::new(IRType::Bool),
                },
                span: None,
            }),
            Some("Set(true)".to_owned())
        );
        assert_eq!(
            default_expr_to_string(&IRExpr::SeqLit {
                elements: vec![bool_lit.clone()],
                ty: IRType::Seq {
                    element: Box::new(IRType::Bool),
                },
                span: None,
            }),
            Some("[true]".to_owned())
        );
        assert_eq!(
            default_expr_to_string(&IRExpr::MapLit {
                entries: vec![(bool_lit.clone(), bool_lit.clone())],
                ty: IRType::Map {
                    key: Box::new(IRType::Bool),
                    value: Box::new(IRType::Bool),
                },
                span: None,
            }),
            Some("Map(true: true)".to_owned())
        );
        assert_eq!(
            default_expr_to_string(&IRExpr::IfElse {
                cond: Box::new(bool_lit.clone()),
                then_body: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                }),
                else_body: None,
                span: None,
            }),
            None
        );
    }
}

#[cfg(test)]
mod tests {
    use super::{VariantMap, VerifyContext};
    use crate::ir::types::{
        IRConst, IRExpr, IRField, IRProgram, IRSystem, IRSystemAction, IRTransParam, IRType,
        IRTypeEntry, IRVariant, IRVariantField, LitVal,
    };

    fn empty_program() -> IRProgram {
        IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![],
            interfaces: vec![],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        }
    }

    fn empty_system(name: &str) -> IRSystem {
        IRSystem {
            name: name.to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: vec![],
            commands: vec![],
            actions: vec![],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        }
    }

    fn enum_ty(name: &str, variants: &[&str]) -> IRType {
        IRType::Enum {
            name: name.to_owned(),
            variants: variants
                .iter()
                .map(|variant| IRVariant::simple(*variant))
                .collect(),
        }
    }

    #[test]
    fn try_id_of_returns_error_for_unknown_variant() {
        let mut variants = VariantMap::new();
        let range = variants.register_enum("Status", &["Pending".to_owned(), "Done".to_owned()]);
        assert_eq!(range, (0, 1));

        assert_eq!(variants.try_id_of("Status", "Pending"), Ok(0));
        assert_eq!(
            variants.try_id_of("Status", "Missing"),
            Err("unknown variant: Status::Missing".to_owned())
        );
    }

    #[test]
    fn pure_scene_verify_context_registers_enum_from_system_field_type_once() {
        let status = enum_ty("Status", &["Pending", "Done"]);
        let mut system = empty_system("Workflow");
        system.fields.push(IRField {
            name: "status".to_owned(),
            ty: status.clone(),
            default: None,
            initial_constraint: None,
        });
        let mut program = empty_program();
        program.types.push(crate::ir::types::IRTypeEntry {
            name: "Status".to_owned(),
            ty: status,
        });
        program.systems.push(system);

        let vctx = VerifyContext::from_ir(&program);

        assert_eq!(vctx.variants.try_id_of("Status", "Pending"), Ok(0));
        assert_eq!(vctx.variants.try_id_of("Status", "Done"), Ok(1));
        assert_eq!(vctx.enum_ranges.get("Status"), Some(&(0, 1)));
    }

    #[test]
    fn pure_scene_verify_context_registers_enum_from_system_action_param_type() {
        let mode = enum_ty("Mode", &["Off", "On"]);
        let mut system = empty_system("Switch");
        system.actions.push(IRSystemAction {
            name: "set_mode".to_owned(),
            params: vec![IRTransParam {
                name: "next_mode".to_owned(),
                ty: mode,
            }],
            guard: crate::ir::types::IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            body: vec![],
            return_expr: None,
        });
        let mut program = empty_program();
        program.systems.push(system);

        let vctx = VerifyContext::from_ir(&program);

        assert_eq!(vctx.variants.try_id_of("Mode", "Off"), Ok(0));
        assert_eq!(vctx.variants.try_id_of("Mode", "On"), Ok(1));
    }

    #[test]
    fn pure_scene_verify_context_registers_payload_enum_adt_sorts() {
        let result = IRType::Enum {
            name: "Result".to_owned(),
            variants: vec![IRVariant {
                name: "Some".to_owned(),
                fields: vec![IRVariantField {
                    name: "value".to_owned(),
                    ty: IRType::Int,
                }],
            }],
        };
        let mut program = empty_program();
        program.types.push(IRTypeEntry {
            name: "Result".to_owned(),
            ty: result,
        });

        let vctx = VerifyContext::from_ir(&program);

        assert_eq!(vctx.variants.try_id_of("Result", "Some"), Ok(0));
        assert!(
            vctx.adt_sorts.contains_key("Result"),
            "payload enums should register an ADT sort"
        );
    }

    #[test]
    fn pure_scene_verify_context_collects_enum_types_from_expression_annotations() {
        let status = enum_ty("Status", &["Pending", "Done"]);
        let mut program = empty_program();
        program.constants.push(IRConst {
            name: "status_seen".to_owned(),
            ty: IRType::Bool,
            value: IRExpr::Var {
                name: "status".to_owned(),
                ty: status,
                span: None,
            },
        });

        let vctx = VerifyContext::from_ir(&program);

        assert_eq!(vctx.variants.try_id_of("Status", "Pending"), Ok(0));
        assert_eq!(vctx.variants.try_id_of("Status", "Done"), Ok(1));
    }
}
