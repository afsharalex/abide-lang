//! Core IR types for Abide.
//!
//! Fully resolved, fully typed, desugared representation.
//! Consumed by: model checker, SMT solver, Agda emitter, simulator.

use serde::{Deserialize, Serialize};

use crate::span::Span;

// ── Types ────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(tag = "tag")]
pub enum IRType {
    Int,
    Bool,
    String,
    Identity,
    Real,
    Float,
    Enum {
        name: std::string::String,
        variants: Vec<IRVariant>,
    },
    Record {
        name: std::string::String,
        fields: Vec<IRRecordField>,
    },
    Fn {
        param: Box<IRType>,
        result: Box<IRType>,
    },
    Entity {
        name: std::string::String,
    },
    Set {
        element: Box<IRType>,
    },
    Seq {
        element: Box<IRType>,
    },
    Map {
        key: Box<IRType>,
        value: Box<IRType>,
    },
    Tuple {
        elements: Vec<IRType>,
    },
    Refinement {
        base: Box<IRType>,
        predicate: Box<IRExpr>,
    },
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRRecordField {
    pub name: std::string::String,
    #[serde(rename = "type")]
    pub ty: IRType,
}

/// A constructor variant of an enum type.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRVariant {
    pub name: std::string::String,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub fields: Vec<IRVariantField>,
}

/// A field within a constructor variant.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRVariantField {
    pub name: std::string::String,
    #[serde(rename = "type")]
    pub ty: IRType,
}

impl IRVariant {
    /// Create a fieldless variant (simple enum constructor).
    pub fn simple(name: impl Into<std::string::String>) -> Self {
        Self {
            name: name.into(),
            fields: vec![],
        }
    }
}

impl IRType {
    /// For Enum types, return variant names as strings (convenience accessor).
    pub fn enum_variant_names(&self) -> Vec<&str> {
        match self {
            IRType::Enum { variants, .. } => variants.iter().map(|v| v.name.as_str()).collect(),
            _ => vec![],
        }
    }

    /// For Enum types, check if any variant has fields.
    pub fn has_variant_fields(&self) -> bool {
        match self {
            IRType::Enum { variants, .. } => variants.iter().any(|v| !v.fields.is_empty()),
            _ => false,
        }
    }
}

// ── Expressions ──────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(tag = "tag")]
pub enum IRExpr {
    Lit {
        #[serde(rename = "type")]
        ty: IRType,
        value: LitVal,
        #[serde(skip)]
        span: Option<Span>,
    },
    Var {
        name: std::string::String,
        #[serde(rename = "type")]
        ty: IRType,
        #[serde(skip)]
        span: Option<Span>,
    },
    Ctor {
        #[serde(rename = "enum")]
        enum_name: std::string::String,
        ctor: std::string::String,
        /// Field arguments for record constructors (e.g., `@Some { value: 1 }`).
        /// Empty for fieldless constructors.
        #[serde(skip_serializing_if = "Vec::is_empty")]
        args: Vec<(std::string::String, IRExpr)>,
        #[serde(skip)]
        span: Option<Span>,
    },
    BinOp {
        op: std::string::String,
        left: Box<IRExpr>,
        right: Box<IRExpr>,
        #[serde(rename = "type")]
        ty: IRType,
        #[serde(skip)]
        span: Option<Span>,
    },
    UnOp {
        op: std::string::String,
        operand: Box<IRExpr>,
        #[serde(rename = "type")]
        ty: IRType,
        #[serde(skip)]
        span: Option<Span>,
    },
    /// Expression-level application.
    ///
    /// This is the generic IR node for pure call-like expression forms:
    ///
    /// - top-level `fn` / `pred` application
    /// - system-local predicate application after qualification
    /// - query evaluation
    ///
    /// It is intentionally **not** used for operational event/command
    /// occurrence. Those lower through dedicated operational nodes such as
    /// `IRAction::{Apply,CrossCall,...}` and `IRSceneEvent`.
    App {
        func: Box<IRExpr>,
        arg: Box<IRExpr>,
        #[serde(rename = "type")]
        ty: IRType,
        #[serde(skip)]
        span: Option<Span>,
    },
    Lam {
        param: std::string::String,
        #[serde(rename = "paramType")]
        param_type: IRType,
        body: Box<IRExpr>,
        #[serde(skip)]
        span: Option<Span>,
    },
    Let {
        bindings: Vec<LetBinding>,
        body: Box<IRExpr>,
        #[serde(skip)]
        span: Option<Span>,
    },
    Forall {
        var: std::string::String,
        domain: IRType,
        body: Box<IRExpr>,
        #[serde(skip)]
        span: Option<Span>,
    },
    Exists {
        var: std::string::String,
        domain: IRType,
        body: Box<IRExpr>,
        #[serde(skip)]
        span: Option<Span>,
    },
    /// `one x: T | P(x)` — exactly one x satisfies P.
    One {
        var: std::string::String,
        domain: IRType,
        body: Box<IRExpr>,
        #[serde(skip)]
        span: Option<Span>,
    },
    /// `lone x: T | P(x)` — at most one x satisfies P.
    Lone {
        var: std::string::String,
        domain: IRType,
        body: Box<IRExpr>,
        #[serde(skip)]
        span: Option<Span>,
    },
    Field {
        expr: Box<IRExpr>,
        field: std::string::String,
        #[serde(rename = "type")]
        ty: IRType,
        #[serde(skip)]
        span: Option<Span>,
    },
    Prime {
        expr: Box<IRExpr>,
        #[serde(skip)]
        span: Option<Span>,
    },
    Always {
        body: Box<IRExpr>,
        #[serde(skip)]
        span: Option<Span>,
    },
    Eventually {
        body: Box<IRExpr>,
        #[serde(skip)]
        span: Option<Span>,
    },
    /// `P until Q` — P holds at every step until Q becomes true.
    Until {
        left: Box<IRExpr>,
        right: Box<IRExpr>,
        #[serde(skip)]
        span: Option<Span>,
    },
    /// `historically P` — P held at every past
    /// step (including the current one). Past-time dual of `always`.
    Historically {
        body: Box<IRExpr>,
        #[serde(skip)]
        span: Option<Span>,
    },
    /// `once P` — P held at some past step
    /// (including the current one). Past-time dual of `eventually`.
    Once {
        body: Box<IRExpr>,
        #[serde(skip)]
        span: Option<Span>,
    },
    /// `previously P` — P held in the immediately
    /// previous step. False at trace position 0. Past-time dual of `next`.
    Previously {
        body: Box<IRExpr>,
        #[serde(skip)]
        span: Option<Span>,
    },
    /// `P since Q` — Q held at some past step and
    /// P held continuously from that point to now. Past-time dual of `until`.
    Since {
        left: Box<IRExpr>,
        right: Box<IRExpr>,
        #[serde(skip)]
        span: Option<Span>,
    },
    /// arithmetic aggregator over a domain.
    Aggregate {
        kind: IRAggKind,
        var: std::string::String,
        domain: IRType,
        body: Box<IRExpr>,
        in_filter: Option<Box<IRExpr>>,
        #[serde(skip)]
        span: Option<Span>,
    },
    /// `saw Sys::event(args)` — past-time event observation.
    /// True at step n iff the event fired with matching args at some step ≤ n.
    /// Each arg is Some(expr) for value match or None for wildcard.
    Saw {
        system_name: std::string::String,
        event_name: std::string::String,
        args: Vec<Option<Box<IRExpr>>>,
        #[serde(skip)]
        span: Option<Span>,
    },
    Match {
        scrutinee: Box<IRExpr>,
        arms: Vec<IRMatchArm>,
        #[serde(skip)]
        span: Option<Span>,
    },
    Choose {
        var: std::string::String,
        domain: IRType,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        predicate: Option<Box<IRExpr>>,
        #[serde(rename = "type")]
        ty: IRType,
        #[serde(skip)]
        span: Option<Span>,
    },
    MapUpdate {
        map: Box<IRExpr>,
        key: Box<IRExpr>,
        value: Box<IRExpr>,
        #[serde(rename = "type")]
        ty: IRType,
        #[serde(skip)]
        span: Option<Span>,
    },
    Index {
        map: Box<IRExpr>,
        key: Box<IRExpr>,
        #[serde(rename = "type")]
        ty: IRType,
        #[serde(skip)]
        span: Option<Span>,
    },
    SetLit {
        elements: Vec<IRExpr>,
        #[serde(rename = "type")]
        ty: IRType,
        #[serde(skip)]
        span: Option<Span>,
    },
    SeqLit {
        elements: Vec<IRExpr>,
        #[serde(rename = "type")]
        ty: IRType,
        #[serde(skip)]
        span: Option<Span>,
    },
    MapLit {
        entries: Vec<(IRExpr, IRExpr)>,
        #[serde(rename = "type")]
        ty: IRType,
        #[serde(skip)]
        span: Option<Span>,
    },
    SetComp {
        var: std::string::String,
        domain: IRType,
        filter: Box<IRExpr>,
        projection: Option<Box<IRExpr>>,
        #[serde(rename = "type")]
        ty: IRType,
        #[serde(skip)]
        span: Option<Span>,
    },
    /// Cardinality: `#S` — count of elements in a set/collection.
    Card {
        expr: Box<IRExpr>,
        #[serde(skip)]
        span: Option<Span>,
    },
    Sorry {
        #[serde(skip)]
        span: Option<Span>,
    },
    Todo {
        #[serde(skip)]
        span: Option<Span>,
    },
    /// `assert expr` — verification condition: prove expr holds at this point.
    /// After the assert, expr can be assumed true for subsequent code.
    Assert {
        expr: Box<IRExpr>,
        #[serde(skip)]
        span: Option<Span>,
    },
    /// `assume expr` — add expr as an assumption without proof.
    /// The user takes responsibility for its truth. Emits a warning.
    Assume {
        expr: Box<IRExpr>,
        #[serde(skip)]
        span: Option<Span>,
    },
    // Imperative constructs
    Block {
        exprs: Vec<IRExpr>,
        #[serde(skip)]
        span: Option<Span>,
    },
    VarDecl {
        name: std::string::String,
        #[serde(rename = "type")]
        ty: IRType,
        init: Box<IRExpr>,
        rest: Box<IRExpr>,
        #[serde(skip)]
        span: Option<Span>,
    },
    While {
        cond: Box<IRExpr>,
        invariants: Vec<IRExpr>,
        #[serde(skip_serializing_if = "Option::is_none")]
        decreases: Option<IRDecreases>,
        body: Box<IRExpr>,
        #[serde(skip)]
        span: Option<Span>,
    },
    IfElse {
        cond: Box<IRExpr>,
        #[serde(rename = "then")]
        then_body: Box<IRExpr>,
        #[serde(rename = "else")]
        #[serde(skip_serializing_if = "Option::is_none")]
        else_body: Option<Box<IRExpr>>,
        #[serde(skip)]
        span: Option<Span>,
    },
}

/// arithmetic aggregator kind in IR.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum IRAggKind {
    Sum,
    Product,
    Min,
    Max,
    Count,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRMatchArm {
    pub pattern: IRPattern,
    pub guard: Option<IRExpr>,
    pub body: IRExpr,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(tag = "tag")]
pub enum IRPattern {
    PVar {
        name: std::string::String,
    },
    PCtor {
        name: std::string::String,
        fields: Vec<IRFieldPat>,
    },
    PWild,
    POr {
        left: Box<IRPattern>,
        right: Box<IRPattern>,
    },
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRFieldPat {
    pub name: std::string::String,
    pub pattern: IRPattern,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct LetBinding {
    pub name: std::string::String,
    #[serde(rename = "type")]
    pub ty: IRType,
    pub expr: IRExpr,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(tag = "tag")]
pub enum LitVal {
    Int { value: i64 },
    Real { value: f64 },
    Float { value: f64 },
    Bool { value: bool },
    Str { value: std::string::String },
}

// ── Entities ─────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IREntity {
    pub name: std::string::String,
    pub fields: Vec<IRField>,
    pub transitions: Vec<IRTransition>,
    /// derived fields declared on this entity.
    /// Each is a zero-argument pure expression evaluated against the
    /// entity instance state. The verifier expands references to
    /// derived fields via the DefEnv mechanism (task #268).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub derived_fields: Vec<IRDerivedField>,
    /// invariants declared on this entity. Each
    /// invariant body is a Boolean expression that must hold in every
    /// reachable state for every instance of the entity. Per  /// entity invariants travel with the entity type into any system
    /// that pools it.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub invariants: Vec<IRInvariant>,
    /// fsm declarations on this entity. Each fsm
    /// names one enum-typed field plus a transition table; the
    /// verifier consults this metadata when encoding actions that
    /// mutate the named field, asserting `(old, new)` is in the
    /// table ( / 50.6).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub fsm_decls: Vec<IRFsm>,
}

/// a finite-state-machine declaration attached to
/// an entity field. `field` is the entity field this fsm constrains;
/// `enum_name` is the field's enum type; `transitions` is the
/// flattened transition table (one entry per `(from, to)` pair from
/// the source rows). Empty `transitions` denotes a fully-terminal fsm
/// (every state is terminal — pathological but legal).
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRFsm {
    pub field: std::string::String,
    pub enum_name: std::string::String,
    pub transitions: Vec<IRFsmTransition>,
}

/// one `(from, to)` transition pair in an fsm
/// table. The original row form `@from -> @to1 | @to2` is flattened
/// into separate `IRFsmTransition` entries (one per target).
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRFsmTransition {
    pub from: std::string::String,
    pub to: std::string::String,
}

/// a derived field on an entity or system.
/// `name` is the declaration name, `body` is the lowered expression,
/// and `ty` is the field's type (inferred from `body` at elab time).
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRDerivedField {
    pub name: std::string::String,
    pub body: IRExpr,
    #[serde(rename = "type")]
    pub ty: IRType,
}

/// a named invariant on an entity or system.
/// `name` is mandatory. `body` is the lowered Boolean expression that must be
/// preserved by every event boundary in the verification scope.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRInvariant {
    pub name: std::string::String,
    pub body: IRExpr,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRField {
    pub name: std::string::String,
    #[serde(rename = "type")]
    pub ty: IRType,
    /// Deterministic default value (`= expr`). For `in {a, b,...}`, this is
    /// the first value (representative for IC3 initial state encoding).
    /// `None` when no deterministic default exists (e.g., `where` constraint only).
    pub default: Option<IRExpr>,
    /// Nondeterministic initial constraint from `in {...}` or `where expr`.
    /// When present, the create encoding asserts this constraint on the field
    /// value instead of (or in addition to) the deterministic default.
    /// Uses `$` as the bound variable for the field value.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub initial_constraint: Option<IRExpr>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRTransition {
    pub name: std::string::String,
    pub refs: Vec<IRTransRef>,
    pub params: Vec<IRTransParam>,
    pub guard: IRExpr,
    pub updates: Vec<IRUpdate>,
    pub postcondition: Option<IRExpr>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRTransRef {
    pub name: std::string::String,
    pub entity: std::string::String,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRTransParam {
    pub name: std::string::String,
    #[serde(rename = "type")]
    pub ty: IRType,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRUpdate {
    pub field: std::string::String,
    pub value: IRExpr,
}

// ── Queries ──────────────────────────────────────────────────────────

/// a public read-only observation on a system.
/// `query name(params) = body` declares a pure expression that can
/// be referenced by external tools and verification blocks.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRQuery {
    pub name: std::string::String,
    pub params: Vec<IRTransParam>,
    pub body: IRExpr,
}

/// R4: a let binding in a program system. Each let binding instantiates a
/// composed system with store bindings that wire the program's stores to
/// the composed system's store parameters.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRLetBinding {
    pub name: std::string::String,
    pub system_type: std::string::String,
    pub store_bindings: Vec<(std::string::String, std::string::String)>,
}

// ── Systems ──────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRSystem {
    pub name: std::string::String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub store_params: Vec<IRStoreParam>,
    /// flat state fields declared on this system.
    /// Struct-typed fields are flattened into sub-fields (e.g., "ui.screen").
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub fields: Vec<IRField>,
    pub entities: Vec<std::string::String>,
    /// command declarations with return types.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub commands: Vec<IRCommand>,
    pub actions: Vec<IRSystemAction>,
    /// fsm declarations on direct system fields.
    /// These constrain allowed transitions for enum-typed flat state
    /// fields mutated by system actions.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub fsm_decls: Vec<IRFsm>,
    /// derived fields declared on this system.
    /// Each is a zero-argument pure expression evaluated against the
    /// system's flat state and pooled entities.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub derived_fields: Vec<IRDerivedField>,
    /// invariants declared on this system.
    /// Each invariant body is a Boolean expression that must hold in
    /// every reachable state. System invariants are scoped to the
    /// declaring system per — they do not travel.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub invariants: Vec<IRInvariant>,
    /// query declarations lowered from the system.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub queries: Vec<IRQuery>,
    /// /: system-local predicates. Same shape as
    /// top-level IRFunction preds but scoped to the declaring system.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub preds: Vec<IRFunction>,
    /// R4: let bindings from program declarations. Programs define their
    /// composition topology via let bindings that instantiate systems with
    /// store bindings. Non-program systems have this field empty.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub let_bindings: Vec<IRLetBinding>,
    /// proc declarations (only on programs).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub procs: Vec<IRProc>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRStoreParam {
    pub name: std::string::String,
    pub entity_type: std::string::String,
}

/// proc declaration in IR — a named DAG of command invocations.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRProc {
    pub name: std::string::String,
    pub params: Vec<IRTransParam>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub requires: Option<IRExpr>,
    pub nodes: Vec<IRProcNode>,
    pub edges: Vec<IRProcEdge>,
}

/// proc node — a named command invocation via an instance handle.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRProcNode {
    pub name: std::string::String,
    pub instance: std::string::String,
    pub command: std::string::String,
    pub args: Vec<IRExpr>,
}

/// proc dependency edge.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRProcEdge {
    pub target: std::string::String,
    pub condition: IRProcDepCond,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(tag = "tag")]
pub enum IRProcDepCond {
    Fact {
        node: std::string::String,
        #[serde(skip_serializing_if = "Option::is_none")]
        qualifier: Option<std::string::String>,
    },
    Not {
        condition: Box<IRProcDepCond>,
    },
    And {
        left: Box<IRProcDepCond>,
        right: Box<IRProcDepCond>,
    },
    Or {
        left: Box<IRProcDepCond>,
        right: Box<IRProcDepCond>,
    },
}

/// command declaration metadata in IR.
/// Carries the command name, parameter types, and optional return type
/// so downstream proc outcome port resolution can validate
/// outcome ports and payload shapes.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRCommand {
    pub name: std::string::String,
    pub params: Vec<IRTransParam>,
    /// Optional return/outcome type.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub return_type: Option<IRType>,
}

// Fairness is not a step-level property. It lives in `AssumptionSet`
// data attached to the verification site.

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRSystemAction {
    pub name: std::string::String,
    pub params: Vec<IRTransParam>,
    pub guard: IRExpr,
    pub body: Vec<IRAction>,
    /// optional return expression (outcome variant).
    /// The verifier does not encode return values — they are used by
    /// proc outcome port resolution.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub return_expr: Option<IRExpr>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(tag = "tag")]
pub enum IRAction {
    Choose {
        var: std::string::String,
        entity: std::string::String,
        filter: Box<IRExpr>,
        ops: Vec<IRAction>,
    },
    ForAll {
        var: std::string::String,
        entity: std::string::String,
        ops: Vec<IRAction>,
    },
    Create {
        entity: std::string::String,
        fields: Vec<IRCreateField>,
    },
    LetCrossCall {
        name: std::string::String,
        system: std::string::String,
        command: std::string::String,
        args: Vec<IRExpr>,
    },
    Apply {
        target: std::string::String,
        transition: std::string::String,
        refs: Vec<std::string::String>,
        args: Vec<IRExpr>,
    },
    CrossCall {
        system: std::string::String,
        command: std::string::String,
        args: Vec<IRExpr>,
    },
    Match {
        scrutinee: IRActionMatchScrutinee,
        arms: Vec<IRActionMatchArm>,
    },
    ExprStmt {
        expr: IRExpr,
    },
}

#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(tag = "tag")]
pub enum IRActionMatchScrutinee {
    Var {
        name: std::string::String,
    },
    CrossCall {
        system: std::string::String,
        command: std::string::String,
        args: Vec<IRExpr>,
    },
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRActionMatchArm {
    pub pattern: IRPattern,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub guard: Option<IRExpr>,
    pub body: Vec<IRAction>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRCreateField {
    pub name: std::string::String,
    pub value: IRExpr,
}

// ── Verification ─────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRVerify {
    pub name: std::string::String,
    /// optional BMC depth override from `verify name [depth: N]`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub depth: Option<usize>,
    pub systems: Vec<IRVerifySystem>,
    /// Per-store bounds: each store declaration carries its own entity type
    /// and pool size. `compute_verify_scope` sizes entities from these
    /// instead of collapsing all stores into a single max(hi) per system.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub stores: Vec<IRStoreDecl>,
    /// Normalized assumption set populated during elaboration.
    /// Verifier backends read fairness and stutter semantics from this field.
    pub assumption_set: IRAssumptionSet,
    pub asserts: Vec<IRExpr>,
    /// Source span of the verify block (not serialized — diagnostic use only).
    #[serde(skip)]
    pub span: Option<Span>,
    /// Source file path (not serialized — diagnostic use only).
    #[serde(skip)]
    pub file: Option<std::string::String>,
}

/// Per-store bounds declaration. Each store has its own entity type and
/// pool size, enabling independent sizing of entity pools across stores
/// that bind different entity types.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRStoreDecl {
    pub name: std::string::String,
    pub entity_type: std::string::String,
    pub lo: i64,
    pub hi: i64,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRVerifySystem {
    pub name: std::string::String,
    pub lo: i64,
    pub hi: i64,
}

// ── AssumptionSet (, populated in ) ────────────────
//
// `IRAssumptionSet` is the normalized fairness/stutter context attached to
// every verify/theorem/lemma site. It is populated by the elab resolve
// pass from the parsed `ast::AssumeBlock` (see `EVerify::assumption_set`)
// and lowered into IR here so the verifier can read it.
//
// Construct defaults are applied during elab collection:
// * verify → stutter = false
// * theorem → stutter = true
// * lemma → stutter = true
//
// Assumption-set normalization:
// * sets are deduplicated and sorted alphabetically by (system, event)
// * if an event is in `strong_fair`, it is removed from `weak_fair`
//
// the verifier reads fairness from
// `IRVerify::assumption_set` at three sites — `fairness_constraints`
// in `verify/harness.rs`, `check_verify_block_tiered` and
// `try_liveness_reduction` in `verify/mod.rs`. Per-tuple lasso
// encoding is wired through `assumption_set.per_tuple`.

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct IRCommandRef {
    pub system: std::string::String,
    pub command: std::string::String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct IRAssumptionSet {
    pub stutter: bool,
    pub weak_fair: Vec<IRCommandRef>,
    pub strong_fair: Vec<IRCommandRef>,
    /// Subset of `weak_fair ∪ strong_fair` whose events are
    /// parameterized. Parameterized fair events default to per-tuple
    /// fairness; this flag selects the lasso-BMC encoding
    /// (per-event vs per-(event, args)-tuple).
    pub per_tuple: Vec<IRCommandRef>,
}

impl IRAssumptionSet {
    /// Lower an elab `AssumptionSet` to the IR mirror. The elab side
    /// stores fair sets as `BTreeSet<EventRef>` (sorted, deduplicated);
    /// the IR mirrors these as `Vec<IRCommandRef>` so the type is
    /// trivially serializable while preserving canonical order.
    pub fn from_elab(set: &crate::elab::types::AssumptionSet) -> Self {
        let to_ref = |e: &crate::elab::types::EventRef| IRCommandRef {
            system: e.system.clone(),
            command: e.command.clone(),
        };
        Self {
            stutter: set.stutter,
            weak_fair: set.weak_fair.iter().map(to_ref).collect(),
            strong_fair: set.strong_fair.iter().map(to_ref).collect(),
            per_tuple: set.per_tuple.iter().map(to_ref).collect(),
        }
    }

    /// Construct the IR-level assumption set default for a `verify`
    /// site: stutter off, no fairness. Mirrors
    /// `elab::types::AssumptionSet::default_for_verify`.
    #[must_use]
    pub fn default_for_verify() -> Self {
        Self {
            stutter: false,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        }
    }

    /// Construct the IR-level assumption set default for a theorem or
    /// lemma site: stutter on, no fairness. Mirrors
    /// `elab::types::AssumptionSet::default_for_theorem_or_lemma`.
    #[must_use]
    pub fn default_for_theorem_or_lemma() -> Self {
        Self {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        }
    }

    /// Whether this assumption set carries any fairness items.
    /// Used by the verifier to short-circuit dispatch.
    #[must_use]
    pub fn has_fair_events(&self) -> bool {
        !self.weak_fair.is_empty() || !self.strong_fair.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRTheorem {
    pub name: std::string::String,
    pub systems: Vec<std::string::String>,
    /// Normalized assumption set. See `IRVerify::assumption_set`.
    pub assumption_set: IRAssumptionSet,
    pub invariants: Vec<IRExpr>,
    pub shows: Vec<IRExpr>,
    /// External proof artifact reference from `by "file"`, when present.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub by_file: Option<std::string::String>,
    /// Lemma names referenced via `by L1, L2,...`.
    /// Conclusions are injected as assumptions during proof.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub by_lemmas: Vec<std::string::String>,
    /// Source span of the theorem block (not serialized — diagnostic use only).
    #[serde(skip)]
    pub span: Option<Span>,
    /// Source file path (not serialized — diagnostic use only).
    #[serde(skip)]
    pub file: Option<std::string::String>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRAxiom {
    pub name: std::string::String,
    pub body: IRExpr,
    /// External proof artifact reference from `by "file"`, when present.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub by_file: Option<std::string::String>,
    /// Source span of the axiom declaration (not serialized — diagnostic use only).
    #[serde(skip)]
    pub span: Option<Span>,
    /// Source file path (not serialized — diagnostic use only).
    #[serde(skip)]
    pub file: Option<std::string::String>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRLemma {
    pub name: std::string::String,
    /// Normalized assumption set. See `IRVerify::assumption_set`.
    pub assumption_set: IRAssumptionSet,
    pub body: Vec<IRExpr>,
    /// Source span of the lemma block (not serialized — diagnostic use only).
    #[serde(skip)]
    pub span: Option<Span>,
    /// Source file path (not serialized — diagnostic use only).
    #[serde(skip)]
    pub file: Option<std::string::String>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRScene {
    pub name: std::string::String,
    pub systems: Vec<std::string::String>,
    /// Per-store bounds from scene given blocks. Mirrors `IRVerify::stores`.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub stores: Vec<IRStoreDecl>,
    pub givens: Vec<IRSceneGiven>,
    pub events: Vec<IRSceneEvent>,
    pub ordering: Vec<IRExpr>,
    pub assertions: Vec<IRExpr>,
    /// Constraint expressions from given blocks, asserted at step 0 as
    /// initial-state assumptions.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub given_constraints: Vec<IRExpr>,
    /// Activate declarations: pre-activate named entity instances at step 0.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub activations: Vec<IRActivation>,
    /// Source span of the scene block (not serialized — diagnostic use only).
    #[serde(skip)]
    pub span: Option<Span>,
    /// Source file path (not serialized — diagnostic use only).
    #[serde(skip)]
    pub file: Option<std::string::String>,
}

/// Activation declaration in the IR. Maps named instances to a store.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRActivation {
    pub instances: Vec<std::string::String>,
    pub store_name: std::string::String,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRSceneGiven {
    pub var: std::string::String,
    pub entity: std::string::String,
    /// optional store name from `in store_name`.
    /// When present, the entity slot should be allocated within the
    /// named store's slot range instead of the global pool.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub store_name: Option<std::string::String>,
    pub constraint: IRExpr,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRSceneEvent {
    pub var: std::string::String,
    pub system: std::string::String,
    pub event: std::string::String,
    pub args: Vec<IRExpr>,
    pub cardinality: Cardinality,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(untagged)]
pub enum Cardinality {
    Named(std::string::String),
    Exact { exactly: i64 },
}

// ── Constants and Functions ──────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRConst {
    pub name: std::string::String,
    #[serde(rename = "type")]
    pub ty: IRType,
    pub value: IRExpr,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRFunction {
    pub name: std::string::String,
    #[serde(rename = "type")]
    pub ty: IRType,
    pub body: IRExpr,
    /// For props: the target system name (from `prop X for System =...`).
    /// None for preds and fns.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub prop_target: Option<std::string::String>,
    /// Requires clauses.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub requires: Vec<IRExpr>,
    /// Ensures clauses.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub ensures: Vec<IRExpr>,
    /// Decreases clause.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub decreases: Option<IRDecreases>,
    /// Source span (not serialized — diagnostic use only).
    #[serde(skip)]
    pub span: Option<Span>,
    /// Source file path (not serialized — diagnostic use only).
    #[serde(skip)]
    pub file: Option<std::string::String>,
}

/// Decreases clause: termination measure for recursive functions.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRDecreases {
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub measures: Vec<IRExpr>,
    pub star: bool,
}

// ── Top-level program ────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRProgram {
    pub types: Vec<IRTypeEntry>,
    pub constants: Vec<IRConst>,
    pub functions: Vec<IRFunction>,
    pub entities: Vec<IREntity>,
    pub systems: Vec<IRSystem>,
    pub verifies: Vec<IRVerify>,
    pub theorems: Vec<IRTheorem>,
    pub axioms: Vec<IRAxiom>,
    pub lemmas: Vec<IRLemma>,
    pub scenes: Vec<IRScene>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRTypeEntry {
    pub name: std::string::String,
    #[serde(rename = "type")]
    pub ty: IRType,
}
