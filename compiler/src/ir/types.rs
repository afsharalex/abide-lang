//! Core IR types for Abide.
//!
//! Fully resolved, fully typed, desugared representation.
//! Consumed by: model checker, SMT solver, Agda emitter, simulator.

use serde::Serialize;

use crate::span::Span;

// ── Types ────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(tag = "tag")]
pub enum IRType {
    Int,
    Bool,
    String,
    Id,
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
    Match {
        scrutinee: Box<IRExpr>,
        arms: Vec<IRMatchArm>,
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
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRField {
    pub name: std::string::String,
    #[serde(rename = "type")]
    pub ty: IRType,
    pub default: Option<IRExpr>,
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

// ── Systems ──────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRSystem {
    pub name: std::string::String,
    pub entities: Vec<std::string::String>,
    pub events: Vec<IREvent>,
    pub schedule: IRSchedule,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IREvent {
    pub name: std::string::String,
    pub params: Vec<IRTransParam>,
    pub guard: IRExpr,
    pub postcondition: Option<IRExpr>,
    pub body: Vec<IRAction>,
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
    Apply {
        target: std::string::String,
        transition: std::string::String,
        refs: Vec<std::string::String>,
        args: Vec<IRExpr>,
    },
    CrossCall {
        system: std::string::String,
        event: std::string::String,
        args: Vec<IRExpr>,
    },
    ExprStmt {
        expr: IRExpr,
    },
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRCreateField {
    pub name: std::string::String,
    pub value: IRExpr,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRSchedule {
    pub when: Vec<IRSchedWhen>,
    pub idle: bool,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRSchedWhen {
    pub condition: IRExpr,
    pub event: std::string::String,
}

// ── Verification ─────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRVerify {
    pub name: std::string::String,
    pub systems: Vec<IRVerifySystem>,
    pub asserts: Vec<IRExpr>,
    /// Source span of the verify block (not serialized — diagnostic use only).
    #[serde(skip)]
    pub span: Option<Span>,
    /// Source file path (not serialized — diagnostic use only).
    #[serde(skip)]
    pub file: Option<std::string::String>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRVerifySystem {
    pub name: std::string::String,
    pub lo: i64,
    pub hi: i64,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRTheorem {
    pub name: std::string::String,
    pub systems: Vec<std::string::String>,
    pub invariants: Vec<IRExpr>,
    pub shows: Vec<IRExpr>,
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
    /// Source span of the axiom declaration (not serialized — diagnostic use only).
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
    pub givens: Vec<IRSceneGiven>,
    pub events: Vec<IRSceneEvent>,
    pub ordering: Vec<IRExpr>,
    pub assertions: Vec<IRExpr>,
    /// Source span of the scene block (not serialized — diagnostic use only).
    #[serde(skip)]
    pub span: Option<Span>,
    /// Source file path (not serialized — diagnostic use only).
    #[serde(skip)]
    pub file: Option<std::string::String>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRSceneGiven {
    pub var: std::string::String,
    pub entity: std::string::String,
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
    /// For props: the target system name (from `prop X for System = ...`).
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
    pub scenes: Vec<IRScene>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IRTypeEntry {
    pub name: std::string::String,
    #[serde(rename = "type")]
    pub ty: IRType,
}
