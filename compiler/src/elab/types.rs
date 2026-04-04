//! Semantic AST types for the Abide elaborator.
//!
//! These types represent the elaborated (resolved, type-checked) form of
//! Abide declarations. The parsed AST (`crate::ast`) is the parse
//! representation; these types carry semantic information.

/// Semantic type representation (resolved from parse-level `TypeRef`/`Name`).
#[derive(Debug, Clone)]
pub enum Ty {
    /// Sum type: name + constructor names
    Enum(String, Vec<String>),
    /// Record type: name + fields (name, type)
    Record(String, Vec<(String, Ty)>),
    /// Type alias: name + underlying type
    Alias(String, Box<Ty>),
    /// Built-in type
    Builtin(BuiltinTy),
    /// Parameterized type: name + args
    Param(String, Vec<Ty>),
    /// Function type: param -> result
    Fn(Box<Ty>, Box<Ty>),
    /// Entity used as type (e.g. in quantifier domains)
    Entity(String),
    /// Not yet resolved (pre-resolve pass)
    Unresolved(String),
    /// Set<T>
    Set(Box<Ty>),
    /// Seq<T>
    Seq(Box<Ty>),
    /// Map<K, V>
    Map(Box<Ty>, Box<Ty>),
    /// (A, B, ...)
    Tuple(Vec<Ty>),
    /// Refinement type: base type + predicate (Int { $ > 0 })
    Refinement(Box<Ty>, Box<EExpr>),
}

impl Ty {
    /// Get the name of a type (for error messages).
    pub fn name(&self) -> &str {
        match self {
            Self::Enum(n, _)
            | Self::Record(n, _)
            | Self::Alias(n, _)
            | Self::Param(n, _)
            | Self::Entity(n)
            | Self::Unresolved(n) => n,
            Self::Builtin(b) => b.name(),
            Self::Fn(_, _) => "->",
            Self::Set(_) => "Set",
            Self::Seq(_) => "Seq",
            Self::Map(_, _) => "Map",
            Self::Tuple(_) => "Tuple",
            Self::Refinement(base, _) => base.name(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuiltinTy {
    Int,
    Bool,
    String,
    Id,
    Real,
    Float,
}

impl BuiltinTy {
    pub fn name(self) -> &'static str {
        match self {
            Self::Int => "Int",
            Self::Bool => "Bool",
            Self::String => "String",
            Self::Id => "Id",
            Self::Real => "Real",
            Self::Float => "Float",
        }
    }
}

// ── Elaborated declarations ──────────────────────────────────────────

/// Elaborated type declaration.
#[derive(Debug, Clone)]
pub struct EType {
    pub name: String,
    pub variants: Vec<EVariant>,
    pub ty: Ty,
    pub span: Option<crate::span::Span>,
}

#[derive(Debug, Clone)]
pub enum EVariant {
    Simple(String),
    Record(String, Vec<(String, Ty)>),
    Param(String, Vec<Ty>),
}

/// Elaborated entity.
#[derive(Debug, Clone)]
pub struct EEntity {
    pub name: String,
    pub fields: Vec<EField>,
    pub actions: Vec<EAction>,
    pub span: Option<crate::span::Span>,
}

#[derive(Debug, Clone)]
pub struct EField {
    pub name: String,
    pub ty: Ty,
    pub default: Option<EExpr>,
    pub span: Option<crate::span::Span>,
}

#[derive(Debug, Clone)]
pub struct EAction {
    pub name: String,
    pub refs: Vec<(String, Ty)>,
    pub params: Vec<(String, Ty)>,
    pub requires: Vec<EExpr>,
    pub body: Vec<EExpr>,
    pub span: Option<crate::span::Span>,
}

/// Elaborated system.
#[derive(Debug, Clone)]
pub struct ESystem {
    pub name: String,
    pub uses: Vec<String>,
    pub scopes: Vec<EScope>,
    pub events: Vec<EEvent>,
    pub next_items: Vec<ENextItem>,
    pub span: Option<crate::span::Span>,
}

#[derive(Debug, Clone)]
pub struct EScope {
    pub entity: String,
    pub lo: i64,
    pub hi: i64,
}

#[derive(Debug, Clone)]
pub struct EEvent {
    pub name: String,
    pub params: Vec<(String, Ty)>,
    pub requires: Vec<EExpr>,
    pub ensures: Vec<EExpr>,
    pub body: Vec<EEventAction>,
    pub span: Option<crate::span::Span>,
}

/// Structured event body actions.
#[derive(Debug, Clone)]
pub enum EEventAction {
    /// choose var: entity where guard { body }
    Choose(String, Ty, EExpr, Vec<EEventAction>),
    /// for var: entity { body }
    ForAll(String, Ty, Vec<EEventAction>),
    /// create `EntityName` { field = expr, ... }
    Create(String, Vec<(String, EExpr)>),
    /// `System::event(args)`
    CrossCall(String, String, Vec<EExpr>),
    /// target.action[refs](args)
    Apply(EExpr, String, Vec<EExpr>, Vec<EExpr>),
    /// Bare expression
    Expr(EExpr),
}

/// Schedule next-block items.
#[derive(Debug, Clone)]
pub enum ENextItem {
    When(Box<EExpr>, String),
    Else,
}

/// Elaborated predicate.
#[derive(Debug, Clone)]
pub struct EPred {
    pub name: String,
    pub params: Vec<(String, Ty)>,
    pub body: EExpr,
    pub span: Option<crate::span::Span>,
    pub file: Option<String>,
}

/// Elaborated property.
#[derive(Debug, Clone)]
pub struct EProp {
    pub name: String,
    pub target: Option<String>,
    pub body: EExpr,
    pub span: Option<crate::span::Span>,
    pub file: Option<String>,
}

/// Elaborated verify block.
#[derive(Debug, Clone)]
pub struct EVerify {
    pub name: String,
    pub targets: Vec<(String, i64, i64)>,
    pub asserts: Vec<EExpr>,
    pub span: Option<crate::span::Span>,
    pub file: Option<String>,
}

/// Elaborated scene.
#[derive(Debug, Clone)]
pub struct EScene {
    pub name: String,
    pub targets: Vec<String>,
    pub givens: Vec<ESceneGiven>,
    pub whens: Vec<ESceneWhen>,
    pub thens: Vec<EExpr>,
    pub span: Option<crate::span::Span>,
    pub file: Option<String>,
}

#[derive(Debug, Clone)]
pub struct ESceneGiven {
    pub var: String,
    pub entity_type: String,
    pub condition: Option<EExpr>,
}

#[derive(Debug, Clone)]
pub enum ESceneWhen {
    Action {
        var: String,
        system: String,
        event: String,
        args: Vec<EExpr>,
        card: Option<String>,
    },
    Assume(EExpr),
}

/// Elaborated theorem block.
#[derive(Debug, Clone)]
pub struct ETheorem {
    pub name: String,
    pub targets: Vec<String>,
    pub invariants: Vec<EExpr>,
    pub shows: Vec<EExpr>,
    pub span: Option<crate::span::Span>,
    pub file: Option<String>,
}

/// Elaborated axiom declaration.
#[derive(Debug, Clone)]
pub struct EAxiom {
    pub name: String,
    pub body: EExpr,
    pub span: Option<crate::span::Span>,
    pub file: Option<String>,
}

/// Elaborated lemma block.
#[derive(Debug, Clone)]
pub struct ELemma {
    pub name: String,
    pub body: Vec<EExpr>,
    pub span: Option<crate::span::Span>,
    pub file: Option<String>,
}

/// Elaborated const declaration.
#[derive(Debug, Clone)]
pub struct EConst {
    pub name: String,
    pub body: EExpr,
    pub span: Option<crate::span::Span>,
}

/// Elaborated fn declaration.
#[derive(Debug, Clone)]
pub struct EFn {
    pub name: String,
    pub params: Vec<(String, Ty)>,
    pub ret_ty: Ty,
    pub contracts: Vec<EContract>,
    pub body: EExpr,
    pub span: Option<crate::span::Span>,
    pub file: Option<String>,
}

/// Contract clause on fn declarations and while loops.
#[derive(Debug, Clone)]
pub enum EContract {
    Requires(EExpr),
    Ensures(EExpr),
    Decreases { measures: Vec<EExpr>, star: bool },
    Invariant(EExpr),
}

// ── Elaborated expressions ───────────────────────────────────────────

/// Type-annotated expression.
#[derive(Debug, Clone)]
pub enum EExpr {
    Lit(Ty, Literal, Option<crate::span::Span>),
    Var(Ty, String, Option<crate::span::Span>),
    Field(Ty, Box<EExpr>, String, Option<crate::span::Span>),
    Prime(Ty, Box<EExpr>, Option<crate::span::Span>),
    BinOp(Ty, BinOp, Box<EExpr>, Box<EExpr>, Option<crate::span::Span>),
    UnOp(Ty, UnOp, Box<EExpr>, Option<crate::span::Span>),
    Call(Ty, Box<EExpr>, Vec<EExpr>, Option<crate::span::Span>),
    CallR(
        Ty,
        Box<EExpr>,
        Vec<EExpr>,
        Vec<EExpr>,
        Option<crate::span::Span>,
    ),
    Qual(Ty, String, String, Option<crate::span::Span>),
    Quant(
        Ty,
        Quantifier,
        String,
        Ty,
        Box<EExpr>,
        Option<crate::span::Span>,
    ),
    Always(Ty, Box<EExpr>, Option<crate::span::Span>),
    Eventually(Ty, Box<EExpr>, Option<crate::span::Span>),
    Assert(Ty, Box<EExpr>, Option<crate::span::Span>),
    Assume(Ty, Box<EExpr>, Option<crate::span::Span>),
    Assign(Ty, Box<EExpr>, Box<EExpr>, Option<crate::span::Span>),
    NamedPair(Ty, String, Box<EExpr>, Option<crate::span::Span>),
    Seq(Ty, Box<EExpr>, Box<EExpr>, Option<crate::span::Span>),
    SameStep(Ty, Box<EExpr>, Box<EExpr>, Option<crate::span::Span>),
    Let(
        Vec<(String, Option<Ty>, EExpr)>,
        Box<EExpr>,
        Option<crate::span::Span>,
    ),
    Lam(
        Vec<(String, Ty)>,
        Option<Ty>,
        Box<EExpr>,
        Option<crate::span::Span>,
    ),
    Unresolved(String, Option<crate::span::Span>),
    TupleLit(Ty, Vec<EExpr>, Option<crate::span::Span>),
    In(Ty, Box<EExpr>, Box<EExpr>, Option<crate::span::Span>),
    Card(Ty, Box<EExpr>, Option<crate::span::Span>),
    Pipe(Ty, Box<EExpr>, Box<EExpr>, Option<crate::span::Span>),
    Match(
        Box<EExpr>,
        Vec<(EPattern, Option<EExpr>, EExpr)>,
        Option<crate::span::Span>,
    ),
    MapUpdate(
        Ty,
        Box<EExpr>,
        Box<EExpr>,
        Box<EExpr>,
        Option<crate::span::Span>,
    ),
    Index(Ty, Box<EExpr>, Box<EExpr>, Option<crate::span::Span>),
    SetComp(
        Ty,
        Option<Box<EExpr>>,
        String,
        Ty,
        Box<EExpr>,
        Option<crate::span::Span>,
    ),
    SetLit(Ty, Vec<EExpr>, Option<crate::span::Span>),
    SeqLit(Ty, Vec<EExpr>, Option<crate::span::Span>),
    MapLit(Ty, Vec<(EExpr, EExpr)>, Option<crate::span::Span>),
    Sorry(Option<crate::span::Span>),
    Todo(Option<crate::span::Span>),
    // Imperative constructs
    Block(Vec<EExpr>, Option<crate::span::Span>),
    /// VarDecl(name, type, init, rest, span)
    VarDecl(
        String,
        Option<Ty>,
        Box<EExpr>,
        Box<EExpr>,
        Option<crate::span::Span>,
    ),
    /// While(cond, contracts, body, span)
    While(
        Box<EExpr>,
        Vec<EContract>,
        Box<EExpr>,
        Option<crate::span::Span>,
    ),
    /// IfElse(cond, then, else, span)
    IfElse(
        Box<EExpr>,
        Box<EExpr>,
        Option<Box<EExpr>>,
        Option<crate::span::Span>,
    ),
    /// Record constructor: @Some { value: 1 }
    /// CtorRecord(ty, qualifier, ctor_name, fields, span)
    CtorRecord(
        Ty,
        Option<String>,
        String,
        Vec<(String, EExpr)>,
        Option<crate::span::Span>,
    ),
}

#[derive(Debug, Clone, PartialEq)]
pub enum EPattern {
    Var(String),
    Ctor(String, Vec<(String, EPattern)>),
    Wild,
    Or(Box<EPattern>, Box<EPattern>),
}

impl EExpr {
    /// Get the type annotation of an expression.
    pub fn ty(&self) -> Ty {
        match self {
            Self::Lit(ty, _, _)
            | Self::Var(ty, _, _)
            | Self::Field(ty, _, _, _)
            | Self::Prime(ty, _, _)
            | Self::BinOp(ty, _, _, _, _)
            | Self::UnOp(ty, _, _, _)
            | Self::Call(ty, _, _, _)
            | Self::CallR(ty, _, _, _, _)
            | Self::Qual(ty, _, _, _)
            | Self::Quant(ty, _, _, _, _, _)
            | Self::Always(ty, _, _)
            | Self::Eventually(ty, _, _)
            | Self::Assert(ty, _, _)
            | Self::Assume(ty, _, _)
            | Self::Assign(ty, _, _, _)
            | Self::NamedPair(ty, _, _, _)
            | Self::Seq(ty, _, _, _)
            | Self::SameStep(ty, _, _, _)
            | Self::TupleLit(ty, _, _)
            | Self::In(ty, _, _, _)
            | Self::Card(ty, _, _)
            | Self::Pipe(ty, _, _, _)
            | Self::MapUpdate(ty, _, _, _, _)
            | Self::Index(ty, _, _, _)
            | Self::SetComp(ty, _, _, _, _, _)
            | Self::SetLit(ty, _, _)
            | Self::SeqLit(ty, _, _)
            | Self::MapLit(ty, _, _) => ty.clone(),
            Self::Let(_, body, _) => body.ty(),
            Self::Match(scrut, _, _) => scrut.ty(),
            Self::Block(items, _) => items
                .last()
                .map_or(Ty::Unresolved(String::new()), EExpr::ty),
            Self::VarDecl(_, _, _, rest, _) => rest.ty(),
            Self::While(_, _, _, _) => Ty::Unresolved(String::new()),
            Self::IfElse(_, then_body, _, _) => then_body.ty(),
            Self::CtorRecord(ty, _, _, _, _) => ty.clone(),
            Self::Sorry(_) | Self::Todo(_) | Self::Lam(_, _, _, _) | Self::Unresolved(_, _) => {
                Ty::Unresolved(String::new())
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Int(i64),
    Real(f64),
    Float(f64),
    Str(String),
    Bool(bool),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    NEq,
    Lt,
    Gt,
    Le,
    Ge,
    And,
    Or,
    Implies,
    Unord,
    Conc,
    Xor,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Quantifier {
    All,
    Exists,
    Some,
    No,
    One,
    Lone,
}

// ── Elaboration result ───────────────────────────────────────────────

/// Full elaboration result containing all elaborated declarations.
#[derive(Debug, Clone)]
pub struct ElabResult {
    pub module_name: Option<String>,
    pub includes: Vec<String>,
    pub use_decls: Vec<crate::ast::UseDecl>,
    /// Alias → canonical name map from use declarations (e.g., `WSlot` → `Slot`).
    /// Used by IR lowering to canonicalize entity/system references.
    pub aliases: std::collections::HashMap<String, String>,
    pub types: Vec<EType>,
    pub entities: Vec<EEntity>,
    pub systems: Vec<ESystem>,
    pub preds: Vec<EPred>,
    pub props: Vec<EProp>,
    pub verifies: Vec<EVerify>,
    pub scenes: Vec<EScene>,
    pub theorems: Vec<ETheorem>,
    pub axioms: Vec<EAxiom>,
    pub lemmas: Vec<ELemma>,
    pub consts: Vec<EConst>,
    pub fns: Vec<EFn>,
}
