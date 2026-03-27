//! Semantic AST types for the Abide elaborator.
//!
//! These types represent the elaborated (resolved, type-checked) form of
//! Abide declarations. The parsed AST (`crate::ast`) is the parse
//! representation; these types carry semantic information.

/// Semantic type representation (resolved from parse-level `TypeRef`/`Name`).
#[derive(Debug, Clone, PartialEq)]
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
}

#[derive(Debug, Clone)]
pub struct EField {
    pub name: String,
    pub ty: Ty,
    pub default: Option<EExpr>,
}

#[derive(Debug, Clone)]
pub struct EAction {
    pub name: String,
    pub refs: Vec<(String, Ty)>,
    pub params: Vec<(String, Ty)>,
    pub requires: Vec<EExpr>,
    pub body: Vec<EExpr>,
}

/// Elaborated system.
#[derive(Debug, Clone)]
pub struct ESystem {
    pub name: String,
    pub uses: Vec<String>,
    pub scopes: Vec<EScope>,
    pub events: Vec<EEvent>,
    pub next_items: Vec<ENextItem>,
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
    When(EExpr, String),
    Else,
}

/// Elaborated predicate.
#[derive(Debug, Clone)]
pub struct EPred {
    pub name: String,
    pub params: Vec<(String, Ty)>,
    pub body: EExpr,
}

/// Elaborated property.
#[derive(Debug, Clone)]
pub struct EProp {
    pub name: String,
    pub target: Option<String>,
    pub body: EExpr,
}

/// Elaborated verify block.
#[derive(Debug, Clone)]
pub struct EVerify {
    pub name: String,
    pub targets: Vec<(String, i64, i64)>,
    pub asserts: Vec<EExpr>,
}

/// Elaborated scene.
#[derive(Debug, Clone)]
pub struct EScene {
    pub name: String,
    pub targets: Vec<String>,
    pub givens: Vec<ESceneGiven>,
    pub whens: Vec<ESceneWhen>,
    pub thens: Vec<EExpr>,
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
}

/// Elaborated axiom declaration.
#[derive(Debug, Clone)]
pub struct EAxiom {
    pub name: String,
    pub body: EExpr,
}

/// Elaborated lemma block.
#[derive(Debug, Clone)]
pub struct ELemma {
    pub name: String,
    pub body: Vec<EExpr>,
}

/// Elaborated const declaration.
#[derive(Debug, Clone)]
pub struct EConst {
    pub name: String,
    pub body: EExpr,
}

/// Elaborated fn declaration.
#[derive(Debug, Clone)]
pub struct EFn {
    pub name: String,
    pub params: Vec<(String, Ty)>,
    pub ret_ty: Ty,
    pub body: EExpr,
}

// ── Elaborated expressions ───────────────────────────────────────────

/// Type-annotated expression.
#[derive(Debug, Clone)]
pub enum EExpr {
    Lit(Ty, Literal),
    Var(Ty, String),
    Field(Ty, Box<EExpr>, String),
    Prime(Ty, Box<EExpr>),
    BinOp(Ty, BinOp, Box<EExpr>, Box<EExpr>),
    UnOp(Ty, UnOp, Box<EExpr>),
    Call(Ty, Box<EExpr>, Vec<EExpr>),
    CallR(Ty, Box<EExpr>, Vec<EExpr>, Vec<EExpr>),
    Qual(Ty, String, String),
    Quant(Ty, Quantifier, String, Ty, Box<EExpr>),
    Always(Ty, Box<EExpr>),
    Eventually(Ty, Box<EExpr>),
    Assert(Ty, Box<EExpr>),
    Assign(Ty, Box<EExpr>, Box<EExpr>),
    NamedPair(Ty, String, Box<EExpr>),
    Seq(Ty, Box<EExpr>, Box<EExpr>),
    SameStep(Ty, Box<EExpr>, Box<EExpr>),
    Let(Vec<(String, Option<Ty>, EExpr)>, Box<EExpr>),
    Lam(Vec<(String, Ty)>, Option<Ty>, Box<EExpr>),
    Unresolved(String),
    TupleLit(Ty, Vec<EExpr>),
    In(Ty, Box<EExpr>, Box<EExpr>),
    Card(Ty, Box<EExpr>),
    Pipe(Ty, Box<EExpr>, Box<EExpr>),
    Match(Box<EExpr>, Vec<(EPattern, Option<EExpr>, EExpr)>),
    MapUpdate(Ty, Box<EExpr>, Box<EExpr>, Box<EExpr>),
    Index(Ty, Box<EExpr>, Box<EExpr>),
    SetComp(Ty, Option<Box<EExpr>>, String, Ty, Box<EExpr>),
    SetLit(Ty, Vec<EExpr>),
    SeqLit(Ty, Vec<EExpr>),
    MapLit(Ty, Vec<(EExpr, EExpr)>),
    Sorry,
    Todo,
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
            Self::Lit(ty, _)
            | Self::Var(ty, _)
            | Self::Field(ty, _, _)
            | Self::Prime(ty, _)
            | Self::BinOp(ty, _, _, _)
            | Self::UnOp(ty, _, _)
            | Self::Call(ty, _, _)
            | Self::CallR(ty, _, _, _)
            | Self::Qual(ty, _, _)
            | Self::Quant(ty, _, _, _, _)
            | Self::Always(ty, _)
            | Self::Eventually(ty, _)
            | Self::Assert(ty, _)
            | Self::Assign(ty, _, _)
            | Self::NamedPair(ty, _, _)
            | Self::Seq(ty, _, _)
            | Self::SameStep(ty, _, _)
            | Self::TupleLit(ty, _)
            | Self::In(ty, _, _)
            | Self::Card(ty, _)
            | Self::Pipe(ty, _, _)
            | Self::MapUpdate(ty, _, _, _)
            | Self::Index(ty, _, _)
            | Self::SetComp(ty, _, _, _, _)
            | Self::SetLit(ty, _)
            | Self::SeqLit(ty, _)
            | Self::MapLit(ty, _) => ty.clone(),
            Self::Let(_, body) => body.ty(),
            Self::Match(scrut, _) => scrut.ty(),
            Self::Sorry | Self::Todo | Self::Lam(_, _, _) | Self::Unresolved(_) => {
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
