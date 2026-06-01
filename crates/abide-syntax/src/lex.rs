//! Abide lexer.
//!
//! Built on `logos`. The token enum is exhaustive — every reserved
//! word, punctuator, and literal class is its own variant. Whitespace
//! and `// line comments` are skipped at the lexer level. The entry
//! point [`lex`] returns either a vector of `(Token, Span)` pairs or a
//! list of [`LexError`]s.

use crate::diagnostic::LexError;
use crate::span::Span;
use logos::Logos;

/// One lexed token. Variants are sorted by category in the source:
/// keywords, operators/punctuation, identifiers, then literals.
#[derive(Logos, Debug, Clone, PartialEq)]
#[logos(skip r"[ \t\n\r]+")]
#[logos(skip r"//[^\n]*")]
pub enum Token {
    // ── Keywords ──────────────────────────────────────────────────────
    #[token("module")]
    Module,
    #[token("include")]
    Include,
    #[token("as")]
    As,
    #[token("use")]
    Use,
    #[token("const")]
    Const,
    #[token("fn")]
    Fn,
    #[token("type")]
    Type,
    #[token("enum")]
    Enum,
    #[token("struct")]
    Struct,
    #[token("entity")]
    Entity,
    #[token("interface")]
    Interface,
    #[token("extern")]
    Extern,
    #[token("system")]
    System,
    #[token("implements")]
    Implements,
    #[token("dep")]
    Dep,
    #[token("action")]
    Action,
    #[token("command")]
    Command,
    #[token("query")]
    Query,
    #[token("store")]
    Store,
    #[token("activate")]
    Activate,
    #[token("return")]
    Return,
    #[token("needs")]
    Needs,
    #[token("fair")]
    Fair,
    #[token("strong")]
    Strong,
    #[token("stutter")]
    Stutter,
    #[token("when")]
    When,
    #[token("may")]
    May,
    #[token("else")]
    Else,
    #[token("where")]
    Where,
    #[token("choose")]
    Choose,
    #[token("for")]
    For,
    #[token("create")]
    Create,
    #[token("pred")]
    Pred,
    #[token("prop")]
    Prop,
    #[token("verify")]
    Verify,
    #[token("assert")]
    Assert,
    #[token("invariant")]
    Invariant,
    #[token("show")]
    Show,
    #[token("lemma")]
    Lemma,
    #[token("scene")]
    Scene,
    #[token("given")]
    Given,
    #[token("let")]
    Let,
    #[token("one")]
    One,
    #[token("assume")]
    Assume,
    #[token("then")]
    Then,
    #[token("requires")]
    Requires,
    #[token("ensures")]
    Ensures,
    #[token("true")]
    True,
    #[token("false")]
    False,
    #[token("not")]
    Not,
    #[token("and")]
    And,
    #[token("or")]
    Or,
    #[token("implies")]
    Implies,
    #[token("in")]
    In,
    #[token("always")]
    Always,
    #[token("eventually")]
    Eventually,
    #[token("until")]
    Until,
    #[token("historically")]
    Historically,
    #[token("once")]
    Once,
    #[token("previously")]
    Previously,
    #[token("since")]
    Since,
    #[token("all")]
    All,
    #[token("exists")]
    Exists,
    #[token("some")]
    Some,
    #[token("no")]
    No,
    #[token("lone")]
    Lone,
    #[token("match")]
    Match,
    #[token("if")]
    If,
    #[token("sorry")]
    Sorry,
    #[token("todo")]
    Todo,
    #[token("theorem")]
    Theorem,
    #[token("axiom")]
    Axiom,
    #[token("by")]
    By,
    #[token("mut")]
    Mut,
    #[token("decreases")]
    Decreases,
    #[token("var")]
    Var,
    #[token("while")]
    While,
    #[token("derived")]
    Derived,
    #[token("fsm")]
    Fsm,
    #[token("under")]
    Under,
    #[token("program")]
    Program,
    #[token("proc")]
    Proc,
    #[token("saw")]
    Saw,
    #[token("sum")]
    Sum,
    #[token("product")]
    Product,
    #[token("min")]
    Min,
    #[token("max")]
    Max,
    #[token("count")]
    Count,

    // ── Symbols ───────────────────────────────────────────────────────
    #[token(":=")]
    ColonEq,
    #[token("::")]
    ColonColon,
    #[token("..")]
    DotDot,
    #[token(".")]
    Dot,
    #[token("@")]
    At,
    #[token("'")]
    Prime,
    #[token("#")]
    Hash,
    #[token("==")]
    EqEq,
    #[token("!=")]
    BangEq,
    #[token("!*")]
    BangStar,
    #[token("=>")]
    FatArrow,
    #[token("=")]
    Eq,
    #[token("<>")]
    Diamond,
    #[token("<=")]
    LtEq,
    #[token(">=")]
    GtEq,
    #[token("<")]
    Lt,
    #[token(">")]
    Gt,
    #[token("+")]
    Plus,
    #[token("->")] // must come before Minus
    Arrow,
    #[token("-")]
    Minus,
    #[token("*")]
    Star,
    #[token("/")]
    Slash,
    #[token("%")]
    Percent,
    #[token("||")] // must come before Pipe
    PipePipe,
    #[token("|>")] // must come before Pipe
    PipeGt,
    #[token("^|")]
    CaretPipe,
    #[token("|")]
    Pipe,
    #[token("&")]
    Amp,
    #[token(":")]
    Colon,
    #[token(";")]
    Semi,
    #[token(",")]
    Comma,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token("_")]
    Underscore,
    #[token("$")]
    Dollar,

    // ── Literals ──────────────────────────────────────────────────────
    #[regex("[a-zA-Z][a-zA-Z0-9_]*", |lex| lex.slice().to_owned())]
    Name(String),

    #[regex(r"[0-9]+\.[0-9]+f", |lex| lex.slice().to_owned())]
    FloatLit(String),

    #[regex(r"[0-9]+\.[0-9]+", |lex| lex.slice().parse::<f64>().unwrap())]
    DoubleLit(f64),

    #[regex(r"[0-9]+", |lex| lex.slice().parse::<i64>().unwrap())]
    IntLit(i64),

    #[regex(r#""[^"]*""#, |lex| {
        let s = lex.slice();
        s[1..s.len()-1].to_owned()
    })]
    StringLit(String),
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(text) = self.static_display_text() {
            return f.write_str(text);
        }
        match self {
            Self::Name(s) | Self::FloatLit(s) => write!(f, "{s}"),
            Self::IntLit(n) => write!(f, "{n}"),
            Self::DoubleLit(n) => write!(f, "{n}"),
            Self::StringLit(s) => write!(f, "\"{s}\""),
            _ => unreachable!("static tokens handled before literal formatting"),
        }
    }
}

impl Token {
    fn static_display_text(&self) -> Option<&'static str> {
        self.keyword_display_text()
            .or_else(|| self.operator_display_text())
            .or_else(|| self.delimiter_display_text())
    }

    fn keyword_display_text(&self) -> Option<&'static str> {
        Some(match self {
            Self::Module => "module",
            Self::Include => "include",
            Self::As => "as",
            Self::Use => "use",
            Self::Const => "const",
            Self::Fn => "fn",
            Self::Type => "type",
            Self::Enum => "enum",
            Self::Struct => "struct",
            Self::Entity => "entity",
            Self::Interface => "interface",
            Self::Extern => "extern",
            Self::System => "system",
            Self::Implements => "implements",
            Self::Dep => "dep",
            Self::Action => "action",
            Self::Command => "command",
            Self::Query => "query",
            Self::Store => "store",
            Self::Activate => "activate",
            Self::Return => "return",
            Self::Needs => "needs",
            Self::Fair => "fair",
            Self::Strong => "strong",
            Self::Stutter => "stutter",
            Self::When => "when",
            Self::May => "may",
            Self::Else => "else",
            Self::Where => "where",
            Self::Choose => "choose",
            Self::For => "for",
            Self::Create => "create",
            Self::Pred => "pred",
            Self::Prop => "prop",
            Self::Verify => "verify",
            Self::Assert => "assert",
            Self::Invariant => "invariant",
            Self::Show => "show",
            Self::Lemma => "lemma",
            Self::Scene => "scene",
            Self::Given => "given",
            Self::Let => "let",
            Self::One => "one",
            Self::Assume => "assume",
            Self::Then => "then",
            Self::Requires => "requires",
            Self::Ensures => "ensures",
            Self::True => "true",
            Self::False => "false",
            Self::Not => "not",
            Self::And => "and",
            Self::Or => "or",
            Self::Implies => "implies",
            Self::In => "in",
            Self::Always => "always",
            Self::Until => "until",
            Self::Eventually => "eventually",
            Self::Historically => "historically",
            Self::Once => "once",
            Self::Previously => "previously",
            Self::Since => "since",
            Self::All => "all",
            Self::Exists => "exists",
            Self::Some => "some",
            Self::No => "no",
            Self::Lone => "lone",
            Self::Match => "match",
            Self::If => "if",
            Self::Sorry => "sorry",
            Self::Todo => "todo",
            Self::Theorem => "theorem",
            Self::Axiom => "axiom",
            Self::By => "by",
            Self::Mut => "mut",
            Self::Decreases => "decreases",
            Self::Var => "var",
            Self::While => "while",
            Self::Derived => "derived",
            Self::Fsm => "fsm",
            Self::Under => "under",
            Self::Program => "program",
            Self::Proc => "proc",
            Self::Saw => "saw",
            Self::Sum => "sum",
            Self::Product => "product",
            Self::Min => "min",
            Self::Max => "max",
            Self::Count => "count",
            _ => return None,
        })
    }

    fn operator_display_text(&self) -> Option<&'static str> {
        Some(match self {
            Self::ColonEq => ":=",
            Self::ColonColon => "::",
            Self::DotDot => "..",
            Self::Dot => ".",
            Self::At => "@",
            Self::Prime => "'",
            Self::Hash => "#",
            Self::EqEq => "==",
            Self::BangEq => "!=",
            Self::BangStar => "!*",
            Self::FatArrow => "=>",
            Self::Eq => "=",
            Self::Diamond => "<>",
            Self::LtEq => "<=",
            Self::GtEq => ">=",
            Self::Lt => "<",
            Self::Gt => ">",
            Self::Plus => "+",
            Self::Arrow => "->",
            Self::Minus => "-",
            Self::Star => "*",
            Self::Slash => "/",
            Self::Percent => "%",
            Self::PipePipe => "||",
            Self::PipeGt => "|>",
            Self::CaretPipe => "^|",
            Self::Pipe => "|",
            Self::Amp => "&",
            _ => return None,
        })
    }

    fn delimiter_display_text(&self) -> Option<&'static str> {
        Some(match self {
            Self::Colon => ":",
            Self::Semi => ";",
            Self::Comma => ",",
            Self::LParen => "(",
            Self::RParen => ")",
            Self::LBracket => "[",
            Self::RBracket => "]",
            Self::LBrace => "{",
            Self::RBrace => "}",
            Self::Underscore => "_",
            Self::Dollar => "$",
            _ => return None,
        })
    }
}

/// Tokenize source text, returning tokens with spans or lex errors.
pub fn lex(src: &str) -> Result<Vec<(Token, Span)>, Vec<LexError>> {
    let mut tokens = Vec::new();
    let mut errors = Vec::new();

    let lexer = Token::lexer(src);
    for (result, range) in lexer.spanned() {
        let span = Span::from(range);
        match result {
            Ok(token) => tokens.push((token, span)),
            Err(()) => errors.push(LexError::new(src, span)),
        }
    }

    if errors.is_empty() {
        Ok(tokens)
    } else {
        Err(errors)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex_ok(src: &str) -> Vec<Token> {
        lex(src).unwrap().into_iter().map(|(t, _)| t).collect()
    }

    #[test]
    fn keywords() {
        let src = "module include as use const fn type enum struct entity system action command query fair strong sorry todo mut";
        let tokens = lex_ok(src);
        assert_eq!(
            tokens,
            vec![
                Token::Module,
                Token::Include,
                Token::As,
                Token::Use,
                Token::Const,
                Token::Fn,
                Token::Type,
                Token::Enum,
                Token::Struct,
                Token::Entity,
                Token::System,
                Token::Action,
                Token::Command,
                Token::Query,
                Token::Fair,
                Token::Strong,
                Token::Sorry,
                Token::Todo,
                Token::Mut,
            ]
        );
    }

    #[test]
    fn removed_surface_words_are_identifiers() {
        let tokens = lex_ok("step event workflow");
        assert_eq!(
            tokens,
            vec![
                Token::Name("step".to_owned()),
                Token::Name("event".to_owned()),
                Token::Name("workflow".to_owned()),
            ]
        );
    }

    #[test]
    fn more_keywords() {
        let src = "requires ensures true false not and or implies in always eventually";
        let tokens = lex_ok(src);
        assert_eq!(
            tokens,
            vec![
                Token::Requires,
                Token::Ensures,
                Token::True,
                Token::False,
                Token::Not,
                Token::And,
                Token::Or,
                Token::Implies,
                Token::In,
                Token::Always,
                Token::Eventually,
            ]
        );
    }

    #[test]
    fn quantifier_keywords() {
        let src = "all exists some no one lone";
        let tokens = lex_ok(src);
        assert_eq!(
            tokens,
            vec![
                Token::All,
                Token::Exists,
                Token::Some,
                Token::No,
                Token::One,
                Token::Lone,
            ]
        );
    }

    /// `derived` keyword for entity/system derived field
    /// declarations ().
    #[test]
    fn derived_keyword() {
        let src = "derived is_done = status";
        let tokens = lex_ok(src);
        assert_eq!(
            tokens,
            vec![
                Token::Derived,
                Token::Name("is_done".into()),
                Token::Eq,
                Token::Name("status".into()),
            ]
        );
    }

    /// assume-block tokens. The new `assume { fair X; strong fair Y;
    /// stutter | no stutter }` syntax on verify/theorem/lemma constructs
    /// requires the lexer to emit each of these as a distinct token.
    #[test]
    fn assume_block_tokens() {
        let src = "assume fair strong stutter no";
        let tokens = lex_ok(src);
        assert_eq!(
            tokens,
            vec![
                Token::Assume,
                Token::Fair,
                Token::Strong,
                Token::Stutter,
                Token::No,
            ]
        );
    }

    /// a realistic mini-source exercising the assume-block sequence
    /// `assume { fair Sys::ev; strong fair Sys::ev2; no stutter }`. This is
    /// not a full parse — just verifies that lexing produces the expected
    /// linear token stream so the parser can rely on it.
    #[test]
    fn assume_block_inline_token_stream() {
        let src = "assume { fair Sys::ev; strong fair Sys::ev2; no stutter }";
        let tokens = lex_ok(src);
        assert_eq!(
            tokens,
            vec![
                Token::Assume,
                Token::LBrace,
                Token::Fair,
                Token::Name("Sys".into()),
                Token::ColonColon,
                Token::Name("ev".into()),
                Token::Semi,
                Token::Strong,
                Token::Fair,
                Token::Name("Sys".into()),
                Token::ColonColon,
                Token::Name("ev2".into()),
                Token::Semi,
                Token::No,
                Token::Stutter,
                Token::RBrace,
            ]
        );
    }

    #[test]
    fn symbols() {
        let src =
            ":: := . .. @ ' # == != !* => = <> <= >= < > + -> - * / % || |> ^| | & : , ( ) [ ] { }";
        let tokens = lex_ok(src);
        assert_eq!(
            tokens,
            vec![
                Token::ColonColon,
                Token::ColonEq,
                Token::Dot,
                Token::DotDot,
                Token::At,
                Token::Prime,
                Token::Hash,
                Token::EqEq,
                Token::BangEq,
                Token::BangStar,
                Token::FatArrow,
                Token::Eq,
                Token::Diamond,
                Token::LtEq,
                Token::GtEq,
                Token::Lt,
                Token::Gt,
                Token::Plus,
                Token::Arrow,
                Token::Minus,
                Token::Star,
                Token::Slash,
                Token::Percent,
                Token::PipePipe,
                Token::PipeGt,
                Token::CaretPipe,
                Token::Pipe,
                Token::Amp,
                Token::Colon,
                Token::Comma,
                Token::LParen,
                Token::RParen,
                Token::LBracket,
                Token::RBracket,
                Token::LBrace,
                Token::RBrace,
            ]
        );
    }

    #[test]
    fn name_vs_keyword() {
        let tokens = lex_ok("imports importing typed");
        assert_eq!(
            tokens,
            vec![
                Token::Name("imports".into()),
                Token::Name("importing".into()),
                Token::Name("typed".into()),
            ]
        );
    }

    #[test]
    fn name_with_underscores() {
        let tokens = lex_ok("order_id failed_attempts mark_paid");
        assert_eq!(
            tokens,
            vec![
                Token::Name("order_id".into()),
                Token::Name("failed_attempts".into()),
                Token::Name("mark_paid".into()),
            ]
        );
    }

    #[test]
    fn integer_literals() {
        let tokens = lex_ok("0 42 500 999");
        assert_eq!(
            tokens,
            vec![
                Token::IntLit(0),
                Token::IntLit(42),
                Token::IntLit(500),
                Token::IntLit(999),
            ]
        );
    }

    #[test]
    #[allow(clippy::approx_constant)]
    fn float_and_double_literals() {
        let tokens = lex_ok("3.14 3.14f 0.0 1.5f");
        assert_eq!(
            tokens,
            vec![
                Token::DoubleLit(3.14),
                Token::FloatLit("3.14f".into()),
                Token::DoubleLit(0.0),
                Token::FloatLit("1.5f".into()),
            ]
        );
    }

    #[test]
    fn string_literals() {
        let tokens = lex_ok(r#""hello" "billing.ab" "submit""#);
        assert_eq!(
            tokens,
            vec![
                Token::StringLit("hello".into()),
                Token::StringLit("billing.ab".into()),
                Token::StringLit("submit".into()),
            ]
        );
    }

    #[test]
    fn comments_skipped() {
        let tokens = lex_ok("module // this is a comment\nuse");
        assert_eq!(tokens, vec![Token::Module, Token::Use]);
    }

    #[test]
    fn multi_char_symbol_priority() {
        //:: vs:= vs:, == vs =, -> vs -, || vs |, |> vs |
        let tokens = lex_ok(":: := : == = -> - || | |> ^|");
        assert_eq!(
            tokens,
            vec![
                Token::ColonColon,
                Token::ColonEq,
                Token::Colon,
                Token::EqEq,
                Token::Eq,
                Token::Arrow,
                Token::Minus,
                Token::PipePipe,
                Token::Pipe,
                Token::PipeGt,
                Token::CaretPipe,
            ]
        );
    }

    #[test]
    fn verify_target_range() {
        let tokens = lex_ok("Commerce[0..500]");
        assert_eq!(
            tokens,
            vec![
                Token::Name("Commerce".into()),
                Token::LBracket,
                Token::IntLit(0),
                Token::DotDot,
                Token::IntLit(500),
                Token::RBracket,
            ]
        );
    }

    #[test]
    fn state_atoms() {
        let tokens = lex_ok("@Pending @OrderStatus::Paid");
        assert_eq!(
            tokens,
            vec![
                Token::At,
                Token::Name("Pending".into()),
                Token::At,
                Token::Name("OrderStatus".into()),
                Token::ColonColon,
                Token::Name("Paid".into()),
            ]
        );
    }

    #[test]
    fn primed_assignment() {
        let tokens = lex_ok("status' = @Paid");
        assert_eq!(
            tokens,
            vec![
                Token::Name("status".into()),
                Token::Prime,
                Token::Eq,
                Token::At,
                Token::Name("Paid".into()),
            ]
        );
    }

    #[test]
    fn spans_are_correct() {
        let tokens = lex("ab cd").unwrap();
        assert_eq!(tokens[0].1, Span { start: 0, end: 2 });
        assert_eq!(tokens[1].1, Span { start: 3, end: 5 });
    }

    #[test]
    fn lex_error_on_invalid_char() {
        let result = lex("module ~ use");
        assert!(result.is_err());
        let errors = result.unwrap_err();
        assert_eq!(errors.len(), 1);
    }

    #[test]
    fn entity_snippet() {
        let src = r"entity Order {
  id: identity
  status: OrderStatus = @Pending
}";
        let tokens = lex_ok(src);
        assert_eq!(tokens[0], Token::Entity);
        assert_eq!(tokens[1], Token::Name("Order".into()));
        assert_eq!(tokens[2], Token::LBrace);
        assert_eq!(tokens[3], Token::Name("id".into()));
    }
}
