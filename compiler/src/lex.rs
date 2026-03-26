use crate::diagnostic::LexError;
use crate::span::Span;
use logos::Logos;

#[derive(Logos, Debug, Clone, PartialEq)]
#[logos(skip r"[ \t\n\r]+")]
#[logos(skip r"//[^\n]*")]
pub enum Token {
    // ── Keywords ──────────────────────────────────────────────────────
    #[token("import")]
    Import,
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
    #[token("entity")]
    Entity,
    #[token("system")]
    System,
    #[token("field")]
    Field,
    #[token("action")]
    Action,
    #[token("event")]
    Event,
    #[token("next")]
    Next,
    #[token("when")]
    When,
    #[token("else")]
    Else,
    #[token("idle")]
    Idle,
    #[token("uses")]
    Uses,
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
    #[token("proof")]
    Proof,
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

    // ── Symbols ───────────────────────────────────────────────────────
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
    #[token("=>")]
    FatArrow,
    #[token("=")]
    Eq,
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
        match self {
            Self::Import => write!(f, "import"),
            Self::As => write!(f, "as"),
            Self::Use => write!(f, "use"),
            Self::Const => write!(f, "const"),
            Self::Fn => write!(f, "fn"),
            Self::Type => write!(f, "type"),
            Self::Entity => write!(f, "entity"),
            Self::System => write!(f, "system"),
            Self::Field => write!(f, "field"),
            Self::Action => write!(f, "action"),
            Self::Event => write!(f, "event"),
            Self::Next => write!(f, "next"),
            Self::When => write!(f, "when"),
            Self::Else => write!(f, "else"),
            Self::Idle => write!(f, "idle"),
            Self::Uses => write!(f, "uses"),
            Self::Where => write!(f, "where"),
            Self::Choose => write!(f, "choose"),
            Self::For => write!(f, "for"),
            Self::Create => write!(f, "create"),
            Self::Pred => write!(f, "pred"),
            Self::Prop => write!(f, "prop"),
            Self::Verify => write!(f, "verify"),
            Self::Assert => write!(f, "assert"),
            Self::Proof => write!(f, "proof"),
            Self::Invariant => write!(f, "invariant"),
            Self::Show => write!(f, "show"),
            Self::Lemma => write!(f, "lemma"),
            Self::Scene => write!(f, "scene"),
            Self::Given => write!(f, "given"),
            Self::Let => write!(f, "let"),
            Self::One => write!(f, "one"),
            Self::Assume => write!(f, "assume"),
            Self::Then => write!(f, "then"),
            Self::Requires => write!(f, "requires"),
            Self::Ensures => write!(f, "ensures"),
            Self::True => write!(f, "true"),
            Self::False => write!(f, "false"),
            Self::Not => write!(f, "not"),
            Self::And => write!(f, "and"),
            Self::Or => write!(f, "or"),
            Self::Implies => write!(f, "implies"),
            Self::In => write!(f, "in"),
            Self::Always => write!(f, "always"),
            Self::Eventually => write!(f, "eventually"),
            Self::All => write!(f, "all"),
            Self::Exists => write!(f, "exists"),
            Self::Some => write!(f, "some"),
            Self::No => write!(f, "no"),
            Self::Lone => write!(f, "lone"),
            Self::Match => write!(f, "match"),
            Self::If => write!(f, "if"),
            Self::ColonColon => write!(f, "::"),
            Self::DotDot => write!(f, ".."),
            Self::Dot => write!(f, "."),
            Self::At => write!(f, "@"),
            Self::Prime => write!(f, "'"),
            Self::Hash => write!(f, "#"),
            Self::EqEq => write!(f, "=="),
            Self::BangEq => write!(f, "!="),
            Self::FatArrow => write!(f, "=>"),
            Self::Eq => write!(f, "="),
            Self::LtEq => write!(f, "<="),
            Self::GtEq => write!(f, ">="),
            Self::Lt => write!(f, "<"),
            Self::Gt => write!(f, ">"),
            Self::Plus => write!(f, "+"),
            Self::Arrow => write!(f, "->"),
            Self::Minus => write!(f, "-"),
            Self::Star => write!(f, "*"),
            Self::Slash => write!(f, "/"),
            Self::Percent => write!(f, "%"),
            Self::PipePipe => write!(f, "||"),
            Self::PipeGt => write!(f, "|>"),
            Self::CaretPipe => write!(f, "^|"),
            Self::Pipe => write!(f, "|"),
            Self::Amp => write!(f, "&"),
            Self::Colon => write!(f, ":"),
            Self::Comma => write!(f, ","),
            Self::LParen => write!(f, "("),
            Self::RParen => write!(f, ")"),
            Self::LBracket => write!(f, "["),
            Self::RBracket => write!(f, "]"),
            Self::LBrace => write!(f, "{{"),
            Self::RBrace => write!(f, "}}"),
            Self::Underscore => write!(f, "_"),
            Self::Name(s) | Self::FloatLit(s) => write!(f, "{s}"),
            Self::IntLit(n) => write!(f, "{n}"),
            Self::DoubleLit(n) => write!(f, "{n}"),
            Self::StringLit(s) => write!(f, "\"{s}\""),
        }
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
        let src = "import as use const fn type entity system field action event";
        let tokens = lex_ok(src);
        assert_eq!(
            tokens,
            vec![
                Token::Import,
                Token::As,
                Token::Use,
                Token::Const,
                Token::Fn,
                Token::Type,
                Token::Entity,
                Token::System,
                Token::Field,
                Token::Action,
                Token::Event,
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

    #[test]
    fn symbols() {
        let src = ":: . .. @ ' # == != => = <= >= < > + -> - * / % || |> ^| | & : , ( ) [ ] { }";
        let tokens = lex_ok(src);
        assert_eq!(
            tokens,
            vec![
                Token::ColonColon,
                Token::Dot,
                Token::DotDot,
                Token::At,
                Token::Prime,
                Token::Hash,
                Token::EqEq,
                Token::BangEq,
                Token::FatArrow,
                Token::Eq,
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
        let tokens = lex_ok(r#""hello" "billing.abide" "submit""#);
        assert_eq!(
            tokens,
            vec![
                Token::StringLit("hello".into()),
                Token::StringLit("billing.abide".into()),
                Token::StringLit("submit".into()),
            ]
        );
    }

    #[test]
    fn comments_skipped() {
        let tokens = lex_ok("import // this is a comment\nuse");
        assert_eq!(tokens, vec![Token::Import, Token::Use]);
    }

    #[test]
    fn multi_char_symbol_priority() {
        // :: vs : , == vs = , -> vs - , || vs | , |> vs |
        let tokens = lex_ok(":: : == = -> - || | |> ^|");
        assert_eq!(
            tokens,
            vec![
                Token::ColonColon,
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
        let result = lex("import ~ use");
        assert!(result.is_err());
        let errors = result.unwrap_err();
        assert_eq!(errors.len(), 1);
    }

    #[test]
    fn entity_snippet() {
        let src = r#"entity Order {
  field id: Id
  field status: OrderStatus = @Pending
}"#;
        let tokens = lex_ok(src);
        assert_eq!(tokens[0], Token::Entity);
        assert_eq!(tokens[1], Token::Name("Order".into()));
        assert_eq!(tokens[2], Token::LBrace);
        assert_eq!(tokens[3], Token::Field);
    }
}
