mod expr;
mod system;
mod types;

use crate::ast::{
    ActivateDecl, AssumeBlock, AssumeItem, AxiomDecl, ByLemmaRef, ConstDecl, Contract, DerivedDecl,
    EntityAction, EntityDecl, EntityItem, EventPath, Expr, ExprKind, FieldDecl, FieldDefault,
    FnDecl, FsmDecl, FsmRow, GivenItem, IncludeDecl, InvariantDecl, InvocArg, LemmaDecl,
    LetBindingDecl, ModuleDecl, Param, PredDecl, Program, PropDecl, SceneDecl, SceneItem,
    StoreDecl, ThenItem, TheoremDecl, TopDecl, TypedParam, UnderBlock, UseDecl, UseItem,
    VerifyDecl, Visibility, WhenItem,
};
use crate::diagnostic::ParseError;
use crate::lex::Token;
use crate::span::Span;

type WhenCallParts = (String, String, Vec<InvocArg>, Option<String>, Span);

// ── Binding powers (Pratt parser) ────────────────────────────────────
// ── Binding power constants ──────────────────────────────────────────
//
// Pratt parser binding powers. Left/right bp encode precedence and
// associativity: left-assoc uses l < r, right-assoc uses l = r.
// Higher numbers bind tighter. Gaps between levels allow future insertion.
//
// Composition operators — four distinct levels ():
// |, ^|, |> → choice (loosest composition)
// || → concurrent
// & → same-step
// -> → sequence (tightest composition)

/// Choice operators: |, ^|, |> (loosest composition, left-assoc)
pub(super) const BP_CHOICE: (u8, u8) = (1, 2);
/// Concurrent: || (left-assoc)
const BP_CONCURRENT: (u8, u8) = (3, 4);
/// Same-step: & (left-assoc)
const BP_SAME_STEP: (u8, u8) = (5, 6);
/// Sequence: -> (tightest composition, right-assoc)
const BP_SEQUENCE: (u8, u8) = (7, 7);
/// Named pair: name: expr (same level as choice)
pub(super) const BP_NAMED_PAIR: u8 = 1;
/// Named pair rhs starts above choice
pub(super) const BP_NAMED_PAIR_RHS: u8 = 3;

/// Implies (right-assoc)
const BP_IMPLIES: (u8, u8) = (9, 9);
/// Until (right-assoc, same level as implies — `P until Q implies R` = `(P until Q) implies R`)
const BP_UNTIL: (u8, u8) = (10, 9);
/// Prefix operators at implies level: always, eventually, assert, quantifiers, let, lambda, match
// Temporal operators bind tighter than
// every logical operator (`implies`, `or`, `and`, `not`). The previous
// value (9) sat between `BP_IMPLIES`/`BP_NAMED_PAIR_RHS` and the
// boolean operators, so `always P implies Q` parsed as `(always P)
// implies Q` (correct) but `always P or Q` parsed as `always (P or Q)`
// (wrong). Raising it to 17 — *equal* to `BP_NOT` and `BP_NOT_RHS`,
// strictly above `BP_AND` (15) and `BP_OR` (13) — makes
// temporal/quantifier/let/lambda/match/assert/assume bodies stop at
// every logical operator. Sharing the binding power with `not` is
// safe because the dispatches are matched on distinct tokens; the
// shared value just means `not` and `always` parse their operands
// with the same right-binding strength. Equality, comparison,
// arithmetic, unary minus, and postfix forms all bind tighter
// (>= 19), so they continue to be consumed inside the body — which
// matches the spec's "temporal binds tightly" rule.
pub(super) const BP_PREFIX_EXPR: u8 = 17;
/// Assignment: = (right-assoc)
const BP_ASSIGN: (u8, u8) = (11, 11);
/// Or (left-assoc)
const BP_OR: (u8, u8) = (13, 14);
/// And (left-assoc)
const BP_AND: (u8, u8) = (15, 16);
/// Not (prefix)
pub(super) const BP_NOT: u8 = 17;
/// Not operand bp (binds tighter than and)
pub(super) const BP_NOT_RHS: u8 = 17;
/// Equality: ==, != (left-assoc)
const BP_EQUALITY: (u8, u8) = (19, 20);
// Membership `in` shares `BP_EQUALITY` level.
/// Comparison: <, >, <=, >= (left-assoc)
const BP_COMPARISON: (u8, u8) = (21, 22);
/// Additive: +, - (left-assoc)
const BP_ADDITIVE: (u8, u8) = (23, 24);
/// Multiplicative: *, /, % (left-assoc)
const BP_MULTIPLICATIVE: (u8, u8) = (25, 26);
/// Unary prefix: -, # (negation, cardinality)
pub(super) const BP_UNARY: u8 = 27;
/// Unary operand bp (binds at multiplicative level so -a*b = (-a)*b)
pub(super) const BP_UNARY_RHS: u8 = 27;
/// Postfix: ',., (), [] (prime, field, call, index)
const BP_POSTFIX: u8 = 29;

pub(super) fn infix_bp(op: &Token) -> Option<(u8, u8)> {
    match op {
        Token::Pipe | Token::CaretPipe | Token::PipeGt => Some(BP_CHOICE),
        Token::PipePipe => Some(BP_CONCURRENT),
        Token::Amp => Some(BP_SAME_STEP),
        Token::Arrow => Some(BP_SEQUENCE),
        Token::Implies => Some(BP_IMPLIES),
        Token::Until | Token::Since => Some(BP_UNTIL),
        Token::Eq => Some(BP_ASSIGN),
        Token::Or => Some(BP_OR),
        Token::And => Some(BP_AND),
        Token::EqEq | Token::BangEq | Token::In | Token::BangStar => Some(BP_EQUALITY),
        Token::Lt | Token::Gt | Token::LtEq | Token::GtEq => Some(BP_COMPARISON),
        Token::Plus | Token::Minus | Token::Diamond => Some(BP_ADDITIVE),
        Token::Star | Token::Slash | Token::Percent => Some(BP_MULTIPLICATIVE),
        _ => None,
    }
}

pub(super) fn postfix_bp(op: &Token) -> Option<u8> {
    match op {
        Token::Prime | Token::Dot | Token::LParen | Token::LBracket => Some(BP_POSTFIX),
        _ => None,
    }
}

fn is_top_level_starter(tok: &Token) -> bool {
    matches!(
        tok,
        Token::Module
            | Token::Include
            | Token::Use
            | Token::Const
            | Token::Fn
            | Token::Type
            | Token::Enum
            | Token::Struct
            | Token::Entity
            | Token::Interface
            | Token::Extern
            | Token::System
            | Token::Proc
            | Token::Program
            | Token::Pred
            | Token::Prop
            | Token::Verify
            | Token::Theorem
            | Token::Lemma
            | Token::Scene
            | Token::Axiom
            | Token::Under
    )
}

fn is_entity_item_starter(tok: &Token, _next: Option<&Token>) -> bool {
    matches!(
        tok,
        Token::Action | Token::Derived | Token::Invariant | Token::Fsm | Token::Name(_)
    )
}

fn is_system_item_starter(tok: &Token, next: Option<&Token>) -> bool {
    matches!(
        tok,
        Token::Dep
            | Token::Command
            | Token::Step
            | Token::Query
            | Token::Pred
            | Token::Derived
            | Token::Invariant
    ) || matches!(tok, Token::Name(_)) && matches!(next, Some(Token::Colon))
}

fn is_interface_item_starter(tok: &Token, _next: Option<&Token>) -> bool {
    matches!(tok, Token::Command | Token::Query)
}

fn is_extern_item_starter(tok: &Token, _next: Option<&Token>) -> bool {
    matches!(tok, Token::Command | Token::May | Token::Assume)
}

fn is_program_item_starter(tok: &Token, _next: Option<&Token>) -> bool {
    matches!(
        tok,
        Token::Let | Token::Use | Token::Invariant | Token::Proc
    )
}

fn is_proc_item_starter(tok: &Token, _next: Option<&Token>) -> bool {
    matches!(tok, Token::Name(_) | Token::Match | Token::Use)
}

fn is_scene_item_starter(tok: &Token, _next: Option<&Token>) -> bool {
    matches!(tok, Token::Given | Token::When | Token::Then)
}

fn is_given_item_starter(tok: &Token, _next: Option<&Token>) -> bool {
    matches!(tok, Token::Store | Token::Activate | Token::Let)
}

fn is_when_item_starter(tok: &Token, _next: Option<&Token>) -> bool {
    matches!(tok, Token::Assume | Token::Let | Token::Name(_))
}

fn is_event_item_starter(tok: &Token) -> bool {
    matches!(tok, Token::Choose | Token::For | Token::Create)
        || !matches!(tok, Token::Semi | Token::RBrace | Token::Return)
}

pub struct ParseOutput {
    pub program: Program,
    pub errors: Vec<ParseError>,
}

/// Parse a string into a `Program`. Convenience wrapper for REPL use.
pub fn parse_string(input: &str) -> Result<crate::ast::Program, ParseError> {
    let output = parse_string_recovering(input).map_err(|errs| ParseError::General {
        msg: errs
            .into_iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
            .join("; "),
        span: (0..0).into(),
        help: None,
    })?;
    if let Some(err) = output.errors.into_iter().next() {
        return Err(err);
    }
    Ok(output.program)
}

/// Parse a string into a partial `Program`, retaining parse diagnostics.
pub fn parse_string_recovering(
    input: &str,
) -> Result<ParseOutput, Vec<crate::diagnostic::LexError>> {
    let tokens = crate::lex::lex(input)?;
    let mut parser = Parser::new(tokens);
    Ok(parser.parse_program_output())
}

// ── Parser state ─────────────────────────────────────────────────────

pub struct Parser {
    tokens: Vec<(Token, Span)>,
    pos: usize,
    errors: Vec<ParseError>,
    recovering: bool,
    /// When true, `Token::In` is not treated as an infix operator.
    /// Used inside `let` binding values to avoid consuming the `let...in` separator.
    no_in: bool,
}

impl Parser {
    pub fn new(tokens: Vec<(Token, Span)>) -> Self {
        Self {
            tokens,
            pos: 0,
            errors: Vec::new(),
            recovering: false,
            no_in: false,
        }
    }

    // ── Helpers ──────────────────────────────────────────────────────

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos).map(|(t, _)| t)
    }

    fn peek_at(&self, offset: usize) -> Option<&Token> {
        self.tokens.get(self.pos + offset).map(|(t, _)| t)
    }

    fn cur_span(&self) -> Span {
        if self.pos < self.tokens.len() {
            self.tokens[self.pos].1
        } else if let Some(last) = self.tokens.last() {
            Span {
                start: last.1.end,
                end: last.1.end,
            }
        } else {
            Span { start: 0, end: 0 }
        }
    }

    fn at_end(&self) -> bool {
        self.pos >= self.tokens.len()
    }

    fn advance(&mut self) -> (Token, Span) {
        let item = self.tokens[self.pos].clone();
        self.pos += 1;
        item
    }

    fn push_recovery_error(&mut self, err: ParseError) {
        if self.recovering {
            self.errors.push(err);
        }
    }

    fn recover_node(
        &mut self,
        mut should_stop: impl FnMut(&Token, Option<&Token>, usize, usize, usize) -> bool,
    ) -> crate::ast::ErrorNode {
        let start = self.cur_span();
        let mut skipped_tokens = Vec::new();
        let mut last_span = start;
        let mut brace_depth = 0usize;
        let mut paren_depth = 0usize;
        let mut bracket_depth = 0usize;
        let mut consumed_any = false;

        while !self.at_end() {
            if consumed_any
                && should_stop(
                    self.peek().expect("not at end"),
                    self.peek_at(1),
                    brace_depth,
                    paren_depth,
                    bracket_depth,
                )
            {
                break;
            }
            let (tok, span) = self.advance();
            consumed_any = true;
            last_span = span;
            skipped_tokens.push(tok.to_string());
            match tok {
                Token::LBrace => brace_depth += 1,
                Token::RBrace => brace_depth = brace_depth.saturating_sub(1),
                Token::LParen => paren_depth += 1,
                Token::RParen => paren_depth = paren_depth.saturating_sub(1),
                Token::LBracket => bracket_depth += 1,
                Token::RBracket => bracket_depth = bracket_depth.saturating_sub(1),
                _ => {}
            }
        }

        crate::ast::ErrorNode {
            skipped_tokens,
            span: start.merge(last_span),
        }
    }

    fn recover_to_top_level(&mut self) -> crate::ast::ErrorNode {
        self.recover_node(|tok, _next, braces, parens, brackets| {
            braces == 0 && parens == 0 && brackets == 0 && is_top_level_starter(tok)
        })
    }

    fn consume_current_as_error_node(&mut self) -> crate::ast::ErrorNode {
        let start = self.cur_span();
        if self.at_end() {
            return crate::ast::ErrorNode {
                skipped_tokens: Vec::new(),
                span: start,
            };
        }
        let (tok, span) = self.advance();
        crate::ast::ErrorNode {
            skipped_tokens: vec![tok.to_string()],
            span: start.merge(span),
        }
    }

    fn recover_to_brace_item(
        &mut self,
        is_item_starter: fn(&Token, Option<&Token>) -> bool,
    ) -> crate::ast::ErrorNode {
        self.recover_node(|tok, next, braces, parens, brackets| {
            braces == 0
                && parens == 0
                && brackets == 0
                && (matches!(tok, Token::RBrace) || is_item_starter(tok, next))
        })
    }

    fn recover_to_event_item(&mut self) -> crate::ast::ErrorNode {
        if matches!(self.peek(), Some(Token::Semi)) {
            return self.consume_current_as_error_node();
        }
        self.recover_node(|tok, _next, braces, parens, brackets| {
            braces == 0
                && parens == 0
                && brackets == 0
                && (matches!(tok, Token::RBrace | Token::Semi | Token::Return)
                    || is_event_item_starter(tok))
        })
    }

    fn recover_to_block_item(&mut self) -> crate::ast::ErrorNode {
        if matches!(self.peek(), Some(Token::Semi)) {
            return self.consume_current_as_error_node();
        }
        self.recover_node(|tok, _next, braces, parens, brackets| {
            braces == 0
                && parens == 0
                && brackets == 0
                && matches!(tok, Token::RBrace | Token::Semi)
        })
    }

    fn expect(&mut self, expected: &Token) -> Result<Span, ParseError> {
        match self.peek() {
            Some(tok) if tok == expected => Ok(self.advance().1),
            Some(tok) => Err(ParseError::expected(
                &format!("`{expected}`"),
                &format!("`{tok}`"),
                self.cur_span(),
            )),
            None => Err(ParseError::eof(self.cur_span())),
        }
    }

    fn eat(&mut self, expected: &Token) -> Option<Span> {
        if self.peek() == Some(expected) {
            Some(self.advance().1)
        } else {
            None
        }
    }

    fn expect_name(&mut self) -> Result<(String, Span), ParseError> {
        match self.peek() {
            Some(Token::Name(_)) => {
                let (tok, span) = self.advance();
                if let Token::Name(name) = tok {
                    Ok((name, span))
                } else {
                    unreachable!()
                }
            }
            // `activate` and `store` are soft keywords —
            // they are valid identifiers in name position (e.g., entity
            // action names, variable names).
            Some(Token::Activate) => {
                let span = self.advance().1;
                Ok(("activate".to_owned(), span))
            }
            Some(Token::Store) => {
                let span = self.advance().1;
                Ok(("store".to_owned(), span))
            }
            Some(tok) => Err(ParseError::expected(
                "identifier",
                &format!("`{tok}`"),
                self.cur_span(),
            )),
            None => Err(ParseError::eof(self.cur_span())),
        }
    }

    fn expect_string(&mut self) -> Result<(String, Span), ParseError> {
        match self.peek() {
            Some(Token::StringLit(_)) => {
                let (tok, span) = self.advance();
                if let Token::StringLit(s) = tok {
                    Ok((s, span))
                } else {
                    unreachable!()
                }
            }
            Some(tok) => Err(ParseError::expected(
                "string literal",
                &format!("`{tok}`"),
                self.cur_span(),
            )),
            None => Err(ParseError::eof(self.cur_span())),
        }
    }

    fn expect_int(&mut self) -> Result<(i64, Span), ParseError> {
        match self.peek() {
            Some(Token::IntLit(_)) => {
                let (tok, span) = self.advance();
                if let Token::IntLit(n) = tok {
                    Ok((n, span))
                } else {
                    unreachable!()
                }
            }
            Some(tok) => Err(ParseError::expected(
                "integer literal",
                &format!("`{tok}`"),
                self.cur_span(),
            )),
            None => Err(ParseError::eof(self.cur_span())),
        }
    }

    // ── Program ──────────────────────────────────────────────────────

    /// Parse a program, stopping at the first error.
    pub fn parse_program(&mut self) -> Result<Program, ParseError> {
        self.errors.clear();
        self.recovering = false;
        let (program, errors) = self.parse_program_recovering();
        if let Some(err) = errors.into_iter().next() {
            return Err(err);
        }
        Ok(program)
    }

    /// Parse a program and retain all recoverable parse diagnostics.
    pub fn parse_program_output(&mut self) -> ParseOutput {
        let (program, errors) = self.parse_program_recovering();
        ParseOutput { program, errors }
    }

    /// Parse a program with error recovery.
    ///
    /// On parse error, skips tokens until the next top-level keyword
    /// and continues parsing. Returns a partial program with all
    /// successfully parsed declarations and all accumulated errors.
    pub fn parse_program_recovering(&mut self) -> (Program, Vec<ParseError>) {
        self.errors.clear();
        self.recovering = true;
        let start = self.cur_span();
        let mut decls = Vec::new();
        while !self.at_end() {
            let pos_before = self.pos;
            match self.top_decl() {
                Ok(decl) => decls.push(decl),
                Err(err) => {
                    self.push_recovery_error(err);
                    if self.pos == pos_before && self.at_end() {
                        break;
                    }
                    decls.push(TopDecl::Error(self.recover_to_top_level()));
                }
            }
        }
        let span = if decls.is_empty() {
            start
        } else {
            start.merge(self.cur_span())
        };
        self.recovering = false;
        (Program { decls, span }, std::mem::take(&mut self.errors))
    }

    fn top_decl(&mut self) -> Result<TopDecl, ParseError> {
        match self.peek() {
            Some(Token::Module) => Ok(TopDecl::Module(self.module_decl()?)),
            Some(Token::Include) => Ok(TopDecl::Include(self.include_decl()?)),
            Some(Token::Use) => Ok(TopDecl::Use(self.use_decl()?)),
            Some(Token::Const) => Ok(TopDecl::Const(self.const_decl()?)),
            Some(Token::Fn) => Ok(TopDecl::Fn(self.fn_decl()?)),
            Some(Token::Type) => self.alias_decl(),
            Some(Token::Enum) => self.enum_decl(),
            Some(Token::Struct) => self.struct_decl(),
            Some(Token::Entity) => Ok(TopDecl::Entity(self.entity_decl()?)),
            Some(Token::Interface) => Ok(TopDecl::Interface(self.interface_decl()?)),
            Some(Token::Extern) => Ok(TopDecl::Extern(self.extern_decl()?)),
            Some(Token::System) => Ok(TopDecl::System(self.system_decl()?)),
            Some(Token::Proc) => Ok(TopDecl::Proc(self.proc_decl()?)),
            Some(Token::Workflow) => Err(ParseError::expected_with_help(
                "top-level declaration",
                "`workflow`",
                self.cur_span(),
                "the `workflow` keyword has been replaced by reusable named `proc` declarations plus `program`-side `use proc_name(...)`",
            )),
            Some(Token::Program) => Ok(TopDecl::Program(self.program_decl()?)),
            Some(Token::Pred) => Ok(TopDecl::Pred(self.pred_decl()?)),
            Some(Token::Prop) => Ok(TopDecl::Prop(self.prop_decl()?)),
            Some(Token::Verify) => Ok(TopDecl::Verify(self.verify_decl()?)),
            Some(Token::Theorem) => Ok(TopDecl::Theorem(self.theorem_decl()?)),
            Some(Token::Lemma) => Ok(TopDecl::Lemma(self.lemma_decl()?)),
            Some(Token::Scene) => Ok(TopDecl::Scene(self.scene_decl()?)),
            Some(Token::Axiom) => Ok(TopDecl::Axiom(self.axiom_decl()?)),
            Some(Token::Under) => Ok(TopDecl::Under(self.under_block()?)),
            // `derived` declarations only live
            // inside entity or system bodies. Reject at the top level
            // with a hint pointing the user at the correct context.
            Some(Token::Derived) => Err(ParseError::expected_with_help(
                "top-level declaration",
                "`derived`",
                self.cur_span(),
                crate::messages::DERIVED_INVALID_SCOPE,
            )),
            // Detect invalid keywords and suggest correct syntax
            Some(Token::Name(ref name)) if name == "import" => Err(ParseError::expected_with_help(
                "top-level declaration",
                "`import`",
                self.cur_span(),
                crate::messages::HINT_IMPORT_KEYWORD,
            )),
            Some(Token::Name(ref name)) if name == "proof" => Err(ParseError::expected_with_help(
                "top-level declaration",
                "`proof`",
                self.cur_span(),
                crate::messages::HINT_PROOF_KEYWORD,
            )),
            Some(Token::Name(ref name)) if name == "field" => Err(ParseError::expected_with_help(
                "top-level declaration",
                "`field`",
                self.cur_span(),
                crate::messages::HINT_FIELD_KEYWORD_TOP,
            )),
            Some(tok) => Err(ParseError::expected(
                "top-level declaration",
                &format!("`{tok}`"),
                self.cur_span(),
            )),
            None => Err(ParseError::eof(self.cur_span())),
        }
    }

    // ── Module / Include / Use ──────────────────────────────────────

    fn module_decl(&mut self) -> Result<ModuleDecl, ParseError> {
        let start = self.expect(&Token::Module)?;
        let (name, end) = self.expect_name()?;
        let end = self.eat(&Token::Semi).unwrap_or(end);
        Ok(ModuleDecl {
            name,
            span: start.merge(end),
        })
    }

    fn include_decl(&mut self) -> Result<IncludeDecl, ParseError> {
        let start = self.expect(&Token::Include)?;
        let (path, end) = self.expect_string()?;
        Ok(IncludeDecl {
            path,
            span: start.merge(end),
        })
    }

    fn use_decl(&mut self) -> Result<UseDecl, ParseError> {
        let start = self.expect(&Token::Use)?;
        let (module, _) = self.expect_name()?;
        self.expect(&Token::ColonColon)?;

        if let Some(star_span) = self.eat(&Token::Star) {
            return Ok(UseDecl::All {
                module,
                span: start.merge(star_span),
            });
        }

        if self.eat(&Token::LBrace).is_some() {
            let items = self.comma_sep(&Token::RBrace, Parser::use_item)?;
            let end = self.expect(&Token::RBrace)?;
            return Ok(UseDecl::Items {
                module,
                items,
                span: start.merge(end),
            });
        }

        let (name, name_span) = self.expect_name()?;
        if self.eat(&Token::As).is_some() {
            let (alias, end) = self.expect_name()?;
            Ok(UseDecl::Alias {
                module,
                name,
                alias,
                span: start.merge(end),
            })
        } else {
            Ok(UseDecl::Single {
                module,
                name,
                span: start.merge(name_span),
            })
        }
    }

    fn use_item(&mut self) -> Result<UseItem, ParseError> {
        let (name, span) = self.expect_name()?;
        if self.eat(&Token::As).is_some() {
            let (alias, end) = self.expect_name()?;
            Ok(UseItem::Alias {
                name,
                alias,
                span: span.merge(end),
            })
        } else {
            Ok(UseItem::Name { name, span })
        }
    }

    // ── Constants and Functions ───────────────────────────────────────

    fn const_decl(&mut self) -> Result<ConstDecl, ParseError> {
        let start = self.expect(&Token::Const)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::Eq)?;
        let value = self.expr()?;
        Ok(ConstDecl {
            span: start.merge(value.span),
            name,
            visibility: Visibility::Private,
            value,
        })
    }

    fn fn_decl(&mut self) -> Result<FnDecl, ParseError> {
        let start = self.expect(&Token::Fn)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::LParen)?;
        let params = self.comma_sep(&Token::RParen, Parser::typed_param)?;
        self.expect(&Token::RParen)?;
        self.expect(&Token::Colon)?;
        // Return type: no refinement allowed (use ensures for return constraints)
        let ret_type = self.type_ref_no_refine()?;
        let contracts = self.contracts()?;
        // Two body forms:
        // = expr (pure, no contracts or contracts allowed)
        // { body } (imperative form with blocks, consistent with action/event)
        let body = if matches!(self.peek(), Some(Token::LBrace)) {
            self.parse_block()?
        } else {
            self.expect(&Token::Eq)?;
            self.expr()?
        };
        Ok(FnDecl {
            span: start.merge(body.span),
            name,
            visibility: Visibility::Private,
            params,
            ret_type,
            contracts,
            body,
        })
    }

    fn typed_param(&mut self) -> Result<TypedParam, ParseError> {
        let (name, start) = self.expect_name()?;
        self.expect(&Token::Colon)?;
        let ty = self.type_ref()?;
        Ok(TypedParam {
            span: start.merge(ty.span),
            name,
            ty,
        })
    }

    // ── Entity Declarations ──────────────────────────────────────────

    fn entity_decl(&mut self) -> Result<EntityDecl, ParseError> {
        let start = self.expect(&Token::Entity)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::LBrace)?;
        let mut items = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) && !self.at_end() {
            match self.entity_item() {
                Ok(item) => items.push(item),
                Err(err) if self.recovering => {
                    self.push_recovery_error(err);
                    items.push(EntityItem::Error(
                        self.recover_to_brace_item(is_entity_item_starter),
                    ));
                }
                Err(err) => return Err(err),
            }
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(EntityDecl {
            name,
            visibility: Visibility::Private,
            items,
            span: start.merge(end),
        })
    }

    fn entity_item(&mut self) -> Result<EntityItem, ParseError> {
        match self.peek() {
            Some(Token::Action) => Ok(EntityItem::Action(self.entity_action()?)),
            // `derived NAME = EXPR` declarations
            // live alongside fields and actions in the entity body.
            Some(Token::Derived) => Ok(EntityItem::Derived(self.derived_decl()?)),
            // `invariant NAME { EXPR }` declarations
            // live alongside fields, derived fields, and actions in the
            // entity body.
            Some(Token::Invariant) => Ok(EntityItem::Invariant(self.invariant_decl()?)),
            // `fsm FIELD { ROWS }` declarations live
            // on entity fields. The fsm body is a transition table; see
            // `fsm_decl` for the row syntax.
            Some(Token::Fsm) => Ok(EntityItem::Fsm(self.fsm_decl()?)),
            Some(Token::Name(ref name)) if name == "field" => {
                // Detect invalid 'field' keyword inside entity body
                Err(ParseError::expected_with_help(
                    "field declaration or `action`",
                    "`field`",
                    self.cur_span(),
                    crate::messages::HINT_FIELD_KEYWORD_ENTITY,
                ))
            }
            Some(Token::Name(_)) => Ok(EntityItem::Field(self.field_decl()?)),
            Some(tok) => Err(ParseError::expected(
                "field declaration, `action`, `derived`, `invariant`, or `fsm`",
                &format!("`{tok}`"),
                self.cur_span(),
            )),
            None => Err(ParseError::eof(self.cur_span())),
        }
    }

    /// parse an `invariant NAME { EXPR }`
    /// declaration. Per invariants take no parameters; the
    /// parser rejects parameterized forms with `INVARIANT_PARAM_REJECTED`.
    fn invariant_decl(&mut self) -> Result<InvariantDecl, ParseError> {
        let start = self.expect(&Token::Invariant)?;
        let (name, _) = self.expect_name()?;
        // reject parameter lists. The next token after
        // the name must be `{` (the body), not `(`.
        if matches!(self.peek(), Some(Token::LParen)) {
            return Err(ParseError::expected_with_help(
                "invariant body `{ ... }`",
                "`(`",
                self.cur_span(),
                crate::messages::INVARIANT_PARAM_REJECTED,
            ));
        }
        self.expect(&Token::LBrace)?;
        let body = self.expr()?;
        let end = self.expect(&Token::RBrace)?;
        Ok(InvariantDecl {
            name,
            body,
            span: start.merge(end),
        })
    }

    /// parse a `derived NAME = EXPR` declaration.
    ///
    /// The body is an arbitrary expression, so the existing expression
    /// parser handles both single-expression form (`derived x = a + b`)
    /// and block form (`derived x = { let t = a; t + b }`) for free.
    /// `` permits both.
    fn derived_decl(&mut self) -> Result<DerivedDecl, ParseError> {
        let start = self.expect(&Token::Derived)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::Eq)?;
        let body = self.expr()?;
        let span = start.merge(body.span);
        Ok(DerivedDecl { name, body, span })
    }

    /// parse an `fsm FIELD { ROWS }` declaration.
    ///
    /// Each row in the body has the shape `@from -> @to1 | @to2 |...`.
    /// A row with no targets (`@from ->`) declares the source state
    /// terminal. Rows are not separated by punctuation; the next row
    /// is detected by the leading `@` (and the body terminates at `}`).
    ///
    /// To distinguish a terminal row followed by another row from a
    /// row with one target, the parser uses three-token lookahead at
    /// the head of the targets list: if the upcoming sequence is
    /// `@ NAME ->`, the `@NAME` belongs to the *next* row's source,
    /// not the current row's targets.
    fn fsm_decl(&mut self) -> Result<FsmDecl, ParseError> {
        let start = self.expect(&Token::Fsm)?;
        let (field, _) = self.expect_name()?;
        self.expect(&Token::LBrace)?;
        let mut rows: Vec<FsmRow> = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) {
            let row_start = self.cur_span();
            // Source state: @name
            self.expect(&Token::At)?;
            let (from, _) = self.expect_name()?;
            let mut row_end = self.expect(&Token::Arrow)?;
            // Target states: optional `@name (| @name)*`. We must
            // disambiguate `@from1 -> \n @from2 ->` (terminal then
            // next row) from `@from -> @t \n @from2 ->` (single
            // target then next row). Three-token lookahead: if
            // `@ NAME ->`, the `@NAME` is the next row's source.
            let next_is_target = matches!(self.peek(), Some(Token::At))
                && matches!(self.peek_at(1), Some(Token::Name(_)))
                && !matches!(self.peek_at(2), Some(Token::Arrow));
            let mut targets: Vec<String> = Vec::new();
            if next_is_target {
                self.expect(&Token::At)?;
                let (first, first_span) = self.expect_name()?;
                targets.push(first);
                row_end = first_span;
                while self.eat(&Token::Pipe).is_some() {
                    self.expect(&Token::At)?;
                    let (next_name, next_span) = self.expect_name()?;
                    targets.push(next_name);
                    row_end = next_span;
                }
            }
            rows.push(FsmRow {
                from,
                targets,
                span: row_start.merge(row_end),
            });
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(FsmDecl {
            field,
            rows,
            span: start.merge(end),
        })
    }

    fn field_decl(&mut self) -> Result<FieldDecl, ParseError> {
        let start = self.cur_span();
        let (name, _) = self.expect_name()?;
        self.expect(&Token::Colon)?;
        let ty = self.type_ref()?;
        let default = if self.eat(&Token::Eq).is_some() {
            Some(FieldDefault::Value(self.expr_bp(28)?)) // atom-level only (Expr14)
        } else if self.eat(&Token::In).is_some() {
            // in { expr, expr,... }
            self.expect(&Token::LBrace)?;
            let mut exprs = vec![self.expr_bp(28)?];
            while self.eat(&Token::Comma).is_some() {
                if self.peek() == Some(&Token::RBrace) {
                    break; // trailing comma
                }
                exprs.push(self.expr_bp(28)?);
            }
            self.expect(&Token::RBrace)?;
            Some(FieldDefault::In(exprs))
        } else if self.eat(&Token::Where).is_some() {
            // where predicate
            Some(FieldDefault::Where(self.expr()?))
        } else {
            None
        };
        let end_span = match &default {
            Some(FieldDefault::Value(e)) => e.span,
            Some(FieldDefault::In(es)) => es.last().map_or(ty.span, |e| e.span),
            Some(FieldDefault::Where(e)) => e.span,
            None => ty.span,
        };
        Ok(FieldDecl {
            name,
            ty,
            default,
            span: start.merge(end_span),
        })
    }

    fn entity_action(&mut self) -> Result<EntityAction, ParseError> {
        let start = self.expect(&Token::Action)?;
        let (name, _) = self.expect_name()?;

        // Optional ref params: [params]
        let ref_params = if self.eat(&Token::LBracket).is_some() {
            let params = self.comma_sep(&Token::RBracket, Parser::param)?;
            self.expect(&Token::RBracket)?;
            params
        } else {
            Vec::new()
        };

        // Value params: (params)
        self.expect(&Token::LParen)?;
        let params = self.comma_sep(&Token::RParen, Parser::param)?;
        self.expect(&Token::RParen)?;

        let contracts = self.contracts()?;

        self.expect(&Token::LBrace)?;
        let mut body = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) {
            while self.eat(&Token::Semi).is_some() {}
            if matches!(self.peek(), Some(Token::RBrace)) {
                break;
            }
            body.push(self.expr()?);
        }
        let end = self.expect(&Token::RBrace)?;

        Ok(EntityAction {
            name,
            ref_params,
            params,
            contracts,
            body,
            span: start.merge(end),
        })
    }

    fn param(&mut self) -> Result<Param, ParseError> {
        let mutable = self.eat(&Token::Mut).is_some();
        let (name, start) = self.expect_name()?;
        self.expect(&Token::Colon)?;
        let ty = self.type_ref()?;
        Ok(Param {
            name,
            ty: ty.clone(),
            mutable,
            span: start.merge(ty.span),
        })
    }

    fn contracts(&mut self) -> Result<Vec<Contract>, ParseError> {
        let mut contracts = Vec::new();
        loop {
            match self.peek() {
                Some(Token::Requires) => {
                    let start = self.advance().1;
                    let expr = self.expr()?;
                    contracts.push(Contract::Requires {
                        span: start.merge(expr.span),
                        expr,
                    });
                }
                Some(Token::Ensures) => {
                    let start = self.advance().1;
                    let expr = self.expr()?;
                    contracts.push(Contract::Ensures {
                        span: start.merge(expr.span),
                        expr,
                    });
                }
                Some(Token::Decreases) => {
                    let start = self.advance().1;
                    // decreases * (escape hatch)
                    if matches!(self.peek(), Some(Token::Star)) {
                        let end = self.advance().1;
                        contracts.push(Contract::Decreases {
                            measures: vec![],
                            star: true,
                            span: start.merge(end),
                        });
                    } else {
                        // decreases expr, expr,... (comma-separated measures)
                        let first = self.expr()?;
                        let mut measures = vec![first];
                        while matches!(self.peek(), Some(Token::Comma)) {
                            self.advance();
                            measures.push(self.expr()?);
                        }
                        let end = measures.last().unwrap().span;
                        contracts.push(Contract::Decreases {
                            span: start.merge(end),
                            measures,
                            star: false,
                        });
                    }
                }
                Some(Token::Invariant) => {
                    let start = self.advance().1;
                    let expr = self.expr()?;
                    contracts.push(Contract::Invariant {
                        span: start.merge(expr.span),
                        expr,
                    });
                }
                _ => break,
            }
        }
        Ok(contracts)
    }

    // ── Imperative blocks (fn body) ─────────────────────────────────

    fn parse_block(&mut self) -> Result<Expr, ParseError> {
        let start = self.expect(&Token::LBrace)?;
        let mut items = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) && !self.at_end() {
            match self.block_item() {
                Ok(item) => items.push(item),
                Err(err) if self.recovering => {
                    self.push_recovery_error(err);
                    let node = self.recover_to_block_item();
                    items.push(Expr {
                        span: node.span,
                        kind: ExprKind::Error(node),
                    });
                }
                Err(err) => return Err(err),
            }
            while self.eat(&Token::Semi).is_some() {}
        }
        let end = self.expect(&Token::RBrace)?;
        let span = start.merge(end);
        // Single-expression block: unwrap to avoid unnecessary Block wrapper
        if items.len() == 1 && !matches!(items[0].kind, ExprKind::VarDecl { .. }) {
            let item = items.into_iter().next().unwrap();
            return Ok(Expr {
                kind: item.kind,
                span,
            });
        }
        Ok(Expr {
            kind: ExprKind::Block(items),
            span,
        })
    }

    fn block_item(&mut self) -> Result<Expr, ParseError> {
        match self.peek() {
            Some(Token::Var) => self.parse_var_decl(),
            Some(Token::While) => self.parse_while(),
            Some(Token::If) => self.parse_if_else(),
            _ => self.expr(),
        }
    }

    fn parse_var_decl(&mut self) -> Result<Expr, ParseError> {
        let start = self.expect(&Token::Var)?;
        let (name, _) = self.expect_name()?;
        let ty = if self.eat(&Token::Colon).is_some() {
            Some(self.type_ref()?)
        } else {
            None
        };
        self.expect(&Token::Eq)?;
        let init = self.expr()?;
        let end = init.span;
        Ok(Expr {
            kind: ExprKind::VarDecl {
                name,
                ty,
                init: Box::new(init),
            },
            span: start.merge(end),
        })
    }

    fn parse_while(&mut self) -> Result<Expr, ParseError> {
        let start = self.expect(&Token::While)?;
        let cond = self.expr()?;
        let contracts = self.contracts()?;
        let body = self.parse_block()?;
        let end = body.span;
        Ok(Expr {
            kind: ExprKind::While {
                cond: Box::new(cond),
                contracts,
                body: Box::new(body),
            },
            span: start.merge(end),
        })
    }

    fn parse_if_else(&mut self) -> Result<Expr, ParseError> {
        let start = self.expect(&Token::If)?;
        let cond = self.expr()?;
        let then_body = self.parse_block()?;
        let else_body = if self.eat(&Token::Else).is_some() {
            if matches!(self.peek(), Some(Token::If)) {
                // else if...
                Some(Box::new(self.parse_if_else()?))
            } else {
                Some(Box::new(self.parse_block()?))
            }
        } else {
            None
        };
        let end = else_body.as_ref().map_or(then_body.span, |e| e.span);
        Ok(Expr {
            kind: ExprKind::IfElse {
                cond: Box::new(cond),
                then_body: Box::new(then_body),
                else_body,
            },
            span: start.merge(end),
        })
    }

    // ── Predicates and Properties ────────────────────────────────────

    fn pred_decl(&mut self) -> Result<PredDecl, ParseError> {
        let start = self.expect(&Token::Pred)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::LParen)?;
        let params = self.comma_sep(&Token::RParen, Parser::param)?;
        self.expect(&Token::RParen)?;
        self.expect(&Token::Eq)?;
        let body = self.expr()?;
        Ok(PredDecl {
            span: start.merge(body.span),
            name,
            visibility: Visibility::Private,
            params,
            body,
        })
    }

    fn prop_decl(&mut self) -> Result<PropDecl, ParseError> {
        let start = self.expect(&Token::Prop)?;
        let (name, _) = self.expect_name()?;

        let systems = if self.eat(&Token::For).is_some() {
            let mut names = vec![];
            let (n, _) = self.expect_name()?;
            names.push(n);
            while self.eat(&Token::Comma).is_some() {
                let (n, _) = self.expect_name()?;
                names.push(n);
            }
            names
        } else {
            Vec::new()
        };

        self.expect(&Token::Eq)?;
        let body = self.expr()?;
        Ok(PropDecl {
            span: start.merge(body.span),
            name,
            visibility: Visibility::Private,
            systems,
            body,
        })
    }

    // ── Verify / Theorem / Lemma ──────────────────────────────────────

    /// Parse an `assume {... }` block on a verify/theorem/lemma construct.
    /// Items inside the block are separated by newlines or `;`. Each item is
    /// one of: `fair PATH`, `strong fair PATH`, `stutter`, `no stutter`.
    ///
    /// only stores the parsed items; normalizes them into an
    /// `AssumptionSet`. wires them into the verifier.
    fn assume_block(&mut self) -> Result<AssumeBlock, ParseError> {
        let start = self.expect(&Token::Assume)?;
        self.expect(&Token::LBrace)?;
        let items = self.assume_items_until_rbrace(start)?;
        let end = self.expect(&Token::RBrace)?;
        Ok(AssumeBlock {
            items,
            span: start.merge(end),
        })
    }

    /// Parse one or more `AssumeItem`s up to (but not consuming) the
    /// closing `}`. Stops on RBrace; emits `ASSUME_STUTTER_CONFLICT`
    /// on a single block that contains both `stutter` and `no stutter`.
    /// `surrounding_start` is the span of the enclosing keyword (`assume`
    /// or `under`) used for the diagnostic anchor.
    fn assume_items_until_rbrace(
        &mut self,
        surrounding_start: Span,
    ) -> Result<Vec<AssumeItem>, ParseError> {
        let mut items: Vec<AssumeItem> = Vec::new();
        let mut saw_stutter = false;
        let mut saw_no_stutter = false;
        while !matches!(self.peek(), Some(Token::RBrace)) {
            // Skip optional `;` separators between items.
            while self.eat(&Token::Semi).is_some() {}
            if matches!(self.peek(), Some(Token::RBrace)) {
                break;
            }
            // Stop on tokens that begin under-block body items
            // (theorem/lemma) so the caller can resume parsing them.
            if matches!(self.peek(), Some(Token::Theorem | Token::Lemma)) {
                break;
            }
            let item = match self.peek() {
                Some(Token::Strong) => {
                    let s = self.advance().1;
                    self.expect(&Token::Fair)?;
                    let path = self.event_path()?;
                    let span = s.merge(path.span);
                    AssumeItem::StrongFair { path, span }
                }
                Some(Token::Fair) => {
                    let s = self.advance().1;
                    let path = self.event_path()?;
                    let span = s.merge(path.span);
                    AssumeItem::Fair { path, span }
                }
                Some(Token::Stutter) => {
                    let s = self.advance().1;
                    saw_stutter = true;
                    AssumeItem::Stutter { span: s }
                }
                Some(Token::No) => {
                    let s = self.advance().1;
                    let end = self.expect(&Token::Stutter)?;
                    saw_no_stutter = true;
                    AssumeItem::NoStutter { span: s.merge(end) }
                }
                // `store name: Type[lo..hi]`
                Some(Token::Store) => AssumeItem::Store(self.store_decl()?),
                // `proc shop.fulfill[0..3]`
                Some(Token::Proc) => AssumeItem::Proc(self.proc_bound_decl()?),
                // `let name = SystemType { field: store }`
                Some(Token::Let) => AssumeItem::Let(self.let_binding_decl()?),
                Some(tok) => {
                    return Err(ParseError::expected(
                        "`store`, `proc`, `let`, `fair`, `strong fair`, `stutter`, `no stutter`, or `}`",
                        &format!("`{tok}`"),
                        self.cur_span(),
                    ));
                }
                None => return Err(ParseError::eof(self.cur_span())),
            };
            items.push(item);
            // Allow `;` after each item.
            while self.eat(&Token::Semi).is_some() {}
        }
        if saw_stutter && saw_no_stutter {
            return Err(ParseError::expected_with_help(
                crate::messages::ASSUME_STUTTER_CONFLICT,
                "both `stutter` and `no stutter`",
                surrounding_start.merge(self.cur_span()),
                crate::messages::HINT_ASSUME_STUTTER_CONFLICT,
            ));
        }
        Ok(items)
    }

    /// parse `store name: Type[lo..hi]`.
    fn store_decl(&mut self) -> Result<StoreDecl, ParseError> {
        let start = self.expect(&Token::Store)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::Colon)?;
        let (entity_type, _) = self.expect_name()?;
        self.expect(&Token::LBracket)?;
        let (lo, _) = self.expect_int()?;
        self.expect(&Token::DotDot)?;
        let (hi, _) = self.expect_int()?;
        let end = self.expect(&Token::RBracket)?;
        Ok(StoreDecl {
            name,
            entity_type,
            lo,
            hi,
            span: start.merge(end),
        })
    }

    /// parse `proc path[lo..hi]`.
    fn proc_bound_decl(&mut self) -> Result<crate::ast::ProcBoundDecl, ParseError> {
        let start = self.expect(&Token::Proc)?;
        let path = self.event_path()?;
        self.expect(&Token::LBracket)?;
        let (lo, _) = self.expect_int()?;
        self.expect(&Token::DotDot)?;
        let (hi, _) = self.expect_int()?;
        let end = self.expect(&Token::RBracket)?;
        Ok(crate::ast::ProcBoundDecl {
            path,
            lo,
            hi,
            span: start.merge(end),
        })
    }

    /// parse `let name = SystemType { field: store,... }`.
    fn let_binding_decl(&mut self) -> Result<LetBindingDecl, ParseError> {
        let start = self.expect(&Token::Let)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::Eq)?;
        let (system_type, _) = self.expect_name()?;
        self.expect(&Token::LBrace)?;
        let fields = self.comma_sep(&Token::RBrace, |p| {
            let (field_name, _) = p.expect_name()?;
            p.expect(&Token::Colon)?;
            let (store_name, _) = p.expect_name()?;
            Ok((field_name, store_name))
        })?;
        let end = self.expect(&Token::RBrace)?;
        Ok(LetBindingDecl {
            name,
            system_type,
            fields,
            span: start.merge(end),
        })
    }

    /// Parse an event path for use inside `assume { fair PATH }`. PATH is
    /// one or more identifiers separated by `::` (type-level) or `.`
    /// (instance-level). Both forms produce the same `EventPath`:
    ///
    /// - `fair Billing::charge` → segments `["Billing", "charge"]`
    /// - `fair billing.charge` → segments `["billing", "charge"]`
    ///
    /// The resolver differentiates by checking whether the first segment
    /// is a system type name or a let-binding instance name.
    fn event_path(&mut self) -> Result<EventPath, ParseError> {
        let (first, start) = self.expect_name()?;
        let mut segments = vec![first];
        let mut end = start;
        while self.eat(&Token::ColonColon).is_some() || self.eat(&Token::Dot).is_some() {
            let (seg, seg_span) = self.expect_name()?;
            segments.push(seg);
            end = seg_span;
        }
        Ok(EventPath {
            segments,
            span: start.merge(end),
        })
    }

    /// parse a single `by L` lemma reference.
    /// Mirrors `event_path` — accepts a multi-segment path of one or
    /// more `::`-separated identifiers (`name`, `Mod::name`, etc.).
    /// The resolve pass routes the segments through `env.decls` for
    /// module-aware lookup.
    fn by_lemma_ref(&mut self) -> Result<ByLemmaRef, ParseError> {
        let (first, start) = self.expect_name()?;
        let mut segments = vec![first];
        let mut end = start;
        while self.eat(&Token::ColonColon).is_some() {
            let (seg, seg_span) = self.expect_name()?;
            segments.push(seg);
            end = seg_span;
        }
        Ok(ByLemmaRef {
            segments,
            span: start.merge(end),
        })
    }

    /// verify blocks no longer use `for System[0..N]`.
    /// Stores and let bindings live inside the assume block.
    fn verify_decl(&mut self) -> Result<VerifyDecl, ParseError> {
        let start = self.expect(&Token::Verify)?;
        let (name, _) = self.expect_name()?;

        // Optional depth: `verify name [depth: N] {... }`
        let depth = if self.eat(&Token::LBracket).is_some() {
            let (key, _) = self.expect_name()?;
            if key != "depth" {
                return Err(ParseError::expected(
                    "`depth`",
                    &format!("`{key}`"),
                    self.cur_span(),
                ));
            }
            self.expect(&Token::Colon)?;
            let val = match self.peek() {
                Some(Token::IntLit(_)) => {
                    let (Token::IntLit(n), _) = self.advance() else {
                        unreachable!()
                    };
                    n
                }
                Some(tok) => {
                    return Err(ParseError::expected(
                        "integer",
                        &format!("`{tok}`"),
                        self.cur_span(),
                    ));
                }
                None => return Err(ParseError::eof(self.cur_span())),
            };
            self.expect(&Token::RBracket)?;
            Some(val)
        } else {
            None
        };

        // Reject legacy `for System[0..N]` with a migration diagnostic.
        if matches!(self.peek(), Some(Token::For)) {
            return Err(ParseError::expected_with_help(
                "`{`",
                "`for`",
                self.cur_span(),
                crate::messages::FOR_SYSTEM_REMOVED,
            ));
        }

        self.expect(&Token::LBrace)?;
        // Optional `assume {... }` block immediately after the body brace.
        let assume_block = if matches!(self.peek(), Some(Token::Assume)) {
            Some(self.assume_block()?)
        } else {
            None
        };
        let mut asserts = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) {
            match self.peek() {
                Some(Token::Assert) => {
                    self.advance();
                    asserts.push(self.expr()?);
                }
                Some(tok) => {
                    return Err(ParseError::expected_with_help(
                        "`assert` or `}`",
                        &format!("`{tok}`"),
                        self.cur_span(),
                        crate::messages::HINT_VERIFY_BODY,
                    ));
                }
                None => return Err(ParseError::eof(self.cur_span())),
            }
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(VerifyDecl {
            name,
            depth,
            assume_block,
            asserts,
            span: start.merge(end),
        })
    }

    fn theorem_decl(&mut self) -> Result<TheoremDecl, ParseError> {
        let start = self.expect(&Token::Theorem)?;
        let (name, _) = self.expect_name()?;

        // Check for expression form: theorem name = expr [by "file"]
        if self.eat(&Token::Eq).is_some() {
            let body_expr = self.expr()?;
            let by_file = if self.eat(&Token::By).is_some() {
                let (file, _) = self.expect_string()?;
                Some(file)
            } else {
                None
            };
            let end = body_expr.span;
            return Ok(TheoremDecl {
                name,
                systems: vec![],
                assume_block: None,
                invariants: vec![],
                shows: vec![body_expr],
                by_file,
                by_lemmas: vec![],
                span: start.merge(end),
            });
        }

        // Block form: theorem name for System, System2 [invariant...] { show... }
        self.expect(&Token::For)?;

        let mut systems = vec![];
        let (n, _) = self.expect_name()?;
        systems.push(n);
        while self.eat(&Token::Comma).is_some() {
            let (n, _) = self.expect_name()?;
            systems.push(n);
        }

        let mut invariants = Vec::new();
        while matches!(self.peek(), Some(Token::Invariant)) {
            self.advance();
            invariants.push(self.expr()?);
        }

        self.expect(&Token::LBrace)?;
        // Optional `assume {... }` block immediately after the body brace.
        let assume_block = if matches!(self.peek(), Some(Token::Assume)) {
            Some(self.assume_block()?)
        } else {
            None
        };
        let mut shows = Vec::new();
        let mut by_lemmas: Vec<ByLemmaRef> = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) {
            match self.peek() {
                Some(Token::Show) => {
                    self.advance();
                    shows.push(self.expr()?);
                }
                Some(Token::By) => {
                    // `by L1, Mod::L2,...` lemma
                    // references. Each entry is a multi-segment path
                    // (qualified or bare). `by "file"` (external proof)
                    // is restricted to the expression form
                    // `theorem name = expr by "file"`.
                    self.advance();
                    by_lemmas.push(self.by_lemma_ref()?);
                    while self.eat(&Token::Comma).is_some() {
                        by_lemmas.push(self.by_lemma_ref()?);
                    }
                }
                Some(Token::Assert) => {
                    return Err(ParseError::expected_with_help(
                        "`show` or `}`",
                        "`assert`",
                        self.cur_span(),
                        crate::messages::HINT_THEOREM_BODY,
                    ));
                }
                Some(tok) => {
                    return Err(ParseError::expected_with_help(
                        "`show` or `}`",
                        &format!("`{tok}`"),
                        self.cur_span(),
                        crate::messages::HINT_THEOREM_BODY_SHOW,
                    ));
                }
                None => return Err(ParseError::eof(self.cur_span())),
            }
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(TheoremDecl {
            name,
            systems,
            assume_block,
            invariants,
            shows,
            by_file: None,
            by_lemmas,
            span: start.merge(end),
        })
    }

    fn axiom_decl(&mut self) -> Result<AxiomDecl, ParseError> {
        let start = self.expect(&Token::Axiom)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::Eq)?;
        let body = self.expr()?;
        let by_file = if self.eat(&Token::By).is_some() {
            let (file, _) = self.expect_string()?;
            Some(file)
        } else {
            None
        };
        let end = body.span;
        Ok(AxiomDecl {
            name,
            body,
            by_file,
            span: start.merge(end),
        })
    }

    fn lemma_decl(&mut self) -> Result<LemmaDecl, ParseError> {
        let start = self.expect(&Token::Lemma)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::LBrace)?;
        // Optional `assume {... }` block immediately after the body brace.
        let assume_block = if matches!(self.peek(), Some(Token::Assume)) {
            Some(self.assume_block()?)
        } else {
            None
        };
        let mut body = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) {
            body.push(self.expr()?);
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(LemmaDecl {
            name,
            assume_block,
            body,
            span: start.merge(end),
        })
    }

    // ── Under Blocks ( / ) ─────────────────────────────

    /// / + (Variant A): parse an `under {... }`
    /// block. Body items: zero or more assumption items (`fair`,
    /// `strong fair`, `stutter`, `no stutter`) followed by zero or
    /// more theorem/lemma declarations. Order between assumption items
    /// and theorems/lemmas is parser-tolerant — the linter recommends
    /// assumption items first.
    ///
    /// Rejects `verify` blocks inside the under block () with
    /// `UNDER_VERIFY_NOT_ALLOWED`.
    fn under_block(&mut self) -> Result<UnderBlock, ParseError> {
        let start = self.expect(&Token::Under)?;
        self.expect(&Token::LBrace)?;
        let mut items: Vec<AssumeItem> = Vec::new();
        let mut theorems: Vec<TheoremDecl> = Vec::new();
        let mut lemmas: Vec<LemmaDecl> = Vec::new();
        loop {
            // Skip optional `;` separators between any items.
            while self.eat(&Token::Semi).is_some() {}
            match self.peek() {
                Some(Token::RBrace) => break,
                None => return Err(ParseError::eof(self.cur_span())),
                Some(Token::Theorem) => {
                    theorems.push(self.theorem_decl()?);
                }
                Some(Token::Lemma) => {
                    lemmas.push(self.lemma_decl()?);
                }
                Some(Token::Verify) => {
                    return Err(ParseError::expected_with_help(
                        crate::messages::UNDER_VERIFY_NOT_ALLOWED,
                        "`verify`",
                        self.cur_span(),
                        crate::messages::HINT_UNDER_VERIFY_NOT_ALLOWED,
                    ));
                }
                Some(Token::Fair | Token::Strong | Token::Stutter | Token::No) => {
                    let new_items = self.assume_items_until_rbrace(start)?;
                    items.extend(new_items);
                }
                Some(tok) => {
                    return Err(ParseError::expected(
                        "assumption item, `theorem`, `lemma`, or `}`",
                        &format!("`{tok}`"),
                        self.cur_span(),
                    ));
                }
            }
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(UnderBlock {
            items,
            theorems,
            lemmas,
            span: start.merge(end),
        })
    }

    // ── Scene Declarations ───────────────────────────────────────────

    /// scene blocks no longer use `for System`.
    /// Stores and let bindings live inside given blocks.
    fn scene_decl(&mut self) -> Result<SceneDecl, ParseError> {
        let start = self.expect(&Token::Scene)?;
        let (name, _) = self.expect_name()?;

        // Reject legacy `for System` with migration diagnostic.
        if matches!(self.peek(), Some(Token::For)) {
            return Err(ParseError::expected_with_help(
                "`{`",
                "`for`",
                self.cur_span(),
                crate::messages::FOR_SYSTEM_REMOVED,
            ));
        }

        self.expect(&Token::LBrace)?;
        let mut items = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) && !self.at_end() {
            match self.scene_item() {
                Ok(item) => items.push(item),
                Err(err) if self.recovering => {
                    self.push_recovery_error(err);
                    items.push(SceneItem::Error(
                        self.recover_to_brace_item(is_scene_item_starter),
                    ));
                }
                Err(err) => return Err(err),
            }
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(SceneDecl {
            name,
            items,
            span: start.merge(end),
        })
    }

    /// scene items support given/when/then blocks
    /// with the new store/let/activate/instance-qualified syntax.
    fn scene_item(&mut self) -> Result<SceneItem, ParseError> {
        match self.peek() {
            Some(Token::Given) => {
                let start = self.advance().1;
                if matches!(self.peek(), Some(Token::LBrace)) {
                    self.advance();
                    let mut items = Vec::new();
                    while !matches!(self.peek(), Some(Token::RBrace)) && !self.at_end() {
                        match self.given_item() {
                            Ok(item) => items.push(item),
                            Err(err) if self.recovering => {
                                self.push_recovery_error(err);
                                items.push(GivenItem::Error(
                                    self.recover_to_brace_item(is_given_item_starter),
                                ));
                            }
                            Err(err) => return Err(err),
                        }
                    }
                    let end = self.expect(&Token::RBrace)?;
                    Ok(SceneItem::GivenBlock {
                        items,
                        span: start.merge(end),
                    })
                } else {
                    // Inline given: given store/let/let x = one Entity
                    let item = self.given_item()?;
                    let end_span = match &item {
                        GivenItem::EntityBinding { span, .. }
                        | GivenItem::Store(StoreDecl { span, .. })
                        | GivenItem::Let(LetBindingDecl { span, .. })
                        | GivenItem::Activate(ActivateDecl { span, .. })
                        | GivenItem::Constraint { span, .. }
                        | GivenItem::Error(crate::ast::ErrorNode { span, .. }) => *span,
                    };
                    Ok(SceneItem::GivenBlock {
                        items: vec![item],
                        span: start.merge(end_span),
                    })
                }
            }
            Some(Token::When) => {
                let start = self.advance().1;
                if matches!(self.peek(), Some(Token::LBrace)) {
                    self.advance();
                    let mut items = Vec::new();
                    while !matches!(self.peek(), Some(Token::RBrace)) && !self.at_end() {
                        match self.when_item() {
                            Ok(item) => items.push(item),
                            Err(err) if self.recovering => {
                                self.push_recovery_error(err);
                                items.push(WhenItem::Error(
                                    self.recover_to_brace_item(is_when_item_starter),
                                ));
                            }
                            Err(err) => return Err(err),
                        }
                    }
                    let end = self.expect(&Token::RBrace)?;
                    Ok(SceneItem::WhenBlock {
                        items,
                        span: start.merge(end),
                    })
                } else {
                    // when assume expr
                    self.expect(&Token::Assume)?;
                    let expr = self.expr()?;
                    Ok(SceneItem::WhenAssume {
                        span: start.merge(expr.span),
                        expr,
                    })
                }
            }
            Some(Token::Then) => {
                let start = self.advance().1;
                if matches!(self.peek(), Some(Token::LBrace)) {
                    self.advance();
                    let mut items = Vec::new();
                    while !matches!(self.peek(), Some(Token::RBrace)) && !self.at_end() {
                        match self.then_item() {
                            Ok(item) => items.push(item),
                            Err(err) if self.recovering => {
                                self.push_recovery_error(err);
                                let node = self.recover_to_block_item();
                                items.push(ThenItem {
                                    span: node.span,
                                    expr: Expr {
                                        span: node.span,
                                        kind: ExprKind::Error(node),
                                    },
                                });
                            }
                            Err(err) => return Err(err),
                        }
                    }
                    let end = self.expect(&Token::RBrace)?;
                    Ok(SceneItem::ThenBlock {
                        items,
                        span: start.merge(end),
                    })
                } else {
                    self.expect(&Token::Assert)?;
                    let expr = self.expr()?;
                    Ok(SceneItem::ThenAssert {
                        span: start.merge(expr.span),
                        expr,
                    })
                }
            }
            Some(tok) => Err(ParseError::expected_with_help(
                "`given`, `when`, or `then`",
                &format!("`{tok}`"),
                self.cur_span(),
                crate::messages::HINT_SCENE_BODY_STRUCTURE,
            )),
            None => Err(ParseError::eof(self.cur_span())),
        }
    }

    /// parse a single given item. Supports:
    /// - `store name: Type[lo..hi]`
    /// - `let name = SystemType { field: store }` (system instantiation)
    /// - `let name = one Entity [in store] [where cond]` (entity binding)
    /// - `activate {instances} in store`
    /// - expression (constraint)
    fn given_item(&mut self) -> Result<GivenItem, ParseError> {
        match self.peek() {
            Some(Token::Store) => Ok(GivenItem::Store(self.store_decl()?)),
            Some(Token::Activate) => Ok(GivenItem::Activate(self.activate_decl()?)),
            Some(Token::Let) => {
                let start = self.cur_span();
                self.advance();
                let (name, _) = self.expect_name()?;
                self.expect(&Token::Eq)?;

                // Check if this is `one Entity` (entity binding) or
                // `SystemType {... }` (system instantiation).
                if matches!(self.peek(), Some(Token::One)) {
                    self.advance();
                    let (entity_type, _) = self.expect_name()?;
                    // Optional `in store_name`
                    let store_name = if self.eat(&Token::In).is_some() {
                        let (sn, _) = self.expect_name()?;
                        Some(sn)
                    } else {
                        None
                    };
                    let condition = if self.eat(&Token::Where).is_some() {
                        Some(self.expr()?)
                    } else {
                        None
                    };
                    let end_span = condition
                        .as_ref()
                        .map_or_else(|| self.cur_span(), |e| e.span);
                    Ok(GivenItem::EntityBinding {
                        name,
                        entity_type,
                        store_name,
                        condition,
                        span: start.merge(end_span),
                    })
                } else {
                    // System instantiation: `let name = SystemType { field: store }`
                    let (system_type, _) = self.expect_name()?;
                    self.expect(&Token::LBrace)?;
                    let fields = self.comma_sep(&Token::RBrace, |p| {
                        let (field_name, _) = p.expect_name()?;
                        p.expect(&Token::Colon)?;
                        let (store_name, _) = p.expect_name()?;
                        Ok((field_name, store_name))
                    })?;
                    let end = self.expect(&Token::RBrace)?;
                    Ok(GivenItem::Let(LetBindingDecl {
                        name,
                        system_type,
                        fields,
                        span: start.merge(end),
                    }))
                }
            }
            _ => {
                // Constraint expression
                let expr = self.expr()?;
                let span = expr.span;
                Ok(GivenItem::Constraint { expr, span })
            }
        }
    }

    /// parse `activate {instances} in store`.
    /// Accepts both `Token::Activate` (keyword) and `Token::Name("activate")`.
    fn activate_decl(&mut self) -> Result<ActivateDecl, ParseError> {
        let start = match self.peek() {
            Some(Token::Activate) => self.advance().1,
            Some(Token::Name(n)) if n == "activate" => self.advance().1,
            _ => {
                return Err(ParseError::expected(
                    "`activate`",
                    &format!(
                        "`{}`",
                        self.peek()
                            .map_or_else(|| "EOF".to_owned(), ToString::to_string)
                    ),
                    self.cur_span(),
                ))
            }
        };
        self.expect(&Token::LBrace)?;
        let instances = self.comma_sep(&Token::RBrace, |p| {
            let (name, _) = p.expect_name()?;
            Ok(name)
        })?;
        self.expect(&Token::RBrace)?;
        self.expect(&Token::In)?;
        let (store_name, end) = self.expect_name()?;
        Ok(ActivateDecl {
            instances,
            store_name,
            span: start.merge(end),
        })
    }

    fn parse_when_call_parts(&mut self) -> Result<WhenCallParts, ParseError> {
        let (instance, start) = self.expect_name()?;
        self.expect(&Token::Dot)?;
        let (command, _) = self.expect_name()?;
        self.expect(&Token::LParen)?;
        let args = self.comma_sep(&Token::RParen, Parser::invoc_arg)?;
        let mut end = self.expect(&Token::RParen)?;
        let card = if self.eat(&Token::LBrace).is_some() {
            let parsed = match self.peek() {
                Some(Token::One) => {
                    self.advance();
                    "one".to_owned()
                }
                Some(Token::Lone) => {
                    self.advance();
                    "lone".to_owned()
                }
                Some(Token::Some) => {
                    self.advance();
                    "some".to_owned()
                }
                Some(Token::No) => {
                    self.advance();
                    "no".to_owned()
                }
                Some(Token::IntLit(_)) => {
                    let (value, _) = self.expect_int()?;
                    value.to_string()
                }
                Some(tok) => {
                    return Err(ParseError::expected(
                        "scene action cardinality (`one`, `lone`, `some`, `no`, or integer)",
                        &format!("`{tok}`"),
                        self.cur_span(),
                    ));
                }
                None => return Err(ParseError::eof(self.cur_span())),
            };
            end = self.expect(&Token::RBrace)?;
            Some(parsed)
        } else {
            None
        };
        Ok((instance, command, args, card, start.merge(end)))
    }

    /// when items use instance-qualified calls.
    /// `instance.command(args)`, `let x = instance.command(args)`, or `assume expr`.
    fn when_item(&mut self) -> Result<WhenItem, ParseError> {
        match self.peek() {
            Some(Token::Assume) => {
                let start = self.advance().1;
                let expr = self.expr()?;
                Ok(WhenItem::Assume {
                    span: start.merge(expr.span),
                    expr,
                })
            }
            Some(Token::Let) => {
                let start = self.advance().1;
                let (name, _) = self.expect_name()?;
                self.expect(&Token::Eq)?;
                let (instance, command, args, card, span) = self.parse_when_call_parts()?;
                Ok(WhenItem::LetCall {
                    name,
                    instance,
                    command,
                    args,
                    card,
                    span: start.merge(span),
                })
            }
            Some(Token::Name(_)) => {
                let (instance, command, args, card, span) = self.parse_when_call_parts()?;
                Ok(WhenItem::InstanceCall {
                    instance,
                    command,
                    args,
                    card,
                    span,
                })
            }
            Some(tok) => Err(ParseError::expected(
                "instance-qualified call, `let` binding, or `assume`",
                &format!("`{tok}`"),
                self.cur_span(),
            )),
            None => Err(ParseError::eof(self.cur_span())),
        }
    }

    fn invoc_arg(&mut self) -> Result<InvocArg, ParseError> {
        match self.peek() {
            Some(Token::At) => {
                let start = self.advance().1;
                let (name, end) = self.expect_name()?;
                Ok(InvocArg::State {
                    name,
                    span: start.merge(end),
                })
            }
            Some(Token::IntLit(_)) => {
                let (value, span) = self.expect_int()?;
                Ok(InvocArg::Int { value, span })
            }
            Some(Token::DoubleLit(_)) => {
                let (tok, span) = self.advance();
                if let Token::DoubleLit(v) = tok {
                    Ok(InvocArg::Real { value: v, span })
                } else {
                    unreachable!()
                }
            }
            Some(Token::FloatLit(_)) => {
                let (tok, span) = self.advance();
                if let Token::FloatLit(v) = tok {
                    Ok(InvocArg::Float { value: v, span })
                } else {
                    unreachable!()
                }
            }
            Some(Token::StringLit(_)) => {
                let (value, span) = self.expect_string()?;
                Ok(InvocArg::Str { value, span })
            }
            Some(Token::Name(_)) => {
                let (first, start) = self.expect_name()?;
                if self.eat(&Token::Dot).is_some() {
                    let (field, end) = self.expect_name()?;
                    Ok(InvocArg::Field {
                        obj: first,
                        field,
                        span: start.merge(end),
                    })
                } else {
                    Ok(InvocArg::Simple {
                        name: first,
                        span: start,
                    })
                }
            }
            Some(tok) => Err(ParseError::expected(
                "invocation argument",
                &format!("`{tok}`"),
                self.cur_span(),
            )),
            None => Err(ParseError::eof(self.cur_span())),
        }
    }

    fn then_item(&mut self) -> Result<ThenItem, ParseError> {
        let start = self.expect(&Token::Assert)?;
        let expr = self.expr()?;
        Ok(ThenItem {
            span: start.merge(expr.span),
            expr,
        })
    }

    // ── Generic helpers ──────────────────────────────────────────────

    pub(super) fn prev_span(&self) -> Span {
        if self.pos > 0 {
            self.tokens[self.pos - 1].1
        } else {
            Span { start: 0, end: 0 }
        }
    }

    pub(super) fn comma_sep<T>(
        &mut self,
        end: &Token,
        mut f: impl FnMut(&mut Self) -> Result<T, ParseError>,
    ) -> Result<Vec<T>, ParseError> {
        let mut items = Vec::new();
        if self.peek() == Some(end) {
            return Ok(items);
        }
        items.push(f(self)?);
        while self.eat(&Token::Comma).is_some() {
            items.push(f(self)?);
        }
        Ok(items)
    }
}

#[cfg(test)]
mod tests;
