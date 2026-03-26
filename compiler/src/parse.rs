use crate::ast::{
    ActionInvoc, CardValue, ChooseBlock, ConstDecl, Contract, CreateBlock, CreateField,
    EntityAction, EntityDecl, EntityItem, EventDecl, EventItem, Expr, ExprKind, FieldDecl,
    FieldPat, FnDecl, ForBlock, GivenItem, ImportDecl, InvocArg, LemmaDecl, LetBind, MatchArm,
    NextBlock, NextItem, Param, Pattern, PredDecl, Program, ProofDecl, PropDecl, QualType,
    RecField, RecordDecl, SceneDecl, SceneItem, SystemDecl, SystemItem, ThenItem, TopDecl,
    TypeDecl, TypeRef, TypeRefKind, TypeVariant, TypedParam, UseDecl, UseItem, VerifyDecl,
    VerifyTarget, WhenItem,
};
use crate::diagnostic::ParseError;
use crate::lex::Token;
use crate::span::Span;

// ── Binding powers (Pratt parser) ────────────────────────────────────
// Level 0 (|,||,^|,|>): l=1  r=2   (left-assoc)
// Level 1 (->):          l=3  r=3   (right-assoc)
// Level 2 (&):           l=5  r=6   (left-assoc)
// Level 3 (implies):     l=7  r=7   (right-assoc)
// Level 4 (=):           l=9  r=9   (right-assoc)
// Level 5 (or):          l=11 r=12  (left-assoc)
// Level 6 (and):         l=13 r=14  (left-assoc)
// Level 7 (not):         prefix r=15
// Level 8 (==,!=,in):    l=17 r=18  (left-assoc)
// Level 9 (<,>,<=,>=):   l=19 r=20  (left-assoc)
// Level 10 (+,-):        l=21 r=22  (left-assoc)
// Level 11 (*,/,%):      l=23 r=24  (left-assoc)
// Level 12 (neg,#):      prefix r=25
// Level 13 (',.,(),[]()): postfix l=27
// Level 14 (atoms):      parsed directly

fn infix_bp(op: &Token) -> Option<(u8, u8)> {
    match op {
        Token::Pipe | Token::PipePipe | Token::CaretPipe | Token::PipeGt => Some((1, 2)),
        Token::Arrow => Some((3, 3)),
        Token::Amp => Some((5, 6)),
        Token::Implies => Some((7, 7)),
        Token::Eq => Some((9, 9)),
        Token::Or => Some((11, 12)),
        Token::And => Some((13, 14)),
        Token::EqEq | Token::BangEq | Token::In => Some((17, 18)),
        Token::Lt | Token::Gt | Token::LtEq | Token::GtEq => Some((19, 20)),
        Token::Plus | Token::Minus => Some((21, 22)),
        Token::Star | Token::Slash | Token::Percent => Some((23, 24)),
        _ => None,
    }
}

fn postfix_bp(op: &Token) -> Option<u8> {
    match op {
        Token::Prime | Token::Dot | Token::LParen | Token::LBracket => Some(27),
        _ => None,
    }
}

// ── Parser state ─────────────────────────────────────────────────────

pub struct Parser {
    tokens: Vec<(Token, Span)>,
    pos: usize,
    /// When true, `Token::In` is not treated as an infix operator.
    /// Used inside `let` binding values to avoid consuming the `let...in` separator.
    no_in: bool,
}

impl Parser {
    pub fn new(tokens: Vec<(Token, Span)>) -> Self {
        Self {
            tokens,
            pos: 0,
            no_in: false,
        }
    }

    // ── Helpers ──────────────────────────────────────────────────────

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos).map(|(t, _)| t)
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

    pub fn parse_program(&mut self) -> Result<Program, ParseError> {
        let start = self.cur_span();
        let mut decls = Vec::new();
        while !self.at_end() {
            decls.push(self.top_decl()?);
        }
        let span = if decls.is_empty() {
            start
        } else {
            start.merge(self.cur_span())
        };
        Ok(Program { decls, span })
    }

    fn top_decl(&mut self) -> Result<TopDecl, ParseError> {
        match self.peek() {
            Some(Token::Import) => Ok(TopDecl::Import(self.import_decl()?)),
            Some(Token::Use) => Ok(TopDecl::Use(self.use_decl()?)),
            Some(Token::Const) => Ok(TopDecl::Const(self.const_decl()?)),
            Some(Token::Fn) => Ok(TopDecl::Fn(self.fn_decl()?)),
            Some(Token::Type) => self.type_or_record_decl(),
            Some(Token::Entity) => Ok(TopDecl::Entity(self.entity_decl()?)),
            Some(Token::System) => Ok(TopDecl::System(self.system_decl()?)),
            Some(Token::Pred) => Ok(TopDecl::Pred(self.pred_decl()?)),
            Some(Token::Prop) => Ok(TopDecl::Prop(self.prop_decl()?)),
            Some(Token::Verify) => Ok(TopDecl::Verify(self.verify_decl()?)),
            Some(Token::Proof) => Ok(TopDecl::Proof(self.proof_decl()?)),
            Some(Token::Lemma) => Ok(TopDecl::Lemma(self.lemma_decl()?)),
            Some(Token::Scene) => Ok(TopDecl::Scene(self.scene_decl()?)),
            Some(tok) => Err(ParseError::expected(
                "top-level declaration",
                &format!("`{tok}`"),
                self.cur_span(),
            )),
            None => Err(ParseError::eof(self.cur_span())),
        }
    }

    // ── Import / Use ─────────────────────────────────────────────────

    fn import_decl(&mut self) -> Result<ImportDecl, ParseError> {
        let start = self.expect(&Token::Import)?;
        let (path, _) = self.expect_string()?;
        self.expect(&Token::As)?;
        let (alias, end) = self.expect_name()?;
        Ok(ImportDecl {
            path,
            alias,
            span: start.merge(end),
        })
    }

    fn use_decl(&mut self) -> Result<UseDecl, ParseError> {
        let start = self.expect(&Token::Use)?;
        let (module, _) = self.expect_name()?;
        self.expect(&Token::ColonColon)?;

        if self.eat(&Token::Star).is_some() {
            return Ok(UseDecl::All {
                module,
                span: start.merge(self.cur_span()),
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
        let ret_type = self.type_ref()?;
        self.expect(&Token::Eq)?;
        let body = self.expr()?;
        Ok(FnDecl {
            span: start.merge(body.span),
            name,
            params,
            ret_type,
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

    // ── Type Declarations ────────────────────────────────────────────

    fn type_or_record_decl(&mut self) -> Result<TopDecl, ParseError> {
        let start = self.expect(&Token::Type)?;
        let (name, _) = self.expect_name()?;

        if self.eat(&Token::LBrace).is_some() {
            // Record: type Name { fields }
            let fields = self.comma_sep(&Token::RBrace, Parser::rec_field)?;
            let end = self.expect(&Token::RBrace)?;
            Ok(TopDecl::Record(RecordDecl {
                name,
                fields,
                span: start.merge(end),
            }))
        } else {
            // Sum type: type Name = Variant | Variant
            self.expect(&Token::Eq)?;
            let mut variants = vec![self.type_variant()?];
            while self.eat(&Token::Pipe).is_some() {
                variants.push(self.type_variant()?);
            }
            let last_span = match variants.last() {
                Some(
                    TypeVariant::Simple { span, .. }
                    | TypeVariant::Record { span, .. }
                    | TypeVariant::Param { span, .. },
                ) => *span,
                None => start,
            };
            Ok(TopDecl::Type(TypeDecl {
                name,
                variants,
                span: start.merge(last_span),
            }))
        }
    }

    fn type_variant(&mut self) -> Result<TypeVariant, ParseError> {
        let (name, start) = self.expect_name()?;
        if self.eat(&Token::LBrace).is_some() {
            let fields = self.comma_sep(&Token::RBrace, Parser::rec_field)?;
            let end = self.expect(&Token::RBrace)?;
            Ok(TypeVariant::Record {
                name,
                fields,
                span: start.merge(end),
            })
        } else if self.eat(&Token::LBracket).is_some() {
            let types = self.comma_sep(&Token::RBracket, Parser::type_ref)?;
            let end = self.expect(&Token::RBracket)?;
            Ok(TypeVariant::Param {
                name,
                types,
                span: start.merge(end),
            })
        } else {
            Ok(TypeVariant::Simple { name, span: start })
        }
    }

    fn rec_field(&mut self) -> Result<RecField, ParseError> {
        let (name, start) = self.expect_name()?;
        self.expect(&Token::Colon)?;
        let ty = self.type_ref()?;
        Ok(RecField {
            span: start.merge(ty.span),
            name,
            ty,
        })
    }

    // ── Type References ──────────────────────────────────────────────

    fn type_ref(&mut self) -> Result<TypeRef, ParseError> {
        let lhs = self.type_ref_atom()?;
        if self.eat(&Token::Arrow).is_some() {
            let rhs = self.type_ref()?; // right-assoc
            let span = lhs.span.merge(rhs.span);
            Ok(TypeRef {
                kind: TypeRefKind::Fn(Box::new(lhs), Box::new(rhs)),
                span,
            })
        } else {
            Ok(lhs)
        }
    }

    fn type_ref_atom(&mut self) -> Result<TypeRef, ParseError> {
        if self.eat(&Token::LParen).is_some() {
            let start = self.cur_span();
            let first = self.type_ref()?;
            if self.eat(&Token::Comma).is_some() {
                // Tuple type
                let mut types = vec![first];
                types.push(self.type_ref()?);
                while self.eat(&Token::Comma).is_some() {
                    types.push(self.type_ref()?);
                }
                let end = self.expect(&Token::RParen)?;
                Ok(TypeRef {
                    kind: TypeRefKind::Tuple(types),
                    span: start.merge(end),
                })
            } else {
                // Parenthesized
                let end = self.expect(&Token::RParen)?;
                Ok(TypeRef {
                    kind: TypeRefKind::Paren(Box::new(first)),
                    span: start.merge(end),
                })
            }
        } else {
            let (name, start) = self.expect_name()?;
            if self.eat(&Token::LBracket).is_some() {
                let types = self.comma_sep(&Token::RBracket, Parser::type_ref)?;
                let end = self.expect(&Token::RBracket)?;
                Ok(TypeRef {
                    kind: TypeRefKind::Param(name, types),
                    span: start.merge(end),
                })
            } else {
                Ok(TypeRef {
                    kind: TypeRefKind::Simple(name),
                    span: start,
                })
            }
        }
    }

    // ── Entity Declarations ──────────────────────────────────────────

    fn entity_decl(&mut self) -> Result<EntityDecl, ParseError> {
        let start = self.expect(&Token::Entity)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::LBrace)?;
        let mut items = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) {
            items.push(self.entity_item()?);
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(EntityDecl {
            name,
            items,
            span: start.merge(end),
        })
    }

    fn entity_item(&mut self) -> Result<EntityItem, ParseError> {
        match self.peek() {
            Some(Token::Field) => Ok(EntityItem::Field(self.field_decl()?)),
            Some(Token::Action) => Ok(EntityItem::Action(self.entity_action()?)),
            Some(tok) => Err(ParseError::expected(
                "`field` or `action`",
                &format!("`{tok}`"),
                self.cur_span(),
            )),
            None => Err(ParseError::eof(self.cur_span())),
        }
    }

    fn field_decl(&mut self) -> Result<FieldDecl, ParseError> {
        let start = self.expect(&Token::Field)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::Colon)?;
        let ty = self.type_ref()?;
        let default = if self.eat(&Token::Eq).is_some() {
            Some(self.expr_bp(28)?) // atom-level only (Expr14)
        } else {
            None
        };
        let end_span = default.as_ref().map_or(ty.span, |e| e.span);
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
        let (name, start) = self.expect_name()?;
        self.expect(&Token::Colon)?;
        let (ty, end) = self.expect_name()?;
        Ok(Param {
            name,
            ty,
            span: start.merge(end),
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
                _ => break,
            }
        }
        Ok(contracts)
    }

    // ── System Declarations ──────────────────────────────────────────

    fn system_decl(&mut self) -> Result<SystemDecl, ParseError> {
        let start = self.expect(&Token::System)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::LBrace)?;
        let mut items = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) {
            items.push(self.system_item()?);
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(SystemDecl {
            name,
            items,
            span: start.merge(end),
        })
    }

    fn system_item(&mut self) -> Result<SystemItem, ParseError> {
        match self.peek() {
            Some(Token::Uses) => {
                let start = self.advance().1;
                let (name, end) = self.expect_name()?;
                Ok(SystemItem::Uses(name, start.merge(end)))
            }
            Some(Token::Event) => Ok(SystemItem::Event(self.event_decl()?)),
            Some(Token::Next) => Ok(SystemItem::Next(self.next_block()?)),
            Some(tok) => Err(ParseError::expected(
                "`uses`, `event`, or `next`",
                &format!("`{tok}`"),
                self.cur_span(),
            )),
            None => Err(ParseError::eof(self.cur_span())),
        }
    }

    fn event_decl(&mut self) -> Result<EventDecl, ParseError> {
        let start = self.expect(&Token::Event)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::LParen)?;
        let params = self.comma_sep(&Token::RParen, Parser::param)?;
        self.expect(&Token::RParen)?;
        let contracts = self.contracts()?;
        self.expect(&Token::LBrace)?;
        let mut items = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) {
            items.push(self.event_item()?);
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(EventDecl {
            name,
            params,
            contracts,
            items,
            span: start.merge(end),
        })
    }

    fn event_item(&mut self) -> Result<EventItem, ParseError> {
        match self.peek() {
            Some(Token::Choose) => Ok(EventItem::Choose(self.choose_block()?)),
            Some(Token::For) => Ok(EventItem::For(self.for_block()?)),
            Some(Token::Create) => Ok(EventItem::Create(self.create_block()?)),
            _ => Ok(EventItem::Expr(self.expr()?)),
        }
    }

    fn choose_block(&mut self) -> Result<ChooseBlock, ParseError> {
        let start = self.expect(&Token::Choose)?;
        let (var, _) = self.expect_name()?;
        self.expect(&Token::Colon)?;
        let (ty, _) = self.expect_name()?;
        self.expect(&Token::Where)?;
        let condition = self.expr()?;
        self.expect(&Token::LBrace)?;
        let mut body = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) {
            body.push(self.expr()?);
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(ChooseBlock {
            var,
            ty,
            condition,
            body,
            span: start.merge(end),
        })
    }

    fn for_block(&mut self) -> Result<ForBlock, ParseError> {
        let start = self.expect(&Token::For)?;
        let (var, _) = self.expect_name()?;
        self.expect(&Token::Colon)?;
        let (ty, _) = self.expect_name()?;
        self.expect(&Token::LBrace)?;
        let mut body = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) {
            body.push(self.expr()?);
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(ForBlock {
            var,
            ty,
            body,
            span: start.merge(end),
        })
    }

    fn create_block(&mut self) -> Result<CreateBlock, ParseError> {
        let start = self.expect(&Token::Create)?;
        let (ty, _) = self.expect_name()?;
        self.expect(&Token::LBrace)?;
        let mut fields = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) {
            fields.push(self.create_field()?);
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(CreateBlock {
            ty,
            fields,
            span: start.merge(end),
        })
    }

    fn create_field(&mut self) -> Result<CreateField, ParseError> {
        let (name, start) = self.expect_name()?;
        self.expect(&Token::Eq)?;
        let value = self.expr_bp(28)?; // atom-level (Expr14)
        Ok(CreateField {
            name,
            span: start.merge(value.span),
            value,
        })
    }

    fn next_block(&mut self) -> Result<NextBlock, ParseError> {
        let start = self.expect(&Token::Next)?;
        self.expect(&Token::LBrace)?;
        let mut items = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) {
            items.push(self.next_item()?);
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(NextBlock {
            items,
            span: start.merge(end),
        })
    }

    fn next_item(&mut self) -> Result<NextItem, ParseError> {
        match self.peek() {
            Some(Token::When) => {
                let start = self.advance().1;
                let condition = self.expr()?;
                self.expect(&Token::FatArrow)?;
                let event = self.expr()?;
                Ok(NextItem::When {
                    condition,
                    event,
                    span: start.merge(self.cur_span()),
                })
            }
            Some(Token::Else) => {
                let start = self.advance().1;
                self.expect(&Token::FatArrow)?;
                let end = self.expect(&Token::Idle)?;
                Ok(NextItem::Else(start.merge(end)))
            }
            Some(tok) => Err(ParseError::expected(
                "`when` or `else`",
                &format!("`{tok}`"),
                self.cur_span(),
            )),
            None => Err(ParseError::eof(self.cur_span())),
        }
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
            systems,
            body,
        })
    }

    // ── Verify / Proof / Lemma ───────────────────────────────────────

    fn verify_decl(&mut self) -> Result<VerifyDecl, ParseError> {
        let start = self.expect(&Token::Verify)?;
        let (label, _) = self.expect_string()?;
        self.expect(&Token::For)?;

        let mut targets = vec![self.verify_target()?];
        while self.eat(&Token::Comma).is_some() {
            targets.push(self.verify_target()?);
        }

        self.expect(&Token::LBrace)?;
        let mut asserts = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) {
            self.expect(&Token::Assert)?;
            asserts.push(self.expr()?);
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(VerifyDecl {
            label,
            targets,
            asserts,
            span: start.merge(end),
        })
    }

    fn verify_target(&mut self) -> Result<VerifyTarget, ParseError> {
        let (system, start) = self.expect_name()?;
        self.expect(&Token::LBracket)?;
        let (min, _) = self.expect_int()?;
        self.expect(&Token::DotDot)?;
        let (max, _) = self.expect_int()?;
        let end = self.expect(&Token::RBracket)?;
        Ok(VerifyTarget {
            system,
            min,
            max,
            span: start.merge(end),
        })
    }

    fn proof_decl(&mut self) -> Result<ProofDecl, ParseError> {
        let start = self.expect(&Token::Proof)?;
        let (label, _) = self.expect_string()?;
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
        let mut shows = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) {
            self.expect(&Token::Show)?;
            shows.push(self.expr()?);
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(ProofDecl {
            label,
            systems,
            invariants,
            shows,
            span: start.merge(end),
        })
    }

    fn lemma_decl(&mut self) -> Result<LemmaDecl, ParseError> {
        let start = self.expect(&Token::Lemma)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::LBrace)?;
        let mut body = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) {
            body.push(self.expr()?);
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(LemmaDecl {
            name,
            body,
            span: start.merge(end),
        })
    }

    // ── Scene Declarations ───────────────────────────────────────────

    fn scene_decl(&mut self) -> Result<SceneDecl, ParseError> {
        let start = self.expect(&Token::Scene)?;
        let (label, _) = self.expect_string()?;
        self.expect(&Token::For)?;

        let mut systems = vec![];
        let (n, _) = self.expect_name()?;
        systems.push(n);
        while self.eat(&Token::Comma).is_some() {
            let (n, _) = self.expect_name()?;
            systems.push(n);
        }

        self.expect(&Token::LBrace)?;
        let mut items = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) {
            items.push(self.scene_item()?);
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(SceneDecl {
            label,
            systems,
            items,
            span: start.merge(end),
        })
    }

    fn scene_item(&mut self) -> Result<SceneItem, ParseError> {
        match self.peek() {
            Some(Token::Given) => {
                let start = self.advance().1;
                if matches!(self.peek(), Some(Token::LBrace)) {
                    self.advance();
                    let mut items = Vec::new();
                    while !matches!(self.peek(), Some(Token::RBrace)) {
                        items.push(self.given_item()?);
                    }
                    let end = self.expect(&Token::RBrace)?;
                    Ok(SceneItem::GivenBlock {
                        items,
                        span: start.merge(end),
                    })
                } else {
                    // given let name = one QualType [where expr]
                    self.expect(&Token::Let)?;
                    let (name, _) = self.expect_name()?;
                    self.expect(&Token::Eq)?;
                    self.expect(&Token::One)?;
                    let qual_type = self.qual_type()?;
                    let condition = if self.eat(&Token::Where).is_some() {
                        Some(self.expr()?)
                    } else {
                        None
                    };
                    let end_span = condition
                        .as_ref()
                        .map_or_else(|| self.cur_span(), |e| e.span);
                    Ok(SceneItem::Given {
                        name,
                        qual_type,
                        condition,
                        span: start.merge(end_span),
                    })
                }
            }
            Some(Token::When) => {
                let start = self.advance().1;
                if matches!(self.peek(), Some(Token::LBrace)) {
                    self.advance();
                    let mut items = Vec::new();
                    while !matches!(self.peek(), Some(Token::RBrace)) {
                        items.push(self.when_item()?);
                    }
                    let end = self.expect(&Token::RBrace)?;
                    Ok(SceneItem::WhenBlock {
                        items,
                        span: start.merge(end),
                    })
                } else if matches!(self.peek(), Some(Token::Action)) {
                    let (name, invoc, card, end) = self.when_action_inner()?;
                    Ok(SceneItem::WhenAction {
                        name,
                        invoc,
                        card,
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
                    while !matches!(self.peek(), Some(Token::RBrace)) {
                        items.push(self.then_item()?);
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
            Some(tok) => Err(ParseError::expected(
                "`given`, `when`, or `then`",
                &format!("`{tok}`"),
                self.cur_span(),
            )),
            None => Err(ParseError::eof(self.cur_span())),
        }
    }

    fn given_item(&mut self) -> Result<GivenItem, ParseError> {
        let start = self.expect(&Token::Let)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::Eq)?;
        self.expect(&Token::One)?;
        let qual_type = self.qual_type()?;
        let condition = if self.eat(&Token::Where).is_some() {
            Some(self.expr()?)
        } else {
            None
        };
        let end_span = condition
            .as_ref()
            .map_or_else(|| self.cur_span(), |e| e.span);
        Ok(GivenItem {
            name,
            qual_type,
            condition,
            span: start.merge(end_span),
        })
    }

    fn qual_type(&mut self) -> Result<QualType, ParseError> {
        let (name, start) = self.expect_name()?;
        if self.eat(&Token::ColonColon).is_some() {
            let (inner, end) = self.expect_name()?;
            Ok(QualType::Qualified {
                module: name,
                name: inner,
                span: start.merge(end),
            })
        } else {
            Ok(QualType::Simple { name, span: start })
        }
    }

    fn when_item(&mut self) -> Result<WhenItem, ParseError> {
        match self.peek() {
            Some(Token::Action) => {
                let start = self.cur_span();
                let (name, invoc, card, end) = self.when_action_inner()?;
                Ok(WhenItem::Action {
                    name,
                    invoc,
                    card,
                    span: start.merge(end),
                })
            }
            Some(Token::Assume) => {
                let start = self.advance().1;
                let expr = self.expr()?;
                Ok(WhenItem::Assume {
                    span: start.merge(expr.span),
                    expr,
                })
            }
            Some(tok) => Err(ParseError::expected(
                "`action` or `assume`",
                &format!("`{tok}`"),
                self.cur_span(),
            )),
            None => Err(ParseError::eof(self.cur_span())),
        }
    }

    /// Parse `action name = ActionInvoc [{CardValue}]` (shared by scene item and when item).
    fn when_action_inner(
        &mut self,
    ) -> Result<(String, ActionInvoc, Option<CardValue>, Span), ParseError> {
        self.expect(&Token::Action)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::Eq)?;
        let invoc = self.action_invoc()?;
        let (card, end) = if self.eat(&Token::LBrace).is_some() {
            let cv = self.card_value()?;
            let end = self.expect(&Token::RBrace)?;
            (Some(cv), end)
        } else {
            (None, invoc.span)
        };
        Ok((name, invoc, card, end))
    }

    fn action_invoc(&mut self) -> Result<ActionInvoc, ParseError> {
        let (first, start) = self.expect_name()?;
        if self.eat(&Token::ColonColon).is_some() {
            let (name, _) = self.expect_name()?;
            self.expect(&Token::LParen)?;
            let args = self.comma_sep(&Token::RParen, Parser::invoc_arg)?;
            let end = self.expect(&Token::RParen)?;
            Ok(ActionInvoc {
                qualifier: Some(first),
                name,
                args,
                span: start.merge(end),
            })
        } else {
            self.expect(&Token::LParen)?;
            let args = self.comma_sep(&Token::RParen, Parser::invoc_arg)?;
            let end = self.expect(&Token::RParen)?;
            Ok(ActionInvoc {
                qualifier: None,
                name: first,
                args,
                span: start.merge(end),
            })
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

    fn card_value(&mut self) -> Result<CardValue, ParseError> {
        match self.peek() {
            Some(Token::One) => {
                self.advance();
                Ok(CardValue::One)
            }
            Some(Token::Lone) => {
                self.advance();
                Ok(CardValue::Lone)
            }
            Some(Token::Some) => {
                self.advance();
                Ok(CardValue::Some)
            }
            Some(Token::No) => {
                self.advance();
                Ok(CardValue::No)
            }
            Some(Token::IntLit(_)) => {
                let (n, _) = self.expect_int()?;
                Ok(CardValue::Num(n))
            }
            Some(tok) => Err(ParseError::expected(
                "cardinality (`one`, `lone`, `some`, `no`, or integer)",
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

    // ── Expressions (Pratt parser) ───────────────────────────────────

    pub fn expr(&mut self) -> Result<Expr, ParseError> {
        self.expr_bp(0)
    }

    fn expr_bp(&mut self, min_bp: u8) -> Result<Expr, ParseError> {
        let start = self.cur_span();
        let mut lhs = self.expr_prefix(min_bp)?;

        loop {
            if self.at_end() {
                break;
            }

            // Postfix operators (level 13, bp 27)
            if let Some(l_bp) = self.peek().and_then(postfix_bp) {
                if l_bp < min_bp {
                    break;
                }
                lhs = self.parse_postfix(lhs)?;
                continue;
            }

            // Named pair: only when lhs is Var and next is Colon (not ColonColon)
            if matches!(self.peek(), Some(Token::Colon))
                && matches!(&lhs.kind, ExprKind::Var(_))
                && 1 >= min_bp
            {
                if let ExprKind::Var(name) = &lhs.kind {
                    let name = name.clone();
                    self.advance(); // consume :
                    let rhs = self.expr_bp(3)?; // rhs is Expr1
                    let span = start.merge(rhs.span);
                    lhs = Expr {
                        kind: ExprKind::NamedPair(name, Box::new(rhs)),
                        span,
                    };
                    continue;
                }
            }

            // Infix operators (skip `in` when inside let binding values)
            if let Some((l_bp, r_bp)) = self.peek().and_then(|t| {
                if self.no_in && matches!(t, Token::In) {
                    None
                } else {
                    infix_bp(t)
                }
            }) {
                if l_bp < min_bp {
                    break;
                }
                let (op, _) = self.advance();
                let rhs = self.expr_bp(r_bp)?;
                let span = start.merge(rhs.span);
                lhs = make_infix(lhs, &op, rhs, span);
                continue;
            }

            break;
        }

        Ok(lhs)
    }

    fn expr_prefix(&mut self, min_bp: u8) -> Result<Expr, ParseError> {
        let start = self.cur_span();
        match self.peek() {
            // Level 12 prefix: unary negation
            Some(Token::Minus) if min_bp <= 25 => {
                self.advance();
                let operand = self.expr_bp(25)?;
                Ok(Expr {
                    kind: ExprKind::Neg(Box::new(operand)),
                    span: start.merge(self.prev_span()),
                })
            }
            // Level 12 prefix: cardinality
            Some(Token::Hash) if min_bp <= 25 => {
                self.advance();
                let operand = self.expr_bp(25)?;
                Ok(Expr {
                    kind: ExprKind::Card(Box::new(operand)),
                    span: start.merge(self.prev_span()),
                })
            }
            // Level 7 prefix: not
            Some(Token::Not) if min_bp <= 15 => {
                self.advance();
                let operand = self.expr_bp(15)?;
                Ok(Expr {
                    kind: ExprKind::Not(Box::new(operand)),
                    span: start.merge(self.prev_span()),
                })
            }
            // Level 3 prefix: temporal
            Some(Token::Always) if min_bp <= 7 => {
                self.advance();
                let body = self.expr_bp(7)?;
                Ok(Expr {
                    kind: ExprKind::Always(Box::new(body)),
                    span: start.merge(self.prev_span()),
                })
            }
            Some(Token::Eventually) if min_bp <= 7 => {
                self.advance();
                let body = self.expr_bp(7)?;
                Ok(Expr {
                    kind: ExprKind::Eventually(Box::new(body)),
                    span: start.merge(self.prev_span()),
                })
            }
            Some(Token::Assert) if min_bp <= 7 => {
                self.advance();
                let body = self.expr_bp(7)?;
                Ok(Expr {
                    kind: ExprKind::AssertExpr(Box::new(body)),
                    span: start.merge(self.prev_span()),
                })
            }
            // Level 3: quantifiers
            Some(
                Token::All | Token::Exists | Token::Some | Token::No | Token::One | Token::Lone,
            ) if min_bp <= 7 => self.parse_quantifier(),
            // Level 3: let ... in
            Some(Token::Let) if min_bp <= 7 => self.parse_let_expr(),
            // Level 3: lambda
            Some(Token::Fn) if min_bp <= 7 => self.parse_lambda(),
            // Level 3: match
            Some(Token::Match) if min_bp <= 7 => self.parse_match_expr(),
            // Atoms
            _ => self.expr_atom(),
        }
    }

    fn parse_quantifier(&mut self) -> Result<Expr, ParseError> {
        let (kind_tok, start) = self.advance();
        let (var, _) = self.expect_name()?;
        self.expect(&Token::Colon)?;
        let ty = self.type_ref()?;
        self.expect(&Token::Pipe)?;
        let body = self.expr_bp(0)?; // body is Expr (level 0)
        let span = start.merge(body.span);
        let kind = match kind_tok {
            Token::All => ExprKind::All(var, ty, Box::new(body)),
            Token::Exists => ExprKind::Exists(var, ty, Box::new(body)),
            Token::Some => ExprKind::SomeQ(var, ty, Box::new(body)),
            Token::No => ExprKind::NoQ(var, ty, Box::new(body)),
            Token::One => ExprKind::OneQ(var, ty, Box::new(body)),
            Token::Lone => ExprKind::LoneQ(var, ty, Box::new(body)),
            _ => unreachable!(),
        };
        Ok(Expr { kind, span })
    }

    fn parse_let_expr(&mut self) -> Result<Expr, ParseError> {
        let start = self.expect(&Token::Let)?;
        let old_no_in = self.no_in;
        self.no_in = true;
        let mut binds = vec![self.let_bind()?];
        while self.eat(&Token::Comma).is_some() {
            binds.push(self.let_bind()?);
        }
        self.no_in = old_no_in;
        self.expect(&Token::In)?;
        let body = self.expr_bp(7)?; // body is Expr3
        let span = start.merge(body.span);
        Ok(Expr {
            kind: ExprKind::Let(binds, Box::new(body)),
            span,
        })
    }

    fn let_bind(&mut self) -> Result<LetBind, ParseError> {
        let (name, start) = self.expect_name()?;
        let ty = if self.eat(&Token::Colon).is_some() {
            Some(self.type_ref()?)
        } else {
            None
        };
        self.expect(&Token::Eq)?;
        let value = self.expr()?;
        Ok(LetBind {
            span: start.merge(value.span),
            name,
            ty,
            value,
        })
    }

    fn parse_lambda(&mut self) -> Result<Expr, ParseError> {
        let start = self.expect(&Token::Fn)?;
        self.expect(&Token::LParen)?;
        let params = self.comma_sep(&Token::RParen, Parser::typed_param)?;
        self.expect(&Token::RParen)?;
        let ret_type = if self.eat(&Token::Colon).is_some() {
            Some(self.type_ref()?)
        } else {
            None
        };
        self.expect(&Token::FatArrow)?;
        let body = self.expr_bp(7)?; // body is Expr3
        let span = start.merge(body.span);
        match ret_type {
            Some(ty) => Ok(Expr {
                kind: ExprKind::LambdaT(params, ty, Box::new(body)),
                span,
            }),
            None => Ok(Expr {
                kind: ExprKind::Lambda(params, Box::new(body)),
                span,
            }),
        }
    }

    fn parse_match_expr(&mut self) -> Result<Expr, ParseError> {
        let start = self.expect(&Token::Match)?;
        let scrutinee = self.expr()?;
        self.expect(&Token::LBrace)?;
        let mut arms = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            arms.push(self.match_arm()?);
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(Expr {
            kind: ExprKind::Match(Box::new(scrutinee), arms),
            span: start.merge(end),
        })
    }

    fn match_arm(&mut self) -> Result<MatchArm, ParseError> {
        let pattern = self.pattern()?;
        let guard = if self.eat(&Token::If).is_some() {
            Some(Box::new(self.expr()?))
        } else {
            None
        };
        self.expect(&Token::FatArrow)?;
        let body = self.expr_bp(7)?; // body is Expr3
        let span = pattern.span().merge(body.span);
        Ok(MatchArm {
            pattern,
            guard,
            body,
            span,
        })
    }

    fn pattern(&mut self) -> Result<Pattern, ParseError> {
        let left = self.pattern_atom()?;
        if self.eat(&Token::Pipe).is_some() {
            let right = self.pattern()?; // right-associative
            let span = left.span().merge(right.span());
            Ok(Pattern::Or(Box::new(left), Box::new(right), span))
        } else {
            Ok(left)
        }
    }

    fn pattern_atom(&mut self) -> Result<Pattern, ParseError> {
        match self.peek() {
            Some(Token::Underscore) => {
                let (_, span) = self.advance();
                Ok(Pattern::Wild(span))
            }
            Some(Token::Name(_)) => {
                let (name, span) = self.expect_name()?;
                if self.peek() == Some(&Token::LBrace) {
                    // Record pattern: Name { field: pat, ... }
                    self.expect(&Token::LBrace)?;
                    let mut fields = Vec::new();
                    let mut has_rest = false;
                    while self.peek() != Some(&Token::RBrace) {
                        if self.eat(&Token::DotDot).is_some() {
                            has_rest = true;
                            break;
                        }
                        let (fname, fspan) = self.expect_name()?;
                        self.expect(&Token::Colon)?;
                        let fpat = self.pattern()?;
                        let fp_span = fspan.merge(fpat.span());
                        fields.push(FieldPat {
                            name: fname,
                            pattern: fpat,
                            span: fp_span,
                        });
                        if self.peek() != Some(&Token::RBrace)
                            && self.peek() != Some(&Token::DotDot)
                        {
                            self.expect(&Token::Comma)?;
                        }
                    }
                    let end = self.expect(&Token::RBrace)?;
                    Ok(Pattern::Ctor(name, fields, has_rest, span.merge(end)))
                } else {
                    // Simple name — could be constructor or variable (resolved later)
                    Ok(Pattern::Var(name, span))
                }
            }
            Some(Token::LParen) => {
                self.advance();
                let inner = self.pattern()?;
                self.expect(&Token::RParen)?;
                Ok(inner)
            }
            Some(tok) => Err(ParseError::expected(
                "pattern",
                &format!("`{tok}`"),
                self.cur_span(),
            )),
            None => Err(ParseError::eof(self.cur_span())),
        }
    }

    #[allow(clippy::too_many_lines)]
    fn expr_atom(&mut self) -> Result<Expr, ParseError> {
        let start = self.cur_span();
        match self.peek() {
            // State atoms: @Name, @Name::Name, @Name::Name::Name
            Some(Token::At) => {
                self.advance();
                let (n1, n1_span) = self.expect_name()?;
                if self.eat(&Token::ColonColon).is_some() {
                    let (n2, n2_span) = self.expect_name()?;
                    if self.eat(&Token::ColonColon).is_some() {
                        let (n3, n3_span) = self.expect_name()?;
                        Ok(Expr {
                            kind: ExprKind::State3(n1, n2, n3),
                            span: start.merge(n3_span),
                        })
                    } else {
                        Ok(Expr {
                            kind: ExprKind::State2(n1, n2),
                            span: start.merge(n2_span),
                        })
                    }
                } else {
                    Ok(Expr {
                        kind: ExprKind::State1(n1),
                        span: start.merge(n1_span),
                    })
                }
            }
            // Parenthesized expr or tuple literal
            Some(Token::LParen) => {
                self.advance();
                let first = self.expr()?;
                if self.eat(&Token::Comma).is_some() {
                    let mut elements = vec![first];
                    if !matches!(self.peek(), Some(Token::RParen)) {
                        elements.push(self.expr()?);
                        while self.eat(&Token::Comma).is_some() {
                            elements.push(self.expr()?);
                        }
                    }
                    let end = self.expect(&Token::RParen)?;
                    Ok(Expr {
                        kind: ExprKind::TupleLit(elements),
                        span: start.merge(end),
                    })
                } else {
                    let end = self.expect(&Token::RParen)?;
                    // Parenthesized expression: just adjust span
                    Ok(Expr {
                        kind: first.kind,
                        span: start.merge(end),
                    })
                }
            }
            // Literals
            Some(Token::True) => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::True,
                    span: start,
                })
            }
            Some(Token::False) => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::False,
                    span: start,
                })
            }
            Some(Token::IntLit(_)) => {
                let (n, span) = self.expect_int()?;
                Ok(Expr {
                    kind: ExprKind::Int(n),
                    span,
                })
            }
            Some(Token::DoubleLit(_)) => {
                let (tok, span) = self.advance();
                if let Token::DoubleLit(v) = tok {
                    Ok(Expr {
                        kind: ExprKind::Real(v),
                        span,
                    })
                } else {
                    unreachable!()
                }
            }
            Some(Token::FloatLit(_)) => {
                let (tok, span) = self.advance();
                if let Token::FloatLit(v) = tok {
                    Ok(Expr {
                        kind: ExprKind::Float(v),
                        span,
                    })
                } else {
                    unreachable!()
                }
            }
            Some(Token::StringLit(_)) => {
                let (s, span) = self.expect_string()?;
                Ok(Expr {
                    kind: ExprKind::Str(s),
                    span,
                })
            }
            // Name, qualified ref (Name::Name, Name::Name::Name), or variable
            Some(Token::Name(_)) => {
                let (n1, n1_span) = self.expect_name()?;
                if self.eat(&Token::ColonColon).is_some() {
                    let (n2, n2_span) = self.expect_name()?;
                    if self.eat(&Token::ColonColon).is_some() {
                        let (n3, n3_span) = self.expect_name()?;
                        Ok(Expr {
                            kind: ExprKind::Qual3(n1, n2, n3),
                            span: n1_span.merge(n3_span),
                        })
                    } else {
                        Ok(Expr {
                            kind: ExprKind::Qual2(n1, n2),
                            span: n1_span.merge(n2_span),
                        })
                    }
                } else {
                    Ok(Expr {
                        kind: ExprKind::Var(n1),
                        span: n1_span,
                    })
                }
            }
            Some(tok) => Err(ParseError::expected(
                "expression",
                &format!("`{tok}`"),
                self.cur_span(),
            )),
            None => Err(ParseError::eof(self.cur_span())),
        }
    }

    fn parse_postfix(&mut self, lhs: Expr) -> Result<Expr, ParseError> {
        let start = lhs.span;
        match self.peek() {
            Some(Token::Prime) => {
                let end = self.advance().1;
                Ok(Expr {
                    kind: ExprKind::Prime(Box::new(lhs)),
                    span: start.merge(end),
                })
            }
            Some(Token::Dot) => {
                self.advance();
                let (name, end) = self.expect_name()?;
                Ok(Expr {
                    kind: ExprKind::Field(Box::new(lhs), name),
                    span: start.merge(end),
                })
            }
            Some(Token::LParen) => {
                self.advance();
                let args = self.comma_sep_expr(&Token::RParen)?;
                let end = self.expect(&Token::RParen)?;
                Ok(Expr {
                    kind: ExprKind::Call(Box::new(lhs), args),
                    span: start.merge(end),
                })
            }
            Some(Token::LBracket) => {
                self.advance();
                let refs = self.comma_sep_expr(&Token::RBracket)?;
                self.expect(&Token::RBracket)?;
                self.expect(&Token::LParen)?;
                let args = self.comma_sep_expr(&Token::RParen)?;
                let end = self.expect(&Token::RParen)?;
                Ok(Expr {
                    kind: ExprKind::CallR(Box::new(lhs), refs, args),
                    span: start.merge(end),
                })
            }
            _ => Err(ParseError::general(
                "unexpected postfix operator",
                self.cur_span(),
            )),
        }
    }

    fn prev_span(&self) -> Span {
        if self.pos > 0 {
            self.tokens[self.pos - 1].1
        } else {
            Span { start: 0, end: 0 }
        }
    }

    // ── Generic helpers ──────────────────────────────────────────────

    fn comma_sep<T>(
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

    fn comma_sep_expr(&mut self, end: &Token) -> Result<Vec<Expr>, ParseError> {
        let mut items = Vec::new();
        if self.peek() == Some(end) {
            return Ok(items);
        }
        items.push(self.expr()?);
        while self.eat(&Token::Comma).is_some() {
            items.push(self.expr()?);
        }
        Ok(items)
    }
}

fn make_infix(lhs: Expr, op: &Token, rhs: Expr, span: Span) -> Expr {
    let kind = match op {
        Token::PipeGt => ExprKind::Pipe(Box::new(lhs), Box::new(rhs)),
        Token::Pipe => ExprKind::Unord(Box::new(lhs), Box::new(rhs)),
        Token::PipePipe => ExprKind::Conc(Box::new(lhs), Box::new(rhs)),
        Token::CaretPipe => ExprKind::Xor(Box::new(lhs), Box::new(rhs)),
        Token::Arrow => ExprKind::Seq(Box::new(lhs), Box::new(rhs)),
        Token::Amp => ExprKind::SameStep(Box::new(lhs), Box::new(rhs)),
        Token::Implies => ExprKind::Impl(Box::new(lhs), Box::new(rhs)),
        Token::Eq => ExprKind::Assign(Box::new(lhs), Box::new(rhs)),
        Token::Or => ExprKind::Or(Box::new(lhs), Box::new(rhs)),
        Token::And => ExprKind::And(Box::new(lhs), Box::new(rhs)),
        Token::EqEq => ExprKind::Eq(Box::new(lhs), Box::new(rhs)),
        Token::BangEq => ExprKind::NEq(Box::new(lhs), Box::new(rhs)),
        Token::In => ExprKind::In(Box::new(lhs), Box::new(rhs)),
        Token::Lt => ExprKind::Lt(Box::new(lhs), Box::new(rhs)),
        Token::Gt => ExprKind::Gt(Box::new(lhs), Box::new(rhs)),
        Token::LtEq => ExprKind::Le(Box::new(lhs), Box::new(rhs)),
        Token::GtEq => ExprKind::Ge(Box::new(lhs), Box::new(rhs)),
        Token::Plus => ExprKind::Add(Box::new(lhs), Box::new(rhs)),
        Token::Minus => ExprKind::Sub(Box::new(lhs), Box::new(rhs)),
        Token::Star => ExprKind::Mul(Box::new(lhs), Box::new(rhs)),
        Token::Slash => ExprKind::Div(Box::new(lhs), Box::new(rhs)),
        Token::Percent => ExprKind::Mod(Box::new(lhs), Box::new(rhs)),
        _ => unreachable!("not an infix operator: {op}"),
    };
    Expr { kind, span }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lex;

    fn parse_expr(src: &str) -> Expr {
        let tokens = lex::lex(src).expect("lex error");
        let mut parser = Parser::new(tokens);
        parser.expr().expect("parse error")
    }

    fn parse_program(src: &str) -> Program {
        let tokens = lex::lex(src).expect("lex error");
        let mut parser = Parser::new(tokens);
        parser.parse_program().expect("parse error")
    }

    // ── Expression precedence tests ──────────────────────────────────

    #[test]
    fn atom_int() {
        let e = parse_expr("42");
        assert!(matches!(e.kind, ExprKind::Int(42)));
    }

    #[test]
    fn atom_var() {
        let e = parse_expr("status");
        assert!(matches!(e.kind, ExprKind::Var(ref s) if s == "status"));
    }

    #[test]
    fn atom_true_false() {
        assert!(matches!(parse_expr("true").kind, ExprKind::True));
        assert!(matches!(parse_expr("false").kind, ExprKind::False));
    }

    #[test]
    fn atom_state() {
        let e = parse_expr("@Pending");
        assert!(matches!(e.kind, ExprKind::State1(ref s) if s == "Pending"));
    }

    #[test]
    fn atom_state2() {
        let e = parse_expr("@OrderStatus::Paid");
        assert!(
            matches!(e.kind, ExprKind::State2(ref a, ref b) if a == "OrderStatus" && b == "Paid")
        );
    }

    #[test]
    fn atom_qual2() {
        let e = parse_expr("Commerce::confirm_payment");
        assert!(
            matches!(e.kind, ExprKind::Qual2(ref a, ref b) if a == "Commerce" && b == "confirm_payment")
        );
    }

    #[test]
    fn binary_add() {
        let e = parse_expr("a + b");
        assert!(matches!(e.kind, ExprKind::Add(_, _)));
    }

    #[test]
    fn precedence_add_mul() {
        // a + b * c → a + (b * c)
        let e = parse_expr("a + b * c");
        match &e.kind {
            ExprKind::Add(lhs, rhs) => {
                assert!(matches!(lhs.kind, ExprKind::Var(ref s) if s == "a"));
                assert!(matches!(rhs.kind, ExprKind::Mul(_, _)));
            }
            other => panic!("expected Add, got {other:?}"),
        }
    }

    #[test]
    fn precedence_and_or() {
        // a or b and c → a or (b and c)
        let e = parse_expr("a or b and c");
        match &e.kind {
            ExprKind::Or(_, rhs) => {
                assert!(matches!(rhs.kind, ExprKind::And(_, _)));
            }
            other => panic!("expected Or, got {other:?}"),
        }
    }

    #[test]
    fn precedence_implies_and() {
        // a and b implies c → (a and b) implies c
        let e = parse_expr("a and b implies c");
        assert!(matches!(e.kind, ExprKind::Impl(_, _)));
    }

    #[test]
    fn right_assoc_seq() {
        // a -> b -> c → a -> (b -> c)
        let e = parse_expr("a -> b -> c");
        match &e.kind {
            ExprKind::Seq(lhs, rhs) => {
                assert!(matches!(lhs.kind, ExprKind::Var(ref s) if s == "a"));
                assert!(matches!(rhs.kind, ExprKind::Seq(_, _)));
            }
            other => panic!("expected Seq, got {other:?}"),
        }
    }

    #[test]
    fn right_assoc_assign() {
        // a = b = c → a = (b = c)
        let e = parse_expr("a = b = c");
        match &e.kind {
            ExprKind::Assign(_, rhs) => {
                assert!(matches!(rhs.kind, ExprKind::Assign(_, _)));
            }
            other => panic!("expected Assign, got {other:?}"),
        }
    }

    #[test]
    fn prefix_neg() {
        let e = parse_expr("-x");
        assert!(matches!(e.kind, ExprKind::Neg(_)));
    }

    #[test]
    fn prefix_not() {
        let e = parse_expr("not x");
        assert!(matches!(e.kind, ExprKind::Not(_)));
    }

    #[test]
    fn prefix_card() {
        let e = parse_expr("#s");
        assert!(matches!(e.kind, ExprKind::Card(_)));
    }

    #[test]
    fn postfix_prime() {
        let e = parse_expr("status'");
        match &e.kind {
            ExprKind::Prime(inner) => {
                assert!(matches!(inner.kind, ExprKind::Var(ref s) if s == "status"));
            }
            other => panic!("expected Prime, got {other:?}"),
        }
    }

    #[test]
    fn postfix_field() {
        let e = parse_expr("o.status");
        match &e.kind {
            ExprKind::Field(inner, name) => {
                assert!(matches!(inner.kind, ExprKind::Var(ref s) if s == "o"));
                assert_eq!(name, "status");
            }
            other => panic!("expected Field, got {other:?}"),
        }
    }

    #[test]
    fn postfix_call() {
        let e = parse_expr("f(x, y)");
        match &e.kind {
            ExprKind::Call(callee, args) => {
                assert!(matches!(callee.kind, ExprKind::Var(ref s) if s == "f"));
                assert_eq!(args.len(), 2);
            }
            other => panic!("expected Call, got {other:?}"),
        }
    }

    #[test]
    fn method_call() {
        let e = parse_expr("o.submit()");
        match &e.kind {
            ExprKind::Call(callee, args) => {
                assert!(matches!(callee.kind, ExprKind::Field(_, _)));
                assert!(args.is_empty());
            }
            other => panic!("expected Call, got {other:?}"),
        }
    }

    #[test]
    fn primed_assign() {
        let e = parse_expr("status' = @Paid");
        match &e.kind {
            ExprKind::Assign(lhs, rhs) => {
                assert!(matches!(lhs.kind, ExprKind::Prime(_)));
                assert!(matches!(rhs.kind, ExprKind::State1(_)));
            }
            other => panic!("expected Assign, got {other:?}"),
        }
    }

    #[test]
    fn always_all() {
        let e = parse_expr("always all o: Order | o.total >= 0");
        assert!(matches!(e.kind, ExprKind::Always(_)));
    }

    #[test]
    fn exists_quantifier() {
        let e = parse_expr("exists o: Order | o.id == order_id");
        assert!(matches!(e.kind, ExprKind::Exists(_, _, _)));
    }

    #[test]
    fn named_pair() {
        let e = parse_expr("order_id: order_id");
        assert!(matches!(e.kind, ExprKind::NamedPair(_, _)));
    }

    #[test]
    fn let_expr() {
        let e = parse_expr("let x = 1 in x + 1");
        match &e.kind {
            ExprKind::Let(binds, body) => {
                assert_eq!(binds.len(), 1);
                assert_eq!(binds[0].name, "x");
                assert!(matches!(body.kind, ExprKind::Add(_, _)));
            }
            other => panic!("expected Let, got {other:?}"),
        }
    }

    #[test]
    fn lambda() {
        let e = parse_expr("fn(x: Int) => x + 1");
        assert!(matches!(e.kind, ExprKind::Lambda(_, _)));
    }

    #[test]
    fn tuple_literal() {
        let e = parse_expr("(a, b, c)");
        match &e.kind {
            ExprKind::TupleLit(elems) => assert_eq!(elems.len(), 3),
            other => panic!("expected TupleLit, got {other:?}"),
        }
    }

    #[test]
    fn paren_expr() {
        let e = parse_expr("(a + b)");
        assert!(matches!(e.kind, ExprKind::Add(_, _)));
    }

    #[test]
    fn pipe_and_composition() {
        let e = parse_expr("a | b");
        assert!(matches!(e.kind, ExprKind::Unord(_, _)));

        let e = parse_expr("a || b");
        assert!(matches!(e.kind, ExprKind::Conc(_, _)));

        let e = parse_expr("a ^| b");
        assert!(matches!(e.kind, ExprKind::Xor(_, _)));

        let e = parse_expr("a |> b");
        assert!(matches!(e.kind, ExprKind::Pipe(_, _)));
    }

    #[test]
    fn equality_and_membership() {
        assert!(matches!(parse_expr("a == b").kind, ExprKind::Eq(_, _)));
        assert!(matches!(parse_expr("a != b").kind, ExprKind::NEq(_, _)));
        assert!(matches!(parse_expr("a in b").kind, ExprKind::In(_, _)));
    }

    #[test]
    fn comparison() {
        assert!(matches!(parse_expr("a < b").kind, ExprKind::Lt(_, _)));
        assert!(matches!(parse_expr("a > b").kind, ExprKind::Gt(_, _)));
        assert!(matches!(parse_expr("a <= b").kind, ExprKind::Le(_, _)));
        assert!(matches!(parse_expr("a >= b").kind, ExprKind::Ge(_, _)));
    }

    #[test]
    fn same_step() {
        assert!(matches!(parse_expr("a & b").kind, ExprKind::SameStep(_, _)));
    }

    #[test]
    fn eventually() {
        assert!(matches!(
            parse_expr("eventually p").kind,
            ExprKind::Eventually(_)
        ));
    }

    // ── Type reference tests ─────────────────────────────────────────

    #[test]
    fn type_ref_simple() {
        let src = "fn id(x: Int): Int = x";
        let prog = parse_program(src);
        assert_eq!(prog.decls.len(), 1);
        if let TopDecl::Fn(f) = &prog.decls[0] {
            assert_eq!(f.name, "id");
            assert!(matches!(f.ret_type.kind, TypeRefKind::Simple(ref s) if s == "Int"));
        } else {
            panic!("expected Fn");
        }
    }

    #[test]
    fn type_ref_fn() {
        let src = "fn apply(f: Int -> Bool, x: Int): Bool = f(x)";
        let prog = parse_program(src);
        if let TopDecl::Fn(f) = &prog.decls[0] {
            assert!(matches!(f.params[0].ty.kind, TypeRefKind::Fn(_, _)));
        } else {
            panic!("expected Fn");
        }
    }

    // ── Declaration tests ────────────────────────────────────────────

    #[test]
    fn import_decl() {
        let prog = parse_program(r#"import "billing.abide" as Billing"#);
        assert_eq!(prog.decls.len(), 1);
        if let TopDecl::Import(i) = &prog.decls[0] {
            assert_eq!(i.path, "billing.abide");
            assert_eq!(i.alias, "Billing");
        } else {
            panic!("expected Import");
        }
    }

    #[test]
    fn use_all() {
        let prog = parse_program("use Billing :: *");
        if let TopDecl::Use(UseDecl::All { module, .. }) = &prog.decls[0] {
            assert_eq!(module, "Billing");
        } else {
            panic!("expected Use::All");
        }
    }

    #[test]
    fn use_items() {
        let src = "use Billing::{PaymentIntent as PI, open_intent, capture_payment}";
        let prog = parse_program(src);
        if let TopDecl::Use(UseDecl::Items { module, items, .. }) = &prog.decls[0] {
            assert_eq!(module, "Billing");
            assert_eq!(items.len(), 3);
        } else {
            panic!("expected Use::Items");
        }
    }

    #[test]
    fn const_decl() {
        let prog = parse_program("const MAX_ORDERS = 500");
        if let TopDecl::Const(c) = &prog.decls[0] {
            assert_eq!(c.name, "MAX_ORDERS");
            assert!(matches!(c.value.kind, ExprKind::Int(500)));
        } else {
            panic!("expected Const");
        }
    }

    #[test]
    fn sum_type() {
        let prog = parse_program("type OrderStatus = Pending | AwaitingPayment | Paid");
        if let TopDecl::Type(t) = &prog.decls[0] {
            assert_eq!(t.name, "OrderStatus");
            assert_eq!(t.variants.len(), 3);
        } else {
            panic!("expected Type");
        }
    }

    #[test]
    fn record_type() {
        let prog = parse_program("type Address { street: String, city: String }");
        if let TopDecl::Record(r) = &prog.decls[0] {
            assert_eq!(r.name, "Address");
            assert_eq!(r.fields.len(), 2);
        } else {
            panic!("expected Record");
        }
    }

    #[test]
    fn entity_decl() {
        let src = r#"entity Order {
  field id: Id
  field status: OrderStatus = @Pending

  action submit()
    requires status == @Pending {
    status' = @AwaitingPayment
  }
}"#;
        let prog = parse_program(src);
        if let TopDecl::Entity(e) = &prog.decls[0] {
            assert_eq!(e.name, "Order");
            assert_eq!(e.items.len(), 3);
        } else {
            panic!("expected Entity");
        }
    }

    #[test]
    fn system_decl() {
        let src = r#"system Commerce {
  uses Order

  event pay(order_id: Id) {
    choose o: Order where o.id == order_id {
      o.submit()
    }
  }

  next {
    else => idle
  }
}"#;
        let prog = parse_program(src);
        if let TopDecl::System(s) = &prog.decls[0] {
            assert_eq!(s.name, "Commerce");
            assert_eq!(s.items.len(), 3); // uses + event + next
        } else {
            panic!("expected System");
        }
    }

    #[test]
    fn pred_decl() {
        let src = "pred non_negative(o: Order) = o.total >= 0";
        let prog = parse_program(src);
        if let TopDecl::Pred(p) = &prog.decls[0] {
            assert_eq!(p.name, "non_negative");
            assert_eq!(p.params.len(), 1);
        } else {
            panic!("expected Pred");
        }
    }

    #[test]
    fn prop_for() {
        let src = "prop safe for Commerce = always true";
        let prog = parse_program(src);
        if let TopDecl::Prop(p) = &prog.decls[0] {
            assert_eq!(p.name, "safe");
            assert_eq!(p.systems.len(), 1);
        } else {
            panic!("expected Prop");
        }
    }

    #[test]
    fn verify_decl() {
        let src = r#"verify "test" for Commerce[0..500] {
  assert always true
}"#;
        let prog = parse_program(src);
        if let TopDecl::Verify(v) = &prog.decls[0] {
            assert_eq!(v.label, "test");
            assert_eq!(v.targets.len(), 1);
            assert_eq!(v.targets[0].min, 0);
            assert_eq!(v.targets[0].max, 500);
            assert_eq!(v.asserts.len(), 1);
        } else {
            panic!("expected Verify");
        }
    }

    #[test]
    fn proof_decl() {
        let src = r#"proof "test" for Commerce
  invariant all o: Order | o.total >= 0 {
  show always true
}"#;
        let prog = parse_program(src);
        if let TopDecl::Proof(p) = &prog.decls[0] {
            assert_eq!(p.label, "test");
            assert_eq!(p.invariants.len(), 1);
            assert_eq!(p.shows.len(), 1);
        } else {
            panic!("expected Proof");
        }
    }

    #[test]
    fn lemma_decl() {
        let src = r#"lemma foo {
  a implies a
}"#;
        let prog = parse_program(src);
        if let TopDecl::Lemma(l) = &prog.decls[0] {
            assert_eq!(l.name, "foo");
            assert_eq!(l.body.len(), 1);
        } else {
            panic!("expected Lemma");
        }
    }

    #[test]
    fn scene_with_blocks() {
        let src = r#"scene "test" for Commerce {
  given {
    let o = one Order where o.total == 100
  }
  when {
    action pay_act = Commerce::pay(o.id){one}
    assume pay_act -> cap
  }
  then {
    assert o.status == @Paid
  }
}"#;
        let prog = parse_program(src);
        if let TopDecl::Scene(s) = &prog.decls[0] {
            assert_eq!(s.label, "test");
            assert_eq!(s.items.len(), 3);
        } else {
            panic!("expected Scene");
        }
    }

    #[test]
    fn contract_parsing() {
        let src = r#"entity Order {
  action submit()
    requires status == @Pending
    requires total > 0
    ensures status == @AwaitingPayment {
    status' = @AwaitingPayment
  }
}"#;
        let prog = parse_program(src);
        if let TopDecl::Entity(e) = &prog.decls[0] {
            if let EntityItem::Action(a) = &e.items[0] {
                assert_eq!(a.contracts.len(), 3);
            } else {
                panic!("expected Action");
            }
        } else {
            panic!("expected Entity");
        }
    }

    #[test]
    fn create_block() {
        let src = r#"system Billing {
  uses PaymentIntent

  event open_intent(order_id: Id) {
    create PaymentIntent {
      order_id = order_id
      amount = 0
      status = @Opened
    }
  }
}"#;
        let prog = parse_program(src);
        if let TopDecl::System(s) = &prog.decls[0] {
            if let SystemItem::Event(e) = &s.items[1] {
                assert_eq!(e.items.len(), 1);
                assert!(matches!(e.items[0], EventItem::Create(_)));
            } else {
                panic!("expected Event");
            }
        } else {
            panic!("expected System");
        }
    }

    // ── Match expression tests ──────────────────────────────────────

    #[test]
    fn match_simple() {
        let e = parse_expr("match s { Pending => 1 Confirmed => 2 }");
        if let ExprKind::Match(scrut, arms) = &e.kind {
            assert!(matches!(scrut.kind, ExprKind::Var(ref s) if s == "s"));
            assert_eq!(arms.len(), 2);
            assert!(matches!(arms[0].pattern, Pattern::Var(ref s, _) if s == "Pending"));
            assert!(matches!(arms[1].pattern, Pattern::Var(ref s, _) if s == "Confirmed"));
            assert!(arms[0].guard.is_none());
        } else {
            panic!("expected Match");
        }
    }

    #[test]
    fn match_wildcard() {
        let e = parse_expr("match x { _ => 0 }");
        if let ExprKind::Match(_, arms) = &e.kind {
            assert_eq!(arms.len(), 1);
            assert!(matches!(arms[0].pattern, Pattern::Wild(_)));
        } else {
            panic!("expected Match");
        }
    }

    #[test]
    fn match_record_pattern() {
        let e = parse_expr("match s { Circle { radius: r } => r }");
        if let ExprKind::Match(_, arms) = &e.kind {
            assert_eq!(arms.len(), 1);
            if let Pattern::Ctor(name, fields, has_rest, _) = &arms[0].pattern {
                assert_eq!(name, "Circle");
                assert_eq!(fields.len(), 1);
                assert_eq!(fields[0].name, "radius");
                assert!(!has_rest);
            } else {
                panic!("expected Ctor pattern");
            }
        } else {
            panic!("expected Match");
        }
    }

    #[test]
    fn match_guard() {
        let e = parse_expr("match s { Circle { radius: r } if r > 100 => 1 _ => 0 }");
        if let ExprKind::Match(_, arms) = &e.kind {
            assert_eq!(arms.len(), 2);
            assert!(arms[0].guard.is_some());
            assert!(arms[1].guard.is_none());
        } else {
            panic!("expected Match");
        }
    }

    #[test]
    fn match_or_pattern() {
        let e = parse_expr("match s { Pending | Confirmed => 1 _ => 0 }");
        if let ExprKind::Match(_, arms) = &e.kind {
            assert_eq!(arms.len(), 2);
            assert!(matches!(arms[0].pattern, Pattern::Or(_, _, _)));
        } else {
            panic!("expected Match");
        }
    }

    #[test]
    fn match_rest_pattern() {
        let e = parse_expr("match s { Circle { radius: r, .. } => r }");
        if let ExprKind::Match(_, arms) = &e.kind {
            if let Pattern::Ctor(_, _, has_rest, _) = &arms[0].pattern {
                assert!(has_rest);
            } else {
                panic!("expected Ctor pattern");
            }
        } else {
            panic!("expected Match");
        }
    }

    #[test]
    fn match_field_access_scrutinee() {
        let e = parse_expr("match o.status { Pending => 1 }");
        if let ExprKind::Match(scrut, _) = &e.kind {
            assert!(matches!(scrut.kind, ExprKind::Field(_, ref f) if f == "status"));
        } else {
            panic!("expected Match");
        }
    }
}
