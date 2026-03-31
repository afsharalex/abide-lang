use crate::ast::{
    ActionInvoc, AliasDecl, AxiomDecl, CardValue, ChooseBlock, ConstDecl, Contract, CreateBlock,
    CreateField, EntityAction, EntityDecl, EntityItem, EventDecl, EventItem, Expr, ExprKind,
    FieldDecl, FieldPat, FnDecl, ForBlock, GivenItem, IncludeDecl, InvocArg, LemmaDecl, LetBind,
    MatchArm, ModuleDecl, NextBlock, NextItem, Param, Pattern, PredDecl, Program, PropDecl,
    QualType, RecField, RecordDecl, SceneDecl, SceneItem, SystemDecl, SystemItem, ThenItem,
    TheoremDecl, TopDecl, TypeDecl, TypeRef, TypeRefKind, TypeVariant, TypedParam, UseDecl,
    UseItem, VerifyDecl, VerifyTarget, Visibility, WhenItem,
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

    /// Parse a program, stopping at the first error.
    pub fn parse_program(&mut self) -> Result<Program, ParseError> {
        let (program, errors) = self.parse_program_recovering();
        if let Some(err) = errors.into_iter().next() {
            return Err(err);
        }
        Ok(program)
    }

    /// Parse a program with error recovery.
    ///
    /// On parse error, skips tokens until the next top-level keyword
    /// and continues parsing. Returns a partial program with all
    /// successfully parsed declarations and all accumulated errors.
    pub fn parse_program_recovering(&mut self) -> (Program, Vec<ParseError>) {
        let start = self.cur_span();
        let mut decls = Vec::new();
        let mut errors = Vec::new();
        while !self.at_end() {
            let pos_before = self.pos;
            match self.top_decl() {
                Ok(decl) => decls.push(decl),
                Err(err) => {
                    errors.push(err);
                    // If the parser didn't advance (error at dispatch), skip the
                    // problematic token. If it did advance (error inside a
                    // declaration), scan forward to the next top-level keyword.
                    if self.pos == pos_before && !self.at_end() {
                        self.pos += 1;
                    }
                    self.skip_to_next_top_level();
                }
            }
        }
        let span = if decls.is_empty() {
            start
        } else {
            start.merge(self.cur_span())
        };
        (Program { decls, span }, errors)
    }

    /// Skip tokens until a top-level keyword or EOF is reached.
    /// Called after the caller has already ensured progress (skipped the
    /// error token if needed). Does NOT skip unconditionally.
    fn skip_to_next_top_level(&mut self) {
        while !self.at_end() {
            match self.peek() {
                Some(
                    Token::Module
                    | Token::Include
                    | Token::Pub
                    | Token::Use
                    | Token::Const
                    | Token::Fn
                    | Token::Type
                    | Token::Enum
                    | Token::Struct
                    | Token::Entity
                    | Token::System
                    | Token::Pred
                    | Token::Prop
                    | Token::Verify
                    | Token::Theorem
                    | Token::Lemma
                    | Token::Scene
                    | Token::Axiom,
                ) => return,
                _ => self.pos += 1,
            }
        }
    }

    fn top_decl(&mut self) -> Result<TopDecl, ParseError> {
        match self.peek() {
            Some(Token::Module) => Ok(TopDecl::Module(self.module_decl()?)),
            Some(Token::Include) => Ok(TopDecl::Include(self.include_decl()?)),
            Some(Token::Pub) => self.pub_decl(),
            Some(Token::Use) => Ok(TopDecl::Use(self.use_decl()?)),
            Some(Token::Const) => Ok(TopDecl::Const(self.const_decl()?)),
            Some(Token::Fn) => Ok(TopDecl::Fn(self.fn_decl()?)),
            Some(Token::Type) => self.alias_decl(),
            Some(Token::Enum) => self.enum_decl(),
            Some(Token::Struct) => self.struct_decl(),
            Some(Token::Entity) => Ok(TopDecl::Entity(self.entity_decl()?)),
            Some(Token::System) => Ok(TopDecl::System(self.system_decl()?)),
            Some(Token::Pred) => Ok(TopDecl::Pred(self.pred_decl()?)),
            Some(Token::Prop) => Ok(TopDecl::Prop(self.prop_decl()?)),
            Some(Token::Verify) => Ok(TopDecl::Verify(self.verify_decl()?)),
            Some(Token::Theorem) => Ok(TopDecl::Theorem(self.theorem_decl()?)),
            Some(Token::Lemma) => Ok(TopDecl::Lemma(self.lemma_decl()?)),
            Some(Token::Scene) => Ok(TopDecl::Scene(self.scene_decl()?)),
            Some(Token::Axiom) => Ok(TopDecl::Axiom(self.axiom_decl()?)),
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

    // ── Module / Include / Pub / Use ────────────────────────────────

    fn module_decl(&mut self) -> Result<ModuleDecl, ParseError> {
        let start = self.expect(&Token::Module)?;
        let (name, end) = self.expect_name()?;
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

    fn pub_decl(&mut self) -> Result<TopDecl, ParseError> {
        self.expect(&Token::Pub)?;
        match self.peek() {
            Some(Token::Type) => {
                let TopDecl::Alias(mut d) = self.alias_decl()? else {
                    unreachable!()
                };
                d.visibility = Visibility::Public;
                Ok(TopDecl::Alias(d))
            }
            Some(Token::Enum) => {
                let decl = self.enum_decl()?;
                match decl {
                    TopDecl::Type(mut t) => {
                        t.visibility = Visibility::Public;
                        Ok(TopDecl::Type(t))
                    }
                    _ => unreachable!(),
                }
            }
            Some(Token::Struct) => {
                let decl = self.struct_decl()?;
                match decl {
                    TopDecl::Record(mut r) => {
                        r.visibility = Visibility::Public;
                        Ok(TopDecl::Record(r))
                    }
                    _ => unreachable!(),
                }
            }
            Some(Token::Entity) => {
                let mut d = self.entity_decl()?;
                d.visibility = Visibility::Public;
                Ok(TopDecl::Entity(d))
            }
            Some(Token::Fn) => {
                let mut d = self.fn_decl()?;
                d.visibility = Visibility::Public;
                Ok(TopDecl::Fn(d))
            }
            Some(Token::Const) => {
                let mut d = self.const_decl()?;
                d.visibility = Visibility::Public;
                Ok(TopDecl::Const(d))
            }
            Some(Token::Pred) => {
                let mut d = self.pred_decl()?;
                d.visibility = Visibility::Public;
                Ok(TopDecl::Pred(d))
            }
            Some(Token::Prop) => {
                let mut d = self.prop_decl()?;
                d.visibility = Visibility::Public;
                Ok(TopDecl::Prop(d))
            }
            Some(tok) => Err(ParseError::expected(
                "`type`, `enum`, `struct`, `entity`, `fn`, `const`, `pred`, or `prop` after `pub`",
                &format!("`{tok}`"),
                self.cur_span(),
            )),
            None => Err(ParseError::eof(self.cur_span())),
        }
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
        //   = expr     (pure, no contracts or contracts allowed)
        //   { body }   (imperative form with blocks, consistent with action/event)
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

    // ── Type Declarations ────────────────────────────────────────────

    /// Parse `enum Name = Variant | Variant`
    fn enum_decl(&mut self) -> Result<TopDecl, ParseError> {
        let start = self.expect(&Token::Enum)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::Eq)?;
        let variants = self.type_variants()?;
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
            visibility: Visibility::Private,
            variants,
            span: start.merge(last_span),
        }))
    }

    /// Parse `struct Name { fields }`
    fn struct_decl(&mut self) -> Result<TopDecl, ParseError> {
        let start = self.expect(&Token::Struct)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::LBrace)?;
        let fields = self.comma_sep(&Token::RBrace, Parser::rec_field)?;
        let end = self.expect(&Token::RBrace)?;
        Ok(TopDecl::Record(RecordDecl {
            name,
            visibility: Visibility::Private,
            fields,
            span: start.merge(end),
        }))
    }

    /// Parse pipe-separated type variants: `Variant | Variant | ...`
    fn type_variants(&mut self) -> Result<Vec<TypeVariant>, ParseError> {
        let mut variants = vec![self.type_variant()?];
        while self.eat(&Token::Pipe).is_some() {
            variants.push(self.type_variant()?);
        }
        Ok(variants)
    }

    /// Parse `type Name = TypeRef` — always a type alias.
    /// Enums use `enum`, structs use `struct`.
    fn alias_decl(&mut self) -> Result<TopDecl, ParseError> {
        let start = self.expect(&Token::Type)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::Eq)?;
        let target = self.type_ref()?;
        Ok(TopDecl::Alias(AliasDecl {
            span: start.merge(target.span),
            name,
            visibility: Visibility::Private,
            target,
        }))
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
        } else if self.eat(&Token::Lt).is_some() {
            let types = self.comma_sep(&Token::Gt, Parser::type_ref)?;
            let end = self.expect(&Token::Gt)?;
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

    /// Parse a type reference without refinement (for fn return types).
    /// Refinement types on return positions are not allowed — use `ensures` instead.
    fn type_ref_no_refine(&mut self) -> Result<TypeRef, ParseError> {
        let lhs = self.type_ref_atom_no_refine()?;
        if self.eat(&Token::Arrow).is_some() {
            let rhs = self.type_ref_no_refine()?;
            let span = lhs.span.merge(rhs.span);
            Ok(TypeRef {
                kind: TypeRefKind::Fn(Box::new(lhs), Box::new(rhs)),
                span,
            })
        } else {
            Ok(lhs)
        }
    }

    /// Parse a type ref atom without refinement support.
    fn type_ref_atom_no_refine(&mut self) -> Result<TypeRef, ParseError> {
        if self.eat(&Token::LParen).is_some() {
            let start = self.cur_span();
            let first = self.type_ref_no_refine()?;
            if self.eat(&Token::Comma).is_some() {
                let mut types = vec![first];
                types.push(self.type_ref_no_refine()?);
                while self.eat(&Token::Comma).is_some() {
                    types.push(self.type_ref_no_refine()?);
                }
                let end = self.expect(&Token::RParen)?;
                Ok(TypeRef {
                    kind: TypeRefKind::Tuple(types),
                    span: start.merge(end),
                })
            } else {
                let end = self.expect(&Token::RParen)?;
                Ok(TypeRef {
                    kind: TypeRefKind::Paren(Box::new(first)),
                    span: start.merge(end),
                })
            }
        } else {
            let (name, start) = self.expect_name()?;
            if self.eat(&Token::Lt).is_some() {
                let types = self.comma_sep(&Token::Gt, Parser::type_ref)?;
                let end = self.expect(&Token::Gt)?;
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
            if self.eat(&Token::Lt).is_some() {
                let types = self.comma_sep(&Token::Gt, Parser::type_ref)?;
                let end = self.expect(&Token::Gt)?;
                let base = TypeRef {
                    kind: TypeRefKind::Param(name, types),
                    span: start.merge(end),
                };
                // Check for refinement: T<A> { pred }
                if self.eat(&Token::LBrace).is_some() {
                    let pred = self.expr()?;
                    let end_r = self.expect(&Token::RBrace)?;
                    Ok(TypeRef {
                        kind: TypeRefKind::RefineParam(Box::new(base), Box::new(pred)),
                        span: start.merge(end_r),
                    })
                } else {
                    Ok(base)
                }
            } else if self.eat(&Token::LBrace).is_some() {
                // Refinement type: T { pred }
                let pred = self.expr()?;
                let end = self.expect(&Token::RBrace)?;
                let base = TypeRef {
                    kind: TypeRefKind::Simple(name),
                    span: start,
                };
                Ok(TypeRef {
                    kind: TypeRefKind::Refine(Box::new(base), Box::new(pred)),
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
            visibility: Visibility::Private,
            items,
            span: start.merge(end),
        })
    }

    fn entity_item(&mut self) -> Result<EntityItem, ParseError> {
        match self.peek() {
            Some(Token::Action) => Ok(EntityItem::Action(self.entity_action()?)),
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
                "field declaration or `action`",
                &format!("`{tok}`"),
                self.cur_span(),
            )),
            None => Err(ParseError::eof(self.cur_span())),
        }
    }

    fn field_decl(&mut self) -> Result<FieldDecl, ParseError> {
        let start = self.cur_span();
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
        let mutable = self.eat(&Token::Mut).is_some();
        let (name, start) = self.expect_name()?;
        self.expect(&Token::Colon)?;
        let (ty, end) = self.expect_name()?;
        Ok(Param {
            name,
            ty,
            mutable,
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
                        // decreases expr, expr, ... (comma-separated measures)
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
        while !matches!(self.peek(), Some(Token::RBrace)) {
            items.push(self.block_item()?);
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
                // else if ...
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
            Some(Token::Use) => {
                let start = self.advance().1;
                let (name, end) = self.expect_name()?;
                Ok(SystemItem::Uses(name, start.merge(end)))
            }
            Some(Token::Event) => Ok(SystemItem::Event(self.event_decl()?)),
            Some(Token::Next) => Ok(SystemItem::Next(self.next_block()?)),
            Some(Token::Name(ref name)) if name == "uses" => Err(ParseError::expected_with_help(
                "`use`, `event`, or `next`",
                "`uses`",
                self.cur_span(),
                crate::messages::HINT_USES_KEYWORD,
            )),
            Some(tok) => Err(ParseError::expected(
                "`use`, `event`, or `next`",
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
            // Detect wrong-context keywords with helpful suggestions
            Some(Token::Given | Token::Then) => Err(ParseError::expected_with_help(
                "event body item",
                &format!("`{}`", self.peek().unwrap()),
                self.cur_span(),
                crate::messages::HINT_EVENT_BODY,
            )),
            Some(Token::Assert) => Err(ParseError::expected_with_help(
                "event body item",
                "`assert`",
                self.cur_span(),
                crate::messages::HINT_ASSERT_IN_EVENT,
            )),
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

    fn verify_decl(&mut self) -> Result<VerifyDecl, ParseError> {
        let start = self.expect(&Token::Verify)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::For)?;

        let mut targets = vec![self.verify_target()?];
        while self.eat(&Token::Comma).is_some() {
            targets.push(self.verify_target()?);
        }

        self.expect(&Token::LBrace)?;
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
                invariants: vec![],
                shows: vec![body_expr],
                by_file,
                span: start.merge(end),
            });
        }

        // Block form: theorem name for System, System2 [invariant ...] { show ... }
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
            match self.peek() {
                Some(Token::Show) => {
                    self.advance();
                    shows.push(self.expr()?);
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
            invariants,
            shows,
            by_file: None,
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
        let (name, _) = self.expect_name()?;
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
            name,
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
            Some(tok) => Err(ParseError::expected_with_help(
                "`given`, `when`, or `then`",
                &format!("`{tok}`"),
                self.cur_span(),
                crate::messages::HINT_SCENE_BODY_STRUCTURE,
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
            // Refinement placeholder: $
            Some(Token::Dollar) => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::Var("$".to_owned()),
                    span: start,
                })
            }
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
            Some(Token::Sorry) => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::Sorry,
                    span: start,
                })
            }
            Some(Token::Todo) => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::Todo,
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
            // Set comprehension: { var: Type where filter } or { expr | var: Type where filter }
            Some(Token::LBrace) => {
                self.advance(); // consume {
                                // Check for simple form: Name : TypeRef where ...
                                // Lookahead: peek(0)=Name, peek(1)=Colon, peek(2)=Name (type start)
                if matches!(self.peek(), Some(Token::Name(_)))
                    && matches!(self.peek_at(1), Some(Token::Colon))
                {
                    // Could be simple set comp or projection form (if the expr before | happens to
                    // start with Name:). Try simple form first: parse var : type where filter.
                    let saved = self.pos;
                    let (var, _) = self.expect_name()?;
                    self.expect(&Token::Colon)?;
                    let domain = self.type_ref()?;
                    if matches!(self.peek(), Some(Token::Where)) {
                        // Simple form confirmed
                        self.advance(); // consume where
                        let filter = self.expr()?;
                        let end = self.expect(&Token::RBrace)?;
                        return Ok(Expr {
                            kind: ExprKind::SetComp {
                                projection: None,
                                var,
                                domain,
                                filter: Box::new(filter),
                            },
                            span: start.merge(end),
                        });
                    }
                    // Not simple form — backtrack and try projection form
                    self.pos = saved;
                }
                // Projection form: expr | var: Type where filter
                // Parse at bp=2 to stop before `|` (which is bp 1)
                let projection = self.expr_bp(2)?;
                self.expect(&Token::Pipe)?;
                let (var, _) = self.expect_name()?;
                self.expect(&Token::Colon)?;
                let domain = self.type_ref()?;
                self.expect(&Token::Where)?;
                let filter = self.expr()?;
                let end = self.expect(&Token::RBrace)?;
                Ok(Expr {
                    kind: ExprKind::SetComp {
                        projection: Some(Box::new(projection)),
                        var,
                        domain,
                        filter: Box::new(filter),
                    },
                    span: start.merge(end),
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
                self.advance(); // consume [
                let first = self.expr()?;
                if self.eat(&Token::ColonEq).is_some() {
                    // Map update: lhs[key := value]
                    let value = self.expr()?;
                    let end = self.expect(&Token::RBracket)?;
                    Ok(Expr {
                        kind: ExprKind::MapUpdate(Box::new(lhs), Box::new(first), Box::new(value)),
                        span: start.merge(end),
                    })
                } else {
                    // Collect remaining comma-separated exprs (if any)
                    let mut refs = vec![first];
                    while self.eat(&Token::Comma).is_some() {
                        refs.push(self.expr()?);
                    }
                    self.expect(&Token::RBracket)?;
                    if matches!(self.peek(), Some(Token::LParen)) {
                        // CallR: lhs[refs](args)
                        self.advance(); // consume (
                        let args = self.comma_sep_expr(&Token::RParen)?;
                        let end = self.expect(&Token::RParen)?;
                        Ok(Expr {
                            kind: ExprKind::CallR(Box::new(lhs), refs, args),
                            span: start.merge(end),
                        })
                    } else if refs.len() == 1 {
                        // Index: lhs[key]
                        let key = refs.into_iter().next().unwrap();
                        let end = self.prev_span();
                        Ok(Expr {
                            kind: ExprKind::Index(Box::new(lhs), Box::new(key)),
                            span: start.merge(end),
                        })
                    } else {
                        Err(ParseError::general(
                            "multiple indices not supported; use map update `[k := v]` or ref call `[refs](args)`",
                            self.cur_span(),
                        ))
                    }
                }
            }
            _ => Err(ParseError::general_with_help(
                "unexpected postfix operator",
                self.cur_span(),
                "valid postfix operators: . (field access), () (call), [] (index/map update), ' (prime)",
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
    fn module_decl() {
        let prog = parse_program("module Commerce");
        assert_eq!(prog.decls.len(), 1);
        if let TopDecl::Module(m) = &prog.decls[0] {
            assert_eq!(m.name, "Commerce");
        } else {
            panic!("expected Module");
        }
    }

    #[test]
    fn include_decl() {
        let prog = parse_program(r#"include "billing.abide""#);
        assert_eq!(prog.decls.len(), 1);
        if let TopDecl::Include(i) = &prog.decls[0] {
            assert_eq!(i.path, "billing.abide");
        } else {
            panic!("expected Include");
        }
    }

    #[test]
    fn pub_type_decl() {
        let prog = parse_program("pub enum OrderStatus = Pending | Paid");
        assert_eq!(prog.decls.len(), 1);
        if let TopDecl::Type(t) = &prog.decls[0] {
            assert_eq!(t.name, "OrderStatus");
            assert_eq!(t.visibility, Visibility::Public);
        } else {
            panic!("expected Type");
        }
    }

    #[test]
    fn pub_entity_decl() {
        let src = r#"pub entity Order {
  id: Id
}"#;
        let prog = parse_program(src);
        assert_eq!(prog.decls.len(), 1);
        if let TopDecl::Entity(e) = &prog.decls[0] {
            assert_eq!(e.name, "Order");
            assert_eq!(e.visibility, Visibility::Public);
        } else {
            panic!("expected Entity");
        }
    }

    #[test]
    fn private_by_default() {
        let prog = parse_program("enum Status = Active | Inactive");
        if let TopDecl::Type(t) = &prog.decls[0] {
            assert_eq!(t.visibility, Visibility::Private);
        } else {
            panic!("expected Type");
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
    fn use_single() {
        let prog = parse_program("use Commerce::Order");
        if let TopDecl::Use(UseDecl::Single { module, name, .. }) = &prog.decls[0] {
            assert_eq!(module, "Commerce");
            assert_eq!(name, "Order");
        } else {
            panic!("expected Use::Single");
        }
    }

    #[test]
    fn use_alias() {
        let prog = parse_program("use Commerce::Order as CO");
        if let TopDecl::Use(UseDecl::Alias {
            module,
            name,
            alias,
            ..
        }) = &prog.decls[0]
        {
            assert_eq!(module, "Commerce");
            assert_eq!(name, "Order");
            assert_eq!(alias, "CO");
        } else {
            panic!("expected Use::Alias");
        }
    }

    #[test]
    fn use_items() {
        let src = "use Billing::{PaymentIntent as PI, open_intent, capture_payment}";
        let prog = parse_program(src);
        if let TopDecl::Use(UseDecl::Items { module, items, .. }) = &prog.decls[0] {
            assert_eq!(module, "Billing");
            assert_eq!(items.len(), 3);
            // First item is an alias
            assert!(
                matches!(&items[0], UseItem::Alias { name, alias, .. } if name == "PaymentIntent" && alias == "PI")
            );
            // Second and third are plain names
            assert!(matches!(&items[1], UseItem::Name { name, .. } if name == "open_intent"));
            assert!(matches!(&items[2], UseItem::Name { name, .. } if name == "capture_payment"));
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
        let prog = parse_program("enum OrderStatus = Pending | AwaitingPayment | Paid");
        if let TopDecl::Type(t) = &prog.decls[0] {
            assert_eq!(t.name, "OrderStatus");
            assert_eq!(t.variants.len(), 3);
        } else {
            panic!("expected Type");
        }
    }

    #[test]
    fn record_type() {
        let prog = parse_program("struct Address { street: String, city: String }");
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
  id: Id
  status: OrderStatus = @Pending

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
  use Order

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
        let src = r#"verify safety_check for Commerce[0..500] {
  assert always true
}"#;
        let prog = parse_program(src);
        if let TopDecl::Verify(v) = &prog.decls[0] {
            assert_eq!(v.name, "safety_check");
            assert_eq!(v.targets.len(), 1);
            assert_eq!(v.targets[0].min, 0);
            assert_eq!(v.targets[0].max, 500);
            assert_eq!(v.asserts.len(), 1);
        } else {
            panic!("expected Verify");
        }
    }

    #[test]
    fn theorem_decl() {
        let src = r#"theorem order_safety for Commerce
  invariant all o: Order | o.total >= 0 {
  show always true
}"#;
        let prog = parse_program(src);
        if let TopDecl::Theorem(t) = &prog.decls[0] {
            assert_eq!(t.name, "order_safety");
            assert_eq!(t.invariants.len(), 1);
            assert_eq!(t.shows.len(), 1);
            assert!(t.by_file.is_none());
        } else {
            panic!("expected Theorem");
        }
    }

    #[test]
    fn theorem_expr_form() {
        let src = r#"theorem no_overdraft = always true"#;
        let prog = parse_program(src);
        if let TopDecl::Theorem(t) = &prog.decls[0] {
            assert_eq!(t.name, "no_overdraft");
            assert_eq!(t.shows.len(), 1);
            assert!(t.by_file.is_none());
        } else {
            panic!("expected Theorem");
        }
    }

    #[test]
    fn theorem_with_by() {
        let src = r#"theorem crypto_safe = always true by "proofs/crypto.agda""#;
        let prog = parse_program(src);
        if let TopDecl::Theorem(t) = &prog.decls[0] {
            assert_eq!(t.name, "crypto_safe");
            assert_eq!(t.by_file, Some("proofs/crypto.agda".to_string()));
        } else {
            panic!("expected Theorem");
        }
    }

    #[test]
    fn axiom_decl() {
        let src = r#"axiom max_accounts = true"#;
        let prog = parse_program(src);
        if let TopDecl::Axiom(a) = &prog.decls[0] {
            assert_eq!(a.name, "max_accounts");
            assert!(a.by_file.is_none());
        } else {
            panic!("expected Axiom");
        }
    }

    #[test]
    fn axiom_with_by() {
        let src = r#"axiom crypto = true by "proofs/crypto.agda""#;
        let prog = parse_program(src);
        if let TopDecl::Axiom(a) = &prog.decls[0] {
            assert_eq!(a.name, "crypto");
            assert_eq!(a.by_file, Some("proofs/crypto.agda".to_string()));
        } else {
            panic!("expected Axiom");
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
        let src = r#"scene payment_test for Commerce {
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
            assert_eq!(s.name, "payment_test");
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
  use PaymentIntent

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

    // ── Generic type reference tests (DDR-023) ─────────────────────────

    #[test]
    fn type_ref_generic_set() {
        let src = "fn ids(s: Set<Int>): Bool = true";
        let prog = parse_program(src);
        if let TopDecl::Fn(f) = &prog.decls[0] {
            match &f.params[0].ty.kind {
                TypeRefKind::Param(name, args) => {
                    assert_eq!(name, "Set");
                    assert_eq!(args.len(), 1);
                    assert!(matches!(args[0].kind, TypeRefKind::Simple(ref s) if s == "Int"));
                }
                other => panic!("expected Param, got {other:?}"),
            }
        } else {
            panic!("expected Fn");
        }
    }

    #[test]
    fn type_ref_generic_map() {
        let src = "fn lookup(m: Map<String, Bool>): Bool = true";
        let prog = parse_program(src);
        if let TopDecl::Fn(f) = &prog.decls[0] {
            match &f.params[0].ty.kind {
                TypeRefKind::Param(name, args) => {
                    assert_eq!(name, "Map");
                    assert_eq!(args.len(), 2);
                    assert!(matches!(args[0].kind, TypeRefKind::Simple(ref s) if s == "String"));
                    assert!(matches!(args[1].kind, TypeRefKind::Simple(ref s) if s == "Bool"));
                }
                other => panic!("expected Param, got {other:?}"),
            }
        } else {
            panic!("expected Fn");
        }
    }

    #[test]
    fn type_ref_nested_generics() {
        let src = "fn nested(s: Set<Set<Int>>): Bool = true";
        let prog = parse_program(src);
        if let TopDecl::Fn(f) = &prog.decls[0] {
            match &f.params[0].ty.kind {
                TypeRefKind::Param(name, args) => {
                    assert_eq!(name, "Set");
                    assert_eq!(args.len(), 1);
                    match &args[0].kind {
                        TypeRefKind::Param(inner_name, inner_args) => {
                            assert_eq!(inner_name, "Set");
                            assert_eq!(inner_args.len(), 1);
                            assert!(
                                matches!(inner_args[0].kind, TypeRefKind::Simple(ref s) if s == "Int")
                            );
                        }
                        other => panic!("expected nested Param, got {other:?}"),
                    }
                }
                other => panic!("expected Param, got {other:?}"),
            }
        } else {
            panic!("expected Fn");
        }
    }

    // ── Mut ref param tests (DDR-016) ───────────────────────────────────

    #[test]
    fn action_mut_ref_param() {
        let src = r#"entity Account {
  balance: Int

  action transfer[mut to: Account](amount: Int)
    requires balance >= amount {
    balance' = balance - amount
  }
}"#;
        let prog = parse_program(src);
        if let TopDecl::Entity(e) = &prog.decls[0] {
            if let EntityItem::Action(a) = &e.items[1] {
                assert_eq!(a.name, "transfer");
                assert_eq!(a.ref_params.len(), 1);
                assert_eq!(a.ref_params[0].name, "to");
                assert_eq!(a.ref_params[0].ty, "Account");
                assert!(a.ref_params[0].mutable);
                assert_eq!(a.params.len(), 1);
                assert_eq!(a.params[0].name, "amount");
                assert!(!a.params[0].mutable);
            } else {
                panic!("expected Action");
            }
        } else {
            panic!("expected Entity");
        }
    }

    #[test]
    fn action_non_mut_ref_param() {
        let src = r#"entity Account {
  balance: Int

  action check[other: Account]() requires true {
    balance' = balance
  }
}"#;
        let prog = parse_program(src);
        if let TopDecl::Entity(e) = &prog.decls[0] {
            if let EntityItem::Action(a) = &e.items[1] {
                assert_eq!(a.ref_params.len(), 1);
                assert!(!a.ref_params[0].mutable);
            } else {
                panic!("expected Action");
            }
        } else {
            panic!("expected Entity");
        }
    }

    #[test]
    fn field_type_generic_collection() {
        let src = r#"entity Warehouse {
  items: Set<Id>
  prices: Map<Id, Int>
}"#;
        let prog = parse_program(src);
        if let TopDecl::Entity(e) = &prog.decls[0] {
            if let EntityItem::Field(f) = &e.items[0] {
                assert_eq!(f.name, "items");
                match &f.ty.kind {
                    TypeRefKind::Param(name, args) => {
                        assert_eq!(name, "Set");
                        assert_eq!(args.len(), 1);
                    }
                    other => panic!("expected Param, got {other:?}"),
                }
            } else {
                panic!("expected Field");
            }
            if let EntityItem::Field(f) = &e.items[1] {
                assert_eq!(f.name, "prices");
                match &f.ty.kind {
                    TypeRefKind::Param(name, args) => {
                        assert_eq!(name, "Map");
                        assert_eq!(args.len(), 2);
                    }
                    other => panic!("expected Param, got {other:?}"),
                }
            } else {
                panic!("expected Field");
            }
        } else {
            panic!("expected Entity");
        }
    }

    // ── Map update and index tests (DDR-034) ────────────────────────────

    #[test]
    fn map_update() {
        let e = parse_expr("m[k := v]");
        match &e.kind {
            ExprKind::MapUpdate(m, k, v) => {
                assert!(matches!(m.kind, ExprKind::Var(ref s) if s == "m"));
                assert!(matches!(k.kind, ExprKind::Var(ref s) if s == "k"));
                assert!(matches!(v.kind, ExprKind::Var(ref s) if s == "v"));
            }
            other => panic!("expected MapUpdate, got {other:?}"),
        }
    }

    #[test]
    fn map_index() {
        let e = parse_expr("m[k]");
        match &e.kind {
            ExprKind::Index(m, k) => {
                assert!(matches!(m.kind, ExprKind::Var(ref s) if s == "m"));
                assert!(matches!(k.kind, ExprKind::Var(ref s) if s == "k"));
            }
            other => panic!("expected Index, got {other:?}"),
        }
    }

    #[test]
    fn map_update_chained() {
        let e = parse_expr("m[a := x][b := y]");
        match &e.kind {
            ExprKind::MapUpdate(inner, b, y) => {
                assert!(matches!(b.kind, ExprKind::Var(ref s) if s == "b"));
                assert!(matches!(y.kind, ExprKind::Var(ref s) if s == "y"));
                match &inner.kind {
                    ExprKind::MapUpdate(m, a, x) => {
                        assert!(matches!(m.kind, ExprKind::Var(ref s) if s == "m"));
                        assert!(matches!(a.kind, ExprKind::Var(ref s) if s == "a"));
                        assert!(matches!(x.kind, ExprKind::Var(ref s) if s == "x"));
                    }
                    other => panic!("expected inner MapUpdate, got {other:?}"),
                }
            }
            other => panic!("expected MapUpdate, got {other:?}"),
        }
    }

    // ── Set comprehension tests (DDR-035) ───────────────────────────────

    #[test]
    fn set_comp_simple() {
        let e = parse_expr("{ a: Account where a.status == @Frozen }");
        match &e.kind {
            ExprKind::SetComp {
                projection,
                var,
                domain,
                filter,
            } => {
                assert!(projection.is_none());
                assert_eq!(var, "a");
                assert!(matches!(&domain.kind, TypeRefKind::Simple(ref n) if n == "Account"));
                assert!(matches!(filter.kind, ExprKind::Eq(_, _)));
            }
            other => panic!("expected SetComp, got {other:?}"),
        }
    }

    #[test]
    fn set_comp_projection() {
        let e = parse_expr("{ a.balance | a: Account where a.balance > 0 }");
        match &e.kind {
            ExprKind::SetComp {
                projection,
                var,
                domain,
                filter,
            } => {
                assert!(projection.is_some());
                let proj = projection.as_ref().unwrap();
                assert!(matches!(&proj.kind, ExprKind::Field(_, ref f) if f == "balance"));
                assert_eq!(var, "a");
                assert!(matches!(&domain.kind, TypeRefKind::Simple(ref n) if n == "Account"));
                assert!(matches!(filter.kind, ExprKind::Gt(_, _)));
            }
            other => panic!("expected SetComp, got {other:?}"),
        }
    }

    #[test]
    fn set_comp_cardinality() {
        let e = parse_expr("#{ a: Account where a.balance > 0 }");
        match &e.kind {
            ExprKind::Card(inner) => {
                assert!(matches!(
                    &inner.kind,
                    ExprKind::SetComp {
                        projection: None,
                        ..
                    }
                ));
            }
            other => panic!("expected Card(SetComp), got {other:?}"),
        }
    }

    // ── Collection literal recognition (DDR-017) ────────────────────────

    #[test]
    fn collection_literal_set() {
        let e = parse_expr("Set(1, 2, 3)");
        match &e.kind {
            ExprKind::Call(callee, args) => {
                assert!(matches!(&callee.kind, ExprKind::Var(ref s) if s == "Set"));
                assert_eq!(args.len(), 3);
                assert!(matches!(args[0].kind, ExprKind::Int(1)));
                assert!(matches!(args[1].kind, ExprKind::Int(2)));
                assert!(matches!(args[2].kind, ExprKind::Int(3)));
            }
            other => panic!("expected Call(Var(Set), [1,2,3]), got {other:?}"),
        }
    }

    // ── Removed keyword detection tests ──────────────────────────

    fn try_parse(src: &str) -> Result<Program, ParseError> {
        let tokens = lex::lex(src).expect("lex error");
        let mut parser = Parser::new(tokens);
        parser.parse_program()
    }

    #[test]
    fn removed_field_keyword_in_entity() {
        let err = try_parse("entity Order { field status: Int }").unwrap_err();
        let msg = format!("{err}");
        assert!(msg.contains("field"), "should mention 'field': {msg}");
    }

    #[test]
    fn removed_import_keyword() {
        let err = try_parse(r#"import "billing.abide" as Billing"#).unwrap_err();
        let msg = format!("{err}");
        assert!(msg.contains("import"), "should mention 'import': {msg}");
    }

    #[test]
    fn removed_proof_keyword() {
        let err = try_parse("proof safety for S { show always true }").unwrap_err();
        let msg = format!("{err}");
        assert!(msg.contains("proof"), "should mention 'proof': {msg}");
    }

    #[test]
    fn removed_uses_keyword() {
        let err = try_parse("system S { uses Order }").unwrap_err();
        let msg = format!("{err}");
        assert!(msg.contains("uses"), "should mention 'uses': {msg}");
    }

    // ── Recovery and multi-error tests ──────────────────────────

    fn try_parse_recovering(src: &str) -> (Program, Vec<ParseError>) {
        let tokens = lex::lex(src).expect("lex error");
        let mut parser = Parser::new(tokens);
        parser.parse_program_recovering()
    }

    #[test]
    fn recovery_reports_multiple_errors() {
        let src = "import x\ntype Status = A | B\nimport y\nentity Order { id: Id }";
        let (program, errors) = try_parse_recovering(src);
        // Two import errors, but type and entity should parse successfully
        assert_eq!(errors.len(), 2, "should have 2 errors: {errors:?}");
        assert_eq!(program.decls.len(), 2, "should have 2 valid decls");
    }

    #[test]
    fn recovery_does_not_skip_valid_starter() {
        let src = "import x\nenum Status = A | B";
        let (program, errors) = try_parse_recovering(src);
        assert_eq!(errors.len(), 1, "one import error");
        assert_eq!(program.decls.len(), 1, "enum should be recovered");
    }

    /// Extract the help text from a ParseError, if present.
    fn extract_help(err: &ParseError) -> Option<&str> {
        match err {
            ParseError::Expected { help, .. } => help.as_deref(),
            ParseError::General { help, .. } => help.as_deref(),
            ParseError::UnexpectedEof { .. } => None,
        }
    }

    #[test]
    fn import_help_text_content() {
        let err = try_parse(r#"import "billing.abide" as Billing"#).unwrap_err();
        let help = extract_help(&err).expect("should have help");
        assert!(
            help.contains("module"),
            "help should mention 'module': {help}"
        );
        assert!(
            help.contains("include"),
            "help should mention 'include': {help}"
        );
    }

    #[test]
    fn field_help_text_content() {
        let err = try_parse("entity Order { field status: Int }").unwrap_err();
        let help = extract_help(&err).expect("should have help");
        assert!(
            help.contains("name: Type"),
            "help should show bare field syntax: {help}"
        );
    }

    #[test]
    fn verify_body_contextual_help() {
        let err = try_parse("verify test for S[0..5] { show always true }").unwrap_err();
        let msg = format!("{err}");
        assert!(
            msg.contains("assert"),
            "should expect 'assert' in verify body: {msg}"
        );
        let help = extract_help(&err).expect("should have help");
        assert!(
            help.contains("assert"),
            "help should mention assert statements: {help}"
        );
    }

    #[test]
    fn theorem_assert_instead_of_show() {
        let err = try_parse("theorem t for S { assert always true }").unwrap_err();
        let msg = format!("{err}");
        assert!(
            msg.contains("show"),
            "should suggest 'show' instead of 'assert': {msg}"
        );
        let help = extract_help(&err).expect("should have help");
        assert!(help.contains("show"), "help should mention 'show': {help}");
    }

    #[test]
    fn scene_body_contextual_help() {
        let err = try_parse("scene s for S { verify true }").unwrap_err();
        let msg = format!("{err}");
        assert!(
            msg.contains("given") || msg.contains("when") || msg.contains("then"),
            "should mention scene sections: {msg}"
        );
        let help = extract_help(&err).expect("should have help");
        assert!(
            help.contains("given"),
            "help should mention 'given': {help}"
        );
    }

    #[test]
    fn event_body_assert_instead_of_requires() {
        let err = try_parse("system S { event e() { assert true } }").unwrap_err();
        let help = extract_help(&err).expect("should have help");
        assert!(
            help.contains("requires"),
            "help should suggest 'requires': {help}"
        );
    }

    // ── DDR-043: enum / struct / type alias tests ───────────────────

    #[test]
    fn enum_simple() {
        let prog = parse_program("enum Status = Active | Inactive | Suspended");
        assert_eq!(prog.decls.len(), 1);
        if let TopDecl::Type(t) = &prog.decls[0] {
            assert_eq!(t.name, "Status");
            assert_eq!(t.variants.len(), 3);
            assert!(matches!(&t.variants[0], TypeVariant::Simple { name, .. } if name == "Active"));
            assert!(
                matches!(&t.variants[1], TypeVariant::Simple { name, .. } if name == "Inactive")
            );
            assert!(
                matches!(&t.variants[2], TypeVariant::Simple { name, .. } if name == "Suspended")
            );
        } else {
            panic!("expected Type from enum");
        }
    }

    #[test]
    fn enum_adt_with_record_variants() {
        let src = "enum Shape = Circle { radius: Real } | Rectangle { width: Real, height: Real }";
        let prog = parse_program(src);
        assert_eq!(prog.decls.len(), 1);
        if let TopDecl::Type(t) = &prog.decls[0] {
            assert_eq!(t.name, "Shape");
            assert_eq!(t.variants.len(), 2);
            assert!(
                matches!(&t.variants[0], TypeVariant::Record { name, fields, .. } if name == "Circle" && fields.len() == 1)
            );
            assert!(
                matches!(&t.variants[1], TypeVariant::Record { name, fields, .. } if name == "Rectangle" && fields.len() == 2)
            );
        } else {
            panic!("expected Type from enum");
        }
    }

    #[test]
    fn struct_decl_test() {
        let src = "struct Address { street: String, city: String, zip: String }";
        let prog = parse_program(src);
        assert_eq!(prog.decls.len(), 1);
        if let TopDecl::Record(r) = &prog.decls[0] {
            assert_eq!(r.name, "Address");
            assert_eq!(r.fields.len(), 3);
            assert_eq!(r.fields[0].name, "street");
            assert_eq!(r.fields[1].name, "city");
            assert_eq!(r.fields[2].name, "zip");
        } else {
            panic!("expected Record from struct");
        }
    }

    #[test]
    fn type_alias_to_tuple() {
        let prog = parse_program("type Coord = (Real, Real)");
        assert_eq!(prog.decls.len(), 1);
        if let TopDecl::Alias(a) = &prog.decls[0] {
            assert_eq!(a.name, "Coord");
            assert!(matches!(&a.target.kind, TypeRefKind::Tuple(ts) if ts.len() == 2));
        } else {
            panic!("expected Alias, got {:?}", prog.decls[0]);
        }
    }

    #[test]
    fn type_alias_to_collection() {
        let prog = parse_program("type Ids = Set<Id>");
        assert_eq!(prog.decls.len(), 1);
        if let TopDecl::Alias(a) = &prog.decls[0] {
            assert_eq!(a.name, "Ids");
            assert!(
                matches!(&a.target.kind, TypeRefKind::Param(name, ts) if name == "Set" && ts.len() == 1)
            );
        } else {
            panic!("expected Alias, got {:?}", prog.decls[0]);
        }
    }

    #[test]
    fn type_alias_to_builtin() {
        let prog = parse_program("type Amount = Real");
        assert_eq!(prog.decls.len(), 1);
        if let TopDecl::Alias(a) = &prog.decls[0] {
            assert_eq!(a.name, "Amount");
            assert!(matches!(&a.target.kind, TypeRefKind::Simple(name) if name == "Real"));
        } else {
            panic!("expected Alias, got {:?}", prog.decls[0]);
        }
    }

    #[test]
    fn pub_enum_struct_type() {
        let src = r#"pub enum Color = Red | Green | Blue
pub struct Point { x: Real, y: Real }
pub type Distance = Real"#;
        let prog = parse_program(src);
        assert_eq!(prog.decls.len(), 3);
        if let TopDecl::Type(t) = &prog.decls[0] {
            assert_eq!(t.name, "Color");
            assert_eq!(t.visibility, Visibility::Public);
            assert_eq!(t.variants.len(), 3);
        } else {
            panic!("expected pub Type from enum");
        }
        if let TopDecl::Record(r) = &prog.decls[1] {
            assert_eq!(r.name, "Point");
            assert_eq!(r.visibility, Visibility::Public);
            assert_eq!(r.fields.len(), 2);
        } else {
            panic!("expected pub Record from struct");
        }
        if let TopDecl::Alias(a) = &prog.decls[2] {
            assert_eq!(a.name, "Distance");
            assert_eq!(a.visibility, Visibility::Public);
        } else {
            panic!("expected pub Alias from type");
        }
    }

    #[test]
    fn type_does_not_produce_enum() {
        // `type` with pipe-separated variants: type_ref() parses `Pending`
        // as a simple alias, leaving `| Paid` as trailing junk.
        let tokens = lex::lex("type OrderStatus = Pending | Paid").expect("lex");
        let mut parser = Parser::new(tokens);
        let (prog, errors) = parser.parse_program_recovering();
        // Should either error or produce an alias (not a multi-variant enum)
        let has_multi_variant = prog
            .decls
            .iter()
            .any(|d| matches!(d, TopDecl::Type(t) if t.variants.len() > 1));
        assert!(
            !has_multi_variant,
            "type with | should not produce multi-variant enum — use enum"
        );
        // The trailing `| Paid` should produce a parse error
        assert!(
            !errors.is_empty() || prog.decls.len() != 1,
            "type with | should produce errors or unexpected decls"
        );
    }

    #[test]
    fn type_does_not_produce_record() {
        // `type Name { fields }` is not valid — use `struct`
        let tokens = lex::lex("type Address { street: String }").expect("lex");
        let mut parser = Parser::new(tokens);
        let result = parser.parse_program();
        assert!(
            result.is_err(),
            "type with {{ fields }} should be rejected — use struct"
        );
    }

    #[test]
    fn type_alias_to_map() {
        let prog = parse_program("type Ledger = Map<Id, Real>");
        assert_eq!(prog.decls.len(), 1);
        if let TopDecl::Alias(a) = &prog.decls[0] {
            assert_eq!(a.name, "Ledger");
            if let TypeRefKind::Param(name, ts) = &a.target.kind {
                assert_eq!(name, "Map");
                assert_eq!(ts.len(), 2);
            } else {
                panic!("expected Param type ref");
            }
        } else {
            panic!("expected Alias, got {:?}", prog.decls[0]);
        }
    }

    #[test]
    fn type_alias_triple_tuple() {
        let prog = parse_program("type RGB = (Int, Int, Int)");
        assert_eq!(prog.decls.len(), 1);
        if let TopDecl::Alias(a) = &prog.decls[0] {
            assert_eq!(a.name, "RGB");
            if let TypeRefKind::Tuple(ts) = &a.target.kind {
                assert_eq!(ts.len(), 3);
            } else {
                panic!("expected Tuple type ref");
            }
        } else {
            panic!("expected Alias, got {:?}", prog.decls[0]);
        }
    }

    #[test]
    fn type_alias_function_type() {
        let prog = parse_program("type Handler = Int -> Bool");
        assert_eq!(prog.decls.len(), 1);
        if let TopDecl::Alias(a) = &prog.decls[0] {
            assert_eq!(a.name, "Handler");
            assert!(
                matches!(a.target.kind, TypeRefKind::Fn(_, _)),
                "expected function type, got {:?}",
                a.target.kind
            );
        } else {
            panic!("expected Alias, got {:?}", prog.decls[0]);
        }
    }

    #[test]
    fn type_single_name_is_alias() {
        // type Status = Pending → alias (no backward compat for enums)
        // Use `enum Status = Pending` for single-variant enums.
        let prog = parse_program("type Status = Pending");
        match &prog.decls[0] {
            TopDecl::Alias(a) => {
                assert_eq!(a.name, "Status");
                assert!(
                    matches!(a.target.kind, TypeRefKind::Simple(ref n) if n == "Pending"),
                    "expected alias to Pending, got {:?}",
                    a.target.kind
                );
            }
            other => panic!("expected Alias, got {other:?}"),
        }
    }

    #[test]
    fn enum_rejects_brace_syntax() {
        let tokens = lex::lex("enum Point { x: Int }").expect("lex");
        let mut parser = Parser::new(tokens);
        let result = parser.parse_program();
        assert!(result.is_err(), "enum with {{ fields }} should be rejected");
    }

    #[test]
    fn struct_rejects_eq_syntax() {
        let tokens = lex::lex("struct Status = A | B").expect("lex");
        let mut parser = Parser::new(tokens);
        let result = parser.parse_program();
        assert!(result.is_err(), "struct with = should be rejected");
    }

    #[test]
    fn type_alias_uppercase_function_type() {
        // type Predicate = User -> Bool — User is uppercase non-builtin
        // but -> makes it a function type, so it must be an alias, not enum.
        let prog = parse_program("type Predicate = User -> Bool");
        match &prog.decls[0] {
            TopDecl::Alias(a) => {
                assert_eq!(a.name, "Predicate");
                assert!(
                    matches!(a.target.kind, TypeRefKind::Fn(_, _)),
                    "expected function type, got {:?}",
                    a.target.kind
                );
            }
            other => panic!("expected Alias, got {other:?}"),
        }
    }

    // ── fn contract tests ─────────────────────────────────────────────

    #[test]
    fn fn_no_contracts() {
        let prog = parse_program("fn double(x: Int): Int = x + x");
        match &prog.decls[0] {
            TopDecl::Fn(f) => {
                assert_eq!(f.name, "double");
                assert!(f.contracts.is_empty());
            }
            other => panic!("expected Fn, got {other:?}"),
        }
    }

    #[test]
    fn fn_with_requires() {
        let prog =
            parse_program("fn gcd(a: Int, b: Int): Int requires a > 0 requires b >= 0 { a }");
        match &prog.decls[0] {
            TopDecl::Fn(f) => {
                assert_eq!(f.name, "gcd");
                assert_eq!(f.contracts.len(), 2);
                assert!(matches!(f.contracts[0], Contract::Requires { .. }));
                assert!(matches!(f.contracts[1], Contract::Requires { .. }));
            }
            other => panic!("expected Fn, got {other:?}"),
        }
    }

    #[test]
    fn fn_with_ensures() {
        let prog = parse_program("fn abs(x: Int): Int ensures result >= 0 { x }");
        match &prog.decls[0] {
            TopDecl::Fn(f) => {
                assert_eq!(f.name, "abs");
                assert_eq!(f.contracts.len(), 1);
                assert!(matches!(f.contracts[0], Contract::Ensures { .. }));
            }
            other => panic!("expected Fn, got {other:?}"),
        }
    }

    #[test]
    fn fn_with_decreases_single() {
        let prog = parse_program("fn countdown(n: Int): Int decreases n { n }");
        match &prog.decls[0] {
            TopDecl::Fn(f) => {
                assert_eq!(f.contracts.len(), 1);
                match &f.contracts[0] {
                    Contract::Decreases { measures, star, .. } => {
                        assert_eq!(measures.len(), 1);
                        assert!(!star);
                    }
                    other => panic!("expected Decreases, got {other:?}"),
                }
            }
            other => panic!("expected Fn, got {other:?}"),
        }
    }

    #[test]
    fn fn_with_decreases_lexicographic() {
        let prog = parse_program("fn ack(m: Int, n: Int): Int decreases m, n { m }");
        match &prog.decls[0] {
            TopDecl::Fn(f) => {
                assert_eq!(f.contracts.len(), 1);
                match &f.contracts[0] {
                    Contract::Decreases { measures, star, .. } => {
                        assert_eq!(measures.len(), 2);
                        assert!(!star);
                    }
                    other => panic!("expected Decreases, got {other:?}"),
                }
            }
            other => panic!("expected Fn, got {other:?}"),
        }
    }

    #[test]
    fn fn_with_decreases_star() {
        let prog = parse_program("fn f(n: Int): Int decreases * { n }");
        match &prog.decls[0] {
            TopDecl::Fn(f) => {
                assert_eq!(f.contracts.len(), 1);
                match &f.contracts[0] {
                    Contract::Decreases { measures, star, .. } => {
                        assert!(measures.is_empty());
                        assert!(star);
                    }
                    other => panic!("expected Decreases, got {other:?}"),
                }
            }
            other => panic!("expected Fn, got {other:?}"),
        }
    }

    #[test]
    fn fn_with_all_contracts() {
        let prog = parse_program(
            "fn gcd(a: Int, b: Int): Int requires a > 0 ensures result > 0 decreases b { a }",
        );
        match &prog.decls[0] {
            TopDecl::Fn(f) => {
                assert_eq!(f.contracts.len(), 3);
                assert!(matches!(f.contracts[0], Contract::Requires { .. }));
                assert!(matches!(f.contracts[1], Contract::Ensures { .. }));
                assert!(matches!(f.contracts[2], Contract::Decreases { .. }));
            }
            other => panic!("expected Fn, got {other:?}"),
        }
    }

    #[test]
    fn fn_pure_form_no_contracts() {
        // Pure form with = body should still work
        let prog = parse_program("fn id(x: Int): Int = x");
        match &prog.decls[0] {
            TopDecl::Fn(f) => {
                assert_eq!(f.name, "id");
                assert!(f.contracts.is_empty());
            }
            other => panic!("expected Fn, got {other:?}"),
        }
    }

    // ── Imperative fn body tests ────────────────────────────────────

    #[test]
    fn fn_with_var_decl() {
        let prog = parse_program("fn f(x: Int): Int { var y = x + 1\ny }");
        match &prog.decls[0] {
            TopDecl::Fn(f) => {
                assert_eq!(f.name, "f");
                match &f.body.kind {
                    ExprKind::Block(items) => {
                        assert_eq!(items.len(), 2);
                        assert!(matches!(items[0].kind, ExprKind::VarDecl { .. }));
                        assert!(matches!(items[1].kind, ExprKind::Var(_)));
                    }
                    other => panic!("expected Block, got {other:?}"),
                }
            }
            other => panic!("expected Fn, got {other:?}"),
        }
    }

    #[test]
    fn fn_with_while_loop() {
        let prog = parse_program("fn f(x: Int): Int { while x > 0 { x } }");
        match &prog.decls[0] {
            TopDecl::Fn(f) => {
                // Single-item block with a while unwraps directly
                match &f.body.kind {
                    ExprKind::While { cond, body, .. } => {
                        assert!(matches!(cond.kind, ExprKind::Gt(_, _)));
                        assert!(matches!(body.kind, ExprKind::Var(_)));
                    }
                    other => panic!("expected While, got {other:?}"),
                }
            }
            other => panic!("expected Fn, got {other:?}"),
        }
    }

    #[test]
    fn fn_with_while_invariant_decreases() {
        let prog =
            parse_program("fn f(x: Int): Int { while x > 0 invariant x >= 0 decreases x { x } }");
        match &prog.decls[0] {
            TopDecl::Fn(f) => match &f.body.kind {
                ExprKind::While {
                    contracts, cond, ..
                } => {
                    assert!(matches!(cond.kind, ExprKind::Gt(_, _)));
                    assert_eq!(contracts.len(), 2);
                    assert!(matches!(contracts[0], Contract::Invariant { .. }));
                    assert!(matches!(contracts[1], Contract::Decreases { .. }));
                }
                other => panic!("expected While, got {other:?}"),
            },
            other => panic!("expected Fn, got {other:?}"),
        }
    }

    #[test]
    fn fn_with_if_else() {
        let prog = parse_program("fn f(x: Int): Int { if x > 0 { x } else { 0 } }");
        match &prog.decls[0] {
            TopDecl::Fn(f) => match &f.body.kind {
                ExprKind::IfElse {
                    cond,
                    then_body,
                    else_body,
                } => {
                    assert!(matches!(cond.kind, ExprKind::Gt(_, _)));
                    assert!(matches!(then_body.kind, ExprKind::Var(_)));
                    assert!(else_body.is_some());
                    assert!(matches!(else_body.as_ref().unwrap().kind, ExprKind::Int(0)));
                }
                other => panic!("expected IfElse, got {other:?}"),
            },
            other => panic!("expected Fn, got {other:?}"),
        }
    }

    #[test]
    fn fn_with_if_no_else() {
        let prog = parse_program("fn f(x: Int): Int { if x > 0 { x } }");
        match &prog.decls[0] {
            TopDecl::Fn(f) => match &f.body.kind {
                ExprKind::IfElse { else_body, .. } => {
                    assert!(else_body.is_none());
                }
                other => panic!("expected IfElse, got {other:?}"),
            },
            other => panic!("expected Fn, got {other:?}"),
        }
    }

    #[test]
    fn fn_with_multiple_statements() {
        let prog = parse_program("fn f(x: Int): Int {\n  var a = 1\n  var b = 2\n  a + b\n}");
        match &prog.decls[0] {
            TopDecl::Fn(f) => match &f.body.kind {
                ExprKind::Block(items) => {
                    assert_eq!(items.len(), 3);
                    assert!(matches!(items[0].kind, ExprKind::VarDecl { .. }));
                    assert!(matches!(items[1].kind, ExprKind::VarDecl { .. }));
                    assert!(matches!(items[2].kind, ExprKind::Add(_, _)));
                }
                other => panic!("expected Block, got {other:?}"),
            },
            other => panic!("expected Fn, got {other:?}"),
        }
    }

    #[test]
    fn fn_with_var_typed() {
        let prog = parse_program("fn f(x: Int): Int { var y: Int = 0\ny }");
        match &prog.decls[0] {
            TopDecl::Fn(f) => match &f.body.kind {
                ExprKind::Block(items) => {
                    assert_eq!(items.len(), 2);
                    match &items[0].kind {
                        ExprKind::VarDecl { name, ty, .. } => {
                            assert_eq!(name, "y");
                            assert!(ty.is_some());
                        }
                        other => panic!("expected VarDecl, got {other:?}"),
                    }
                }
                other => panic!("expected Block, got {other:?}"),
            },
            other => panic!("expected Fn, got {other:?}"),
        }
    }

    #[test]
    fn fn_with_else_if_chain() {
        let prog =
            parse_program("fn f(x: Int): Int { if x > 0 { 1 } else if x == 0 { 0 } else { 2 } }");
        match &prog.decls[0] {
            TopDecl::Fn(f) => {
                match &f.body.kind {
                    ExprKind::IfElse { else_body, .. } => {
                        // The else branch is another IfElse
                        let eb = else_body.as_ref().unwrap();
                        assert!(matches!(eb.kind, ExprKind::IfElse { .. }));
                    }
                    other => panic!("expected IfElse, got {other:?}"),
                }
            }
            other => panic!("expected Fn, got {other:?}"),
        }
    }

    #[test]
    fn fn_single_expr_body_unwraps() {
        // A block with a single non-VarDecl expression should unwrap
        let prog = parse_program("fn f(x: Int): Int { x + 1 }");
        match &prog.decls[0] {
            TopDecl::Fn(f) => {
                assert!(
                    matches!(f.body.kind, ExprKind::Add(_, _)),
                    "single-expr block should unwrap, got {:?}",
                    f.body.kind
                );
            }
            other => panic!("expected Fn, got {other:?}"),
        }
    }

    // ── Refinement type tests ───────────────────────────────────────

    #[test]
    fn refinement_type_alias() {
        let prog = parse_program("type Positive = Int { $ > 0 }");
        match &prog.decls[0] {
            TopDecl::Alias(a) => match &a.target.kind {
                TypeRefKind::Refine(base, pred) => {
                    assert!(matches!(base.kind, TypeRefKind::Simple(ref n) if n == "Int"));
                    assert!(matches!(pred.kind, ExprKind::Gt(_, _)));
                }
                other => panic!("expected Refine, got {other:?}"),
            },
            other => panic!("expected Alias, got {other:?}"),
        }
    }

    #[test]
    fn refinement_param_type() {
        let prog = parse_program("fn f(x: Int{ $ > 0 }): Int = x");
        match &prog.decls[0] {
            TopDecl::Fn(f) => {
                assert!(matches!(f.params[0].ty.kind, TypeRefKind::Refine(_, _)));
            }
            other => panic!("expected Fn, got {other:?}"),
        }
    }

    #[test]
    fn refinement_left_to_right() {
        let prog = parse_program("fn clamp(lo: Int, hi: Int{ $ > lo }): Int = hi");
        match &prog.decls[0] {
            TopDecl::Fn(f) => {
                assert_eq!(f.params.len(), 2);
                assert!(matches!(f.params[0].ty.kind, TypeRefKind::Simple(_)));
                assert!(matches!(f.params[1].ty.kind, TypeRefKind::Refine(_, _)));
            }
            other => panic!("expected Fn, got {other:?}"),
        }
    }

    #[test]
    fn refinement_dollar_in_expr() {
        let prog = parse_program("type Byte = Int { $ >= 0 and $ <= 255 }");
        match &prog.decls[0] {
            TopDecl::Alias(a) => {
                assert!(matches!(a.target.kind, TypeRefKind::Refine(_, _)));
            }
            other => panic!("expected Alias, got {other:?}"),
        }
    }

    #[test]
    fn fn_body_not_confused_with_refinement() {
        // fn without contracts + { body } must parse as fn body, not refinement
        let prog = parse_program("fn sign(x: Int): Int { if x > 0 { 1 } else { 0 } }");
        match &prog.decls[0] {
            TopDecl::Fn(f) => {
                assert!(matches!(f.ret_type.kind, TypeRefKind::Simple(ref n) if n == "Int"));
                assert!(matches!(f.body.kind, ExprKind::IfElse { .. }));
            }
            other => panic!("expected Fn, got {other:?}"),
        }
    }

    #[test]
    fn refinement_param_name() {
        let prog = parse_program("fn g(x: Int{ x > 0 }, y: Int{ y > x }): Int = y");
        match &prog.decls[0] {
            TopDecl::Fn(f) => {
                assert_eq!(f.params.len(), 2);
                assert!(matches!(f.params[0].ty.kind, TypeRefKind::Refine(_, _)));
                assert!(matches!(f.params[1].ty.kind, TypeRefKind::Refine(_, _)));
            }
            other => panic!("expected Fn, got {other:?}"),
        }
    }
}
