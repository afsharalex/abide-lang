//! Expression parsing — Pratt parser for all expression forms.

use super::{
    infix_bp, postfix_bp, Parser, BP_CHOICE, BP_NAMED_PAIR, BP_NAMED_PAIR_RHS, BP_NOT, BP_NOT_RHS,
    BP_PREFIX_EXPR, BP_UNARY, BP_UNARY_RHS,
};
use crate::ast::{
    AggKind, Expr, ExprKind, FieldPat, LetBind, MatchArm, Pattern, RelCompBinding, SawArg,
};
use crate::diagnostic::ParseError;
use crate::lex::Token;
use crate::span::Span;

fn make_infix(lhs: Expr, op: &Token, rhs: Expr, span: Span) -> Expr {
    let kind = match op {
        Token::PipeGt => ExprKind::Pipe(Box::new(lhs), Box::new(rhs)),
        Token::Pipe => ExprKind::Unord(Box::new(lhs), Box::new(rhs)),
        Token::PipePipe => ExprKind::Conc(Box::new(lhs), Box::new(rhs)),
        Token::CaretPipe => ExprKind::Xor(Box::new(lhs), Box::new(rhs)),
        Token::Arrow => ExprKind::Seq(Box::new(lhs), Box::new(rhs)),
        Token::Amp => ExprKind::SameStep(Box::new(lhs), Box::new(rhs)),
        Token::Implies => ExprKind::Impl(Box::new(lhs), Box::new(rhs)),
        Token::Until => ExprKind::Until(Box::new(lhs), Box::new(rhs)),
        Token::Since => ExprKind::Since(Box::new(lhs), Box::new(rhs)),
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
        Token::Diamond => ExprKind::Diamond(Box::new(lhs), Box::new(rhs)),
        Token::BangStar => ExprKind::Disjoint(Box::new(lhs), Box::new(rhs)),
        _ => unreachable!("not an infix operator: {op}"),
    };
    Expr { kind, span }
}

impl Parser {
    // ── Expressions (Pratt parser) ───────────────────────────────────

    pub(super) fn expr(&mut self) -> Result<Expr, ParseError> {
        self.expr_bp(0)
    }

    pub(super) fn expr_bp(&mut self, min_bp: u8) -> Result<Expr, ParseError> {
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
                && BP_NAMED_PAIR >= min_bp
            {
                if let ExprKind::Var(name) = &lhs.kind {
                    let name = name.clone();
                    self.advance(); // consume :
                    let rhs = self.expr_bp(BP_NAMED_PAIR_RHS)?;
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
            // Unary negation: -x
            Some(Token::Minus) if min_bp <= BP_UNARY => {
                self.advance();
                let operand = self.expr_bp(BP_UNARY_RHS)?;
                Ok(Expr {
                    kind: ExprKind::Neg(Box::new(operand)),
                    span: start.merge(self.prev_span()),
                })
            }
            // Cardinality: #s
            Some(Token::Hash) if min_bp <= BP_UNARY => {
                self.advance();
                let operand = self.expr_bp(BP_UNARY_RHS)?;
                Ok(Expr {
                    kind: ExprKind::Card(Box::new(operand)),
                    span: start.merge(self.prev_span()),
                })
            }
            // Logical not
            Some(Token::Not) if min_bp <= BP_NOT => {
                self.advance();
                let operand = self.expr_bp(BP_NOT_RHS)?;
                Ok(Expr {
                    kind: ExprKind::Not(Box::new(operand)),
                    span: start.merge(self.prev_span()),
                })
            }
            // Temporal/quantifier/let/lambda/match prefix forms
            Some(Token::Always) if min_bp <= BP_PREFIX_EXPR => {
                self.advance();
                let body = self.expr_bp(BP_PREFIX_EXPR)?;
                Ok(Expr {
                    kind: ExprKind::Always(Box::new(body)),
                    span: start.merge(self.prev_span()),
                })
            }
            Some(Token::Eventually) if min_bp <= BP_PREFIX_EXPR => {
                self.advance();
                let body = self.expr_bp(BP_PREFIX_EXPR)?;
                Ok(Expr {
                    kind: ExprKind::Eventually(Box::new(body)),
                    span: start.merge(self.prev_span()),
                })
            }
            // / — past-time temporal operators.
            // Same prefix binding power as `always`/`eventually` per
            // (temporal operators bind tightly).
            Some(Token::Historically) if min_bp <= BP_PREFIX_EXPR => {
                self.advance();
                let body = self.expr_bp(BP_PREFIX_EXPR)?;
                Ok(Expr {
                    kind: ExprKind::Historically(Box::new(body)),
                    span: start.merge(self.prev_span()),
                })
            }
            Some(Token::Once) if min_bp <= BP_PREFIX_EXPR => {
                self.advance();
                let body = self.expr_bp(BP_PREFIX_EXPR)?;
                Ok(Expr {
                    kind: ExprKind::Once(Box::new(body)),
                    span: start.merge(self.prev_span()),
                })
            }
            Some(Token::Previously) if min_bp <= BP_PREFIX_EXPR => {
                self.advance();
                let body = self.expr_bp(BP_PREFIX_EXPR)?;
                Ok(Expr {
                    kind: ExprKind::Previously(Box::new(body)),
                    span: start.merge(self.prev_span()),
                })
            }
            // `saw E::f(args)` past-time event observation.
            Some(Token::Saw) if min_bp <= BP_PREFIX_EXPR => {
                self.advance();
                let saw_expr = self.parse_saw_expr(start)?;
                Ok(saw_expr)
            }
            Some(Token::Assert) if min_bp <= BP_PREFIX_EXPR => {
                self.advance();
                let body = self.expr_bp(BP_PREFIX_EXPR)?;
                Ok(Expr {
                    kind: ExprKind::AssertExpr(Box::new(body)),
                    span: start.merge(self.prev_span()),
                })
            }
            Some(Token::Assume) if min_bp <= BP_PREFIX_EXPR => {
                self.advance();
                let body = self.expr_bp(BP_PREFIX_EXPR)?;
                Ok(Expr {
                    kind: ExprKind::AssumeExpr(Box::new(body)),
                    span: start.merge(self.prev_span()),
                })
            }
            Some(
                Token::All | Token::Exists | Token::Some | Token::No | Token::One | Token::Lone,
            ) if min_bp <= BP_PREFIX_EXPR => self.parse_quantifier(),
            // arithmetic aggregators
            Some(Token::Sum | Token::Product | Token::Min | Token::Max | Token::Count)
                if min_bp <= BP_PREFIX_EXPR =>
            {
                self.parse_aggregate()
            }
            Some(Token::Let) if min_bp <= BP_PREFIX_EXPR => self.parse_let_expr(),
            Some(Token::Fn) if min_bp <= BP_PREFIX_EXPR => self.parse_lambda(),
            Some(Token::Match) if min_bp <= BP_PREFIX_EXPR => self.parse_match_expr(),
            Some(Token::Choose) if min_bp <= BP_PREFIX_EXPR => self.parse_choose_expr(),
            // Atoms
            _ => self.expr_atom(),
        }
    }

    fn parse_choose_expr(&mut self) -> Result<Expr, ParseError> {
        let start = self.expect(&Token::Choose)?;
        let (binder, _) = self.expect_name()?;
        self.expect(&Token::Colon)?;
        let ty = self.type_ref()?;
        let predicate = if self.eat(&Token::Where).is_some() {
            Some(Box::new(self.expr_bp(0)?))
        } else {
            None
        };
        let end = predicate.as_ref().map_or(ty.span, |pred| pred.span);
        Ok(Expr {
            kind: ExprKind::Choose(binder, ty, predicate),
            span: start.merge(end),
        })
    }

    /// Parse `all x: T | body` or `all x: T in coll | body`.
    fn parse_quantifier(&mut self) -> Result<Expr, ParseError> {
        let (kind_tok, start) = self.advance();
        let (var, _) = self.expect_name()?;
        self.expect(&Token::Colon)?;
        let ty = self.type_ref()?;
        // Optional `in coll` after the type
        let in_expr = if self.eat(&Token::In).is_some() {
            let old_no_in = self.no_in;
            self.no_in = true;
            // Parse at min_bp=3 so `|` (BP_CHOICE=1) stops the expression.
            let coll = self.expr_bp(3)?;
            self.no_in = old_no_in;
            Some(Box::new(coll))
        } else {
            None
        };

        self.expect(&Token::Pipe)?;
        let body = self.expr_bp(0)?;
        let span = start.merge(body.span);
        let kind = match kind_tok {
            Token::All => ExprKind::All(var, ty, in_expr, Box::new(body)),
            Token::Exists => ExprKind::Exists(var, ty, in_expr, Box::new(body)),
            Token::Some => ExprKind::SomeQ(var, ty, in_expr, Box::new(body)),
            Token::No => ExprKind::NoQ(var, ty, in_expr, Box::new(body)),
            Token::One => ExprKind::OneQ(var, ty, in_expr, Box::new(body)),
            Token::Lone => ExprKind::LoneQ(var, ty, in_expr, Box::new(body)),
            _ => unreachable!(),
        };
        Ok(Expr { kind, span })
    }

    /// parse `sum x: T | body` or `sum x in coll | body`.
    fn parse_aggregate(&mut self) -> Result<Expr, ParseError> {
        let (kind_tok, start) = self.advance();
        let kind = match kind_tok {
            Token::Sum => AggKind::Sum,
            Token::Product => AggKind::Product,
            Token::Min => AggKind::Min,
            Token::Max => AggKind::Max,
            Token::Count => AggKind::Count,
            _ => unreachable!(),
        };
        let (var, _) = self.expect_name()?;

        self.expect(&Token::Colon)?;
        let ty = self.type_ref()?;
        // Optional `in coll` after the type
        let in_expr = if self.eat(&Token::In).is_some() {
            let old_no_in = self.no_in;
            self.no_in = true;
            let coll = self.expr_bp(3)?;
            self.no_in = old_no_in;
            Some(Box::new(coll))
        } else {
            None
        };
        self.expect(&Token::Pipe)?;
        let body = self.expr_bp(0)?;
        let span = start.merge(body.span);
        Ok(Expr {
            kind: ExprKind::Aggregate(kind, var, ty, in_expr, Box::new(body)),
            span,
        })
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

    /// Parse `saw E::f(args)` expression after consuming `Token::Saw`.
    ///
    /// Syntax: `saw <Name> (:: <Name>)* ( <arg>,... )`
    /// Each arg is either `_` (wildcard) or an expression (value match).
    /// Trailing `->` or `=>` after the call are rejected.
    fn parse_saw_expr(&mut self, start: Span) -> Result<Expr, ParseError> {
        // Parse the event path: Name (:: Name)*
        let (first, _) = self.expect_name()?;
        let mut path = vec![first];
        while self.eat(&Token::ColonColon).is_some() {
            let (seg, _) = self.expect_name()?;
            path.push(seg);
        }

        // Parse argument list
        self.expect(&Token::LParen)?;
        let mut args = Vec::new();
        while self.peek() != Some(&Token::RParen) {
            if self.peek() == Some(&Token::Underscore) {
                let (_, span) = self.advance();
                args.push(SawArg::Wild(span));
            } else {
                let e = self.expr()?;
                args.push(SawArg::Expr(e));
            }
            if self.peek() != Some(&Token::RParen) {
                self.expect(&Token::Comma)?;
            }
        }
        let end = self.expect(&Token::RParen)?;

        // Reject arrow forms after `saw`.
        if self.peek() == Some(&Token::Arrow) || self.peek() == Some(&Token::FatArrow) {
            return Err(ParseError::general(
                crate::messages::SAW_RETURN_VALUE_FORBIDDEN,
                start.merge(end),
            ));
        }

        Ok(Expr {
            kind: ExprKind::Saw(path, args),
            span: start.merge(end),
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
        let pattern = if self.peek() == Some(&Token::If) {
            Pattern::Wild(self.cur_span())
        } else {
            self.pattern()?
        };
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

    pub(super) fn pattern(&mut self) -> Result<Pattern, ParseError> {
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
                    // Record pattern: Name { field: pat,... }
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
            // With optional record fields: @Name { field: expr,... }
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
                    } else if self.is_ctor_record_start() {
                        let (fields, end) = self.parse_ctor_fields()?;
                        Ok(Expr {
                            kind: ExprKind::State2Record(n1, n2, fields),
                            span: start.merge(end),
                        })
                    } else {
                        Ok(Expr {
                            kind: ExprKind::State2(n1, n2),
                            span: start.merge(n2_span),
                        })
                    }
                } else if self.is_ctor_record_start() {
                    let (fields, end) = self.parse_ctor_fields()?;
                    Ok(Expr {
                        kind: ExprKind::State1Record(n1, fields),
                        span: start.merge(end),
                    })
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
            // Set comprehension:
            // `{ var: Type where filter }`
            // `{ expr | var: Type in source where filter }`
            // `{ expr | var in source where filter }`
            Some(Token::LBrace) => {
                self.advance(); // consume {
                if matches!(self.peek(), Some(Token::Name(_)))
                    && matches!(self.peek_at(1), Some(Token::Colon) | Some(Token::In))
                {
                    let saved = self.pos;
                    let (var, _) = self.expect_name()?;
                    let domain = if self.eat(&Token::Colon).is_some() {
                        Some(self.type_ref()?)
                    } else {
                        None
                    };
                    let source = if self.eat(&Token::In).is_some() {
                        Some(Box::new(self.expr_bp(BP_CHOICE.1)?))
                    } else {
                        None
                    };
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
                                source,
                                filter: Box::new(filter),
                            },
                            span: start.merge(end),
                        });
                    }
                    // Not simple form — backtrack and try projection form
                    self.pos = saved;
                }
                // Projection form: expr | var: Type where filter
                // Parse above choice level to stop before `|`
                let projection = self.expr_bp(BP_CHOICE.1)?;
                self.expect(&Token::Pipe)?;
                let (var, _) = self.expect_name()?;
                let domain = if self.eat(&Token::Colon).is_some() {
                    Some(self.type_ref()?)
                } else {
                    None
                };
                let source = if self.eat(&Token::In).is_some() {
                    Some(Box::new(self.expr_bp(BP_CHOICE.1)?))
                } else {
                    None
                };
                self.expect(&Token::Where)?;
                let filter = self.expr()?;
                let end = self.expect(&Token::RBrace)?;
                Ok(Expr {
                    kind: ExprKind::SetComp {
                        projection: Some(Box::new(projection)),
                        var,
                        domain,
                        source,
                        filter: Box::new(filter),
                    },
                    span: start.merge(end),
                })
            }
            // Name, qualified ref (Name::Name, Name::Name::Name), or variable
            Some(Token::Name(_)) => {
                let (n1, n1_span) = self.expect_name()?;
                if self.eat(&Token::ColonColon).is_some() {
                    let (n2, n2_span) = self.expect_qualified_name_segment()?;
                    if self.eat(&Token::ColonColon).is_some() {
                        let (n3, n3_span) = self.expect_qualified_name_segment()?;
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
                } else if self.is_ctor_record_start() {
                    // Struct constructor: Name { field: expr,... }
                    let (fields, end) = self.parse_ctor_fields()?;
                    Ok(Expr {
                        kind: ExprKind::StructCtor(n1, fields),
                        span: n1_span.merge(end),
                    })
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
                if matches!(&lhs.kind, ExprKind::Var(name) if name == "Rel") {
                    let saved = self.pos;
                    if let Ok(expr) = self.relation_comprehension_call(start) {
                        return Ok(expr);
                    }
                    self.pos = saved;
                }
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
 // Map update: lhs[key:= value]
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

    pub(super) fn comma_sep_expr(&mut self, end: &Token) -> Result<Vec<Expr>, ParseError> {
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

    fn relation_comprehension_call(&mut self, start: Span) -> Result<Expr, ParseError> {
        let projection = self.expr_bp(BP_CHOICE.1)?;
        self.expect(&Token::Pipe)?;
        let mut bindings = Vec::new();
        loop {
            let (var, var_span) = self.expect_name()?;
            self.expect(&Token::Colon)?;
            let domain = self.type_ref()?;
            let source = if self.eat(&Token::In).is_some() {
                Some(Box::new(self.expr_bp(BP_CHOICE.1)?))
            } else {
                None
            };
            let span = var_span.merge(source.as_ref().map_or(domain.span, |expr| expr.span));
            bindings.push(RelCompBinding {
                var,
                domain,
                source,
                span,
            });
            if self.eat(&Token::Comma).is_none() {
                break;
            }
        }
        self.expect(&Token::Where)?;
        let filter = self.expr()?;
        let end = self.expect(&Token::RParen)?;
        Ok(Expr {
            kind: ExprKind::RelComp {
                projection: Box::new(projection),
                bindings,
                filter: Box::new(filter),
            },
            span: start.merge(end),
        })
    }
}
