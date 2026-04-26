//! Type declaration and type reference parsing.

use super::Parser;
use crate::ast::{
    AliasDecl, Expr, NewtypeDecl, RecField, RecordDecl, TopDecl, TypeDecl, TypeRef, TypeRefKind,
    TypeVariant, Visibility,
};
use crate::diagnostic::ParseError;
use crate::lex::Token;
use crate::span::Span;

impl Parser {
    /// Parse `enum Name =...` or `enum Name<T, E> =...`
    pub(super) fn enum_decl(&mut self) -> Result<TopDecl, ParseError> {
        let start = self.expect(&Token::Enum)?;
        let (name, _) = self.expect_name()?;
        // Optional type parameters: <T> or <T, E>
        let type_params = if self.eat(&Token::Lt).is_some() {
            let params = self.comma_sep(&Token::Gt, |p| {
                let (n, _) = p.expect_name()?;
                Ok(n)
            })?;
            self.expect(&Token::Gt)?;
            params
        } else {
            vec![]
        };
        self.expect(&Token::Eq)?;
        let variants = self.type_variants()?;
        let last_span = match variants.last() {
            Some(
                TypeVariant::Simple { span, .. }
                | TypeVariant::Tuple { span, .. }
                | TypeVariant::Record { span, .. }
                | TypeVariant::Param { span, .. },
            ) => *span,
            None => start,
        };
        Ok(TopDecl::Type(TypeDecl {
            name,
            type_params,
            visibility: Visibility::Private,
            variants,
            span: start.merge(last_span),
        }))
    }

    /// Parse `struct Name { fields }`
    pub(super) fn struct_decl(&mut self) -> Result<TopDecl, ParseError> {
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

    /// Parse pipe-separated type variants: `Variant | Variant |...`
    fn type_variants(&mut self) -> Result<Vec<TypeVariant>, ParseError> {
        let mut variants = vec![self.type_variant()?];
        while self.eat(&Token::Pipe).is_some() {
            variants.push(self.type_variant()?);
        }
        Ok(variants)
    }

    /// Parse `type Name = TypeRef` — always a type alias.
    /// Enums use `enum`, structs use `struct`.
    pub(super) fn alias_decl(&mut self) -> Result<TopDecl, ParseError> {
        let start = self.expect(&Token::Type)?;
        let (name, _) = self.expect_name()?;
        // Newtype syntax: `type UserId(string)`
        if self.eat(&Token::LParen).is_some() {
            let inner = self.type_ref()?;
            let end = self.expect(&Token::RParen)?;
            return Ok(TopDecl::Newtype(NewtypeDecl {
                span: start.merge(end),
                name,
                visibility: Visibility::Private,
                inner,
            }));
        }
        // Alias syntax: `type Money = int{$ > 0}`
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
        } else if self.eat(&Token::LParen).is_some() {
            // Tuple variant: ok(Int), ok(Int, String)
            let fields = self.comma_sep(&Token::RParen, Parser::type_ref)?;
            let end = self.expect(&Token::RParen)?;
            Ok(TypeVariant::Tuple {
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

    pub(super) fn rec_field(&mut self) -> Result<RecField, ParseError> {
        let (name, start) = self.expect_name()?;
        self.expect(&Token::Colon)?;
        let ty = self.type_ref()?;
        Ok(RecField {
            span: start.merge(ty.span),
            name,
            ty,
        })
    }

    /// Check if the current position starts a constructor record: `{ Name:...`.
    /// Distinguished from a block body by the `Name:` pattern after `{`.
    pub(super) fn is_ctor_record_start(&self) -> bool {
        matches!(self.peek_at(0), Some(Token::LBrace))
            && matches!(self.peek_at(1), Some(Token::Name(_)))
            && matches!(self.peek_at(2), Some(Token::Colon))
    }

    /// Parse constructor field arguments: `{ field: expr, field: expr,... }`
    pub(super) fn parse_ctor_fields(&mut self) -> Result<(Vec<(String, Expr)>, Span), ParseError> {
        self.expect(&Token::LBrace)?;
        let mut fields = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace) | None) {
            let (name, _) = self.expect_name()?;
            self.expect(&Token::Colon)?;
            let value = self.expr()?;
            fields.push((name, value));
            self.eat(&Token::Comma);
        }
        let end = self.expect(&Token::RBrace)?;
        Ok((fields, end))
    }

    // ── Type References ──────────────────────────────────────────────

    pub(super) fn type_ref(&mut self) -> Result<TypeRef, ParseError> {
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
    pub(super) fn type_ref_no_refine(&mut self) -> Result<TypeRef, ParseError> {
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
            // Named refinement: `name: Type{pred}`
            // e.g. `b: bool{b == true}`, `x: int{x > 0}`
            // Parse name, colon, base type name, then {pred}.
            if self.eat(&Token::Colon).is_some() {
                let (base_name, base_start) = self.expect_name()?;
                let base = TypeRef {
                    kind: TypeRefKind::Simple(base_name),
                    span: base_start,
                };
                self.expect(&Token::LBrace)?;
                let pred = self.expr()?;
                let end = self.expect(&Token::RBrace)?;
                return Ok(TypeRef {
                    kind: TypeRefKind::NamedRefine(name, Box::new(base), Box::new(pred)),
                    span: start.merge(end),
                });
            }
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
}
