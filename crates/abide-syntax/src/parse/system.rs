//! System and program declaration parsing.

use super::Parser;
use crate::ast::{
    ChooseBlock, CommandBodyDecl, CommandDecl, Contract, CreateBlock, CreateField, DepDecl,
    EventItem, EventLetCall, EventMatchArm, EventMatchBlock, EventMatchScrutinee, Expr,
    ExternAssumeBlock, ExternAssumeItem, ExternDecl, ExternItem, ForBlock, InterfaceDecl,
    InterfaceItem, MayDecl, Pattern, ProcDecl, ProcItem, ProcUseDecl, ProgramDecl, ProgramItem,
    QueryDecl, QuerySigDecl, StoreParam, SystemActionDecl, SystemDecl, SystemItem,
};
use crate::diagnostic::ParseError;
use crate::lex::Token;
use crate::span::Span;

type ParsedCommandSig = (
    Span,
    String,
    Vec<crate::ast::Param>,
    Option<crate::ast::TypeRef>,
    Span,
);

impl Parser {
    pub(super) fn interface_decl(&mut self) -> Result<InterfaceDecl, ParseError> {
        let start = self.expect(&Token::Interface)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::LBrace)?;
        let mut items = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) && !self.at_end() {
            match self.interface_item() {
                Ok(item) => items.push(item),
                Err(err) if self.recovering => {
                    self.push_recovery_error(err);
                    items.push(InterfaceItem::Error(
                        self.recover_to_brace_item(super::is_interface_item_starter),
                    ));
                }
                Err(err) => return Err(err),
            }
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(InterfaceDecl {
            name,
            items,
            span: start.merge(end),
        })
    }

    pub(super) fn system_decl(&mut self) -> Result<SystemDecl, ParseError> {
        let start = self.expect(&Token::System)?;
        let (name, _) = self.expect_name()?;

        // Parse optional Store<T> constructor parameters.
        let params = if self.eat(&Token::LParen).is_some() {
            let ps = self.comma_sep(&Token::RParen, Parser::store_param)?;
            self.expect(&Token::RParen)?;
            ps
        } else {
            vec![]
        };

        let implements = if self.eat(&Token::Implements).is_some() {
            let (iface, _) = self.expect_name()?;
            Some(iface)
        } else {
            None
        };

        self.expect(&Token::LBrace)?;
        let mut items = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) && !self.at_end() {
            match self.system_item() {
                Ok(item) => items.push(item),
                Err(err) if self.recovering => {
                    self.push_recovery_error(err);
                    items.push(SystemItem::Error(
                        self.recover_to_brace_item(super::is_system_item_starter),
                    ));
                }
                Err(err) => return Err(err),
            }
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(SystemDecl {
            name,
            params,
            implements,
            items,
            span: start.merge(end),
        })
    }

    pub(super) fn extern_decl(&mut self) -> Result<ExternDecl, ParseError> {
        let start = self.expect(&Token::Extern)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::LBrace)?;
        let mut items = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) && !self.at_end() {
            match self.extern_item() {
                Ok(item) => items.push(item),
                Err(err) if self.recovering => {
                    self.push_recovery_error(err);
                    items.push(ExternItem::Error(
                        self.recover_to_brace_item(super::is_extern_item_starter),
                    ));
                }
                Err(err) => return Err(err),
            }
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(ExternDecl {
            name,
            items,
            span: start.merge(end),
        })
    }

    /// R4: parse `program Name(store_params) { let bindings; invariant blocks }`.
    /// Programs are composition roots with no commands/steps/queries.
    pub(super) fn program_decl(&mut self) -> Result<ProgramDecl, ParseError> {
        let start = self.expect(&Token::Program)?;
        let (name, _) = self.expect_name()?;

        // Parse optional Store<T> constructor parameters (same as system).
        let params = if self.eat(&Token::LParen).is_some() {
            let ps = self.comma_sep(&Token::RParen, Parser::store_param)?;
            self.expect(&Token::RParen)?;
            ps
        } else {
            vec![]
        };

        self.expect(&Token::LBrace)?;
        let mut items = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) && !self.at_end() {
            match self.peek() {
                Some(Token::Let) => match self.let_binding_decl() {
                    Ok(item) => items.push(ProgramItem::Let(item)),
                    Err(err) if self.recovering => {
                        self.push_recovery_error(err);
                        items.push(ProgramItem::Error(
                            self.recover_to_brace_item(super::is_program_item_starter),
                        ));
                    }
                    Err(err) => return Err(err),
                },
                Some(Token::Use) => match self.program_proc_use_decl() {
                    Ok(item) => items.push(ProgramItem::UseProc(item)),
                    Err(err) if self.recovering => {
                        self.push_recovery_error(err);
                        items.push(ProgramItem::Error(
                            self.recover_to_brace_item(super::is_program_item_starter),
                        ));
                    }
                    Err(err) => return Err(err),
                },
                Some(Token::Invariant) => match self.invariant_decl() {
                    Ok(item) => items.push(ProgramItem::Invariant(item)),
                    Err(err) if self.recovering => {
                        self.push_recovery_error(err);
                        items.push(ProgramItem::Error(
                            self.recover_to_brace_item(super::is_program_item_starter),
                        ));
                    }
                    Err(err) => return Err(err),
                },
                Some(Token::Proc) => match self.proc_decl() {
                    Ok(item) => items.push(ProgramItem::Proc(item)),
                    Err(err) if self.recovering => {
                        self.push_recovery_error(err);
                        items.push(ProgramItem::Error(
                            self.recover_to_brace_item(super::is_program_item_starter),
                        ));
                    }
                    Err(err) => return Err(err),
                },
                Some(tok) => {
                    let err = ParseError::expected(
                        "`let`, `use`, `invariant`, or `proc`",
                        &format!("`{tok}`"),
                        self.cur_span(),
                    );
                    if self.recovering {
                        self.push_recovery_error(err);
                        items.push(ProgramItem::Error(
                            self.recover_to_brace_item(super::is_program_item_starter),
                        ));
                    } else {
                        return Err(err);
                    }
                }
                None => return Err(ParseError::eof(self.cur_span())),
            }
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(ProgramDecl {
            name,
            params,
            items,
            span: start.merge(end),
        })
    }

    /// Parse `proc name(params) [requires expr] { body }`.
    ///
    /// Proc body items:
    /// - Node declaration: `name = instance.command(args)`
    /// - Needs condition: `name needs source.port and other`
    /// - Composition sugar: `a.ok -> b.ok -> c` (desugared to needs edges)
    pub(super) fn proc_decl(&mut self) -> Result<ProcDecl, ParseError> {
        let start = self.expect(&Token::Proc)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::LParen)?;
        let params = self.comma_sep(&Token::RParen, Parser::param)?;
        self.expect(&Token::RParen)?;
        let requires = if self.eat(&Token::Requires).is_some() {
            Some(self.expr()?)
        } else {
            None
        };
        self.expect(&Token::LBrace)?;
        let mut items = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) && !self.at_end() {
            while self.eat(&Token::Semi).is_some() {}
            if matches!(self.peek(), Some(Token::RBrace)) {
                break;
            }
            let parsed = if matches!(self.peek(), Some(Token::Use)) {
                self.proc_use_item()
            } else if matches!(self.peek(), Some(Token::Match)) {
                self.proc_match_item()
            } else {
                self.proc_item()
            };
            match parsed {
                Ok(mut parsed) => items.append(&mut parsed),
                Err(err) if self.recovering => {
                    self.push_recovery_error(err);
                    items.push(ProcItem::Error(
                        self.recover_to_brace_item(super::is_proc_item_starter),
                    ));
                }
                Err(err) => return Err(err),
            }
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(ProcDecl {
            name,
            params,
            requires,
            items,
            span: start.merge(end),
        })
    }

    fn proc_use_decl(
        &mut self,
        require_alias: bool,
        allow_alias: bool,
    ) -> Result<ProcUseDecl, ParseError> {
        let start = self.expect(&Token::Use)?;
        let (proc_name, _) = self.expect_name()?;
        self.expect(&Token::LParen)?;
        let args = self.comma_sep(&Token::RParen, |p| {
            let (name, _) = p.expect_name()?;
            Ok(name)
        })?;
        let end = self.expect(&Token::RParen)?;
        let alias = if self.eat(&Token::As).is_some() {
            if !allow_alias {
                return Err(ParseError::expected_with_help(
                    "end of proc use",
                    "`as`",
                    self.cur_span(),
                    "program-level `use` instantiates a reusable proc directly; aliases are only allowed for proc composition inside another proc",
                ));
            }
            let (alias, _) = self.expect_name()?;
            Some(alias)
        } else if require_alias {
            return Err(ParseError::expected(
                "`as alias`",
                &format!(
                    "`{}`",
                    self.peek().map_or("EOF".to_owned(), |t| format!("{t}"))
                ),
                self.cur_span(),
            ));
        } else {
            None
        };
        Ok(ProcUseDecl {
            proc_name,
            args,
            alias,
            span: start.merge(end),
        })
    }

    fn program_proc_use_decl(&mut self) -> Result<ProcUseDecl, ParseError> {
        self.proc_use_decl(false, false)
    }

    fn proc_use_item(&mut self) -> Result<Vec<ProcItem>, ParseError> {
        Ok(vec![ProcItem::UseProc(self.proc_use_decl(true, true)?)])
    }

    /// Parse a single proc body item. Returns one or more ProcItems
    /// (composition sugar desugars to multiple needs edges).
    ///
    /// Disambiguates:
    /// - `name = instance.command(args)` → Node
    /// - `name needs condition` → NeedsEdge
    /// - `a.port -> b.port -> c` → desugared NeedsEdge chain
    fn proc_item(&mut self) -> Result<Vec<ProcItem>, ParseError> {
        let start = self.cur_span();
        let (first_name, first_span) = self.expect_name()?;

        // Check for node declaration: `name = instance.command(args)`
        if self.eat(&Token::Eq).is_some() {
            let (instance, _) = self.expect_name()?;
            self.expect(&Token::Dot)?;
            let (command, _) = self.expect_name()?;
            self.expect(&Token::LParen)?;
            let args = self.comma_sep(&Token::RParen, Parser::expr)?;
            let end = self.expect(&Token::RParen)?;
            return Ok(vec![ProcItem::Node {
                name: first_name,
                instance,
                command,
                args,
                span: start.merge(end),
            }]);
        }

        // Check for needs condition: `name needs source.port and other`
        if self.eat(&Token::Needs).is_some() {
            let condition = self.proc_dep_condition()?;
            return Ok(vec![ProcItem::NeedsEdge {
                target: first_name,
                condition,
                span: start.merge(self.cur_span()),
            }]);
        }

        // Composition sugar: `a.port -> b.port -> c`
        // first_name is the first segment; check for `.port`
        let (first_ref, first_port) = self.finish_proc_ref(first_name)?;

        // Must have `->` to be composition sugar
        if !matches!(self.peek(), Some(Token::Arrow)) {
            return Err(ParseError::expected(
                "`=`, `needs`, `.`, or `->`",
                &format!(
                    "`{}`",
                    self.peek().map_or("EOF".to_owned(), |t| format!("{t}"))
                ),
                self.cur_span(),
            ));
        }

        // Parse chain: collect (name, Option<port>) segments
        let mut chain: Vec<(String, Option<String>)> = vec![(first_ref, first_port)];
        while self.eat(&Token::Arrow).is_some() {
            let (seg_name, _) = self.expect_name()?;
            let (seg_ref, seg_port) = self.finish_proc_ref(seg_name)?;
            chain.push((seg_ref, seg_port));
        }

        // Reject port on the terminal segment — only source nodes have ports.
        if let Some((ref terminal_name, Some(ref terminal_port))) = chain.last() {
            return Err(ParseError::expected_with_help(
                "end of composition chain",
                &format!("`.{terminal_port}`"),
                self.cur_span(),
                &format!(
                    "the terminal node `{terminal_name}` in a `->` chain cannot have a port; \
                     ports (`.ok`, `.err`, etc.) are only meaningful on source nodes"
                ),
            ));
        }

        // Desugar chain into needs edges: each segment needs the previous
        let mut edges = Vec::new();
        for i in 1..chain.len() {
            let (ref source, ref source_port) = chain[i - 1];
            let (ref target, _) = chain[i];
            edges.push(ProcItem::NeedsEdge {
                target: target.clone(),
                condition: crate::ast::ProcDepCond::Fact {
                    node: source.clone(),
                    qualifier: source_port.clone(),
                },
                span: first_span.merge(self.cur_span()),
            });
        }
        Ok(edges)
    }

    /// Parse proc branching sugar and desugar it into needs edges.
    ///
    /// Example:
    ///
    /// `match charge { @ok => paid, reserve @err => fail }`
    fn proc_match_item(&mut self) -> Result<Vec<ProcItem>, ParseError> {
        let start = self.expect(&Token::Match)?;
        let (source_name, _) = self.expect_name()?;
        let (source, qualifier) = self.finish_proc_ref(source_name)?;
        if let Some(qualifier) = qualifier {
            return Err(ParseError::expected_with_help(
                "proc node reference",
                &format!("`.{qualifier}`"),
                self.cur_span(),
                "match on a proc source expects a node reference like `charge` or `flow::charge`, not an outcome-qualified fact",
            ));
        }
        self.expect(&Token::LBrace)?;
        let mut edges = Vec::new();

        while !matches!(self.peek(), Some(Token::RBrace)) && !self.at_end() {
            self.expect(&Token::At)?;
            let (port, _) = self.expect_name()?;
            self.expect(&Token::FatArrow)?;

            let (first_target, first_target_span) = self.expect_name()?;
            edges.push(ProcItem::NeedsEdge {
                target: first_target,
                condition: crate::ast::ProcDepCond::Fact {
                    node: source.clone(),
                    qualifier: Some(port.clone()),
                },
                span: start.merge(first_target_span),
            });

            while self.eat(&Token::Comma).is_some() {
                if matches!(self.peek(), Some(Token::RBrace | Token::At)) {
                    break;
                }
                let (target, target_span) = self.expect_name()?;
                edges.push(ProcItem::NeedsEdge {
                    target,
                    condition: crate::ast::ProcDepCond::Fact {
                        node: source.clone(),
                        qualifier: Some(port.clone()),
                    },
                    span: start.merge(target_span),
                });
            }

            while self.eat(&Token::Semi).is_some() {}
        }

        self.expect(&Token::RBrace)?;
        Ok(edges)
    }

    fn proc_dep_condition(&mut self) -> Result<crate::ast::ProcDepCond, ParseError> {
        self.proc_dep_or()
    }

    fn proc_dep_or(&mut self) -> Result<crate::ast::ProcDepCond, ParseError> {
        let mut cond = self.proc_dep_and()?;
        while self.eat(&Token::Or).is_some() {
            let rhs = self.proc_dep_and()?;
            cond = crate::ast::ProcDepCond::Or(Box::new(cond), Box::new(rhs));
        }
        Ok(cond)
    }

    fn proc_dep_and(&mut self) -> Result<crate::ast::ProcDepCond, ParseError> {
        let mut cond = self.proc_dep_not()?;
        while self.eat(&Token::And).is_some() {
            let rhs = self.proc_dep_not()?;
            cond = crate::ast::ProcDepCond::And(Box::new(cond), Box::new(rhs));
        }
        Ok(cond)
    }

    fn proc_dep_not(&mut self) -> Result<crate::ast::ProcDepCond, ParseError> {
        if self.eat(&Token::Not).is_some() {
            let inner = self.proc_dep_not()?;
            return Ok(crate::ast::ProcDepCond::Not(Box::new(inner)));
        }
        self.proc_dep_atom()
    }

    fn proc_dep_atom(&mut self) -> Result<crate::ast::ProcDepCond, ParseError> {
        if self.eat(&Token::LParen).is_some() {
            let cond = self.proc_dep_condition()?;
            self.expect(&Token::RParen)?;
            return Ok(cond);
        }
        let (node, _) = self.expect_name()?;
        let (node, qualifier) = self.finish_proc_ref(node)?;
        Ok(crate::ast::ProcDepCond::Fact { node, qualifier })
    }

    fn finish_proc_ref(&mut self, head: String) -> Result<(String, Option<String>), ParseError> {
        let mut path = head;
        while self.eat(&Token::ColonColon).is_some() {
            let (segment, _) = self.expect_name()?;
            path.push_str("::");
            path.push_str(&segment);
        }
        let qualifier = if self.eat(&Token::Dot).is_some() {
            let (qualifier, _) = self.expect_name()?;
            Some(qualifier)
        } else {
            None
        };
        Ok((path, qualifier))
    }

    /// Parse a single `name: Store<EntityType>` parameter, optionally bounded
    /// as `name: Store<EntityType>[N]`, `[lo..hi]`, or `[..hi]`.
    /// The type is `Store<Entity>` where `Store` matches the keyword token
    /// or `Name("Store")`.
    pub(super) fn store_param(&mut self) -> Result<StoreParam, ParseError> {
        let (name, start) = self.expect_name()?;
        self.expect(&Token::Colon)?;
        // Accept `Store` — now handled by expect_name as soft keyword,
        // so we need to check the name value.
        let (store_kw, _) = self.expect_name()?;
        if store_kw != "Store" && store_kw != "store" {
            return Err(ParseError::expected(
                "`Store`",
                &format!("`{store_kw}`"),
                self.cur_span(),
            ));
        }
        self.expect(&Token::Lt)?;
        let (entity_type, _) = self.expect_name()?;
        let gt_span = self.expect(&Token::Gt)?;
        let (bounds, end) = if matches!(self.peek(), Some(Token::LBracket)) {
            let (bounds, end) = self.store_bounds()?;
            (Some(bounds), end)
        } else {
            (None, gt_span)
        };
        Ok(StoreParam {
            name,
            entity_type,
            bounds,
            span: start.merge(end),
        })
    }

    pub(super) fn system_item(&mut self) -> Result<SystemItem, ParseError> {
        match self.peek() {
            Some(Token::Use) => Err(ParseError::expected_with_help(
                "system item (`command`, `action`, `query`, `fsm`, `derived`, `invariant`, or field)",
                "`use`",
                self.cur_span(),
                crate::messages::USE_ENTITY_REMOVED,
            )),
            Some(tok @ (Token::Fair | Token::Strong)) => Err(ParseError::expected(
                "system item (`command`, `action`, `query`, `fsm`, `derived`, `invariant`, or field)",
                &format!("`{tok}`"),
                self.cur_span(),
            )),
            Some(Token::Dep) => Ok(SystemItem::Dep(self.dep_decl()?)),
            Some(Token::Command) => Ok(SystemItem::Command(self.system_command_decl()?)),
            Some(Token::Action) => Ok(SystemItem::Action(self.system_action_decl()?)),
            Some(Token::Query) => Ok(SystemItem::Query(self.query_decl()?)),
            Some(Token::Pred) => Ok(SystemItem::Pred(self.pred_decl()?)),
            Some(Token::Fsm) => Ok(SystemItem::Fsm(self.fsm_decl()?)),
            Some(Token::Derived) => Ok(SystemItem::Derived(self.derived_decl()?)),
            Some(Token::Invariant) => Ok(SystemItem::Invariant(self.invariant_decl()?)),
            Some(Token::Name(ref name)) if name == "uses" => Err(ParseError::expected_with_help(
                "system item (`command`, `action`, `query`, `fsm`, `derived`, `invariant`, or field)",
                "`uses`",
                self.cur_span(),
                crate::messages::USE_ENTITY_REMOVED,
            )),
            // Field declaration: `name: Type = default`
            Some(Token::Name(_)) if matches!(self.peek_at(1), Some(Token::Colon)) => {
                Ok(SystemItem::Field(self.field_decl()?))
            }
            Some(tok) => Err(ParseError::expected(
                "system item (`command`, `action`, `query`, `fsm`, `derived`, `invariant`, or field)",
                &format!("`{tok}`"),
                self.cur_span(),
            )),
            None => Err(ParseError::eof(self.cur_span())),
        }
    }

    pub(super) fn interface_item(&mut self) -> Result<InterfaceItem, ParseError> {
        match self.peek() {
            Some(Token::Command) => Ok(InterfaceItem::Command(self.command_decl()?)),
            Some(Token::Query) => Ok(InterfaceItem::QuerySig(self.query_sig_decl()?)),
            Some(tok) => Err(ParseError::expected(
                "interface item (`command` or `query`)",
                &format!("`{tok}`"),
                self.cur_span(),
            )),
            None => Err(ParseError::eof(self.cur_span())),
        }
    }

    pub(super) fn extern_item(&mut self) -> Result<ExternItem, ParseError> {
        match self.peek() {
            Some(Token::Command) => Ok(ExternItem::Command(self.command_decl()?)),
            Some(Token::May) => Ok(ExternItem::May(self.may_decl()?)),
            Some(Token::Assume) => Ok(ExternItem::Assume(self.extern_assume_block()?)),
            Some(tok) => Err(ParseError::expected(
                "extern item (`command`, `may`, or `assume`)",
                &format!("`{tok}`"),
                self.cur_span(),
            )),
            None => Err(ParseError::eof(self.cur_span())),
        }
    }

    fn dep_decl(&mut self) -> Result<DepDecl, ParseError> {
        let start = self.expect(&Token::Dep)?;
        let (name, end) = self.expect_name()?;
        Ok(DepDecl {
            name,
            span: start.merge(end),
        })
    }

    fn command_decl(&mut self) -> Result<CommandDecl, ParseError> {
        let (start, name, params, return_type, end) = self.command_sig_decl()?;
        Ok(CommandDecl {
            name,
            params,
            return_type,
            body: None,
            span: start.merge(end),
        })
    }

    fn system_command_decl(&mut self) -> Result<CommandDecl, ParseError> {
        let (start, name, params, return_type, end) = self.command_sig_decl()?;
        let body = self.command_body_decl()?;
        let span = if let Some(body) = &body {
            start.merge(body.span)
        } else {
            start.merge(end)
        };
        Ok(CommandDecl {
            name,
            params,
            return_type,
            body,
            span,
        })
    }

    fn command_sig_decl(&mut self) -> Result<ParsedCommandSig, ParseError> {
        let start = self.expect(&Token::Command)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::LParen)?;
        let params = self.comma_sep(&Token::RParen, Parser::param)?;
        let rparen = self.expect(&Token::RParen)?;
        // Optional return type: `-> TypeName`
        let (return_type, end) = if self.eat(&Token::Arrow).is_some() {
            let ty = self.type_ref_no_refine()?;
            let s = ty.span;
            (Some(ty), s)
        } else {
            (None, rparen)
        };
        Ok((start, name, params, return_type, end))
    }

    fn command_body_decl(&mut self) -> Result<Option<CommandBodyDecl>, ParseError> {
        let contracts = self.contracts()?;
        for c in &contracts {
            if let Contract::Ensures { span, .. } = c {
                return Err(ParseError::expected_with_help(
                    "`requires` or `{`",
                    "`ensures`",
                    *span,
                    crate::messages::ACTION_ENSURES_NOT_ALLOWED,
                ));
            }
        }

        let body_start = if let Some(lb) = self.eat(&Token::LBrace) {
            if let Some(first_contract) = contracts.first() {
                let first_span = match first_contract {
                    Contract::Requires { span, .. }
                    | Contract::Ensures { span, .. }
                    | Contract::Decreases { span, .. }
                    | Contract::Invariant { span, .. } => *span,
                };
                first_span.merge(lb)
            } else {
                lb
            }
        } else {
            if contracts.is_empty() {
                return Ok(None);
            }
            return Err(ParseError::expected(
                "`{`",
                &format!(
                    "`{}`",
                    self.peek().map_or("EOF".to_owned(), |t| format!("{t}"))
                ),
                self.cur_span(),
            ));
        };

        let mut items = Vec::new();
        let mut return_expr = None;
        while !matches!(self.peek(), Some(Token::RBrace)) {
            while self.eat(&Token::Semi).is_some() {}
            if matches!(self.peek(), Some(Token::RBrace)) {
                break;
            }
            if matches!(self.peek(), Some(Token::Return)) {
                self.advance();
                return_expr = Some(self.expr()?);
                while self.eat(&Token::Semi).is_some() {}
                break;
            }
            match self.event_item() {
                Ok(item) => items.push(item),
                Err(err) if self.recovering => {
                    self.push_recovery_error(err);
                    items.push(EventItem::Error(self.recover_to_event_item()));
                }
                Err(err) => return Err(err),
            }
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(Some(CommandBodyDecl {
            contracts,
            items,
            return_expr,
            span: body_start.merge(end),
        }))
    }

    fn system_call_parts(&mut self) -> Result<(String, String, Vec<Expr>, Span), ParseError> {
        let (system, start) = self.expect_name()?;
        self.expect(&Token::ColonColon)?;
        let (command, _) = self.expect_name()?;
        self.expect(&Token::LParen)?;
        let args = self.comma_sep(&Token::RParen, Parser::expr)?;
        let end = self.expect(&Token::RParen)?;
        Ok((system, command, args, start.merge(end)))
    }

    fn system_action_decl(&mut self) -> Result<SystemActionDecl, ParseError> {
        let start = self.expect(&Token::Action)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::LParen)?;
        let params = self.comma_sep(&Token::RParen, Parser::param)?;
        self.expect(&Token::RParen)?;
        let body = self.command_body_decl()?.ok_or_else(|| {
            ParseError::expected(
                "`requires` or `{`",
                &format!(
                    "`{}`",
                    self.peek().map_or("EOF".to_owned(), |t| format!("{t}"))
                ),
                self.cur_span(),
            )
        })?;
        Ok(SystemActionDecl {
            name,
            params,
            contracts: body.contracts,
            items: body.items,
            return_expr: body.return_expr,
            span: start.merge(body.span),
        })
    }

    fn query_decl(&mut self) -> Result<QueryDecl, ParseError> {
        let start = self.expect(&Token::Query)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::LParen)?;
        let params = self.comma_sep(&Token::RParen, Parser::param)?;
        self.expect(&Token::RParen)?;
        self.expect(&Token::Eq)?;
        let body = self.expr()?;
        let end = body.span;
        Ok(QueryDecl {
            name,
            params,
            body,
            span: start.merge(end),
        })
    }

    fn query_sig_decl(&mut self) -> Result<QuerySigDecl, ParseError> {
        let start = self.expect(&Token::Query)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::LParen)?;
        let params = self.comma_sep(&Token::RParen, Parser::param)?;
        self.expect(&Token::RParen)?;
        self.expect(&Token::Arrow)?;
        let return_type = self.type_ref()?;
        let end = return_type.span;
        Ok(QuerySigDecl {
            name,
            params,
            return_type,
            span: start.merge(end),
        })
    }

    fn may_decl(&mut self) -> Result<MayDecl, ParseError> {
        let start = self.expect(&Token::May)?;
        let (command, _) = self.expect_name()?;
        self.expect(&Token::LBrace)?;
        let mut returns = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) && !self.at_end() {
            while self.eat(&Token::Semi).is_some() {}
            if matches!(self.peek(), Some(Token::RBrace)) {
                break;
            }
            self.expect(&Token::Return)?;
            returns.push(self.expr()?);
            while self.eat(&Token::Semi).is_some() {}
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(MayDecl {
            command,
            returns,
            span: start.merge(end),
        })
    }

    fn extern_assume_block(&mut self) -> Result<ExternAssumeBlock, ParseError> {
        let start = self.expect(&Token::Assume)?;
        self.expect(&Token::LBrace)?;
        let mut items = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) && !self.at_end() {
            while self.eat(&Token::Semi).is_some() {}
            if matches!(self.peek(), Some(Token::RBrace)) {
                break;
            }
            match self.peek() {
                Some(Token::Strong) => {
                    let (tok, s) = self.advance();
                    match self.peek() {
                        Some(Token::Fair) => {
                            self.advance();
                            let path = self.event_path()?;
                            let span = s.merge(path.span);
                            items.push(ExternAssumeItem::StrongFair { path, span });
                        }
                        _ => {
                            return Err(ParseError::expected(
                                "`fair`",
                                &format!("`{tok}`"),
                                self.cur_span(),
                            ));
                        }
                    }
                }
                Some(Token::Fair) => {
                    let (_, s) = self.advance();
                    let path = self.event_path()?;
                    let span = s.merge(path.span);
                    items.push(ExternAssumeItem::Fair { path, span });
                }
                _ => {
                    let expr = self.expr()?;
                    items.push(ExternAssumeItem::Expr {
                        span: expr.span,
                        expr,
                    });
                }
            }
            while self.eat(&Token::Semi).is_some() {}
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(ExternAssumeBlock {
            items,
            span: start.merge(end),
        })
    }

    pub(super) fn event_item(&mut self) -> Result<EventItem, ParseError> {
        match self.peek() {
            Some(Token::Choose) => Ok(EventItem::Choose(self.choose_block()?)),
            Some(Token::For) => Ok(EventItem::For(self.for_block()?)),
            Some(Token::Create) => Ok(EventItem::Create(self.create_block()?)),
            Some(Token::Let) => Ok(EventItem::LetCall(self.event_let_call()?)),
            Some(Token::Match) => Ok(EventItem::Match(self.event_match_block()?)),
            // Detect wrong-context keywords with helpful suggestions
            Some(Token::Given | Token::Then) => Err(ParseError::expected_with_help(
                "command/action body item",
                &format!("`{}`", self.peek().unwrap()),
                self.cur_span(),
                crate::messages::HINT_EVENT_BODY,
            )),
            Some(Token::Assert) => Err(ParseError::expected_with_help(
                "command/action body item",
                "`assert`",
                self.cur_span(),
                crate::messages::HINT_ASSERT_IN_EVENT,
            )),
            _ => Ok(EventItem::Expr(self.expr()?)),
        }
    }

    fn event_let_call(&mut self) -> Result<EventLetCall, ParseError> {
        let start = self.expect(&Token::Let)?;
        let (name, _) = self.expect_name()?;
        self.expect(&Token::Eq)?;
        let (system, command, args, span) = self.system_call_parts()?;
        Ok(EventLetCall {
            name,
            system,
            command,
            args,
            span: start.merge(span),
        })
    }

    fn event_match_scrutinee(&mut self) -> Result<EventMatchScrutinee, ParseError> {
        let (first, start) = self.expect_name()?;
        if self.eat(&Token::ColonColon).is_some() {
            let (command, _) = self.expect_name()?;
            self.expect(&Token::LParen)?;
            let args = self.comma_sep(&Token::RParen, Parser::expr)?;
            let end = self.expect(&Token::RParen)?;
            Ok(EventMatchScrutinee::Call {
                system: first,
                command,
                args,
                span: start.merge(end),
            })
        } else {
            Ok(EventMatchScrutinee::Var(first, start))
        }
    }

    fn event_match_block(&mut self) -> Result<EventMatchBlock, ParseError> {
        let start = self.expect(&Token::Match)?;
        let scrutinee = self.event_match_scrutinee()?;
        self.expect(&Token::LBrace)?;
        let mut arms = Vec::new();
        while self.peek() != Some(&Token::RBrace) && !self.at_end() {
            arms.push(self.event_match_arm()?);
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(EventMatchBlock {
            scrutinee,
            arms,
            span: start.merge(end),
        })
    }

    fn event_match_arm(&mut self) -> Result<EventMatchArm, ParseError> {
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
        self.expect(&Token::LBrace)?;
        let mut items = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) && !self.at_end() {
            while self.eat(&Token::Semi).is_some() {}
            if matches!(self.peek(), Some(Token::RBrace)) {
                break;
            }
            match self.event_item() {
                Ok(item) => items.push(item),
                Err(err) if self.recovering => {
                    self.push_recovery_error(err);
                    items.push(EventItem::Error(self.recover_to_event_item()));
                }
                Err(err) => return Err(err),
            }
        }
        let end = self.expect(&Token::RBrace)?;
        let span = pattern.span().merge(end);
        Ok(EventMatchArm {
            pattern,
            guard,
            items,
            span,
        })
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
        while !matches!(self.peek(), Some(Token::RBrace)) && !self.at_end() {
            while self.eat(&Token::Semi).is_some() {}
            if matches!(self.peek(), Some(Token::RBrace)) {
                break;
            }
            match self.event_item() {
                Ok(item) => body.push(item),
                Err(err) if self.recovering => {
                    self.push_recovery_error(err);
                    body.push(EventItem::Error(self.recover_to_event_item()));
                }
                Err(err) => return Err(err),
            }
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
        while !matches!(self.peek(), Some(Token::RBrace)) && !self.at_end() {
            while self.eat(&Token::Semi).is_some() {}
            if matches!(self.peek(), Some(Token::RBrace)) {
                break;
            }
            match self.event_item() {
                Ok(item) => body.push(item),
                Err(err) if self.recovering => {
                    self.push_recovery_error(err);
                    body.push(EventItem::Error(self.recover_to_event_item()));
                }
                Err(err) => return Err(err),
            }
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
        // Optional `in store_name` clause: `create User in users {... }`
        let store = if self.eat(&Token::In).is_some() {
            Some(self.expect_name()?.0)
        } else {
            None
        };
        self.expect(&Token::LBrace)?;
        let mut fields = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) {
            fields.push(self.create_field()?);
        }
        let end = self.expect(&Token::RBrace)?;
        Ok(CreateBlock {
            ty,
            store,
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
}
