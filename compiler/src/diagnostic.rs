#![allow(unused_assignments)]

use crate::span::Span;
use miette::Diagnostic;
use thiserror::Error;

#[derive(Error, Diagnostic, Debug)]
pub enum AbideError {
    #[error(transparent)]
    #[diagnostic(transparent)]
    Lex(#[from] LexError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    Parse(#[from] ParseError),
}

#[derive(Error, Diagnostic, Debug)]
#[error("unexpected character")]
#[diagnostic(code(abide::lex::unexpected))]
pub struct LexError {
    #[source_code]
    pub src: String,
    #[label("here")]
    pub span: miette::SourceSpan,
}

impl LexError {
    pub fn new(src: &str, span: Span) -> Self {
        Self {
            src: src.to_owned(),
            span: span.into(),
        }
    }
}

#[derive(Error, Diagnostic, Debug, Clone)]
pub enum ParseError {
    #[error("expected {expected}, found {found}")]
    #[diagnostic(code(abide::parse::expected))]
    Expected {
        expected: String,
        found: String,
        #[label("here")]
        span: miette::SourceSpan,
        #[help]
        help: Option<String>,
    },

    #[error("unexpected end of input")]
    #[diagnostic(code(abide::parse::eof))]
    UnexpectedEof {
        #[label("here")]
        span: miette::SourceSpan,
    },

    #[error("{msg}")]
    #[diagnostic(code(abide::parse::error))]
    General {
        msg: String,
        #[label("{msg}")]
        span: miette::SourceSpan,
        #[help]
        help: Option<String>,
    },
}

impl ParseError {
    pub fn expected(expected: &str, found: &str, span: Span) -> Self {
        Self::Expected {
            expected: expected.to_owned(),
            found: found.to_owned(),
            span: span.into(),
            help: None,
        }
    }

    pub fn expected_with_help(expected: &str, found: &str, span: Span, help: &str) -> Self {
        Self::Expected {
            expected: expected.to_owned(),
            found: found.to_owned(),
            span: span.into(),
            help: Some(help.to_owned()),
        }
    }

    pub fn eof(span: Span) -> Self {
        Self::UnexpectedEof { span: span.into() }
    }

    pub fn general(msg: &str, span: Span) -> Self {
        Self::General {
            msg: msg.to_owned(),
            span: span.into(),
            help: None,
        }
    }

    pub fn general_with_help(msg: &str, span: Span, help: &str) -> Self {
        Self::General {
            msg: msg.to_owned(),
            span: span.into(),
            help: Some(help.to_owned()),
        }
    }
}
