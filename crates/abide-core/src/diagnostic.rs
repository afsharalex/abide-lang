#![allow(unused_assignments)]

use crate::span::Span;
use miette::{Diagnostic as MietteDiagnostic, LabeledSpan};
use serde::{Deserialize, Serialize};
use thiserror::Error;

#[derive(Error, MietteDiagnostic, Debug)]
pub enum AbideError {
    #[error(transparent)]
    #[diagnostic(transparent)]
    Lex(#[from] LexError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    Parse(#[from] ParseError),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum DiagnosticSeverity {
    Error,
    Warning,
    Info,
    Hint,
}

impl DiagnosticSeverity {
    #[must_use]
    pub fn is_error(self) -> bool {
        matches!(self, Self::Error)
    }
}

impl From<DiagnosticSeverity> for miette::Severity {
    fn from(value: DiagnosticSeverity) -> Self {
        match value {
            DiagnosticSeverity::Error => Self::Error,
            DiagnosticSeverity::Warning => Self::Warning,
            DiagnosticSeverity::Info => Self::Advice,
            DiagnosticSeverity::Hint => Self::Advice,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RelatedDiagnostic {
    pub message: String,
    pub span: Option<Span>,
    pub file: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Diagnostic {
    pub severity: DiagnosticSeverity,
    pub code: Option<String>,
    pub message: String,
    pub span: Option<Span>,
    pub file: Option<String>,
    pub help: Option<String>,
    pub related: Vec<RelatedDiagnostic>,
}

impl Diagnostic {
    #[must_use]
    pub fn error(message: impl Into<String>) -> Self {
        Self {
            severity: DiagnosticSeverity::Error,
            code: None,
            message: message.into(),
            span: None,
            file: None,
            help: None,
            related: Vec::new(),
        }
    }

    #[must_use]
    pub fn warning(message: impl Into<String>) -> Self {
        Self {
            severity: DiagnosticSeverity::Warning,
            code: None,
            message: message.into(),
            span: None,
            file: None,
            help: None,
            related: Vec::new(),
        }
    }

    #[must_use]
    pub fn with_code(mut self, code: impl Into<String>) -> Self {
        self.code = Some(code.into());
        self
    }

    #[must_use]
    pub fn with_span(mut self, span: Span) -> Self {
        self.span = Some(span);
        self
    }

    #[must_use]
    pub fn in_file(mut self, file: impl Into<String>) -> Self {
        self.file = Some(file.into());
        self
    }

    #[must_use]
    pub fn with_help(mut self, help: impl Into<String>) -> Self {
        self.help = Some(help.into());
        self
    }

    #[must_use]
    pub fn with_related(
        mut self,
        message: impl Into<String>,
        span: Option<Span>,
        file: Option<String>,
    ) -> Self {
        self.related.push(RelatedDiagnostic {
            message: message.into(),
            span,
            file,
        });
        self
    }

    #[must_use]
    pub fn is_error(&self) -> bool {
        self.severity.is_error()
    }
}

impl std::fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let severity = match self.severity {
            DiagnosticSeverity::Error => "error",
            DiagnosticSeverity::Warning => "warning",
            DiagnosticSeverity::Info => "info",
            DiagnosticSeverity::Hint => "hint",
        };
        if let Some(code) = &self.code {
            write!(f, "{severity}[{code}]: {}", self.message)
        } else {
            write!(f, "{severity}: {}", self.message)
        }
    }
}

impl std::error::Error for Diagnostic {}

impl MietteDiagnostic for Diagnostic {
    fn severity(&self) -> Option<miette::Severity> {
        Some(self.severity.into())
    }

    fn code<'a>(&'a self) -> Option<Box<dyn std::fmt::Display + 'a>> {
        self.code
            .as_ref()
            .map(|code| Box::new(code.clone()) as Box<dyn std::fmt::Display>)
    }

    fn help<'a>(&'a self) -> Option<Box<dyn std::fmt::Display + 'a>> {
        self.help
            .as_ref()
            .map(|help| Box::new(help.clone()) as Box<dyn std::fmt::Display>)
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan> + '_>> {
        let mut labels = Vec::new();
        if let Some(span) = self.span {
            labels.push(LabeledSpan::new_with_span(
                Some(self.message.clone()),
                miette::SourceSpan::from(span),
            ));
        }
        let same_file = self.file.as_deref();
        for related in &self.related {
            if let Some(span) = related.span {
                if related.file.as_deref().is_none() || related.file.as_deref() == same_file {
                    labels.push(LabeledSpan::new_with_span(
                        Some(related.message.clone()),
                        miette::SourceSpan::from(span),
                    ));
                }
            }
        }
        (!labels.is_empty())
            .then_some(Box::new(labels.into_iter()) as Box<dyn Iterator<Item = LabeledSpan>>)
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiagnosticSink {
    diagnostics: Vec<Diagnostic>,
}

impl DiagnosticSink {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push(&mut self, diagnostic: Diagnostic) {
        self.diagnostics.push(diagnostic);
    }

    pub fn extend<I>(&mut self, diagnostics: I)
    where
        I: IntoIterator<Item = Diagnostic>,
    {
        self.diagnostics.extend(diagnostics);
    }

    #[must_use]
    pub fn has_errors(&self) -> bool {
        self.diagnostics.iter().any(Diagnostic::is_error)
    }

    #[must_use]
    pub fn into_sorted_deduped(mut self) -> Vec<Diagnostic> {
        self.diagnostics.sort_by(|a, b| {
            (
                a.file.as_deref(),
                a.span.map(|s| s.start),
                a.span.map(|s| s.end),
                severity_rank(a.severity),
                a.code.as_deref(),
                a.message.as_str(),
            )
                .cmp(&(
                    b.file.as_deref(),
                    b.span.map(|s| s.start),
                    b.span.map(|s| s.end),
                    severity_rank(b.severity),
                    b.code.as_deref(),
                    b.message.as_str(),
                ))
        });
        self.diagnostics.dedup();
        self.diagnostics
    }
}

fn severity_rank(severity: DiagnosticSeverity) -> u8 {
    match severity {
        DiagnosticSeverity::Error => 0,
        DiagnosticSeverity::Warning => 1,
        DiagnosticSeverity::Info => 2,
        DiagnosticSeverity::Hint => 3,
    }
}

#[derive(Error, MietteDiagnostic, Debug, Clone)]
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

    #[must_use]
    pub fn to_diagnostic(&self) -> Diagnostic {
        Diagnostic::error("unexpected character")
            .with_code("abide::lex::unexpected")
            .with_span(source_span_to_span(self.span))
    }
}

#[derive(Error, MietteDiagnostic, Debug, Clone)]
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

    #[must_use]
    pub fn to_diagnostic(&self) -> Diagnostic {
        match self {
            Self::Expected {
                expected,
                found,
                span,
                help,
            } => {
                let mut diagnostic =
                    Diagnostic::error(format!("expected {expected}, found {found}"))
                        .with_code("abide::parse::expected")
                        .with_span(source_span_to_span(*span));
                if let Some(help) = help {
                    diagnostic = diagnostic.with_help(help.clone());
                }
                diagnostic
            }
            Self::UnexpectedEof { span } => Diagnostic::error("unexpected end of input")
                .with_code("abide::parse::eof")
                .with_span(source_span_to_span(*span)),
            Self::General { msg, span, help } => {
                let mut diagnostic = Diagnostic::error(msg.clone())
                    .with_code("abide::parse::error")
                    .with_span(source_span_to_span(*span));
                if let Some(help) = help {
                    diagnostic = diagnostic.with_help(help.clone());
                }
                diagnostic
            }
        }
    }
}

fn source_span_to_span(span: miette::SourceSpan) -> Span {
    let offset = span.offset();
    let len = span.len();
    Span {
        start: offset,
        end: offset + len,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn diagnostic_sink_sorts_and_dedups() {
        let mut sink = DiagnosticSink::new();
        sink.push(
            Diagnostic::warning("later")
                .with_code("W001")
                .with_span(Span { start: 10, end: 12 })
                .in_file("b.ab"),
        );
        sink.push(
            Diagnostic::error("first")
                .with_code("E001")
                .with_span(Span { start: 1, end: 2 })
                .in_file("a.ab"),
        );
        sink.push(
            Diagnostic::error("first")
                .with_code("E001")
                .with_span(Span { start: 1, end: 2 })
                .in_file("a.ab"),
        );

        let diagnostics = sink.into_sorted_deduped();
        assert_eq!(diagnostics.len(), 2);
        assert_eq!(diagnostics[0].message, "first");
        assert_eq!(diagnostics[1].message, "later");
    }

    #[test]
    fn parse_error_converts_to_shared_diagnostic() {
        let diagnostic = ParseError::expected_with_help(
            "type name",
            "}",
            Span { start: 4, end: 5 },
            "try a type name here",
        )
        .to_diagnostic();
        assert_eq!(diagnostic.code.as_deref(), Some("abide::parse::expected"));
        assert_eq!(diagnostic.help.as_deref(), Some("try a type name here"));
        assert_eq!(diagnostic.span, Some(Span { start: 4, end: 5 }));
    }

    #[test]
    fn lex_error_converts_to_shared_diagnostic() {
        let diagnostic = LexError::new("!", Span { start: 0, end: 1 }).to_diagnostic();
        assert_eq!(diagnostic.code.as_deref(), Some("abide::lex::unexpected"));
        assert_eq!(diagnostic.message, "unexpected character");
        assert_eq!(diagnostic.span, Some(Span { start: 0, end: 1 }));
        assert!(diagnostic.is_error());
    }

    #[test]
    fn diagnostic_labels_only_include_same_file_related_spans() {
        let diagnostic = Diagnostic::error("primary")
            .with_span(Span { start: 10, end: 12 })
            .in_file("a.ab")
            .with_related(
                "same file",
                Some(Span { start: 20, end: 22 }),
                Some("a.ab".to_owned()),
            )
            .with_related(
                "other file",
                Some(Span { start: 30, end: 32 }),
                Some("b.ab".to_owned()),
            );

        let labels: Vec<_> = diagnostic.labels().expect("labels should exist").collect();
        assert_eq!(
            labels.len(),
            2,
            "cross-file related span should not render as a label"
        );
    }

    #[test]
    fn diagnostic_sink_reports_error_presence() {
        let mut sink = DiagnosticSink::new();
        sink.push(Diagnostic::warning("warn"));
        assert!(
            !sink.has_errors(),
            "warning-only sink should not report errors"
        );
        sink.push(Diagnostic::error("err"));
        assert!(
            sink.has_errors(),
            "sink should report errors after an error diagnostic"
        );
    }
}
