//! Cross-crate diagnostic vocabulary.
//!
//! This module defines two parallel representations:
//!
//! - The [`Diagnostic`] struct — a serializable, format-agnostic record
//!   that flows through the compiler and out of `verify`/`emit-ir`/`qa`
//!   in JSON form for external tools (notably Invaria).
//! - The [`LexError`] / [`ParseError`] enums — `miette`-aware errors
//!   carried alongside ownership of their source string for direct
//!   terminal rendering.
//!
//! [`Diagnostic`] is the canonical surface; both error enums convert to
//! it via `to_diagnostic`.

#![allow(unused_assignments)]

use crate::span::Span;
use miette::{Diagnostic as MietteDiagnostic, LabeledSpan};
use serde::{Deserialize, Serialize};
use thiserror::Error;

/// Top-level error enum carried out of the lexer and parser entry points.
///
/// The variants are flattened into [`Diagnostic`] for serialization; this
/// enum exists so `?`-propagation through `miette`-rendered code paths
/// preserves source-context labels.
#[derive(Error, MietteDiagnostic, Debug)]
pub enum AbideError {
    /// A lexer error — see [`LexError`].
    #[error(transparent)]
    #[diagnostic(transparent)]
    Lex(#[from] LexError),

    /// A parser error — see [`ParseError`].
    #[error(transparent)]
    #[diagnostic(transparent)]
    Parse(#[from] ParseError),
}

/// Severity classification for diagnostics emitted by the compiler.
///
/// Both `Info` and `Hint` map to `miette::Severity::Advice`; the
/// distinction is preserved here for downstream consumers (LSP, JSON
/// emit) that want to render hints differently from informational notes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum DiagnosticSeverity {
    /// Hard failure — compilation cannot proceed past this point.
    Error,
    /// Non-fatal: code is suspicious but accepted.
    Warning,
    /// Informational note attached to other output.
    Info,
    /// Suggestion the user may want to apply.
    Hint,
}

impl DiagnosticSeverity {
    /// Returns `true` if this severity is [`Self::Error`].
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

/// A secondary location attached to a primary [`Diagnostic`].
///
/// Related notes are used to point at a second site that helps explain
/// the primary error — for example, the original definition when
/// reporting a redefinition, or the call site when reporting a type
/// mismatch at a function parameter.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RelatedDiagnostic {
    /// Short message describing this related location.
    pub message: String,
    /// Optional source span for the related location.
    pub span: Option<Span>,
    /// Optional file path. When rendering via `miette`, related spans
    /// from other files are dropped from the label set (a single
    /// rendered diagnostic only carries labels into one source file).
    pub file: Option<String>,
}

/// A single compiler diagnostic — error, warning, info, or hint.
///
/// `Diagnostic` is the serializable, transport-friendly form. It is the
/// type emitted by `verify --format json` and consumed by Invaria and
/// the LSP. Builder methods (`with_*`, `in_file`) consume `self` for
/// chained construction.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Diagnostic {
    /// Severity classification.
    pub severity: DiagnosticSeverity,
    /// Stable diagnostic code (`abide::lex::unexpected`, etc.), used for
    /// suppression and external indexing.
    pub code: Option<String>,
    /// Primary user-facing message.
    pub message: String,
    /// Span pointing at the offending location in `file`.
    pub span: Option<Span>,
    /// File path the diagnostic was raised against.
    pub file: Option<String>,
    /// Optional `help:` line suggesting a fix.
    pub help: Option<String>,
    /// Secondary annotations — see [`RelatedDiagnostic`].
    pub related: Vec<RelatedDiagnostic>,
}

impl Diagnostic {
    /// Constructs a fresh error diagnostic with the given message and no
    /// span, code, help, or related notes set.
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

    /// Constructs a fresh warning diagnostic with the given message.
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

    /// Attaches a stable diagnostic code (e.g. `abide::parse::expected`).
    #[must_use]
    pub fn with_code(mut self, code: impl Into<String>) -> Self {
        self.code = Some(code.into());
        self
    }

    /// Attaches the primary source span.
    #[must_use]
    pub fn with_span(mut self, span: Span) -> Self {
        self.span = Some(span);
        self
    }

    /// Records the file path this diagnostic targets.
    #[must_use]
    pub fn in_file(mut self, file: impl Into<String>) -> Self {
        self.file = Some(file.into());
        self
    }

    /// Attaches a `help:` line suggesting how the user can resolve the
    /// issue.
    #[must_use]
    pub fn with_help(mut self, help: impl Into<String>) -> Self {
        self.help = Some(help.into());
        self
    }

    /// Appends a secondary annotation pointing at another site involved
    /// in the diagnostic. See [`RelatedDiagnostic`].
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

    /// Returns `true` if this diagnostic is at error severity.
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

// Manually implementing `miette::Diagnostic` (rather than deriving)
// lets us synthesize multiple labels at render time from
// `self.span` plus each `related` entry, and drop cross-file
// related spans that would otherwise produce labels into a source
// file `miette` isn't rendering.
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

/// Collector for diagnostics produced during a single compilation
/// session.
///
/// The sink preserves insertion order until it is drained via
/// [`Self::into_sorted_deduped`], which is the canonical way to emit
/// stable, reader-friendly output: diagnostics are sorted by
/// (file, span, severity, code, message) and exact duplicates are
/// collapsed.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiagnosticSink {
    diagnostics: Vec<Diagnostic>,
}

impl DiagnosticSink {
    /// Constructs an empty sink.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Appends a single diagnostic.
    pub fn push(&mut self, diagnostic: Diagnostic) {
        self.diagnostics.push(diagnostic);
    }

    /// Appends every diagnostic from `diagnostics` in order.
    pub fn extend<I>(&mut self, diagnostics: I)
    where
        I: IntoIterator<Item = Diagnostic>,
    {
        self.diagnostics.extend(diagnostics);
    }

    /// Returns `true` if any collected diagnostic has error severity.
    /// Used as the compilation-failure signal at pipeline boundaries.
    #[must_use]
    pub fn has_errors(&self) -> bool {
        self.diagnostics.iter().any(Diagnostic::is_error)
    }

    /// Drains the sink and returns its diagnostics sorted into a stable
    /// reporting order with exact duplicates removed.
    ///
    /// The sort key is `(file, span.start, span.end, severity_rank,
    /// code, message)` so output is deterministic across runs — important
    /// for snapshot tests and for tools that diff diagnostic output.
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

/// Classifies lexer failures before they are converted into diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LexErrorKind {
    /// A byte sequence did not match any token.
    Unexpected,
    /// A decimal integer literal is syntactically valid but outside the
    /// current `int` literal range.
    IntegerOverflow,
}

impl LexErrorKind {
    #[must_use]
    pub fn message(self) -> &'static str {
        match self {
            Self::Unexpected => "unexpected character",
            Self::IntegerOverflow => "integer literal is too large for int",
        }
    }

    #[must_use]
    pub fn code(self) -> &'static str {
        match self {
            Self::Unexpected => "abide::lex::unexpected",
            Self::IntegerOverflow => "abide::lex::integer_overflow",
        }
    }

    #[must_use]
    pub fn help(self) -> Option<&'static str> {
        match self {
            Self::Unexpected => None,
            Self::IntegerOverflow => {
                Some("use a smaller integer literal or model the value with another type")
            }
        }
    }
}

impl std::fmt::Display for LexErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.message())
    }
}

/// A lexer error carrying its own copy of the source string so
/// `miette` can render the offending character in context.
///
/// Prefer [`Self::to_diagnostic`] when forwarding the error into the
/// regular [`DiagnosticSink`] pipeline.
#[derive(Error, MietteDiagnostic, Debug, Clone)]
#[error("{kind}")]
#[diagnostic(code(abide::lex::unexpected))]
pub struct LexError {
    /// Specific lexer failure class.
    pub kind: LexErrorKind,
    /// Owned source text used by `miette` for label rendering.
    #[source_code]
    pub src: String,
    /// Span pointing at the offending character.
    #[label("here")]
    pub span: miette::SourceSpan,
}

impl LexError {
    /// Constructs a `LexError` from a borrowed source string and a span.
    /// The source is cloned because `miette` needs to hold it past the
    /// lexer's lifetime.
    pub fn new(src: &str, span: Span) -> Self {
        Self {
            kind: LexErrorKind::Unexpected,
            src: src.to_owned(),
            span: span.into(),
        }
    }

    /// Constructs a lexer error for an overflowing integer literal.
    pub fn integer_overflow(src: &str, span: Span) -> Self {
        Self {
            kind: LexErrorKind::IntegerOverflow,
            src: src.to_owned(),
            span: span.into(),
        }
    }

    /// Converts this lexer error into the cross-crate [`Diagnostic`]
    /// representation (sheds the source text — the diagnostic carries
    /// only the span and code).
    #[must_use]
    pub fn to_diagnostic(&self) -> Diagnostic {
        let diagnostic = Diagnostic::error(self.kind.message())
            .with_code(self.kind.code())
            .with_span(source_span_to_span(self.span));
        if let Some(help) = self.kind.help() {
            diagnostic.with_help(help)
        } else {
            diagnostic
        }
    }
}

/// Parser-stage errors, classified by shape.
///
/// `Expected` is by far the most common — it is produced wherever the
/// hand-rolled parser fails a token-class match. `UnexpectedEof` is
/// reserved for the special case where lookahead runs off the input.
/// `General` is the escape hatch for ad hoc parse errors with custom
/// messages.
#[derive(Error, MietteDiagnostic, Debug, Clone)]
pub enum ParseError {
    /// A token-class mismatch — the parser wanted one thing, saw another.
    #[error("expected {expected}, found {found}")]
    #[diagnostic(code(abide::parse::expected))]
    Expected {
        /// Description of what the parser was looking for.
        expected: String,
        /// Description of what it found instead (token name or literal).
        found: String,
        /// Span of the offending token.
        #[label("here")]
        span: miette::SourceSpan,
        /// Optional inline suggestion (e.g. "did you mean `=`?").
        #[help]
        help: Option<String>,
    },

    /// The parser ran off the end of input while still expecting tokens.
    #[error("unexpected end of input")]
    #[diagnostic(code(abide::parse::eof))]
    UnexpectedEof {
        /// Span pointing at the position past the end of input.
        #[label("here")]
        span: miette::SourceSpan,
    },

    /// Catch-all for ad hoc parser errors that don't fit `Expected`.
    #[error("{msg}")]
    #[diagnostic(code(abide::parse::error))]
    General {
        /// Free-form error message.
        msg: String,
        /// Span the message points at.
        #[label("{msg}")]
        span: miette::SourceSpan,
        /// Optional `help:` line.
        #[help]
        help: Option<String>,
    },
}

impl ParseError {
    /// Constructs an [`Self::Expected`] error without a help hint.
    pub fn expected(expected: &str, found: &str, span: Span) -> Self {
        Self::Expected {
            expected: expected.to_owned(),
            found: found.to_owned(),
            span: span.into(),
            help: None,
        }
    }

    /// Constructs an [`Self::Expected`] error with an inline help hint.
    pub fn expected_with_help(expected: &str, found: &str, span: Span, help: &str) -> Self {
        Self::Expected {
            expected: expected.to_owned(),
            found: found.to_owned(),
            span: span.into(),
            help: Some(help.to_owned()),
        }
    }

    /// Constructs an [`Self::UnexpectedEof`] error.
    pub fn eof(span: Span) -> Self {
        Self::UnexpectedEof { span: span.into() }
    }

    /// Constructs a [`Self::General`] error with no help hint.
    pub fn general(msg: &str, span: Span) -> Self {
        Self::General {
            msg: msg.to_owned(),
            span: span.into(),
            help: None,
        }
    }

    /// Constructs a [`Self::General`] error with an inline help hint.
    pub fn general_with_help(msg: &str, span: Span, help: &str) -> Self {
        Self::General {
            msg: msg.to_owned(),
            span: span.into(),
            help: Some(help.to_owned()),
        }
    }

    /// Converts this parser error into the cross-crate [`Diagnostic`]
    /// representation, preserving the error code, message, span, and
    /// any help hint.
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
    fn diagnostic_sink_sorts_same_location_by_severity_then_code_then_message() {
        let span = Span { start: 1, end: 2 };
        let mut sink = DiagnosticSink::new();
        sink.extend([
            Diagnostic::warning("z")
                .with_code("B")
                .with_span(span)
                .in_file("a.ab"),
            Diagnostic::error("b")
                .with_code("B")
                .with_span(span)
                .in_file("a.ab"),
            Diagnostic::error("a")
                .with_code("A")
                .with_span(span)
                .in_file("a.ab"),
            Diagnostic {
                severity: DiagnosticSeverity::Hint,
                code: Some("C".to_owned()),
                message: "hint".to_owned(),
                span: Some(span),
                file: Some("a.ab".to_owned()),
                help: None,
                related: Vec::new(),
            },
            Diagnostic {
                severity: DiagnosticSeverity::Info,
                code: Some("C".to_owned()),
                message: "info".to_owned(),
                span: Some(span),
                file: Some("a.ab".to_owned()),
                help: None,
                related: Vec::new(),
            },
        ]);

        let diagnostics = sink.into_sorted_deduped();
        let severities: Vec<_> = diagnostics.iter().map(|d| d.severity).collect();
        let messages: Vec<_> = diagnostics.iter().map(|d| d.message.as_str()).collect();

        assert_eq!(
            severities,
            vec![
                DiagnosticSeverity::Error,
                DiagnosticSeverity::Error,
                DiagnosticSeverity::Warning,
                DiagnosticSeverity::Info,
                DiagnosticSeverity::Hint,
            ]
        );
        assert_eq!(messages, vec!["a", "b", "z", "info", "hint"]);
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
    fn parse_error_variants_preserve_codes_messages_spans_and_help() {
        let eof = ParseError::eof(Span { start: 9, end: 9 }).to_diagnostic();
        assert_eq!(eof.code.as_deref(), Some("abide::parse::eof"));
        assert_eq!(eof.message, "unexpected end of input");
        assert_eq!(eof.span, Some(Span { start: 9, end: 9 }));
        assert_eq!(eof.help, None);

        let general = ParseError::general_with_help(
            "expected declaration",
            Span { start: 2, end: 6 },
            "try `entity`",
        )
        .to_diagnostic();
        assert_eq!(general.code.as_deref(), Some("abide::parse::error"));
        assert_eq!(general.message, "expected declaration");
        assert_eq!(general.span, Some(Span { start: 2, end: 6 }));
        assert_eq!(general.help.as_deref(), Some("try `entity`"));

        let expected =
            ParseError::expected("identifier", "number", Span { start: 1, end: 3 }).to_diagnostic();
        assert_eq!(expected.code.as_deref(), Some("abide::parse::expected"));
        assert_eq!(expected.message, "expected identifier, found number");
        assert_eq!(expected.help, None);
    }

    #[test]
    fn lex_error_converts_to_shared_diagnostic() {
        let diagnostic = LexError::new("!", Span { start: 0, end: 1 }).to_diagnostic();
        assert_eq!(diagnostic.code.as_deref(), Some("abide::lex::unexpected"));
        assert_eq!(diagnostic.message, "unexpected character");
        assert_eq!(diagnostic.span, Some(Span { start: 0, end: 1 }));
        assert_eq!(diagnostic.help, None);
        assert!(diagnostic.is_error());

        assert_eq!(LexErrorKind::Unexpected.to_string(), "unexpected character");
        assert_eq!(LexErrorKind::Unexpected.help(), None);

        let overflow = LexError::integer_overflow("999", Span { start: 0, end: 3 }).to_diagnostic();
        assert_eq!(
            overflow.code.as_deref(),
            Some("abide::lex::integer_overflow")
        );
        assert_eq!(overflow.message, "integer literal is too large for int");
        assert_eq!(
            overflow.help.as_deref(),
            Some("use a smaller integer literal or model the value with another type")
        );
        assert_eq!(
            LexErrorKind::IntegerOverflow.to_string(),
            "integer literal is too large for int"
        );
        assert_eq!(
            LexErrorKind::IntegerOverflow.help(),
            Some("use a smaller integer literal or model the value with another type")
        );
    }

    #[test]
    fn diagnostic_builder_display_and_miette_fields_are_stable() {
        let diagnostic = Diagnostic::warning("careful")
            .with_code("abide::warn::careful")
            .with_span(Span { start: 3, end: 8 })
            .in_file("main.ab")
            .with_help("try a safer expression");

        assert_eq!(
            diagnostic.to_string(),
            "warning[abide::warn::careful]: careful"
        );
        assert!(!diagnostic.is_error());
        assert_eq!(diagnostic.severity(), Some(miette::Severity::Warning));
        assert_eq!(
            diagnostic.code().map(|code| code.to_string()),
            Some("abide::warn::careful".to_owned())
        );
        assert_eq!(
            diagnostic.help().map(|help| help.to_string()),
            Some("try a safer expression".to_owned())
        );
    }

    #[test]
    fn diagnostic_display_without_code_uses_plain_prefix() {
        assert_eq!(Diagnostic::error("boom").to_string(), "error: boom");
    }

    #[test]
    fn non_error_severities_map_to_expected_miette_severities() {
        assert_eq!(
            miette::Severity::from(DiagnosticSeverity::Info),
            miette::Severity::Advice
        );
        assert_eq!(
            miette::Severity::from(DiagnosticSeverity::Hint),
            miette::Severity::Advice
        );
        assert!(!DiagnosticSeverity::Warning.is_error());
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
        assert_eq!(labels[0].label(), Some("primary"));
        assert_eq!(labels[1].label(), Some("same file"));
        assert_eq!(labels[0].inner().offset(), 10);
        assert_eq!(labels[1].inner().offset(), 20);
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
