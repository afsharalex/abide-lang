//! Diagnostic types for the Abide elaborator.
//!
//! Errors carry optional source spans for miette rendering.
//! When a span is present, errors display with source code snippets.

use crate::span::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorKind {
    DuplicateDecl,
    UndefinedRef,
    AmbiguousRef,
    TypeMismatch,
    InvalidPrime,
    ParamMismatch,
    InvalidDefault,
    InvalidScope,
    MissingField,
    CyclicDefinition,
}

impl ErrorKind {
    /// Diagnostic code for this error kind.
    pub fn code(&self) -> &'static str {
        match self {
            Self::DuplicateDecl => "abide::elab::duplicate",
            Self::UndefinedRef => "abide::elab::undefined",
            Self::AmbiguousRef => "abide::elab::ambiguous",
            Self::TypeMismatch => "abide::elab::type_mismatch",
            Self::InvalidPrime => "abide::elab::invalid_prime",
            Self::ParamMismatch => "abide::elab::param_mismatch",
            Self::InvalidDefault => "abide::elab::invalid_default",
            Self::InvalidScope => "abide::elab::invalid_scope",
            Self::MissingField => "abide::elab::missing_field",
            Self::CyclicDefinition => "abide::elab::cyclic",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ElabError {
    pub kind: ErrorKind,
    pub message: String,
    pub context: String,
    /// Source span for the primary error location.
    pub span: Option<Span>,
    /// Source file path (for multi-file diagnostic rendering).
    pub file: Option<String>,
    /// Optional help text ("did you mean?", fix suggestions).
    pub help: Option<String>,
}

impl ElabError {
    pub fn new(kind: ErrorKind, message: impl Into<String>, context: impl Into<String>) -> Self {
        Self {
            kind,
            message: message.into(),
            context: context.into(),
            span: None,
            file: None,
            help: None,
        }
    }

    /// Create an error with a source span.
    pub fn with_span(
        kind: ErrorKind,
        message: impl Into<String>,
        context: impl Into<String>,
        span: Span,
    ) -> Self {
        Self {
            kind,
            message: message.into(),
            context: context.into(),
            span: Some(span),
            file: None,
            help: None,
        }
    }

    /// Add a help message to this error.
    #[must_use]
    pub fn with_help(mut self, help: impl Into<String>) -> Self {
        self.help = Some(help.into());
        self
    }

    /// Tag this error with a source file path.
    #[must_use]
    pub fn in_file(mut self, file: impl Into<String>) -> Self {
        self.file = Some(file.into());
        self
    }
}

impl std::fmt::Display for ElabError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{:?}] {}", self.kind, self.message)?;
        if !self.context.is_empty() {
            write!(f, " ({})", self.context)?;
        }
        Ok(())
    }
}

impl std::error::Error for ElabError {}

impl miette::Diagnostic for ElabError {
    fn code<'a>(&'a self) -> Option<Box<dyn std::fmt::Display + 'a>> {
        Some(Box::new(self.kind.code()))
    }

    fn help<'a>(&'a self) -> Option<Box<dyn std::fmt::Display + 'a>> {
        self.help
            .as_ref()
            .map(|h| Box::new(h.as_str()) as Box<dyn std::fmt::Display>)
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = miette::LabeledSpan> + '_>> {
        let span = self.span?;
        let label = if self.context.is_empty() {
            "here".to_string()
        } else {
            self.context.clone()
        };
        Some(Box::new(std::iter::once(miette::LabeledSpan::new(
            Some(label),
            span.start,
            span.end - span.start,
        ))))
    }
}
