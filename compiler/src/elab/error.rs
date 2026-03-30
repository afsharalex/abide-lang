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
    /// Short numeric diagnostic code (e.g., `E001`).
    pub fn code(&self) -> &'static str {
        match self {
            Self::DuplicateDecl => "E001",
            Self::UndefinedRef => "E002",
            Self::TypeMismatch => "E003",
            Self::InvalidPrime => "E004",
            Self::CyclicDefinition => "E005",
            Self::InvalidScope => "E006",
            Self::AmbiguousRef => "E007",
            Self::ParamMismatch => "E008",
            Self::InvalidDefault => "E009",
            Self::MissingField => "E010",
        }
    }

    /// One-line description of this error kind.
    pub fn title(&self) -> &'static str {
        match self {
            Self::DuplicateDecl => "duplicate declaration",
            Self::UndefinedRef => "undefined reference",
            Self::TypeMismatch => "type mismatch",
            Self::InvalidPrime => "invalid primed variable",
            Self::CyclicDefinition => "cyclic definition",
            Self::InvalidScope => "invalid scope or visibility",
            Self::AmbiguousRef => "ambiguous reference",
            Self::ParamMismatch => "parameter mismatch",
            Self::InvalidDefault => "invalid default value",
            Self::MissingField => "missing required field",
        }
    }

    /// Extended explanation of this error kind with common causes and fixes.
    pub fn explanation(&self) -> &'static str {
        match self {
            Self::DuplicateDecl => {
                "Two declarations with the same name exist in the same scope. \
                 Rename one of them, or if they are in different modules, use \
                 qualified names (Module::Name) to disambiguate."
            }
            Self::UndefinedRef => {
                "A name was referenced that does not exist in the current scope. \
                 Check spelling, ensure the declaration exists, or add a `use` \
                 import if it is in another module."
            }
            Self::TypeMismatch => {
                "An expression has a type that does not match what was expected. \
                 Check that field types, function arguments, and operator operands \
                 have compatible types."
            }
            Self::InvalidPrime => {
                "A primed variable (x') was used outside an action body, or on a \
                 name that is not a field. Primed variables represent next-state \
                 values and are only valid inside action/event bodies."
            }
            Self::CyclicDefinition => {
                "A definition refers to itself (directly or transitively), creating \
                 an infinite loop. Break the cycle by restructuring the definitions."
            }
            Self::InvalidScope => {
                "A declaration was accessed from a scope where it is not visible. \
                 Private declarations can only be accessed within their own module. \
                 Mark the declaration `pub` to make it accessible from other modules."
            }
            Self::AmbiguousRef => {
                "A name resolves to multiple declarations and cannot be \
                 disambiguated. Use a qualified name (Module::Name) to specify \
                 which declaration you mean."
            }
            Self::ParamMismatch => {
                "The number or types of arguments do not match the declaration's \
                 parameter list. Check the function/predicate signature."
            }
            Self::InvalidDefault => {
                "A field default value has an invalid type or uses an expression \
                 that is not allowed in default position."
            }
            Self::MissingField => {
                "A required field was not provided. All entity fields without \
                 defaults must be initialized."
            }
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
    /// Secondary span for multi-location diagnostics (e.g., original declaration).
    pub secondary_span: Option<Span>,
    /// Label for the secondary span.
    pub secondary_label: Option<String>,
    /// Source file for the secondary span (when different from primary file).
    pub secondary_file: Option<String>,
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
            secondary_span: None,
            secondary_label: None,
            secondary_file: None,
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
            secondary_span: None,
            secondary_label: None,
            secondary_file: None,
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

    /// Add a secondary span with label (for multi-location diagnostics).
    ///
    /// When the secondary span is in the same file as the primary, both render
    /// as miette labels. When in a different file, the secondary location is
    /// included in the label text (miette can only render spans against one source).
    #[must_use]
    pub fn with_secondary(mut self, span: Span, label: impl Into<String>) -> Self {
        self.secondary_span = Some(span);
        self.secondary_label = Some(label.into());
        self
    }

    /// Add a secondary span with label and file (for cross-file diagnostics).
    #[must_use]
    pub fn with_secondary_in_file(
        mut self,
        span: Span,
        label: impl Into<String>,
        file: impl Into<String>,
    ) -> Self {
        self.secondary_span = Some(span);
        self.secondary_label = Some(label.into());
        self.secondary_file = Some(file.into());
        self
    }
}

impl std::fmt::Display for ElabError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "error[{}]: {}", self.kind.code(), self.message)?;
        if !self.context.is_empty() {
            write!(f, " ({})", self.context)?;
        }
        Ok(())
    }
}

impl std::error::Error for ElabError {}

impl miette::Diagnostic for ElabError {
    fn code<'a>(&'a self) -> Option<Box<dyn std::fmt::Display + 'a>> {
        Some(Box::new(format!("abide::{}", self.kind.code())))
    }

    fn help<'a>(&'a self) -> Option<Box<dyn std::fmt::Display + 'a>> {
        if let Some(ref h) = self.help {
            Some(Box::new(h.clone()) as Box<dyn std::fmt::Display>)
        } else {
            // Fall back to the error kind's explanation
            Some(Box::new(self.kind.explanation()) as Box<dyn std::fmt::Display>)
        }
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = miette::LabeledSpan> + '_>> {
        let span = self.span?;
        let label = if self.context.is_empty() {
            "here".to_string()
        } else {
            self.context.clone()
        };
        let primary = miette::LabeledSpan::new(Some(label), span.start, span.end - span.start);

        if let (Some(sec_span), Some(sec_label)) = (self.secondary_span, &self.secondary_label) {
            // Only render secondary as a miette label if it's in the same file.
            // Cross-file secondary spans can't be rendered against the primary source;
            // they're folded into help text by report_elab_errors instead.
            let same_file = match (&self.file, &self.secondary_file) {
                (Some(f1), Some(f2)) => f1 == f2,
                // Both untagged or secondary untagged → assumed same file
                (None | Some(_), None) => true,
                (None, Some(_)) => false,
            };
            if same_file {
                Some(Box::new(
                    [
                        primary,
                        miette::LabeledSpan::new(
                            Some(sec_label.clone()),
                            sec_span.start,
                            sec_span.end - sec_span.start,
                        ),
                    ]
                    .into_iter(),
                ))
            } else {
                // Cross-file: only render primary label
                Some(Box::new(std::iter::once(primary)))
            }
        } else {
            Some(Box::new(std::iter::once(primary)))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use miette::Diagnostic;

    #[test]
    fn error_code_format() {
        assert_eq!(ErrorKind::DuplicateDecl.code(), "E001");
        assert_eq!(ErrorKind::UndefinedRef.code(), "E002");
        assert_eq!(ErrorKind::TypeMismatch.code(), "E003");
        assert_eq!(ErrorKind::InvalidPrime.code(), "E004");
        assert_eq!(ErrorKind::CyclicDefinition.code(), "E005");
        assert_eq!(ErrorKind::InvalidScope.code(), "E006");
    }

    #[test]
    fn display_includes_error_code() {
        let err = ElabError::new(ErrorKind::DuplicateDecl, "duplicate 'Foo'", "");
        let text = format!("{err}");
        assert!(text.starts_with("error[E001]:"), "got: {text}");
        assert!(text.contains("duplicate 'Foo'"), "got: {text}");
    }

    #[test]
    fn miette_code_includes_prefix() {
        let err = ElabError::new(ErrorKind::UndefinedRef, "unknown 'Bar'", "");
        let code = err.code().unwrap().to_string();
        assert_eq!(code, "abide::E002");
    }

    #[test]
    fn miette_help_falls_back_to_explanation() {
        let err = ElabError::new(ErrorKind::InvalidPrime, "x' outside action", "");
        let help = err.help().unwrap().to_string();
        assert!(help.contains("primed variable"), "got: {help}");
    }

    #[test]
    fn miette_help_uses_explicit_when_set() {
        let err =
            ElabError::new(ErrorKind::UndefinedRef, "unknown", "").with_help("did you mean 'Foo'?");
        let help = err.help().unwrap().to_string();
        assert_eq!(help, "did you mean 'Foo'?");
    }

    #[test]
    fn single_span_produces_one_label() {
        let err = ElabError::with_span(
            ErrorKind::DuplicateDecl,
            "duplicate",
            "here",
            Span { start: 10, end: 20 },
        );
        let labels: Vec<_> = err.labels().unwrap().collect();
        assert_eq!(labels.len(), 1);
    }

    #[test]
    fn same_file_secondary_produces_two_labels() {
        let err = ElabError::with_span(
            ErrorKind::DuplicateDecl,
            "duplicate 'X'",
            "duplicate here",
            Span { start: 50, end: 60 },
        )
        .in_file("a.abide".to_owned())
        .with_secondary(Span { start: 10, end: 20 }, "first declared here");
        // secondary_file is None → same file as primary
        let labels: Vec<_> = err.labels().unwrap().collect();
        assert_eq!(
            labels.len(),
            2,
            "same-file secondary should produce 2 labels"
        );
    }

    #[test]
    fn cross_file_secondary_produces_one_label() {
        let err = ElabError::with_span(
            ErrorKind::DuplicateDecl,
            "duplicate 'X'",
            "duplicate here",
            Span { start: 50, end: 60 },
        )
        .in_file("a.abide".to_owned())
        .with_secondary_in_file(
            Span { start: 10, end: 20 },
            "first declared here",
            "b.abide",
        );
        let labels: Vec<_> = err.labels().unwrap().collect();
        assert_eq!(
            labels.len(),
            1,
            "cross-file secondary should produce only 1 label (primary)"
        );
    }

    #[test]
    fn error_kind_has_title_and_explanation() {
        for kind in [
            ErrorKind::DuplicateDecl,
            ErrorKind::UndefinedRef,
            ErrorKind::TypeMismatch,
            ErrorKind::InvalidPrime,
            ErrorKind::CyclicDefinition,
            ErrorKind::InvalidScope,
            ErrorKind::AmbiguousRef,
            ErrorKind::ParamMismatch,
            ErrorKind::InvalidDefault,
            ErrorKind::MissingField,
        ] {
            assert!(!kind.title().is_empty(), "{kind:?} has empty title");
            assert!(
                !kind.explanation().is_empty(),
                "{kind:?} has empty explanation"
            );
        }
    }
}
