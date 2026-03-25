//! Diagnostic types for the Abide elaborator.

use std::fmt;

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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ElabError {
    pub kind: ErrorKind,
    pub message: String,
    pub context: String,
}

impl ElabError {
    pub fn new(kind: ErrorKind, message: impl Into<String>, context: impl Into<String>) -> Self {
        Self {
            kind,
            message: message.into(),
            context: context.into(),
        }
    }
}

impl fmt::Display for ElabError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{:?}] {}", self.kind, self.message)?;
        if !self.context.is_empty() {
            write!(f, " ({})", self.context)?;
        }
        Ok(())
    }
}
