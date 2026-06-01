//! Byte-offset spans into source text.

use serde::{Deserialize, Serialize};

/// Half-open byte-offset range into source text: `[start, end)`.
///
/// Spans are flat byte indices, not (line, column) pairs — line/column
/// resolution is the renderer's job. A zero-length span (`start == end`)
/// represents a point location.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct Span {
    /// Start byte offset (inclusive).
    pub start: usize,
    /// End byte offset (exclusive).
    pub end: usize,
}

impl Span {
    /// Returns the smallest span covering both `self` and `other`.
    ///
    /// Used when combining child-node spans into a parent-node span during
    /// parsing and lowering.
    #[must_use]
    pub fn merge(self, other: Self) -> Self {
        Self {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}

impl From<std::ops::Range<usize>> for Span {
    fn from(range: std::ops::Range<usize>) -> Self {
        Self {
            start: range.start,
            end: range.end,
        }
    }
}

impl From<Span> for miette::SourceSpan {
    fn from(span: Span) -> Self {
        (span.start, span.end - span.start).into()
    }
}
