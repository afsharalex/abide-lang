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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn merge_covers_both_spans_regardless_of_order() {
        let left = Span { start: 10, end: 20 };
        let right = Span { start: 2, end: 5 };

        assert_eq!(left.merge(right), Span { start: 2, end: 20 });
        assert_eq!(right.merge(left), Span { start: 2, end: 20 });
    }

    #[test]
    fn range_conversion_preserves_half_open_bounds() {
        assert_eq!(Span::from(4..9), Span { start: 4, end: 9 });
    }

    #[test]
    fn source_span_conversion_uses_offset_and_length() {
        let source_span = miette::SourceSpan::from(Span { start: 7, end: 12 });

        assert_eq!(source_span.offset(), 7);
        assert_eq!(source_span.len(), 5);
    }

    #[test]
    fn zero_length_span_converts_to_point_source_span() {
        let source_span = miette::SourceSpan::from(Span { start: 3, end: 3 });

        assert_eq!(source_span.offset(), 3);
        assert_eq!(source_span.len(), 0);
    }
}
