use std::fmt;

/// A half-open range `[start, end)` of UTF-8 byte offsets inside a [`SourceText`].
///
/// Roslyn measures spans in UTF-16 code units because that is what `System.String`
/// uses. Rustlyn measures them in UTF-8 bytes, which is what `str` uses; the
/// conversion to UTF-16 offsets lives at the API edge (it is only needed for LSP
/// and for compatibility output).
///
/// [`SourceText`]: crate::SourceText
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct TextSpan {
    start: u32,
    length: u32,
}

impl TextSpan {
    /// Creates a span starting at `start` that covers `length` bytes.
    #[must_use]
    pub const fn new(start: u32, length: u32) -> Self {
        Self { start, length }
    }

    /// Creates a span covering `[start, end)`.
    ///
    /// # Panics
    ///
    /// Panics if `end < start`, at the caller: bounds out of order are its
    /// mistake, and this line would say nothing of which caller made it.
    #[must_use]
    #[track_caller]
    pub const fn from_bounds(start: u32, end: u32) -> Self {
        assert!(end >= start, "end must not precede start");
        Self {
            start,
            length: end - start,
        }
    }

    /// An empty span at `position`.
    #[must_use]
    pub const fn at(position: u32) -> Self {
        Self::new(position, 0)
    }

    #[must_use]
    pub const fn start(self) -> u32 {
        self.start
    }

    #[must_use]
    pub const fn end(self) -> u32 {
        self.start + self.length
    }

    #[must_use]
    pub const fn length(self) -> u32 {
        self.length
    }

    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.length == 0
    }

    /// Whether `position` lies inside the span. The end position is excluded.
    #[must_use]
    pub const fn contains(self, position: u32) -> bool {
        position >= self.start && position < self.end()
    }

    /// Whether `other` is fully covered by this span.
    #[must_use]
    pub const fn contains_span(self, other: Self) -> bool {
        other.start >= self.start && other.end() <= self.end()
    }

    /// Whether the two spans share at least one byte.
    #[must_use]
    pub const fn overlaps_with(self, other: Self) -> bool {
        let start = max(self.start, other.start);
        let end = min(self.end(), other.end());
        start < end
    }

    /// Like [`Self::overlaps_with`], but empty spans touching an edge count as an
    /// intersection. This is the distinction Roslyn draws between `OverlapsWith`
    /// and `IntersectsWith`, and it is what lets a caret position "hit" a node.
    #[must_use]
    pub const fn intersects_with(self, other: Self) -> bool {
        other.start <= self.end() && other.end() >= self.start
    }

    /// The overlapping part of two spans, if any.
    #[must_use]
    pub const fn intersection(self, other: Self) -> Option<Self> {
        let start = max(self.start, other.start);
        let end = min(self.end(), other.end());
        if start <= end {
            Some(Self::from_bounds(start, end))
        } else {
            None
        }
    }

    /// The smallest span covering both operands.
    #[must_use]
    pub const fn union(self, other: Self) -> Self {
        Self::from_bounds(min(self.start, other.start), max(self.end(), other.end()))
    }
}

const fn min(a: u32, b: u32) -> u32 {
    if a < b { a } else { b }
}

const fn max(a: u32, b: u32) -> u32 {
    if a > b { a } else { b }
}

impl fmt::Debug for TextSpan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}..{})", self.start, self.end())
    }
}

impl fmt::Display for TextSpan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

impl From<TextSpan> for std::ops::Range<usize> {
    fn from(span: TextSpan) -> Self {
        span.start as usize..span.end() as usize
    }
}

/// A zero-based line/character pair.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default, Debug)]
pub struct LinePosition {
    pub line: u32,
    pub character: u32,
}

impl LinePosition {
    #[must_use]
    pub const fn new(line: u32, character: u32) -> Self {
        Self { line, character }
    }
}

impl fmt::Display for LinePosition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Displayed one-based, the way compilers report locations.
        write!(f, "{}:{}", self.line + 1, self.character + 1)
    }
}

/// A [`TextSpan`] projected onto line/character coordinates.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct LinePositionSpan {
    pub start: LinePosition,
    pub end: LinePosition,
}

impl LinePositionSpan {
    #[must_use]
    pub const fn new(start: LinePosition, end: LinePosition) -> Self {
        Self { start, end }
    }
}

impl fmt::Display for LinePositionSpan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}-{}", self.start, self.end)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bounds_and_accessors() {
        let span = TextSpan::from_bounds(3, 7);
        assert_eq!(span.start(), 3);
        assert_eq!(span.end(), 7);
        assert_eq!(span.length(), 4);
        assert!(!span.is_empty());
        assert!(TextSpan::at(3).is_empty());
    }

    #[test]
    fn containment() {
        let span = TextSpan::from_bounds(3, 7);
        assert!(!span.contains(2));
        assert!(span.contains(3));
        assert!(span.contains(6));
        assert!(!span.contains(7));
        assert!(span.contains_span(TextSpan::from_bounds(4, 7)));
        assert!(!span.contains_span(TextSpan::from_bounds(4, 8)));
    }

    #[test]
    fn overlap_differs_from_intersection_at_the_edges() {
        let a = TextSpan::from_bounds(3, 7);
        let b = TextSpan::from_bounds(7, 9);
        assert!(!a.overlaps_with(b));
        assert!(a.intersects_with(b));
        assert_eq!(a.intersection(b), Some(TextSpan::at(7)));
        assert_eq!(
            a.intersection(TextSpan::from_bounds(5, 9)),
            Some(TextSpan::from_bounds(5, 7))
        );
        assert_eq!(a.intersection(TextSpan::from_bounds(8, 9)), None);
    }

    #[test]
    fn union_covers_both() {
        let a = TextSpan::from_bounds(3, 7);
        let b = TextSpan::from_bounds(9, 11);
        assert_eq!(a.union(b), TextSpan::from_bounds(3, 11));
    }
}
