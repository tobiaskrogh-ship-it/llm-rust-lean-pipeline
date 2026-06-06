//! Extracted from
//! `core::iter::adapters::map::<impl ExactSizeIterator for Map<I, F>>::is_empty`.
//!
//! Original:
//! ```ignore
//! fn is_empty(&self) -> bool {
//!     self.iter.is_empty()
//! }
//! ```
//!
//! Monomorphized with `I = core::ops::Range<u64>` and `F = fn(u64) -> u64`.
//!
//! Notes:
//! - `ExactSizeIterator::is_empty` is itself an unstable method whose default
//!   body is `self.len() == 0`. Per the skill's "inline trait method calls"
//!   rule we inline that default body.
//! - `Range<u64>` does not implement `ExactSizeIterator` on stable, so the
//!   inner `len()` is itself inlined as `end - start`. The composed result is
//!   simply `start >= end` — exactly the predicate `Range::is_empty` would
//!   return (and the same body the `Iterator::next` impl uses to decide
//!   exhaustion).

use core::ops::Range;

/// Concrete monomorphization of `core::iter::adapters::map::Map<I, F>`.
pub struct Map {
    pub iter: Range<u64>,
    pub f: fn(u64) -> u64,
}

impl Map {
    /// Report whether the inner iterator is empty.
    pub fn is_empty(&self) -> bool {
        // `ExactSizeIterator::is_empty` -> `self.len() == 0`,
        // and `<Range<u64>>::len()` inlines to `end - start` (as usize).
        // The composed predicate simplifies to `start >= end`.
        self.iter.start >= self.iter.end
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // No direct source test for `Map::is_empty` alone. Skill rule: write a
    // minimum of one trivial test.
    #[test]
    fn is_empty_false_for_nonempty_range() {
        let m = Map { iter: 0..10, f: |x| x + 3 };
        assert!(!m.is_empty());
    }

    #[test]
    fn is_empty_true_for_empty_range() {
        let m = Map { iter: 5..5, f: |x| x + 3 };
        assert!(m.is_empty());
    }

    #[test]
    fn is_empty_after_full_drain() {
        let mut m = Map { iter: 0..3, f: |x| x + 1 };
        while m.iter.next().is_some() {}
        assert!(m.is_empty());
    }
}
