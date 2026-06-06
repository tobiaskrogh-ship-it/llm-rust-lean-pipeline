//! Extracted from
//! `core::iter::adapters::map::<impl ExactSizeIterator for Map<I, F>>::len`.
//!
//! Original:
//! ```ignore
//! fn len(&self) -> usize {
//!     self.iter.len()
//! }
//! ```
//!
//! Monomorphized with `I = core::ops::Range<u64>` and `F = fn(u64) -> u64`.
//!
//! Note: `Range<u64>` does not implement `ExactSizeIterator` on stable
//! (its `len` method is unstable / unavailable because a `u64` range can
//! exceed `usize` on 32-bit targets). Per the skill's "inline trait method
//! calls" rule we inline the obvious concrete body for the inner `len`:
//!     (self.iter.end - self.iter.start) as usize
//! which is the same value `ExactSizeIterator::len` would return.

use core::ops::Range;

/// Concrete monomorphization of `core::iter::adapters::map::Map<I, F>`.
pub struct Map {
    pub iter: Range<u64>,
    pub f: fn(u64) -> u64,
}

impl Map {
    /// Return the remaining length, delegating to the inner iterator's `len`
    /// (inlined as `end - start` for `Range<u64>`).
    pub fn len(&self) -> usize {
        (self.iter.end - self.iter.start) as usize
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // No direct source test for `Map::len` alone. Skill rule: write a
    // minimum of one trivial test.
    #[test]
    fn len_is_inner_len() {
        let m = Map { iter: 0..10, f: |x| x + 3 };
        assert_eq!(m.len(), 10);
    }

    #[test]
    fn len_decreases_with_consumption() {
        let mut m = Map { iter: 0..10, f: |x| x + 3 };
        assert_eq!(m.len(), 10);
        m.iter.next();
        assert_eq!(m.len(), 9);
        m.iter.next_back();
        assert_eq!(m.len(), 8);
    }

    #[test]
    fn len_is_zero_for_empty_range() {
        let m = Map { iter: 5..5, f: |x| x + 3 };
        assert_eq!(m.len(), 0);
    }
}
