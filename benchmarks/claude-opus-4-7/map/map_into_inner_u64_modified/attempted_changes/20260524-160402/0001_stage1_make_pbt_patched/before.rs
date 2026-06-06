//! Extracted from `core::iter::adapters::map::Map::into_inner`.
//!
//! Original:
//! ```ignore
//! pub(crate) fn into_inner(self) -> I {
//!     self.iter
//! }
//! ```
//!
//! Monomorphized with `I = core::ops::Range<u64>` and `F = fn(u64) -> u64`.

use core::ops::Range;

/// Concrete monomorphization of `core::iter::adapters::map::Map<I, F>`.
pub struct Map {
    pub iter: Range<u64>,
    pub f: fn(u64) -> u64,
}

impl Map {
    /// Consume the `Map`, returning the inner iterator.
    pub fn into_inner(self) -> Range<u64> {
        self.iter
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // No direct source test for `Map::into_inner`. Skill rule: write a minimum
    // of one trivial test.

    fn plus3(x: u64) -> u64 {
        x + 3
    }

    #[test]
    fn into_inner_returns_underlying_range() {
        let m = Map { iter: 0..10, f: plus3 };
        let inner = m.into_inner();
        assert_eq!(inner, 0..10);
    }

    #[test]
    fn into_inner_after_partial_consumption_preserves_position() {
        let mut m = Map { iter: 0..5, f: |x| x * 2 };
        let _ = m.iter.next();
        let _ = m.iter.next();
        let inner = m.into_inner();
        assert_eq!(inner.collect::<Vec<_>>(), vec![2u64, 3, 4]);
    }
}
