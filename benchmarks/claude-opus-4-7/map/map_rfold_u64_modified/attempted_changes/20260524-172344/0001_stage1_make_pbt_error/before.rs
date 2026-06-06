//! Extracted from
//! `core::iter::adapters::map::<impl DoubleEndedIterator for Map<I, F>>::rfold`.
//!
//! Original:
//! ```ignore
//! fn rfold<Acc, G>(self, init: Acc, g: G) -> Acc
//! where
//!     G: FnMut(Acc, Self::Item) -> Acc,
//! {
//!     self.iter.rfold(init, map_fold(self.f, g))
//! }
//! ```
//!
//! Monomorphized with `I = core::ops::Range<u64>`, `F = fn(u64) -> u64`, and
//! `Acc = u64`. The private helper `map_fold` is inlined below.

use core::ops::Range;

/// Concrete monomorphization of `core::iter::adapters::map::Map<I, F>`.
pub struct Map {
    pub iter: Range<u64>,
    pub f: fn(u64) -> u64,
}

/// Inlined private helper `map_fold` from
/// `core::iter::adapters::map::map_fold`, monomorphized to `u64`.
fn map_fold(
    mut f: impl FnMut(u64) -> u64,
    mut g: impl FnMut(u64, u64) -> u64,
) -> impl FnMut(u64, u64) -> u64 {
    move |acc, elt| g(acc, f(elt))
}

impl Map {
    /// Consume the `Map` from the back by folding all elements through `g`
    /// after applying the inner mapper.
    pub fn rfold(self, init: u64, g: impl FnMut(u64, u64) -> u64) -> u64 {
        self.iter.rfold(init, map_fold(self.f, g))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // No direct source test for `Map::rfold` alone exists; the closest is
    // `test_map_try_folds` which uses `try_rfold`. We mirror the structural
    // assertion (mapped rfold == shifted-range rfold).
    #[test]
    fn rfold_matches_shifted_rfold() {
        let g = |acc: u64, x: u64| 2 * acc + x;
        let mapped = Map { iter: 0..10, f: |x| x + 3 }.rfold(7, g);
        let unmapped: u64 = (3..13u64).rfold(7, g);
        assert_eq!(mapped, unmapped);
    }

    // Mirror of `test_double_ended_map` exercising the back end: the rfold
    // must equal the fold for an associative-commutative operation.
    #[test]
    fn rfold_equals_fold_for_addition() {
        let g = |a: u64, b: u64| a + b;
        let m_fwd = Map { iter: 1..7, f: |x| x * 2 };
        let m_rev = Map { iter: 1..7, f: |x| x * 2 };
        // Compute fwd by hand: 2+4+6+8+10+12 = 42.
        let fwd: u64 = m_fwd.iter.map(m_fwd.f).fold(0, g);
        let rev = m_rev.rfold(0, g);
        assert_eq!(fwd, 42);
        assert_eq!(rev, 42);
    }
}
