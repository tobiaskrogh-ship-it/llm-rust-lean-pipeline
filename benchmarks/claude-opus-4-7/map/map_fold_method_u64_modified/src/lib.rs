//! Extracted from
//! `core::iter::adapters::map::<impl Iterator for Map<I, F>>::fold`.
//!
//! Original:
//! ```ignore
//! fn fold<Acc, G>(self, init: Acc, g: G) -> Acc
//! where
//!     G: FnMut(Acc, Self::Item) -> Acc,
//! {
//!     self.iter.fold(init, map_fold(self.f, g))
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

impl Map {
    /// Consume the `Map` by folding all elements through `g` after applying
    /// the inner mapper.
    ///
    /// Hax-compatible rewrite: the original used the private helper
    /// `map_fold` returning `impl FnMut(...)` and delegated to
    /// `Range::fold` (also `FnMut`-bound). Both `impl FnMut(...) -> u64`
    /// and `Range::fold`'s bound trigger Hax's "equality constraint on
    /// associated types of parent trait" error (`FnOnce::Output = u64`).
    /// We replace `Fn*` bounds with `fn(...)` pointers and inline the
    /// fold as an explicit `while` loop.
    pub fn fold(self, init: u64, g: fn(u64, u64) -> u64) -> u64 {
        let mut acc = init;
        let mut i = self.iter.start;
        let end = self.iter.end;
        while i < end {
            acc = g(acc, (self.f)(i));
            i = i + 1;
        }
        acc
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Mirror of `tests/iter/adapters/map.rs::test_map_try_folds`, adapted to
    // the (non-try) `fold` path. The source asserts that a mapped fold equals
    // the equivalent fold over a shifted range.
    #[test]
    fn fold_matches_shifted_fold() {
        let g = |acc: u64, x: u64| 2 * acc + x;
        let mapped = Map { iter: 0..10, f: |x| x + 3 }.fold(7, g);
        let unmapped: u64 = (3..13u64).fold(7, g);
        assert_eq!(mapped, unmapped);
    }

    // Mirror of `tests/iter/adapters/map.rs::test_double_ended_map`, adapted
    // to compare the forward fold with a hand-summed expected value.
    #[test]
    fn fold_sums_with_offset() {
        let m = Map { iter: 1..7, f: |x| x * 2 };
        // 2+4+6+8+10+12 = 42
        let sum = m.fold(0, |a, b| a + b);
        assert_eq!(sum, 42);
    }

    // Edge-case clause of the contract: when `iter` is empty, `f` and `g`
    // are never invoked and `init` is returned unchanged. A buggy
    // implementation that, e.g., always calls `g` once with a sentinel
    // value would be caught here.
    #[test]
    fn empty_range_returns_init() {
        let m = Map { iter: 5..5, f: |x| x.wrapping_mul(3).wrapping_add(1) };
        let result = m.fold(99, |acc, x| acc.wrapping_add(x).wrapping_add(1));
        assert_eq!(result, 99);
    }

    // Canonical postcondition: `Map { iter, f }.fold(init, g)` is observably
    // equivalent to folding the raw range with `g` composed on the left with
    // `f`, in forward order. The non-commutative `g` (it mixes `acc` and `x`
    // asymmetrically via multiplication) also pins down left-to-right
    // iteration order — a reverse-order implementation would produce a
    // different result and fail this test.
    #[test]
    fn matches_composed_fold() {
        let f: fn(u64) -> u64 = |x| x.wrapping_mul(x).wrapping_add(1);
        let g = |acc: u64, x: u64| acc.wrapping_mul(31).wrapping_add(x);
        let via_map = Map { iter: 2..15, f }.fold(0, g);
        let via_compose: u64 = (2..15u64).fold(0, |acc, x| g(acc, f(x)));
        assert_eq!(via_map, via_compose);
    }
}
