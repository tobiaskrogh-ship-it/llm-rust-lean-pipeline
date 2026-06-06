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

    // === Property-based tests for the contract of `Map::rfold` ===

    // Precondition / failure clause: if `iter` is empty, no calls to `f` or
    // `g` happen and the result is exactly `init`. A buggy implementation
    // that called either closure on the empty range would panic here.
    #[test]
    fn empty_range_returns_init_without_calling_closures() {
        let panicking_f: fn(u64) -> u64 = |_| panic!("f must not be called on empty range");
        let panicking_g = |_a: u64, _x: u64| -> u64 {
            panic!("g must not be called on empty range")
        };
        for init in [0u64, 1, 42, u64::MAX] {
            for r in [0..0u64, 5..5, u64::MAX..u64::MAX] {
                let m = Map { iter: r, f: panicking_f };
                let result = m.rfold(init, panicking_g);
                assert_eq!(result, init);
            }
        }
    }

    // Main postcondition: `Map { iter, f }.rfold(init, g)` agrees with the
    // reference computation `iter.rfold(init, |a, e| g(a, f(e)))` across a
    // grid of inputs. This pins down two independent claims at once:
    //   (a) f is applied to every element before g sees it, and
    //   (b) elements are folded in right-to-left order.
    // (b) is independent of (a) because the grid includes non-commutative
    // `g`s — an implementation that traversed in the wrong direction would
    // disagree with the reference on at least one input.
    #[test]
    fn matches_iter_rfold_specification() {
        let fs: [fn(u64) -> u64; 4] = [
            |x| x,
            |x| x.wrapping_add(7),
            |x| x.wrapping_mul(3),
            |x| x ^ 0xA5A5,
        ];
        let gs: [fn(u64, u64) -> u64; 3] = [
            |a, x| a.wrapping_add(x),                  // commutative
            |a, x| a.wrapping_mul(10).wrapping_add(x), // non-commutative: pins order
            |a, x| a.wrapping_sub(x),                  // non-commutative
        ];
        let ranges: [Range<u64>; 6] = [
            0..0,   // empty
            0..1,   // singleton
            0..2,   // pair: distinguishes left-to-right vs right-to-left
            0..5,
            3..10,
            100..115,
        ];
        let inits: [u64; 3] = [0, 1, 1_000];

        for f in fs {
            for g in gs {
                for r in &ranges {
                    for init in inits {
                        let mapped = Map { iter: r.clone(), f }.rfold(init, g);
                        let reference: u64 = r.clone().rfold(init, |a, e| g(a, f(e)));
                        assert_eq!(
                            mapped, reference,
                            "mismatch on range={:?} init={}", r, init
                        );
                    }
                }
            }
        }
    }
}
