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

    /// Property: `into_inner` returns the inner `Range<u64>` byte-for-byte —
    /// same `start`, same `end` — and the result does not depend on `f`.
    ///
    /// This is the entire contract: there are no preconditions, no panics, no
    /// failure modes. The return type `Range<u64>` already forbids `f` from
    /// appearing in the result, so the only thing left to pin down is that the
    /// `iter` field is forwarded unchanged.
    ///
    /// The sweep covers:
    ///   - empty ranges (`start == end`),
    ///   - "reversed" empty ranges (`start > end`, still a valid `Range`),
    ///   - the `0` and `u64::MAX` boundaries,
    ///   - typical small/medium values,
    /// crossed with several distinct `f` functions to catch any implementation
    /// that consults `f` when computing the result.
    #[test]
    fn property_into_inner_returns_iter_unchanged() {
        let fs: [fn(u64) -> u64; 3] = [|x| x, plus3, |_| 42];
        let interesting = [0u64, 1, 7, 100, u64::MAX - 1, u64::MAX];
        for &start in &interesting {
            for &end in &interesting {
                for &f in &fs {
                    let m = Map { iter: start..end, f };
                    let inner = m.into_inner();
                    assert_eq!(
                        inner,
                        start..end,
                        "into_inner did not forward iter for {start}..{end}",
                    );
                }
            }
        }
    }
}
