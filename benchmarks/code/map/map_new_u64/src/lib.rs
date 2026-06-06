//! Extracted from `core::iter::adapters::map::Map::new`.
//!
//! Original:
//! ```ignore
//! pub(in crate::iter) fn new(iter: I, f: F) -> Map<I, F> {
//!     Map { iter, f }
//! }
//! ```
//!
//! Monomorphized with `I = core::ops::Range<u64>` and `F = fn(u64) -> u64`.

use core::ops::Range;

/// Concrete monomorphization of `core::iter::adapters::map::Map<I, F>`.
#[derive(Clone)]
pub struct Map {
    pub iter: Range<u64>,
    pub f: fn(u64) -> u64,
}

impl Map {
    /// Construct a new `Map` wrapping `iter` with mapper `f`.
    pub fn new(iter: Range<u64>, f: fn(u64) -> u64) -> Map {
        Map { iter, f }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // No dedicated source test for `Map::new` exists — it is exercised
    // implicitly through `Iterator::map` in `tests/iter/adapters/map.rs`.
    // We write the minimum-one-trivial-test required by the skill.

    fn plus3(x: u64) -> u64 {
        x + 3
    }

    #[test]
    fn map_new_stores_fields() {
        let m = Map::new(0..10, plus3);
        assert_eq!(m.iter, 0..10);
        assert_eq!((m.f)(4), 7);
    }

    #[test]
    fn map_new_round_trip() {
        // Mirror the construction shape used in `test_double_ended_map`:
        //   xs.iter().map(|&x| x * -1)
        // Adapted to a Range<u64> source and a u64-safe mapper.
        let m = Map::new(1..7, |x| x * 2);
        let collected: Vec<u64> = m.iter.map(m.f).collect();
        assert_eq!(collected, vec![2, 4, 6, 8, 10, 12]);
    }
}
