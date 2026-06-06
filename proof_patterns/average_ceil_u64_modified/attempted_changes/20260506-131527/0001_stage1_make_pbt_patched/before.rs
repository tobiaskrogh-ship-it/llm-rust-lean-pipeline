//! Concrete `u64` extraction of `num_integer::average_ceil`.
//!
//! Source: `num-integer-0.1.46/src/average.rs` lines 60–64 (impl) and
//! lines 73–78 (free function).
//!
//! The original is implemented as a generic blanket impl over any `Integer`
//! type that supports the relevant bitwise operations. Monomorphized to `u64`
//! the algorithm collapses to a single expression — the Henry Gordon Dietz
//! "average of two integers without overflow" formula:
//!
//! ```text
//!     (x | y) - ((x ^ y) >> 1)
//! ```
//!
//! See `http://aggregate.org/MAGIC/#Average%20of%20Integers`.

/// Returns ⌈(x + y) / 2⌉ without overflow, for `u64`.
///
/// Monomorphic version of `num_integer::average_ceil::<u64>`.
#[inline]
pub fn average_ceil(x: u64, y: u64) -> u64 {
    (x | y) - ((x ^ y) >> 1)
}

#[cfg(test)]
mod tests {
    use super::average_ceil;

    // ---- Tests transferred from num-integer-0.1.46/tests/average.rs ----
    // The source uses a macro `test_average!(i64, u64)` to generate tests for
    // each integer pair. The two `u64` ceil tests below correspond to the
    // `mod u64 { mod ceil { ... } }` arms of that macro.

    #[test]
    fn bounded() {
        assert_eq!(average_ceil(14u64, 16), 15u64);
        assert_eq!(average_ceil(14u64, 17), 16u64);
    }

    #[test]
    fn overflow() {
        let max = u64::MAX;
        assert_eq!(average_ceil(max - 3, max - 1), max - 2);
        assert_eq!(average_ceil(max - 3, max - 2), max - 2);
    }

    // ---- Doc-test cases from num-integer-0.1.46/src/average.rs (the u64-
    //      compatible ones from the trait's doc example). ----

    #[test]
    fn doc_examples_u64() {
        assert_eq!(average_ceil(3, 10), 7);
        assert_eq!(average_ceil(4, 4), 4);
        // u8::MAX.average_ceil(&2) == 129 — adapted to u64
        assert_eq!(average_ceil(u8::MAX as u64, 2), 129);
    }

    // ---- Contract-style postcondition tests. ----
    //
    // average_ceil(x, y) is the ceiling of the true mathematical average
    // (x + y) / 2. Equivalently:
    //   - the result times 2 equals x + y if (x + y) is even, and x + y + 1
    //     otherwise (the "+1" accounting for the ceiling rounding);
    //   - the result is symmetric in x, y;
    //   - the result is min(x, y) ≤ result ≤ max(x, y) (both inclusive).
    //
    // These hold without overflow even when x + y exceeds u64::MAX.

    #[test]
    fn symmetric() {
        for x in 0u64..50 {
            for y in 0u64..50 {
                assert_eq!(average_ceil(x, y), average_ceil(y, x));
            }
        }
    }

    #[test]
    fn between_min_and_max() {
        for x in 0u64..50 {
            for y in 0u64..50 {
                let r = average_ceil(x, y);
                let lo = x.min(y);
                let hi = x.max(y);
                assert!(lo <= r && r <= hi, "{} not in [{}, {}]", r, lo, hi);
            }
        }
    }

    #[test]
    fn matches_ceil_of_true_average_u128() {
        // Using u128 lets us compute (x + y) / 2 with proper ceiling rounding
        // and no overflow, giving a tight oracle for average_ceil.
        for x in (0u64..200).chain([
            u64::MAX, u64::MAX - 1, u64::MAX / 2, u64::MAX / 2 + 1,
        ].into_iter()) {
            for y in (0u64..200).chain([
                u64::MAX, u64::MAX - 1, u64::MAX / 2, u64::MAX / 2 + 1,
            ].into_iter()) {
                let sum = x as u128 + y as u128;
                let oracle = ((sum + 1) / 2) as u64; // ceil((x + y) / 2)
                assert_eq!(
                    average_ceil(x, y), oracle,
                    "mismatch at ({x}, {y})"
                );
            }
        }
    }

    // ---- Cross-check against the original num-integer crate. ----
    //
    // The strongest behavioral-equivalence check: call both implementations
    // on a sweep of inputs and assert they agree. Includes some extreme
    // values to stress overflow behavior.

    #[test]
    fn agrees_with_source() {
        use num_integer::Average;
        let sample = [
            0u64, 1, 2, 3, 7, 8, 14, 15, 16, 17, 100,
            u64::MAX / 2, u64::MAX / 2 + 1,
            u64::MAX - 3, u64::MAX - 2, u64::MAX - 1, u64::MAX,
        ];
        for &x in &sample {
            for &y in &sample {
                assert_eq!(
                    average_ceil(x, y),
                    x.average_ceil(&y),
                    "extracted disagrees with source at ({x}, {y})"
                );
            }
        }

        // Dense small sweep, too.
        for x in 0u64..=64 {
            for y in 0u64..=64 {
                assert_eq!(average_ceil(x, y), x.average_ceil(&y));
            }
        }
    }
}
