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

    // The contract is small. There are no preconditions (total on (u64, u64))
    // and no failure conditions (no panic, no error, no overflow). The
    // postcondition is a single semantic claim:
    //
    //     average_ceil(x, y) == ⌈(x + y) / 2⌉
    //
    // computed in unbounded arithmetic — i.e. correct even when x + y would
    // overflow u64. Everything else (symmetry, idempotence on x == y,
    // min ≤ result ≤ max, parity of 2*result vs x+y) is derivable from this
    // postcondition and is therefore not given a separate test.

    /// Smoke tests on hand-picked inputs.
    ///
    /// Pulled from the upstream `num-integer-0.1.46/tests/average.rs` macro
    /// (`mod u64 { mod ceil { ... } }`) and from the trait's doc-example.
    /// These would catch a transposed shift, an off-by-one in the ceiling
    /// rounding, or a regression in the overflow-avoiding formula.
    #[test]
    fn concrete_cases() {
        // Standard small inputs.
        assert_eq!(average_ceil(14, 16), 15);
        assert_eq!(average_ceil(14, 17), 16); // odd sum → genuine ceiling
        assert_eq!(average_ceil(3, 10), 7);
        assert_eq!(average_ceil(4, 4), 4);    // x == y → x
        assert_eq!(average_ceil(u8::MAX as u64, 2), 129);

        // Overflow-boundary cases: x + y > u64::MAX.
        let max = u64::MAX;
        assert_eq!(average_ceil(max - 3, max - 1), max - 2);
        assert_eq!(average_ceil(max - 3, max - 2), max - 2); // odd sum
        assert_eq!(average_ceil(max, max), max);
        assert_eq!(average_ceil(max, 0), (max / 2) + 1);     // ceil of max/2
    }

    /// THE postcondition: `average_ceil(x, y) == ⌈(x + y) / 2⌉` in
    /// unbounded arithmetic. Computing the oracle in `u128` sidesteps any
    /// `u64` overflow.
    ///
    /// The sweep covers a dense small range plus the four extreme regions
    /// (near 0, near u64::MAX/2, near u64::MAX), so it pins down behavior
    /// across the full input domain — including every overflow corner.
    #[test]
    fn postcondition_ceiling_average() {
        let extremes = [
            u64::MAX,
            u64::MAX - 1,
            u64::MAX - 2,
            u64::MAX - 3,
            u64::MAX / 2,
            u64::MAX / 2 + 1,
        ];
        let xs = (0u64..200).chain(extremes.iter().copied());
        for x in xs {
            let ys = (0u64..200).chain(extremes.iter().copied());
            for y in ys {
                let sum = x as u128 + y as u128;
                let oracle = ((sum + 1) / 2) as u64; // ⌈(x + y) / 2⌉
                assert_eq!(
                    average_ceil(x, y), oracle,
                    "average_ceil({x}, {y}) = {} but oracle = {oracle}",
                    average_ceil(x, y),
                );
            }
        }
    }

    /// Behavioral equivalence with the original
    /// `num_integer::Average::average_ceil::<u64>` from which this code was
    /// extracted. Independent of the u128 oracle: catches regressions where
    /// the extraction drifted from upstream even if both happened to satisfy
    /// the postcondition test through coincidence.
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
        // Dense small sweep too.
        for x in 0u64..=64 {
            for y in 0u64..=64 {
                assert_eq!(average_ceil(x, y), x.average_ceil(&y));
            }
        }
    }
}
