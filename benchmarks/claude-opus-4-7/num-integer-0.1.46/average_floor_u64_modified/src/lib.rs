//! Extracted from `num-integer` v0.1.46, function `num_integer::average_floor`,
//! monomorphized to `u64`.
//!
//! Original implementation (in `src/average.rs`):
//!
//! ```ignore
//! impl<I> Average for I
//! where
//!     I: Integer + Shr<usize, Output = I>,
//!     for<'a, 'b> &'a I:
//!         BitAnd<&'b I, Output = I> + BitOr<&'b I, Output = I> + BitXor<&'b I, Output = I>,
//! {
//!     // The Henry Gordon Dietz implementation as shown in the Hacker's Delight,
//!     // see http://aggregate.org/MAGIC/#Average%20of%20Integers
//!     #[inline]
//!     fn average_floor(&self, other: &I) -> I {
//!         (self & other) + ((self ^ other) >> 1)
//!     }
//! }
//!
//! pub fn average_floor<T: Average>(x: T, y: T) -> T {
//!     x.average_floor(&y)
//! }
//! ```
//!
//! Monomorphizing to `u64` collapses the trait machinery into a single free
//! function. Bitwise ops on `u64` are by-value (the `&u64`/`&u64` operator
//! impls in the original implementation are an artifact of the generic bound
//! `for<'a, 'b> &'a I: BitAnd<&'b I, ...>`, since `u64: Copy` we drop the
//! references). The `>> 1` corresponds to the `Shr<usize>` bound.

/// Returns the floor value of the average of `x` and `y` -- `⌊(x + y)/2⌋`.
///
/// Equivalent to `num_integer::average_floor::<u64>(x, y)`.
#[inline]
pub fn average_floor(x: u64, y: u64) -> u64 {
    (x & y) + ((x ^ y) >> 1)
}

#[cfg(test)]
mod tests {
    use super::average_floor;

    // ---- Transferred from `tests/average.rs` (`test_average!(i64, u64)`,
    //      `mod u64 { mod floor { ... } }`). The macro expansion is inlined
    //      here with the `Average::average_floor` method calls rewritten to
    //      our local free function.

    #[test]
    fn bounded() {
        assert_eq!(average_floor(14u64, 16), 15u64);
        assert_eq!(average_floor(14u64, 17), 15u64);
    }

    #[test]
    fn overflow() {
        let max = u64::MAX;
        assert_eq!(average_floor(max - 3, max - 1), max - 2);
        assert_eq!(average_floor(max - 3, max - 2), max - 3);
    }

    // ---- Doc-tests transferred from the trait method `average_floor` in
    //      `src/average.rs`. Only the unsigned (`u8::max_value()`) example is
    //      directly applicable to `u64`; the signed examples don't typecheck
    //      under `u64` and are dropped (their corresponding behavior is
    //      already covered by the `overflow` test above).

    #[test]
    fn doc_examples_unsigned() {
        // `assert_eq!(( 3).average_floor(&10),  6);` (literal at default int type,
        //  reusable for u64).
        assert_eq!(average_floor(3, 10), 6);
        // `assert_eq!(( 4).average_floor(& 4),  4);`
        assert_eq!(average_floor(4, 4), 4);
        // `assert_eq!(u8::max_value().average_floor(&2), 128);` -- promote to u64
        //  so the same algebraic identity holds.
        assert_eq!(average_floor(u8::MAX as u64, 2), 128);
    }

    // ---- Contract-style postcondition test (per the
    //      `generate_property_based_tests` skill: postconditions, not derived
    //      facts). The defining property of `average_floor` is
    //      `floor((x + y) / 2)`, and crucially it must NOT overflow even
    //      when `x + y > u64::MAX`. We check the contract at the boundary
    //      using a 128-bit reference computation.

    #[test]
    fn matches_floor_of_sum_over_two() {
        let xs: [u64; 8] = [
            0,
            1,
            2,
            42,
            1_000_000,
            (u64::MAX / 2) - 1,
            u64::MAX - 1,
            u64::MAX,
        ];
        for &x in &xs {
            for &y in &xs {
                let expected = (((x as u128) + (y as u128)) / 2) as u64;
                assert_eq!(
                    average_floor(x, y),
                    expected,
                    "average_floor({x}, {y}) should be floor((x + y)/2) = {expected}"
                );
            }
        }
    }

    // ---- Cross-check against the original `num-integer` crate as a
    //      dev-dependency. This is the strongest behavioral-equivalence
    //      check available without a formal proof: every input pair in a
    //      sweep is run through both the extracted function and
    //      `num_integer::average_floor::<u64>` and the results are required
    //      to agree.

    #[test]
    fn agrees_with_source() {
        // Small sweep
        for a in 0u64..=64 {
            for b in 0u64..=64 {
                assert_eq!(
                    average_floor(a, b),
                    num_integer::average_floor::<u64>(a, b),
                    "extracted disagrees with source at ({a}, {b})"
                );
            }
        }
        // Boundary sweep: a few "hard" inputs near u64::MAX where naive
        // (a + b)/2 would overflow.
        let edge: [u64; 10] = [
            0,
            1,
            2,
            u64::MAX / 2,
            u64::MAX / 2 + 1,
            u64::MAX - 2,
            u64::MAX - 1,
            u64::MAX,
            0xAAAA_AAAA_AAAA_AAAA,
            0x5555_5555_5555_5555,
        ];
        for &a in &edge {
            for &b in &edge {
                assert_eq!(
                    average_floor(a, b),
                    num_integer::average_floor::<u64>(a, b),
                    "extracted disagrees with source at edge ({a}, {b})"
                );
            }
        }
    }

    // ---- Property-based tests (per the `generate_property_based_tests`
    //      skill). The contract of `average_floor` reduces to a single
    //      postcondition on arbitrary `u64` inputs, with no preconditions
    //      and no failure cases (the bit-trick implementation never
    //      overflows, even when `x + y > u64::MAX`). The randomized test
    //      below pins down that one postcondition; derived facts
    //      (commutativity, idempotence on `x == y`, bounds
    //      `min(x, y) <= r <= max(x, y)`, parity, "no panic") follow from
    //      the floor-of-sum identity and are deliberately not retested.
    proptest::proptest! {
        // Postcondition: `average_floor(x, y) == floor((x + y) / 2)`,
        // where the sum is taken over the integers (NOT modulo 2^64).
        // This is the sole contract clause of `average_floor`. Computing
        // the reference value via `u128` makes the no-overflow guarantee
        // part of the assertion: any implementation that wrapped on
        // `x + y` would fail here for inputs near `u64::MAX`.
        #[test]
        fn prop_matches_floor_of_sum_over_two(x: u64, y: u64) {
            let expected = (((x as u128) + (y as u128)) / 2) as u64;
            proptest::prop_assert_eq!(average_floor(x, y), expected);
        }
    }
}
