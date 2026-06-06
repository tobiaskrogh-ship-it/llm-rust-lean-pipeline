//! `trailing_zeros_u64` — a minimal single-`while`-loop reference example.
//!
//! Counts the number of trailing (low-order) zero bits of a `u64`, with the
//! convention `trailing_zeros_u64(0) == 64`. It is a shift-and-count loop:
//! shift the value right one bit at a time while the low bit is zero,
//! counting the shifts. The loop terminates because the working value `y`
//! strictly decreases — in fact halves — every iteration and stays non-zero.
//!
//! This crate exists as a proof-pattern reference: a single `while` loop
//! walked by a bit-level measure (`y` as a Nat), which is the helper shape
//! Stein's binary GCD depends on.

/// Number of trailing zero bits of `x`; `trailing_zeros_u64(0) == 64`.
///
/// For `x != 0` the result `r` satisfies: `r < 64`, `2^r` divides `x`,
/// and bit `r` of `x` is set (so `r` is the position of the lowest set
/// bit and `x` is not divisible by `2^(r + 1)`).
pub fn trailing_zeros_u64(x: u64) -> u32 {
    if x == 0 {
        return 64;
    }
    let mut y = x;
    let mut count: u32 = 0;
    while y & 1 == 0 {
        y >>= 1;
        count = count + 1;
    }
    count
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Hand-computed values, including the `x == 0` convention.
    #[test]
    fn known_values() {
        assert_eq!(trailing_zeros_u64(0), 64);
        assert_eq!(trailing_zeros_u64(1), 0);
        assert_eq!(trailing_zeros_u64(2), 1);
        assert_eq!(trailing_zeros_u64(3), 0);
        assert_eq!(trailing_zeros_u64(4), 2);
        assert_eq!(trailing_zeros_u64(8), 3);
        assert_eq!(trailing_zeros_u64(12), 2);
        assert_eq!(trailing_zeros_u64(1u64 << 63), 63);
    }

    /// Postcondition (range): for a non-zero input the result is below 64.
    #[test]
    fn result_below_64_when_nonzero() {
        for x in 1u64..=300 {
            assert!(trailing_zeros_u64(x) < 64);
        }
    }

    /// Postcondition (divisibility): `2^result` divides `x`.
    #[test]
    fn power_of_two_divides() {
        for x in 1u64..=300 {
            let r = trailing_zeros_u64(x);
            assert_eq!(x % (1u64 << r), 0);
        }
    }

    /// Postcondition (exactness): bit `result` of `x` is set, so `x` is
    /// not divisible by `2^(result + 1)`.
    #[test]
    fn lowest_set_bit_is_at_result() {
        for x in 1u64..=300 {
            let r = trailing_zeros_u64(x);
            assert_eq!((x >> r) & 1, 1);
        }
    }

    /// Property (pointwise sharpness across all bit positions): for every
    /// `k` in `0..64`, the input `1u64 << k` has exactly `k` trailing zeros.
    /// This pins the function down on the powers-of-two diagonal across the
    /// full u64 bit range — coverage that the `1..=300` loops above miss.
    #[test]
    fn property_powers_of_two_exact() {
        for k in 0u32..64 {
            assert_eq!(trailing_zeros_u64(1u64 << k), k);
        }
    }

    /// Property (joint contract on diverse high-bit inputs): for a broad
    /// pseudo-random sample spanning the full u64 range, the three
    /// postconditions (range `r < 64`, divisibility `2^r | x`, exactness
    /// bit `r` set) all hold simultaneously. This stresses the contract on
    /// inputs the small-range loops above never reach.
    #[test]
    fn property_contract_diverse_inputs() {
        // Deterministic LCG (Numerical Recipes) to sample u64 widely without
        // a dev-dependency. Seeds chosen to mix high and low bits.
        let mut state: u64 = 0x9E37_79B9_7F4A_7C15;
        for _ in 0..2000 {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            // Force nonzero; bias toward varied trailing-zero counts by
            // occasionally masking off low bits.
            let shift = (state >> 58) as u32 % 64;
            let x = (state | 1).wrapping_shl(shift);
            if x == 0 {
                continue;
            }
            let r = trailing_zeros_u64(x);
            // (range)
            assert!(r < 64, "range violated: x={:#x} r={}", x, r);
            // (divisibility): 2^r divides x
            assert_eq!(x % (1u64 << r), 0, "divisibility violated: x={:#x} r={}", x, r);
            // (exactness): bit r of x is set
            assert_eq!((x >> r) & 1, 1, "exactness violated: x={:#x} r={}", x, r);
        }

        // Explicit edge cases: u64::MAX and "all but lowest k bits" patterns.
        assert_eq!(trailing_zeros_u64(u64::MAX), 0);
        for k in 0u32..64 {
            // A value whose lowest set bit is exactly at position k, with
            // arbitrary higher bits set (the full upper mask).
            let x = (!0u64) << k;
            let r = trailing_zeros_u64(x);
            assert_eq!(r, k);
            assert_eq!(x % (1u64 << r), 0);
            assert_eq!((x >> r) & 1, 1);
        }
    }
}
