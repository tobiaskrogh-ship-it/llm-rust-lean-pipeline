//! Extracted from `core::mem::copy`, monomorphized to `u64`.
//!
//! Source: `to_be_extracted/core-1.94.0/src/mem/mod.rs:994` (function `copy`).
//!
//! The source defines `copy` as:
//!
//! ```ignore
//! pub const fn copy<T: Copy>(x: &T) -> T { *x }
//! ```

/// Bitwise-copies a value.
#[inline]
pub const fn copy(x: &u64) -> u64 {
    *x
}

#[cfg(test)]
mod tests {
    use super::*;

    // Doc-test from source uses `Result<(), &i32>` and `map_err`; the closest
    // monomorphic-to-u64 analog is to verify the function reproduces the
    // pointed-to value and is usable as a function pointer.
    #[test]
    fn doctest_basic_copy() {
        let x: u64 = 1;
        let y = copy(&x);
        assert_eq!(y, 1);
        assert_eq!(x, 1); // original still readable; we only had a reference.
    }

    #[test]
    fn copy_various_u64_values() {
        assert_eq!(copy(&0u64), 0);
        assert_eq!(copy(&u64::MAX), u64::MAX);
        assert_eq!(copy(&12345u64), 12345);
        let big = 0xDEAD_BEEF_CAFE_BABEu64;
        assert_eq!(copy(&big), big);
    }

    #[test]
    fn copy_usable_as_fn_pointer() {
        // The function is useful as a `fn(&T) -> T` combinator argument.
        let f: fn(&u64) -> u64 = copy;
        let v = 99u64;
        assert_eq!(f(&v), 99);
    }

    /// Property: for every `u64` value `x`, `copy(&x) == x`.
    ///
    /// This is the function's entire contract: the returned value is bit-for-bit
    /// the value behind the reference. The test sweeps:
    ///   * all "interesting" boundary values (0, 1, MAX, MAX-1, power-of-two
    ///     boundaries, single-bit patterns, alternating-bit patterns), and
    ///   * a long deterministic linear-congruential walk through the `u64`
    ///     state space so the property is exercised on a broad sample of
    ///     inputs (not just edge cases).
    ///
    /// A buggy implementation that masked, wrapped, swapped bytes, or returned
    /// a constant on some inputs would be caught here. There is deliberately
    /// only one property test, because there is only one independent semantic
    /// claim to make about `copy`.
    #[test]
    fn prop_copy_returns_input() {
        // Edge / boundary values.
        let edges: [u64; 12] = [
            0,
            1,
            2,
            u64::MAX,
            u64::MAX - 1,
            u64::MAX / 2,
            u64::MAX / 2 + 1,
            1u64 << 32,
            (1u64 << 32) - 1,
            0xAAAA_AAAA_AAAA_AAAA, // alternating 1010…
            0x5555_5555_5555_5555, // alternating 0101…
            0xFFFF_FFFF_0000_0000,
        ];
        for &x in &edges {
            assert_eq!(copy(&x), x, "copy(&{x}) should return {x}");
        }

        // Single-bit values: cover every bit position 0..64.
        for bit in 0..64u32 {
            let x = 1u64 << bit;
            assert_eq!(copy(&x), x, "copy of single-bit value 1<<{bit} failed");
        }

        // Deterministic pseudo-random sweep using a known LCG (Numerical
        // Recipes constants) so the test is fully reproducible.
        let mut state: u64 = 0x0123_4567_89AB_CDEF;
        for _ in 0..4096 {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            let x = state;
            assert_eq!(copy(&x), x, "copy(&{x}) should return {x}");
        }
    }
}
