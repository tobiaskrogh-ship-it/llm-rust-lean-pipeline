//! Concrete `u64` extraction of `num_integer::mod_floor`.
//!
//! Source: `num-integer` v0.1.46, `src/lib.rs`.
//!
//! The free function in the source crate is:
//!
//! ```ignore
//! pub fn mod_floor<T: Integer>(x: T, y: T) -> T {
//!     x.mod_floor(&y)
//! }
//! ```
//! (src/lib.rs:403)
//!
//! For unsigned integer types, the `Integer::mod_floor` impl is provided
//! by the `impl_integer_for_usize!` macro at src/lib.rs:859 as:
//!
//! ```ignore
//! fn mod_floor(&self, other: &Self) -> Self { *self % *other }
//! ```
//!
//! For `u64`, floored modulus coincides with truncated remainder because
//! both operands are non-negative, so the extracted body is simply
//! `x % y`. The function panics on `y == 0`, matching the source's
//! behavior (which inherits the panic from `%`).

/// Floored integer modulus for `u64`.
///
/// Equivalent to `num_integer::mod_floor::<u64>(x, y)`.
#[inline]
pub fn my_mod_floor(x: u64, y: u64) -> u64 {
    x % y
}

#[cfg(test)]
mod tests {
    use super::my_mod_floor;

    // Transferred from the `test_div_mod_floor` test produced by the
    // `impl_integer_for_usize!` macro in num-integer/src/lib.rs:961.
    // The original test exercised `div_floor`, `mod_floor`, and
    // `div_mod_floor` together; here we keep only the `mod_floor`
    // assertions (the others are not part of this extraction).
    #[test]
    fn test_mod_floor() {
        assert_eq!(my_mod_floor(10u64, 3u64), 1u64);
        assert_eq!(my_mod_floor(5u64, 5u64), 0u64);
        assert_eq!(my_mod_floor(3u64, 7u64), 3u64);
    }

    // Cross-check against the original `num-integer` crate on a sweep
    // of small inputs.
    #[test]
    fn agrees_with_source() {
        for x in 0u64..=80 {
            for y in 1u64..=80 {
                assert_eq!(
                    my_mod_floor(x, y),
                    num_integer::mod_floor(x, y),
                    "extracted disagrees with source at ({x}, {y})"
                );
            }
        }
    }

    // Spot-check large values near `u64::MAX`.
    #[test]
    fn agrees_with_source_large() {
        let cases: &[(u64, u64)] = &[
            (u64::MAX, 1),
            (u64::MAX, 2),
            (u64::MAX, u64::MAX),
            (u64::MAX - 1, 7),
            (1, u64::MAX),
            (0, u64::MAX),
            (1u64 << 63, 3),
        ];
        for &(x, y) in cases {
            assert_eq!(
                my_mod_floor(x, y),
                num_integer::mod_floor(x, y),
                "disagree at ({x}, {y})"
            );
        }
    }

    /// Failure condition: modulus by zero panics.
    #[test]
    #[should_panic]
    fn panics_on_zero_divisor() {
        let _ = my_mod_floor(7, 0);
    }
}
