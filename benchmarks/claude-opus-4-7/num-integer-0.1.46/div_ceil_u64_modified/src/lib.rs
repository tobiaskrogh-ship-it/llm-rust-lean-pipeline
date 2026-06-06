//! Concrete extraction of `num_integer::div_ceil` monomorphized to `u64`.
//!
//! Source: `num-integer` 0.1.46, `src/lib.rs`.
//!
//! - The free function `pub fn div_ceil<T: Integer>(x: T, y: T) -> T` lives at
//!   line 412-415 and simply forwards to `x.div_ceil(&y)`.
//! - The `Integer for u64` implementation of `div_ceil` (inside the
//!   `impl_integer_for_usize!` macro, instantiated as `impl_integer_for_usize!(u64, ...)`)
//!   is at line 863-866:
//!
//!   ```ignore
//!   fn div_ceil(&self, other: &Self) -> Self {
//!       *self / *other + (0 != *self % *other) as Self
//!   }
//!   ```
//!
//! Inlining the trait impl into the free function and substituting `Self = u64`
//! gives the body below. No private helpers, no external-crate methods, and no
//! generics are used by this code path — the monomorphization is direct.

/// Ceiled integer division for `u64`.
///
/// Equivalent to `num_integer::div_ceil::<u64>(x, y)`. Panics when `y == 0`,
/// matching the source crate's behavior (the `/` and `%` operators panic on
/// division by zero).
pub fn div_ceil(x: u64, y: u64) -> u64 {
    let q = x / y;
    let r = x % y;
    if r == 0 { q } else { q + 1 }
}

#[cfg(test)]
mod tests {
    use super::div_ceil;

    // -----------------------------------------------------------------------
    // Tests transferred from the source crate.
    //
    // The source crate's `test_integer_u64` module (instantiated from the
    // `impl_integer_for_usize!` macro) does not include a dedicated
    // `test_div_ceil`. The closest behavioral specification in the source is
    // the doc-test on the `Integer::div_ceil` trait method (src/lib.rs lines
    // 80-91). The unsigned cases of that doc-test are transferred verbatim
    // (with the function call rewritten from `x.div_ceil(&y)` to
    // `div_ceil(x, y)`).
    // -----------------------------------------------------------------------

    /// Doc-test from `Integer::div_ceil`, unsigned-applicable cases (the signed
    /// cases involve negative numerators/denominators and don't apply to u64).
    #[test]
    fn doc_test_div_ceil_unsigned_cases() {
        assert_eq!(div_ceil(8, 3), 3);
        assert_eq!(div_ceil(1, 2), 1);
    }

    // -----------------------------------------------------------------------
    // Failure-condition (precondition) tests.
    //
    // The function's contract requires `y != 0`; calling with `y == 0` must
    // panic (the docstring explicitly promises this, matching `num_integer`).
    // This is a distinct contract clause from the postcondition tests below
    // and is not captured by any of them.
    // -----------------------------------------------------------------------

    /// Failure condition: `div_ceil(x, 0)` panics for every `x`. Covers
    /// `x == 0` (where mathematically `0/0` is undefined), a typical positive
    /// `x`, and `x == u64::MAX`.
    #[test]
    fn panics_when_divisor_is_zero() {
        for &x in &[0u64, 1, 7, u64::MAX] {
            let result = std::panic::catch_unwind(|| div_ceil(x, 0));
            assert!(
                result.is_err(),
                "div_ceil({x}, 0) did not panic but the contract requires it to"
            );
        }
    }

    // -----------------------------------------------------------------------
    // Postcondition (contract-style) tests.
    //
    // These check the defining property of div_ceil: for y > 0,
    //   div_ceil(x, y) == ceil(x / y) == (x + y - 1) / y           (no overflow)
    //   y * div_ceil(x, y) >= x  and  y * (div_ceil(x, y) - 1) < x  when q > 0
    // -----------------------------------------------------------------------

    /// Postcondition: `div_ceil(x, y)` is the smallest q such that q * y >= x.
    #[test]
    fn postcondition_smallest_q_with_qy_ge_x() {
        for x in 0u64..=64 {
            for y in 1u64..=16 {
                let q = div_ceil(x, y);
                // q * y >= x
                assert!(q * y >= x, "div_ceil({x}, {y}) = {q} but {q} * {y} < {x}");
                // (q - 1) * y < x   (only when q > 0)
                if q > 0 {
                    assert!(
                        (q - 1) * y < x,
                        "div_ceil({x}, {y}) = {q} but ({q} - 1) * {y} >= {x}"
                    );
                }
            }
        }
    }

    /// Postcondition: when `x % y == 0`, `div_ceil(x, y) == x / y`. When
    /// `x % y != 0`, `div_ceil(x, y) == x / y + 1`.
    #[test]
    fn postcondition_relation_to_floor_div() {
        for x in 0u64..=128 {
            for y in 1u64..=32 {
                let expected = if x % y == 0 { x / y } else { x / y + 1 };
                assert_eq!(div_ceil(x, y), expected, "x = {x}, y = {y}");
            }
        }
    }

    // -----------------------------------------------------------------------
    // Cross-check against the published source crate.
    //
    // This is the strongest behavioral-equivalence check available without a
    // formal proof: for every (x, y) in a sweep, our extracted function agrees
    // with `num_integer::div_ceil` from the original crate.
    // -----------------------------------------------------------------------

    /// Cross-check: extracted `div_ceil` agrees with `num_integer::div_ceil` on
    /// a sweep of small inputs.
    #[test]
    fn agrees_with_source() {
        for x in 0u64..=64 {
            for y in 1u64..=64 {
                assert_eq!(
                    div_ceil(x, y),
                    num_integer::div_ceil(x, y),
                    "extracted disagrees with source at ({x}, {y})"
                );
            }
        }
    }

    /// Cross-check: extracted `div_ceil` agrees with `num_integer::div_ceil` at
    /// boundary values (max, near-max, powers of two, and 1).
    #[test]
    fn agrees_with_source_at_boundaries() {
        let interesting: &[u64] = &[
            0,
            1,
            2,
            3,
            4,
            7,
            8,
            15,
            16,
            255,
            256,
            (1u64 << 31) - 1,
            1u64 << 31,
            (1u64 << 32) - 1,
            1u64 << 32,
            (1u64 << 63) - 1,
            1u64 << 63,
            u64::MAX - 1,
            u64::MAX,
        ];
        for &x in interesting {
            for &y in interesting {
                if y == 0 {
                    continue;
                }
                assert_eq!(
                    div_ceil(x, y),
                    num_integer::div_ceil(x, y),
                    "extracted disagrees with source at ({x}, {y})"
                );
            }
        }
    }
}
