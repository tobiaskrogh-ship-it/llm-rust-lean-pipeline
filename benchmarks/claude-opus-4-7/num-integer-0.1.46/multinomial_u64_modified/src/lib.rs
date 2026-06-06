//! Extracted from `num-integer` 0.1.46 (`num_integer::multinomial`),
//! monomorphized to `u64`.
//!
//! The function depends on `binomial`, which depends on `multiply_and_divide`,
//! which depends on `gcd`. All four are inlined here as private helpers,
//! monomorphized to `u64`.
//!
//! Hax-compatibility rewrites (semantics preserved; tests cover the
//! changes):
//!   * `u64::trailing_zeros()` extracts to
//!     `core_models.num.Impl_9.trailing_zeros`, which the Hax Lean
//!     prelude does not model. Replaced with a primitive
//!     shift-and-count helper `trailing_zeros_u64`, per the canonical
//!     `u64_trailing_zeros_method.rs` archive pattern (mirroring
//!     `proof_patterns/trailing_zeros_u64_modified`).
//!   * The `while m != n { ... }` outer subtract-and-strip loop in
//!     `gcd` is rewritten as tail recursion in `gcd_stein_loop`, per the
//!     recursion-preference rule. Loop depth is ≤ 64 on `u64`, well
//!     within the safe recursion-depth rule-of-thumb. Mirrors
//!     `proof_patterns/gcd_stein_u64_modified`.
//!   * The `loop { if d > k { break; } ... }` in `binomial` extracts to
//!     `rust_primitives.hax.while_loop_return` (the early-exit variant),
//!     which the Hax Lean prelude does not model
//!     (`loop_break_to_while.rs` archive). Rewritten as a tail-recursive
//!     helper `binomial_loop` carrying the loop state `(n, d, r)`. This
//!     also satisfies the recursion-preference rule (single accumulator
//!     tuple, decreasing measure `k - d + 1`, depth ≤ `k + 1` ≤ 68 for
//!     overflow-free inputs). Mirrors `proof_patterns/binomial_u64_modified`.
//!   * The `for i in k { ... }` slice iteration in `multinomial` desugars
//!     to `Iterator::next` driven from `IntoIterator::into_iter` and
//!     extracts to `core_models.iter.traits.iterator.Iterator.fold` over
//!     `core_models.iter.traits.collect.IntoIterator (RustSlice T)`,
//!     neither of which the Hax Lean prelude models
//!     (`for_loop_over_slice_to_recursion.rs` archive). Rewritten as a
//!     tail-recursive helper `multinomial_loop` indexed by `i`, carrying
//!     the running sum `p` and the accumulated product `r`. Decreasing
//!     measure: `k.len() - i`.

/// Number of trailing zero bits of `x`; `trailing_zeros_u64(0) == 64`.
///
/// Inlined replacement for `u64::trailing_zeros()`, which has no model
/// in the Hax Lean prelude.
fn trailing_zeros_u64(x: u64) -> u32 {
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

/// Tail-recursive core of Stein's binary GCD: assumes both inputs odd
/// and non-zero, and returns the GCD of the odd parts. The original
/// `while m != n { ... }` loop on the outer subtract-and-strip step is
/// replaced by structural recursion on the (m, n) state.
fn gcd_stein_loop(m: u64, n: u64) -> u64 {
    if m == n {
        m
    } else if m > n {
        let d = m - n;
        gcd_stein_loop(d >> trailing_zeros_u64(d), n)
    } else {
        let d = n - m;
        gcd_stein_loop(m, d >> trailing_zeros_u64(d))
    }
}

/// Calculates the Greatest Common Divisor (GCD) of two `u64` values, using
/// Stein's binary algorithm. Inlined from
/// `<u64 as Integer>::gcd` (via the `impl_integer_for_usize!` macro).
fn gcd(x: u64, y: u64) -> u64 {
    if x == 0 || y == 0 {
        return x | y;
    }

    // find common factors of 2
    let shift = trailing_zeros_u64(x | y);

    // divide both by 2 until odd
    let m = x >> trailing_zeros_u64(x);
    let n = y >> trailing_zeros_u64(y);

    gcd_stein_loop(m, n) << shift
}

/// Calculate `r * a / b`, avoiding overflows and fractions.
///
/// Assumes that `b` divides `r * a` evenly.
fn multiply_and_divide(r: u64, a: u64, b: u64) -> u64 {
    let g = gcd(r, b);
    r / g * (a / (b / g))
}

/// Tail-recursive form of the inner accumulator loop of `binomial`.
///
/// Carries the loop state `(n, d, r)`: at each step, we multiply the
/// running product `r` by `n / d` (mediated by `multiply_and_divide` to
/// avoid intermediate overflow), then decrement `n` and increment `d`.
/// Terminates when `d > k`, returning the accumulated `r`.
///
/// Decreasing measure: `k - d + 1` (equivalently, the bound `d <= k + 1`).
/// Depth ≤ `k + 1`, which is ≤ 68 across the overflow-free `u64` domain.
fn binomial_loop(n: u64, k: u64, d: u64, r: u64) -> u64 {
    if d > k {
        r
    } else {
        binomial_loop(n - 1, k, d + 1, multiply_and_divide(r, n, d))
    }
}

/// Calculate the binomial coefficient.
fn binomial(n: u64, k: u64) -> u64 {
    if k > n {
        return 0;
    }
    if k > n - k {
        return binomial(n, n - k);
    }
    binomial_loop(n, k, 1, 1)
}

/// Tail-recursive form of the `multinomial` slice iteration. Carries the
/// running sum `p` and the accumulated product `r`; walks `k` by index
/// `i` with decreasing measure `k.len() - i`.
fn multinomial_loop(k: &[u64], i: usize, p: u64, r: u64) -> u64 {
    if i >= k.len() {
        r
    } else {
        let p_new = p + k[i];
        multinomial_loop(k, i + 1, p_new, r * binomial(p_new, k[i]))
    }
}

/// Calculate the multinomial coefficient.
pub fn multinomial(k: &[u64]) -> u64 {
    multinomial_loop(k, 0, 0, 1)
}

#[cfg(test)]
mod tests {
    use super::{binomial, multinomial};

    #[test]
    fn test_multinomial() {
        macro_rules! check_binomial {
            ($t:ty, $k:expr) => {{
                let n: $t = $k.iter().fold(0, |acc, &x| acc + x);
                let k: &[$t] = $k;
                assert_eq!(k.len(), 2);
                assert_eq!(multinomial(k), binomial(n, k[0]));
            }};
        }

        check_binomial!(u64, &[2, 98]);
        check_binomial!(u64, &[11, 24]);
        check_binomial!(u64, &[4, 10]);

        macro_rules! check_multinomial {
            ($t:ty, $k:expr, $r:expr) => {{
                let k: &[$t] = $k;
                let expected: $t = $r;
                assert_eq!(multinomial(k), expected);
            }};
        }

        check_multinomial!(u64, &[2, 1, 2], 30);
        check_multinomial!(u64, &[2, 3, 0], 10);

        check_multinomial!(u64, &[], 1);
        check_multinomial!(u64, &[0], 1);
        check_multinomial!(u64, &[12345], 1);
    }

    /// Independent reference implementation: computes
    /// `(sum k_i)! / prod(k_i!)` by direct factorials. Only valid when the
    /// sum is small enough that `(sum)!` fits in `u64` (sum <= 20).
    fn multinomial_reference(k: &[u64]) -> u64 {
        let n: u64 = k.iter().sum();
        let mut numerator: u64 = 1;
        for i in 1..=n {
            numerator *= i;
        }
        let mut denominator: u64 = 1;
        for &x in k {
            for i in 1..=x {
                denominator *= i;
            }
        }
        // The multinomial coefficient is always an integer, so this division
        // is exact.
        numerator / denominator
    }

    /// Postcondition (boundary): `multinomial(&[])` is the empty product, 1.
    #[test]
    fn empty_slice_returns_one() {
        assert_eq!(multinomial(&[]), 1);
    }

    /// Postcondition (boundary): a singleton always returns 1, independent
    /// of its value (`n! / n! = 1`). Includes the extreme `u64::MAX` to pin
    /// down that no arithmetic on the value itself happens beyond
    /// `binomial(n, n)`.
    #[test]
    fn singleton_returns_one() {
        for n in 0u64..256 {
            assert_eq!(multinomial(&[n]), 1);
        }
        assert_eq!(multinomial(&[u64::MAX]), 1);
    }

    /// Postcondition (full spec on small inputs): `multinomial` agrees with
    /// the direct factorial-based definition on every slice of length 0..=4
    /// with each entry in `0..=5` (sum at most 20, so the reference does
    /// not overflow).
    #[test]
    fn matches_factorial_reference_on_small_inputs() {
        // length 0
        assert_eq!(multinomial(&[]), multinomial_reference(&[]));
        // length 1
        for a in 0u64..=10 {
            let k = [a];
            assert_eq!(multinomial(&k), multinomial_reference(&k));
        }
        // length 2
        for a in 0u64..=8 {
            for b in 0u64..=8 {
                let k = [a, b];
                assert_eq!(multinomial(&k), multinomial_reference(&k));
            }
        }
        // length 3
        for a in 0u64..=5 {
            for b in 0u64..=5 {
                for c in 0u64..=5 {
                    let k = [a, b, c];
                    assert_eq!(multinomial(&k), multinomial_reference(&k));
                }
            }
        }
        // length 4
        for a in 0u64..=4 {
            for b in 0u64..=4 {
                for c in 0u64..=4 {
                    for d in 0u64..=4 {
                        let k = [a, b, c, d];
                        assert_eq!(multinomial(&k), multinomial_reference(&k));
                    }
                }
            }
        }
    }

    /// Postcondition (independent on larger inputs): `multinomial` is
    /// symmetric in its argument — the result does not depend on the order
    /// of `k`. The implementation iterates left-to-right with a running
    /// sum, so symmetry is not visibly true from the code. This catches
    /// reorder-sensitive bugs even on inputs whose sum is too large for the
    /// factorial reference.
    #[test]
    fn permutation_invariance() {
        // Hand-picked tuples; results stay well below `u64::MAX`. The last
        // few have sums above 20, so they are not covered by the reference
        // test.
        let cases: &[&[u64]] = &[
            &[1, 2, 3],
            &[0, 5, 7],
            &[2, 2, 2, 2],
            &[3, 4, 5, 0, 2],
            &[10, 10, 10],
            &[15, 5, 5, 5],
            &[20, 5, 1, 1, 1],
        ];
        for &k in cases {
            let expected = multinomial(k);
            // every cyclic rotation
            let mut rotated: Vec<u64> = k.to_vec();
            for _ in 0..k.len() {
                rotated.rotate_left(1);
                assert_eq!(multinomial(&rotated), expected);
            }
            // full reversal
            let mut reversed: Vec<u64> = k.to_vec();
            reversed.reverse();
            assert_eq!(multinomial(&reversed), expected);
            // swap of the first two entries
            if k.len() >= 2 {
                let mut swapped: Vec<u64> = k.to_vec();
                swapped.swap(0, 1);
                assert_eq!(multinomial(&swapped), expected);
            }
        }
    }

    /// Failure condition: when the running sum `p = p + *i` overflows
    /// `u64`, the implementation panics on the unchecked addition. The
    /// first iteration sets `p = u64::MAX` (and `r = binomial(u64::MAX,
    /// u64::MAX) = 1`); the second iteration's `p + 1` overflows.
    #[test]
    #[should_panic]
    fn sum_overflow_panics() {
        let _ = multinomial(&[u64::MAX, 1]);
    }
}
