//! Concrete `u64` extraction of `num_integer::binomial`.
//!
//! Source: `num-integer-0.1.46/src/lib.rs` lines 1148–1167 (`binomial`),
//! lines 1124–1128 (the private helper `multiply_and_divide`), and lines
//! 870–895 (the `Integer::gcd` impl for unsigned primitives, Stein's
//! algorithm — used inside `multiply_and_divide`).
//!
//! Monomorphization notes:
//!   * The original is generic over `T: Integer + Clone`. With `T = u64`,
//!     `T::zero()` / `T::one()` collapse to `0u64` / `1u64`, the `.clone()`
//!     calls become trivial `Copy`, and the `gcd` trait method is inlined
//!     as `gcd_u64` below.
//!   * The body otherwise matches the original line-for-line, including
//!     the one-level tail recursion that swaps `k` for `n - k` so the loop
//!     iterates at most `min(k, n - k) + 1` times.
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
//!     `gcd_u64` is rewritten as tail recursion in `gcd_stein_loop`, per
//!     the recursion-preference rule. Loop depth is ≤ 64 on `u64`, well
//!     within the safe recursion-depth rule-of-thumb.
//!     (Mirrors `proof_patterns/gcd_stein_u64_modified`.)
//!   * The `loop { if d > k { break; } ... }` in `binomial` extracts to
//!     `rust_primitives.hax.while_loop_return` (the early-exit variant),
//!     which the Hax Lean prelude does not model
//!     (`loop_break_to_while.rs` archive). Rewritten as a tail-recursive
//!     helper `binomial_loop` carrying the loop state `(n, d, r)`. This
//!     also satisfies the recursion-preference rule (single accumulator
//!     tuple, decreasing measure `k - d + 1`, depth ≤ `k + 1` ≤ 68 for
//!     overflow-free inputs).

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

/// Greatest common divisor on `u64`, Stein's binary algorithm.
///
/// Inlined from the unsigned arm of the `Integer for $T` impl macro in
/// `num-integer-0.1.46/src/lib.rs` lines 870–895.
fn gcd_u64(x: u64, y: u64) -> u64 {
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
/// Assumes that `b` divides `r * a` evenly. Inlined from
/// `num-integer-0.1.46/src/lib.rs` lines 1124–1128.
fn multiply_and_divide(r: u64, a: u64, b: u64) -> u64 {
    // See http://blog.plover.com/math/choose-2.html for the idea.
    let g = gcd_u64(r, b);
    r / g * (a / (b / g))
}

/// Tail-recursive form of the inner accumulator loop of `binomial`.
///
/// Carries the loop state `(n, d, r)`: at each step, we multiply the
/// running product `r` by `n / d` (mediated by `multiply_and_divide` to
/// avoid intermediate overflow), then decrement `n` and increment `d`.
/// Terminates when `d > k`, returning the accumulated `r`.
///
/// Decreasing measure: `k - d + 1` (or, equivalently, the bound
/// `d <= k + 1`). Depth ≤ `k + 1`, which is ≤ 68 across the
/// overflow-free `u64` domain.
fn binomial_loop(n: u64, k: u64, d: u64, r: u64) -> u64 {
    if d > k {
        r
    } else {
        binomial_loop(n - 1, k, d + 1, multiply_and_divide(r, n, d))
    }
}

/// Calculate the binomial coefficient C(n, k) for `u64`.
///
/// For `u64` the largest `n` for which there is no overflow for any `k`
/// is `67` (matching the table in the original `binomial` doc-comment).
///
/// Monomorphic `u64` version of `num_integer::binomial::<u64>`. The body
/// is unchanged from the source other than the type substitution and
/// the loop → tail-recursion rewrite above.
pub fn binomial(n: u64, k: u64) -> u64 {
    // See http://blog.plover.com/math/choose.html for the idea.
    if k > n {
        return 0;
    }
    if k > n - k {
        return binomial(n, n - k);
    }
    binomial_loop(n, k, 1, 1)
}

#[cfg(test)]
mod tests {
    use super::binomial;

    // ---- Tests transferred from `test_binomial` in
    //      num-integer-0.1.46/src/lib.rs lines 1258–1312, the `u64` arms.
    //      The original `check!($t, $x, $y, $r)` macro is reproduced
    //      monomorphized to `u64`. ----

    #[test]
    fn test_binomial_u64() {
        macro_rules! check {
            ($x:expr, $y:expr, $r:expr) => {{
                let x: u64 = $x;
                let y: u64 = $y;
                let expected: u64 = $r;
                assert_eq!(binomial(x, y), expected);
                if y <= x {
                    assert_eq!(binomial(x, x - y), expected);
                }
            }};
        }

        check!(100, 2, 4950);
        check!(35, 11, 417225900);
        check!(14, 4, 1001);
        check!(0, 0, 1);
        check!(2, 3, 0);
    }

    // ---- Equivalent of `test_iter_binomial`'s `check_binomial!(u64, 67)`
    //      arm (num-integer-0.1.46/src/lib.rs line 1254). The source uses
    //      `IterBinomial::new(n)` as an oracle; here we use Pascal's
    //      triangle, which is computed iteratively in `u64` and known to
    //      be overflow-free up to `n = 67`. ----

    #[test]
    fn pascal_oracle_up_to_n67() {
        let n_max: usize = 67;
        let mut row: Vec<u64> = vec![1];
        for n in 1..=n_max {
            let mut next = vec![0u64; n + 1];
            next[0] = 1;
            next[n] = 1;
            for k in 1..n {
                next[k] = row[k - 1] + row[k];
            }
            for k in 0..=n {
                assert_eq!(
                    binomial(n as u64, k as u64),
                    next[k],
                    "mismatch at n={n}, k={k}"
                );
            }
            row = next;
        }
    }

    // ---- Contract-style postcondition tests. ----

    #[test]
    fn k_greater_than_n_is_zero() {
        for n in 0u64..30 {
            for k in (n + 1)..=(n + 5) {
                assert_eq!(binomial(n, k), 0);
            }
        }
    }

    #[test]
    fn boundary_k_zero_and_k_eq_n() {
        for n in 0u64..50 {
            assert_eq!(binomial(n, 0), 1);
            assert_eq!(binomial(n, n), 1);
        }
    }

    // Pascal's recurrence: C(n, k) = C(n-1, k-1) + C(n-1, k) for n >= 1
    // and 1 <= k. This is the defining recurrence for binomial coefficients
    // (combined with the boundary C(n, 0) = 1 and the k > n => 0 clause).
    //
    // This is independent of the symmetry / boundary properties: a buggy
    // implementation could satisfy all boundaries and symmetry but still
    // miscompute interior cells, and would be caught here.
    //
    // Note: when k == n, the right-hand `binomial(n - 1, k)` falls into the
    // k > n branch and returns 0, which is exactly what Pascal's recurrence
    // requires for the diagonal. The bound n <= 50 keeps every term well
    // within the overflow-free range (n <= 67).
    #[test]
    fn pascal_recurrence() {
        for n in 1u64..=50 {
            for k in 1u64..=n {
                assert_eq!(
                    binomial(n, k),
                    binomial(n - 1, k - 1) + binomial(n - 1, k),
                    "Pascal's recurrence violated at (n={n}, k={k})"
                );
            }
        }
    }

    // Symmetry: C(n, k) == C(n, n - k) for k <= n.
    //
    // This is a structural property the implementation exploits — when
    // k > n - k the function recurses with the swapped argument (the line
    // `if k > n - k { return binomial(n, n - k); }`), which is how the
    // loop iteration count is bounded by `min(k, n - k) + 1`. It is also
    // an independent semantic clause: a buggy implementation that
    // satisfies the boundaries C(n,0)=1, C(n,n)=1 and the k > n branch,
    // and even Pascal's recurrence on a subset of cells, could still
    // violate symmetry on the cells in between. Bound n <= 67 stays in
    // the overflow-free range for u64.
    #[test]
    fn symmetry() {
        for n in 0u64..=67 {
            for k in 0u64..=n {
                assert_eq!(
                    binomial(n, k),
                    binomial(n, n - k),
                    "symmetry violated at (n={n}, k={k})"
                );
            }
        }
    }

    // ---- Cross-check against the original `num-integer` crate. ----

    #[test]
    fn agrees_with_source() {
        for n in 0u64..=60 {
            for k in 0u64..=60 {
                assert_eq!(
                    binomial(n, k),
                    num_integer::binomial(n, k),
                    "extracted disagrees with source at (n={n}, k={k})"
                );
            }
        }
        // Edge of overflow-free range for u64.
        for k in 0u64..=67 {
            assert_eq!(binomial(67, k), num_integer::binomial(67u64, k));
        }
    }
}
