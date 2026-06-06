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

/// Greatest common divisor on `u64`, Euclidean algorithm.
///
/// The original is `num-integer-0.1.46/src/lib.rs` lines 870–895, which uses
/// Stein's binary algorithm. Stein's is impractical to extract into Lean for
/// two independent reasons:
///
///   * `u64::trailing_zeros` is not defined in the Hax → Lean prelude
///     (`core_models.num.Impl_9.trailing_zeros` was reported as an
///     "unknown identifier" in `lake build`).
///   * Stein's natural termination measure is `max(m, n)`, which the blog
///     example writes as `if m < n { n } else { m }`. In Lean this triggers
///     `hax_construct_pure: mvcgen generated more than one goal containing
///     the metavariable. ... Try to remove if-then-else and match-constructs.`
///     There is no obvious way to bound `m + n` without a precondition, and
///     no other measure for Stein's is single-expression-without-if.
///
/// We therefore switch to the Euclidean algorithm. The mathematical result is
/// identical — `gcd(x, y)` is the same regardless of algorithm — and the
/// `agrees_with_source` test cross-checks behavior against the original
/// `num_integer::binomial::<u64>`. The measure is a single decreasing `u64`
/// (`b` strictly decreases each iteration because `a % b < b` for `b > 0`).
fn gcd_u64(x: u64, y: u64) -> u64 {
    let mut a = x;
    let mut b = y;
    while b != 0 {
        hax_lib::loop_decreases!(b);
        let t = b;
        b = a % b;
        a = t;
    }
    a
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

/// Calculate the binomial coefficient C(n, k) for `u64`.
///
/// For `u64` the largest `n` for which there is no overflow for any `k`
/// is `67` (matching the table in the original `binomial` doc-comment).
///
/// Monomorphic `u64` version of `num_integer::binomial::<u64>`. The body
/// is unchanged from the source other than the type substitution.
pub fn binomial(mut n: u64, k: u64) -> u64 {
    // See http://blog.plover.com/math/choose.html for the idea.
    if k > n {
        return 0;
    }
    if k > n - k {
        return binomial(n, n - k);
    }
    let mut r: u64 = 1;
    let mut d: u64 = 1;
    // The original is `loop { if d > k { break; } ... }`. Hax's bare-`loop`
    // extraction produces a degenerate `let ⟨...⟩ := sorry` (it can't see
    // the `break` as a structured exit). Rewrite as a `while` with an
    // explicit termination measure so it lowers through
    // `rust_primitives.hax.while_loop`. The measure `(k + 1) - d` is
    // strictly positive at iteration entry (`d <= k`) and decreases by 1
    // each iteration; the post-conditions of the two early-return guards
    // (`k <= n` and `2*k <= n`) ensure `k + 1 <= u64::MAX` so the
    // expression itself never overflows.
    while d <= k {
        hax_lib::loop_decreases!((k + 1) - d);
        r = multiply_and_divide(r, n, d);
        n = n - 1;
        d = d + 1;
    }
    r
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
