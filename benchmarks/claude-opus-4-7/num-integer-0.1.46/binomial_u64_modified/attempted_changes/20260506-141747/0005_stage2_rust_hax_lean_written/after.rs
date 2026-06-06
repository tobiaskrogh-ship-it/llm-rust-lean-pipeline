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
//!     the one-level tail recursion that swaps `k` for `n - k` so the
//!     binomial inner loop iterates at most `min(k, n - k) + 1` times.
//!
//! Hax-compatibility notes (changes from the upstream form):
//!   * `u64::trailing_zeros` is not (yet) modelled in the Hax → Lean
//!     prelude (`core_models.num.Impl_9.trailing_zeros` is undefined),
//!     so we inline it as `count_trailing_zeros_u64`. The semantics are
//!     identical — we count low zero bits by iterated `>> 1`, and return
//!     `64` for the zero input as the standard library does.
//!   * The original `binomial` body is `loop { if d > k { break; } ... }`
//!     and the original `gcd_u64` body is a `while m != n { ... }`. The
//!     Hax → Lean backend cannot extract bare `loop {}` cleanly (it emits
//!     `sorry`-bound state), and even after rewriting both as `while`
//!     loops with `loop_decreases!`, `hax_construct_pure` fails to
//!     discharge `_pureTermination` for any measure that involves the
//!     loop condition (e.g. `k - d` or `if m > n { m } else { n }`).
//!     We therefore extract both loops as tail-recursive helper functions
//!     (`gcd_u64_iter`, `binomial_iter`); Hax handles them via
//!     `partial_fixpoint` with no purity obligation on a measure.
//!     The single remaining `while` (`count_trailing_zeros_u64`) has a
//!     trivial pure measure (`v` itself, no arithmetic), so it stays.

/// Tail-recursive worker for `count_trailing_zeros_u64`. Strips trailing
/// zero bits from `v` while incrementing `count`. Used only when the
/// initial `v` is non-zero.
fn count_trailing_zeros_u64(mut v: u64) -> u32 {
    if v == 0 {
        return 64;
    }
    let mut count: u32 = 0;
    while v & 1 == 0 {
        hax_lib::loop_decreases!(v);
        v = v >> 1;
        count = count + 1;
    }
    count
}

/// Tail-recursive worker for `gcd_u64`. The inputs `m` and `n` must both
/// be odd and non-zero; the recursion preserves that invariant.
fn gcd_u64_iter(m: u64, n: u64) -> u64 {
    if m == n {
        m
    } else if m > n {
        let m_diff = m - n;
        let m_odd = m_diff >> count_trailing_zeros_u64(m_diff);
        gcd_u64_iter(m_odd, n)
    } else {
        let n_diff = n - m;
        let n_odd = n_diff >> count_trailing_zeros_u64(n_diff);
        gcd_u64_iter(m, n_odd)
    }
}

/// Greatest common divisor on `u64`, Stein's binary algorithm.
///
/// Inlined from the unsigned arm of the `Integer for $T` impl macro in
/// `num-integer-0.1.46/src/lib.rs` lines 870–895. The `while m != n {}`
/// body has been factored into the tail-recursive `gcd_u64_iter` for
/// Hax compatibility (see crate-level docs). Semantics are unchanged.
fn gcd_u64(x: u64, y: u64) -> u64 {
    let m = x;
    let n = y;
    if m == 0 || n == 0 {
        return m | n;
    }

    // find common factors of 2
    let shift = count_trailing_zeros_u64(m | n);

    // divide n and m by 2 until odd
    let m = m >> count_trailing_zeros_u64(m);
    let n = n >> count_trailing_zeros_u64(n);

    gcd_u64_iter(m, n) << shift
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

/// Tail-recursive worker for `binomial`. Computes the loop body
/// `r = multiply_and_divide(r, n, d); n -= 1; d += 1;` until `d > k`.
fn binomial_iter(r: u64, n: u64, d: u64, k: u64) -> u64 {
    if d > k {
        r
    } else {
        let r_next = multiply_and_divide(r, n, d);
        binomial_iter(r_next, n - 1, d + 1, k)
    }
}

/// Calculate the binomial coefficient C(n, k) for `u64`.
///
/// For `u64` the largest `n` for which there is no overflow for any `k`
/// is `67` (matching the table in the original `binomial` doc-comment).
///
/// Monomorphic `u64` version of `num_integer::binomial::<u64>`. The body
/// is unchanged from the source other than the type substitution and the
/// `loop {}` → `binomial_iter(...)` rewrite for Hax compatibility (see
/// crate-level docs).
pub fn binomial(n: u64, k: u64) -> u64 {
    // See http://blog.plover.com/math/choose.html for the idea.
    if k > n {
        return 0;
    }
    if k > n - k {
        return binomial(n, n - k);
    }
    binomial_iter(1, n, 1, k)
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

    #[test]
    fn symmetric_in_k() {
        for n in 0u64..50 {
            for k in 0..=n {
                assert_eq!(binomial(n, k), binomial(n, n - k));
            }
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
