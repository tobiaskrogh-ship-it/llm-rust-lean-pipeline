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

/// Number of trailing zero bits in a `u64`, returning `64` for `0`.
///
/// Inlined replacement for `u64::trailing_zeros`: Hax extracts
/// `.trailing_zeros()` as `core_models.num.Impl_9.trailing_zeros`, an
/// identifier that the Hax Lean prelude does not define, so `lake build`
/// fails. The loop walks the bits one at a time; for the inputs supplied
/// by Stein's algorithm below this is called only on positive values, so
/// the `x == 0` branch matches the Rust intrinsic's contract but is never
/// reached on the hot path inside `gcd_u64`.
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

/// Greatest common divisor on `u64`, Stein's binary algorithm.
///
/// Inlined from the unsigned arm of the `Integer for $T` impl macro in
/// `num-integer-0.1.46/src/lib.rs` lines 870–895. The original calls
/// `.trailing_zeros()` on `u64`, which extracts to an undefined Lean
/// identifier; we use `trailing_zeros_u64` instead.
fn gcd_u64(x: u64, y: u64) -> u64 {
    let mut m = x;
    let mut n = y;
    if m == 0 || n == 0 {
        return m | n;
    }

    // find common factors of 2
    let shift = trailing_zeros_u64(m | n);

    // divide n and m by 2 until odd
    m >>= trailing_zeros_u64(m);
    n >>= trailing_zeros_u64(n);

    while m != n {
        if m > n {
            m -= n;
            m >>= trailing_zeros_u64(m);
        } else {
            n -= m;
            n >>= trailing_zeros_u64(n);
        }
    }
    m << shift
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
    // Rewritten from `loop { if d > k { break; } ... }` to an explicit
    // `while d <= k { ... }`. Hax extracted the original `loop`/`break`
    // shape with a `sorry` placeholder in place of the loop state tuple
    // (`let ⟨d, n, r⟩ := sorry`), which `lake build` then rejected.
    while d <= k {
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
