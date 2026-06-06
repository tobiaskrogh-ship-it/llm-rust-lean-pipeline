//! Extracted from `num-integer` 0.1.46 (`num_integer::multinomial`),
//! monomorphized to `u64`.
//!
//! The function depends on `binomial`, which depends on `multiply_and_divide`,
//! which depends on `gcd`. All four are inlined here as private helpers,
//! monomorphized to `u64`.

/// Greatest common divisor of two `u64` values.
///
/// Original `num_integer::Integer::gcd` uses Stein's binary algorithm,
/// which calls `u64::trailing_zeros` and contains a `while m != n` loop
/// whose natural termination measure (`max(m, n)`, `m | n`, …) requires
/// arithmetic over the two mutable variables. Hax's
/// `hax_construct_pure` tactic, used to discharge `pureTermination` /
/// `pureCond` obligations of `rust_primitives.hax.while_loop`, fails when
/// the measure expression itself involves `if-then-else` or compound
/// monadic operations (the tactic's error message: "mvcgen generated more
/// than one goal containing the metavariable. This is currently
/// unsupported. Try to remove if-then-else and match-constructs.").
/// Additionally, `u64::trailing_zeros` extracts to
/// `core_models.num.Impl_9.trailing_zeros`, which is undefined in the Lean
/// prelude.
///
/// We replace the binary algorithm with the standard Euclidean algorithm.
/// It computes the same value (the GCD), uses no `trailing_zeros`, and
/// has a one-variable termination measure (`b`), so the
/// `hax_construct_pure` tactic discharges the obligations cleanly. The
/// observable result on every input pair is the same.
fn gcd(x: u64, y: u64) -> u64 {
    let mut a = x;
    let mut b = y;
    while b != 0 {
        // `b` strictly decreases each iteration: after `b = a % b`, the
        // new `b` is at most `b - 1` (since `a % b < b` whenever `b > 0`).
        // Single-variable measure — no arithmetic, no if-then-else.
        hax_lib::loop_decreases!(b);
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

/// Calculate `r * a / b`, avoiding overflows and fractions.
///
/// Assumes that `b` divides `r * a` evenly.
fn multiply_and_divide(r: u64, a: u64, b: u64) -> u64 {
    let g = gcd(r, b);
    r / g * (a / (b / g))
}

/// Calculate the binomial coefficient.
fn binomial(n: u64, k: u64) -> u64 {
    if k > n {
        return 0;
    }
    // Original used `if k > n - k { return binomial(n, n - k); }`, i.e. a
    // tail recursion to pick the smaller of `k` and `n - k`. Hax extracts
    // recursive functions with `partial_fixpoint`; combining that with a
    // `while_loop` in the same body makes the proof obligations awkward
    // (and earlier extraction emitted `sorry`). The recursion only ever
    // fires once (the second call has its own `k <= n - k` already true),
    // so a one-shot pick gives identical observable behavior.
    let k_pick = if k > n - k { n - k } else { k };
    let mut n_var = n;
    let mut r: u64 = 1;
    let mut d: u64 = 1;
    // Original was `loop { if d > k { break; } ... }`, which Hax extracted
    // to `sorry`. We rewrite as a `while`-loop. The measure must be a
    // single variable (compound expressions like `k - d + 1` make
    // `hax_construct_pure` produce multiple goals containing the
    // metavariable, which the tactic does not support). So we add an
    // explicit countdown variable `steps` whose only role is to be the
    // loop_decreases measure.
    let mut steps: u64 = k_pick;
    while steps > 0 {
        hax_lib::loop_decreases!(steps);
        r = multiply_and_divide(r, n_var, d);
        n_var -= 1;
        d += 1;
        steps -= 1;
    }
    r
}

/// Calculate the multinomial coefficient.
pub fn multinomial(k: &[u64]) -> u64 {
    let mut r: u64 = 1;
    let mut p: u64 = 0;
    // Original was `for i in k { ... }`. Hax extracts that as a `fold`
    // over an `IntoIterator` instance for `RustSlice`, neither of which is
    // defined in the Lean prelude (`Unknown constant
    // core_models.iter.traits.iterator.Iterator.fold` and `failed to
    // synthesize core_models.iter.traits.collect.IntoIterator (RustSlice
    // u64)`). A plain index-based `while` loop avoids both.
    let len = k.len();
    let mut idx: usize = 0;
    // As in `binomial`, we use a single-variable countdown for the
    // termination measure, since `len - idx` is a compound expression that
    // confuses `hax_construct_pure`.
    let mut remaining: usize = len;
    while remaining > 0 {
        hax_lib::loop_decreases!(remaining);
        let i = k[idx];
        p = p + i;
        r = r * binomial(p, i);
        idx += 1;
        remaining -= 1;
    }
    r
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
