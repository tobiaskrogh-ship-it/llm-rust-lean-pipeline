//! Counterpart to `count_to`: same shape (while loop with `loop_invariant!`
//! and `loop_decreases!`) but the invariant uses `%`, which Hax's pureP/grind
//! synthesis cannot lift out of `RustM`. The point is to demonstrate the
//! failure mode the skill warns about — and to motivate the workaround
//! (drop the Rust-level invariant, prove it in Lean via
//! `Spec.MonoLoopCombinator.while_loop`).
//!
//! `modulo_via_subtraction(a, b)` computes `a % b` by repeated subtraction.
//! The natural invariant `x % b == a % b` is true on every iteration but
//! fails at extraction time:
//!   * `x % b` extracts to `x %? b : RustM u64` (Rust `%` panics if `b == 0`)
//!   * `pureP/grind` can't lift `RustM u64 → u64` without a proof of `b > 0`
//!   * Even with `#[hax_lib::requires(b > 0)]` the synthesis runs at macro
//!     expansion and has no access to the precondition context
//! Result: `lake build` rejects the extracted file.


pub fn modulo_via_subtraction(a: u64, b: u64) -> u64 {
    let mut x = a;
    while x >= b {
        // No `loop_invariant!`: the natural invariant `x % b == a % b` can't
        // be expressed at the Rust level (Hax's pureP/grind synthesis can't
        // lift partial-op expressions to `Prop`); see `While_exampleObligations.lean`
        // for the Lean-level proof using `Spec.MonoLoopCombinator.while_loop`.

        x -= b;
    }
    x
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Inputs where `a / b` is small, so the subtraction loop terminates
    /// in O(1) iterations. Used by every property test to keep the suite
    /// fast even when probing values near `u64::MAX`. Pairs with very
    /// small `b` and very large `a` (e.g. `(u64::MAX, 7)`) are deliberately
    /// excluded — naive evaluation would loop ~2^61 times.
    const BOUNDARY_PAIRS: &[(u64, u64)] = &[
        (0, 1),
        (0, u64::MAX),
        (1, 1),
        (1, 2),
        (1, u64::MAX),
        (u64::MAX - 1, u64::MAX),
        (u64::MAX, u64::MAX),
        (u64::MAX, u64::MAX - 1),
        (u64::MAX, (u64::MAX / 2) + 1),
    ];

    /// Postcondition (full contract): when `b > 0`, the function returns
    /// `a % b`. Exercised as a property over a small exhaustive sweep
    /// plus the `BOUNDARY_PAIRS` near `u64::MAX`. A buggy implementation
    /// that returns any value other than `a % b` for some valid input
    /// would be caught here.
    #[test]
    fn matches_native_mod() {
        for a in 0u64..=64 {
            for b in 1u64..=16 {
                assert_eq!(
                    modulo_via_subtraction(a, b),
                    a % b,
                    "a={a}, b={b}",
                );
            }
        }
        for &(a, b) in BOUNDARY_PAIRS {
            assert_eq!(
                modulo_via_subtraction(a, b),
                a % b,
                "a={a}, b={b}",
            );
        }
    }

    /// Independent range claim: when `b > 0`, the result is strictly
    /// less than `b`. This is the "smallest non-negative" half of the
    /// modulo contract — analogous to the "greatest" clause of the gcd
    /// contract — and is exactly the natural loop invariant for this
    /// implementation. A buggy implementation that returned `a` unchanged
    /// (no iterations), or that stopped one subtraction early, would be
    /// caught here even without a reference to the native `%` operator.
    #[test]
    fn result_less_than_divisor() {
        for a in 0u64..=64 {
            for b in 1u64..=16 {
                let r = modulo_via_subtraction(a, b);
                assert!(r < b, "a={a}, b={b}, r={r}");
            }
        }
        for &(a, b) in BOUNDARY_PAIRS {
            let r = modulo_via_subtraction(a, b);
            assert!(r < b, "a={a}, b={b}, r={r}");
        }
    }
}
