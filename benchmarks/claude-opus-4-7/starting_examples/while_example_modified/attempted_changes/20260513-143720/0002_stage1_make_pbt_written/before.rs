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

    #[test]
    fn matches_native_mod() {
        for (a, b) in [(10u64, 3), (15, 5), (7, 7), (100, 11), (0, 1), (1, 1), (u64::MAX, 7)] {
            assert_eq!(modulo_via_subtraction(a, b), a % b);
        }
    }

    #[test]
    fn smallest_remainder_returned() {
        assert_eq!(modulo_via_subtraction(10, 3), 1);
        assert_eq!(modulo_via_subtraction(15, 5), 0);
    }
}
