//! Counterpart to `while_example`: same idea (proof obligations live in
//! Lean, Rust source is minimal) but for *recursion* instead of a `while`
//! loop. Hax extracts recursive functions via `partial_fixpoint`; the proof
//! technique uses a different spec lemma than
//! `Spec.MonoLoopCombinator.while_loop`.
//!
//! `count_down(n)` always returns 0. The recursion decrements `n` until it
//! reaches 0. Termination measure is `n` itself (strictly decreasing on each
//! recursive call). Postcondition: `count_down n = pure 0` for every
//! `n : u64`.
//!
//! Smallest non-trivial partial_fixpoint example: just enough structure to
//! demonstrate the proof pattern (custom termination + induction + recursive
//! equation), without any algorithmic complexity to obscure it.

pub fn count_down(n: u64) -> u64 {
    if n == 0 {
        0
    } else {
        count_down(n - 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Postcondition, base case: `count_down(0)` returns `0`.
    ///
    /// Pinned out as a separate test because it is the only input that hits
    /// the non-recursive branch of the implementation, and it is the base
    /// case of the downstream induction proof.
    #[test]
    fn postcondition_at_zero() {
        assert_eq!(count_down(0), 0);
    }

    /// Postcondition, recursive case: `count_down(n) == 0` for every
    /// `n > 0` in a small exhaustive range.
    ///
    /// Catches off-by-one bugs near the base case — e.g. an implementation
    /// that returns `n` instead of recursing, or that stops one step early
    /// and returns `1`.
    #[test]
    fn postcondition_small_inputs_exhaustive() {
        for n in 1u64..=256 {
            assert_eq!(count_down(n), 0);
        }
    }

    /// Postcondition holds at larger inputs too. Sampled rather than
    /// exhaustive: the implementation recurses `n` times, so we stay well
    /// below the default test-thread stack limit (~2 MB) while still
    /// exercising inputs orders of magnitude beyond the small range.
    #[test]
    fn postcondition_larger_inputs() {
        for n in [100u64, 1_000, 10_000] {
            assert_eq!(count_down(n), 0);
        }
    }
}
