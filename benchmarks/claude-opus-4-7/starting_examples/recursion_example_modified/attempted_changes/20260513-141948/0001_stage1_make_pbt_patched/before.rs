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

    #[test]
    fn returns_zero_at_zero() {
        assert_eq!(count_down(0), 0);
    }

    #[test]
    fn returns_zero_at_small_inputs() {
        for n in 0u64..16 {
            assert_eq!(count_down(n), 0);
        }
    }
}
