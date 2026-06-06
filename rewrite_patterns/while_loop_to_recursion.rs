// proof-burden (not extraction): `while` loops extract cleanly via Hax,
// but the proof has to apply `Spec.MonoLoopCombinator.while_loop` and
// discharge a body-step Hoare triple through `Std.Do.Triple.bind` —
// intricate manipulation in a sparsely-documented tactic library, and
// the dominant source of proof-stage stagnation in batch runs.
//
// Tail-recursive functions extracted as `partial_fixpoint` admit equational
// reasoning instead: `Nat.strongRecOn` on the recursion measure plus
// `unfold`/`rw`/induction — well-supported tactics with rich error
// messages. See `proof_patterns/recursion_example` for the canonical proof
// shape and `proof_patterns/sum_to_n_modified` / `proof_patterns/factorial_modified`
// for real targets verified this way.
//
// This is a preference rewrite — apply when the loop has no break/continue,
// a single accumulator state, and bounded iteration depth (~10^5 max, since
// Rust does not guarantee tail-call optimisation). Do NOT apply when the
// loop has early exits, the depth could be data-dependent and large, or
// the algorithm's correctness depends on iteration order.

// before

pub fn sum_to_n(n: u64) -> u64 {
    let mut sum = 0u64;
    let mut i = 1u64;
    while i <= n {
        sum = sum + i;
        i = i + 1;
    }
    sum
}

// after

fn sum_loop(n: u64, i: u64, acc: u64) -> u64 {
    if i > n {
        acc
    } else {
        sum_loop(n, i + 1, acc + i)
    }
}

pub fn sum_to_n(n: u64) -> u64 {
    sum_loop(n, 1, 0)
}
