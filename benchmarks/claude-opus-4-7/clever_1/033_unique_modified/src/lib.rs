/// Return sorted unique elements of `l`. (Return type widened to
/// `Vec<i64>` to match the docstring; CLEVER auto-defaulted to `i64`.)
//
// Three Hax-incompatibility fixes vs the original:
//
//  1. `Vec::push` is not modeled in the Hax Lean prelude
//     (`alloc.vec.Impl_1.push` is undefined; `lake build` fails with
//     `Unknown identifier`). Per `vec_push_to_extend_from_slice_typed_chunk.rs`,
//     replace each `.push(x)` with a typed-let chunk
//     (`let chunk: [i64; N] = [...]`) followed by
//     `acc.extend_from_slice(&chunk)`. The typed let is needed so Hax
//     can solve the `RustArray i64 N` size parameter from the let's
//     type ascription.
//
//  2. The `while` loop in the original `insert_sorted` is replaced
//     with a tail-recursive helper `insert_sorted_at`. Recursion-
//     preference rule: `partial_fixpoint` extraction admits cleaner
//     downstream proofs than `Spec.MonoLoopCombinator.while_loop`
//     Hoare-triple chaining. The state here (`i`, `inserted`, `acc`)
//     threads cleanly as parameters, and the iteration depth is
//     bounded by `v.len()` (well under 10^5 in any realistic test).
//
//  3. `dedupe_at`'s guard `i == 0 || sorted[i] != sorted[i - 1]`
//     is short-circuit `||` over a partial op (`i - 1` underflows at
//     `i = 0`). Hax's `do`-block extraction is eager — every `←` bind
//     runs before the `||?` combinator, so `i - 1` would be evaluated
//     at `i = 0` and the extracted Lean would diverge (`RustM.fail`),
//     silently breaking downstream proofs. Per
//     `short_circuit_and_with_partial_op.rs`, rewrite as `if`/`else`
//     so the partial op stays under its guard through extraction.

fn insert_sorted_at(
    v: &[i64],
    x: i64,
    i: usize,
    inserted: bool,
    mut acc: Vec<i64>,
) -> Vec<i64> {
    if i >= v.len() {
        if !inserted {
            let chunk: [i64; 1] = [x];
            acc.extend_from_slice(&chunk);
            acc
        } else {
            acc
        }
    } else {
        let vi = v[i];
        if !inserted && vi >= x {
            let chunk: [i64; 2] = [x, vi];
            acc.extend_from_slice(&chunk);
            insert_sorted_at(v, x, i + 1, true, acc)
        } else {
            let chunk: [i64; 1] = [vi];
            acc.extend_from_slice(&chunk);
            insert_sorted_at(v, x, i + 1, inserted, acc)
        }
    }
}

fn insert_sorted(v: Vec<i64>, x: i64) -> Vec<i64> {
    insert_sorted_at(&v, x, 0, false, Vec::new())
}

fn sort_at(l: &[i64], i: usize, acc: Vec<i64>) -> Vec<i64> {
    if i >= l.len() {
        acc
    } else {
        sort_at(l, i + 1, insert_sorted(acc, l[i]))
    }
}

fn dedupe_at(sorted: &[i64], i: usize, mut acc: Vec<i64>) -> Vec<i64> {
    if i >= sorted.len() {
        acc
    } else {
        // `if`/`else` instead of `i == 0 || sorted[i] != sorted[i - 1]`
        // so the `i - 1` partial op stays under its guard through Hax's
        // eager `do`-block extraction.
        let keep = if i == 0 {
            true
        } else {
            sorted[i] != sorted[i - 1]
        };
        if keep {
            let chunk: [i64; 1] = [sorted[i]];
            acc.extend_from_slice(&chunk);
            dedupe_at(sorted, i + 1, acc)
        } else {
            dedupe_at(sorted, i + 1, acc)
        }
    }
}

pub fn unique(l: &[i64]) -> Vec<i64> {
    let sorted = sort_at(l, 0, Vec::new());
    dedupe_at(&sorted, 0, Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    // --- Anchor unit test: pins down the empty-input base case ---

    #[test]
    fn empty_input_yields_empty_output() {
        assert_eq!(unique(&[]), Vec::<i64>::new());
    }

    // --- Property tests: the three independent postcondition clauses ---

    proptest! {
        // Postcondition 1: the output is strictly increasing.
        // This single property captures BOTH "sorted ascending" and
        // "no duplicates" — strict ordering rules out repeats.
        #[test]
        fn output_is_strictly_increasing(l in proptest::collection::vec(any::<i64>(), 0..32)) {
            let out = unique(&l);
            for w in out.windows(2) {
                prop_assert!(w[0] < w[1], "output not strictly increasing: {:?}", out);
            }
        }

        // Postcondition 2: every input element is present in the output.
        // (Output "covers" the input as a set.)
        #[test]
        fn output_contains_every_input_element(l in proptest::collection::vec(any::<i64>(), 0..32)) {
            let out = unique(&l);
            for x in &l {
                prop_assert!(out.contains(x), "input element {} missing from output {:?}", x, out);
            }
        }

        // Postcondition 3: every output element came from the input.
        // (Output is a subset of the input — no spurious elements.)
        #[test]
        fn output_only_contains_input_elements(l in proptest::collection::vec(any::<i64>(), 0..32)) {
            let out = unique(&l);
            for y in &out {
                prop_assert!(l.contains(y), "output element {} not in input {:?}", y, l);
            }
        }
    }
}
