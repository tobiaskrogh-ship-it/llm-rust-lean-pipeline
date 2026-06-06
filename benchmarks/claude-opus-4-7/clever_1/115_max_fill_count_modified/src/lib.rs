/// CLEVER 115 (HumanEval/116) — note that the canonical signature here
/// is named `max_fill_count` but the docstring describes a *different*
/// problem: sort an array of non-negative integers by the number of
/// `1` bits in their binary representation (ascending), ties broken by
/// decimal value.  The function name in this crate honours the CLEVER
/// docstring's algorithm.  Override to `u64` per the docstring's
/// "non-negative integers".
fn popcount_at(n: u64, acc: u64) -> u64 {
    if n == 0 { acc } else { popcount_at(n / 2, acc + (n % 2)) }
}

fn lex_less(a: u64, b: u64) -> bool {
    let pa = popcount_at(a, 0);
    let pb = popcount_at(b, 0);
    if pa < pb { true }
    else if pa > pb { false }
    else { a < b }
}

// Hax-compatibility rewrite (see
// `rewrite_patterns/vec_push_to_extend_from_slice_typed_chunk.rs` and
// `rewrite_patterns/while_loop_to_recursion.rs`):
//   * `Vec::push` (`alloc.vec.Impl_1.push`) is undefined in the Hax Lean
//     prelude — use `extend_from_slice` with a *typed* `[u64; 1]` let
//     binding so Hax's emitted `RustArray u64 1` carries the size in the
//     type ascription and `unsize` elaborates cleanly.
//   * The original `while` loop is single-accumulator with bounded depth
//     (≤ `v.len()`). Tail recursion (`partial_fixpoint`) admits cleaner
//     proofs than `Spec.MonoLoopCombinator.while_loop`.
fn insert_sorted_at(v: &[u64], x: u64, i: usize, done: bool, r: Vec<u64>) -> Vec<u64> {
    if i >= v.len() {
        let mut r = r;
        if !done {
            let chunk: [u64; 1] = [x];
            r.extend_from_slice(&chunk);
        }
        r
    } else {
        let mut r = r;
        let mut done = done;
        if !done && !lex_less(v[i], x) {
            let chunk: [u64; 1] = [x];
            r.extend_from_slice(&chunk);
            done = true;
        }
        let chunk: [u64; 1] = [v[i]];
        r.extend_from_slice(&chunk);
        insert_sorted_at(v, x, i + 1, done, r)
    }
}

fn insert_sorted(v: Vec<u64>, x: u64) -> Vec<u64> {
    insert_sorted_at(&v, x, 0, false, Vec::new())
}

fn sort_at(l: &[u64], i: usize, s: Vec<u64>) -> Vec<u64> {
    if i >= l.len() { s } else { sort_at(l, i + 1, insert_sorted(s, l[i])) }
}

pub fn sort_by_popcount(l: &[u64]) -> Vec<u64> {
    sort_at(l, 0, Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn known() {
        // popcounts: 1→1, 5→2, 2→1, 3→2, 4→1
        // sort by (popcount asc, value asc):
        // pop=1: {1, 2, 4}; pop=2: {3, 5}
        // sorted: 1, 2, 4, 3, 5
        assert_eq!(sort_by_popcount(&[1, 5, 2, 3, 4]), vec![1, 2, 4, 3, 5]);
    }

    proptest! {
        /// Postcondition (1/2): the result is a permutation of the input.
        /// We compare the two as multisets by sorting each numerically and
        /// checking equality. This catches implementations that drop, add,
        /// or replace elements.
        #[test]
        fn output_is_permutation_of_input(
            v in proptest::collection::vec(any::<u64>(), 0..16)
        ) {
            let out = sort_by_popcount(&v);
            let mut a = v.clone();
            let mut b = out.clone();
            a.sort();
            b.sort();
            prop_assert_eq!(a, b);
        }

        /// Postcondition (2/2): the result is non-decreasing under the
        /// lexicographic key (popcount, value). This pins down both the
        /// primary popcount-ascending order and the value-ascending
        /// tiebreaker within each popcount class.
        #[test]
        fn output_is_sorted_by_popcount_then_value(
            v in proptest::collection::vec(any::<u64>(), 0..16)
        ) {
            let out = sort_by_popcount(&v);
            for i in 1..out.len() {
                let prev = out[i - 1];
                let cur = out[i];
                let pp = prev.count_ones();
                let pc = cur.count_ones();
                prop_assert!(
                    pp < pc || (pp == pc && prev <= cur),
                    "out[{}]={} (popcount {}) must precede out[{}]={} (popcount {})",
                    i - 1, prev, pp, i, cur, pc
                );
            }
        }
    }
}
