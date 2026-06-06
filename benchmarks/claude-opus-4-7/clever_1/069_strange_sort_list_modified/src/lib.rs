/// HumanEval/70 — `strange_sort_list(l)`.  Return a permutation of `l`
/// whose elements alternate between the current minimum and the
/// current maximum of the remaining items.
///
/// Examples:
///   [1, 2, 3, 4]      -> [1, 4, 2, 3]
///   [5, 5, 5, 5]      -> [5, 5, 5, 5]
///   []                -> []
///
/// Implemented as: sort the input, then take from alternating ends.
//
// Hax-compatibility rewrites (see
// `rewrite_patterns/vec_push_to_extend_from_slice_typed_chunk.rs` and
// `rewrite_patterns/while_loop_to_recursion.rs`):
//   * `Vec::push` (`alloc.vec.Impl_1.push`) is undefined in the Hax Lean
//     prelude — replaced with `extend_from_slice` over a *typed*
//     `[i64; N]` let binding so Hax emits `RustArray i64 N` with the
//     size in the type ascription and `unsize` elaborates cleanly.
//   * The `while`-loop body of `insert_sorted` is lifted into a private
//     tail-recursive helper `insert_sorted_at`; the public function just
//     seeds it. Tail recursion extracts as `partial_fixpoint`, which
//     admits clean `Nat.strongRecOn` induction downstream.

fn insert_sorted_at(v: &[i64], x: i64, i: usize, inserted: bool, acc: Vec<i64>) -> Vec<i64> {
    let n = v.len();
    if i >= n {
        let mut acc = acc;
        if !inserted {
            let chunk: [i64; 1] = [x];
            acc.extend_from_slice(&chunk);
        }
        acc
    } else if !inserted && v[i] >= x {
        // Emit `x` then `v[i]` in a single chunk; mark inserted = true.
        let mut acc = acc;
        let chunk: [i64; 2] = [x, v[i]];
        acc.extend_from_slice(&chunk);
        insert_sorted_at(v, x, i + 1, true, acc)
    } else {
        // Emit `v[i]` alone; carry `inserted` unchanged.
        let mut acc = acc;
        let chunk: [i64; 1] = [v[i]];
        acc.extend_from_slice(&chunk);
        insert_sorted_at(v, x, i + 1, inserted, acc)
    }
}

fn insert_sorted(v: Vec<i64>, x: i64) -> Vec<i64> {
    insert_sorted_at(&v, x, 0, false, Vec::new())
}

fn sort_at(l: &[i64], i: usize, sorted: Vec<i64>) -> Vec<i64> {
    if i >= l.len() {
        sorted
    } else {
        sort_at(l, i + 1, insert_sorted(sorted, l[i]))
    }
}

fn build_strange_at(sorted: &[i64], taken: usize, acc: Vec<i64>) -> Vec<i64> {
    let n = sorted.len();
    if taken >= n {
        acc
    } else {
        let half = taken / 2;
        let idx = if taken % 2 == 0 {
            half
        } else {
            n - 1 - half
        };
        let mut acc = acc;
        let chunk: [i64; 1] = [sorted[idx]];
        acc.extend_from_slice(&chunk);
        build_strange_at(sorted, taken + 1, acc)
    }
}

pub fn strange_sort_list(l: &[i64]) -> Vec<i64> {
    let sorted = sort_at(l, 0, Vec::new());
    build_strange_at(&sorted, 0, Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Brute-force oracle: sort + alternating-end pick.
    fn naive_strange_sort(l: &[i64]) -> Vec<i64> {
        let mut sorted = l.to_vec();
        sorted.sort();
        let mut out = Vec::new();
        let mut lo = 0usize;
        let mut hi = sorted.len();
        let mut take_min = true;
        while lo < hi {
            if take_min {
                out.push(sorted[lo]);
                lo += 1;
            } else {
                out.push(sorted[hi - 1]);
                hi -= 1;
            }
            take_min = !take_min;
        }
        out
    }

    /// Boundary cases.
    #[test]
    fn small_cases() {
        assert_eq!(strange_sort_list(&[]), Vec::<i64>::new());
        assert_eq!(strange_sort_list(&[7]), vec![7]);
        assert_eq!(strange_sort_list(&[1, 2, 3, 4]), vec![1, 4, 2, 3]);
        assert_eq!(strange_sort_list(&[5, 5, 5, 5]), vec![5, 5, 5, 5]);
    }

    proptest! {
        /// Postcondition: matches the brute-force oracle — the precise
        /// "alternating min/max" arrangement.
        #[test]
        fn matches_brute_force(l in proptest::collection::vec(-100i64..=100, 0..12)) {
            prop_assert_eq!(strange_sort_list(&l), naive_strange_sort(&l));
        }

        /// Multiset preservation: result is a permutation of the input.
        /// Independent of `matches_brute_force` in spirit — it isolates the
        /// "uses exactly the input's elements" clause from the arrangement.
        /// (Length preservation follows from this, so it is not tested
        /// separately.)
        #[test]
        fn permutation_of_input(l in proptest::collection::vec(-100i64..=100, 0..12)) {
            let mut a = l.clone();
            let mut b = strange_sort_list(&l);
            a.sort();
            b.sort();
            prop_assert_eq!(a, b);
        }
    }
}
