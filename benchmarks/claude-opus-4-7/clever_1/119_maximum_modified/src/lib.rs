/// HumanEval/120 / CLEVER 119 — `maximum(arr, k)`.  Return a sorted-
/// ascending list of the `k` largest values in `arr`.  If `k == 0` or
/// `arr` is empty, return `[]`.  If `k >= arr.len()`, return a sorted
/// copy of `arr`.
//
// Hax-compatibility rewrites:
//   * `Vec::push` (`alloc.vec.Impl_1.push`) is undefined in the Hax Lean
//     prelude — `extend_from_slice` with a typed `[u64; N]` let binding
//     keeps the size in the type ascription so `unsize` elaborates
//     cleanly (see `rewrite_patterns/vec_push_to_extend_from_slice_typed_chunk.rs`).
//   * The original `while` loop in `insert_asc` is lifted into a tail-
//     recursive helper for the cleaner downstream proof shape (see
//     `rewrite_patterns/while_loop_to_recursion.rs`).
fn insert_asc_at(v: &[u64], x: u64, i: usize, done: bool, acc: Vec<u64>) -> Vec<u64> {
    if i >= v.len() {
        if done {
            acc
        } else {
            let mut acc = acc;
            let chunk: [u64; 1] = [x];
            acc.extend_from_slice(&chunk);
            acc
        }
    } else {
        let mut acc = acc;
        if !done && v[i] >= x {
            let chunk: [u64; 2] = [x, v[i]];
            acc.extend_from_slice(&chunk);
            insert_asc_at(v, x, i + 1, true, acc)
        } else {
            let chunk: [u64; 1] = [v[i]];
            acc.extend_from_slice(&chunk);
            insert_asc_at(v, x, i + 1, done, acc)
        }
    }
}

fn insert_asc(v: Vec<u64>, x: u64) -> Vec<u64> {
    insert_asc_at(&v, x, 0, false, Vec::new())
}

fn sort_at(l: &[u64], i: usize, s: Vec<u64>) -> Vec<u64> {
    if i >= l.len() { s } else { sort_at(l, i + 1, insert_asc(s, l[i])) }
}

fn tail_from(s: &[u64], start: usize, acc: Vec<u64>) -> Vec<u64> {
    if start >= s.len() {
        acc
    } else {
        let mut acc = acc;
        let chunk: [u64; 1] = [s[start]];
        acc.extend_from_slice(&chunk);
        tail_from(s, start + 1, acc)
    }
}

pub fn maximum(arr: &[u64], k: u64) -> Vec<u64> {
    if k == 0 || arr.is_empty() { return Vec::new(); }
    let sorted = sort_at(arr, 0, Vec::new());
    let n = sorted.len() as u64;
    let start = if k >= n { 0 } else { (n - k) as usize };
    tail_from(&sorted, start, Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn known() {
        assert_eq!(maximum(&[], 3), vec![]);
        assert_eq!(maximum(&[1, 2, 3], 0), vec![]);
        assert_eq!(maximum(&[5, 3, 1, 2, 4], 3), vec![3, 4, 5]);
        assert_eq!(maximum(&[1, 2, 3, 4], 10), vec![1, 2, 3, 4]);
    }

    proptest! {
        // Special-case clause: k == 0 or arr empty => empty result.
        #[test]
        fn prop_empty_on_zero_k_or_empty_arr(arr in proptest::collection::vec(any::<u64>(), 0..32), k in any::<u64>()) {
            if k == 0 {
                prop_assert_eq!(maximum(&arr, k), Vec::<u64>::new());
            }
            if arr.is_empty() {
                prop_assert_eq!(maximum(&arr, k), Vec::<u64>::new());
            }
        }

        // Length postcondition: result.len() == min(k, arr.len()).
        #[test]
        fn prop_length_is_min_k_len(arr in proptest::collection::vec(any::<u64>(), 0..32), k in 0u64..64) {
            let out = maximum(&arr, k);
            let expected = std::cmp::min(k as usize, arr.len());
            prop_assert_eq!(out.len(), expected);
        }

        // Sortedness postcondition: result is sorted ascending.
        #[test]
        fn prop_result_sorted_ascending(arr in proptest::collection::vec(any::<u64>(), 0..32), k in 0u64..64) {
            let out = maximum(&arr, k);
            for i in 1..out.len() {
                prop_assert!(out[i - 1] <= out[i]);
            }
        }

        // Content postcondition: result is exactly the k largest elements of arr
        // (as a multiset, so ties are handled). Compared against an independent
        // reference: sort ascending, take the last min(k, len) elements.
        #[test]
        fn prop_result_is_k_largest(arr in proptest::collection::vec(any::<u64>(), 0..32), k in 0u64..64) {
            let out = maximum(&arr, k);
            let mut sorted = arr.clone();
            sorted.sort();
            let take = std::cmp::min(k as usize, sorted.len());
            let expected: Vec<u64> = sorted[sorted.len() - take..].to_vec();
            prop_assert_eq!(out, expected);
        }
    }
}
