/// HumanEval/145 / CLEVER 143 — `order_by_points(nums)`.  Stable-sort
/// `nums` ascending by the sum of their signed digits (where for
/// negative `n`, the first digit takes the sign).  Ties preserve the
/// original order.
fn first_digit_at(n: i64) -> i64 {
    if n < 10 { n } else { first_digit_at(n / 10) }
}
fn digit_sum_at(n: i64, acc: i64) -> i64 {
    if n == 0 { acc } else { digit_sum_at(n / 10, acc + n % 10) }
}
fn signed_digit_sum(n: i64) -> i64 {
    if n == 0 { 0 }
    else if n > 0 { digit_sum_at(n, 0) }
    else { let m = -n; digit_sum_at(m, 0) - 2 * first_digit_at(m) }
}

// Hax-compatibility rewrite (see `rewrite_patterns/vec_push_to_extend_from_slice_typed_chunk.rs`):
//   * `Vec::push` (`alloc.vec.Impl_1.push`) is undefined in the Hax Lean
//     prelude — use `extend_from_slice` with a *typed* `[i64; N]` let
//     binding so Hax's emitted `RustArray i64 N` carries the size in the
//     ascription and `unsize` elaborates cleanly.
//   * The original `while` loop is rewritten as tail recursion (see
//     `rewrite_patterns/while_loop_to_recursion.rs`) — this matches the
//     style already used by `first_digit_at`, `digit_sum_at`, `sort_at`
//     in this file, and produces a `partial_fixpoint` definition that the
//     proof stage handles via `Nat.strongRecOn` on `v.len() - i`.
fn insert_stable_at(v: Vec<i64>, x: i64, kx: i64, i: usize, done: bool, acc: Vec<i64>) -> Vec<i64> {
    if i >= v.len() {
        if done {
            acc
        } else {
            let mut acc = acc;
            let chunk: [i64; 1] = [x];
            acc.extend_from_slice(&chunk);
            acc
        }
    } else {
        let vi = v[i];
        let mut acc = acc;
        if !done && signed_digit_sum(vi) > kx {
            // Insert x before the first element with a strictly greater key.
            let chunk: [i64; 2] = [x, vi];
            acc.extend_from_slice(&chunk);
            insert_stable_at(v, x, kx, i + 1, true, acc)
        } else {
            let chunk: [i64; 1] = [vi];
            acc.extend_from_slice(&chunk);
            insert_stable_at(v, x, kx, i + 1, done, acc)
        }
    }
}

fn insert_stable(v: Vec<i64>, x: i64) -> Vec<i64> {
    let kx = signed_digit_sum(x);
    insert_stable_at(v, x, kx, 0, false, Vec::new())
}

fn sort_at(l: &[i64], i: usize, s: Vec<i64>) -> Vec<i64> {
    if i >= l.len() { s } else { sort_at(l, i + 1, insert_stable(s, l[i])) }
}

pub fn order_by_points(nums: &[i64]) -> Vec<i64> {
    sort_at(nums, 0, Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    // The contract refers to `signed_digit_sum` as the sort key.
    fn key(n: i64) -> i64 { signed_digit_sum(n) }

    #[test]
    fn known() {
        // ds: 1→1, 11→2, -1→-1, -11→(-1+1)=0, 0→0
        // sorted asc, stable: -1(-1), then ties at 0 in input order (-11, 0),
        // then 1, then 11.
        assert_eq!(order_by_points(&[1, 11, -1, -11, 0]), vec![-1, -11, 0, 1, 11]);
    }

    // We restrict inputs to a moderate range. In particular we avoid
    // `i64::MIN`, on which the implementation's `let m = -n` would overflow.
    fn input_strategy() -> impl Strategy<Value = Vec<i64>> {
        prop::collection::vec(-1_000_000i64..=1_000_000, 0..30)
    }

    proptest! {
        // Postcondition 1 — Permutation: the output is a rearrangement of
        // the input (same multiset of elements).
        #[test]
        fn output_is_permutation_of_input(nums in input_strategy()) {
            let out = order_by_points(&nums);
            let mut a = nums.clone();
            let mut b = out;
            a.sort();
            b.sort();
            prop_assert_eq!(a, b);
        }

        // Postcondition 2 — Sorted by key: adjacent elements in the output
        // are non-decreasing under `signed_digit_sum`.
        #[test]
        fn output_is_sorted_by_signed_digit_sum(nums in input_strategy()) {
            let out = order_by_points(&nums);
            for i in 1..out.len() {
                prop_assert!(key(out[i - 1]) <= key(out[i]));
            }
        }

        // Postcondition 3 — Stability: for each key value k, the subsequence
        // of input elements whose key equals k is preserved verbatim in the
        // output. This is the standard "filter-by-key equality" formulation
        // of stable sorting; it is independent of the multiset/sortedness
        // properties above (a sort can be a sorted permutation but reorder
        // ties arbitrarily).
        #[test]
        fn output_is_stable(nums in input_strategy()) {
            let out = order_by_points(&nums);
            let mut keys: Vec<i64> = nums.iter().map(|&n| key(n)).collect();
            keys.sort();
            keys.dedup();
            for k in keys {
                let input_subseq: Vec<i64> =
                    nums.iter().copied().filter(|&x| key(x) == k).collect();
                let output_subseq: Vec<i64> =
                    out.iter().copied().filter(|&x| key(x) == k).collect();
                prop_assert_eq!(input_subseq, output_subseq);
            }
        }
    }
}
