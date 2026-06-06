/// Return a list identical to `l` at indices NOT divisible by 3, with the
/// values at indices divisible by 3 replaced by those same values in
/// ascending order. (Return type widened to `Vec<i64>` to match the
/// docstring; CLEVER auto-defaulted to `i64`.)

// Tail-recursive walk of `v`, inserting `x` at the first position where
// `v[i] >= x` so the result stays sorted (assuming `v` is itself sorted).
// `Vec::push` is unsupported by the Hax Lean prelude, so the per-element
// append is done via `extend_from_slice` over a *typed* `[i64; N]` let-
// binding — Hax needs the size in the type annotation for `unsize` to
// elaborate the array length. The original `while` loop is also lifted
// into tail recursion per the recursion-preference rule.
fn insert_sorted_at(v: &[i64], x: i64, i: usize, inserted: bool, acc: Vec<i64>) -> Vec<i64> {
    if i >= v.len() {
        if !inserted {
            let mut acc = acc;
            let chunk: [i64; 1] = [x];
            acc.extend_from_slice(&chunk);
            acc
        } else {
            acc
        }
    } else if !inserted && v[i] >= x {
        let mut acc = acc;
        let chunk: [i64; 2] = [x, v[i]];
        acc.extend_from_slice(&chunk);
        insert_sorted_at(v, x, i + 1, true, acc)
    } else {
        let mut acc = acc;
        let chunk: [i64; 1] = [v[i]];
        acc.extend_from_slice(&chunk);
        insert_sorted_at(v, x, i + 1, inserted, acc)
    }
}

fn insert_sorted(v: Vec<i64>, x: i64) -> Vec<i64> {
    insert_sorted_at(&v, x, 0, false, Vec::new())
}

fn collect_thirds(l: &[i64], i: usize, acc: Vec<i64>) -> Vec<i64> {
    if i >= l.len() {
        acc
    } else if i % 3 == 0 {
        collect_thirds(l, i + 1, insert_sorted(acc, l[i]))
    } else {
        collect_thirds(l, i + 1, acc)
    }
}

fn rebuild_at(l: &[i64], sorted: &[i64], i: usize, j: usize, acc: Vec<i64>) -> Vec<i64> {
    if i >= l.len() {
        acc
    } else if i % 3 == 0 {
        let mut acc = acc;
        let chunk: [i64; 1] = [sorted[j]];
        acc.extend_from_slice(&chunk);
        rebuild_at(l, sorted, i + 1, j + 1, acc)
    } else {
        let mut acc = acc;
        let chunk: [i64; 1] = [l[i]];
        acc.extend_from_slice(&chunk);
        rebuild_at(l, sorted, i + 1, j, acc)
    }
}

pub fn sort_third(l: &[i64]) -> Vec<i64> {
    let sorted = collect_thirds(l, 0, Vec::new());
    rebuild_at(l, &sorted, 0, 0, Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        /// Postcondition: the output has the same length as the input.
        #[test]
        fn length_preserved(l in proptest::collection::vec(any::<i64>(), 0..50)) {
            let out = sort_third(&l);
            prop_assert_eq!(out.len(), l.len());
        }

        /// Postcondition: at indices `i` with `i % 3 != 0`, the output
        /// equals the input element-for-element.
        #[test]
        fn non_third_indices_unchanged(
            l in proptest::collection::vec(any::<i64>(), 0..50)
        ) {
            let out = sort_third(&l);
            for i in 0..l.len() {
                if i % 3 != 0 {
                    prop_assert_eq!(out[i], l[i]);
                }
            }
        }

        /// Postcondition: at indices `i` with `i % 3 == 0`, the output
        /// values appear in ascending order.
        #[test]
        fn third_indices_sorted(
            l in proptest::collection::vec(any::<i64>(), 0..50)
        ) {
            let out = sort_third(&l);
            let thirds: Vec<i64> =
                (0..out.len()).filter(|i| i % 3 == 0).map(|i| out[i]).collect();
            for w in thirds.windows(2) {
                prop_assert!(w[0] <= w[1]);
            }
        }

        /// Postcondition: the multiset of values at indices divisible by 3
        /// in the output equals the multiset of values at those same
        /// indices in the input. (Together with `third_indices_sorted`,
        /// this pins down the third-index values exactly.)
        #[test]
        fn third_indices_are_permutation(
            l in proptest::collection::vec(any::<i64>(), 0..50)
        ) {
            let out = sort_third(&l);
            let mut input_thirds: Vec<i64> =
                (0..l.len()).filter(|i| i % 3 == 0).map(|i| l[i]).collect();
            let mut output_thirds: Vec<i64> =
                (0..out.len()).filter(|i| i % 3 == 0).map(|i| out[i]).collect();
            input_thirds.sort();
            output_thirds.sort();
            prop_assert_eq!(input_thirds, output_thirds);
        }
    }
}
