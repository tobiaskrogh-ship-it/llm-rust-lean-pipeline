/// Return a list identical to `l` at odd indices, with values at even
/// indices replaced by those same values in ascending order. (Return type
/// widened to `Vec<i64>` to match the docstring.)
fn insert_sorted_at(v: &[i64], i: usize, x: i64, inserted: bool, acc: Vec<i64>) -> Vec<i64> {
    if i >= v.len() {
        let mut acc = acc;
        if !inserted {
            // Typed let — Hax emits the size in the type annotation
            // `RustArray i64 1`, so `unsize` can elaborate the size.
            let chunk: [i64; 1] = [x];
            acc.extend_from_slice(&chunk);
        }
        acc
    } else if !inserted && v[i] >= x {
        let mut acc = acc;
        let chunk: [i64; 2] = [x, v[i]];
        acc.extend_from_slice(&chunk);
        insert_sorted_at(v, i + 1, x, true, acc)
    } else {
        let mut acc = acc;
        let chunk: [i64; 1] = [v[i]];
        acc.extend_from_slice(&chunk);
        insert_sorted_at(v, i + 1, x, inserted, acc)
    }
}

fn insert_sorted(v: Vec<i64>, x: i64) -> Vec<i64> {
    insert_sorted_at(&v, 0, x, false, Vec::new())
}

fn collect_evens(l: &[i64], i: usize, acc: Vec<i64>) -> Vec<i64> {
    if i >= l.len() {
        acc
    } else if i % 2 == 0 {
        collect_evens(l, i + 1, insert_sorted(acc, l[i]))
    } else {
        collect_evens(l, i + 1, acc)
    }
}

fn rebuild_at(l: &[i64], sorted: &[i64], i: usize, j: usize, acc: Vec<i64>) -> Vec<i64> {
    if i >= l.len() {
        acc
    } else if i % 2 == 0 {
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

pub fn sort_even(l: &[i64]) -> Vec<i64> {
    let sorted = collect_evens(l, 0, Vec::new());
    rebuild_at(l, &sorted, 0, 0, Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Helper: multiset equality on two slices of i64 (sort copies and compare).
    fn same_multiset(a: &[i64], b: &[i64]) -> bool {
        let mut a = a.to_vec();
        let mut b = b.to_vec();
        a.sort();
        b.sort();
        a == b
    }

    proptest! {
        // Contract postcondition: length is preserved.
        #[test]
        fn length_preserved(l in proptest::collection::vec(any::<i64>(), 0..32)) {
            let out = sort_even(&l);
            prop_assert_eq!(out.len(), l.len());
        }

        // Contract postcondition: values at odd indices are identical to the input.
        #[test]
        fn odd_indices_unchanged(l in proptest::collection::vec(any::<i64>(), 0..32)) {
            let out = sort_even(&l);
            for i in (1..l.len()).step_by(2) {
                prop_assert_eq!(out[i], l[i]);
            }
        }

        // Contract postcondition: values at even indices are in non-decreasing order.
        #[test]
        fn even_indices_sorted(l in proptest::collection::vec(any::<i64>(), 0..32)) {
            let out = sort_even(&l);
            let evens: Vec<i64> = out.iter().step_by(2).copied().collect();
            for w in evens.windows(2) {
                prop_assert!(w[0] <= w[1]);
            }
        }

        // Contract postcondition: the multiset of values at even indices is preserved
        // (output even-indexed values are exactly the input even-indexed values, reordered).
        // Independent from `even_indices_sorted`: catches implementations that produce a
        // sorted but wrong sequence (e.g. all zeros) at even positions.
        #[test]
        fn even_indices_multiset_preserved(l in proptest::collection::vec(any::<i64>(), 0..32)) {
            let out = sort_even(&l);
            let in_evens: Vec<i64> = l.iter().step_by(2).copied().collect();
            let out_evens: Vec<i64> = out.iter().step_by(2).copied().collect();
            prop_assert!(same_multiset(&in_evens, &out_evens));
        }
    }

    // Edge case: empty input yields empty output (function is total; no panic).
    #[test]
    fn empty_input() {
        assert_eq!(sort_even(&[]), Vec::<i64>::new());
    }
}
