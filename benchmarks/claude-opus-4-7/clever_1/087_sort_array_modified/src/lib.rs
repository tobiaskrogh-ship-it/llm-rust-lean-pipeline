/// HumanEval/88 / CLEVER 087 — `sort_array(lst)`.  Sort `lst` ascending
/// if `(lst[0] + lst[last]) % 2 != 0` (sum is odd); descending otherwise.
/// Spec restricts to non-negative integers → `u64`.
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

fn reverse_at(s: &[u64], i: usize, acc: Vec<u64>) -> Vec<u64> {
    if i >= s.len() {
        acc
    } else {
        let mut acc = acc;
        let chunk: [u64; 1] = [s[s.len() - 1 - i]];
        acc.extend_from_slice(&chunk);
        reverse_at(s, i + 1, acc)
    }
}

pub fn sort_array(lst: &[u64]) -> Vec<u64> {
    if lst.is_empty() { return Vec::new(); }
    let sorted = sort_at(lst, 0, Vec::new());
    let parity = (lst[0] % 2 + lst[lst.len() - 1] % 2) % 2;
    if parity != 0 { sorted } else { reverse_at(&sorted, 0, Vec::new()) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn is_sorted_asc(v: &[u64]) -> bool {
        let mut i = 1;
        while i < v.len() {
            if v[i - 1] > v[i] { return false; }
            i += 1;
        }
        true
    }

    fn is_sorted_desc(v: &[u64]) -> bool {
        let mut i = 1;
        while i < v.len() {
            if v[i - 1] < v[i] { return false; }
            i += 1;
        }
        true
    }

    fn multiset_eq(a: &[u64], b: &[u64]) -> bool {
        let mut a = a.to_vec();
        let mut b = b.to_vec();
        a.sort();
        b.sort();
        a == b
    }

    // Edge case: empty input yields empty output.
    #[test]
    fn empty_input_returns_empty() {
        assert_eq!(sort_array(&[]), Vec::<u64>::new());
    }

    proptest! {
        // Postcondition: output is a permutation of the input (same multiset).
        // This pins down that the function only reorders; it doesn't drop,
        // duplicate, or invent elements.
        #[test]
        fn output_is_permutation_of_input(
            l in proptest::collection::vec(0u64..=100, 0..12)
        ) {
            let r = sort_array(&l);
            prop_assert!(multiset_eq(&l, &r));
        }

        // Postcondition: when (lst[0] + lst[last]) is odd, output is ascending.
        #[test]
        fn ascending_when_sum_is_odd(
            l in proptest::collection::vec(0u64..=100, 1..12)
        ) {
            let parity = (l[0] % 2 + l[l.len() - 1] % 2) % 2;
            prop_assume!(parity != 0);
            let r = sort_array(&l);
            prop_assert!(is_sorted_asc(&r));
        }

        // Postcondition: when (lst[0] + lst[last]) is even, output is descending.
        #[test]
        fn descending_when_sum_is_even(
            l in proptest::collection::vec(0u64..=100, 1..12)
        ) {
            let parity = (l[0] % 2 + l[l.len() - 1] % 2) % 2;
            prop_assume!(parity == 0);
            let r = sort_array(&l);
            prop_assert!(is_sorted_desc(&r));
        }
    }
}
