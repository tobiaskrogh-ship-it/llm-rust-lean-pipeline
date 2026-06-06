/// HumanEval/88 / CLEVER 087 — `sort_array(lst)`.  Sort `lst` ascending
/// if `(lst[0] + lst[last]) % 2 != 0` (sum is odd); descending otherwise.
/// Spec restricts to non-negative integers → `u64`.
fn insert_asc(v: Vec<u64>, x: u64) -> Vec<u64> {
    let mut r: Vec<u64> = Vec::new();
    let mut i = 0usize;
    let mut done = false;
    while i < v.len() {
        if !done && v[i] >= x { r.push(x); done = true; }
        r.push(v[i]); i += 1;
    }
    if !done { r.push(x); }
    r
}

fn sort_at(l: &[u64], i: usize, s: Vec<u64>) -> Vec<u64> {
    if i >= l.len() { s } else { sort_at(l, i + 1, insert_asc(s, l[i])) }
}

fn reverse_at(s: &[u64], i: usize, mut acc: Vec<u64>) -> Vec<u64> {
    if i >= s.len() { acc } else {
        acc.push(s[s.len() - 1 - i]);
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
