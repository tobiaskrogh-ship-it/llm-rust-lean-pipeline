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

fn insert_sorted(v: Vec<u64>, x: u64) -> Vec<u64> {
    let mut r: Vec<u64> = Vec::new();
    let mut i = 0usize;
    let mut done = false;
    while i < v.len() {
        if !done && !lex_less(v[i], x) { r.push(x); done = true; }
        r.push(v[i]); i += 1;
    }
    if !done { r.push(x); }
    r
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
