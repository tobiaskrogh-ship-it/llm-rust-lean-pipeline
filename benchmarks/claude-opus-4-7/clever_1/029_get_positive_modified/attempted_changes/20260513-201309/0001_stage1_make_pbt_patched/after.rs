/// Return only the strictly positive (> 0) numbers from `l`, in input order.
/// (Return type widened from CLEVER's auto-defaulted `i64` to `Vec<i64>` to
/// match the docstring's "Return only positive numbers in the list".)
fn collect_at(l: &[i64], i: usize, mut acc: Vec<i64>) -> Vec<i64> {
    if i >= l.len() {
        acc
    } else if l[i] > 0 {
        acc.push(l[i]);
        collect_at(l, i + 1, acc)
    } else {
        collect_at(l, i + 1, acc)
    }
}

pub fn get_positive(l: &[i64]) -> Vec<i64> {
    collect_at(l, 0, Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    // Edge case: empty input -> empty output. Pins down the base case of the
    // recursion explicitly.
    #[test]
    fn empty_input_yields_empty() {
        assert_eq!(get_positive(&[]), Vec::<i64>::new());
    }

    // Boundary: the docstring says "strictly positive (> 0)", so zero must be
    // excluded. Catches a `>= 0` off-by-one in the predicate.
    #[test]
    fn zero_is_not_positive() {
        assert_eq!(get_positive(&[0, -1, 0, -2]), Vec::<i64>::new());
    }

    proptest! {
        // Full postcondition: `get_positive(l)` equals the subsequence of `l`
        // obtained by keeping the entries strictly greater than zero, in input
        // order. This single equality captures three independent things:
        //   * soundness:    every element of the output is > 0,
        //   * completeness: every positive entry of `l` survives,
        //   * order:        the relative order of kept entries matches `l`.
        // A buggy implementation that returned the empty vec, included zeros
        // or negatives, dropped a positive entry, duplicated entries, or
        // reordered the output would all be caught here.
        #[test]
        fn matches_filter_reference(l: Vec<i64>) {
            let expected: Vec<i64> = l.iter().copied().filter(|&x| x > 0).collect();
            prop_assert_eq!(get_positive(&l), expected);
        }
    }
}
