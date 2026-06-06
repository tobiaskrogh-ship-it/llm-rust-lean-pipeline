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
fn insert_sorted(v: Vec<i64>, x: i64) -> Vec<i64> {
    let mut result: Vec<i64> = Vec::new();
    let n = v.len();
    let mut i: usize = 0;
    let mut inserted = false;
    while i < n {
        if !inserted && v[i] >= x {
            result.push(x);
            inserted = true;
        }
        result.push(v[i]);
        i += 1;
    }
    if !inserted {
        result.push(x);
    }
    result
}

fn sort_at(l: &[i64], i: usize, sorted: Vec<i64>) -> Vec<i64> {
    if i >= l.len() {
        sorted
    } else {
        sort_at(l, i + 1, insert_sorted(sorted, l[i]))
    }
}

fn build_strange_at(sorted: &[i64], taken: usize, mut acc: Vec<i64>) -> Vec<i64> {
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
        acc.push(sorted[idx]);
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
        /// Postcondition: matches the brute-force oracle.
        #[test]
        fn matches_brute_force(l in proptest::collection::vec(-100i64..=100, 0..12)) {
            prop_assert_eq!(strange_sort_list(&l), naive_strange_sort(&l));
        }

        /// Length preservation: same number of elements as input.
        #[test]
        fn length_preserved(l in proptest::collection::vec(-100i64..=100, 0..12)) {
            prop_assert_eq!(strange_sort_list(&l).len(), l.len());
        }

        /// Multiset preservation: result is a permutation of the input.
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
