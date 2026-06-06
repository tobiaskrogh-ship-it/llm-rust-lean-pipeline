/// HumanEval/47 — `median(l)`.  Returns a median of the integer list.
///
/// Note: CLEVER's reference returns a `float` (the average of the two
/// central elements for even-length lists).  Mapped to `i64` here by
/// returning the **lower** median of the two central elements when the
/// length is even — the same convention used by quickselect-based
/// integer medians.  Semantics are preserved on odd-length lists, where
/// the median is the unique central element.  For an empty input the
/// function returns `0` as a degenerate sentinel.
fn count_strictly_less(l: &[i64], m: i64, i: usize) -> u64 {
    if i >= l.len() {
        0
    } else if l[i] < m {
        1 + count_strictly_less(l, m, i + 1)
    } else {
        count_strictly_less(l, m, i + 1)
    }
}

fn count_strictly_greater(l: &[i64], m: i64, i: usize) -> u64 {
    if i >= l.len() {
        0
    } else if l[i] > m {
        1 + count_strictly_greater(l, m, i + 1)
    } else {
        count_strictly_greater(l, m, i + 1)
    }
}

/// Pick any l[i] satisfying the lower-median property.  The first one
/// scanned will satisfy it because the property is satisfied by exactly
/// one value (or the smaller of two adjacent ones on even lengths).
fn find_median_at(l: &[i64], i: usize) -> i64 {
    let n = l.len() as u64;
    if n == 0 {
        0
    } else if i >= l.len() {
        0
    } else {
        let half = (n - 1) / 2;
        let lt = count_strictly_less(l, l[i], 0);
        let gt = count_strictly_greater(l, l[i], 0);
        if lt <= half && gt + 1 + half <= n {
            l[i]
        } else {
            find_median_at(l, i + 1)
        }
    }
}

pub fn median(l: &[i64]) -> i64 {
    find_median_at(l, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Brute-force oracle: sort and take the lower-of-two-central element
    /// (or the unique central element for odd-length lists).
    fn naive_median(l: &[i64]) -> i64 {
        if l.is_empty() {
            return 0;
        }
        let mut v = l.to_vec();
        v.sort();
        v[(v.len() - 1) / 2]
    }

    /// Boundary: empty list returns 0.
    #[test]
    fn empty_returns_zero() {
        assert_eq!(median(&[]), 0);
    }

    /// Single element list: median is that element.
    #[test]
    fn singleton_returns_element() {
        assert_eq!(median(&[42]), 42);
        assert_eq!(median(&[-7]), -7);
    }

    /// Convention clause: on even-length lists, the **lower** of the two
    /// central elements is returned (the docstring calls this out as a
    /// deliberate i64-vs-float design choice).  A buggy implementation
    /// returning the upper median would fail here.
    #[test]
    fn even_length_returns_lower_median() {
        // Central elements are 2 and 3; lower median is 2.
        assert_eq!(median(&[1, 2, 3, 4]), 2);
        // Same multiset, different order — convention is order-independent.
        assert_eq!(median(&[4, 3, 2, 1]), 2);
    }

    proptest! {
        /// Postcondition: agrees with brute-force sort-and-pick.
        #[test]
        fn matches_brute_force(l in proptest::collection::vec(-100i64..=100, 1..12)) {
            prop_assert_eq!(median(&l), naive_median(&l));
        }

        /// The returned value must actually be an element of the list.
        #[test]
        fn returned_value_is_in_list(l in proptest::collection::vec(-100i64..=100, 1..12)) {
            let m = median(&l);
            prop_assert!(l.contains(&m));
        }
    }
}
