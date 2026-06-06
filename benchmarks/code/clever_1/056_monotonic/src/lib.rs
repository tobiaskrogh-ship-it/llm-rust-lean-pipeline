/// HumanEval/57 — `monotonic(l)`.  Returns true iff the elements of `l`
/// are monotonically increasing OR monotonically decreasing.  Lists of
/// length 0 or 1 are vacuously both, so the answer is `true`.
///
/// Implemented as two tail-recursive scans over the slice.  Note the
/// `||` short-circuit guards no partial operation here (both helpers
/// are total), so it survives Hax extraction faithfully.
fn is_nondecreasing_from(l: &[i64], i: u64) -> bool {
    let n = l.len() as u64;
    if i + 1 >= n {
        true
    } else if l[i as usize] > l[(i + 1) as usize] {
        false
    } else {
        is_nondecreasing_from(l, i + 1)
    }
}

fn is_nonincreasing_from(l: &[i64], i: u64) -> bool {
    let n = l.len() as u64;
    if i + 1 >= n {
        true
    } else if l[i as usize] < l[(i + 1) as usize] {
        false
    } else {
        is_nonincreasing_from(l, i + 1)
    }
}

pub fn monotonic(l: &[i64]) -> bool {
    if is_nondecreasing_from(l, 0) {
        true
    } else {
        is_nonincreasing_from(l, 0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Brute-force oracle: scan all adjacent pairs.
    fn naive_monotonic(l: &[i64]) -> bool {
        let mut up_ok = true;
        let mut down_ok = true;
        for i in 0..l.len().saturating_sub(1) {
            if l[i] > l[i + 1] {
                up_ok = false;
            }
            if l[i] < l[i + 1] {
                down_ok = false;
            }
        }
        up_ok || down_ok
    }

    /// Boundary: empty list and singleton are monotonic.
    #[test]
    fn small_lists_are_monotonic() {
        assert!(monotonic(&[]));
        assert!(monotonic(&[7]));
    }

    proptest! {
        /// Main postcondition: agrees with the brute-force oracle on random lists.
        #[test]
        fn matches_brute_force(l in proptest::collection::vec(-100i64..=100, 0..12)) {
            prop_assert_eq!(monotonic(&l), naive_monotonic(&l));
        }

        /// Non-strict monotonicity: a constant list is monotonic.
        /// This pins down the semantic claim that the comparison is `>`/`<`
        /// (not `>=`/`<=`) — i.e. plateaus are allowed. A buggy implementation
        /// using strict comparisons would still satisfy `matches_brute_force`
        /// on strictly-varying lists, so this is an independent contract clause.
        #[test]
        fn constant_list_is_monotonic(c in -1000i64..=1000, n in 0usize..10) {
            let v = vec![c; n];
            prop_assert!(monotonic(&v));
        }
    }
}
