/// HumanEval/126 / CLEVER 125 — `is_sorted(lst)`.  True iff `lst` is in
/// non-decreasing order AND no value appears more than twice.  Override
/// to `u64` per docstring's "no negative numbers".
fn count_at(l: &[u64], v: u64, i: usize, acc: u64) -> u64 {
    if i >= l.len() { acc }
    else if l[i] == v { count_at(l, v, i + 1, acc + 1) }
    else { count_at(l, v, i + 1, acc) }
}

fn check_at(l: &[u64], i: usize) -> bool {
    if i >= l.len() { true }
    else {
        if i + 1 < l.len() && l[i] > l[i + 1] { return false; }
        if count_at(l, l[i], 0, 0) > 2 { return false; }
        check_at(l, i + 1)
    }
}

pub fn is_sorted(lst: &[u64]) -> bool {
    check_at(lst, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Brute-force oracle for the full contract:
    /// `is_sorted(l)` iff `l` is non-decreasing AND no value appears more than twice.
    fn naive_is_sorted(l: &[u64]) -> bool {
        // non-decreasing check
        for i in 0..l.len().saturating_sub(1) {
            if l[i] > l[i + 1] {
                return false;
            }
        }
        // multiplicity check: every value occurs at most twice
        for &v in l {
            let c = l.iter().filter(|&&w| w == v).count();
            if c > 2 {
                return false;
            }
        }
        true
    }

    /// Boundary cases plus the original hand-picked examples covering
    /// each clause in isolation: empty, sorted-unique, sorted-with-doubles,
    /// triple repeat (multiplicity violation), and a strict inversion
    /// (sortedness violation).
    #[test]
    fn known() {
        assert!(is_sorted(&[]));
        assert!(is_sorted(&[1, 2, 3]));
        assert!(is_sorted(&[1, 1, 2]));         // exactly 2 of 1
        assert!(!is_sorted(&[1, 1, 1]));        // 3 of 1
        assert!(!is_sorted(&[3, 2, 1]));
        assert!(is_sorted(&[1, 2, 2, 3]));
    }

    proptest! {
        /// Main postcondition: agrees with the brute-force oracle on random lists.
        /// The value range `0..5` paired with length up to 8 guarantees that
        /// triple-duplicates, sorted-with-doubles, and unsorted samples all
        /// appear with high frequency, exercising both clauses in both directions.
        #[test]
        fn matches_brute_force(l in proptest::collection::vec(0u64..5, 0..8)) {
            prop_assert_eq!(is_sorted(&l), naive_is_sorted(&l));
        }

        /// Multiplicity-clause negative pin-down: any value appearing 3+ times
        /// must be rejected, regardless of value magnitude. This is independent
        /// of the sortedness clause — a buggy implementation that only checked
        /// order (or that only counted small values) would still pass
        /// `matches_brute_force` on samples where the multiplicity violation
        /// happens to coincide with an order violation, but would fail here.
        #[test]
        fn triple_repeat_rejected(v in 0u64..1_000_000, k in 3usize..6) {
            let lst = vec![v; k];
            prop_assert!(!is_sorted(&lst));
        }
    }
}
