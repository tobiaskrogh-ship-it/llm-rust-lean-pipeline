/// HumanEval/52 — `below_threshold(l, t)`.  Return true iff every
/// element of `l` is strictly less than `t`.  The empty list vacuously
/// satisfies the property.
fn all_below_at(l: &[i64], t: i64, i: usize) -> bool {
    if i >= l.len() {
        true
    } else if l[i] >= t {
        false
    } else {
        all_below_at(l, t, i + 1)
    }
}

pub fn below_threshold(l: &[i64], t: i64) -> bool {
    all_below_at(l, t, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Brute-force oracle.
    fn naive_below(l: &[i64], t: i64) -> bool {
        l.iter().all(|x| *x < t)
    }

    /// Boundary: empty list is always below threshold.
    #[test]
    fn empty_is_below_any_threshold() {
        for t in [-1000, -1, 0, 1, 1000] {
            assert!(below_threshold(&[], t));
        }
    }

    proptest! {
        /// Postcondition matches the brute-force oracle.
        #[test]
        fn matches_brute_force(
            l in proptest::collection::vec(-1000i64..=1000, 0..16),
            t in -1000i64..=1000,
        ) {
            prop_assert_eq!(below_threshold(&l, t), naive_below(&l, t));
        }

        /// Soundness ("true" direction): if reported `true`, no element is ≥ t.
        #[test]
        fn no_false_positive(
            l in proptest::collection::vec(-1000i64..=1000, 0..16),
            t in -1000i64..=1000,
        ) {
            if below_threshold(&l, t) {
                for &x in &l {
                    prop_assert!(x < t);
                }
            }
        }

        /// Completeness ("false" direction): if some element is ≥ t,
        /// reported `false`.
        #[test]
        fn no_false_negative(
            l in proptest::collection::vec(-1000i64..=1000, 0..16),
            t in -1000i64..=1000,
        ) {
            if l.iter().any(|x| *x >= t) {
                prop_assert!(!below_threshold(&l, t));
            }
        }
    }
}
