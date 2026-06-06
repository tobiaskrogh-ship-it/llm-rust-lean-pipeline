/// HumanEval/90 / CLEVER 089 — `next_smallest(lst)`.  Return the
/// second-smallest *unique* element of `lst`, or `None` if there's no
/// such element (empty, single element, or all values equal).
fn min_at(l: &[i64], i: usize, best: i64, found: bool) -> (i64, bool) {
    if i >= l.len() { (best, found) }
    else if !found || l[i] < best { min_at(l, i + 1, l[i], true) }
    else { min_at(l, i + 1, best, found) }
}

fn min_above_at(l: &[i64], floor: i64, i: usize, best: i64, found: bool) -> (i64, bool) {
    if i >= l.len() { (best, found) }
    else if l[i] > floor && (!found || l[i] < best) {
        min_above_at(l, floor, i + 1, l[i], true)
    } else {
        min_above_at(l, floor, i + 1, best, found)
    }
}

pub fn next_smallest(lst: &[i64]) -> Option<i64> {
    let (m1, f1) = min_at(lst, 0, 0, false);
    if !f1 { return None; }
    let (m2, f2) = min_above_at(lst, m1, 0, 0, false);
    if f2 { Some(m2) } else { None }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    // --- Failure conditions: returns None ---

    #[test]
    fn empty_is_none() {
        assert_eq!(next_smallest(&[]), None);
    }

    proptest! {
        // All-equal lists have only one unique value, so result must be None.
        #[test]
        fn all_equal_is_none(x in -50i64..=50, n in 1usize..12) {
            let l: Vec<i64> = std::iter::repeat(x).take(n).collect();
            prop_assert_eq!(next_smallest(&l), None);
        }

        // Converse postcondition: if result is None, fewer than 2 distinct values.
        #[test]
        fn none_implies_fewer_than_two_unique(
            l in proptest::collection::vec(-50i64..=50, 0..12)
        ) {
            if next_smallest(&l).is_none() {
                let mut s: Vec<i64> = l.iter().copied().collect();
                s.sort();
                s.dedup();
                prop_assert!(s.len() < 2);
            }
        }

        // --- Success postcondition: when Some(x) ---

        // (1) x must be an element of the list.
        #[test]
        fn some_result_is_in_list(
            l in proptest::collection::vec(-50i64..=50, 0..12)
        ) {
            if let Some(x) = next_smallest(&l) {
                prop_assert!(l.iter().any(|&y| y == x));
            }
        }

        // (2) x is not the minimum: some list element is strictly less than x.
        #[test]
        fn some_result_exceeds_some_element(
            l in proptest::collection::vec(-50i64..=50, 0..12)
        ) {
            if let Some(x) = next_smallest(&l) {
                prop_assert!(l.iter().any(|&y| y < x));
            }
        }

        // (3) x is the *next* smallest: nothing in the list lies strictly
        //     between min(l) and x.
        #[test]
        fn nothing_strictly_between_min_and_result(
            l in proptest::collection::vec(-50i64..=50, 1..12)
        ) {
            if let Some(x) = next_smallest(&l) {
                let m = *l.iter().min().unwrap();
                prop_assert!(!l.iter().any(|&y| m < y && y < x));
            }
        }
    }
}
