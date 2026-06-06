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
    fn naive(l: &[i64]) -> Option<i64> {
        let mut s: Vec<i64> = l.iter().copied().collect();
        s.sort(); s.dedup();
        if s.len() < 2 { None } else { Some(s[1]) }
    }
    proptest! {
        #[test]
        fn matches(l in proptest::collection::vec(-50i64..=50, 0..12)) {
            prop_assert_eq!(next_smallest(&l), naive(&l));
        }
    }
}
