/// HumanEval/68 — `pluck(l)`.  Find the smallest even value's
/// `[value, index]` pair in `l`.  Ties on value broken by smallest
/// index.  Returns an empty list if no even value (or empty input).
///
/// Note: CLEVER's spec restricts inputs to non-negative integers.  The
/// implementation accepts any `i64`; on a non-negative domain it is
/// faithful to the spec.  On a list containing negatives the
/// "smallest even" interpretation is the arithmetically smallest, which
/// is a reasonable extension.
fn smallest_even_at(l: &[i64], i: usize, best: i64, found: bool) -> (i64, bool) {
    if i >= l.len() {
        (best, found)
    } else if l[i] % 2 == 0 && (!found || l[i] < best) {
        smallest_even_at(l, i + 1, l[i], true)
    } else {
        smallest_even_at(l, i + 1, best, found)
    }
}

fn first_index_of(l: &[i64], target: i64, i: usize) -> u64 {
    if i >= l.len() {
        0
    } else if l[i] == target {
        i as u64
    } else {
        first_index_of(l, target, i + 1)
    }
}

pub fn pluck(l: &[i64]) -> Vec<i64> {
    let (val, found) = smallest_even_at(l, 0, 0, false);
    if !found {
        Vec::new()
    } else {
        let idx = first_index_of(l, val, 0) as i64;
        let mut result = Vec::new();
        result.push(val);
        result.push(idx);
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Boundary: empty list returns empty.
    #[test]
    fn empty_returns_empty() {
        assert_eq!(pluck(&[]), Vec::<i64>::new());
    }

    /// Boundary: no even values returns empty.
    #[test]
    fn all_odd_returns_empty() {
        assert_eq!(pluck(&[1, 3, 5, 7]), Vec::<i64>::new());
    }

    proptest! {
        /// Structural postcondition: result is either empty or `[value, index]`
        /// with `index` a valid position into `l`.
        #[test]
        fn output_shape(l in proptest::collection::vec(0i64..=200, 0..16)) {
            let r = pluck(&l);
            if !r.is_empty() {
                prop_assert_eq!(r.len(), 2);
                prop_assert!(r[1] >= 0);
                prop_assert!((r[1] as usize) < l.len());
            }
        }

        /// Existence characterization: result is non-empty iff `l` contains an even value.
        #[test]
        fn nonempty_iff_has_even(l in proptest::collection::vec(0i64..=200, 0..16)) {
            let has_even = l.iter().any(|x| x % 2 == 0);
            prop_assert_eq!(!pluck(&l).is_empty(), has_even);
        }

        /// Minimality of value: when non-empty, the returned value is even and is
        /// less than or equal to every even element of `l`.
        #[test]
        fn value_is_minimum_even(l in proptest::collection::vec(0i64..=200, 0..16)) {
            let r = pluck(&l);
            if !r.is_empty() {
                let v = r[0];
                prop_assert!(v % 2 == 0);
                for &x in &l {
                    if x % 2 == 0 {
                        prop_assert!(v <= x);
                    }
                }
            }
        }

        /// First-occurrence index: when non-empty, the index points to a position
        /// whose element equals the returned value, and no earlier position holds
        /// that value (ties on value broken by smallest index).
        #[test]
        fn index_is_first_occurrence(l in proptest::collection::vec(0i64..=200, 0..16)) {
            let r = pluck(&l);
            if !r.is_empty() {
                let v = r[0];
                let i = r[1] as usize;
                prop_assert!(i < l.len());
                prop_assert_eq!(l[i], v);
                for j in 0..i {
                    prop_assert!(l[j] != v);
                }
            }
        }
    }
}
