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

    /// Brute-force oracle.
    fn naive_pluck(l: &[i64]) -> Vec<i64> {
        let mut best: Option<(i64, usize)> = None;
        for (i, &x) in l.iter().enumerate() {
            if x.rem_euclid(2) == 0 || x % 2 == 0 {
                match best {
                    None => best = Some((x, i)),
                    Some((bv, _)) if x < bv => best = Some((x, i)),
                    _ => {}
                }
            }
        }
        match best {
            Some((v, i)) => vec![v, i as i64],
            None => vec![],
        }
    }

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
        /// Postcondition: matches the brute-force oracle.
        #[test]
        fn matches_brute_force(l in proptest::collection::vec(0i64..=200, 0..16)) {
            prop_assert_eq!(pluck(&l), naive_pluck(&l));
        }

        /// If non-empty, the value field is even and is an element of `l`.
        #[test]
        fn returned_value_is_even_and_present(l in proptest::collection::vec(0i64..=200, 0..16)) {
            let r = pluck(&l);
            if !r.is_empty() {
                prop_assert!(r[0] % 2 == 0);
                prop_assert!(l.contains(&r[0]));
            }
        }
    }
}
