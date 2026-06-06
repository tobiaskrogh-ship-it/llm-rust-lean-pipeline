/// HumanEval/69 / CLEVER 068 — `search(numbers)`.  Return the largest
/// integer that is greater than zero and whose frequency in `numbers`
/// is at least its own value.  If no such integer exists, return `0`
/// (since the spec requires the answer to be `> 0`, `0` is a safe
/// sentinel for "no answer").
fn count_occurrences(l: &[u64], v: u64, i: usize) -> u64 {
    if i >= l.len() {
        0
    } else if l[i] == v {
        1 + count_occurrences(l, v, i + 1)
    } else {
        count_occurrences(l, v, i + 1)
    }
}

fn search_at(l: &[u64], i: usize, best: u64) -> u64 {
    if i >= l.len() {
        best
    } else {
        let v = l[i];
        if v > 0 && v > best {
            let c = count_occurrences(l, v, 0);
            if c >= v {
                search_at(l, i + 1, v)
            } else {
                search_at(l, i + 1, best)
            }
        } else {
            search_at(l, i + 1, best)
        }
    }
}

pub fn search(numbers: &[u64]) -> u64 {
    search_at(numbers, 0, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn naive(l: &[u64]) -> u64 {
        let mut best: u64 = 0;
        for &v in l {
            if v > 0 && v > best {
                let c = l.iter().filter(|&&x| x == v).count() as u64;
                if c >= v { best = v; }
            }
        }
        best
    }

    #[test]
    fn small_cases() {
        assert_eq!(search(&[]), 0);
        assert_eq!(search(&[0, 0, 0]), 0);
        assert_eq!(search(&[1, 1, 2]), 1);
        assert_eq!(search(&[2, 2, 2, 1]), 2);
        assert_eq!(search(&[3, 3, 3, 4]), 3);
    }

    proptest! {
        #[test]
        fn matches_oracle(l in proptest::collection::vec(0u64..=10, 0..20)) {
            prop_assert_eq!(search(&l), naive(&l));
        }

        /// If a positive answer is returned, its frequency in `l` ≥ its value.
        #[test]
        fn frequency_invariant(l in proptest::collection::vec(0u64..=10, 0..20)) {
            let r = search(&l);
            if r > 0 {
                let freq = l.iter().filter(|&&x| x == r).count() as u64;
                prop_assert!(freq >= r);
            }
        }

        /// Maximality: no value strictly greater than the result satisfies the
        /// "frequency ≥ self" condition.  Together with `frequency_invariant`
        /// this pins down the result as *the greatest* such value (and also
        /// handles the `r = 0` case: no positive `v` in `l` has `count(v) ≥ v`).
        #[test]
        fn maximality(l in proptest::collection::vec(0u64..=10, 0..20)) {
            let r = search(&l);
            for &v in &l {
                if v > r {
                    let freq = l.iter().filter(|&&x| x == v).count() as u64;
                    prop_assert!(freq < v);
                }
            }
        }
    }
}
