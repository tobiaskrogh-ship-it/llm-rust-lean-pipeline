/// HumanEval/58 — `common(l1, l2)`.  Return the unique common elements
/// of two lists, in order of first appearance in `l1`.
///
/// Note: CLEVER's reference returns the common elements sorted.  Here
/// we return them in `l1`-appearance order; the unique-set is the same
/// either way, and the property tests treat the output as a set.
fn contains_at(l: &[i64], x: i64, i: usize) -> bool {
    if i >= l.len() {
        false
    } else if l[i] == x {
        true
    } else {
        contains_at(l, x, i + 1)
    }
}

fn build_common_at(l1: &[i64], l2: &[i64], i: usize, mut acc: Vec<i64>) -> Vec<i64> {
    if i >= l1.len() {
        acc
    } else if contains_at(l2, l1[i], 0) && !contains_at(&acc, l1[i], 0) {
        // Vec::push is unmodeled in the Hax Lean prelude
        // (`alloc.vec.Impl_1.push`). Use `extend_from_slice` with a typed
        // size-1 array so the size appears in the let's type annotation
        // and Hax can elaborate `RustArray i64 1`.
        let chunk: [i64; 1] = [l1[i]];
        acc.extend_from_slice(&chunk);
        build_common_at(l1, l2, i + 1, acc)
    } else {
        build_common_at(l1, l2, i + 1, acc)
    }
}

pub fn common(l1: &[i64], l2: &[i64]) -> Vec<i64> {
    build_common_at(l1, l2, 0, Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    use std::collections::HashSet;

    /// Brute-force: take the set intersection.
    fn naive_common(l1: &[i64], l2: &[i64]) -> HashSet<i64> {
        let s1: HashSet<i64> = l1.iter().copied().collect();
        let s2: HashSet<i64> = l2.iter().copied().collect();
        s1.intersection(&s2).copied().collect()
    }

    proptest! {
        /// Postcondition: the output, viewed as a set, equals the
        /// intersection of `l1` and `l2` as sets.
        #[test]
        fn output_set_equals_intersection(
            l1 in proptest::collection::vec(-50i64..=50, 0..16),
            l2 in proptest::collection::vec(-50i64..=50, 0..16),
        ) {
            let result = common(&l1, &l2);
            let result_set: HashSet<i64> = result.iter().copied().collect();
            prop_assert_eq!(result_set, naive_common(&l1, &l2));
        }

        /// Output contains no duplicates.
        #[test]
        fn output_has_no_duplicates(
            l1 in proptest::collection::vec(-50i64..=50, 0..16),
            l2 in proptest::collection::vec(-50i64..=50, 0..16),
        ) {
            let result = common(&l1, &l2);
            let result_set: HashSet<i64> = result.iter().copied().collect();
            prop_assert_eq!(result.len(), result_set.len());
        }
    }
}
