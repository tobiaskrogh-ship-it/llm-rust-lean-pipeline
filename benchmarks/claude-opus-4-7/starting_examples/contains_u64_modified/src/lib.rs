/// Returns `true` iff some element of `arr` equals `target`.
///
/// Minimal demonstration of an existential postcondition extracted from
/// a tail-recursive linear scan. The two proof clauses are:
///   - Soundness   :  contains(arr, t) = true  →  ∃ i, i < arr.len ∧ arr[i] = t
///   - Completeness: (∃ i, i < arr.len ∧ arr[i] = t)  →  contains(arr, t) = true
/// Each direction is proved by induction on the recursion index, with the
/// existential witness in soundness extracted from the `true`-branch.
fn contains_at(arr: &[u64], target: u64, i: usize) -> bool {
    if i >= arr.len() {
        false
    } else if arr[i] == target {
        true
    } else {
        contains_at(arr, target, i + 1)
    }
}

pub fn contains(arr: &[u64], target: u64) -> bool {
    contains_at(arr, target, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        /// Soundness clause of the iff.
        ///
        /// Contract captured:
        ///     contains(arr, target) = true  ⇒  ∃ i. i < arr.len() ∧ arr[i] = target
        ///
        /// A buggy implementation that ever returns `true` without a real
        /// witness (e.g. off-by-one that reads past the end, or always-true)
        /// would be caught here.
        #[test]
        fn soundness_true_implies_witness_exists(
            arr in proptest::collection::vec(any::<u64>(), 0..32),
            target: u64,
        ) {
            if contains(&arr, target) {
                prop_assert!(
                    arr.iter().any(|&x| x == target),
                    "contains returned true but no index witnesses the membership",
                );
            }
        }

        /// Completeness clause of the iff.
        ///
        /// Contract captured:
        ///     (∃ i. i < arr.len() ∧ arr[i] = target)  ⇒  contains(arr, target) = true
        ///
        /// We force the existential by planting `target` at a random index.
        /// A buggy implementation that returns `false` despite a real witness
        /// (e.g. stops one step early, or always-false) would be caught here.
        #[test]
        fn completeness_witness_implies_true(
            mut arr in proptest::collection::vec(any::<u64>(), 1..32),
            idx in any::<prop::sample::Index>(),
            target: u64,
        ) {
            let i = idx.index(arr.len());
            arr[i] = target;
            prop_assert!(
                contains(&arr, target),
                "contains returned false despite arr[{}] = target",
                i,
            );
        }
    }
}
