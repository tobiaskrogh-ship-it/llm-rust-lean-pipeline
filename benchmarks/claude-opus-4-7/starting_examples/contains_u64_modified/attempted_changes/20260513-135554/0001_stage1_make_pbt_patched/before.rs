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
