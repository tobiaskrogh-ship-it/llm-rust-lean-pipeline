/// Returns `numbers[index]` if `index < numbers.len()`, else 0.
///
/// Minimal demonstration of slice indexing with explicit bound discharge:
/// the `numbers[index]` access extracts (via Hax) to the partial operator
/// `numbers[index]_?`, and the proof has to show the index is in bounds
/// in the then-branch.
pub fn slice_get(numbers: &[u64], index: usize) -> u64 {
    if index < numbers.len() {
        numbers[index]
    } else {
        0
    }
}
