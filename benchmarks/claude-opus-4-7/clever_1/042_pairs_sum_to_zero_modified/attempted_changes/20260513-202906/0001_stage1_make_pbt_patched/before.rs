/// Return true iff two distinct positions in `numbers` hold values that
/// sum to zero.
///
/// Note: with the `u64` type pinned by CLEVER, the only pair summing to 0
/// is two zero entries. A richer formulation requires `&[i64]`.
fn count_zeros_at(numbers: &[u64], i: usize, acc: u64) -> u64 {
    if i >= numbers.len() {
        acc
    } else if numbers[i] == 0 {
        count_zeros_at(numbers, i + 1, acc + 1)
    } else {
        count_zeros_at(numbers, i + 1, acc)
    }
}

pub fn pairs_sum_to_zero(numbers: &[u64]) -> bool {
    count_zeros_at(numbers, 0, 0) >= 2
}
