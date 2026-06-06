/// Return true iff three distinct positions in `numbers` hold values that
/// sum to zero.
///
/// Note: CLEVER pins the type as `u64`, so the only way three non-negative
/// values can sum to 0 is if all three are 0. The function therefore
/// reduces to "at least three zero entries". A semantically richer
/// formulation requires `&[i64]`.
fn count_zeros_at(numbers: &[u64], i: usize, acc: u64) -> u64 {
    if i >= numbers.len() {
        acc
    } else if numbers[i] == 0 {
        count_zeros_at(numbers, i + 1, acc + 1)
    } else {
        count_zeros_at(numbers, i + 1, acc)
    }
}

pub fn triples_sum_to_zero(numbers: &[u64]) -> bool {
    count_zeros_at(numbers, 0, 0) >= 3
}
