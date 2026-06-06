/// Apply a linear shift to a list so the smallest number becomes 0.
/// Integer version of the float "scale to [0,1]" contract — without floats
/// we cannot also force the largest to be 1, so the contract is restricted
/// to the shift (subtract min). Length must be ≥ 2.
fn min_at(numbers: &[i64], i: usize, m: i64) -> i64 {
    if i >= numbers.len() {
        m
    } else if numbers[i] < m {
        min_at(numbers, i + 1, numbers[i])
    } else {
        min_at(numbers, i + 1, m)
    }
}

fn shift_at(numbers: &[i64], delta: i64, i: usize, mut acc: Vec<i64>) -> Vec<i64> {
    if i >= numbers.len() {
        acc
    } else {
        acc.push(numbers[i] - delta);
        shift_at(numbers, delta, i + 1, acc)
    }
}

pub fn rescale_to_unit(numbers: &[i64]) -> Vec<i64> {
    if numbers.len() < 2 {
        Vec::new()
    } else {
        let m = min_at(numbers, 1, numbers[0]);
        shift_at(numbers, m, 0, Vec::new())
    }
}
