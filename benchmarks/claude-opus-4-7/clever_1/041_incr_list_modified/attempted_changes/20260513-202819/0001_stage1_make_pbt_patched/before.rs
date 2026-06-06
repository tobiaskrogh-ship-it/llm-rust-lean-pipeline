/// Return a new list where each element of `numbers` is incremented by 1.
fn incr_at(numbers: &[i64], i: usize, mut acc: Vec<i64>) -> Vec<i64> {
    if i >= numbers.len() {
        acc
    } else {
        acc.push(numbers[i] + 1);
        incr_at(numbers, i + 1, acc)
    }
}

pub fn incr_list(numbers: &[i64]) -> Vec<i64> {
    incr_at(numbers, 0, Vec::new())
}
