/// Remove all elements that occur more than once in `numbers`. Elements
/// kept appear in their original input order.
fn count_at(numbers: &[i64], target: i64, i: usize, acc: i64) -> i64 {
    if i >= numbers.len() {
        acc
    } else if numbers[i] == target {
        count_at(numbers, target, i + 1, acc + 1)
    } else {
        count_at(numbers, target, i + 1, acc)
    }
}

fn build_at(numbers: &[i64], i: usize, mut acc: Vec<i64>) -> Vec<i64> {
    if i >= numbers.len() {
        acc
    } else if count_at(numbers, numbers[i], 0, 0) == 1 {
        acc.push(numbers[i]);
        build_at(numbers, i + 1, acc)
    } else {
        build_at(numbers, i + 1, acc)
    }
}

pub fn remove_duplicates(numbers: &[i64]) -> Vec<i64> {
    build_at(numbers, 0, Vec::new())
}
