/// From a supplied list of numbers (length ≥ 2), select the pair with the
/// smallest absolute difference and return them as `(smaller, larger)`.
fn abs_diff(a: i64, b: i64) -> i64 {
    if a > b { a - b } else { b - a }
}

fn scan_at(
    numbers: &[i64],
    i: usize,
    j: usize,
    best_i: usize,
    best_j: usize,
) -> (usize, usize) {
    let n = numbers.len();
    if i + 1 >= n {
        (best_i, best_j)
    } else if j >= n {
        scan_at(numbers, i + 1, i + 2, best_i, best_j)
    } else {
        let cur = abs_diff(numbers[i], numbers[j]);
        let best = abs_diff(numbers[best_i], numbers[best_j]);
        if cur < best {
            scan_at(numbers, i, j + 1, i, j)
        } else {
            scan_at(numbers, i, j + 1, best_i, best_j)
        }
    }
}

pub fn find_closest_elements(numbers: &[i64]) -> (i64, i64) {
    if numbers.len() < 2 {
        (0, 0)
    } else {
        let (i, j) = scan_at(numbers, 0, 1, 0, 1);
        if numbers[i] <= numbers[j] {
            (numbers[i], numbers[j])
        } else {
            (numbers[j], numbers[i])
        }
    }
}
