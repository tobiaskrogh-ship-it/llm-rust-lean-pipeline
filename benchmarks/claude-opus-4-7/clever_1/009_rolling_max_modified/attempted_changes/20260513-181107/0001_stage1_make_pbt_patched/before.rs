/// From a given list of integers, generate a list of the rolling maximum
/// element found until each position in the sequence.
/// (CLEVER's signature column for problem 9 lists `sum_product(...) -> (int, int)`
/// but its docstring describes rolling-max. We follow the docstring.)
pub fn rolling_max(numbers: &[i64]) -> Vec<i64> {
    let mut result: Vec<i64> = Vec::new();
    let mut max_so_far: i64 = i64::MIN;
    for &n in numbers {
        if n > max_so_far {
            max_so_far = n;
        }
        result.push(max_so_far);
    }
    result
}
