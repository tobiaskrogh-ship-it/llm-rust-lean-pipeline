/// For a given list of input numbers, calculate the mean absolute deviation
/// around the mean:  MAD = average | x - x_mean |.
///
/// Note: CLEVER's reference signature is `(numbers: List[float]) -> float`.
/// Translated to `i64` because the Hax Lean prelude has gaps in `f64`
/// support (missing `Impl.abs`, `PartialOrd`, `Neg`, broken `Sub.sub` for
/// non-integer types). Integer arithmetic loses fractional precision on the
/// mean and the deviation sum compared to the `f64` reference, but the
/// shape of the contract (average absolute distance from the mean) is the
/// same.
fn sum_from(numbers: &[i64], i: usize) -> i64 {
    if i >= numbers.len() {
        0
    } else {
        numbers[i] + sum_from(numbers, i + 1)
    }
}

fn abs_dev_sum_from(numbers: &[i64], mean: i64, i: usize) -> i64 {
    if i >= numbers.len() {
        0
    } else {
        let d = numbers[i] - mean;
        let abs_d = if d >= 0 { d } else { -d };
        abs_d + abs_dev_sum_from(numbers, mean, i + 1)
    }
}

pub fn mean_absolute_deviation(numbers: &[i64]) -> i64 {
    let n = numbers.len() as i64;
    if n == 0 {
        0
    } else {
        let mean = sum_from(numbers, 0) / n;
        abs_dev_sum_from(numbers, mean, 0) / n
    }
}
