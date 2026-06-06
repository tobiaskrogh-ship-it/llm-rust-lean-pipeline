/// For a given list of input numbers, calculate Mean Absolute Deviation
/// around the mean:  MAD = average | x - x_mean |
pub fn mean_absolute_deviation(numbers: &[f64]) -> f64 {
    let n = numbers.len() as f64;
    let mut sum: f64 = 0.0;
    for &x in numbers {
        sum += x;
    }
    let mean = sum / n;
    let mut acc: f64 = 0.0;
    for &x in numbers {
        acc += (x - mean).abs();
    }
    acc / n
}
