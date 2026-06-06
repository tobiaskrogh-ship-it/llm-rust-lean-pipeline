/// Check if in given list of numbers, are any two numbers closer to each
/// other than given threshold.
pub fn has_close_elements(numbers: &[f64], threshold: f64) -> bool {
    let n = numbers.len();
    let mut i = 0;
    while i < n {
        let mut j = 0;
        while j < n {
            if i != j {
                let diff = (numbers[i] - numbers[j]).abs();
                if diff < threshold {
                    return true;
                }
            }
            j += 1;
        }
        i += 1;
    }
    false
}
