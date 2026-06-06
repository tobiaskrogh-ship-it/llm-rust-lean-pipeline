/// Check if in given list of numbers, are any two numbers closer to each
/// other than the given threshold.
///
/// Note: CLEVER's reference signature is `(numbers: List[float], threshold:
/// float) -> bool`. Translated to `i64` here because the Hax Lean prelude has
/// gaps in `f64` support (no `Impl.abs`, no `PartialOrd f64 f64`, no `Neg
/// f64`, and `Sub.sub` is emitted without type arguments for non-integer
/// types). Semantics are preserved up to integer arithmetic.
fn has_close_elements_at(numbers: &[i64], threshold: i64, k: u64) -> bool {
    let n = numbers.len() as u64;
    if k >= n * n {
        false
    } else {
        let i = (k / n) as usize;
        let j = (k % n) as usize;
        let diff = if numbers[i] > numbers[j] {
            numbers[i] - numbers[j]
        } else {
            numbers[j] - numbers[i]
        };
        if i != j && diff < threshold {
            true
        } else {
            has_close_elements_at(numbers, threshold, k + 1)
        }
    }
}

pub fn has_close_elements(numbers: &[i64], threshold: i64) -> bool {
    has_close_elements_at(numbers, threshold, 0)
}
