/// For a given list of integers, return a tuple of (sum, product).
/// Empty sum is 0; empty product is 1.
pub fn sum_product(numbers: &[i64]) -> (i64, i64) {
    let mut sum: i64 = 0;
    let mut product: i64 = 1;
    for &n in numbers {
        sum += n;
        product *= n;
    }
    (sum, product)
}
