/// Insert `delimiter` between every two consecutive elements of `numbers`.
pub fn intersperse(numbers: &[i64], delimiter: i64) -> Vec<i64> {
    let mut result: Vec<i64> = Vec::new();
    let mut first = true;
    for &n in numbers {
        if !first {
            result.push(delimiter);
        }
        result.push(n);
        first = false;
    }
    result
}
