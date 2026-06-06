/// HumanEval/108 / CLEVER 107 — `count_nums(arr)`.  Count elements
/// whose *signed* digit sum is > 0.  For negative `n`, the leading
/// digit takes the sign (e.g. `-123 → -1 + 2 + 3 = 4`).
fn first_digit_at(n: i64) -> i64 {
    if n < 10 { n } else { first_digit_at(n / 10) }
}

fn digit_sum_at(n: i64, acc: i64) -> i64 {
    if n == 0 { acc } else { digit_sum_at(n / 10, acc + n % 10) }
}

fn signed_digit_sum(n: i64) -> i64 {
    if n == 0 { 0 }
    else if n > 0 { digit_sum_at(n, 0) }
    else {
        let m = -n;
        digit_sum_at(m, 0) - 2 * first_digit_at(m)
    }
}

fn count_at(arr: &[i64], i: usize, acc: i64) -> i64 {
    if i >= arr.len() { acc }
    else if signed_digit_sum(arr[i]) > 0 { count_at(arr, i + 1, acc + 1) }
    else { count_at(arr, i + 1, acc) }
}

pub fn count_nums(arr: &[i64]) -> i64 {
    count_at(arr, 0, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known() {
        assert_eq!(count_nums(&[]), 0);
        assert_eq!(count_nums(&[-1, 11, -11]), 1);  // 11 only
        assert_eq!(count_nums(&[1, 1, 2]), 3);
    }
}
