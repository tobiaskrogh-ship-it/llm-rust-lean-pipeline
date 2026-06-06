/// For a given number n ≥ 2, find the largest divisor of n that is
/// strictly less than n. For n ≤ 1 returns 0 (no proper divisor exists).
fn largest_divisor_at(n: i64, d: i64) -> i64 {
    if d <= 0 {
        1
    } else if n % d == 0 {
        d
    } else {
        largest_divisor_at(n, d - 1)
    }
}

pub fn largest_divisor(n: i64) -> i64 {
    if n <= 1 {
        0
    } else {
        largest_divisor_at(n, n - 1)
    }
}
