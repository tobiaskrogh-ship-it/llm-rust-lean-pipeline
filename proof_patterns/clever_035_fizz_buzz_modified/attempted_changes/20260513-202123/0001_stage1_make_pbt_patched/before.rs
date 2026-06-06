/// Count occurrences of the digit 7 across integers strictly less than n
/// that are divisible by 11 or 13.
fn count_sevens(n: i64) -> i64 {
    if n <= 0 {
        0
    } else if n % 10 == 7 {
        count_sevens(n / 10) + 1
    } else {
        count_sevens(n / 10)
    }
}

fn scan_at(i: i64, n: i64, acc: i64) -> i64 {
    if i >= n {
        acc
    } else if i % 11 == 0 || i % 13 == 0 {
        scan_at(i + 1, n, acc + count_sevens(i))
    } else {
        scan_at(i + 1, n, acc)
    }
}

pub fn fizz_buzz(n: i64) -> i64 {
    scan_at(0, n, 0)
}
