/// Return the list of prime factors of n in non-decreasing order,
/// repeated by multiplicity. (n ≥ 2; for n ≤ 1 returns an empty list.)
fn factorize_at(n: i64, p: i64, mut acc: Vec<i64>) -> Vec<i64> {
    if n <= 1 {
        acc
    } else if p * p > n {
        acc.push(n);
        acc
    } else if n % p == 0 {
        acc.push(p);
        factorize_at(n / p, p, acc)
    } else {
        factorize_at(n, p + 1, acc)
    }
}

pub fn factorize(n: i64) -> Vec<i64> {
    if n <= 1 {
        Vec::new()
    } else {
        factorize_at(n, 2, Vec::new())
    }
}
