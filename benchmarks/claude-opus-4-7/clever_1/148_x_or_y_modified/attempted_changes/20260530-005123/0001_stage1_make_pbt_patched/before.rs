/// HumanEval/150 / CLEVER 148 — `x_or_y(n, x, y)`.  Return `x` if `n` is
/// prime, else `y`.  Canonical CLEVER signature has a typo
/// (`int n: i64, int x: i64, int y: i64`); we interpret it as the
/// natural three-argument shape.  i64 to match canonical despite
/// non-negative spec for `n` (so we don't lose flexibility on x, y).
fn is_prime_at(n: i64, d: i64) -> bool {
    if d * d > n { true }
    else if n % d == 0 { false }
    else { is_prime_at(n, d + 1) }
}

fn is_prime(n: i64) -> bool {
    if n < 2 { false } else { is_prime_at(n, 2) }
}

pub fn x_or_y(n: i64, x: i64, y: i64) -> i64 {
    if is_prime(n) { x } else { y }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known() {
        assert_eq!(x_or_y(7, 34, 12), 34);
        assert_eq!(x_or_y(15, 8, 5), 5);
        assert_eq!(x_or_y(2, 1, 0), 1);
        assert_eq!(x_or_y(1, 7, 9), 9);
    }
}
