/// HumanEval/139 / CLEVER 137 — `special_factorial(n)`.  Brazilian
/// factorial: `n! * (n-1)! * (n-2)! * ... * 1!` for `n >= 1`.
/// Convention: returns 1 for n == 0.
fn factorial_at(k: u64, cur: u64, acc: u64) -> u64 {
    if cur > k { acc } else { factorial_at(k, cur + 1, acc * cur) }
}

fn build_at(n: u64, k: u64, acc: u64) -> u64 {
    if k > n { acc }
    else { build_at(n, k + 1, acc * factorial_at(k, 1, 1)) }
}

pub fn special_factorial(n: u64) -> u64 {
    if n == 0 { 1 } else { build_at(n, 1, 1) }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known() {
        assert_eq!(special_factorial(0), 1);
        assert_eq!(special_factorial(1), 1);            // 1!
        assert_eq!(special_factorial(2), 2);            // 1! * 2!
        assert_eq!(special_factorial(3), 12);           // 1! * 2! * 3!
        assert_eq!(special_factorial(4), 288);          // 1 * 2 * 6 * 24
    }
}
