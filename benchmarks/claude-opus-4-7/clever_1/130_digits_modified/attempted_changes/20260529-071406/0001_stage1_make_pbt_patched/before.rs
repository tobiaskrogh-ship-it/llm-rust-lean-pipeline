/// HumanEval/131 / CLEVER 130 — `digits(n)`.  Product of the odd digits
/// of `n`.  Return `0` if all digits are even (or n == 0).
fn walk_at(n: u64, acc: u64, any_odd: bool) -> u64 {
    if n == 0 { if any_odd { acc } else { 0 } }
    else {
        let d = n % 10;
        if d % 2 == 1 { walk_at(n / 10, acc * d, true) }
        else { walk_at(n / 10, acc, any_odd) }
    }
}

pub fn digits(n: u64) -> u64 {
    if n == 0 { 0 } else { walk_at(n, 1, false) }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known() {
        assert_eq!(digits(0), 0);
        assert_eq!(digits(1), 1);
        assert_eq!(digits(4), 0);          // all even
        assert_eq!(digits(235), 15);       // 3 * 5
        assert_eq!(digits(2468), 0);
        assert_eq!(digits(2222), 0);
    }
}
