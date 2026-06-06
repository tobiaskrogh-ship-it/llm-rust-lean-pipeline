/// HumanEval/155 / CLEVER 153 — `even_odd_count(num)`.  Return
/// `(even_count, odd_count)` of the decimal digits of `num`.  For
/// `num == 0` we count one digit `0`, which is even → `(1, 0)`.
fn count_at(n: u64, e: u64, o: u64) -> (u64, u64) {
    if n == 0 { (e, o) }
    else if (n % 10) % 2 == 0 { count_at(n / 10, e + 1, o) }
    else { count_at(n / 10, e, o + 1) }
}

pub fn even_odd_count(num: u64) -> (u64, u64) {
    if num == 0 { (1, 0) } else { count_at(num, 0, 0) }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known() {
        assert_eq!(even_odd_count(0), (1, 0));
        assert_eq!(even_odd_count(7), (0, 1));
        assert_eq!(even_odd_count(12), (1, 1));
        assert_eq!(even_odd_count(123), (1, 2));
        assert_eq!(even_odd_count(246), (3, 0));
    }
}
