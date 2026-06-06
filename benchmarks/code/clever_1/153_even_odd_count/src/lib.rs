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
    use proptest::prelude::*;

    #[test]
    fn known() {
        assert_eq!(even_odd_count(0), (1, 0));
        assert_eq!(even_odd_count(7), (0, 1));
        assert_eq!(even_odd_count(12), (1, 1));
        assert_eq!(even_odd_count(123), (1, 2));
        assert_eq!(even_odd_count(246), (3, 0));
    }

    /// Reference using an entirely different decomposition (string-based)
    /// so that bugs in the arithmetic recursion of `even_odd_count`
    /// would not be mirrored here.
    fn reference_count(num: u64) -> (u64, u64) {
        if num == 0 {
            return (1, 0);
        }
        let mut e: u64 = 0;
        let mut o: u64 = 0;
        for c in num.to_string().chars() {
            let d = c.to_digit(10).unwrap() as u64;
            if d % 2 == 0 {
                e += 1;
            } else {
                o += 1;
            }
        }
        (e, o)
    }

    proptest! {
        /// Postcondition: the returned `(even, odd)` pair equals the
        /// counts of even and odd decimal digits of `num`. Verified
        /// against an independent string-based reference.
        #[test]
        fn matches_reference(num in any::<u64>()) {
            prop_assert_eq!(even_odd_count(num), reference_count(num));
        }
    }
}
