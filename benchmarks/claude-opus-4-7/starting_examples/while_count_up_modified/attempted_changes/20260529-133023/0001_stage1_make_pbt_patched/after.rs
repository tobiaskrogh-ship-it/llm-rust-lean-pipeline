/// DO NOT REWRITE TO USE RECURSION
pub fn count_up_while(n: u64) -> u64 {
    let mut i = 0;
    while i < n {
        i += 1;
    }
    i
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Boundary: count_up_while(0) returns 0 without entering the loop.
    #[test]
    fn zero_returns_zero() {
        assert_eq!(count_up_while(0), 0);
    }

    /// Known small values guard against off-by-one errors.
    #[test]
    fn known_values() {
        assert_eq!(count_up_while(1), 1);
        assert_eq!(count_up_while(5), 5);
        assert_eq!(count_up_while(100), 100);
    }

    proptest! {
        /// Postcondition: the function returns its input.
        /// Bounded to keep test time reasonable since the loop is O(n).
        #[test]
        fn returns_n(n in 0u64..10_000) {
            prop_assert_eq!(count_up_while(n), n);
        }
    }
}
