pub fn is_zero(x: u8) -> bool {
    x == 0
}


#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    // Postcondition (zero case): is_zero returns true exactly when the input is 0.
    #[test]
    fn zero_returns_true() {
        assert!(is_zero(0));
    }

    // Postcondition (non-zero case): is_zero returns false for every non-zero u8.
    proptest! {
        #[test]
        fn nonzero_returns_false(x in 1u8..=255u8) {
            prop_assert!(!is_zero(x));
        }
    }
}
