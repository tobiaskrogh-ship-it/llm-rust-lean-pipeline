pub fn add_one(x: u8) -> u8 {
    x + 1
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        /// Postcondition: for every valid input (x in 0..=254), add_one returns exactly x + 1.
        #[test]
        fn test_add_one_result_is_successor(x in 0u8..255u8) {
            prop_assert_eq!(add_one(x), x + 1);
        }
    }

    /// Failure condition: add_one(255) panics due to u8 overflow (debug-mode arithmetic).
    #[test]
    #[should_panic]
    fn test_add_one_panics_on_max() {
        add_one(u8::MAX);
    }
}
