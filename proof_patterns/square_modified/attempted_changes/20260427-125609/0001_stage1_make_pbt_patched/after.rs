fn square(x: u8) -> u8 {
    x * x
}

#[cfg(test)]
mod tests {
    use super::square;
    use proptest::prelude::*;

    proptest! {
        /// Postcondition: for every input in the non-overflow range (0..=15) the
        /// result equals x * x exactly.
        #[test]
        fn square_correct_in_safe_range(x in 0u8..=15) {
            prop_assert_eq!(square(x), x * x);
        }

        /// Failure condition: inputs ≥ 16 cause a u8 overflow in debug mode and
        /// must panic.
        #[test]
        fn square_panics_on_overflow(x in 16u8..=u8::MAX) {
            let result = std::panic::catch_unwind(|| square(x));
            prop_assert!(result.is_err());
        }
    }
}