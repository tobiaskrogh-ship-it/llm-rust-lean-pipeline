pub fn clamp(x: u8, lo: u8, hi: u8) -> u8 {
    if x < lo { lo } else if x > hi { hi } else { x }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    prop_compose! {
        /// Yields (x, lo, hi) with lo ≤ hi and x < lo (lower-clamp zone).
        /// Generated with zero rejects: lo is drawn first, hi ≥ lo second,
        /// and x < lo third.
        fn below_bound()
            (lo in 1u8..=255u8)
            (hi in lo..=255u8, x in 0u8..lo)
            -> (u8, u8, u8)
        {
            (x, lo, hi)
        }
    }

    prop_compose! {
        /// Yields (x, lo, hi) with lo ≤ hi and x > hi (upper-clamp zone).
        /// Generated with zero rejects: hi is drawn first (≤ 254 so x > hi
        /// is always reachable), lo ≤ hi second, and x > hi third.
        fn above_bound()
            (hi in 0u8..=254u8)
            (lo in 0u8..=hi, x in hi+1..=255u8)
            -> (u8, u8, u8)
        {
            (x, lo, hi)
        }
    }

    proptest! {
        // Postcondition: when x is below the lower bound, clamp pins to lo.
        #[test]
        fn returns_lo_when_below((x, lo, hi) in below_bound()) {
            prop_assert_eq!(clamp(x, lo, hi), lo);
        }

        // Postcondition: when x is above the upper bound, clamp pins to hi.
        #[test]
        fn returns_hi_when_above((x, lo, hi) in above_bound()) {
            prop_assert_eq!(clamp(x, lo, hi), hi);
        }

        // Postcondition: when x is already in [lo, hi], clamp returns x unchanged.
        // Three independent u8 values are sorted to guarantee lo ≤ x ≤ hi
        // with zero rejects.
        #[test]
        fn returns_x_when_in_range(a in 0u8..=255u8, b in 0u8..=255u8, c in 0u8..=255u8) {
            let mut arr = [a, b, c];
            arr.sort();
            let (lo, x, hi) = (arr[0], arr[1], arr[2]);
            prop_assert_eq!(clamp(x, lo, hi), x);
        }
    }
}
