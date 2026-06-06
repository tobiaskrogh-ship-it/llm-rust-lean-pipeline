/// For a given list of input numbers, calculate the mean absolute deviation
/// around the mean:  MAD = average | x - x_mean |.
///
/// Note: CLEVER's reference signature is `(numbers: List[float]) -> float`.
/// Translated to `i64` because the Hax Lean prelude has gaps in `f64`
/// support (missing `Impl.abs`, `PartialOrd`, `Neg`, broken `Sub.sub` for
/// non-integer types). Integer arithmetic loses fractional precision on the
/// mean and the deviation sum compared to the `f64` reference, but the
/// shape of the contract (average absolute distance from the mean) is the
/// same.
fn sum_from(numbers: &[i64], i: usize) -> i64 {
    if i >= numbers.len() {
        0
    } else {
        numbers[i] + sum_from(numbers, i + 1)
    }
}

fn abs_dev_sum_from(numbers: &[i64], mean: i64, i: usize) -> i64 {
    if i >= numbers.len() {
        0
    } else {
        let d = numbers[i] - mean;
        let abs_d = if d >= 0 { d } else { -d };
        abs_d + abs_dev_sum_from(numbers, mean, i + 1)
    }
}

pub fn mean_absolute_deviation(numbers: &[i64]) -> i64 {
    let n = numbers.len() as i64;
    if n == 0 {
        0
    } else {
        let mean = sum_from(numbers, 0) / n;
        abs_dev_sum_from(numbers, mean, 0) / n
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    // Iterative reference reimplementing the contract:
    //     MAD(xs) = (Σ |x_i - mean|) / n,   mean = (Σ x_i) / n,
    // with the same integer-truncating arithmetic as the implementation.
    fn reference_mad(numbers: &[i64]) -> i64 {
        let n = numbers.len() as i64;
        if n == 0 {
            return 0;
        }
        let sum: i64 = numbers.iter().sum();
        let mean = sum / n;
        let abs_dev_sum: i64 = numbers.iter().map(|x| (x - mean).abs()).sum();
        abs_dev_sum / n
    }

    // Postcondition for the empty-slice edge case: result is 0.
    #[test]
    fn empty_returns_zero() {
        assert_eq!(mean_absolute_deviation(&[]), 0);
    }

    // Full postcondition: for any input within the safe range
    // (no sum/deviation overflow), the result equals the defining formula.
    //
    // Value bound 10^9 with length ≤ 50 keeps |Σ x_i| ≤ 5·10^10 and the
    // |x_i - mean| sum ≤ 10^11, well inside i64 range.
    proptest! {
        #[test]
        fn matches_reference_formula(
            v in prop::collection::vec(-1_000_000_000i64..1_000_000_000, 0..50),
        ) {
            prop_assert_eq!(mean_absolute_deviation(&v), reference_mad(&v));
        }
    }

    // Independent semantic claim: MAD is an average of absolute values,
    // so the result is always non-negative. Stated separately because it
    // is a basic correctness property every implementation must satisfy,
    // not just this one.
    proptest! {
        #[test]
        fn result_is_non_negative(
            v in prop::collection::vec(-1_000_000_000i64..1_000_000_000, 0..50),
        ) {
            prop_assert!(mean_absolute_deviation(&v) >= 0);
        }
    }

    // Edge case: a single element has zero deviation from its own mean.
    proptest! {
        #[test]
        fn single_element_returns_zero(x in -1_000_000_000i64..1_000_000_000i64) {
            prop_assert_eq!(mean_absolute_deviation(&[x]), 0);
        }
    }

    // Edge case: when all elements are identical, deviation sum is zero,
    // so MAD is zero. This tests the "absolute deviation" part of the
    // contract independently.
    proptest! {
        #[test]
        fn constant_array_returns_zero(x in -1_000_000i64..1_000_000i64, count in 1usize..50) {
            let v = vec![x; count];
            prop_assert_eq!(mean_absolute_deviation(&v), 0);
        }
    }

    // Postcondition: MAD is the average of absolute deviations, so it must
    // be bounded by the maximum absolute deviation from the mean. This ensures
    // the result stays within a reasonable envelope.
    proptest! {
        #[test]
        fn result_bounded_by_max_deviation(
            v in prop::collection::vec(-1_000_000_000i64..1_000_000_000, 1..50),
        ) {
            let n = v.len() as i64;
            let sum: i64 = v.iter().sum();
            let mean = sum / n;
            let max_dev = v.iter().map(|x| (x - mean).abs()).max().unwrap_or(0);
            let mad = mean_absolute_deviation(&v);
            prop_assert!(mad <= max_dev, "MAD {} exceeds max deviation {}", mad, max_dev);
        }
    }
}
