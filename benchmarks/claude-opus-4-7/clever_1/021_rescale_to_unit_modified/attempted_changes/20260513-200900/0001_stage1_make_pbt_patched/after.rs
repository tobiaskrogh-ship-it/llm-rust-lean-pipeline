/// Apply a linear shift to a list so the smallest number becomes 0.
/// Integer version of the float "scale to [0,1]" contract — without floats
/// we cannot also force the largest to be 1, so the contract is restricted
/// to the shift (subtract min). Length must be ≥ 2.
fn min_at(numbers: &[i64], i: usize, m: i64) -> i64 {
    if i >= numbers.len() {
        m
    } else if numbers[i] < m {
        min_at(numbers, i + 1, numbers[i])
    } else {
        min_at(numbers, i + 1, m)
    }
}

fn shift_at(numbers: &[i64], delta: i64, i: usize, mut acc: Vec<i64>) -> Vec<i64> {
    if i >= numbers.len() {
        acc
    } else {
        acc.push(numbers[i] - delta);
        shift_at(numbers, delta, i + 1, acc)
    }
}

pub fn rescale_to_unit(numbers: &[i64]) -> Vec<i64> {
    if numbers.len() < 2 {
        Vec::new()
    } else {
        let m = min_at(numbers, 1, numbers[0]);
        shift_at(numbers, m, 0, Vec::new())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    // Use a bounded range so that arithmetic on i64 differences cannot overflow.
    // Differences live in [-2*BOUND, 2*BOUND] which is far from i64::MAX.
    const BOUND: i64 = 1_000_000_000;

    fn bounded_vec(min_len: usize, max_len: usize) -> impl Strategy<Value = Vec<i64>> {
        prop::collection::vec(-BOUND..=BOUND, min_len..=max_len)
    }

    proptest! {
        // Contract clause: precondition-violation behavior.
        // When len < 2 (i.e. 0 or 1), the function returns an empty Vec.
        #[test]
        fn short_input_returns_empty(v in bounded_vec(0, 1)) {
            prop_assert_eq!(rescale_to_unit(&v), Vec::<i64>::new());
        }

        // Contract clause: length postcondition.
        // When len >= 2, output length equals input length.
        #[test]
        fn preserves_length(v in bounded_vec(2, 32)) {
            prop_assert_eq!(rescale_to_unit(&v).len(), v.len());
        }

        // Contract clause: min-zero postcondition.
        // When len >= 2, the minimum of the output is 0.
        #[test]
        fn output_min_is_zero(v in bounded_vec(2, 32)) {
            let out = rescale_to_unit(&v);
            prop_assert_eq!(*out.iter().min().unwrap(), 0);
        }

        // Contract clause: uniform-shift postcondition.
        // When len >= 2, every element is decreased by the *same* delta, so
        // pairwise differences are preserved. This is independent of the
        // "min becomes 0" claim — a buggy impl could zero the min by clamping
        // (failing this) while still satisfying min == 0.
        #[test]
        fn is_uniform_shift(v in bounded_vec(2, 32)) {
            let out = rescale_to_unit(&v);
            for i in 0..v.len() {
                prop_assert_eq!(out[i] - out[0], v[i] - v[0]);
            }
        }
    }
}
