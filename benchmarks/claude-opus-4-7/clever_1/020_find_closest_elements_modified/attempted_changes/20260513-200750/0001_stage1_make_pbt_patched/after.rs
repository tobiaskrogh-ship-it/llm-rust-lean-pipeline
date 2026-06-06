/// From a supplied list of numbers (length ≥ 2), select the pair with the
/// smallest absolute difference and return them as `(smaller, larger)`.
fn abs_diff(a: i64, b: i64) -> i64 {
    if a > b { a - b } else { b - a }
}

fn scan_at(
    numbers: &[i64],
    i: usize,
    j: usize,
    best_i: usize,
    best_j: usize,
) -> (usize, usize) {
    let n = numbers.len();
    if i + 1 >= n {
        (best_i, best_j)
    } else if j >= n {
        scan_at(numbers, i + 1, i + 2, best_i, best_j)
    } else {
        let cur = abs_diff(numbers[i], numbers[j]);
        let best = abs_diff(numbers[best_i], numbers[best_j]);
        if cur < best {
            scan_at(numbers, i, j + 1, i, j)
        } else {
            scan_at(numbers, i, j + 1, best_i, best_j)
        }
    }
}

pub fn find_closest_elements(numbers: &[i64]) -> (i64, i64) {
    if numbers.len() < 2 {
        (0, 0)
    } else {
        let (i, j) = scan_at(numbers, 0, 1, 0, 1);
        if numbers[i] <= numbers[j] {
            (numbers[i], numbers[j])
        } else {
            (numbers[j], numbers[i])
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    // Bounded i64 range so |a - b| can't overflow. Length >= 2 satisfies the
    // documented precondition; we cover the len<2 case in a separate unit test.
    fn numbers_strategy() -> impl Strategy<Value = Vec<i64>> {
        prop::collection::vec(-1_000_000_000i64..=1_000_000_000, 2..20)
    }

    proptest! {
        // Postcondition 1: the result pair is ordered (smaller, larger).
        // A buggy impl that returned (larger, smaller) would be caught here.
        #[test]
        fn result_is_ordered(numbers in numbers_strategy()) {
            let (a, b) = find_closest_elements(&numbers);
            prop_assert!(a <= b);
        }

        // Postcondition 2: both result values are present in the input at
        // two distinct positions. A buggy impl that synthesised a pair with
        // the correct minimum difference (e.g. (0, 0) on an input containing
        // duplicates) would be caught here.
        #[test]
        fn result_elements_drawn_from_input(numbers in numbers_strategy()) {
            let (a, b) = find_closest_elements(&numbers);
            let mut found = false;
            for i in 0..numbers.len() {
                for j in 0..numbers.len() {
                    if i != j && numbers[i] == a && numbers[j] == b {
                        found = true;
                    }
                }
            }
            prop_assert!(found);
        }

        // Postcondition 3: the difference of the returned pair is the
        // minimum over all distinct index pairs. A buggy impl that returned
        // any valid pair from the input — but not the closest one — would
        // be caught here.
        #[test]
        fn result_difference_is_minimum(numbers in numbers_strategy()) {
            let (a, b) = find_closest_elements(&numbers);
            let result_diff = b - a;
            for i in 0..numbers.len() {
                for j in (i + 1)..numbers.len() {
                    let diff = (numbers[i] - numbers[j]).abs();
                    prop_assert!(result_diff <= diff);
                }
            }
        }
    }

    // Failure / defensive behaviour: when the documented precondition
    // (length >= 2) is violated, the function returns (0, 0).
    #[test]
    fn short_input_returns_zero_zero() {
        assert_eq!(find_closest_elements(&[]), (0, 0));
        assert_eq!(find_closest_elements(&[42]), (0, 0));
    }
}
