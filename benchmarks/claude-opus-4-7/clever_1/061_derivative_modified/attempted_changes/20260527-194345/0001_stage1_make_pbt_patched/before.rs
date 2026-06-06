/// HumanEval/62 — `derivative(xs)`.  Given coefficients
/// `xs = [a0, a1, a2, ..., a_{n-1}]` representing the polynomial
/// `a0 + a1*x + a2*x^2 + ... + a_{n-1}*x^{n-1}`, return the
/// coefficients of its derivative: `[a1, 2*a2, 3*a3, ..., (n-1)*a_{n-1}]`.
///
/// The empty input and a single-element (constant polynomial) input
/// both yield an empty derivative.
fn build_at(c: &[i64], i: usize, mut acc: Vec<i64>) -> Vec<i64> {
    if i >= c.len() {
        acc
    } else {
        acc.push((i as i64) * c[i]);
        build_at(c, i + 1, acc)
    }
}

pub fn derivative(c: &[i64]) -> Vec<i64> {
    // Index 0 contributes the constant term, which differentiates to 0;
    // we start collection at index 1 (which becomes index 0 of result).
    if c.is_empty() {
        Vec::new()
    } else {
        build_at(c, 1, Vec::new())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Brute-force oracle.
    fn naive_derivative(c: &[i64]) -> Vec<i64> {
        let mut out = Vec::new();
        for (i, &v) in c.iter().enumerate().skip(1) {
            out.push((i as i64) * v);
        }
        out
    }

    /// Boundary cases.
    #[test]
    fn empty_and_constant() {
        assert_eq!(derivative(&[]), Vec::<i64>::new());
        assert_eq!(derivative(&[7]), Vec::<i64>::new());
    }

    /// Known small cases.
    #[test]
    fn small_cases() {
        // 3 + 1*x + 2*x^2 + 4*x^3 + 5*x^4  →  1 + 4*x + 12*x^2 + 20*x^3
        assert_eq!(derivative(&[3, 1, 2, 4, 5]), vec![1, 4, 12, 20]);
        // 1 + 2*x + 3*x^2  →  2 + 6*x
        assert_eq!(derivative(&[1, 2, 3]), vec![2, 6]);
    }

    proptest! {
        /// Postcondition: matches the brute-force oracle.
        #[test]
        fn matches_brute_force(c in proptest::collection::vec(-100i64..=100, 0..12)) {
            prop_assert_eq!(derivative(&c), naive_derivative(&c));
        }

        /// Length contract: result length is `max(0, input.len() - 1)`.
        #[test]
        fn length_drops_by_one(c in proptest::collection::vec(-100i64..=100, 0..12)) {
            let expected_len = if c.is_empty() { 0 } else { c.len() - 1 };
            prop_assert_eq!(derivative(&c).len(), expected_len);
        }

        /// k-th coefficient of result is `(k+1) * c[k+1]`.
        #[test]
        fn coefficient_formula(c in proptest::collection::vec(-100i64..=100, 1..12)) {
            let d = derivative(&c);
            for k in 0..d.len() {
                prop_assert_eq!(d[k], ((k + 1) as i64) * c[k + 1]);
            }
        }
    }
}
