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

    /// Boundary cases: empty input and constant polynomial both yield empty result.
    #[test]
    fn empty_and_constant() {
        assert_eq!(derivative(&[]), Vec::<i64>::new());
        assert_eq!(derivative(&[7]), Vec::<i64>::new());
    }

    proptest! {
        /// Length contract: result length is `max(0, input.len() - 1)`.
        /// Independent of value correctness — a buggy impl could produce
        /// correct coefficients but wrong length (e.g. by appending an extra 0).
        #[test]
        fn length_drops_by_one(c in proptest::collection::vec(-100i64..=100, 0..12)) {
            let expected_len = if c.is_empty() { 0 } else { c.len() - 1 };
            prop_assert_eq!(derivative(&c).len(), expected_len);
        }

        /// Value postcondition: `result[k] == (k+1) * c[k+1]` for every valid `k`.
        /// This is the full mathematical contract on the returned coefficients.
        #[test]
        fn coefficient_formula(c in proptest::collection::vec(-100i64..=100, 1..12)) {
            let d = derivative(&c);
            for k in 0..d.len() {
                prop_assert_eq!(d[k], ((k + 1) as i64) * c[k + 1]);
            }
        }
    }
}
