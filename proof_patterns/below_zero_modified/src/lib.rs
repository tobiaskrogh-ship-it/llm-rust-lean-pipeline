/// Given a list of deposit and withdrawal operations on an account that
/// starts at zero, return true iff the balance ever falls below zero.
//
// Rewritten as tail recursion (per `while_loop_to_recursion.rs` and
// `iter_chain_to_recursion.rs`) to avoid:
//   - the `for &op in operations` iterator chain, which extracts to
//     undefined `core.slice.iter.Iter.*` identifiers in the Hax Lean
//     prelude, and
//   - the early `return true;` inside the loop, which would otherwise
//     extract to the undefined `rust_primitives.hax.while_loop_return`
//     combinator.
// Single accumulator state (`balance`) threaded as a parameter; the
// decreasing measure is `operations.len() - i`.
fn below_zero_at(operations: &[i64], i: usize, balance: i64) -> bool {
    if i >= operations.len() {
        false
    } else {
        let new_balance = balance + operations[i];
        if new_balance < 0 {
            true
        } else {
            below_zero_at(operations, i + 1, new_balance)
        }
    }
}

pub fn below_zero(operations: &[i64]) -> bool {
    below_zero_at(operations, 0, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Direct specification of the postcondition:
    /// returns `true` iff some non-empty prefix of `operations` sums to a
    /// negative number. Uses `i128` so the spec itself cannot overflow on
    /// any input the function under test can legally accept.
    fn spec_below_zero(operations: &[i64]) -> bool {
        let mut prefix: i128 = 0;
        for &op in operations {
            prefix += op as i128;
            if prefix < 0 {
                return true;
            }
        }
        false
    }

    /// Boundary: an empty sequence has no prefix sum, so the balance never
    /// falls below zero.
    #[test]
    fn empty_input_returns_false() {
        assert!(!below_zero(&[]));
    }

    proptest! {
        /// Core contract (both directions of the iff):
        /// `below_zero(ops) == true` iff some prefix of `ops` sums to a
        /// negative number.
        ///
        /// Element magnitudes and length are bounded so the running `i64`
        /// balance inside `below_zero` cannot overflow (worst case
        /// |sum| <= 1024 * 1e12 < i64::MAX).
        #[test]
        fn matches_prefix_sum_spec(
            ops in prop::collection::vec(-1_000_000_000_000_i64..=1_000_000_000_000, 0..1024)
        ) {
            prop_assert_eq!(below_zero(&ops), spec_below_zero(&ops));
        }
    }
}
