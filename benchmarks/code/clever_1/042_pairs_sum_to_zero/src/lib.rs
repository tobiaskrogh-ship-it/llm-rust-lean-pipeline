/// Return true iff two distinct positions in `numbers` hold values that
/// sum to zero.
///
/// Note: with the `u64` type pinned by CLEVER, the only pair summing to 0
/// is two zero entries. A richer formulation requires `&[i64]`.
fn count_zeros_at(numbers: &[u64], i: usize, acc: u64) -> u64 {
    if i >= numbers.len() {
        acc
    } else if numbers[i] == 0 {
        count_zeros_at(numbers, i + 1, acc + 1)
    } else {
        count_zeros_at(numbers, i + 1, acc)
    }
}

pub fn pairs_sum_to_zero(numbers: &[u64]) -> bool {
    count_zeros_at(numbers, 0, 0) >= 2
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    // --- Postcondition (full spec) ------------------------------------------
    //
    // For `u64`, `x + y == 0` iff `x == 0 && y == 0`. Hence "there exist
    // distinct positions i != j with numbers[i] + numbers[j] == 0" is
    // equivalent to "there are at least two zero entries in numbers".
    //
    // This single property pins the entire postcondition. We use a value
    // range that frequently emits zeros so the interesting branch is well
    // covered, and a slice length that includes the empty and singleton
    // boundary cases.
    proptest! {
        #[test]
        fn matches_zero_count_spec(
            numbers in proptest::collection::vec(0u64..=4, 0..16)
        ) {
            let zero_count = numbers.iter().filter(|&&x| x == 0).count();
            prop_assert_eq!(pairs_sum_to_zero(&numbers), zero_count >= 2);
        }
    }

    // --- Boundary / distinctness / witness unit tests -----------------------
    //
    // These deterministically pin edge cases that a random sampler may visit
    // only by chance, and each rules out a plausible buggy implementation.

    /// No precondition: the empty slice is accepted and yields `false`
    /// (no pair can exist when there are no positions at all).
    #[test]
    fn empty_slice_returns_false() {
        assert!(!pairs_sum_to_zero(&[]));
    }

    /// Distinctness clause: a single zero is not a witness to itself —
    /// the function must require two distinct positions.
    /// (Catches an implementation that returns true whenever any zero exists.)
    #[test]
    fn single_zero_returns_false() {
        assert!(!pairs_sum_to_zero(&[0]));
    }

    /// Existence clause: two zeros at distinct positions are a valid witness,
    /// regardless of where they sit among non-zero entries.
    /// (Catches an implementation that fails to find a witness when one exists.)
    #[test]
    fn two_zeros_witness_returns_true() {
        assert!(pairs_sum_to_zero(&[0, 0]));
        assert!(pairs_sum_to_zero(&[1, 0, 2, 0, 3]));
    }
}
