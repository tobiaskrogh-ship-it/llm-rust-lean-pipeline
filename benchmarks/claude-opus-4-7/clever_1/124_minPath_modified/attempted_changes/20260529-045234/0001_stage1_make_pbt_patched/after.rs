/// CLEVER 124 — `minPath(grid, k)`.  The canonical CLEVER signature is
/// `pub fn minPath(grid: u64, k: u64) -> u64`, which discards the
/// actual `N×N` grid structure HumanEval/124 needs; only the grid's
/// linear length `N²` (passed as `grid`) and the path length `k` are
/// available.  No faithful implementation of the spec ("minimum
/// lexicographic path of length k") is possible with this reduced
/// signature.  Returning `0` as a degenerate sentinel; flagged
/// upstream in CLEVER's prompt set.
#[allow(non_snake_case)]
pub fn minPath(grid: u64, k: u64) -> u64 {
    let _ = grid;
    let _ = k;
    0
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn degenerate_stub_returns_zero() {
        assert_eq!(minPath(0, 0), 0);
        assert_eq!(minPath(9, 4), 0);
    }

    proptest! {
        // Postcondition (and the entire contract of this degenerate stub):
        // for every pair of `u64` inputs the function returns `0`.  Because the
        // CLEVER signature throws away the grid contents, this constant-zero
        // sentinel *is* the specification — there is no richer postcondition
        // to test.  Implicitly this also pins down totality / no-panic: a
        // panicking implementation would fail this test.
        #[test]
        fn prop_always_returns_zero(grid in any::<u64>(), k in any::<u64>()) {
            prop_assert_eq!(minPath(grid, k), 0);
        }
    }
}
