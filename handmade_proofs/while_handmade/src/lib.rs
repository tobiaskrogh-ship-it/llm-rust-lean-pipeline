//! Counts from 0 up to `n` with a `while` loop: `count_to(n)` returns `n`.
//! Minimal `while`-loop example parallel to `recursion_handmade` — same
//! contract, iterative shape. Total for every `u64`.

pub fn count_to(n: u64) -> u64 {
    let mut i = 0;
    while i != n {
        i += 1;
    }
    i
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Postcondition: `count_to(n)` returns `n`.
    #[test]
    fn counts_to_n() {
        for n in 0u64..=100 {
            assert_eq!(count_to(n), n);
        }
    }

    /// Boundary: `count_to(0)` returns `0` — the loop never runs.
    #[test]
    fn count_to_zero_is_zero() {
        assert_eq!(count_to(0), 0);
    }
}
