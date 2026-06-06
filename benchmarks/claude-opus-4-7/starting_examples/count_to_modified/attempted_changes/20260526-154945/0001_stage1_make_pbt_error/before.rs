pub fn count_to(n: u64) -> u64 {
    if n == 0 {
        0
    } else {
        count_to(n - 1) + 1
    }
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

    /// Boundary: `count_to(0)` returns `0`.
    #[test]
    fn count_to_zero_is_zero() {
        assert_eq!(count_to(0), 0);
    }
}