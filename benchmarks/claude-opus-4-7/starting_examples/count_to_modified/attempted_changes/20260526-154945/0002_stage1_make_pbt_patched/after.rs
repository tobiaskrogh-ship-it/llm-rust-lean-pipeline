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

    /// Property: `count_to(n) == n` extends to larger inputs beyond the
    /// dense `0..=100` sweep. Uses a deterministic, irregular sample
    /// (including powers of two and off-by-one neighbours) that stays
    /// within stack-safe recursion depth.
    #[test]
    fn count_to_is_identity_on_wider_sample() {
        let samples: [u64; 12] = [
            101, 127, 128, 129, 255, 256, 500, 1023, 1024, 2500, 5000, 10_000,
        ];
        for &n in &samples {
            assert_eq!(count_to(n), n);
        }
    }
}