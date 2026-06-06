//! `max_odd_part` — reference example for an outer `while` loop whose body
//! calls a looping helper function.
//!
//! The public function `max_odd_part` runs a counter loop over `1..=n`; in
//! each iteration its body calls `trailing_zeros_u64`, which itself contains
//! a `while` loop. Verifying `max_odd_part` therefore requires *composing*
//! the helper's postcondition into the outer loop's body step — the proof
//! shape Stein's binary GCD needs (`m >>= trailing_zeros_u64(m)` inside the
//! main loop).
//!
//! The "odd part" of a positive integer `i` is `i` with all factors of two
//! removed, i.e. `i >> trailing_zeros_u64(i)`. `max_odd_part(n)` is the
//! largest odd part among `1..=n` (and `0` for `n == 0`).

/// Number of trailing zero bits of `x`; `trailing_zeros_u64(0) == 64`.
/// A single shift-and-count `while` loop (see the `trailing_zeros_u64`
/// reference crate). Private here — extracted as a dependency of
/// `max_odd_part`, exactly as in Stein's binary GCD.
fn trailing_zeros_u64(x: u64) -> u32 {
    if x == 0 {
        return 64;
    }
    let mut y = x;
    let mut count: u32 = 0;
    while y & 1 == 0 {
        y >>= 1;
        count = count + 1;
    }
    count
}

/// Largest odd part among the integers `1..=n` (`0` when `n == 0`).
///
/// Contract:
/// - `max_odd_part(n) <= n` for every `n`;
/// - `max_odd_part(n)` is odd whenever `n >= 1`.
pub fn max_odd_part(n: u64) -> u64 {
    let mut best: u64 = 0;
    let mut i: u64 = 1;
    while i <= n {
        let r = trailing_zeros_u64(i);
        let odd = i >> r;
        if odd > best {
            best = odd;
        }
        i = i + 1;
    }
    best
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Hand-computed values. Odd parts of `1..=10` are 1,1,3,1,5,3,7,1,9,5.
    #[test]
    fn known_values() {
        assert_eq!(max_odd_part(0), 0);
        assert_eq!(max_odd_part(1), 1);
        assert_eq!(max_odd_part(2), 1);
        assert_eq!(max_odd_part(3), 3);
        assert_eq!(max_odd_part(4), 3);
        assert_eq!(max_odd_part(10), 9);
    }

    /// Postcondition (bound): the result never exceeds `n`.
    #[test]
    fn result_at_most_n() {
        for n in 0u64..=300 {
            assert!(max_odd_part(n) <= n);
        }
    }

    /// Postcondition (oddness): for `n >= 1` the result is odd.
    #[test]
    fn result_is_odd_when_nonempty() {
        for n in 1u64..=300 {
            assert_eq!(max_odd_part(n) % 2, 1);
        }
    }
}
