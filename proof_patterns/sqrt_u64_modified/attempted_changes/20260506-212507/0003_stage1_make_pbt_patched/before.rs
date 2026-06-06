//! Extracted from `num-integer` 0.1.46 — `pub fn sqrt<T: Roots>(x: T) -> T`
//! (defined in `src/roots.rs:114`, with the `u64` impl produced by the
//! `unsigned_roots!(u64)` macro at `src/roots.rs:275-313`), monomorphized to
//! `u64`.
//!
//! The original is generic over the `Roots` trait. For `u64`, the call
//! `x.sqrt()` expands to the body inside `unsigned_roots!(u64)`. We inline
//! that body, the private `fixpoint` / `log2` helpers, and use the no-std
//! integer-only initial-guess path (`1 << ((log2(x) + 1) / 2)`), which makes
//! the implementation purely integer (no `f64`) while remaining
//! mathematically equivalent — the Babylonian iteration converges to the same
//! truncated principal square root regardless of the starting guess.
//!
//! The closure passed to `fixpoint` and the `fixpoint` helper itself are
//! defunctionalized into explicit `while` loops at the call site.

/// Returns ⌊log₂(x)⌋ for a positive `u64`.
#[inline]
fn log2(x: u64) -> u32 {
    debug_assert!(x > 0);
    64 - 1 - x.leading_zeros()
}

/// Returns the truncated principal square root of `x` -- `⌊√x⌋`.
///
/// This is solving for `r` in `r² = x`, rounding toward zero.
/// The result satisfies `r² ≤ x < (r+1)²`.
///
/// # Examples
///
/// ```
/// use sqrt_u64::sqrt;
/// let x: u64 = 12345;
/// assert_eq!(sqrt(x * x), x);
/// assert_eq!(sqrt(x * x + 1), x);
/// assert_eq!(sqrt(x * x - 1), x - 1);
/// ```
pub fn sqrt(x: u64) -> u64 {
    let a = x;

    // Inlined from `unsigned_roots!(u64)` in src/roots.rs:275-313.
    // The `bits::<u64>() > 64` guard is statically false for u64, so we drop it.

    if a < 4 {
        return (a > 0) as u64;
    }

    // Initial guess (no-std variant from the source).
    let mut x: u64 = 1u64 << ((log2(a) + 1) / 2);

    // Babylonian iteration: next(x) = (a / x + x) / 2.
    // Inlined from `fixpoint` in src/roots.rs:170-186 with the closure
    // `|x| (a / x + x) >> 1` substituted directly.
    let mut xn: u64 = (a / x + x) >> 1;
    while x < xn {
        x = xn;
        xn = (a / x + x) >> 1;
    }
    while x > xn {
        x = xn;
        xn = (a / x + x) >> 1;
    }
    x
}

#[cfg(test)]
mod tests {
    use super::sqrt;

    // ---------------------------------------------------------------------
    // Test-vector generators, monomorphized from `tests/roots.rs` in the
    // source crate. The originals are generic over `T: TestInteger`; here
    // every `T` becomes `u64`.
    // ---------------------------------------------------------------------

    fn extend(v: &mut Vec<u64>, start: u64, end: u64) {
        let mut i = start;
        while i < end {
            v.push(i);
            i = i + 1;
        }
        v.push(i);
    }

    fn extend_shl(v: &mut Vec<u64>, start: u64, end: u64, mask: u64) {
        let mut i = start;
        while i != end {
            v.push(i);
            i = (i << 1) & mask;
        }
    }

    fn extend_shr(v: &mut Vec<u64>, start: u64, end: u64) {
        let mut i = start;
        while i != end {
            v.push(i);
            i = i >> 1;
        }
    }

    /// Get the maximum value that will round down as `f64` (if any),
    /// and its successor that will round up.
    ///
    /// Monomorphized from `tests/roots.rs::mantissa_max` for the unsigned
    /// `u64` case: `bits = 8 * size_of::<u64>() = 64`, `MANTISSA_DIGITS = 53`,
    /// so `rounding_bit = 1 << (64 - 53 - 1) = 1024`.
    fn mantissa_max() -> Option<(u64, u64)> {
        const MANTISSA_DIGITS: usize = 53;
        let bits: usize = 8 * core::mem::size_of::<u64>();
        if bits > MANTISSA_DIGITS {
            let rounding_bit: u64 = 1u64 << (bits - MANTISSA_DIGITS - 1);
            let x = u64::MAX - rounding_bit;
            let x1 = x + 1;
            Some((x, x1))
        } else {
            None
        }
    }

    /// Monomorphized from `tests/roots.rs::pos::<T>` with `T = u64`.
    fn pos() -> Vec<u64> {
        let mut v: Vec<u64> = vec![];
        // mem::size_of::<u64>() != 1, so we take the else-branch.
        extend(&mut v, 0u64, i8::MAX as u64);
        extend(&mut v, u64::MAX - i8::MAX as u64, u64::MAX);
        if let Some((i, j)) = mantissa_max() {
            v.push(i);
            v.push(j);
        }
        // For unsigned u64: `!T::min_value() = !0 = u64::MAX`, used as mask.
        extend_shl(&mut v, u64::MAX, 0u64, u64::MAX);
        extend_shr(&mut v, u64::MAX, 0u64);
        v
    }

    /// Monomorphized from `tests/roots.rs::check`, specialised to `n = 2`
    /// (square root) and the unsigned positive branch.
    ///
    /// The original calls `i.nth_root(n)` and (when `n == 2`) asserts
    /// equality with `i.sqrt()`. We only have `sqrt`, so we drop the
    /// `nth_root` cross-check and keep the property checks:
    /// `rt² ≤ i < (rt+1)²` (with the upper bound guarded by overflow).
    fn check(v: &[u64]) {
        for &i in v {
            let rt = sqrt(i);
            // rt^2 ≤ i. rt ≤ ⌊√(2^64−1)⌋ = 2^32−1, so rt*rt cannot overflow.
            let rt_sq = rt
                .checked_mul(rt)
                .expect("rt*rt should not overflow for sqrt(u64)");
            assert!(rt_sq <= i, "sqrt({}) = {} but {}^2 = {} > {}", i, rt, rt, rt_sq, i);
            // i < (rt+1)^2 if (rt+1)^2 doesn't overflow.
            let rt1 = rt + 1;
            if let Some(x) = rt1.checked_mul(rt1) {
                assert!(i < x, "sqrt({}) = {} but ({}+1)^2 = {} ≤ {}", i, rt, rt, x, i);
            }
        }
    }

    // ---------------------------------------------------------------------
    // Transferred tests
    // ---------------------------------------------------------------------

    /// From `tests/roots.rs` `test_roots!(i64, u64)` → `mod u64 { fn sqrt }`.
    #[test]
    fn sqrt_test() {
        check(&pos());
    }

    /// Doc-test from `Roots::sqrt` (src/roots.rs:71-78), monomorphized from
    /// `i32` to `u64`.
    #[test]
    fn sqrt_doctest() {
        let x: u64 = 12345;
        assert_eq!(sqrt(x * x), x);
        assert_eq!(sqrt(x * x + 1), x);
        assert_eq!(sqrt(x * x - 1), x - 1);
    }

    // A few small spot-checks corresponding to the boundary cases the source
    // implementation explicitly handles (`a < 4`).
    #[test]
    fn sqrt_small() {
        assert_eq!(sqrt(0), 0);
        assert_eq!(sqrt(1), 1);
        assert_eq!(sqrt(2), 1);
        assert_eq!(sqrt(3), 1);
        assert_eq!(sqrt(4), 2);
    }
}
