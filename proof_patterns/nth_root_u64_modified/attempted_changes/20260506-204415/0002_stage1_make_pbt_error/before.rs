//! Concrete monomorphization of `num_integer::nth_root` (from `num-integer-0.1.46`)
//! specialized to `u64`.
//!
//! Source: `src/roots.rs`, the `unsigned_roots!(u64)` macro expansion of
//! `Roots::nth_root` (along with its helpers `sqrt`, `cbrt`, the private
//! `fixpoint`/`bits`/`log2` helpers, and the `u32` cube-root used as a
//! sub-call inside the `u64` `cbrt`).
//!
//! Algorithm is preserved verbatim where possible. Generic trait calls are
//! replaced with concrete `u64` operations; `num_traits::checked_pow(x, n as
//! usize)` is replaced with the std intrinsic `u64::checked_pow(x, n)`.
//! The `bits::<T>() > 64` 128-bit branch in the source is dead for `u64`
//! and has been removed. The `std` flavor of `guess` is used (matches the
//! default features of the source crate).

/// log2 for nonzero `u64`.
#[inline]
fn log2_u64(x: u64) -> u32 {
    debug_assert!(x > 0);
    63 - x.leading_zeros()
}

/// Iterate `f` until two consecutive values are equal (or one cycle of
/// length two is detected via the second loop). Direct port of the
/// generic `fixpoint` helper, monomorphized to `u64`.
#[inline]
fn fixpoint<F>(mut x: u64, f: F) -> u64
where
    F: Fn(u64) -> u64,
{
    let mut xn = f(x);
    while x < xn {
        x = xn;
        xn = f(x);
    }
    while x > xn {
        x = xn;
        xn = f(x);
    }
    x
}

/// Cube root for `u32`, used as a sub-call inside `cbrt_u64` for inputs
/// that fit in `u32`. Implementation is the Hacker's Delight `icbrt2`
/// variant from the `unsigned_roots!` macro's `cbrt` branch when
/// `bits::<T>() <= 32`.
fn cbrt_u32(a: u32) -> u32 {
    let mut x = a;
    let mut y2: u32 = 0;
    let mut y: u32 = 0;
    let smax: u32 = 32 / 3;
    for s in (0..smax + 1).rev() {
        let s = s * 3;
        y2 *= 4;
        y *= 2;
        let b = 3 * (y2 + y) + 1;
        if x >> s >= b {
            x -= b << s;
            y2 += 2 * y + 1;
            y += 1;
        }
    }
    y
}

/// Truncated principal square root of `a: u64`. Direct port of the
/// `unsigned_roots!(u64)` `sqrt` body (the 128-bit branch is dead and
/// has been removed; the `std` flavor of `guess` is used).
pub fn sqrt_u64(a: u64) -> u64 {
    if a < 4 {
        return (a > 0) as u64;
    }
    // std flavor
    let guess = |x: u64| -> u64 { (x as f64).sqrt() as u64 };
    // Babylonian method
    let next = |x: u64| -> u64 { (a / x + x) >> 1 };
    fixpoint(guess(a), next)
}

/// Truncated principal cube root of `a: u64`. Direct port of the
/// `unsigned_roots!(u64)` `cbrt` body. The `bits::<T>() <= 32` branch
/// is delegated to `cbrt_u32` for the `a <= u32::MAX` case.
pub fn cbrt_u64(a: u64) -> u64 {
    if a < 8 {
        return (a > 0) as u64;
    }
    if a <= u32::MAX as u64 {
        return cbrt_u32(a as u32) as u64;
    }
    let guess = |x: u64| -> u64 { (x as f64).cbrt() as u64 };
    let next = |x: u64| -> u64 { (a / (x * x) + x * 2) / 3 };
    fixpoint(guess(a), next)
}

/// Returns the truncated principal `n`th root of `self_val: u64`.
///
/// Equivalent to `<u64 as num_integer::Roots>::nth_root(&self_val, n)` in
/// `num-integer-0.1.46`.
///
/// # Panics
///
/// Panics if `n == 0`.
pub fn nth_root(self_val: u64, n: u32) -> u64 {
    fn go(a: u64, n: u32) -> u64 {
        // Specialize small roots
        match n {
            0 => panic!("can't find a root of degree 0!"),
            1 => return a,
            2 => return sqrt_u64(a),
            3 => return cbrt_u64(a),
            _ => (),
        }

        // The root of values less than 2ⁿ can only be 0 or 1.
        // (`bits::<u64>() == 64`)
        if 64 <= n || a < (1u64 << n) {
            return (a > 0) as u64;
        }

        // The 128-bit branch (`bits::<T>() > 64`) from the source is
        // dead for `u64` and is omitted.

        // std-flavored `guess`. For `u64`, `bits::<T>() <= 32` is false,
        // so the dispatch is on `x <= u32::MAX as u64`.
        let guess = |x: u64, n: u32| -> u64 {
            if x <= u32::MAX as u64 {
                1u64 << ((log2_u64(x) + n - 1) / n)
            } else {
                ((x as f64).ln() / f64::from(n)).exp() as u64
            }
        };

        // https://en.wikipedia.org/wiki/Nth_root_algorithm
        let n1 = n - 1;
        let next = |x: u64| -> u64 {
            let y = match x.checked_pow(n1) {
                Some(ax) => a / ax,
                None => 0,
            };
            (y + x * n1 as u64) / n as u64
        };
        fixpoint(guess(a, n), next)
    }
    go(self_val, n)
}

#[cfg(test)]
mod tests {
    //! Tests transferred from `tests/roots.rs` of `num-integer-0.1.46`,
    //! monomorphized to `u64`. The original test file uses a
    //! `test_roots!($I, $U)` macro to generate a `mod $U { ... }` block
    //! per integer pair; we keep the unsigned half for the `u64`
    //! instantiation here.
    //!
    //! Note: the original `mod $U` `nth_root` test in fact uses `$I`
    //! (the signed mate) for both its `bits` count and its `pos::<$I>()`
    //! input — apparently a copy-paste bug. We adapt it to use the
    //! actually-extracted type (`u64`) so the test exercises *this*
    //! function. The bound is taken to be `4..63`, matching the
    //! original `8 * size_of::<i64>() - 1 == 63`.
    use super::*;

    /// `f64::MANTISSA_DIGITS` (53). Lifted as a local constant to keep
    /// the test self-contained.
    const MANTISSA_DIGITS: u32 = 53;

    /// Adapted from the generic `check<T>` in `tests/roots.rs`.
    /// Only the `*i >= T::zero()` (positive) branch survives for `u64`.
    fn check(v: &[u64], n: u32) {
        for i in v {
            let rt = nth_root(*i, n);
            if n == 2 {
                assert_eq!(rt, sqrt_u64(*i));
            } else if n == 3 {
                assert_eq!(rt, cbrt_u64(*i));
            }
            let rt1 = rt + 1;
            assert!(rt.pow(n) <= *i);
            if let Some(x) = rt1.checked_pow(n) {
                assert!(*i < x);
            }
        }
    }

    /// Adapted from generic `mantissa_max<T>` to `u64`.
    /// `T::min_value().is_zero()` is true for `u64`, so `bits = 64`.
    fn mantissa_max() -> Option<(u64, u64)> {
        let bits: u32 = 64;
        if bits > MANTISSA_DIGITS {
            let rounding_bit: u64 = 1u64 << (bits - MANTISSA_DIGITS - 1);
            let x = u64::MAX - rounding_bit;
            let x1 = x + 1;
            let x2 = x1 + 1;
            assert!((x as f64) < (x1 as f64));
            assert_eq!(x1 as f64, x2 as f64);
            Some((x, x1))
        } else {
            None
        }
    }

    fn extend(v: &mut Vec<u64>, start: u64, end: u64) {
        let mut i = start;
        while i < end {
            v.push(i);
            i += 1;
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
            i >>= 1;
        }
    }

    /// Adapted from generic `pos<T>()`. For `u64` the size is not 1, so
    /// we take the non-trivial branch. `i8::MAX as u64 = 127`, and
    /// `!T::min_value() == u64::MAX` for `u64`.
    fn pos() -> Vec<u64> {
        let mut v: Vec<u64> = vec![];
        extend(&mut v, 0, 127);
        extend(&mut v, u64::MAX - 127, u64::MAX);
        if let Some((i, j)) = mantissa_max() {
            v.push(i);
            v.push(j);
        }
        extend_shl(&mut v, u64::MAX, 0, u64::MAX);
        extend_shr(&mut v, u64::MAX, 0);
        v
    }

    #[test]
    #[should_panic]
    fn zeroth_root() {
        nth_root(123u64, 0);
    }

    #[test]
    fn sqrt() {
        check(&pos(), 2);
    }

    #[test]
    fn cbrt() {
        check(&pos(), 3);
    }

    #[test]
    fn nth_root_test() {
        // Original used `size_of::<i64>() - 1 == 63`; we use the same
        // upper bound so the test surface matches.
        let bits: u32 = 63;
        let pos = pos();
        for n in 4..bits {
            check(&pos, n);
        }
    }

    #[test]
    fn bit_size() {
        let bits: u32 = 64;
        assert_eq!(nth_root(u64::MAX, bits - 1), 2);
        assert_eq!(nth_root(u64::MAX, bits), 1);
    }
}
