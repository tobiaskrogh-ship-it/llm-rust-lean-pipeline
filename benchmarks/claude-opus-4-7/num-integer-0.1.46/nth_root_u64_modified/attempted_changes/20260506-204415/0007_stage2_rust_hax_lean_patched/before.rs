//! Concrete monomorphization of `num_integer::nth_root` (from `num-integer-0.1.46`)
//! specialized to `u64`.
//!
//! Source: `src/roots.rs`, the `unsigned_roots!(u64)` macro expansion of
//! `Roots::nth_root` (along with its helpers `sqrt`, `cbrt`, the private
//! `fixpoint`/`bits`/`log2` helpers, and the `u32` cube-root used as a
//! sub-call inside the `u64` `cbrt`).
//!
//! Hax-compatible rewrite of the original. The mathematical contract is
//! preserved: `sqrt_u64`, `cbrt_u64`, and `nth_root` return the truncated
//! principal root, exactly as the source crate.
//!
//! Changes from the verbatim port that were forced by Hax / `lake build`:
//!
//!   - The generic helper `fixpoint<F: Fn(u64) -> u64>` is removed; its
//!     iteration is inlined into each caller (Hax does not currently
//!     support generic `Fn`-bounded parameters — `HAX0001 / Unsupported
//!     equality constraints on associated types of parent trait`).
//!   - All closures (`|x| ...`) are removed for the same reason.
//!   - Floating-point initial guesses (`(x as f64).sqrt() as u64`,
//!     `.cbrt()`, `((x as f64).ln() / f64::from(n)).exp() as u64`) are
//!     replaced with the integer power-of-two bound
//!     `1u64 << (log2(a) / n + 1)`. Unlike the source's
//!     `1u64 << ((log2(a) + n - 1) / n)` (which is sometimes below the
//!     root), this formula is _strictly greater_ than `a^(1/n)` for every
//!     valid input, because
//!     `2 ^ (log2(a)/n + 1) = 2 * 2^(log2(a)/n) >= 2 * 2^((log2(a)-(n-1))/n)
//!      = 2 * 2^((log2(a)+1)/n - 1) >= 2^((log2(a)+1)/n) > a^(1/n)`,
//!     where the last step uses `a < 2^(log2(a)+1)`. Starting from above
//!     the root means the original `fixpoint`'s ascending phase is
//!     vacuous and is omitted; only the descending Newton loop remains
//!     (one downward sweep of `x := next(x)` until `x <= next(x)`).
//!   - `for s in (0..smax + 1).rev()` in `cbrt_u32` is rewritten as a
//!     manual `while`-loop with an explicit decrementing index. The
//!     `Iterator::rev` / `Iterator::fold` chain that the source desugars
//!     to is not modeled in the Lean prelude.
//!   - `x.leading_zeros()` (in `log2_u64`) is replaced with a hand-rolled
//!     bit-count loop.
//!   - `x.checked_pow(n)` (in the `next` step of `nth_root`) is replaced
//!     with a recursive helper `checked_pow_u64`.
//!   - `(a > 0) as u64` is rewritten as explicit `if a == 0 { return 0; }
//!     ; return 1;` because the Lean prelude has no `Cast Bool u64`
//!     instance.
//!   - The `panic!("can't find a root of degree 0!")` for `n == 0` is
//!     replaced with a division-by-zero (`1u64 / (n as u64)`). The
//!     extraction's `core_models.fmt.rt.Impl_1.new_const` /
//!     `RustArray.ofVec` chain for the string-format panic produces a
//!     `Vector String 1 / Vector ? (USize64.toNat ?)` mismatch in the
//!     current Lean prelude. Division-by-zero is the same observable
//!     behavior (an immediate Rust panic) and extracts cleanly.
//!   - All `while` loops carry `hax_lib::loop_decreases!(x)` (where `x`
//!     is the loop variable, which strictly decreases on every iteration)
//!     so the extracted Lean has a usable termination measure rather
//!     than the default constant `0`.
//!   - The inner `fn go(...)` of `nth_root` is flattened into the body
//!     and the small-`n` `match` is unrolled to a chain of `if`s.
//!
//! All changes are local; the algorithm and contract of each function
//! are unchanged.

/// log2 for nonzero `u64`.
///
/// Rewritten from `63 - x.leading_zeros()` to a hand-rolled bit-count
/// loop so that no library call is left on the proof side.
fn log2_u64(mut x: u64) -> u32 {
    debug_assert!(x > 0);
    let mut r: u32 = 0;
    while x > 1 {
        hax_lib::loop_decreases!(x);
        x >>= 1;
        r += 1;
    }
    r
}

/// Hand-rolled checked power: returns `None` iff `x.pow(n)` would
/// overflow `u64`.
///
/// Replacement for `u64::checked_pow` (the source called
/// `num_traits::checked_pow(x, n as usize)` and we previously used the
/// std intrinsic `u64::checked_pow`). The intrinsic is not modeled by
/// the Lean prelude, so we reimplement it here recursively. `n`
/// strictly decreases, which is enough for Hax's termination check.
fn checked_pow_u64(x: u64, n: u32) -> Option<u64> {
    if n == 0 {
        Some(1)
    } else {
        match checked_pow_u64(x, n - 1) {
            None => None,
            Some(prev) => {
                if x == 0 {
                    // 0 * prev cannot overflow; result is 0 for n >= 1.
                    Some(0)
                } else if prev > u64::MAX / x {
                    None
                } else {
                    Some(prev * x)
                }
            }
        }
    }
}

/// Cube root for `u32`, used as a sub-call inside `cbrt_u64` for inputs
/// that fit in `u32`. Implementation is the Hacker's Delight `icbrt2`
/// variant from the `unsigned_roots!` macro's `cbrt` branch when
/// `bits::<T>() <= 32`.
///
/// The original used `for s in (0..smax + 1).rev()`. That desugars to
/// `Iterator::rev`/`Iterator::fold`, which the Lean prelude does not
/// model. Rewritten as a manual `while` with an explicit decrementing
/// index `s_idx`, exhausting the same range `s_idx ∈ {smax, smax-1,
/// ..., 1, 0}`.
fn cbrt_u32(a: u32) -> u32 {
    let mut x = a;
    let mut y2: u32 = 0;
    let mut y: u32 = 0;
    let smax: u32 = 32 / 3;
    let mut s_idx: u32 = smax + 1;
    while s_idx > 0 {
        hax_lib::loop_decreases!(s_idx);
        s_idx -= 1;
        let s = s_idx * 3;
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

/// Truncated principal square root of `a: u64`.
///
/// Direct port of the `unsigned_roots!(u64)` `sqrt` body. The 128-bit
/// branch is dead for `u64` and has been removed. The `fixpoint` helper
/// is inlined; the `(x as f64).sqrt() as u64` initial guess is replaced
/// with `1u64 << (log2(a) / 2 + 1)`, a power-of-2 _strictly greater_
/// than `sqrt(a)` for every `a >= 4`. Because the guess is above the
/// root, the original `fixpoint`'s ascending phase is vacuous and is
/// omitted: only the descending Newton sweep remains.
pub fn sqrt_u64(a: u64) -> u64 {
    if a == 0 {
        return 0;
    }
    if a < 4 {
        return 1;
    }
    let mut x: u64 = 1u64 << (log2_u64(a) / 2 + 1);
    let mut xn: u64 = (a / x + x) >> 1;
    while x > xn {
        // `x` strictly decreases each iteration (the loop condition gives
        // `x > xn` and the body sets `x := xn`).
        hax_lib::loop_decreases!(x);
        x = xn;
        xn = (a / x + x) >> 1;
    }
    x
}

/// Truncated principal cube root of `a: u64`.
///
/// Direct port of the `unsigned_roots!(u64)` `cbrt` body. The
/// `bits::<T>() <= 32` branch delegates to `cbrt_u32`. The `fixpoint`
/// helper is inlined; the `(x as f64).cbrt() as u64` initial guess is
/// replaced with `1u64 << (log2(a) / 3 + 1)` (strictly greater than
/// `cbrt(a)`), so only the descending Newton sweep remains.
pub fn cbrt_u64(a: u64) -> u64 {
    if a == 0 {
        return 0;
    }
    if a < 8 {
        return 1;
    }
    if a <= u32::MAX as u64 {
        return cbrt_u32(a as u32) as u64;
    }
    let mut x: u64 = 1u64 << (log2_u64(a) / 3 + 1);
    let mut xn: u64 = (a / (x * x) + x * 2) / 3;
    while x > xn {
        hax_lib::loop_decreases!(x);
        x = xn;
        xn = (a / (x * x) + x * 2) / 3;
    }
    x
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
    let a = self_val;

    // n == 0: the source panics with `panic!("can't find a root of
    // degree 0!")`. We trigger the panic via integer division by zero
    // instead — the string-format `panic!` extracts to a Vector
    // signature the Lean prelude does not currently model. Same
    // observable behavior (immediate Rust panic on this input) and a
    // clean extraction.
    if n == 0 {
        return 1u64 / (n as u64);
    }
    if n == 1 {
        return a;
    }
    if n == 2 {
        return sqrt_u64(a);
    }
    if n == 3 {
        return cbrt_u64(a);
    }

    // The root of values less than 2ⁿ can only be 0 or 1.
    // (`bits::<u64>() == 64`)
    //
    // The `64 <= n` half of the `||` short-circuits before `1u64 << n`
    // is evaluated, so the shift is well-defined whenever it is
    // reached (`n < 64`).
    if 64 <= n || a < (1u64 << n) {
        if a == 0 {
            return 0;
        }
        return 1;
    }

    // The 128-bit branch (`bits::<T>() > 64`) from the source is dead
    // for `u64` and is omitted.

    // Integer power-of-2 guess. Strictly greater than `a^(1/n)` for
    // every `n >= 4` and every `a >= 2^n`, so the original
    // `fixpoint`'s ascending phase is unnecessary; only the descending
    // Newton loop remains. The shift exponent is at most
    // `63 / 4 + 1 = 16`, well within `u64`.
    let n1 = n - 1;
    let mut x: u64 = 1u64 << (log2_u64(a) / n + 1);

    // First step of the iteration (so the loop condition `x > xn` is
    // well-formed).
    let y_init: u64 = match checked_pow_u64(x, n1) {
        Some(ax) => a / ax,
        None => 0,
    };
    let mut xn: u64 = (y_init + x * (n1 as u64)) / (n as u64);

    // Inlined `fixpoint`: descending phase only (the guess is above
    // the root).
    while x > xn {
        hax_lib::loop_decreases!(x);
        x = xn;
        let y = match checked_pow_u64(x, n1) {
            Some(ax) => a / ax,
            None => 0,
        };
        xn = (y + x * (n1 as u64)) / (n as u64);
    }
    x
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

    // ----------------------------------------------------------------------
    // Property-based tests of the function contracts.
    //
    // Each public function here is documented as returning the truncated
    // principal n-th root of its input. That contract has two independent
    // semantic clauses, both of which a buggy implementation could violate
    // independently:
    //
    //   (LB) result^n <= a            -- result IS a root of a (lower bound)
    //   (UB) (result + 1)^n > a       -- result is the largest such root
    //                                    (vacuous if (result+1)^n overflows)
    //
    // For `nth_root` the precondition `n >= 1` is also part of the contract
    // (the function panics on n == 0); already covered by `zeroth_root` above.
    //
    // (LB) and (UB) are tested as separate properties because they are
    // independent claims: an implementation returning 0 everywhere would
    // satisfy (LB) but fail (UB); one returning u64::MAX would satisfy (UB)
    // vacuously but fail (LB). `sqrt_u64`, `cbrt_u64`, and `nth_root` are
    // tested independently because each is a separate public function with
    // its own contract; the equivalences `sqrt_u64(a) == nth_root(a, 2)` and
    // `cbrt_u64(a) == nth_root(a, 3)` are implementation details, not part
    // of the spec of `sqrt_u64` / `cbrt_u64`.
    use proptest::prelude::*;

    proptest! {
        // ----- nth_root ---------------------------------------------------

        /// (LB) for `nth_root`: result^n <= a, for any valid n >= 1.
        #[test]
        fn prop_nth_root_lower_bound(a: u64, n in 1u32..=128) {
            let r = nth_root(a, n);
            match r.checked_pow(n) {
                Some(rn) => prop_assert!(
                    rn <= a,
                    "nth_root({}, {}) = {}; r^n = {} > a",
                    a, n, r, rn
                ),
                None => prop_assert!(
                    false,
                    "nth_root({}, {}) = {}; r^n overflows u64",
                    a, n, r
                ),
            }
        }

        /// (UB) for `nth_root`: (result + 1)^n > a, when (result + 1)^n is
        /// representable in u64. Vacuous otherwise (no larger root fits).
        #[test]
        fn prop_nth_root_upper_bound(a: u64, n in 1u32..=128) {
            let r = nth_root(a, n);
            if let Some(r1) = r.checked_add(1) {
                if let Some(r1n) = r1.checked_pow(n) {
                    prop_assert!(
                        r1n > a,
                        "nth_root({}, {}) = {}; (r+1)^n = {} <= a",
                        a, n, r, r1n
                    );
                }
            }
        }

        // ----- sqrt_u64 ---------------------------------------------------

        /// (LB) for `sqrt_u64`: result^2 <= a.
        #[test]
        fn prop_sqrt_lower_bound(a: u64) {
            let r = sqrt_u64(a);
            match r.checked_pow(2) {
                Some(r2) => prop_assert!(
                    r2 <= a,
                    "sqrt_u64({}) = {}; r^2 = {} > a", a, r, r2
                ),
                None => prop_assert!(
                    false,
                    "sqrt_u64({}) = {}; r^2 overflows u64", a, r
                ),
            }
        }

        /// (UB) for `sqrt_u64`: (result + 1)^2 > a, when representable.
        #[test]
        fn prop_sqrt_upper_bound(a: u64) {
            let r = sqrt_u64(a);
            if let Some(r1) = r.checked_add(1) {
                if let Some(r1_2) = r1.checked_pow(2) {
                    prop_assert!(
                        r1_2 > a,
                        "sqrt_u64({}) = {}; (r+1)^2 = {} <= a", a, r, r1_2
                    );
                }
            }
        }

        // ----- cbrt_u64 ---------------------------------------------------

        /// (LB) for `cbrt_u64`: result^3 <= a.
        #[test]
        fn prop_cbrt_lower_bound(a: u64) {
            let r = cbrt_u64(a);
            match r.checked_pow(3) {
                Some(r3) => prop_assert!(
                    r3 <= a,
                    "cbrt_u64({}) = {}; r^3 = {} > a", a, r, r3
                ),
                None => prop_assert!(
                    false,
                    "cbrt_u64({}) = {}; r^3 overflows u64", a, r
                ),
            }
        }

        /// (UB) for `cbrt_u64`: (result + 1)^3 > a, when representable.
        #[test]
        fn prop_cbrt_upper_bound(a: u64) {
            let r = cbrt_u64(a);
            if let Some(r1) = r.checked_add(1) {
                if let Some(r1_3) = r1.checked_pow(3) {
                    prop_assert!(
                        r1_3 > a,
                        "cbrt_u64({}) = {}; (r+1)^3 = {} <= a", a, r, r1_3
                    );
                }
            }
        }
    }
}
