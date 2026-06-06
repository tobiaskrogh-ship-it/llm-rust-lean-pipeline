//! Concrete `u64` extraction of `num_integer::cbrt` (v0.1.46).
//!
//! Source: `to_be_extracted/num-integer-0.1.46/src/roots.rs:121` (`pub fn cbrt`)
//! delegating to `<u64 as Roots>::cbrt` defined by the `unsigned_roots!` macro
//! at `src/roots.rs:316` (instantiated as `unsigned_roots!(u64)` on line 385).
//!
//! Monomorphizations / inlining performed:
//!   * `Roots::cbrt` impl for `u64` (via the `unsigned_roots!` macro) inlined
//!     directly as the function body.
//!   * Branches whose conditions can be evaluated at extract-time for `T = u64`
//!     have been eliminated:
//!       - `bits::<u64>() > 64` is always false → first branch dropped.
//!       - `bits::<u64>() <= 32` is always false → Hacker's-Delight `icbrt2`
//!         path is dropped from the top-level (it remains as the kernel for
//!         the `u32` fast path, where it actually applies).
//!   * The `(a as u32).cbrt() as u64` recursive call is replaced by an
//!     inlined private `cbrt_u32` helper that runs the very same
//!     Hacker's-Delight `icbrt2` algorithm the source uses for `u32`
//!     (`src/roots.rs:333..351`).
//!   * The closure `next: |x| ...` passed to `fixpoint` has been
//!     defunctionalized: `fixpoint_cbrt(a, x0)` inlines the recurrence
//!     `(a / (x*x) + x*2) / 3` directly.
//!   * The `#[cfg(feature = "std")]` `f64`-based guess is used (we are
//!     running with std), matching the default published behaviour.
//!
//! Behavioural equivalence is checked by:
//!   * A transferred-from-source postcondition test that mirrors the source's
//!     `tests/roots.rs` `check` routine specialized to `n = 3` over the
//!     same `pos::<u64>()` input vector the source builds.
//!   * A doc-test analogue from `Roots::cbrt` (`src/roots.rs:96..103`),
//!     limited to non-negative inputs (since `u64` cannot represent the
//!     negative cases).
//!   * A direct cross-check: `assert_eq!(cbrt(x), num_integer::cbrt(x))` over
//!     a sweep of inputs that includes small values, the u32 boundary, the
//!     f64 mantissa edge, and the upper boundary.

#![allow(clippy::needless_return)]

/// Hacker's-Delight `icbrt2`, monomorphized to `u32`.
///
/// Mirrors the body of the `Roots::cbrt` impl for `u32` produced by
/// `unsigned_roots!(u32)` in `src/roots.rs:333..351`.
fn cbrt_u32(a: u32) -> u32 {
    let mut x = a;
    let mut y2: u32 = 0;
    let mut y: u32 = 0;
    let smax: u32 = 32 / 3; // bits::<u32>() / 3 = 10
    let mut s_iter = smax + 1;
    while s_iter > 0 {
        s_iter -= 1;
        let s = s_iter * 3;
        y2 *= 4;
        y *= 2;
        let b = 3 * (y2 + y) + 1;
        if (x >> s) >= b {
            x -= b << s;
            y2 += 2 * y + 1;
            y += 1;
        }
    }
    y
}

/// Defunctionalized `fixpoint(guess, |x| (a/(x*x) + x*2) / 3)` from
/// `src/roots.rs:373..374` (the `next` closure for cube roots).
fn fixpoint_cbrt(a: u64, mut x: u64) -> u64 {
    let mut xn = (a / (x * x) + x * 2) / 3;
    while x < xn {
        x = xn;
        xn = (a / (x * x) + x * 2) / 3;
    }
    while x > xn {
        x = xn;
        xn = (a / (x * x) + x * 2) / 3;
    }
    x
}

/// Concrete `u64` cube root --- truncated principal `∛x`.
///
/// `cbrt(x)` returns the largest `r: u64` with `r*r*r <= x`.
pub fn cbrt(x: u64) -> u64 {
    let a = x;

    // Source has `if a < 8 { return (a > 0) as $T; }` --- inlined.
    if a < 8 {
        return if a > 0 { 1 } else { 0 };
    }

    // Source has `if a <= core::u32::MAX as $T { return (a as u32).cbrt() as $T; }`.
    // We inline the `<u32 as Roots>::cbrt` body via `cbrt_u32`.
    if a <= u32::MAX as u64 {
        return cbrt_u32(a as u32) as u64;
    }

    // f64-based guess + Newton fixpoint, as in the `#[cfg(feature = "std")]`
    // branch of the source.
    let guess = (a as f64).cbrt() as u64;
    fixpoint_cbrt(a, guess)
}

#[cfg(test)]
mod tests {
    use super::cbrt;

    /// Build the `pos::<u64>()` test vector exactly as the source's
    /// `tests/roots.rs:108..131` does for `T = u64`. Closed-form because the
    /// generic helpers (`extend`, `extend_shl`, `extend_shr`, `mantissa_max`)
    /// are all monomorphizable at extract-time.
    fn pos_u64() -> Vec<u64> {
        let mut v: Vec<u64> = Vec::new();

        // size_of::<u64>() == 8, so we take the `else` branch.
        // extend(&mut v, 0, i8::MAX as u64 = 127)
        let mut i: u64 = 0;
        while i < 127 {
            v.push(i);
            i += 1;
        }
        v.push(i);

        // extend(&mut v, u64::MAX - 127, u64::MAX)
        let mut i: u64 = u64::MAX - 127;
        while i < u64::MAX {
            v.push(i);
            i += 1;
        }
        v.push(i);

        // mantissa_max::<u64>(): bits = 64, MANTISSA_DIGITS = 53,
        // so rounding_bit = 1 << (64 - 53 - 1) = 1 << 10.
        let rounding_bit: u64 = 1u64 << (64 - 53 - 1);
        let mx = u64::MAX - rounding_bit;
        let mx1 = mx + 1;
        v.push(mx);
        v.push(mx1);

        // extend_shl(&mut v, u64::MAX, 0, !0u64)
        // For unsigned, mask = !T::min_value() = u64::MAX, a no-op mask.
        let mut i: u64 = u64::MAX;
        while i != 0 {
            v.push(i);
            i = i << 1; // bits past the top are dropped, matching the masked op.
        }

        // extend_shr(&mut v, u64::MAX, 0)
        let mut i: u64 = u64::MAX;
        while i != 0 {
            v.push(i);
            i >>= 1;
        }

        v
    }

    /// Specialized `check(v, 3)` from `tests/roots.rs:16..43`, with `n = 3`
    /// pinned in. The original assertions for the positive branch are:
    ///
    ///   assert!(rt.pow(n) <= *i);
    ///   if let Some(x) = checked_pow(rt+1, n as usize) { assert!(*i < x); }
    ///
    /// We rewrite to use `u64::checked_pow(3)` directly.
    fn check_cbrt(v: &[u64]) {
        for &i in v {
            let rt = cbrt(i);
            let rt_cubed = rt
                .checked_pow(3)
                .expect("rt^3 should fit in u64 since rt = cbrt(i) <= cbrt(u64::MAX)");
            assert!(rt_cubed <= i, "cbrt({i}) = {rt}, but {rt}^3 = {rt_cubed} > {i}");
            if let Some(rt1_cubed) = (rt + 1).checked_pow(3) {
                assert!(
                    i < rt1_cubed,
                    "cbrt({i}) = {rt}, but {i} >= ({rt}+1)^3 = {rt1_cubed}"
                );
            }
        }
    }

    /// Transferred from `tests/roots.rs:240..242` --- the `u64` flavour of
    /// `mod u64 { ... fn cbrt() { check(&pos::<u64>(), 3); } }`.
    #[test]
    fn cbrt_pos() {
        check_cbrt(&pos_u64());
    }

    /// Transferred from the `Roots::cbrt` doc-test
    /// (`src/roots.rs:96..103`), restricted to the non-negative cases since
    /// `u64` has no negatives.
    #[test]
    fn cbrt_doc_examples() {
        let x: u64 = 1234;
        assert_eq!(cbrt(x * x * x), x);
        assert_eq!(cbrt(x * x * x + 1), x);
        assert_eq!(cbrt(x * x * x - 1), x - 1);
    }

    /// Tiny exhaustive sweep of the small/perfect-cube boundary.
    #[test]
    fn cbrt_small_values() {
        assert_eq!(cbrt(0), 0);
        assert_eq!(cbrt(1), 1);
        assert_eq!(cbrt(2), 1);
        assert_eq!(cbrt(7), 1);
        assert_eq!(cbrt(8), 2);
        assert_eq!(cbrt(26), 2);
        assert_eq!(cbrt(27), 3);
        assert_eq!(cbrt(63), 3);
        assert_eq!(cbrt(64), 4);
    }

    /// Postcondition over a dense range straddling the u32 fast-path boundary.
    #[test]
    fn cbrt_postcondition_dense() {
        // 0..=200 covers the `< 8` branch and small u32 path.
        for x in 0u64..=200 {
            let r = cbrt(x);
            assert!(r * r * r <= x);
            assert!(x < (r + 1) * (r + 1) * (r + 1));
        }
        // Around the u32 boundary (boundary = u32::MAX = 4_294_967_295).
        for delta in 0u64..=200 {
            for x in [
                (u32::MAX as u64).saturating_sub(delta),
                (u32::MAX as u64).saturating_add(delta),
            ] {
                let r = cbrt(x);
                let r3 = r.checked_pow(3).unwrap();
                assert!(r3 <= x);
                let r1_3 = (r + 1).checked_pow(3);
                if let Some(b) = r1_3 {
                    assert!(x < b);
                }
            }
        }
    }

    /// Cross-check directly against the published `num_integer::cbrt`
    /// over a hand-picked sweep that exercises every code path:
    ///   * the `< 8` short-circuit,
    ///   * the `u32` fast path (Hacker's-Delight `icbrt2`),
    ///   * the f64-guess + Newton fixpoint path,
    ///   * the u32/u64 boundary,
    ///   * the f64-mantissa boundary,
    ///   * and `u64::MAX`.
    #[test]
    fn agrees_with_source() {
        use num_integer::Roots;

        let mut inputs: Vec<u64> = Vec::new();
        // small
        for x in 0u64..=300 {
            inputs.push(x);
        }
        // around perfect cubes
        for k in 0u64..=200 {
            let c = k * k * k;
            for off in [0i64, -1, 1, -2, 2] {
                let x = (c as i128 + off as i128).max(0) as u64;
                inputs.push(x);
            }
        }
        // around u32 boundary
        for delta in 0u64..=20 {
            inputs.push((u32::MAX as u64).saturating_sub(delta));
            inputs.push((u32::MAX as u64).saturating_add(delta));
        }
        // mantissa-edge
        let rounding_bit: u64 = 1u64 << (64 - 53 - 1);
        inputs.push(u64::MAX - rounding_bit);
        inputs.push(u64::MAX - rounding_bit + 1);
        // shl/shr sweep --- mirrors `pos`'s `extend_shl` / `extend_shr`.
        let mut i: u64 = u64::MAX;
        while i != 0 {
            inputs.push(i);
            i = i << 1;
        }
        let mut i: u64 = u64::MAX;
        while i != 0 {
            inputs.push(i);
            i >>= 1;
        }
        inputs.push(u64::MAX);
        inputs.push(0);

        for x in inputs {
            let ours = cbrt(x);
            let theirs = (&x).cbrt();
            assert_eq!(
                ours, theirs,
                "cbrt({x}) disagrees: extracted = {ours}, num-integer = {theirs}"
            );
        }
    }
}
