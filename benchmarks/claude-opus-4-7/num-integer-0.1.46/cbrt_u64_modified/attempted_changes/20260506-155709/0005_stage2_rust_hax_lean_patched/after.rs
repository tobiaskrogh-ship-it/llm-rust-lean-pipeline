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
//!   * The `#[cfg(feature = "std")]` `f64`-based guess is replaced with
//!     the `#[cfg(not(feature = "std"))]` integer-only guess
//!     `1 << ((bit_length(a) + 2) / 3)` because Hax does not support
//!     `f64` casts / `f64::cbrt`. Both branches feed the same
//!     `fixpoint_cbrt`, which converges to `floor(cbrt(a))` from any
//!     starting value `>= cbrt(a)` whose square fits in `u64`.
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
        hax_lib::loop_decreases!(s_iter);
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
///
/// Structural simplification vs. the source's `fixpoint`: the source
/// keeps two while loops (the first walking up while `xn > x`, the
/// second walking down while `xn < x`) because its `f64`-based initial
/// guess can land on either side of `cbrt(a)`. Our integer-only initial
/// guess `1u64 << ((bit_length(a) + 2) / 3)` always satisfies
/// `guess^3 >= 2^bit_length(a) > a`, so `next(guess) <= guess` and the
/// first iteration of the source's first loop is already at its
/// termination condition. Dropping the first loop therefore preserves
/// the value of `fixpoint_cbrt` for every input we pass it, and avoids
/// a Hax synthesis failure on the `u64::MAX - xn` termination measure
/// (checked subtraction `-?` is fallible, so `_pureTermination` cannot
/// be synthesized for that expression).
fn fixpoint_cbrt(a: u64, mut x: u64) -> u64 {
    let mut xn = (a / (x * x) + x * 2) / 3;
    while x > xn {
        hax_lib::loop_decreases!(x);
        x = xn;
        xn = (a / (x * x) + x * 2) / 3;
    }
    x
}

/// Number of bits required to represent `a` (so `bit_length_u64(0) = 0`,
/// `bit_length_u64(1) = 1`, `bit_length_u64(u64::MAX) = 64`).
///
/// Replaces `u64::leading_zeros` / `u64::ilog2`, which Hax does not
/// extract cleanly. Used to compute the integer-only initial guess for
/// the Newton fixpoint.
fn bit_length_u64(a: u64) -> u32 {
    let mut bits: u32 = 0;
    let mut tmp: u64 = a;
    while tmp > 0 {
        hax_lib::loop_decreases!(tmp);
        tmp >>= 1;
        bits += 1;
    }
    bits
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
    // `u32::MAX` is written out as the literal `4_294_967_295u64` because
    // `u32::MAX` does not extract through Hax (it becomes an undefined
    // `core_models.num.Impl_8.MAX` symbol in the Lean output).
    if a <= 4_294_967_295u64 {
        return cbrt_u32(a as u32) as u64;
    }

    // Integer-only initial guess for the Newton fixpoint, replacing the
    // `#[cfg(feature = "std")]` `(a as f64).cbrt() as u64` branch of the
    // source. Hax does not support `f64` casts or `f64::cbrt`, so we use
    // the `#[cfg(not(feature = "std"))]`-style guess from `num-integer`:
    // shift `1` left by `(bit_length(a) + 2) / 3`. For all `a > 0`, this
    // is `>= cbrt(a)`; for `a <= u64::MAX`, the shift amount is at most
    // `22`, so the guess is at most `1 << 22` and `guess * guess <= 1 << 44`,
    // which keeps the first iteration of `fixpoint_cbrt` well inside `u64`.
    let bits = bit_length_u64(a);
    let guess: u64 = 1u64 << ((bits + 2) / 3);
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

    // -----------------------------------------------------------------
    // Property-based contract tests.
    //
    // Contract of `cbrt`:
    //   * Precondition:  none --- accepts every `u64`.
    //   * Postcondition: writing `r = cbrt(x)`,
    //       (P1) `r^3 <= x`              --- "r is a cube-root candidate",
    //       (P2) `x < (r+1)^3` whenever `(r+1)^3` fits in `u64`
    //                                    --- "r is the *greatest* such".
    //     When `(r+1)^3` overflows `u64`, (P2) is vacuous since
    //     `x < 2^64 <= (r+1)^3`.
    //   * Failure:       the function is total --- it never panics and
    //                    has no error-return channel.
    //
    // (P1) and (P2) are independent contract clauses, so each gets its
    // own test:
    //   * a buggy implementation that always returned `0` would satisfy
    //     (P1) but break (P2) for every `x >= 1`;
    //   * a buggy implementation that returned the *ceiling* cube root
    //     would satisfy (P2) but break (P1) on every non-cube `x`.
    //
    // Totality is implicit in the (P1)/(P2) sweeps: a panic on any
    // input in `prop_inputs()` would fail those tests too. We do not
    // duplicate the input sweep just to assert it again.
    //
    // We deliberately do *not* test derived consequences:
    //   * `cbrt(k*k*k) = k` for `k <= cbrt(u64::MAX)` --- follows from
    //     (P1) ∧ (P2) at `x = k^3`.
    //   * Monotonicity `x <= y => cbrt(x) <= cbrt(y)` --- follows from
    //     `cbrt(x) = floor(x^(1/3))`; not an independent claim.
    //   * `cbrt((r+1)^3 - 1) = r` --- same content as the roundtrip.
    //   * `(cbrt(x))^2 <= x` for `x >= 1` --- algebraic consequence of
    //     (P1).
    // Each derived test would translate to a redundant proof obligation
    // downstream.
    // -----------------------------------------------------------------

    /// Deterministic input set for the property tests, chosen so that
    /// each branch of `cbrt` is exercised:
    ///   * `x < 8`               --- the short-circuit branch.
    ///   * `8 <= x <= u32::MAX`  --- the Hacker's-Delight `icbrt2` u32 path.
    ///   * `x > u32::MAX`        --- the `f64`-guess + Newton fixpoint path.
    /// Plus values known to stress cube-root implementations: the
    /// u32/u64 path-selector boundary, the f64-mantissa boundary near
    /// `u64::MAX` (where the initial `f64` guess is no longer ulp-tight
    /// and the fixpoint loop has to do real work), perfect cubes and
    /// their immediate neighbours, and bit-pattern sweeps via shifts
    /// (a stand-in for `proptest`-style bit generators, which are not
    /// available in this crate's dev-dependencies).
    fn prop_inputs() -> Vec<u64> {
        let mut v: Vec<u64> = Vec::new();

        // Small values: covers `< 8` and the start of the u32 path.
        for x in 0u64..=300 {
            v.push(x);
        }

        // Perfect cubes `k^3` and their immediate neighbours up to
        // `k = 65_536` (so `k^3 < 2^48`), straddling the u32 path
        // and the fixpoint path.
        for k in 0u64..=65_536 {
            let c = k.saturating_mul(k).saturating_mul(k);
            v.push(c.saturating_sub(1));
            v.push(c);
            v.push(c.saturating_add(1));
        }

        // u32/u64 path-selector boundary.
        for delta in 0u64..=64 {
            v.push((u32::MAX as u64).saturating_sub(delta));
            v.push((u32::MAX as u64).saturating_add(delta));
        }

        // f64-mantissa boundary near `u64::MAX`.
        let rounding_bit: u64 = 1u64 << (64 - 53 - 1);
        for delta in 0u64..=64 {
            v.push((u64::MAX - rounding_bit).saturating_sub(delta));
            v.push((u64::MAX - rounding_bit).saturating_add(delta));
        }
        v.push(u64::MAX);

        // Single-bit values, ones-suffix masks, and ones-prefix masks
        // --- a poor-man's bit-pattern sweep.
        for k in 0u32..64 {
            v.push(1u64 << k);
            v.push((1u64 << k).wrapping_sub(1));
            v.push(u64::MAX << k);
            v.push(u64::MAX >> k);
        }

        v
    }

    /// Property (P1): `cbrt(x)^3 <= x` for every `x: u64`.
    ///
    /// This is the "is a cube root" half of the postcondition. The
    /// computation `r * r * r` cannot overflow `u64` --- the largest
    /// possible result is `r = floor(cbrt(u64::MAX)) = 2_642_245`,
    /// whose cube fits in `u64` --- but we use `checked_pow(3)` to
    /// turn the no-overflow side condition into an explicit assertion.
    #[test]
    fn prop_cube_le_x() {
        for x in prop_inputs() {
            let r = cbrt(x);
            let r3 = r
                .checked_pow(3)
                .unwrap_or_else(|| panic!("cbrt({x}) = {r}, but {r}^3 overflows u64"));
            assert!(
                r3 <= x,
                "(P1) violated: cbrt({x}) = {r}, but {r}^3 = {r3} > {x}",
            );
        }
    }

    /// Property (P2): for every `x: u64`, either `(cbrt(x)+1)^3`
    /// overflows `u64` (vacuous --- then `x < 2^64 <= (r+1)^3`), or
    /// `x < (cbrt(x)+1)^3`.
    ///
    /// This is the "is the *greatest* cube root" half of the
    /// postcondition. Without it, `cbrt` could legally return any
    /// value `r` with `r^3 <= x` --- e.g. always `0` --- and still
    /// satisfy (P1).
    #[test]
    fn prop_x_lt_next_cube() {
        for x in prop_inputs() {
            let r = cbrt(x);
            // `r <= cbrt(u64::MAX) = 2_642_245`, so `r + 1` cannot
            // overflow; only the cubing step might.
            if let Some(b) = (r + 1).checked_pow(3) {
                assert!(
                    x < b,
                    "(P2) violated: cbrt({x}) = {r}, but {x} >= ({r}+1)^3 = {b}",
                );
            }
            // else: (r+1)^3 overflows u64, so the bound is vacuous.
        }
    }
}
