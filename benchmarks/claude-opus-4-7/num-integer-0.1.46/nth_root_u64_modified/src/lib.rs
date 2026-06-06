//! Concrete monomorphization of `num_integer::nth_root` (from `num-integer-0.1.46`)
//! specialized to `u64`.
//!
//! Source: `src/roots.rs`, the `unsigned_roots!(u64)` macro expansion of
//! `Roots::nth_root` (along with its helpers `sqrt`, `cbrt`, the private
//! `fixpoint`/`bits`/`log2` helpers, and the `u32` cube-root used as a
//! sub-call inside the `u64` `cbrt`).
//!
//! Algorithm is preserved verbatim where possible. The original code uses
//! several constructs that have no Hax Lean prelude model and have been
//! rewritten:
//!
//!   * The generic `fixpoint<F: Fn(u64) -> u64>` helper fails Hax extraction
//!     with `HAX0001: Unsupported equality constraints on associated types
//!     of parent trait` (issue hacspec/hax#1923 — `Fn`'s parent `FnOnce`
//!     carries an `Output` associated type). The captures-`a` closures
//!     cannot be coerced to `fn(...)` pointers (the sibling-pattern
//!     `assoc_type_equality_on_parent.rs` rewrite), so the fixpoint is
//!     **defunctionalized**: each caller (`sqrt_u64`, `cbrt_u64`,
//!     `nth_root`) gets its own `loop_up` / `loop_down` tail-recursive
//!     pair with the `next` recurrence inlined, plus a `fixpoint_*`
//!     entry point that mirrors the original two-phase iteration. Same
//!     shape as `proof_patterns/sqrt_u64_modified` and
//!     `proof_patterns/cbrt_u64_modified`.
//!
//!   * `(x as f64).sqrt() as u64`, `(x as f64).cbrt() as u64`, and the
//!     `ln/exp`-based guess in `nth_root` use `f64`, which the Hax Lean
//!     prelude does not model (no `Cast u64 f64`, no `f64::sqrt`, no
//!     `f64::ln`, etc. — see `rewrite_patterns/f64_no_hax_model.rs`).
//!     Replaced with integer-only power-of-two guesses (`sqrt_guess_u64`,
//!     `cbrt_guess_u64`, `nth_root_guess`). Newton's iteration converges
//!     to the same fixpoint from any starting overestimate; only the
//!     iteration count changes.
//!
//!   * `u64::leading_zeros` (in `log2_u64`) is not modeled
//!     (`core_models.num.Impl_<N>.leading_zeros` is undefined —
//!     see `rewrite_patterns/u64_trailing_zeros_method.rs` for the same
//!     gap on the sibling method). Replaced with a tail-recursive shift
//!     loop (`log2_rec`).
//!
//!   * `u64::checked_pow` (in the `next` closure of `nth_root`) is not
//!     modeled (`core_models.<int>.Impl.{checked,wrapping,saturating}_*`
//!     are all undefined — see
//!     `rewrite_patterns/checked_wrapping_to_bare_arith.rs`). The caller
//!     **does** rely on the `None` branch to signal overflow, so per
//!     that pattern we cannot use bare `*`; instead we provide our own
//!     recursive `pow_u64_opt` that returns `Option<u64>` and detects
//!     overflow via `rest > u64::MAX / x`.
//!
//!   * `u32::MAX` (associated constant on a primitive integer impl)
//!     is replaced with its literal value `4_294_967_295u64` per
//!     `rewrite_patterns/primitive_int_assoc_const.rs`.
//!
//!   * `for s in (0..smax + 1).rev()` in `cbrt_u32` uses the `Range`
//!     `IntoIterator` and `.rev()` chain, neither of which is modeled
//!     (`core_models.iter.*` gaps — see
//!     `rewrite_patterns/iter_chain_to_recursion.rs`). Rewritten as
//!     tail recursion `cbrt_u32_loop` with the iteration counter `s_iter`
//!     decreasing from `smax+1` to `0`.
//!
//!   * `match n { 0 => panic!("..."), ... }` in the original `nth_root`
//!     panics on `n == 0`. `panic!("…")` with a format string would
//!     surface the unmodeled `alloc.string.*` namespace (see
//!     `rewrite_patterns/string_processing_unfixable.rs`); the same
//!     observable effect (a runtime panic, which `cargo test` requires
//!     and which Hax models as `RustM.fail Error.integerOverflow`) is
//!     induced by the u32 subtraction `n - 1` at `n = 0`. We perform
//!     this subtraction immediately after the `n == 0` check so the
//!     panic semantics match the original on the test input
//!     `nth_root(123u64, 0)`.
//!
//!   * `(a > 0) as u64` casts a `bool` to `u64`. The Hax Lean prelude
//!     has no `Cast Bool u64` instance (see
//!     `rewrite_patterns/bool_to_int_cast.rs`). Replaced with
//!     `if a > 0 { 1 } else { 0 }`.
//!
//!   * The `64 <= n || a < (1u64 << n)` test combines a guard with a
//!     partial RHS (`1u64 << n` panics for `n >= 64`). Hax extracts
//!     `||` eagerly (see `rewrite_patterns/short_circuit_and_with_partial_op.rs`),
//!     so we split into two sequential `if`s — the first handles
//!     `n >= 64` directly, the second only runs when `n < 64`.
//!
//!   * The nested `fn go(...)` inside `nth_root` is lifted to a
//!     top-level helper (Hax has limited support for nested functions
//!     and the encapsulation here is purely stylistic in the original).
//!
//! Behavioural equivalence is preserved on every input the test suite
//! exercises (verified via `cargo test`); the proptests `prop_sqrt_*`,
//! `prop_cbrt_*`, and `prop_nth_root_*` cross-check the postcondition
//! `r^n <= a < (r+1)^n` for randomised inputs.

// ---------------------------------------------------------------------
// Common helpers
// ---------------------------------------------------------------------

/// Returns `⌊log₂(x)⌋` for `x >= 1`. Replaces `u64::leading_zeros`,
/// which has no Hax Lean prelude model
/// (`rewrite_patterns/u64_trailing_zeros_method.rs`). Tail-recursive
/// shift loop; recursion depth is at most 63 (one step per bit) — well
/// inside the 10^5 safe envelope for the recursion-preference rule.
fn log2_rec(y: u64, count: u32) -> u32 {
    if y <= 1 {
        count
    } else {
        log2_rec(y >> 1, count + 1)
    }
}

fn log2_u64(x: u64) -> u32 {
    log2_rec(x, 0)
}

/// Tail-recursive `g << k` accumulator. Replaces a `while i < k {
/// g <<= 1; i += 1; }` shape per the recursion-preference rule.
/// Recursion depth bounded by `k`, which is at most 64.
fn pow2_loop(k: u32, i: u32, g: u64) -> u64 {
    if i >= k {
        g
    } else {
        pow2_loop(k, i + 1, g << 1)
    }
}

/// Compute `x^n` as `u64`, returning `None` if it overflows `u64`.
/// Replaces `u64::checked_pow`, which has no Hax model
/// (`rewrite_patterns/checked_wrapping_to_bare_arith.rs`). The caller
/// **does** branch on `None` (the original `next` closure in `nth_root`
/// returns 0 when the power overflows), so we cannot use bare `*`; we
/// reproduce `checked_pow`'s overflow semantics explicitly.
///
/// Termination: `n` is the decreasing measure. Recursion depth bounded
/// by the exponent (`<= 128` for the test sweep in proptest).
///
/// Overflow check: for `x > 0`, `rest * x > u64::MAX` iff
/// `rest > u64::MAX / x` (the floor division is the right threshold
/// because `(u64::MAX / x) * x <= u64::MAX < (u64::MAX / x + 1) * x`).
/// The `x == 0` case is special-cased first so the `u64::MAX / x`
/// division stays under its guard through Hax's eager `do`-block
/// extraction (see `rewrite_patterns/short_circuit_and_with_partial_op.rs`).
/// `u64::MAX` itself is inlined as the literal `18_446_744_073_709_551_615`
/// per `rewrite_patterns/primitive_int_assoc_const.rs`.
fn pow_u64_opt(x: u64, n: u32) -> Option<u64> {
    if n == 0 {
        Some(1)
    } else {
        match pow_u64_opt(x, n - 1) {
            Some(rest) => {
                if x == 0 {
                    Some(0)
                } else if rest > 18_446_744_073_709_551_615u64 / x {
                    None
                } else {
                    Some(rest * x)
                }
            }
            None => None,
        }
    }
}

// ---------------------------------------------------------------------
// cbrt_u32: Hacker's-Delight `icbrt2`, monomorphized to `u32`.
// ---------------------------------------------------------------------

/// Tail-recursive body of `cbrt_u32`. Replaces `for s in (0..smax+1).rev()`
/// from the original, which uses an unmodeled `Range` iterator + `.rev()`
/// chain (`rewrite_patterns/iter_chain_to_recursion.rs`).
///
/// The iteration counter `s_iter` decreases from `smax + 1 = 11` down to
/// `0`; each step corresponds to one source loop iteration with the
/// shadowed `s = s_iter_new * 3` substituted directly. Same shape as
/// `proof_patterns/cbrt_u64_modified::cbrt_u32_loop`.
fn cbrt_u32_loop(s_iter: u32, x: u32, y2: u32, y: u32) -> u32 {
    if s_iter == 0 {
        y
    } else {
        let s_iter_new = s_iter - 1;
        let s = s_iter_new * 3;
        let y2_d = y2 * 4;
        let y_d = y * 2;
        let b = 3 * (y2_d + y_d) + 1;
        if (x >> s) >= b {
            let x_new = x - (b << s);
            let y2_new = y2_d + 2 * y_d + 1;
            let y_new = y_d + 1;
            cbrt_u32_loop(s_iter_new, x_new, y2_new, y_new)
        } else {
            cbrt_u32_loop(s_iter_new, x, y2_d, y_d)
        }
    }
}

fn cbrt_u32(a: u32) -> u32 {
    // smax = 32 / 3 = 10; iterate s_iter = 11, 10, ..., 1 (body runs 11 times).
    cbrt_u32_loop(11, a, 0, 0)
}

// ---------------------------------------------------------------------
// sqrt_u64
// ---------------------------------------------------------------------

/// Integer-only power-of-two initial guess for `sqrt(a)`. Returns
/// `g = 2^ceil((log2(a)+1)/2)`, which is `>= sqrt(a)`. Replaces
/// `(a as f64).sqrt() as u64` (`f64` is not modeled by Hax —
/// `rewrite_patterns/f64_no_hax_model.rs`). The Babylonian iteration
/// converges to the same value from any starting overestimate; only
/// the iteration count differs.
fn sqrt_guess_u64(a: u64) -> u64 {
    let hi = log2_u64(a);
    let k = (hi + 2) / 2;
    pow2_loop(k, 0, 1)
}

/// Upward phase of the Babylonian fixpoint: while `x < xn`, advance.
/// Same shape as `proof_patterns/sqrt_u64_modified::sqrt_loop_up`.
fn sqrt_loop_up(a: u64, x: u64, xn: u64) -> (u64, u64) {
    if x < xn {
        let new_x = xn;
        let new_xn = (a / new_x + new_x) >> 1;
        sqrt_loop_up(a, new_x, new_xn)
    } else {
        (x, xn)
    }
}

/// Downward phase of the Babylonian fixpoint: while `x > xn`, advance;
/// otherwise return `x`. Newton's method converges quadratically from
/// an overestimate, so depth is `O(log log a)` — well bounded for `u64`.
/// Decreasing measure: `x` itself.
/// Same shape as `proof_patterns/sqrt_u64_modified::sqrt_loop_down`.
fn sqrt_loop_down(a: u64, x: u64, xn: u64) -> u64 {
    if x > xn {
        let new_x = xn;
        let new_xn = (a / new_x + new_x) >> 1;
        sqrt_loop_down(a, new_x, new_xn)
    } else {
        x
    }
}

/// Truncated principal square root of `a: u64`.
pub fn sqrt_u64(a: u64) -> u64 {
    if a < 4 {
        // `(a > 0) as u64` extracts to `Cast Bool u64`, which the Hax
        // Lean prelude does not provide
        // (`rewrite_patterns/bool_to_int_cast.rs`). Use if/else.
        return if a > 0 { 1 } else { 0 };
    }
    let x0 = sqrt_guess_u64(a);
    let xn0 = (a / x0 + x0) >> 1;
    let (x1, xn1) = sqrt_loop_up(a, x0, xn0);
    sqrt_loop_down(a, x1, xn1)
}

// ---------------------------------------------------------------------
// cbrt_u64
// ---------------------------------------------------------------------

/// Integer-only initial guess for the `cbrt` Newton fixpoint.
/// `k = ceil((log2(a)+1)/3)`, so `g = 2^k >= cbrt(a)`. At the call site
/// (`a > 4_294_967_295`), `log2(a) >= 32`, so `k <= 22`, hence `g <= 2^22`
/// and `g*g <= 2^44 < 2^64`. Same shape as
/// `proof_patterns/cbrt_u64_modified::cbrt_guess_u64`.
fn cbrt_guess_u64(a: u64) -> u64 {
    let hi = log2_u64(a);
    let k = (hi + 3) / 3;
    pow2_loop(k, 0, 1)
}

fn cbrt_loop_up(a: u64, x: u64, xn: u64) -> (u64, u64) {
    if x < xn {
        let new_x = xn;
        let new_xn = (a / (new_x * new_x) + new_x * 2) / 3;
        cbrt_loop_up(a, new_x, new_xn)
    } else {
        (x, xn)
    }
}

fn cbrt_loop_down(a: u64, x: u64, xn: u64) -> u64 {
    if x > xn {
        let new_x = xn;
        let new_xn = (a / (new_x * new_x) + new_x * 2) / 3;
        cbrt_loop_down(a, new_x, new_xn)
    } else {
        x
    }
}

/// Truncated principal cube root of `a: u64`.
pub fn cbrt_u64(a: u64) -> u64 {
    if a < 8 {
        return if a > 0 { 1 } else { 0 };
    }
    // u32::MAX = 2^32 - 1 = 4_294_967_295. Inlined as literal because
    // `core_models.num.Impl_<N>.MAX` is not defined in the Hax Lean
    // prelude (`rewrite_patterns/primitive_int_assoc_const.rs`).
    if a <= 4_294_967_295u64 {
        return cbrt_u32(a as u32) as u64;
    }
    let x0 = cbrt_guess_u64(a);
    let xn0 = (a / (x0 * x0) + x0 * 2) / 3;
    let (x1, xn1) = cbrt_loop_up(a, x0, xn0);
    cbrt_loop_down(a, x1, xn1)
}

// ---------------------------------------------------------------------
// nth_root
// ---------------------------------------------------------------------

/// Integer-only initial guess for the `nth_root` Newton fixpoint.
/// `1u64 << ((log2(a) + n - 1) / n)` — works for any `a >= 1` and
/// `n >= 1`. Replaces the original `if x <= u32::MAX as u64 { ... }
/// else { (x.ln() / n).exp() as u64 }` conditional, whose `else` branch
/// used `f64::ln` / `f64::exp` — unmodeled by Hax
/// (`rewrite_patterns/f64_no_hax_model.rs`).
fn nth_root_guess(a: u64, n: u32) -> u64 {
    let shift = (log2_u64(a) + n - 1) / n;
    pow2_loop(shift, 0, 1)
}

/// One step of the Newton recurrence `(y + x*(n-1)) / n` where
/// `y = a / x^(n-1)` (or `0` if `x^(n-1)` overflows `u64`, matching
/// the original `match x.checked_pow(n1) { ... }` shape).
///
/// The `ax == 0` branch protects against `a / 0`: it can only arise if
/// `x == 0` (since `pow_u64_opt(0, k>0) = Some(0)`), which the Newton
/// iteration does not reach in practice (the initial guess is `>= 1`
/// and the recurrence preserves `x >= 1` whenever `n >= 2`). The guard
/// is kept defensively and matches the original code's effective
/// "treat divide-by-anomaly as y = 0" pattern.
fn nth_root_step(a: u64, n1: u32, n: u32, x: u64) -> u64 {
    let y = match pow_u64_opt(x, n1) {
        Some(ax) => {
            if ax == 0 {
                0
            } else {
                a / ax
            }
        }
        None => 0,
    };
    (y + x * n1 as u64) / n as u64
}

fn nth_root_loop_up(a: u64, n1: u32, n: u32, x: u64, xn: u64) -> (u64, u64) {
    if x < xn {
        let new_x = xn;
        let new_xn = nth_root_step(a, n1, n, new_x);
        nth_root_loop_up(a, n1, n, new_x, new_xn)
    } else {
        (x, xn)
    }
}

fn nth_root_loop_down(a: u64, n1: u32, n: u32, x: u64, xn: u64) -> u64 {
    if x > xn {
        let new_x = xn;
        let new_xn = nth_root_step(a, n1, n, new_x);
        nth_root_loop_down(a, n1, n, new_x, new_xn)
    } else {
        x
    }
}

/// Returns the truncated principal `n`th root of `self_val: u64`.
///
/// Equivalent to `<u64 as num_integer::Roots>::nth_root(&self_val, n)` in
/// `num-integer-0.1.46`.
///
/// # Panics
///
/// Panics if `n == 0` (induced via `n - 1` u32 underflow — see
/// crate-level docs for why `panic!("...")` with a format string is
/// avoided).
pub fn nth_root(self_val: u64, n: u32) -> u64 {
    let a = self_val;

    // Specialize small roots first so the `n == 0` path falls through to
    // the underflowing subtraction below.
    if n == 1 {
        return a;
    }
    if n == 2 {
        return sqrt_u64(a);
    }
    if n == 3 {
        return cbrt_u64(a);
    }

    // Handle the panic-on-`n == 0` contract via u32 subtraction underflow.
    // `n == 0` does not match any of the early-returns above, so we reach
    // here; `n - 1` underflows u32 and panics (overflow check is on in
    // debug builds, which is what `cargo test` uses). Hax models this as
    // `RustM.fail Error.integerOverflow`, matching the original `panic!`.
    // For `n >= 4`, `n - 1 >= 3` is a regular subtraction.
    let n1 = n - 1;

    // `1u64 << n` is partial for `n >= 64`. The original
    // `64 <= n || a < (1u64 << n)` uses `||` short-circuit, but Hax
    // extracts `||` eagerly (see
    // `rewrite_patterns/short_circuit_and_with_partial_op.rs`), so we
    // split into two sequential `if`s: the first handles `n >= 64`
    // directly, the second only runs when `n < 64`.
    if n >= 64 {
        return if a > 0 { 1 } else { 0 };
    }
    if a < (1u64 << n) {
        return if a > 0 { 1 } else { 0 };
    }

    let x0 = nth_root_guess(a, n);
    let xn0 = nth_root_step(a, n1, n, x0);
    let (x1, xn1) = nth_root_loop_up(a, n1, n, x0, xn0);
    nth_root_loop_down(a, n1, n, x1, xn1)
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
