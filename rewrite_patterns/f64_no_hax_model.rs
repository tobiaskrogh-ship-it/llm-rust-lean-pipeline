// unsupported: `f64` (and `f32`) — neither casts *to* a float nor method
// calls *on* a float have a model in the Hax Lean prelude.
//   - `x as f64` extracts to a `Cast <int> f64` typeclass call. `lake build`
//     fails with `error: failed to synthesize instance of type class
//     Cast u64 f64` (or `Cast u32 f64`, etc.).
//   - `x.cbrt()` / `x.sqrt()` / `x.ln()` / any `f64` inherent method
//     extracts to `std.f64.Impl.<method>`, which the prelude does not
//     define. `lake build` fails with
//     `error: Unknown identifier 'std.f64.Impl.cbrt'`.
// There is no "small fix" — `f64` itself is the problem. The computation
// has to be reformulated to stay in the integer domain. When the float
// only served as a fast initial guess for a converging integer recurrence
// (Newton's method, binary search, etc.), a coarser integer guess is
// sufficient: the recurrence still converges to the same fixpoint.
// Sibling pattern `bool_to_int_cast.rs` covers a different missing `Cast`
// instance (`Cast Bool <int>`); this one covers the broader `f64` gap.
// Sibling pattern `f64_signature_to_i64.rs` covers the harder case where
// the function's **public signature** is `f64`-typed (so the float can't
// be confined to an internal call site) and the body uses comparison /
// `abs` / subtraction on floats — all of which hit additional prelude
// gaps beyond the casts/methods this pattern documents.

// before

pub fn cbrt(x: u64) -> u64 {
    let a = x;
    if a < 8 {
        return if a > 0 { 1 } else { 0 };
    }
    if a <= 4_294_967_295u64 {
        return cbrt_u32(a as u32) as u64;
    }
    // f64-based initial guess for Newton's fixpoint.
    let guess = (a as f64).cbrt() as u64;
    fixpoint_cbrt(a, guess)
}

// after

/// Integer-only initial guess for the Newton fixpoint, replacing
/// `(a as f64).cbrt() as u64`. Returns a power-of-two `g` with
/// `cbrt(a) <= g < 2^32`, so the recurrence `(a / (x*x) + 2*x) / 3`
/// stays inside `u64` from the first step. The fixpoint converges to the
/// same value regardless of starting point, so a coarse integer guess
/// suffices.
fn cbrt_guess_u64(a: u64) -> u64 {
    // floor(log2(a)) via shift loop.
    let mut hi: u32 = 0;
    let mut y: u64 = a;
    while y > 1 {
        y >>= 1;
        hi += 1;
    }
    // k = ceil((hi + 1) / 3); compute 2^k via a doubling loop.
    let k: u32 = (hi + 3) / 3;
    let mut g: u64 = 1;
    let mut i: u32 = 0;
    while i < k {
        g <<= 1;
        i += 1;
    }
    g
}

pub fn cbrt(x: u64) -> u64 {
    let a = x;
    if a < 8 {
        return if a > 0 { 1 } else { 0 };
    }
    if a <= 4_294_967_295u64 {
        return cbrt_u32(a as u32) as u64;
    }
    // Integer-only guess; `f64` cast / `f64::cbrt` would both fail Hax.
    let guess = cbrt_guess_u64(a);
    fixpoint_cbrt(a, guess)
}
