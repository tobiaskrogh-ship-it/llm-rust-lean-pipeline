// unsupported: a function whose **signature** is `f64`-typed and whose body
// performs arithmetic / comparison / `abs` on those floats. Distinct from
// `f64_no_hax_model.rs`, which covers a single internal `f64` call (e.g.
// `(a as f64).cbrt() as u64`) inside an otherwise-integer function. Here the
// public types `&[f64]`, `f64` are pinned by tests, so the rewriter cannot
// keep the algorithm in float space at all.
//
// The Hax Lean prelude (`Hax/core_models/epilogue/float.lean`) declares only
// `Add` / `Sub` / `Mul` / `Div` for `f64`. Everything else the body usually
// needs is missing:
//
//   - `core_models.f64.Impl.abs` is **undefined**. Only `core_models.f32`
//     has `Impl.abs`, and even that is mis-typed (its body claims `f64`).
//     `lake build` fails:
//         error: Unknown identifier `core_models.f64.Impl.abs`
//   - `core_models.cmp.PartialOrd` has **no `f64` instance**, so any `<`,
//     `>`, `<=`, `>=` on `f64` fails synthesis:
//         error: failed to synthesize instance of type class
//                Decidable __do_lift⁢
//   - `Neg f64` is **not defined**, so even rewriting `.abs()` as
//     `if x < 0.0 { -x } else { x }` does not unblock.
//   - `core_models.ops.arith.Sub.sub` is emitted **without** its explicit
//     type arguments. Integer types route through the `-?` infix in
//     `rust_primitives/ops.lean` and so don't surface this; `f64` has no
//     `-?` and the generic typeclass call breaks:
//         error: Application type mismatch: ... has type f64 ... but is
//                expected to have type Type ... in the application
//                core_models.ops.arith.Sub.sub __do_lift⁢¹
//
// Conclusion: there is no Rust-level fix that keeps the signature float-
// typed. Translate the signature to `i64` (or `u64` fixed-point with a
// chosen scale) and reformulate `.abs()` as a conditional on the integer
// difference. Document the type change in the doc-comment so downstream
// stages see the semantic shift.

// before

pub fn has_close_elements(numbers: &[f64], threshold: f64) -> bool {
    let n = numbers.len();
    let mut i = 0;
    while i < n {
        let mut j = 0;
        while j < n {
            if i != j {
                let diff = (numbers[i] - numbers[j]).abs();
                if diff < threshold {
                    return true;
                }
            }
            j += 1;
        }
        i += 1;
    }
    false
}

// after

/// Translated `f64 -> i64` because the Hax Lean prelude has gaps in `f64`
/// support (no `Impl.abs`, no `PartialOrd`, no `Neg`, broken `Sub.sub` for
/// non-integer types). Per the recursion-preference rule, both nested
/// loops collapse into one tail-recursive function indexed by
/// `k = i*n + j`, with the obvious decreasing measure `n*n - k`.
fn has_close_elements_at(numbers: &[i64], threshold: i64, k: u64) -> bool {
    let n = numbers.len() as u64;
    if k >= n * n {
        false
    } else {
        let i = (k / n) as usize;
        let j = (k % n) as usize;
        // `.abs()` on the i64 difference rewritten as a conditional, since
        // even `i64::abs` would surface as a typeclass call; pure `if/else`
        // arithmetic stays inside the integer fragment Hax models cleanly.
        let diff = if numbers[i] > numbers[j] {
            numbers[i] - numbers[j]
        } else {
            numbers[j] - numbers[i]
        };
        if i != j && diff < threshold {
            true
        } else {
            has_close_elements_at(numbers, threshold, k + 1)
        }
    }
}

pub fn has_close_elements(numbers: &[i64], threshold: i64) -> bool {
    has_close_elements_at(numbers, threshold, 0)
}
