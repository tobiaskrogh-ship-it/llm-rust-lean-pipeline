// unsupported: `.abs()` on signed primitive integers — `i8::abs`,
// `i16::abs`, `i32::abs`, `i64::abs`, `i128::abs`, `isize::abs`. These
// extract to inherent methods on `core_models.<int>.Impl.abs`, which the
// Hax Lean prelude does not model. `lake build` fails with:
//   error: Unknown identifier `core_models.i64.Impl.abs`
//
// Mechanical fix: inline `.abs()` as `if x < 0 { -x } else { x }`. This
// preserves Rust's `<int>::MIN` panic exactly — `-i32::MIN` overflows in
// debug mode, the same way `i32::MIN.abs()` does — so tests that exercise
// that boundary continue to fail in the same place.
//
// For `f64::abs()` see `f64_signature_to_i64.rs` (the prelude has further
// gaps that prevent staying in the float domain at all).

// before

pub fn distance(a: i64, b: i64) -> i64 {
    (a - b).abs()
}

// after

pub fn distance(a: i64, b: i64) -> i64 {
    let d = a - b;
    if d < 0 { -d } else { d }
}
