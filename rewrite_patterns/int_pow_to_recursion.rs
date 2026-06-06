// unsupported: `.pow(n)` on primitive integers — `u8::pow`, `u32::pow`,
// `u64::pow`, `i32::pow`, etc. These extract to inherent methods on
// `core_models.<int>.Impl.pow`, which the Hax Lean prelude does not model.
// `lake build` fails with:
//   error: Unknown identifier `core_models.u64.Impl.pow`
//
// Mechanical fix: replace with structural recursion on the exponent. Per
// the project's recursion-preference rule, this is the preferred shape
// over a `while` loop — a single decreasing measure (`exp`) and no
// mutable state means the Lean termination checker and any downstream
// proof are both substantially simpler.

// before

pub fn ipow(base: u64, exp: u32) -> u64 {
    base.pow(exp)
}

// after

pub fn ipow(base: u64, exp: u32) -> u64 {
    if exp == 0 {
        1
    } else {
        base * ipow(base, exp - 1)
    }
}
