// unsupported: `.checked_*` / `.wrapping_*` / `.saturating_*` / `.overflowing_*`
// arithmetic methods on primitive integers — `u64::wrapping_add`,
// `i32::checked_mul`, `u8::saturating_sub`, etc. Each extracts to a method
// on `core_models.<int>.Impl.{wrapping,checked,saturating,overflowing}_<op>`,
// which the Hax Lean prelude does not model. `lake build` fails with:
//   error: Unknown identifier `core_models.u64.Impl.wrapping_add`
//
// Hax already encodes overflow checks on bare arithmetic: extraction lowers
// `+` / `-` / `*` into `RustM` Hoare triples with an overflow obligation,
// and the downstream proof stage discharges that obligation explicitly. So
// the Rust source can drop the overflow-aware wrapper and use plain
// arithmetic; the obligation it would have encoded is regained at the
// proof level.
//
// `wrapping_*` -> bare op is type-preserving. `checked_*` returns
// `Option<T>`; if the caller relies on the `None` branch to signal
// overflow, the function signature has to change (return `T` and let the
// extracted Hoare triple carry the overflow guard). `saturating_*` and
// `overflowing_*` change the contract entirely and may need callers
// updated; flag it rather than rewriting blindly.

// before

pub fn next(a: u64, b: u64) -> u64 {
    a.wrapping_add(b)
}

// after

pub fn next(a: u64, b: u64) -> u64 {
    a + b
}
