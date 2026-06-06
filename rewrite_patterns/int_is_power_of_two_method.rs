// unsupported: `usize::is_power_of_two` (and the sibling
// `u8/u16/u32/u64/u128::is_power_of_two`). Extraction succeeds and emits
// a call to `core_models.num.Impl_<N>.is_power_of_two`, but the Hax Lean
// prelude has no definition for that identifier, so `lake build` fails
// with `Unknown identifier 'core_models.num.Impl_11.is_power_of_two'`
// (impl number varies per primitive width).
// Workaround: inline the classic bit-twiddling check, but as an
// `if`/`else`, NOT as `x != 0 && (x & (x - 1)) == 0`. The `&&` form
// looks identical in Rust (short-circuit guards `x - 1` against
// underflow at `x = 0`), but Hax's `do`-block extraction is eager —
// every `←` bind runs before the `&&?` combinator, so `x - 1` is
// evaluated unconditionally and `is_power_of_two_usize 0` extracts to
// `RustM.fail Error.integerOverflow`. `lake build` still passes (no
// extraction error), but downstream proof obligations that claim
// `is_power_of_two_usize 0 = RustM.ok false` become FALSE in the
// extracted model. The `if`/`else` form preserves the guard through
// extraction — the else branch is gated by the if-condition's value.
// See the sibling `short_circuit_and_with_partial_op.rs` for the
// general rule. `u64_trailing_zeros_method.rs` covers the same
// extraction failure for bit-count methods; this one covers
// `is_power_of_two` specifically.

// before

pub fn is_size_align_valid(size: usize, align: usize) -> bool {
    if !align.is_power_of_two() {
        return false;
    }
    // ...
    true
}

// after

// `usize::is_power_of_two()` extracts to an unmodeled
// `core_models.num.Impl_11.is_power_of_two` identifier in the Hax Lean
// prelude. Inline the standard bit-twiddling check using primitives Hax
// models (`==`, `&`, `-`). Use `if`/`else` — NOT `x != 0 && …` — so the
// guard on `x - 1` survives Hax's eager `do`-block extraction
// (see `short_circuit_and_with_partial_op.rs`).
fn is_power_of_two_usize(x: usize) -> bool {
    if x == 0 { false } else { (x & (x - 1)) == 0 }
}

pub fn is_size_align_valid(size: usize, align: usize) -> bool {
    if !is_power_of_two_usize(align) {
        return false;
    }
    // ...
    true
}
