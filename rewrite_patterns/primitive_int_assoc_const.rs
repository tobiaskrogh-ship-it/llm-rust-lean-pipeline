// unsupported: associated constants on primitive integer types
// (`u32::MAX`, `u64::MAX`, `i32::MIN`, `usize::MAX`, etc.). Extraction
// emits a reference to `core_models.num.Impl_<N>.MAX` (the impl number
// varies per primitive), but the Hax Lean prelude does not define those
// constants, so `lake build` fails with
//   `error: Unknown identifier 'core_models.num.Impl_8.MAX'`
// (or `Impl_9.MAX`, etc., depending on which integer width is used).
// Workaround: replace the associated-constant reference with the literal
// value at the right type — the bit-pattern is fixed and well-known.
// Sibling pattern `u64_trailing_zeros_method.rs` covers the same kind of
// failure for *methods* on integer impl blocks; this one covers *constants*.

// before

if a <= u32::MAX as u64 {
    return cbrt_u32(a as u32) as u64;
}

// after

// `u32::MAX = 2^32 - 1 = 4_294_967_295`. Inlining the literal avoids the
// missing `core_models.num.Impl_8.MAX` identifier in the Hax Lean prelude.
if a <= 4_294_967_295u64 {
    return cbrt_u32(a as u32) as u64;
}
