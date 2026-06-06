// unsupported: anonymous `impl Trait` parameter where the trait spelling
// contains characters that are illegal in Lean identifiers — e.g.
// `impl FnOnce() -> u64`, `impl Fn(u32) -> bool`. Hax derives the type
// parameter name directly from the trait spelling, producing identifiers
// like `impl_FnOnce()_-__u64` with embedded parentheses and hyphens.
// `cargo hax into lean` extraction succeeds, but `lake build` fails with
// `error: unexpected token '('; expected ')'` at the parameter binder.
// Workaround: replace `impl Trait` with a named generic `F: Trait`. Hax
// then uses the explicit identifier `F` for the extracted type parameter.
// This preserves all closure semantics (mutable captures still work, so
// tests exercising closure side effects continue to pass).
// Note: if your tests *don't* rely on closures capturing mutable state,
// prefer the bare function-pointer form `fn(...) -> ...` (see
// `assoc_type_equality_on_parent.rs`) — it avoids the `FnOnce` trait
// machinery entirely and keeps the extracted Lean out of `RustM`.

// before

pub fn ok_or_else(b: bool, f: impl FnOnce() -> u64) -> Result<(), u64> {
    if b { Ok(()) } else { Err(f()) }
}

// after

pub fn ok_or_else<F: FnOnce() -> u64>(b: bool, f: F) -> Result<(), u64> {
    if b { Ok(()) } else { Err(f()) }
}
