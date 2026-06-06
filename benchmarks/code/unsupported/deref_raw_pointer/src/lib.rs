//! Unsupported: raw pointer dereference inside an `unsafe` block.
//! Hax models a safe subset of Rust; raw pointer operations have no
//! Lean representation by design.

pub unsafe fn deref(p: *const u64) -> u64 {
    unsafe { *p }
}
