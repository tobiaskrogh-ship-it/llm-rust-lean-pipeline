//! Unsupported: `core::mem::transmute`. Same family as `deref_raw_pointer`:
//! the rewrite pattern `unsafe_transmute_to_bits.rs` says to replace this
//! with the safe `f64::to_bits()` method.

pub fn bits(x: f64) -> u64 {
    unsafe { core::mem::transmute(x) }
}
