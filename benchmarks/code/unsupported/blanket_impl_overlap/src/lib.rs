//! Unsupported (likely): blanket implementations. The blanket
//! `impl<T: Default> Tag for T` is fine in Rust but creates an open
//! family of instances Hax has to enumerate for monomorphisation —
//! often producing duplicate / conflicting trait impls in the Lean
//! output.

pub trait Tag {
    fn tag() -> u64;
}

impl<T: Default> Tag for T {
    fn tag() -> u64 { 42 }
}

pub fn tag_u64() -> u64 {
    <u64 as Tag>::tag()
}
