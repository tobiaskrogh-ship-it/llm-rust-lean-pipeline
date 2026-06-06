//! Extracted from `core::mem::forget`, monomorphized to `u64`.
//!
//! Source: `to_be_extracted/core-1.94.0/src/mem/mod.rs:159` (function `forget`).
//!
//! `mem::forget` is defined as `let _ = ManuallyDrop::new(t);`. `ManuallyDrop`
//! is a `#[repr(transparent)]` wrapper struct with no `Drop` impl — its only
//! purpose is to suppress the destructor of its wrapped value. The struct is
//! inlined here as a private type so this crate is self-contained.

/// Inlined from `core::mem::ManuallyDrop`. We only need construction; no
/// destructor runs because `ManuallyDrop` has no `Drop` impl.
#[repr(transparent)]
struct ManuallyDrop<T> {
    value: T,
}

impl<T> ManuallyDrop<T> {
    /// Inlined from `ManuallyDrop::new`.
    const fn new(value: T) -> ManuallyDrop<T> {
        ManuallyDrop { value }
    }
}

/// Takes ownership and "forgets" about the value without running its destructor.
#[inline]
pub const fn forget(t: u64) {
    let _ = ManuallyDrop::new(t);
}

#[cfg(test)]
mod tests {
    use super::*;

    // The source's doc-tests for `forget` use `File` and `Vec<u8>` (alloc/std
    // types) which can't run in a `#[no_std]`, alloc-free, dependency-free
    // crate. The closest analog for the monomorphized-to-`u64` case is to
    // verify the function returns `()` and does not mutate a copied value.
    #[test]
    fn forget_returns_unit_for_u64() {
        let x: u64 = 42;
        let unit: () = forget(x);
        let _ = unit;
        // Since u64 is Copy, the caller's copy is untouched.
        assert_eq!(x, 42);
    }

    #[test]
    fn forget_accepts_various_u64_values() {
        forget(0u64);
        forget(u64::MAX);
        forget(1u64);
        forget(u64::MAX / 2);
    }
}
