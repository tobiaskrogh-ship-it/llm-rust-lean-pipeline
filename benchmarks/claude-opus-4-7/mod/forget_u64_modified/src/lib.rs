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

    // Contract of `forget` for `u64`:
    //
    //   * Preconditions:   none — every `u64` is a valid argument (totality).
    //   * Postcondition:   returns `()`; there is no other observable effect.
    //   * Failure:         cannot panic, cannot return an error, cannot
    //                      overflow.
    //   * Const-ness:      declared `const fn`, so it must be callable in a
    //                      `const` context for any `u64` argument.
    //
    // Each test below pins down one of these clauses. We deliberately do not
    // exhaust the 2^64 input space — a representative cover of boundaries
    // (0, 1, MAX-1, MAX) and interior points is enough, because the function
    // body never branches on its argument.

    /// Postcondition + totality: `forget(t)` returns `()` for any `u64`,
    /// including the boundaries and a handful of interior values. A buggy
    /// implementation that panicked on, e.g., `u64::MAX` or `0` would be
    /// caught here.
    #[test]
    fn forget_returns_unit_on_representative_values() {
        let values: [u64; 9] = [
            0,
            1,
            2,
            42,
            u64::MAX / 2,
            (1u64 << 63) - 1,
            1u64 << 63,
            u64::MAX - 1,
            u64::MAX,
        ];
        for &x in &values {
            let result: () = forget(x);
            // Bind to ensure the unit return is actually used; no further
            // observation is possible because `()` has a single inhabitant.
            let _ = result;
        }
    }

    /// Calling convention: since `u64: Copy`, passing `t` to `forget` by
    /// value does not invalidate the caller's binding. This is a property of
    /// `Copy`, not of `forget` itself, but it documents the expected
    /// interaction at call sites that were previously written for non-`Copy`
    /// generic `T`.
    #[test]
    fn forget_leaves_caller_copy_intact() {
        let x: u64 = 0xDEAD_BEEF_CAFE_BABE;
        forget(x);
        assert_eq!(x, 0xDEAD_BEEF_CAFE_BABE);
    }

    /// Const-ness: `forget` is declared `const fn`, so it must evaluate in
    /// `const` context for any `u64`. A regression that made the body
    /// non-const (e.g. by introducing a non-const call) would fail to
    /// compile this test.
    #[test]
    fn forget_is_callable_in_const_context() {
        const _U_ZERO: () = forget(0);
        const _U_MAX: () = forget(u64::MAX);
        const _U_MID: () = forget(u64::MAX / 2);
    }
}
