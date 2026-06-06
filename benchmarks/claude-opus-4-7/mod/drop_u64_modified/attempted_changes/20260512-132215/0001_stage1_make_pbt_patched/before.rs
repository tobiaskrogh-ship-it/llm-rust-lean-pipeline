//! Extracted from `core::mem::drop`, monomorphized to `u64`.
//!
//! Source: `to_be_extracted/core-1.94.0/src/mem/mod.rs:970` (function `drop`).
//!
//! The source defines `drop` as:
//!
//! ```ignore
//! pub const fn drop<T>(_x: T) where T: [const] Destruct {}
//! ```
//!
//! Body is empty — the parameter is moved in and dropped at function exit.
//! For `u64` (a `Copy` type) the call is effectively a no-op on the caller's
//! value.

/// Disposes of a value.
#[inline]
pub fn drop(_x: u64) {}

#[cfg(test)]
mod tests {
    use super::*;

    // Doc-test #1 from source: `let v = vec![1, 2, 3]; drop(v);` uses `Vec`
    // (alloc); the closest monomorphic-to-u64 analog is just a trivial call.
    #[test]
    fn doctest_basic_call() {
        let v: u64 = 7;
        drop(v);
    }

    // Doc-test #3 from source verifies that Copy types are unaffected by
    // `drop` — the original copy persists. Transferred for `u64`.
    #[test]
    fn doctest_copy_types_unaffected() {
        let x: u64 = 1;
        drop(x); // a copy of `x` is moved and dropped
        // `x` still available because u64 is Copy.
        assert_eq!(x, 1);
    }

    #[test]
    fn drop_returns_unit() {
        let r: () = drop(123u64);
        let _ = r;
    }
}
