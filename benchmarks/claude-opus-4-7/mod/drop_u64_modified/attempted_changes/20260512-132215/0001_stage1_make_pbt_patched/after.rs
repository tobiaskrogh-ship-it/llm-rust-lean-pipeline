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

    // ---- Original doctest-derived tests --------------------------------

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

    // ---- Property-based tests ------------------------------------------
    //
    // `drop(_x: u64)` has no preconditions and an empty body. The contract
    // therefore reduces to three claims:
    //
    //   (P1) Totality / never-panics: defined for every `u64`.
    //   (P2) Postcondition on the return value: returns the unit value `()`.
    //   (P3) Caller-side `Copy` invariant: because `u64: Copy`, the value
    //        passed in is unaffected at the call site.
    //
    // proptest is not a dependency in this crate, so each "property" test
    // iterates over a deterministic corpus that combines the two boundary
    // values (`0`, `u64::MAX`) with a spread of bit-patterns. This is a
    // sound poor-man's property test for a function with no preconditions.

    /// Deterministic corpus: extremes, low/high bytes, powers of two,
    /// patterns that exercise every bit, and a few "interesting" values.
    fn sample_u64s() -> [u64; 16] {
        [
            0,
            1,
            2,
            u64::MAX,
            u64::MAX - 1,
            u64::MAX / 2,
            u64::MAX / 2 + 1,
            0x0000_0000_FFFF_FFFF,
            0xFFFF_FFFF_0000_0000,
            0xAAAA_AAAA_AAAA_AAAA,
            0x5555_5555_5555_5555,
            0xDEAD_BEEF_DEAD_BEEF,
            1 << 0,
            1 << 32,
            1 << 63,
            42,
        ]
    }

    /// (P1) Totality: `drop` accepts every `u64` without panicking.
    /// (P2) Postcondition: each call yields `()`.
    #[test]
    fn prop_drop_is_total_and_returns_unit() {
        for &x in sample_u64s().iter() {
            // If `drop` panicked on any value the test process would abort
            // and the test would fail.
            let r: () = drop(x);
            // `()` is a singleton inhabited only by `()`, so this is the
            // strongest postcondition we can state. We compare explicitly
            // rather than discarding so the assertion is visible.
            assert_eq!(r, ());
        }
    }

    /// (P3) `Copy` invariant: the caller's value is bitwise unchanged
    /// after `drop`. This is the one observable, semantically independent
    /// claim — it is what distinguishes `drop` from a hypothetical
    /// implementation that consumed and then mutated through a pointer.
    #[test]
    fn prop_drop_preserves_caller_value_for_copy_types() {
        for &x in sample_u64s().iter() {
            let before = x;
            drop(x);
            // `x` is still in scope because `u64: Copy`; the bit pattern
            // must be unchanged.
            assert_eq!(x, before);
        }
    }

    /// (P1) repeated: calling `drop` many times in a row on the same value
    /// is still total. Guards against any hypothetical state accumulation
    /// (which the empty body forbids, but the test pins the contract).
    #[test]
    fn prop_drop_can_be_called_repeatedly() {
        let x: u64 = 0xCAFE_F00D_BAAA_AAAD;
        for _ in 0..1024 {
            drop(x);
        }
        assert_eq!(x, 0xCAFE_F00D_BAAA_AAAD);
    }
}
