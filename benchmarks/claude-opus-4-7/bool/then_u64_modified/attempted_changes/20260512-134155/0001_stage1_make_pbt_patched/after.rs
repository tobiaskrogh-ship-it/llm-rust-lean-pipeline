//! Extracted from `core::bool` — inlined `bool::then`, monomorphized to `u64`.

/// Returns `Some(f())` if `b` is `true`, or `None` otherwise.
#[inline]
pub fn then(b: bool, f: impl FnOnce() -> u64) -> Option<u64> {
    if b { Some(f()) } else { None }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from the first doc-test of `bool::then`.
    #[test]
    fn then_basic() {
        assert_eq!(then(false, || 0u64), None);
        assert_eq!(then(true, || 0u64), Some(0u64));
    }

    // Transferred from the second doc-test of `bool::then` (lazy-evaluation).
    // The source's closure returns `()`; monomorphized here to return `u64`.
    #[test]
    fn then_lazy() {
        let mut a = 0u64;

        then(true, || {
            a += 1;
            0u64
        });
        then(false, || {
            a += 1;
            0u64
        });

        // `a` is incremented once because the closure is evaluated lazily by `then`.
        assert_eq!(a, 1);
    }

    // Property: when `b == true`, the result is `Some(f())` — the closure's
    // value is passed through unchanged. Sampled over u64 including boundary
    // values (0, 1, MAX, MAX-1, MAX/2, and a mid-range power of two).
    #[test]
    fn then_true_passes_through_closure_value() {
        for v in [0u64, 1, 2, 1u64 << 32, u64::MAX / 2, u64::MAX - 1, u64::MAX] {
            assert_eq!(then(true, || v), Some(v));
        }
    }

    // Property: when `b == false`, the result is `None`, independent of what
    // the closure would have returned. Sampled over the same range of u64
    // values to rule out any dependence of the `None`-branch on `f`'s value.
    #[test]
    fn then_false_is_none_regardless_of_closure_value() {
        for v in [0u64, 1, 2, 1u64 << 32, u64::MAX / 2, u64::MAX - 1, u64::MAX] {
            assert_eq!(then(false, || v), None);
        }
    }
}
