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
}
