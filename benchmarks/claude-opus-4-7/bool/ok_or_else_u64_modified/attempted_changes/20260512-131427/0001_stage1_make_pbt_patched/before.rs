//! Extracted from `core::bool` — inlined `bool::ok_or_else`, monomorphized to `u64`.

/// Returns `Ok(())` if `b` is `true`, or `Err(f())` otherwise.
#[inline]
pub fn ok_or_else(b: bool, f: impl FnOnce() -> u64) -> Result<(), u64> {
    if b { Ok(()) } else { Err(f()) }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from the first doc-test of `bool::ok_or_else`.
    #[test]
    fn ok_or_else_basic() {
        assert_eq!(ok_or_else(false, || 0u64), Err(0u64));
        assert_eq!(ok_or_else(true, || 0u64), Ok(()));
    }

    // Transferred from the second doc-test of `bool::ok_or_else` (lazy-evaluation).
    // The source's closure returns `()`; monomorphized here to return `u64`.
    #[test]
    fn ok_or_else_lazy() {
        let mut a = 0u64;

        assert!(
            ok_or_else(true, || {
                a += 1;
                0u64
            })
            .is_ok()
        );
        assert!(
            ok_or_else(false, || {
                a += 1;
                0u64
            })
            .is_err()
        );

        // `a` is incremented once because the closure is evaluated lazily by
        // `ok_or_else`.
        assert_eq!(a, 1);
    }
}
