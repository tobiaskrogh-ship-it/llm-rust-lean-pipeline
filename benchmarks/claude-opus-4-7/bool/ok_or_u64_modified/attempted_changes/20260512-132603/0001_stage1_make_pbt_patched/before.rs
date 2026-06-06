//! Extracted from `core::bool` — inlined `bool::ok_or`, monomorphized to `u64`.

/// Returns `Ok(())` if `b` is `true`, or `Err(err)` otherwise.
///
/// Arguments passed to `ok_or` are eagerly evaluated; if you are
/// passing the result of a function call, it is recommended to use
/// `ok_or_else`, which is lazily evaluated.
#[inline]
pub fn ok_or(b: bool, err: u64) -> Result<(), u64> {
    if b { Ok(()) } else { Err(err) }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from the first doc-test of `bool::ok_or`.
    #[test]
    fn ok_or_basic() {
        assert_eq!(ok_or(false, 0u64), Err(0u64));
        assert_eq!(ok_or(true, 0u64), Ok(()));
    }

    // Transferred from the second doc-test of `bool::ok_or` (eager-evaluation).
    // The source's closure returns `()`; monomorphized here to return `u64`.
    #[test]
    fn ok_or_eager() {
        let mut a = 0u64;
        let mut function_with_side_effects = || {
            a += 1;
            0u64
        };

        assert!(ok_or(true, function_with_side_effects()).is_ok());
        assert!(ok_or(false, function_with_side_effects()).is_err());

        // `a` is incremented twice because the value passed to `ok_or` is
        // evaluated eagerly.
        assert_eq!(a, 2);
    }
}
