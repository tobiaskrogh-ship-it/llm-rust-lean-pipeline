//! Extracted from `core::bool` — inlined `bool::then_some`, monomorphized to `u64`.

/// Returns `Some(t)` if `b` is `true`, or `None` otherwise.
///
/// Arguments passed to `then_some` are eagerly evaluated; if you are
/// passing the result of a function call, it is recommended to use
/// `then`, which is lazily evaluated.
#[inline]
pub fn then_some(b: bool, t: u64) -> Option<u64> {
    if b { Some(t) } else { None }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from the first doc-test of `bool::then_some`.
    #[test]
    fn then_some_basic() {
        assert_eq!(then_some(false, 0u64), None);
        assert_eq!(then_some(true, 0u64), Some(0u64));
    }

    // Transferred from the second doc-test of `bool::then_some` (eager-evaluation).
    // The source's closure returns `()`; monomorphized here to return `u64`.
    #[test]
    fn then_some_eager() {
        let mut a = 0u64;
        let mut function_with_side_effects = || {
            a += 1;
            0u64
        };

        then_some(true, function_with_side_effects());
        then_some(false, function_with_side_effects());

        // `a` is incremented twice because the value passed to `then_some` is
        // evaluated eagerly.
        assert_eq!(a, 2);
    }
}
