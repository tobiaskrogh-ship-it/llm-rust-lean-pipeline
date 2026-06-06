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
    use proptest::prelude::*;

    // Transferred from the second doc-test of `bool::then_some` (eager-evaluation).
    // The source's closure returns `()`; monomorphized here to return `u64`.
    // Kept as a plain `#[test]` because it pins down Rust evaluation order,
    // which is orthogonal to the value-level contract captured by the
    // property tests below.
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

    proptest! {
        /// Postcondition (true branch): when `b == true`, the result is
        /// `Some(t)` — i.e., the payload is preserved exactly. A buggy
        /// implementation that returned `Some(t.wrapping_add(1))`, `Some(0)`,
        /// or any other transformed value would be caught.
        #[test]
        fn then_some_true_preserves_value(t: u64) {
            prop_assert_eq!(then_some(true, t), Some(t));
        }

        /// Postcondition (false branch): when `b == false`, the result is
        /// `None`, regardless of `t`. A buggy implementation that swapped
        /// the branches, or that returned `Some(t)` for specific `t`, would
        /// be caught.
        #[test]
        fn then_some_false_is_none(t: u64) {
            prop_assert_eq!(then_some(false, t), None);
        }
    }
}
