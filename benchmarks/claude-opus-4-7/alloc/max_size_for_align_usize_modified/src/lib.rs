//! Extracted from `core::alloc::Layout::max_size_for_align` (src/alloc/layout.rs:78).
//!
//! Monomorphized to `usize`. The original uses the `unchecked_sub` intrinsic;
//! since the maximum possible alignment is `isize::MAX + 1`, the subtraction
//! cannot overflow, so it is rewritten as plain `-`.

/// Returns the largest size allowed for a memory block with the given
/// power-of-two alignment.
pub fn max_size_for_align(align: usize) -> usize {
    // Rounded up size is:
    //   size_rounded_up = (size + align - 1) & !(align - 1);
    //
    // Checking for summation overflow is both necessary and sufficient.
    //
    // The maximum possible alignment is `isize::MAX + 1`, so the subtraction
    // cannot overflow.
    //
    // `isize::MAX as usize` extracts to `core_models.num.Impl_5.MAX`, which
    // the Hax Lean prelude does not define. On the 64-bit target this crate
    // targets, `isize::MAX = 2^63 - 1 = 9_223_372_036_854_775_807`; the
    // literal is inlined to avoid the missing identifier (semantics
    // unchanged: `+ 1` still yields `2^63`, the largest legal alignment).
    (9_223_372_036_854_775_807usize + 1) - align
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Upper bound of the valid input domain: the largest legal alignment is
    /// `isize::MAX + 1` (which is `1 << 63` on a 64-bit target).
    const MAX_ALIGN: usize = isize::MAX as usize + 1;

    /// Postcondition over the entire valid input domain.
    ///
    /// The precondition is that `align` is a power of two no greater than
    /// `MAX_ALIGN`. Exhaustively over every such alignment (all 64 powers of
    /// two, `1 << 0` .. `1 << 63`), the result is exactly
    /// `(isize::MAX + 1) - align`. The final iteration (`shift == 63`,
    /// `align == MAX_ALIGN`) also pins the contractual boundary case where the
    /// maximum alignment leaves no room: the result is `0`.
    #[test]
    fn postcondition_formula_over_valid_alignments() {
        for shift in 0..usize::BITS {
            let align = 1_usize << shift;
            assert_eq!(max_size_for_align(align), MAX_ALIGN - align);
        }
    }

    /// Failure condition / precondition boundary.
    ///
    /// `MAX_ALIGN + 1` is the first value past the valid domain; the internal
    /// subtraction underflows, so the function must panic (debug overflow
    /// check). This pins that the contract only holds for `align <= MAX_ALIGN`.
    #[test]
    #[should_panic]
    fn panics_when_align_exceeds_max() {
        let _ = max_size_for_align(MAX_ALIGN + 1);
    }
}
