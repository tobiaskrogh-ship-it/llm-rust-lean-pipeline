//! Extracted from `core::alloc::Layout::padding_needed_for`
//! (src/alloc/layout.rs:272).
//!
//! Monomorphized to `usize`. `self.size()` is passed as `size`. `Alignment::new`
//! becomes `usize::is_power_of_two` (returning `usize::MAX` when not a power of
//! two, as the original returns when `Alignment::new` is `None`). The private
//! helper `size_rounded_up_to_custom_align` is inlined; `unchecked_sub` → `-`.

// `usize::is_power_of_two()` extracts to an unmodeled
// `core_models.num.Impl_11.is_power_of_two` identifier in the Hax Lean
// prelude. Inline the standard bit-twiddling check using primitives that
// Hax does model (`!=`, `&`, `-`, `==`).
fn is_power_of_two_usize(x: usize) -> bool {
    x != 0 && (x & (x - 1)) == 0
}

/// Returns the amount of padding that must be inserted after a block of size
/// `size` so that the following address satisfies `align`.
///
/// The return value has no meaning if `align` is not a power of two
/// (`usize::MAX` is returned in that case).
pub fn padding_needed_for(size: usize, align: usize) -> usize {
    // `Alignment::new(align)` is `None` unless `align` is a power of two.
    if !is_power_of_two_usize(align) {
        // `usize::MAX` on 64-bit = 2^64 - 1 = 18_446_744_073_709_551_615.
        // Inlining the literal avoids the missing
        // `core_models.num.Impl_11.MAX` identifier in the Hax Lean prelude.
        return 18_446_744_073_709_551_615usize;
    }
    let len_rounded_up = size_rounded_up_to_custom_align(size, align);
    // Cannot overflow because the rounded-up value is never less than `size`.
    len_rounded_up - size
}

// Inlined from `Layout::size_rounded_up_to_custom_align` (src/alloc/layout.rs:285).
fn size_rounded_up_to_custom_align(size: usize, align: usize) -> usize {
    let align_m1 = align - 1;
    (size + align_m1) & !align_m1
}

#[cfg(test)]
mod tests {
    use super::*;

    // Concrete anchor from the doc comment: the padding after a block of
    // size 9 for alignment 4 is 3.
    #[test]
    fn doc_example() {
        assert_eq!(padding_needed_for(9, 4), 3);
    }

    // Failure / special-case clause: when `align` is not a power of two
    // (this includes `align == 0`), the function returns `usize::MAX`
    // regardless of `size`.
    #[test]
    fn prop_non_power_of_two_returns_max() {
        for align in 0usize..256 {
            if !align.is_power_of_two() {
                for size in 0usize..256 {
                    assert_eq!(padding_needed_for(size, align), usize::MAX);
                }
            }
        }
    }

    // Postcondition clause A: for a power-of-two `align`, `size + result`
    // is a multiple of `align` — i.e. the result rounds `size` up so the
    // following address is aligned. (`size` kept small so `size + align - 1`
    // cannot overflow, which is the function's implicit precondition.)
    #[test]
    fn prop_result_aligns_size_up() {
        for k in 0u32..16 {
            let align = 1usize << k;
            for size in 0usize..1000 {
                let p = padding_needed_for(size, align);
                assert_eq!((size + p) % align, 0);
            }
        }
    }

    // Postcondition clause B: the padding is the *smallest* value with that
    // property, i.e. strictly less than `align`. Independent of clause A:
    // together they uniquely pin down the result (a result that overshoots
    // by a whole `align` block still satisfies A but fails B).
    #[test]
    fn prop_padding_is_minimal() {
        for k in 0u32..16 {
            let align = 1usize << k;
            for size in 0usize..1000 {
                let p = padding_needed_for(size, align);
                assert!(p < align);
            }
        }
    }
}
