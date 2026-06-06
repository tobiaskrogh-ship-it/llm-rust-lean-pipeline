//! Extracted from `core::alloc::Layout::array` (src/alloc/layout.rs:480).
//!
//! Monomorphized to element type `u64`: `T::LAYOUT` becomes a fixed element
//! size of 8 and alignment of 8 (`size_of::<u64>()` / `align_of::<u64>()`).
//! The `inner` closure and the private helper `max_size_for_align` are inlined;
//! `from_size_align_unchecked` becomes a plain struct construction; the
//! `unchecked_mul`/`unchecked_sub` intrinsics become `*`/`-` (the preceding
//! bound guarantees they cannot overflow).

/// Layout of a block of memory: a size and a power-of-two alignment.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Layout {
    size: usize,
    align: usize,
}

impl Layout {
    pub fn size(&self) -> usize {
        self.size
    }
    pub fn align(&self) -> usize {
        self.align
    }
}

/// Returned on arithmetic overflow or when the total size would exceed
/// `isize::MAX`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LayoutError;

/// Creates a layout describing the record for a `[u64; n]`.
pub fn array_u64(n: usize) -> Result<Layout, LayoutError> {
    // `u64::LAYOUT`: size_of::<u64>() == 8, align_of::<u64>() == 8.
    let element_size: usize = 8;
    let align: usize = 8;

    // We need to check that the total size won't overflow a `usize` and that it
    // still fits in an `isize`. Division checks both with a single threshold.
    if element_size != 0 && n > max_size_for_align(align) / element_size {
        return Err(LayoutError);
    }

    // We just checked that we won't overflow `usize` when we multiply.
    let array_size = element_size * n;

    // `array_size` will not exceed `isize::MAX` even when rounded up to the
    // alignment, and `align` is a power of two.
    Ok(Layout { size: array_size, align })
}

// Inlined from `Layout::max_size_for_align` (src/alloc/layout.rs:78).
fn max_size_for_align(align: usize) -> usize {
    // `isize::MAX = 2^63 - 1 = 9_223_372_036_854_775_807` (Hax models isize as
    // 64-bit). Inlining the literal avoids the missing
    // `core_models.num.Impl_5.MAX` identifier in the Hax Lean prelude.
    (9_223_372_036_854_775_807usize + 1) - align
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from `tests/alloc.rs::layout_array_edge_cases`,
    // monomorphized to the `for_type::<T>()` case with `size_of::<T>() == 8`
    // (e.g. `i64`/`u64`). The `()` ZST case and the `[i32; _]`/`[u8; _]`
    // cases are dropped: they require different element-type monomorphizations
    // than `u64`.
    #[test]
    fn layout_array_edge_cases() {
        const MAX_SIZE: usize = isize::MAX as usize;
        const ELEM: usize = 8; // size_of::<u64>()

        let edge = (MAX_SIZE + 1) / ELEM;
        let low = edge.saturating_sub(10);
        let high = edge.saturating_add(10);
        assert!(array_u64(low).is_ok());
        assert!(array_u64(high).is_err());
        for n in low..=high {
            assert_eq!(array_u64(n).is_ok(), n * ELEM <= MAX_SIZE);
        }
    }

    #[test]
    fn basic_cases() {
        assert_eq!(array_u64(0).unwrap(), Layout { size: 0, align: 8 });
        assert_eq!(array_u64(3).unwrap(), Layout { size: 24, align: 8 });
    }

    // Largest `n` accepted by the contract: `8 * n <= isize::MAX`.
    // Derived independently of the implementation's own threshold formula
    // (`isize::MAX / 8`, used only to pick sample points); the boundary
    // itself is asserted via `byte_size_fits` below.
    const THRESHOLD: usize = (isize::MAX as usize) / 8;

    // Independent characterisation of the success condition: the record for
    // `[u64; n]` is constructible iff its total byte size fits in `isize::MAX`.
    fn byte_size_fits(n: usize) -> bool {
        (n as u128) * 8 <= isize::MAX as u128
    }

    // POSTCONDITION: whenever the call succeeds, the layout is exactly
    // `{ size: 8*n, align: 8 }`. `size == 8*n` (output/input relation) and
    // `align == 8` (constant alignment) are independent claims — a buggy
    // implementation could satisfy one and violate the other.
    #[test]
    fn prop_success_yields_size_8n_and_align_8() {
        let samples: [usize; 11] = [
            0, 1, 2, 3, 100, 1_000,
            1 << 20, 1 << 40, 1 << 55,
            THRESHOLD - 1, THRESHOLD,
        ];
        for &n in &samples {
            let layout = array_u64(n).expect("n is within the valid range");
            assert_eq!(layout.size(), 8 * n, "size must be 8*n for n={n}");
            assert_eq!(layout.align(), 8, "align must always be 8 for n={n}");
        }
    }

    // FAILURE CONDITION: inputs whose byte size would exceed `isize::MAX`
    // are rejected with `LayoutError`, and the call never panics (the guarded
    // multiplication does not overflow even for `usize::MAX`).
    #[test]
    fn prop_overflow_inputs_yield_error() {
        let samples: [usize; 7] = [
            THRESHOLD + 1, THRESHOLD + 2,
            1 << 61, 1 << 62, 1 << 63,
            usize::MAX - 1, usize::MAX,
        ];
        for &n in &samples {
            assert_eq!(array_u64(n), Err(LayoutError), "n={n} must overflow");
        }
    }

    // EXACT BOUNDARY: the call succeeds iff the total byte size `8*n` fits in
    // `isize::MAX`. Straddles the threshold one element at a time and also
    // checks the extreme inputs, so an off-by-one in the cutoff is caught.
    #[test]
    fn prop_ok_iff_byte_size_fits_isize_max() {
        for delta in 0..=64usize {
            let lo = THRESHOLD - delta;
            assert_eq!(array_u64(lo).is_ok(), byte_size_fits(lo), "n={lo}");
            let hi = THRESHOLD + delta;
            assert_eq!(array_u64(hi).is_ok(), byte_size_fits(hi), "n={hi}");
        }
        for &n in &[0usize, 1, usize::MAX / 2, usize::MAX - 1, usize::MAX] {
            assert_eq!(array_u64(n).is_ok(), byte_size_fits(n), "n={n}");
        }
    }
}
