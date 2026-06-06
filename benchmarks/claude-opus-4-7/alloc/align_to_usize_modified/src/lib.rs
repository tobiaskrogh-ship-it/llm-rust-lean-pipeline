//! Extracted from `core::alloc::Layout::align_to` (src/alloc/layout.rs:244).
//!
//! `Layout` is modeled as `{ size: usize, align: usize }`. `Alignment::new`
//! becomes `usize::is_power_of_two`; `Alignment::max` becomes `usize::max`. The
//! private helper `from_size_alignment` (and the `max_size_for_align` it calls)
//! is inlined; `unchecked_sub` → `-`.

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

/// Returned when the requested alignment is invalid or the resulting layout
/// would overflow `isize`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LayoutError;

/// Creates a layout describing a record that has the same layout as `layout`
/// but is aligned to at least `align` bytes.
pub fn align_to(layout: Layout, align: usize) -> Result<Layout, LayoutError> {
    if is_power_of_two_usize(align) {
        // Inlined `usize::max`: `Ord::max` (extracted to the undefined
        // `core_models.cmp.Ord.max`) returns the larger value, and the
        // second argument on a tie — matched exactly here.
        let new_align = if layout.align > align {
            layout.align
        } else {
            align
        };
        from_size_alignment(layout.size, new_align)
    } else {
        Err(LayoutError)
    }
}

// Inlined `usize::is_power_of_two` (extracts to the undefined
// `core_models.num.Impl_11.is_power_of_two` in the Hax Lean prelude). A
// value is a power of two iff it is non-zero and has exactly one bit set;
// `x & (x - 1) == 0` clears the lowest set bit, and the `x != 0`
// short-circuit guards the `x - 1` subtraction.
fn is_power_of_two_usize(x: usize) -> bool {
    x != 0 && (x & (x - 1)) == 0
}

// Inlined from `Layout::from_size_alignment` (src/alloc/layout.rs:101).
fn from_size_alignment(size: usize, align: usize) -> Result<Layout, LayoutError> {
    if size > max_size_for_align(align) {
        return Err(LayoutError);
    }
    Ok(Layout { size, align })
}

// Inlined from `Layout::max_size_for_align` (src/alloc/layout.rs:78).
// `isize::MAX` is an associated constant on a primitive integer type; it
// extracts to the undefined `core_models.num.Impl_5.MAX`. On 64-bit
// targets `isize::MAX as usize + 1 == 2^63 == 9_223_372_036_854_775_808`,
// so the literal is substituted. This matches the test helper
// `spec_max_size_for_align`, which evaluates to the same value on this
// target.
fn max_size_for_align(align: usize) -> usize {
    9_223_372_036_854_775_808usize - align
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from the `align_to` assertions of
    // `tests/alloc.rs::layout_errors`. `Layout::new::<[u8; 2]>()` has size 2,
    // align 1.
    #[test]
    fn layout_errors() {
        let layout = Layout { size: 2, align: 1 };

        // Should error if the alignment is not a power of two.
        assert!(align_to(layout, 3).is_err());

        // Errors on arithmetic overflow as the alignment cannot overflow `isize`.
        let size_max = isize::MAX as usize;
        assert!(align_to(layout, size_max + 1).is_err());
    }

    #[test]
    fn raises_alignment() {
        let layout = Layout { size: 2, align: 1 };
        assert_eq!(
            align_to(layout, 4).unwrap(),
            Layout { size: 2, align: 4 }
        );
        // Already sufficiently aligned: alignment is unchanged.
        let layout = Layout { size: 16, align: 8 };
        assert_eq!(align_to(layout, 4).unwrap(), Layout { size: 16, align: 8 });
    }

    // ---------------------------------------------------------------------
    // Property-based tests.
    //
    // No external proptest/quickcheck dependency is available, so the
    // properties are driven by a small deterministic xorshift PRNG plus
    // explicit boundary cases. `Layout` always carries a power-of-two
    // alignment (the type invariant in the original `core` code), so
    // every generated layout respects that.
    // ---------------------------------------------------------------------

    struct Rng(u64);

    impl Rng {
        fn next_u64(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
    }

    /// The contract's size bound, stated independently of the
    /// implementation helper: a layout with alignment `align` is valid
    /// iff its size is at most this value.
    fn spec_max_size_for_align(align: usize) -> usize {
        (isize::MAX as usize + 1) - align
    }

    /// A power-of-two `usize` (the `Layout` alignment invariant): one of
    /// `1, 2, 4, ..., 2^(usize::BITS - 1)`.
    fn gen_pow2(rng: &mut Rng) -> usize {
        let shift = (rng.next_u64() % usize::BITS as u64) as u32;
        1usize << shift
    }

    // Precondition on `align`: `align_to` may only succeed when `align`
    // is a power of two. For every non-power-of-two `align` (0 included)
    // the result is `Err`, regardless of the layout.
    #[test]
    fn prop_non_power_of_two_align_is_error() {
        for &align in &[0usize, 3, 6, 7, 100, usize::MAX] {
            let layout = Layout { size: 12345, align: 8 };
            assert!(align_to(layout, align).is_err());
        }

        let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
        for _ in 0..2000 {
            let align = rng.next_u64() as usize;
            if align.is_power_of_two() {
                continue;
            }
            let layout = Layout {
                size: rng.next_u64() as usize,
                align: gen_pow2(&mut rng),
            };
            assert!(
                align_to(layout, align).is_err(),
                "non-power-of-two align {align} must error"
            );
        }
    }

    // Postcondition: when `align` is a power of two and the size fits
    // (`size <= spec_max_size_for_align(max(layout.align, align))`), the
    // result is `Ok` with the size unchanged and the alignment raised to
    // exactly `max(layout.align, align)`.
    #[test]
    fn prop_valid_inputs_preserve_size_and_raise_alignment() {
        let mut rng = Rng(0xDEAD_BEEF_CAFE_F00D);
        for _ in 0..3000 {
            let layout_align = gen_pow2(&mut rng);
            let align = gen_pow2(&mut rng);
            let new_align = layout_align.max(align);
            let max_size = spec_max_size_for_align(new_align);

            // Sizes inside [0, max_size], biased to also hit 0 and the
            // exact upper boundary.
            let size = match rng.next_u64() % 3 {
                0 => 0,
                1 => max_size,
                _ => (rng.next_u64() as usize) % (max_size + 1),
            };

            let layout = Layout { size, align: layout_align };
            assert_eq!(
                align_to(layout, align),
                Ok(Layout { size, align: new_align }),
            );
        }
    }

    // Failure condition: when `align` is a power of two but the size
    // exceeds `spec_max_size_for_align(max(layout.align, align))`, the
    // result is `Err` (the `isize` overflow case).
    #[test]
    fn prop_size_overflow_is_error() {
        let mut rng = Rng(0x0123_4567_89AB_CDEF);
        for _ in 0..3000 {
            let layout_align = gen_pow2(&mut rng);
            let align = gen_pow2(&mut rng);
            let new_align = layout_align.max(align);
            let max_size = spec_max_size_for_align(new_align);

            // Sizes inside [max_size + 1, usize::MAX]; this range is
            // always non-empty since max_size <= 2^(usize::BITS-1) - 1.
            let span = usize::MAX - max_size; // >= 1
            let size = match rng.next_u64() % 3 {
                0 => max_size + 1,
                1 => usize::MAX,
                _ => max_size + 1 + (rng.next_u64() as usize) % span,
            };

            let layout = Layout { size, align: layout_align };
            assert!(
                align_to(layout, align).is_err(),
                "size {size} > max {max_size} for align {new_align} must error"
            );
        }
    }
}
