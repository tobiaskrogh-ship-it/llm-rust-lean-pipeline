//! Extracted from `core::array::<[T; N]>::split_array_ref` (src/array/mod.rs:737),
//! monomorphized to `u64`. The inherent method `(&self) -> (&[T; M], &[T])` is
//! rewritten as a free function over a `&[u64; N]`.
//!
//! The original calls `self.split_first_chunk::<M>().unwrap()`. The private
//! slice helper `split_first_chunk` (src/slice/mod.rs:387) is inlined here.
//! Its body uses an unstable raw-pointer cast (`first.as_ptr().cast_array()`);
//! since `first.len() == M` on the `Some` path, that is equivalent to the
//! stable `TryFrom<&[T]> for &[T; M]` conversion, which is used instead so the
//! crate is self-contained on stable.

/// Returns an array reference to the first `M` items in the slice and the
/// remaining slice. Returns `None` if the slice is shorter than `M`.
fn split_first_chunk<const M: usize>(s: &[u64]) -> Option<(&[u64; M], &[u64])> {
    let Some((first, tail)) = s.split_at_checked(M) else { return None };
    // SAFETY-equivalent: `first.len() == M`, so the conversion succeeds.
    Some((first.try_into().unwrap(), tail))
}

/// Divides one array reference into two at an index.
///
/// The first will contain all indices from `[0, M)` and the second will
/// contain all indices from `[M, N)`.
///
/// # Panics
///
/// Panics if `M > N`.
#[inline]
pub fn split_array_ref<const M: usize, const N: usize>(a: &[u64; N]) -> (&[u64; M], &[u64]) {
    split_first_chunk::<M>(a).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from the doc-test on `split_array_ref` (src/array/mod.rs),
    // monomorphized to `u64`, call site rewritten to the free function.
    #[test]
    fn doctest_split_array_ref() {
        let v: [u64; 6] = [1, 2, 3, 4, 5, 6];

        {
            let (left, right) = split_array_ref::<0, 6>(&v);
            assert_eq!(left, &[]);
            assert_eq!(right, &[1, 2, 3, 4, 5, 6]);
        }

        {
            let (left, right) = split_array_ref::<2, 6>(&v);
            assert_eq!(left, &[1, 2]);
            assert_eq!(right, &[3, 4, 5, 6]);
        }

        {
            let (left, right) = split_array_ref::<6, 6>(&v);
            assert_eq!(left, &[1, 2, 3, 4, 5, 6]);
            assert_eq!(right, &[]);
        }
    }

    // Transferred from core's `tests/array.rs::array_split_array_ref_out_of_bounds`.
    #[test]
    #[should_panic]
    fn array_split_array_ref_out_of_bounds() {
        let v: [u64; 6] = [1, 2, 3, 4, 5, 6];

        split_array_ref::<7, 6>(&v);
    }

    // --- Property-based tests -------------------------------------------------

    // Deterministic LCG so the property is checked over many varied inputs
    // without a `proptest` dependency (downstream this becomes a Lean
    // proof obligation, so the body must stay extractable).
    fn next(state: &mut u64) -> u64 {
        *state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        *state
    }

    /// The full postcondition contract for a valid call (`M <= N`):
    ///
    /// 1. `left` is exactly the first `M` elements of `a`, in order.
    /// 2. `right` is exactly the remaining `N - M` elements of `a`, in order.
    ///
    /// These are independent claims: a split at the wrong index, or a
    /// reordering, satisfies neither vacuously — clause 1 pins the left
    /// boundary, clause 2 pins the right boundary, and together they force
    /// the split to be contiguous, order-preserving, and exactly at `M`.
    fn prop_split_contract<const M: usize, const N: usize>(a: &[u64; N]) {
        let (left, right) = split_array_ref::<M, N>(a);

        // Postcondition 1: left half is the first M elements (in order).
        assert_eq!(left.len(), M);
        assert_eq!(&left[..], &a[..M]);

        // Postcondition 2: right half is the trailing N - M elements (in order).
        assert_eq!(right.len(), N - M);
        assert_eq!(right, &a[M..]);
    }

    // Interior split (0 < M < N) over many randomized contents. Distinct,
    // varied element values mean any off-by-one in the split index or any
    // reordering would be caught.
    #[test]
    fn prop_split_array_ref_interior() {
        let mut state = 0x1234_5678_9abc_def0u64;
        for _ in 0..1000 {
            let mut a = [0u64; 8];
            for slot in a.iter_mut() {
                *slot = next(&mut state);
            }
            prop_split_contract::<3, 8>(&a);
        }
    }

    // Boundary instantiation M == 0: left is always empty, right is all of `a`.
    #[test]
    fn prop_split_array_ref_empty_left() {
        let mut state = 0x0fed_cba9_8765_4321u64;
        for _ in 0..1000 {
            let mut a = [0u64; 8];
            for slot in a.iter_mut() {
                *slot = next(&mut state);
            }
            prop_split_contract::<0, 8>(&a);
        }
    }

    // Boundary instantiation M == N: left is all of `a`, right is empty.
    #[test]
    fn prop_split_array_ref_empty_right() {
        let mut state = 0xdead_beef_cafe_babeu64;
        for _ in 0..1000 {
            let mut a = [0u64; 8];
            for slot in a.iter_mut() {
                *slot = next(&mut state);
            }
            prop_split_contract::<8, 8>(&a);
        }
    }
}
