//! Extracted from `core::array::<[T; N]>::rsplit_array_mut` (src/array/mod.rs:848),
//! monomorphized to `u64`. The inherent method `(&mut self) -> (&mut [T], &mut [T; M])`
//! is rewritten as a free function over a `&mut [u64; N]`.
//!
//! The original calls `self.split_last_chunk_mut::<M>().unwrap()`. The private
//! slice helper `split_last_chunk_mut` (src/slice/mod.rs:478) is inlined here.
//! Its body uses an unstable raw-pointer cast (`last.as_mut_ptr().cast_array()`);
//! since `last.len() == M` on the `Some` path, that is equivalent to the
//! stable `TryFrom<&mut [T]> for &mut [T; M]` conversion, which is used instead.

/// Returns the remaining slice and a mutable array reference to the last `M`
/// items. Returns `None` if the slice is shorter than `M`.
fn split_last_chunk_mut<const M: usize>(s: &mut [u64]) -> Option<(&mut [u64], &mut [u64; M])> {
    let Some(index) = s.len().checked_sub(M) else { return None };
    let (init, last) = s.split_at_mut(index);
    // SAFETY-equivalent: `last.len() == M`, so the conversion succeeds.
    Some((init, last.try_into().unwrap()))
}

/// Divides one mutable array reference into two at an index from the end.
///
/// The first will contain all indices from `[0, N - M)` and the second will
/// contain all indices from `[N - M, N)`.
///
/// # Panics
///
/// Panics if `M > N`.
#[inline]
pub fn rsplit_array_mut<const M: usize, const N: usize>(
    a: &mut [u64; N],
) -> (&mut [u64], &mut [u64; M]) {
    split_last_chunk_mut::<M>(a).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from the doc-test on `rsplit_array_mut` (src/array/mod.rs),
    // monomorphized to `u64`, call site rewritten to the free function.
    #[test]
    fn doctest_rsplit_array_mut() {
        let mut v: [u64; 6] = [1, 0, 3, 0, 5, 6];
        let (left, right) = rsplit_array_mut::<4, 6>(&mut v);
        assert_eq!(left, &mut [1, 0]);
        assert_eq!(right, &mut [3, 0, 5, 6][..]);
        left[1] = 2;
        right[1] = 4;
        assert_eq!(v, [1, 2, 3, 4, 5, 6]);
    }

    // Transferred from core's `tests/array.rs::array_rsplit_array_mut`,
    // monomorphized to `u64`.
    #[test]
    fn array_rsplit_array_mut() {
        let mut v: [u64; 6] = [1, 2, 3, 4, 5, 6];

        {
            let (left, right) = rsplit_array_mut::<0, 6>(&mut v);
            assert_eq!(left, &mut [1, 2, 3, 4, 5, 6]);
            assert_eq!(right, &mut []);
        }

        {
            let (left, right) = rsplit_array_mut::<6, 6>(&mut v);
            assert_eq!(left, &mut []);
            assert_eq!(right, &mut [1, 2, 3, 4, 5, 6]);
        }
    }

    // Transferred from core's `tests/array.rs::array_rsplit_array_mut_out_of_bounds`.
    #[test]
    #[should_panic]
    fn array_rsplit_array_mut_out_of_bounds() {
        let mut v: [u64; 6] = [1, 2, 3, 4, 5, 6];

        rsplit_array_mut::<7, 6>(&mut v);
    }

    // --- Property-based tests -------------------------------------------
    //
    // `M` and `N` are const generics, so they cannot be randomized; only the
    // array data can. We fix a representative *middle* split (M = 4, N = 9 —
    // neither the `M == 0` nor `M == N` boundary, neither covered by the
    // transferred unit tests) and randomize the contents over many runs.

    // Deterministic splitmix64 PRNG: no external dependency, fully
    // reproducible, adequate for exercising the data path.
    fn next_rand(state: &mut u64) -> u64 {
        *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = *state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    // Postcondition (split location + content/order): for `M <= N`, `left` is
    // exactly the prefix `a[0 .. N-M]` and `right` is exactly the suffix
    // `a[N-M .. N]`, element-for-element in order. A buggy implementation
    // with an off-by-one split index, that splits from the front instead of
    // the end, or that reorders/corrupts elements, is caught here.
    #[test]
    fn prop_split_is_prefix_and_suffix() {
        const M: usize = 4;
        const N: usize = 9;
        let mut state: u64 = 0x1234_5678_9ABC_DEF0;
        for _ in 0..512 {
            let mut a = [0u64; N];
            for slot in a.iter_mut() {
                *slot = next_rand(&mut state);
            }
            let original = a;

            let (left, right) = rsplit_array_mut::<M, N>(&mut a);

            assert_eq!(left.len(), N - M);
            assert_eq!(right.len(), M);
            for i in 0..N - M {
                assert_eq!(left[i], original[i]);
            }
            for i in 0..M {
                assert_eq!(right[i], original[N - M + i]);
            }
        }
    }

    // Postcondition (mutable aliasing + partition): the returned references
    // mutably alias the *original* storage. Writing through every `left[i]`
    // and every `right[i]` updates exactly the original elements once each
    // (the two views partition `[0, N)` with no gap or overlap). A buggy
    // implementation that splits a copy, or maps the suffix to the wrong
    // base offset (so some index is written twice and another not at all),
    // is caught here.
    #[test]
    fn prop_writes_alias_and_partition_original() {
        const M: usize = 4;
        const N: usize = 9;
        let mut state: u64 = 0x0FED_CBA9_8765_4321;
        for _ in 0..512 {
            let mut a = [0u64; N];
            for slot in a.iter_mut() {
                *slot = next_rand(&mut state);
            }
            let mut expected = a;
            for v in expected.iter_mut() {
                *v = v.wrapping_add(1);
            }

            {
                let (left, right) = rsplit_array_mut::<M, N>(&mut a);
                for i in 0..N - M {
                    left[i] = left[i].wrapping_add(1);
                }
                for i in 0..M {
                    right[i] = right[i].wrapping_add(1);
                }
            }

            assert_eq!(a, expected);
        }
    }
}
