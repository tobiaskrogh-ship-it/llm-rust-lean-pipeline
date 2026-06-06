//! Extracted from `core::array::<[T; N]>::split_array_mut` (src/array/mod.rs:770),
//! monomorphized to `u64`. The inherent method `(&mut self) -> (&mut [T; M], &mut [T])`
//! is rewritten as a free function over a `&mut [u64; N]`.
//!
//! The original calls `self.split_first_chunk_mut::<M>().unwrap()`. The private
//! slice helper `split_first_chunk_mut` (src/slice/mod.rs:417) is inlined here.
//! Its body uses an unstable raw-pointer cast (`first.as_mut_ptr().cast_array()`);
//! since `first.len() == M` on the `Some` path, that is equivalent to the
//! stable `TryFrom<&mut [T]> for &mut [T; M]` conversion, which is used instead.

/// Returns a mutable array reference to the first `M` items in the slice and
/// the remaining slice. Returns `None` if the slice is shorter than `M`.
fn split_first_chunk_mut<const M: usize>(s: &mut [u64]) -> Option<(&mut [u64; M], &mut [u64])> {
    let Some((first, tail)) = s.split_at_mut_checked(M) else { return None };
    // SAFETY-equivalent: `first.len() == M`, so the conversion succeeds.
    Some((first.try_into().unwrap(), tail))
}

/// Divides one mutable array reference into two at an index.
///
/// The first will contain all indices from `[0, M)` and the second will
/// contain all indices from `[M, N)`.
///
/// # Panics
///
/// Panics if `M > N`.
#[inline]
pub fn split_array_mut<const M: usize, const N: usize>(
    a: &mut [u64; N],
) -> (&mut [u64; M], &mut [u64]) {
    split_first_chunk_mut::<M>(a).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from the doc-test on `split_array_mut` (src/array/mod.rs),
    // monomorphized to `u64`, call site rewritten to the free function.
    #[test]
    fn doctest_split_array_mut() {
        let mut v: [u64; 6] = [1, 0, 3, 0, 5, 6];
        let (left, right) = split_array_mut::<2, 6>(&mut v);
        assert_eq!(left, &mut [1, 0][..]);
        assert_eq!(right, &mut [3, 0, 5, 6]);
        left[1] = 2;
        right[1] = 4;
        assert_eq!(v, [1, 2, 3, 4, 5, 6]);
    }

    // Transferred from core's `tests/array.rs::array_split_array_mut`,
    // monomorphized to `u64`.
    #[test]
    fn array_split_array_mut() {
        let mut v: [u64; 6] = [1, 2, 3, 4, 5, 6];

        {
            let (left, right) = split_array_mut::<0, 6>(&mut v);
            assert_eq!(left, &mut []);
            assert_eq!(right, &mut [1, 2, 3, 4, 5, 6]);
        }

        {
            let (left, right) = split_array_mut::<6, 6>(&mut v);
            assert_eq!(left, &mut [1, 2, 3, 4, 5, 6]);
            assert_eq!(right, &mut []);
        }
    }

    // Transferred from core's `tests/array.rs::array_split_array_mut_out_of_bounds`.
    #[test]
    #[should_panic]
    fn array_split_array_mut_out_of_bounds() {
        let mut v: [u64; 6] = [1, 2, 3, 4, 5, 6];

        split_array_mut::<7, 6>(&mut v);
    }

    // ---- Property-based tests -------------------------------------------
    //
    // `M` and `N` are compile-time const generics, so they are fixed per
    // instantiation; the *contents* of the input array are randomized with a
    // small deterministic LCG. Each generic helper is exercised over many
    // random arrays for several representative `(M, N)` pairs, including the
    // boundary cases `M == 0` and `M == N`.

    fn lcg(state: &mut u64) -> u64 {
        // Knuth MMIX LCG constants; deterministic and reproducible.
        *state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        *state
    }

    fn random_array<const N: usize>(state: &mut u64) -> [u64; N] {
        let mut a = [0u64; N];
        for slot in a.iter_mut() {
            *slot = lcg(state);
        }
        a
    }

    // Postcondition (valid call, `M <= N`): the result partitions the input.
    // `left` is exactly the first `M` elements and `right` is exactly the
    // remaining `N - M` elements, in order. A buggy implementation that split
    // at the wrong index, reordered, or dropped/duplicated elements would be
    // caught here.
    fn check_prefix_suffix<const M: usize, const N: usize>(orig: [u64; N]) {
        let mut v = orig;
        let (left, right) = split_array_mut::<M, N>(&mut v);
        assert_eq!(&left[..], &orig[..M]);
        assert_eq!(&right[..], &orig[M..]);
    }

    // Postcondition (valid call): the returned references are *live, disjoint
    // mutable views* into the original storage, with index map `left[i] ->
    // a[i]` and `right[j] -> a[M + j]`. This is independent of the
    // prefix/suffix claim: an implementation returning copies, or aliasing the
    // wrong region, would pass `check_prefix_suffix` but fail here.
    fn check_mutation_aliasing<const M: usize, const N: usize>(orig: [u64; N]) {
        let mut v = orig;
        {
            let (left, right) = split_array_mut::<M, N>(&mut v);
            for i in 0..M {
                left[i] = left[i].wrapping_add(1);
            }
            for j in 0..(N - M) {
                right[j] = right[j].wrapping_sub(1);
            }
        }
        for i in 0..M {
            assert_eq!(v[i], orig[i].wrapping_add(1));
        }
        for j in 0..(N - M) {
            assert_eq!(v[M + j], orig[M + j].wrapping_sub(1));
        }
    }

    #[test]
    fn prop_prefix_suffix() {
        let mut state: u64 = 0x1234_5678_9abc_def0;
        for _ in 0..256 {
            check_prefix_suffix::<0, 6>(random_array(&mut state));
            check_prefix_suffix::<1, 6>(random_array(&mut state));
            check_prefix_suffix::<3, 6>(random_array(&mut state));
            check_prefix_suffix::<6, 6>(random_array(&mut state));
            check_prefix_suffix::<2, 5>(random_array(&mut state));
            check_prefix_suffix::<5, 8>(random_array(&mut state));
        }
    }

    #[test]
    fn prop_mutation_aliasing() {
        let mut state: u64 = 0x0fed_cba9_8765_4321;
        for _ in 0..256 {
            check_mutation_aliasing::<0, 6>(random_array(&mut state));
            check_mutation_aliasing::<1, 6>(random_array(&mut state));
            check_mutation_aliasing::<3, 6>(random_array(&mut state));
            check_mutation_aliasing::<6, 6>(random_array(&mut state));
            check_mutation_aliasing::<2, 5>(random_array(&mut state));
            check_mutation_aliasing::<5, 8>(random_array(&mut state));
        }
    }

    // Failure condition: `M > N` panics (the inlined `split_first_chunk_mut`
    // returns `None`, and `split_array_mut` unwraps it). Const generics force
    // a fixed instantiation; this complements `array_split_array_mut_out_of_bounds`
    // (M=7, N=6) by pinning the minimal boundary case M=1 > N=0.
    #[test]
    #[should_panic]
    fn split_array_mut_panics_when_m_exceeds_n_boundary() {
        let mut v: [u64; 0] = [];
        split_array_mut::<1, 0>(&mut v);
    }
}
