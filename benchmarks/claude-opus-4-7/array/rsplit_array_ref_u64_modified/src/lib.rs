//! Extracted from `core::array::<[T; N]>::rsplit_array_ref` (src/array/mod.rs:815),
//! monomorphized to `u64`. The inherent method `(&self) -> (&[T], &[T; M])` is
//! rewritten as a free function over a `&[u64; N]`.
//!
//! The original calls `self.split_last_chunk::<M>().unwrap()`. The private
//! slice helper `split_last_chunk` (src/slice/mod.rs:447) is inlined here.
//! Its body uses an unstable raw-pointer cast (`last.as_ptr().cast_array()`);
//! since `last.len() == M` on the `Some` path, that is equivalent to the
//! stable `TryFrom<&[T]> for &[T; M]` conversion, which is used instead.

/// Returns the remaining slice and an array reference to the last `M` items.
///
/// Panics if the slice is shorter than `M`.
//
// Rewritten for Hax: the original used `s.len().checked_sub(M)` and
// returned `Option`, then `rsplit_array_ref` called `Option::unwrap` —
// panicking exactly when `M > s.len()`. Both `usize::checked_sub`
// (`core_models.num.Impl_11.checked_sub`) and `Option::unwrap`
// (`core_models.option.Impl.unwrap`) are undefined in the Hax Lean
// prelude (`lake build` "Unknown identifier"). Bare `s.len() - M`
// underflows (panics) on exactly the same `M > s.len()` condition —
// Hax encodes the subtraction-overflow obligation in `RustM` — so the
// `Option` is dropped and the contract (the `should_panic` out-of-bounds
// test) is preserved. `try_into().unwrap()` is `Result::unwrap`
// (`core_models.result.Impl.unwrap`), which IS modeled, so it stays.
fn split_last_chunk<const M: usize>(s: &[u64]) -> (&[u64], &[u64; M]) {
    let index = s.len() - M;
    let (init, last) = s.split_at(index);
    // SAFETY-equivalent: `last.len() == M`, so the conversion succeeds.
    (init, last.try_into().unwrap())
}

/// Divides one array reference into two at an index from the end.
///
/// The first will contain all indices from `[0, N - M)` and the second will
/// contain all indices from `[N - M, N)`.
///
/// # Panics
///
/// Panics if `M > N`.
#[inline]
pub fn rsplit_array_ref<const M: usize, const N: usize>(a: &[u64; N]) -> (&[u64], &[u64; M]) {
    split_last_chunk::<M>(a)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        // Postcondition (the single core semantic claim): when `M <= N`,
        // `rsplit_array_ref::<M, N>(a)` partitions `a` exactly at index
        // `N - M` — `left` is the length-`(N - M)` prefix `a[0 .. N - M]`
        // and `right` is the length-`M` suffix `a[N - M .. N]`. Exercised
        // over arbitrary contents at an interior cut and at both boundaries
        // (M = 0 and M = N), which are the distinct edge cases of the
        // underlying `checked_sub` / `split_at` logic.
        //
        // The length facts (`left.len() == N - M`, `right.len() == M`) and
        // the reconstruction fact (`[left, right].concat() == a`) are
        // implied by these equalities and are intentionally not tested
        // separately, as they are derived rather than independent claims.
        #[test]
        fn rsplit_partitions_at_n_minus_m(a in any::<[u64; 12]>()) {
            // Interior cut: M = 5, N = 12  ->  split index N - M = 7.
            {
                let (left, right) = rsplit_array_ref::<5, 12>(&a);
                prop_assert_eq!(left, &a[0..7]);
                prop_assert_eq!(right, &a[7..12]);
            }
            // Boundary M = 0: right is empty, left is the whole array.
            {
                let (left, right) = rsplit_array_ref::<0, 12>(&a);
                prop_assert_eq!(left, &a[..]);
                prop_assert_eq!(right, &([] as [u64; 0]));
            }
            // Boundary M = N: left is empty, right is the whole array.
            {
                let (left, right) = rsplit_array_ref::<12, 12>(&a);
                prop_assert_eq!(left, &([] as [u64; 0])[..]);
                prop_assert_eq!(right, &a);
            }
        }
    }

    // Failure condition: `rsplit_array_ref` panics when `M > N`.
    // (`M`/`N` are const generics, so this cannot be property-driven;
    // transferred from core's `tests/array.rs`.)
    #[test]
    #[should_panic]
    fn array_rsplit_array_ref_out_of_bounds() {
        let v: [u64; 6] = [1, 2, 3, 4, 5, 6];

        rsplit_array_ref::<7, 6>(&v);
    }
}
