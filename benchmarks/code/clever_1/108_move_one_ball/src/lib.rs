/// HumanEval/109 / CLEVER 108 — `move_one_ball(arr)`.  Can `arr` be
/// sorted in non-decreasing order via right rotations?  Empty list
/// returns true.  Spec assumes distinct elements but the algorithm
/// works generally.
fn is_sorted_split_at(l: &[i64], k: usize, i: usize) -> bool {
    let n = l.len();
    if i + 1 >= n { true }
    else {
        let a = l[(i + k) % n];
        let b = l[(i + 1 + k) % n];
        if a > b { false } else { is_sorted_split_at(l, k, i + 1) }
    }
}

fn try_at(l: &[i64], k: usize) -> bool {
    if k >= l.len() { false }
    else if is_sorted_split_at(l, k, 0) { true }
    else { try_at(l, k + 1) }
}

pub fn move_one_ball(arr: &[i64]) -> bool {
    if arr.is_empty() { true } else { try_at(arr, 0) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn known() {
        assert!(move_one_ball(&[]));
        assert!(move_one_ball(&[3, 4, 5, 1, 2]));   // shift by 2
        assert!(move_one_ball(&[1, 2, 3]));
        assert!(!move_one_ball(&[3, 5, 4, 1, 2]));
    }

    /// True iff `arr` is sorted in non-decreasing order.
    fn is_sorted(arr: &[i64]) -> bool {
        arr.windows(2).all(|w| w[0] <= w[1])
    }

    /// Cyclically rotate `arr` so that the element originally at index
    /// `k % arr.len()` becomes the new first element.  This enumerates
    /// the same family of arrays as the right-rotations the algorithm
    /// considers, so it is the right notion of "some rotation" for
    /// stating the contract.
    fn rotated(arr: &[i64], k: usize) -> Vec<i64> {
        let n = arr.len();
        if n == 0 {
            return vec![];
        }
        let k = k % n;
        let mut out = Vec::with_capacity(n);
        out.extend_from_slice(&arr[k..]);
        out.extend_from_slice(&arr[..k]);
        out
    }

    /// True iff some cyclic rotation of `arr` is sorted (vacuously true
    /// for the empty slice).
    fn some_rotation_is_sorted(arr: &[i64]) -> bool {
        if arr.is_empty() {
            return true;
        }
        (0..arr.len()).any(|k| is_sorted(&rotated(arr, k)))
    }

    proptest! {
        // (1) Boundary: empty slice is always accepted.
        #[test]
        fn empty_returns_true(_dummy in any::<bool>()) {
            prop_assert!(move_one_ball(&[]));
        }

        // (2) Completeness: if rotating a sorted array by some k yields
        //     `arr`, then `move_one_ball(arr)` must report `true`.
        //     We generate a sorted vector and rotate it by an arbitrary
        //     offset; the result is, by construction, sortable by a
        //     single rotation.
        #[test]
        fn rotation_of_sorted_returns_true(
            mut v in prop::collection::vec(-50i64..50, 0..8),
            k in 0usize..32,
        ) {
            v.sort();
            let r = rotated(&v, k);
            prop_assert!(move_one_ball(&r));
        }

        // (3) Soundness: if `move_one_ball(arr)` returns true then
        //     either `arr` is empty or some cyclic rotation of `arr`
        //     really is sorted in non-decreasing order.  A buggy
        //     implementation that returned `true` on, say, `[3,5,4,1,2]`
        //     would fail this check.
        #[test]
        fn true_implies_some_rotation_sorted(
            v in prop::collection::vec(-5i64..5, 0..7),
        ) {
            if move_one_ball(&v) {
                prop_assert!(some_rotation_is_sorted(&v));
            }
        }
    }
}
