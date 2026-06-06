/// HumanEval/100 / CLEVER 099 — `make_a_pile(n)`.  Return `[n, n+2,
/// n+4, ..., n + 2*(n-1)]` (n levels, each adds 2 to the previous).
//
// Hax-compatibility rewrite (see
// `rewrite_patterns/vec_push_to_extend_from_slice_typed_chunk.rs`):
// `Vec::push` (`alloc.vec.Impl_1.push`) is undefined in the Hax Lean
// prelude. Use `extend_from_slice` with a *typed* `[u64; 1]` let binding
// so the emitted `RustArray u64 1` carries the size in its ascription
// and `unsize` elaborates cleanly.
fn build_at(n: u64, k: u64, acc: Vec<u64>) -> Vec<u64> {
    if k >= n {
        acc
    } else {
        let mut acc = acc;
        let chunk: [u64; 1] = [n + 2 * k];
        acc.extend_from_slice(&chunk);
        build_at(n, k + 1, acc)
    }
}

pub fn make_a_pile(n: u64) -> Vec<u64> {
    if n == 0 { Vec::new() } else { build_at(n, 0, Vec::new()) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn known() {
        assert_eq!(make_a_pile(0), vec![]);
        assert_eq!(make_a_pile(1), vec![1]);
        assert_eq!(make_a_pile(3), vec![3, 5, 7]);
        assert_eq!(make_a_pile(4), vec![4, 6, 8, 10]);
    }

    proptest! {
        /// Contract clause (postcondition, length): the returned vector
        /// has exactly `n` elements.
        #[test]
        fn length_is_n(n in 0u64..1000) {
            let pile = make_a_pile(n);
            prop_assert_eq!(pile.len() as u64, n);
        }

        /// Contract clause (postcondition, contents): the element at
        /// index `k` is exactly `n + 2*k` for every `k < n`.  Combined
        /// with the length property above this pins down the full
        /// specification of `make_a_pile`.
        #[test]
        fn element_formula(n in 0u64..1000) {
            let pile = make_a_pile(n);
            for k in 0..n {
                prop_assert_eq!(pile[k as usize], n + 2 * k);
            }
        }
    }
}
