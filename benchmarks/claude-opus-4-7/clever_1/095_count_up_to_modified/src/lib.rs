/// HumanEval/96 / CLEVER 095 — `count_up_to(n)`.  Return the list of
/// primes strictly less than `n`, in ascending order.  Empty if n < 2.
fn is_prime_at(n: u64, d: u64) -> bool {
    if d * d > n { true }
    else if n % d == 0 { false }
    else { is_prime_at(n, d + 1) }
}
fn is_prime(n: u64) -> bool {
    if n < 2 { false } else { is_prime_at(n, 2) }
}

// Hax-compatibility rewrite (see `rewrite_patterns/vec_push_to_extend_from_slice_typed_chunk.rs`):
// `Vec::push` (`alloc.vec.Impl_1.push`) is undefined in the Hax Lean prelude — use
// `extend_from_slice` with a *typed* `[u64; 1]` let binding so Hax's emitted
// `RustArray u64 1` carries the size in the ascription and `unsize` elaborates cleanly.
fn build_at(n: u64, k: u64, acc: Vec<u64>) -> Vec<u64> {
    if k >= n { acc }
    else if is_prime(k) {
        let mut acc = acc;
        let chunk: [u64; 1] = [k];
        acc.extend_from_slice(&chunk);
        build_at(n, k + 1, acc)
    } else {
        build_at(n, k + 1, acc)
    }
}

pub fn count_up_to(n: u64) -> Vec<u64> {
    build_at(n, 0, Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Independent reference primality oracle (trial division).
    /// Used so the property tests don't compare the implementation to itself.
    fn ref_is_prime(n: u64) -> bool {
        if n < 2 {
            return false;
        }
        let mut d: u64 = 2;
        while d.checked_mul(d).map_or(false, |s| s <= n) {
            if n % d == 0 {
                return false;
            }
            d += 1;
        }
        true
    }

    #[test]
    fn known() {
        assert_eq!(count_up_to(0), vec![]);
        assert_eq!(count_up_to(2), vec![]);
        assert_eq!(count_up_to(5), vec![2, 3]);
        assert_eq!(count_up_to(11), vec![2, 3, 5, 7]);
        assert_eq!(count_up_to(20), vec![2, 3, 5, 7, 11, 13, 17, 19]);
    }

    proptest! {
        // (1) Boundary: n < 2 ⇒ the result is empty.
        #[test]
        fn empty_below_two(n in 0u64..2) {
            prop_assert!(count_up_to(n).is_empty());
        }

        // (2) Soundness: every element of the result is prime.
        #[test]
        fn all_elements_prime(n in 0u64..150) {
            for p in count_up_to(n) {
                prop_assert!(ref_is_prime(p), "non-prime {} appeared in count_up_to({})", p, n);
            }
        }

        // (3) Upper bound: every element is strictly less than n.
        #[test]
        fn all_elements_below_n(n in 0u64..150) {
            for p in count_up_to(n) {
                prop_assert!(p < n, "element {} not strictly below n={}", p, n);
            }
        }

        // (4) Strictly ascending order (implies no duplicates).
        #[test]
        fn strictly_ascending(n in 0u64..150) {
            let v = count_up_to(n);
            for w in v.windows(2) {
                prop_assert!(w[0] < w[1], "order violated: {} !< {}", w[0], w[1]);
            }
        }

        // (5) Completeness: every prime in [0, n) is present in the result.
        #[test]
        fn complete(n in 0u64..150) {
            let v = count_up_to(n);
            for k in 0..n {
                if ref_is_prime(k) {
                    prop_assert!(v.contains(&k), "missing prime {} from count_up_to({})", k, n);
                }
            }
        }
    }
}
