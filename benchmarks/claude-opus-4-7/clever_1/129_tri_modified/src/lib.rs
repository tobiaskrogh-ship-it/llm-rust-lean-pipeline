/// HumanEval/130 / CLEVER 129 — `tri(n)`.  Return the first `n + 1`
/// terms of the recurrence:
///   tri(1) = 3,  tri(n)     = 1 + n/2  if n is even,
///                tri(n)     = tri(n-1) + tri(n-2) + tri(n+1)  if n is odd.
/// Non-negative `n`, so use `u64`.
///
/// The trick: for odd n, expanding the recurrence and tri(n+1) (even)
/// gives a closed form so this is computable without forward references.
/// tri(0) is unspecified; we return 3 (matches Python solutions in the wild).
//
// Hax-compatibility rewrites:
//   * `Vec::push` (`alloc.vec.Impl_1.push`) is undefined in the Hax Lean
//     prelude — use `extend_from_slice` with a *typed* `[u64; 1]` let
//     binding so Hax's emitted `RustArray u64 1` carries the size in the
//     ascription and `unsize` elaborates cleanly. See
//     `rewrite_patterns/vec_push_to_extend_from_slice_typed_chunk.rs`.
//   * `while` loop over `i` with a single Vec accumulator and a clearly
//     decreasing measure (`n + 1 - i`) is converted to tail recursion to
//     admit cleaner downstream proofs via `Nat.strongRecOn`. See
//     `rewrite_patterns/while_loop_to_recursion.rs`.
fn tri_at(n: u64, i: u64, acc: Vec<u64>) -> Vec<u64> {
    if i > n {
        acc
    } else {
        let v = if i == 0 {
            3
        } else if i == 1 {
            3
        } else if i % 2 == 0 {
            1 + i / 2
        } else {
            // For odd i ≥ 3: tri(i) = tri(i-1) + tri(i-2) + tri(i+1)
            //   tri(i-1) = 1 + (i-1)/2
            //   tri(i-2) = previous odd's value (already computed → acc[i-2])
            //   tri(i+1) = 1 + (i+1)/2
            // Simplify: tri(i) = 1 + (i-1)/2 + acc[(i-2) as usize] + 1 + (i+1)/2.
            let prev_odd = acc[(i - 2) as usize];
            let a = 1 + (i - 1) / 2;
            let b = 1 + (i + 1) / 2;
            a + prev_odd + b
        };
        let mut acc = acc;
        let chunk: [u64; 1] = [v];
        acc.extend_from_slice(&chunk);
        tri_at(n, i + 1, acc)
    }
}

pub fn tri(n: u64) -> Vec<u64> {
    tri_at(n, 0, Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn known() {
        // tri(3) = tri(2) + tri(1) + tri(4) = 2 + 3 + 3 = 8
        // tri(2) = 1 + 2/2 = 2; tri(4) = 1 + 4/2 = 3
        let r = tri(4);
        assert_eq!(r[1], 3);    // tri(1)
        assert_eq!(r[2], 2);    // tri(2)
        assert_eq!(r[3], 8);    // tri(3)
        assert_eq!(r[4], 3);    // tri(4)
    }

    proptest! {
        // Structural postcondition: the result has length n + 1.
        #[test]
        fn length_is_n_plus_one(n in 0u64..200) {
            let r = tri(n);
            prop_assert_eq!(r.len() as u64, n + 1);
        }

        // Base cases: tri(0) and tri(1) are both 3.
        // These ground the recursion; without them no other value is determined.
        #[test]
        fn base_cases(n in 0u64..200) {
            let r = tri(n);
            prop_assert_eq!(r[0], 3);
            if n >= 1 {
                prop_assert_eq!(r[1], 3);
            }
        }

        // Even branch of the spec: for even i >= 2, tri(i) = 1 + i/2.
        #[test]
        fn even_terms_closed_form(n in 0u64..200) {
            let r = tri(n);
            let mut i = 2u64;
            while i <= n {
                prop_assert_eq!(r[i as usize], 1 + i / 2);
                i += 2;
            }
        }

        // Odd branch of the spec (the defining recurrence):
        // for odd i >= 3, tri(i) = tri(i-1) + tri(i-2) + tri(i+1).
        // We only check it when i+1 is in range so tri(i+1) is observable.
        #[test]
        fn odd_recurrence_holds(n in 0u64..200) {
            let r = tri(n);
            let mut i = 3u64;
            while i + 1 <= n {
                prop_assert_eq!(
                    r[i as usize],
                    r[(i - 1) as usize] + r[(i - 2) as usize] + r[(i + 1) as usize]
                );
                i += 2;
            }
        }
    }
}
