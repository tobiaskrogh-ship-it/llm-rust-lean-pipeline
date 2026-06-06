/// HumanEval/163 / CLEVER 160 — `generate_integers(a, b)`.  Return the
/// even single-digit integers (0, 2, 4, 6, 8) in `[min(a, b), max(a, b)]`,
/// in ascending order.
fn build_at(lo: u64, hi: u64, k: u64, mut acc: Vec<u64>) -> Vec<u64> {
    if k > hi || k > 8 { acc }
    else {
        if k >= lo && k % 2 == 0 {
            // `Vec::push` is unmodeled in the Hax Lean prelude
            // (`alloc.vec.Impl_1.push`). Use the typed-chunk +
            // `extend_from_slice` rewrite from
            // rewrite_patterns/vec_push_to_extend_from_slice_typed_chunk.rs.
            let chunk: [u64; 1] = [k];
            acc.extend_from_slice(&chunk);
        }
        build_at(lo, hi, k + 1, acc)
    }
}

pub fn generate_integers(a: u64, b: u64) -> Vec<u64> {
    let lo = if a < b { a } else { b };
    let hi = if a < b { b } else { a };
    build_at(lo, hi, 0, Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn known() {
        assert_eq!(generate_integers(2, 8), vec![2, 4, 6, 8]);
        assert_eq!(generate_integers(8, 2), vec![2, 4, 6, 8]);
        assert_eq!(generate_integers(10, 14), vec![]);
        assert_eq!(generate_integers(0, 0), vec![0]);
    }

    // Use a small range so we frequently hit the interesting window [0, 8],
    // but still exercise inputs that lie above it.
    fn input() -> impl Strategy<Value = u64> {
        0u64..30
    }

    proptest! {
        // Soundness: every element returned is an even single-digit integer
        // lying in [min(a, b), max(a, b)].
        #[test]
        fn every_element_is_even_single_digit_in_range(a in input(), b in input()) {
            let lo = a.min(b);
            let hi = a.max(b);
            for &x in generate_integers(a, b).iter() {
                prop_assert!(x % 2 == 0, "element {} is not even", x);
                prop_assert!(x <= 8,    "element {} is not a single digit", x);
                prop_assert!(x >= lo,   "element {} is below min(a,b)={}", x, lo);
                prop_assert!(x <= hi,   "element {} is above max(a,b)={}", x, hi);
            }
        }

        // Completeness: every even single-digit integer in [min(a, b), max(a, b)]
        // appears in the result.
        #[test]
        fn every_even_single_digit_in_range_is_present(a in input(), b in input()) {
            let lo = a.min(b);
            let hi = a.max(b);
            let result = generate_integers(a, b);
            for x in [0u64, 2, 4, 6, 8] {
                if x >= lo && x <= hi {
                    prop_assert!(result.contains(&x),
                        "expected {} in result for (a={}, b={}), got {:?}", x, a, b, result);
                }
            }
        }

        // Order: the result is strictly ascending. Strict ordering also
        // rules out duplicate elements.
        #[test]
        fn result_is_strictly_ascending(a in input(), b in input()) {
            let result = generate_integers(a, b);
            for i in 1..result.len() {
                prop_assert!(result[i - 1] < result[i],
                    "result not strictly ascending at index {}: {:?}", i, result);
            }
        }

        // Symmetry: swapping the arguments yields the same result.
        #[test]
        fn symmetric_in_arguments(a in input(), b in input()) {
            prop_assert_eq!(generate_integers(a, b), generate_integers(b, a));
        }
    }
}
