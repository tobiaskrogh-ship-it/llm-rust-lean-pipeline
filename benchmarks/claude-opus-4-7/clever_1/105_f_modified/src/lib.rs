/// HumanEval/106 / CLEVER 105 — `f(n)`.  Return a list of length `n`
/// where position `i` (1-indexed) is `i!` if `i` is even, else `1+2+...+i`.
fn factorial_at(k: u64, cur: u64, acc: u64) -> u64 {
    if cur > k { acc } else { factorial_at(k, cur + 1, acc * cur) }
}
fn sum_at(k: u64, cur: u64, acc: u64) -> u64 {
    if cur > k { acc } else { sum_at(k, cur + 1, acc + cur) }
}

fn build_at(n: u64, k: u64, mut acc: Vec<u64>) -> Vec<u64> {
    if k > n { acc }
    else {
        let v = if k % 2 == 0 { factorial_at(k, 1, 1) } else { sum_at(k, 1, 0) };
        // `Vec::push` is unmodeled in the Hax Lean prelude; use a typed-let
        // chunk + `extend_from_slice` per
        // `rewrite_patterns/vec_push_to_extend_from_slice_typed_chunk.rs`.
        let chunk: [u64; 1] = [v];
        acc.extend_from_slice(&chunk);
        build_at(n, k + 1, acc)
    }
}

pub fn f(n: u64) -> Vec<u64> {
    if n == 0 { Vec::new() } else { build_at(n, 1, Vec::new()) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn known() {
        // i=1 (odd) → 1
        // i=2 (even) → 2
        // i=3 (odd) → 6
        // i=4 (even) → 24
        // i=5 (odd) → 15
        assert_eq!(f(0), vec![]);
        assert_eq!(f(5), vec![1, 2, 6, 24, 15]);
    }

    // Reference factorial for the spec side of property tests.
    // Used only as an oracle; bounded to inputs where the result fits in u64.
    fn factorial_spec(k: u64) -> u64 {
        let mut acc: u64 = 1;
        let mut i: u64 = 1;
        while i <= k {
            acc *= i;
            i += 1;
        }
        acc
    }

    proptest! {
        // Length postcondition: f(n) has exactly n elements.
        // Bound n to keep within the safe domain (factorial fits in u64 for n ≤ 20).
        #[test]
        fn length_matches_n(n in 0u64..=20) {
            prop_assert_eq!(f(n).len(), n as usize);
        }

        // Odd-position postcondition: for odd i in 1..=n, f(n)[i-1] is the i-th
        // triangular number 1 + 2 + ... + i = i*(i+1)/2.
        #[test]
        fn odd_positions_are_triangular(n in 0u64..=20) {
            let v = f(n);
            for i in 1..=n {
                if i % 2 == 1 {
                    prop_assert_eq!(v[(i - 1) as usize], i * (i + 1) / 2);
                }
            }
        }

        // Even-position postcondition: for even i in 1..=n, f(n)[i-1] == i!.
        #[test]
        fn even_positions_are_factorial(n in 0u64..=20) {
            let v = f(n);
            for i in 1..=n {
                if i % 2 == 0 {
                    prop_assert_eq!(v[(i - 1) as usize], factorial_spec(i));
                }
            }
        }
    }
}
