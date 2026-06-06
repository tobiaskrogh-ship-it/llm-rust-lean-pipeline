/// HumanEval/104 / CLEVER 103 — `unique_digits(x)`.  Return a sorted
/// list of positive integers from `x` whose decimal digits are all odd.
/// (The name "unique" is misleading; "all-odd-digit" is the actual contract.)
//
// Hax-compatibility rewrites:
//   * `Vec::push` (`alloc.vec.Impl_1.push`) is undefined in the Hax Lean
//     prelude — replaced with `extend_from_slice(&chunk)` where `chunk`
//     is a *typed* `[u64; 1]` let binding so Hax's emitted `RustArray u64 1`
//     carries the size in the ascription and `unsize` elaborates cleanly.
//     (See `rewrite_patterns/vec_push_to_extend_from_slice_typed_chunk.rs`.)
//   * The `while` loop in the original `insert_asc` is lifted into a
//     tail-recursive helper. Per the recursion-preference rule this also
//     avoids the constant-`0` decreasing measure that Hax emits for the
//     `while_loop` combinator.
fn has_even_digit_at(n: u64) -> bool {
    if n == 0 { false }
    else if (n % 10) % 2 == 0 { true }
    else { has_even_digit_at(n / 10) }
}

fn has_even_digit(n: u64) -> bool {
    if n == 0 { true } else { has_even_digit_at(n) }
}

fn insert_asc_at(v: &[u64], i: usize, e: u64, done: bool, acc: Vec<u64>) -> Vec<u64> {
    if i >= v.len() {
        if !done {
            let mut acc = acc;
            let chunk: [u64; 1] = [e];
            acc.extend_from_slice(&chunk);
            acc
        } else {
            acc
        }
    } else if !done && v[i] >= e {
        let mut acc = acc;
        let chunk_e: [u64; 1] = [e];
        acc.extend_from_slice(&chunk_e);
        let chunk_v: [u64; 1] = [v[i]];
        acc.extend_from_slice(&chunk_v);
        insert_asc_at(v, i + 1, e, true, acc)
    } else {
        let mut acc = acc;
        let chunk_v: [u64; 1] = [v[i]];
        acc.extend_from_slice(&chunk_v);
        insert_asc_at(v, i + 1, e, done, acc)
    }
}

fn insert_asc(v: Vec<u64>, e: u64) -> Vec<u64> {
    insert_asc_at(&v, 0, e, false, Vec::new())
}

fn filter_at(l: &[u64], i: usize, acc: Vec<u64>) -> Vec<u64> {
    if i >= l.len() { acc }
    else if has_even_digit(l[i]) { filter_at(l, i + 1, acc) }
    else { filter_at(l, i + 1, insert_asc(acc, l[i])) }
}

pub fn unique_digits(x: &[u64]) -> Vec<u64> {
    filter_at(x, 0, Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn known() {
        assert_eq!(unique_digits(&[15, 33, 1422, 1]), vec![1, 15, 33]);
        assert_eq!(unique_digits(&[152, 323, 1422, 10]), vec![]);
    }

    /// Reference predicate matching the spec: every decimal digit of `n`
    /// is odd. By convention (matching the implementation), 0 has the
    /// digit 0 (even), so `all_odd_digits(0) == false`.
    fn all_odd_digits(mut n: u64) -> bool {
        if n == 0 {
            return false;
        }
        while n != 0 {
            if (n % 10) % 2 == 0 {
                return false;
            }
            n /= 10;
        }
        true
    }

    proptest! {
        /// Contract clause 1 (postcondition on ordering):
        /// the returned vector is sorted in non-decreasing order.
        #[test]
        fn output_is_sorted(input in proptest::collection::vec(0u64..100_000, 0..20)) {
            let out = unique_digits(&input);
            for w in out.windows(2) {
                prop_assert!(w[0] <= w[1]);
            }
        }

        /// Contract clause 2 (postcondition on element selection):
        /// as a multiset, the output equals the input elements whose
        /// decimal digits are all odd. This single property captures
        /// (a) soundness — every output element comes from the input and
        ///     has all odd digits;
        /// (b) completeness — every all-odd-digit input element appears
        ///     in the output;
        /// (c) multiplicity preservation — duplicates are preserved.
        #[test]
        fn output_is_filter_multiset(input in proptest::collection::vec(0u64..100_000, 0..20)) {
            let out = unique_digits(&input);
            let mut expected: Vec<u64> = input
                .iter()
                .copied()
                .filter(|&n| all_odd_digits(n))
                .collect();
            let mut got = out.clone();
            expected.sort();
            got.sort();
            prop_assert_eq!(expected, got);
        }
    }
}
