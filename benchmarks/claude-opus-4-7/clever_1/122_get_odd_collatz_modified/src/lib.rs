/// HumanEval/123 / CLEVER 122 — `get_odd_collatz(n)`.  Return the
/// sorted list of odd numbers in the Collatz sequence starting at `n`.
/// The sequence: `x → x/2` if x even, `x → 3x + 1` if x odd; ends at 1.
//
// Hax-compatibility rewrites:
//   * `Vec::push` (`alloc.vec.Impl_1.push`) is undefined in the Hax Lean
//     prelude — use `extend_from_slice` with a *typed* `[u64; 1]` let
//     binding so Hax's emitted `RustArray u64 1` carries the size in the
//     ascription and `unsize` elaborates cleanly. See
//     `rewrite_patterns/vec_push_to_extend_from_slice_typed_chunk.rs`.
//   * `acc.iter().any(|&v| v == x)` extracts to unmodeled
//     `core_models.iter.traits.iterator.Iterator.any`. Replace with a
//     tail-recursive helper walking the slice by index. See
//     `rewrite_patterns/iter_chain_to_recursion.rs`.
//   * The `while` loop in `insert_asc` is converted to tail recursion
//     per the recursion-preference rule (single accumulator state —
//     `(i, done, acc)` — bounded depth = length of the input vector,
//     which is small for the test ranges). See
//     `rewrite_patterns/while_loop_to_recursion.rs`.

fn vec_contains(v: &[u64], x: u64, i: usize) -> bool {
    if i >= v.len() {
        false
    } else if v[i] == x {
        true
    } else {
        vec_contains(v, x, i + 1)
    }
}

fn insert_asc_at(v: &[u64], x: u64, i: usize, done: bool, acc: Vec<u64>) -> Vec<u64> {
    if i >= v.len() {
        if done {
            acc
        } else {
            let mut acc = acc;
            let chunk: [u64; 1] = [x];
            acc.extend_from_slice(&chunk);
            acc
        }
    } else {
        let mut acc = acc;
        let new_done = if !done && v[i] >= x {
            let chunk: [u64; 1] = [x];
            acc.extend_from_slice(&chunk);
            true
        } else {
            done
        };
        if !new_done || v[i] != x {
            let chunk: [u64; 1] = [v[i]];
            acc.extend_from_slice(&chunk);
        }
        insert_asc_at(v, x, i + 1, new_done, acc)
    }
}

fn insert_asc(v: Vec<u64>, x: u64) -> Vec<u64> {
    insert_asc_at(&v, x, 0, false, Vec::new())
}

fn step_at(x: u64, acc: Vec<u64>) -> Vec<u64> {
    if x == 1 {
        if !vec_contains(&acc, 1, 0) { insert_asc(acc, 1) } else { acc }
    } else if x % 2 == 1 {
        let next = if vec_contains(&acc, x, 0) { acc } else { insert_asc(acc, x) };
        step_at(3 * x + 1, next)
    } else {
        step_at(x / 2, acc)
    }
}

pub fn get_odd_collatz(n: u64) -> Vec<u64> {
    if n == 0 { Vec::new() } else { step_at(n, Vec::new()) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    use std::collections::BTreeSet;

    #[test]
    fn known() {
        // 1 → [1]
        assert_eq!(get_odd_collatz(1), vec![1]);
        // 5 → 5, 16, 8, 4, 2, 1. odds: 1, 5
        assert_eq!(get_odd_collatz(5), vec![1, 5]);
    }

    /// Edge / failure case: n == 0 yields the empty vector.
    #[test]
    fn zero_is_empty() {
        assert_eq!(get_odd_collatz(0), Vec::<u64>::new());
    }

    /// Iterative reference simulation: collect the odd values appearing
    /// in the Collatz orbit starting at `n` (including the terminal `1`),
    /// returned sorted ascending with no duplicates. Iterative form avoids
    /// any recursion-depth concerns in the test harness. Bounding `n` below
    /// keeps every intermediate value comfortably inside `u64`.
    fn reference(n: u64) -> Vec<u64> {
        if n == 0 {
            return Vec::new();
        }
        let mut odds: BTreeSet<u64> = BTreeSet::new();
        let mut x = n;
        while x != 1 {
            if x % 2 == 1 {
                odds.insert(x);
            }
            x = if x % 2 == 0 { x / 2 } else { 3 * x + 1 };
        }
        odds.insert(1);
        odds.into_iter().collect()
    }

    proptest! {
        /// Postcondition (form): the output is strictly increasing.
        /// Implies sortedness AND uniqueness in a single check.
        #[test]
        fn prop_sorted_strictly_ascending(n in 1u64..=10_000) {
            let r = get_odd_collatz(n);
            for i in 1..r.len() {
                prop_assert!(r[i - 1] < r[i],
                    "not strictly ascending at index {i}: {:?}", r);
            }
        }

        /// Postcondition (content type): every returned element is odd.
        /// Independent of sortedness — neither implies the other.
        #[test]
        fn prop_all_elements_odd(n in 1u64..=10_000) {
            let r = get_odd_collatz(n);
            for v in &r {
                prop_assert!(v % 2 == 1, "even element {v} in result {:?}", r);
            }
        }

        /// Postcondition (correctness): the result equals the sorted
        /// unique list of odd values in the Collatz orbit starting at `n`.
        /// This is the core semantic claim of the function.
        #[test]
        fn prop_matches_reference(n in 1u64..=10_000) {
            prop_assert_eq!(get_odd_collatz(n), reference(n));
        }
    }
}
