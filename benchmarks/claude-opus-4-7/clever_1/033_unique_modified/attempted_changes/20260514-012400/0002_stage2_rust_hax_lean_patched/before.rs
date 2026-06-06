/// Return sorted unique elements of `l`. (Return type widened to
/// `Vec<i64>` to match the docstring; CLEVER auto-defaulted to `i64`.)
fn insert_sorted(v: Vec<i64>, x: i64) -> Vec<i64> {
    let mut result: Vec<i64> = Vec::new();
    let n = v.len();
    let mut i: usize = 0;
    let mut inserted = false;
    while i < n {
        if !inserted && v[i] >= x {
            // Typed let — Hax emits the size in the type annotation
            // `RustArray i64 1`, so `unsize` can elaborate the size.
            let chunk: [i64; 1] = [x];
            result.extend_from_slice(&chunk);
            inserted = true;
        }
        let chunk: [i64; 1] = [v[i]];
        result.extend_from_slice(&chunk);
        i += 1;
    }
    if !inserted {
        let chunk: [i64; 1] = [x];
        result.extend_from_slice(&chunk);
    }
    result
}

fn sort_at(l: &[i64], i: usize, acc: Vec<i64>) -> Vec<i64> {
    if i >= l.len() {
        acc
    } else {
        sort_at(l, i + 1, insert_sorted(acc, l[i]))
    }
}

fn dedupe_at(sorted: &[i64], i: usize, acc: Vec<i64>) -> Vec<i64> {
    if i >= sorted.len() {
        acc
    } else if i == 0 || sorted[i] != sorted[i - 1] {
        let mut acc = acc;
        let chunk: [i64; 1] = [sorted[i]];
        acc.extend_from_slice(&chunk);
        dedupe_at(sorted, i + 1, acc)
    } else {
        dedupe_at(sorted, i + 1, acc)
    }
}

pub fn unique(l: &[i64]) -> Vec<i64> {
    let sorted = sort_at(l, 0, Vec::new());
    dedupe_at(&sorted, 0, Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    // --- Anchor unit test: pins down the empty-input base case ---

    #[test]
    fn empty_input_yields_empty_output() {
        assert_eq!(unique(&[]), Vec::<i64>::new());
    }

    // --- Property tests: the three independent postcondition clauses ---

    proptest! {
        // Postcondition 1: the output is strictly increasing.
        // This single property captures BOTH "sorted ascending" and
        // "no duplicates" — strict ordering rules out repeats.
        #[test]
        fn output_is_strictly_increasing(l in proptest::collection::vec(any::<i64>(), 0..32)) {
            let out = unique(&l);
            for w in out.windows(2) {
                prop_assert!(w[0] < w[1], "output not strictly increasing: {:?}", out);
            }
        }

        // Postcondition 2: every input element is present in the output.
        // (Output "covers" the input as a set.)
        #[test]
        fn output_contains_every_input_element(l in proptest::collection::vec(any::<i64>(), 0..32)) {
            let out = unique(&l);
            for x in &l {
                prop_assert!(out.contains(x), "input element {} missing from output {:?}", x, out);
            }
        }

        // Postcondition 3: every output element came from the input.
        // (Output is a subset of the input — no spurious elements.)
        #[test]
        fn output_only_contains_input_elements(l in proptest::collection::vec(any::<i64>(), 0..32)) {
            let out = unique(&l);
            for y in &out {
                prop_assert!(l.contains(y), "output element {} not in input {:?}", y, l);
            }
        }
    }
}
