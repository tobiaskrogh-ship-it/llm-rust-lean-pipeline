/// HumanEval/147 / CLEVER 145 — `get_max_triples(n)`.  Build the array
/// `a` of length `n` with `a[i] = (i+1)² - (i+1) + 1`.  Count triples
/// (i, j, k) with `i < j < k` such that `a[i] + a[j] + a[k]` is a
/// multiple of 3.  `n == 0` → 0.
fn ai(i: u64) -> u64 {
    let x = i + 1;
    x * x - x + 1
}

fn loop_k(n: u64, i: u64, j: u64, k: u64, acc: u64) -> u64 {
    if k > n { acc }
    else if (ai(i - 1) + ai(j - 1) + ai(k - 1)) % 3 == 0 {
        loop_k(n, i, j, k + 1, acc + 1)
    } else {
        loop_k(n, i, j, k + 1, acc)
    }
}

fn loop_j(n: u64, i: u64, j: u64, acc: u64) -> u64 {
    if j >= n { acc } else { loop_j(n, i, j + 1, loop_k(n, i, j, j + 1, acc)) }
}

fn loop_i(n: u64, i: u64, acc: u64) -> u64 {
    if i + 1 >= n { acc } else { loop_i(n, i + 1, loop_j(n, i, i + 1, acc)) }
}

pub fn get_max_triples(n: u64) -> u64 {
    if n < 3 { 0 } else { loop_i(n, 1, 0) }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Independent reference: build the array directly and iterate over all
    /// (i, j, k) with i < j < k < n, counting those whose sum is divisible by 3.
    /// Structurally different from the recursive accumulator in `get_max_triples`,
    /// so any off-by-one in the recursive bounds shows up as a mismatch.
    fn naive_count(n: u64) -> u64 {
        if n < 3 {
            return 0;
        }
        let n_usize = n as usize;
        let a: Vec<u64> = (0..n)
            .map(|i| {
                let x = i + 1;
                x * x - x + 1
            })
            .collect();
        let mut count: u64 = 0;
        for i in 0..n_usize {
            for j in (i + 1)..n_usize {
                for k in (j + 1)..n_usize {
                    if (a[i] + a[j] + a[k]) % 3 == 0 {
                        count += 1;
                    }
                }
            }
        }
        count
    }

    #[test]
    fn known() {
        // n=5: a = [1, 3, 7, 13, 21]. Triples summing to multiple of 3: (1,7,13)=21,
        // (1,3,21)=25 not div by 3, ... Verified count = 1.
        assert_eq!(get_max_triples(5), 1);
        assert_eq!(get_max_triples(0), 0);
        assert_eq!(get_max_triples(2), 0);
    }

    /// Contract (boundary): for n < 3 there are no triples to form,
    /// so the result must be 0.
    #[test]
    fn below_three_is_zero() {
        assert_eq!(get_max_triples(0), 0);
        assert_eq!(get_max_triples(1), 0);
        assert_eq!(get_max_triples(2), 0);
    }

    /// Contract (core postcondition): for every n, `get_max_triples(n)`
    /// equals the number of triples (i, j, k) with i < j < k < n such that
    /// a[i] + a[j] + a[k] is divisible by 3.
    #[test]
    fn matches_naive_count() {
        for n in 0u64..=25 {
            assert_eq!(
                get_max_triples(n),
                naive_count(n),
                "mismatch at n = {}",
                n
            );
        }
    }
}
