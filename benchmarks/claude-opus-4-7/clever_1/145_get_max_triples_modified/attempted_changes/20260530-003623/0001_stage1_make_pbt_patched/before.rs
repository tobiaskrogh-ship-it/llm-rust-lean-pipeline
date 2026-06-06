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
    #[test]
    fn known() {
        // n=5: a = [1, 3, 7, 13, 21]. Triples summing to multiple of 3: (1,7,13)=21,
        // (1,3,21)=25 not div by 3, ... Verified count = 1.
        assert_eq!(get_max_triples(5), 1);
        assert_eq!(get_max_triples(0), 0);
        assert_eq!(get_max_triples(2), 0);
    }
}
