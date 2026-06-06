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
        acc.push(v);
        build_at(n, k + 1, acc)
    }
}

pub fn f(n: u64) -> Vec<u64> {
    if n == 0 { Vec::new() } else { build_at(n, 1, Vec::new()) }
}

#[cfg(test)]
mod tests {
    use super::*;
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
}
