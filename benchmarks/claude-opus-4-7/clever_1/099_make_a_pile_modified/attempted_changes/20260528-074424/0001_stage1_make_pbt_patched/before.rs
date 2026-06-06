/// HumanEval/100 / CLEVER 099 — `make_a_pile(n)`.  Return `[n, n+2,
/// n+4, ..., n + 2*(n-1)]` (n levels, each adds 2 to the previous).
fn build_at(n: u64, k: u64, mut acc: Vec<u64>) -> Vec<u64> {
    if k >= n { acc }
    else {
        acc.push(n + 2 * k);
        build_at(n, k + 1, acc)
    }
}

pub fn make_a_pile(n: u64) -> Vec<u64> {
    if n == 0 { Vec::new() } else { build_at(n, 0, Vec::new()) }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known() {
        assert_eq!(make_a_pile(0), vec![]);
        assert_eq!(make_a_pile(1), vec![1]);
        assert_eq!(make_a_pile(3), vec![3, 5, 7]);
        assert_eq!(make_a_pile(4), vec![4, 6, 8, 10]);
    }
}
