/// HumanEval/96 / CLEVER 095 — `count_up_to(n)`.  Return the list of
/// primes strictly less than `n`, in ascending order.  Empty if n < 2.
fn is_prime_at(n: u64, d: u64) -> bool {
    if d * d > n { true }
    else if n % d == 0 { false }
    else { is_prime_at(n, d + 1) }
}
fn is_prime(n: u64) -> bool {
    if n < 2 { false } else { is_prime_at(n, 2) }
}

fn build_at(n: u64, k: u64, mut acc: Vec<u64>) -> Vec<u64> {
    if k >= n { acc }
    else if is_prime(k) {
        acc.push(k);
        build_at(n, k + 1, acc)
    } else {
        build_at(n, k + 1, acc)
    }
}

pub fn count_up_to(n: u64) -> Vec<u64> {
    build_at(n, 0, Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known() {
        assert_eq!(count_up_to(0), vec![]);
        assert_eq!(count_up_to(2), vec![]);
        assert_eq!(count_up_to(5), vec![2, 3]);
        assert_eq!(count_up_to(11), vec![2, 3, 5, 7]);
        assert_eq!(count_up_to(20), vec![2, 3, 5, 7, 11, 13, 17, 19]);
    }
}
