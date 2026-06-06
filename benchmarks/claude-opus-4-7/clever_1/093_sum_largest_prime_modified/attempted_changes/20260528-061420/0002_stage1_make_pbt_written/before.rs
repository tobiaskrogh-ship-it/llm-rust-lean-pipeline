/// HumanEval/94 / CLEVER 093 — `sum_largest_prime(lst)`.  Find the
/// largest prime in `lst`; return the sum of its decimal digits.
/// Return `0` for an empty list or no primes.
fn is_prime_at(n: u64, d: u64) -> bool {
    if d * d > n { true }
    else if n % d == 0 { false }
    else { is_prime_at(n, d + 1) }
}
fn is_prime(n: u64) -> bool {
    if n < 2 { false } else { is_prime_at(n, 2) }
}

fn largest_prime_at(l: &[u64], i: usize, best: u64, found: bool) -> (u64, bool) {
    if i >= l.len() { (best, found) }
    else if is_prime(l[i]) && (!found || l[i] > best) {
        largest_prime_at(l, i + 1, l[i], true)
    } else {
        largest_prime_at(l, i + 1, best, found)
    }
}

fn digit_sum_at(n: u64, acc: u64) -> u64 {
    if n == 0 { acc } else { digit_sum_at(n / 10, acc + n % 10) }
}

pub fn sum_largest_prime(lst: &[u64]) -> u64 {
    let (p, found) = largest_prime_at(lst, 0, 0, false);
    if !found { 0 } else { digit_sum_at(p, 0) }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known() {
        assert_eq!(sum_largest_prime(&[]), 0);
        assert_eq!(sum_largest_prime(&[4, 6, 8]), 0);
        assert_eq!(sum_largest_prime(&[2, 3, 5, 7]), 7);    // 7 → 7
        assert_eq!(sum_largest_prime(&[13, 4, 11]), 1 + 3); // 13 → 4
    }
}
