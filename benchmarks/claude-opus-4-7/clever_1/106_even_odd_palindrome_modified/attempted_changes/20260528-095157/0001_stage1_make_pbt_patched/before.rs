/// HumanEval/107 / CLEVER 106 — `even_odd_palindrome(n)`.  Count the
/// number of palindromic integers in `1..=n` that are even and odd
/// respectively.  Returns `(even_count, odd_count)`.
fn rev_at(n: u64, acc: u64) -> u64 {
    if n == 0 { acc } else { rev_at(n / 10, acc * 10 + n % 10) }
}
fn is_palindrome(n: u64) -> bool { rev_at(n, 0) == n }

fn count_at(n: u64, k: u64, e: u64, o: u64) -> (u64, u64) {
    if k > n { (e, o) }
    else if is_palindrome(k) {
        if k % 2 == 0 { count_at(n, k + 1, e + 1, o) }
        else { count_at(n, k + 1, e, o + 1) }
    } else {
        count_at(n, k + 1, e, o)
    }
}

pub fn even_odd_palindrome(n: u64) -> (u64, u64) {
    count_at(n, 1, 0, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known() {
        // 1..=3: palindromes are 1, 2, 3 → odd=2 (1, 3), even=1 (2)
        assert_eq!(even_odd_palindrome(3), (1, 2));
        // 1..=12: palindromes are 1, 2, 3, 4, 5, 6, 7, 8, 9, 11
        // even: 2, 4, 6, 8 = 4; odd: 1, 3, 5, 7, 9, 11 = 6
        assert_eq!(even_odd_palindrome(12), (4, 6));
    }
}
