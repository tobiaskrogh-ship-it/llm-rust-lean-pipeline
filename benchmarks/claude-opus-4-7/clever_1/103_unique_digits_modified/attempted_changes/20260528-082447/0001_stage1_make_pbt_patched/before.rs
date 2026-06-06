/// HumanEval/104 / CLEVER 103 — `unique_digits(x)`.  Return a sorted
/// list of positive integers from `x` whose decimal digits are all odd.
/// (The name "unique" is misleading; "all-odd-digit" is the actual contract.)
fn has_even_digit_at(n: u64) -> bool {
    if n == 0 { false }
    else if (n % 10) % 2 == 0 { true }
    else { has_even_digit_at(n / 10) }
}

fn has_even_digit(n: u64) -> bool {
    if n == 0 { true } else { has_even_digit_at(n) }
}

fn insert_asc(v: Vec<u64>, e: u64) -> Vec<u64> {
    let mut r: Vec<u64> = Vec::new();
    let mut i = 0usize;
    let mut done = false;
    while i < v.len() {
        if !done && v[i] >= e { r.push(e); done = true; }
        r.push(v[i]); i += 1;
    }
    if !done { r.push(e); }
    r
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
    #[test]
    fn known() {
        assert_eq!(unique_digits(&[15, 33, 1422, 1]), vec![1, 15, 33]);
        assert_eq!(unique_digits(&[152, 323, 1422, 10]), vec![]);
    }
}
