/// HumanEval/123 / CLEVER 122 — `get_odd_collatz(n)`.  Return the
/// sorted list of odd numbers in the Collatz sequence starting at `n`.
/// The sequence: `x → x/2` if x even, `x → 3x + 1` if x odd; ends at 1.
fn insert_asc(v: Vec<u64>, x: u64) -> Vec<u64> {
    let mut r: Vec<u64> = Vec::new();
    let mut i = 0usize;
    let mut done = false;
    while i < v.len() {
        if !done && v[i] >= x { r.push(x); done = true; }
        if !done || v[i] != x { r.push(v[i]); }
        i += 1;
    }
    if !done { r.push(x); }
    r
}

fn step_at(x: u64, acc: Vec<u64>) -> Vec<u64> {
    if x == 1 {
        if !acc.iter().any(|&v| v == 1) { insert_asc(acc, 1) } else { acc }
    } else if x % 2 == 1 {
        let next = if acc.iter().any(|&v| v == x) { acc } else { insert_asc(acc, x) };
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
    #[test]
    fn known() {
        // 1 → [1]
        assert_eq!(get_odd_collatz(1), vec![1]);
        // 5 → 5, 16, 8, 4, 2, 1. odds: 1, 5
        assert_eq!(get_odd_collatz(5), vec![1, 5]);
    }
}
