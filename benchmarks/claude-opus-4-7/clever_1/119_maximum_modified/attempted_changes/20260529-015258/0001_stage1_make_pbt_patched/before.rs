/// HumanEval/120 / CLEVER 119 — `maximum(arr, k)`.  Return a sorted-
/// ascending list of the `k` largest values in `arr`.  If `k == 0` or
/// `arr` is empty, return `[]`.  If `k >= arr.len()`, return a sorted
/// copy of `arr`.
fn insert_asc(v: Vec<u64>, x: u64) -> Vec<u64> {
    let mut r: Vec<u64> = Vec::new();
    let mut i = 0usize;
    let mut done = false;
    while i < v.len() {
        if !done && v[i] >= x { r.push(x); done = true; }
        r.push(v[i]); i += 1;
    }
    if !done { r.push(x); }
    r
}
fn sort_at(l: &[u64], i: usize, s: Vec<u64>) -> Vec<u64> {
    if i >= l.len() { s } else { sort_at(l, i + 1, insert_asc(s, l[i])) }
}

fn tail_from(s: &[u64], start: usize, mut acc: Vec<u64>) -> Vec<u64> {
    if start >= s.len() { acc }
    else {
        acc.push(s[start]);
        tail_from(s, start + 1, acc)
    }
}

pub fn maximum(arr: &[u64], k: u64) -> Vec<u64> {
    if k == 0 || arr.is_empty() { return Vec::new(); }
    let sorted = sort_at(arr, 0, Vec::new());
    let n = sorted.len() as u64;
    let start = if k >= n { 0 } else { (n - k) as usize };
    tail_from(&sorted, start, Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known() {
        assert_eq!(maximum(&[], 3), vec![]);
        assert_eq!(maximum(&[1, 2, 3], 0), vec![]);
        assert_eq!(maximum(&[5, 3, 1, 2, 4], 3), vec![3, 4, 5]);
        assert_eq!(maximum(&[1, 2, 3, 4], 10), vec![1, 2, 3, 4]);
    }
}
