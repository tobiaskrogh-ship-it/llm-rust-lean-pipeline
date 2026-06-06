/// HumanEval/88 / CLEVER 087 — `sort_array(lst)`.  Sort `lst` ascending
/// if `(lst[0] + lst[last]) % 2 != 0` (sum is odd); descending otherwise.
/// Spec restricts to non-negative integers → `u64`.
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

fn reverse_at(s: &[u64], i: usize, mut acc: Vec<u64>) -> Vec<u64> {
    if i >= s.len() { acc } else {
        acc.push(s[s.len() - 1 - i]);
        reverse_at(s, i + 1, acc)
    }
}

pub fn sort_array(lst: &[u64]) -> Vec<u64> {
    if lst.is_empty() { return Vec::new(); }
    let sorted = sort_at(lst, 0, Vec::new());
    let parity = (lst[0] % 2 + lst[lst.len() - 1] % 2) % 2;
    if parity != 0 { sorted } else { reverse_at(&sorted, 0, Vec::new()) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn naive(l: &[u64]) -> Vec<u64> {
        if l.is_empty() { return Vec::new(); }
        let mut s = l.to_vec(); s.sort();
        let p = (l[0] + l[l.len()-1]) % 2;
        if p == 1 { s } else { s.reverse(); s }
    }
    proptest! {
        #[test]
        fn matches(l in proptest::collection::vec(0u64..=100, 0..12)) {
            prop_assert_eq!(sort_array(&l), naive(&l));
        }
    }
}
