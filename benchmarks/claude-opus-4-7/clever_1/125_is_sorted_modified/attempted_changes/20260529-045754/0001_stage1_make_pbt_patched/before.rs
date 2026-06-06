/// HumanEval/126 / CLEVER 125 — `is_sorted(lst)`.  True iff `lst` is in
/// non-decreasing order AND no value appears more than twice.  Override
/// to `u64` per docstring's "no negative numbers".
fn count_at(l: &[u64], v: u64, i: usize, acc: u64) -> u64 {
    if i >= l.len() { acc }
    else if l[i] == v { count_at(l, v, i + 1, acc + 1) }
    else { count_at(l, v, i + 1, acc) }
}

fn check_at(l: &[u64], i: usize) -> bool {
    if i >= l.len() { true }
    else {
        if i + 1 < l.len() && l[i] > l[i + 1] { return false; }
        if count_at(l, l[i], 0, 0) > 2 { return false; }
        check_at(l, i + 1)
    }
}

pub fn is_sorted(lst: &[u64]) -> bool {
    check_at(lst, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known() {
        assert!(is_sorted(&[]));
        assert!(is_sorted(&[1, 2, 3]));
        assert!(is_sorted(&[1, 1, 2]));         // exactly 2 of 1
        assert!(!is_sorted(&[1, 1, 1]));        // 3 of 1
        assert!(!is_sorted(&[3, 2, 1]));
        assert!(is_sorted(&[1, 2, 2, 3]));
    }
}
