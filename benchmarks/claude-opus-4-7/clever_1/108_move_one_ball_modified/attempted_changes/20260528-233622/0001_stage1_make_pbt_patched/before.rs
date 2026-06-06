/// HumanEval/109 / CLEVER 108 — `move_one_ball(arr)`.  Can `arr` be
/// sorted in non-decreasing order via right rotations?  Empty list
/// returns true.  Spec assumes distinct elements but the algorithm
/// works generally.
fn is_sorted_split_at(l: &[i64], k: usize, i: usize) -> bool {
    let n = l.len();
    if i + 1 >= n { true }
    else {
        let a = l[(i + k) % n];
        let b = l[(i + 1 + k) % n];
        if a > b { false } else { is_sorted_split_at(l, k, i + 1) }
    }
}

fn try_at(l: &[i64], k: usize) -> bool {
    if k >= l.len() { false }
    else if is_sorted_split_at(l, k, 0) { true }
    else { try_at(l, k + 1) }
}

pub fn move_one_ball(arr: &[i64]) -> bool {
    if arr.is_empty() { true } else { try_at(arr, 0) }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known() {
        assert!(move_one_ball(&[]));
        assert!(move_one_ball(&[3, 4, 5, 1, 2]));   // shift by 2
        assert!(move_one_ball(&[1, 2, 3]));
        assert!(!move_one_ball(&[3, 5, 4, 1, 2]));
    }
}
