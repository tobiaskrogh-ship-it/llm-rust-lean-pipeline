/// HumanEval/135 / CLEVER 134 — `can_arrange(arr)`.  Return the largest
/// index `i` such that `arr[i] <= arr[i-1]`, or `-1` if no such index
/// exists.  Note the spec says "not greater than or equal to the
/// element immediately preceding it" → arr[i] < arr[i-1].  i64 because
/// of the -1 sentinel.
fn scan_at(arr: &[i64], i: usize, best: i64) -> i64 {
    if i >= arr.len() { best }
    else if arr[i] < arr[i - 1] { scan_at(arr, i + 1, i as i64) }
    else { scan_at(arr, i + 1, best) }
}

pub fn can_arrange(arr: &[i64]) -> i64 {
    if arr.len() < 2 { -1 } else { scan_at(arr, 1, -1) }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known() {
        assert_eq!(can_arrange(&[1, 2, 4, 3, 5]), 3);
        assert_eq!(can_arrange(&[1, 2, 3]), -1);
        assert_eq!(can_arrange(&[]), -1);
        assert_eq!(can_arrange(&[5]), -1);
    }
}
