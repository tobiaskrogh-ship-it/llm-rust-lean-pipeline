/// HumanEval/122 / CLEVER 121 — `add_elements(arr, k)`.  Sum of the
/// elements among the first `k` of `arr` whose absolute value has at
/// most 2 decimal digits (i.e. `-99 ≤ v ≤ 99`).
fn sum_at(arr: &[i64], k: i64, i: i64, acc: i64) -> i64 {
    if i >= k || (i as usize) >= arr.len() { acc }
    else {
        let v = arr[i as usize];
        let abs_v = if v < 0 { -v } else { v };
        if abs_v <= 99 { sum_at(arr, k, i + 1, acc + v) }
        else { sum_at(arr, k, i + 1, acc) }
    }
}

pub fn add_elements(arr: &[i64], k: i64) -> i64 {
    if k <= 0 { 0 } else { sum_at(arr, k, 0, 0) }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known() {
        assert_eq!(add_elements(&[111, 21, 3, 4000, 5, 6, 7, 8, 9], 4), 24); // 21 + 3
        assert_eq!(add_elements(&[1, 2, 3, 4], 3), 6);
    }
}
