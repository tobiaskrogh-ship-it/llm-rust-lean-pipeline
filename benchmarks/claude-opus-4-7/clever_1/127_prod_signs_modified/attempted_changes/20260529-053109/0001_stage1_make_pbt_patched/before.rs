/// HumanEval/128 / CLEVER 127 — `prod_signs(arr)`.  Return `sum(|v|) *
/// product(sgn(v))` where `sgn(0) = 0`, `sgn(>0) = 1`, `sgn(<0) = -1`.
/// Return `None` for empty input.
fn run_at(arr: &[i64], i: usize, sum_abs: i64, sign: i64) -> i64 {
    if i >= arr.len() { sum_abs * sign }
    else {
        let v = arr[i];
        let av = if v < 0 { -v } else { v };
        let s = if v == 0 { 0 } else if v > 0 { 1 } else { -1 };
        run_at(arr, i + 1, sum_abs + av, sign * s)
    }
}

pub fn prod_signs(arr: &[i64]) -> Option<i64> {
    if arr.is_empty() { None } else { Some(run_at(arr, 0, 0, 1)) }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known() {
        assert_eq!(prod_signs(&[]), None);
        assert_eq!(prod_signs(&[1, 2, 2, -4]), Some(-9));    // (1+2+2+4)*-1
        assert_eq!(prod_signs(&[0, 1]), Some(0));            // 0 zeroes the sign
        assert_eq!(prod_signs(&[1, 1, 1]), Some(3));
    }
}
