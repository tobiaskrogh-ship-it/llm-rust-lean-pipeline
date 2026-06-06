/// HumanEval/146 / CLEVER 144 — `specialFilter(nums)`.  Count elements
/// > 10 whose first AND last decimal digits are both odd (1, 3, 5, 7, 9).
fn first_digit_at(n: i64) -> i64 {
    if n < 10 { n } else { first_digit_at(n / 10) }
}

fn count_at(l: &[i64], i: usize, acc: i64) -> i64 {
    if i >= l.len() { acc }
    else {
        let v = l[i];
        if v > 10 {
            let first = first_digit_at(v);
            let last = v % 10;
            if first % 2 == 1 && last % 2 == 1 {
                count_at(l, i + 1, acc + 1)
            } else { count_at(l, i + 1, acc) }
        } else { count_at(l, i + 1, acc) }
    }
}

#[allow(non_snake_case)]
pub fn specialFilter(nums: &[i64]) -> i64 {
    count_at(nums, 0, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known() {
        assert_eq!(specialFilter(&[15, -73, 14, -15]), 1);   // 15 only
        assert_eq!(specialFilter(&[33, -2, -3, 45, 21, 109]), 2); // 33, 45
        assert_eq!(specialFilter(&[]), 0);
    }
}
