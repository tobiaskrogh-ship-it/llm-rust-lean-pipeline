/// HumanEval/151 / CLEVER 149 — `double_the_difference(numbers)`.  Sum
/// of squares of the positive odd integers in `numbers`.  Negative
/// values are ignored.  (All inputs are already integers here.)
fn sum_at(l: &[i64], i: usize, acc: i64) -> i64 {
    if i >= l.len() { acc }
    else if l[i] > 0 && l[i] % 2 == 1 { sum_at(l, i + 1, acc + l[i] * l[i]) }
    else { sum_at(l, i + 1, acc) }
}

pub fn double_the_difference(numbers: &[i64]) -> i64 {
    sum_at(numbers, 0, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known() {
        assert_eq!(double_the_difference(&[]), 0);
        assert_eq!(double_the_difference(&[1, 3, 2, 0]), 10);     // 1 + 9
        assert_eq!(double_the_difference(&[-1, -2, 0]), 0);
        assert_eq!(double_the_difference(&[9, -2]), 81);
    }
}
