/// HumanEval/121 / CLEVER 120 — `solution(lst)`.  Sum of all odd
/// elements at even indices.
fn sum_at(l: &[i64], i: usize, acc: i64) -> i64 {
    if i >= l.len() { acc }
    else if i % 2 == 0 && l[i] % 2 != 0 { sum_at(l, i + 1, acc + l[i]) }
    else { sum_at(l, i + 1, acc) }
}

pub fn solution(lst: &[i64]) -> i64 {
    sum_at(lst, 0, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known() {
        assert_eq!(solution(&[5, 8, 7, 1]), 12);   // 5 + 7
        assert_eq!(solution(&[3, 3, 3, 3, 3]), 9); // 3 + 3 + 3
        assert_eq!(solution(&[30, 13, 24, 321]), 0);
    }
}
