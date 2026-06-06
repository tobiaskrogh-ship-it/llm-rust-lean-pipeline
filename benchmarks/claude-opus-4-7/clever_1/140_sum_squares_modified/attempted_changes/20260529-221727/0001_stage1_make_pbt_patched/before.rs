/// HumanEval/142 / CLEVER 140 — `sum_squares(lst)`.  Sum the elements
/// after transforming: square if index `i % 3 == 0`; cube if `i % 4 == 0`
/// and not `i % 3 == 0`; otherwise unchanged.
fn sum_at(l: &[i64], i: usize, acc: i64) -> i64 {
    if i >= l.len() { acc }
    else {
        let v = l[i];
        let term = if i % 3 == 0 { v * v }
                   else if i % 4 == 0 { v * v * v }
                   else { v };
        sum_at(l, i + 1, acc + term)
    }
}

pub fn sum_squares(lst: &[i64]) -> i64 {
    sum_at(lst, 0, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known() {
        // index 0: 1² = 1; 1: 2; 2: 3; 3: 16; 4: 5³ = 125; 5: 6; 6: 49; 7: 8
        // sum: 1 + 2 + 3 + 16 + 125 + 6 + 49 + 8 = 210
        assert_eq!(sum_squares(&[1, 2, 3, 4, 5, 6, 7, 8]), 210);
        assert_eq!(sum_squares(&[]), 0);
        // index 0: 5² = 25
        assert_eq!(sum_squares(&[5]), 25);
    }
}
