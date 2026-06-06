/// HumanEval/152 / CLEVER 150 — `compare(scores, guesses)`.  For each
/// position `i`, return `|scores[i] - guesses[i]|`.  Output length is
/// `min(len(scores), len(guesses))`.
fn build_at(s: &[i64], g: &[i64], i: usize, mut acc: Vec<i64>) -> Vec<i64> {
    if i >= s.len() || i >= g.len() { acc }
    else {
        let d = if s[i] >= g[i] { s[i] - g[i] } else { g[i] - s[i] };
        acc.push(d);
        build_at(s, g, i + 1, acc)
    }
}

pub fn compare(scores: &[i64], guesses: &[i64]) -> Vec<i64> {
    build_at(scores, guesses, 0, Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known() {
        assert_eq!(compare(&[1, 2, 3, 4, 5, 1], &[1, 2, 3, 4, 2, -2]), vec![0, 0, 0, 0, 3, 3]);
        assert_eq!(compare(&[0, 5, 0, 0, 0, 4], &[4, 1, 1, 0, 0, -2]), vec![4, 4, 1, 0, 0, 6]);
    }
}
