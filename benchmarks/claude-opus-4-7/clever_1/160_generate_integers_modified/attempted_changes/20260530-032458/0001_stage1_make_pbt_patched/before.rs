/// HumanEval/163 / CLEVER 160 — `generate_integers(a, b)`.  Return the
/// even single-digit integers (0, 2, 4, 6, 8) in `[min(a, b), max(a, b)]`,
/// in ascending order.
fn build_at(lo: u64, hi: u64, k: u64, mut acc: Vec<u64>) -> Vec<u64> {
    if k > hi || k > 8 { acc }
    else {
        if k >= lo && k % 2 == 0 {
            acc.push(k);
        }
        build_at(lo, hi, k + 1, acc)
    }
}

pub fn generate_integers(a: u64, b: u64) -> Vec<u64> {
    let lo = if a < b { a } else { b };
    let hi = if a < b { b } else { a };
    build_at(lo, hi, 0, Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known() {
        assert_eq!(generate_integers(2, 8), vec![2, 4, 6, 8]);
        assert_eq!(generate_integers(8, 2), vec![2, 4, 6, 8]);
        assert_eq!(generate_integers(10, 14), vec![]);
        assert_eq!(generate_integers(0, 0), vec![0]);
    }
}
