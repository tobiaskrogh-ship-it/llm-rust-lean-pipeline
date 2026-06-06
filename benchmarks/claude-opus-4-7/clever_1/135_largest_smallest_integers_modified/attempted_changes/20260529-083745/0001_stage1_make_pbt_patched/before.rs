/// HumanEval/136 / CLEVER 135 — `largest_smallest_integers(lst)`.
/// Returns `(a, b)` where `a` is the largest negative integer in `lst`
/// (or `None`), and `b` is the smallest positive integer in `lst` (or
/// `None`).  Zero counts as neither.
fn lneg_at(l: &[i64], i: usize, best: i64, found: bool) -> (i64, bool) {
    if i >= l.len() { (best, found) }
    else if l[i] < 0 && (!found || l[i] > best) { lneg_at(l, i + 1, l[i], true) }
    else { lneg_at(l, i + 1, best, found) }
}

fn spos_at(l: &[i64], i: usize, best: i64, found: bool) -> (i64, bool) {
    if i >= l.len() { (best, found) }
    else if l[i] > 0 && (!found || l[i] < best) { spos_at(l, i + 1, l[i], true) }
    else { spos_at(l, i + 1, best, found) }
}

pub fn largest_smallest_integers(lst: &[i64]) -> (Option<i64>, Option<i64>) {
    let (a, af) = lneg_at(lst, 0, 0, false);
    let (b, bf) = spos_at(lst, 0, 0, false);
    let aa = if af { Some(a) } else { None };
    let bb = if bf { Some(b) } else { None };
    (aa, bb)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known() {
        assert_eq!(largest_smallest_integers(&[2, 4, 1, 3, 5, 7]), (None, Some(1)));
        assert_eq!(largest_smallest_integers(&[]), (None, None));
        assert_eq!(largest_smallest_integers(&[0, 0]), (None, None));
        assert_eq!(largest_smallest_integers(&[-3, -2, -5, 6, 7]), (Some(-2), Some(6)));
    }
}
