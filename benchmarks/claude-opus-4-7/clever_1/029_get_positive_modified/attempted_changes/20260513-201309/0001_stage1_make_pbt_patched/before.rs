/// Return only the strictly positive (> 0) numbers from `l`, in input order.
/// (Return type widened from CLEVER's auto-defaulted `i64` to `Vec<i64>` to
/// match the docstring's "Return only positive numbers in the list".)
fn collect_at(l: &[i64], i: usize, mut acc: Vec<i64>) -> Vec<i64> {
    if i >= l.len() {
        acc
    } else if l[i] > 0 {
        acc.push(l[i]);
        collect_at(l, i + 1, acc)
    } else {
        collect_at(l, i + 1, acc)
    }
}

pub fn get_positive(l: &[i64]) -> Vec<i64> {
    collect_at(l, 0, Vec::new())
}
