/// Return the maximum element in the list. For the empty list, returns 0.
fn max_at(l: &[i64], i: usize, m: i64) -> i64 {
    if i >= l.len() {
        m
    } else if l[i] > m {
        max_at(l, i + 1, l[i])
    } else {
        max_at(l, i + 1, m)
    }
}

pub fn max_element(l: &[i64]) -> i64 {
    if l.is_empty() {
        0
    } else {
        max_at(l, 1, l[0])
    }
}
