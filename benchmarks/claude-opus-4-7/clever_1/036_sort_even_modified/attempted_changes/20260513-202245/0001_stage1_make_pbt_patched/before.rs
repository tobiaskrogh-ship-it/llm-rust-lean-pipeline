/// Return a list identical to `l` at odd indices, with values at even
/// indices replaced by those same values in ascending order. (Return type
/// widened to `Vec<i64>` to match the docstring.)
fn insert_sorted(v: Vec<i64>, x: i64) -> Vec<i64> {
    let mut result: Vec<i64> = Vec::new();
    let n = v.len();
    let mut i: usize = 0;
    let mut inserted = false;
    while i < n {
        if !inserted && v[i] >= x {
            result.push(x);
            inserted = true;
        }
        result.push(v[i]);
        i += 1;
    }
    if !inserted {
        result.push(x);
    }
    result
}

fn collect_evens(l: &[i64], i: usize, acc: Vec<i64>) -> Vec<i64> {
    if i >= l.len() {
        acc
    } else if i % 2 == 0 {
        collect_evens(l, i + 1, insert_sorted(acc, l[i]))
    } else {
        collect_evens(l, i + 1, acc)
    }
}

fn rebuild_at(l: &[i64], sorted: &[i64], i: usize, j: usize, mut acc: Vec<i64>) -> Vec<i64> {
    if i >= l.len() {
        acc
    } else if i % 2 == 0 {
        acc.push(sorted[j]);
        rebuild_at(l, sorted, i + 1, j + 1, acc)
    } else {
        acc.push(l[i]);
        rebuild_at(l, sorted, i + 1, j, acc)
    }
}

pub fn sort_even(l: &[i64]) -> Vec<i64> {
    let sorted = collect_evens(l, 0, Vec::new());
    rebuild_at(l, &sorted, 0, 0, Vec::new())
}
