/// Return sorted unique elements of `l`. (Return type widened to
/// `Vec<i64>` to match the docstring; CLEVER auto-defaulted to `i64`.)
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

fn sort_at(l: &[i64], i: usize, acc: Vec<i64>) -> Vec<i64> {
    if i >= l.len() {
        acc
    } else {
        sort_at(l, i + 1, insert_sorted(acc, l[i]))
    }
}

fn dedupe_at(sorted: &[i64], i: usize, mut acc: Vec<i64>) -> Vec<i64> {
    if i >= sorted.len() {
        acc
    } else if i == 0 || sorted[i] != sorted[i - 1] {
        acc.push(sorted[i]);
        dedupe_at(sorted, i + 1, acc)
    } else {
        dedupe_at(sorted, i + 1, acc)
    }
}

pub fn unique(l: &[i64]) -> Vec<i64> {
    let sorted = sort_at(l, 0, Vec::new());
    dedupe_at(&sorted, 0, Vec::new())
}
