/// HumanEval/145 / CLEVER 143 — `order_by_points(nums)`.  Stable-sort
/// `nums` ascending by the sum of their signed digits (where for
/// negative `n`, the first digit takes the sign).  Ties preserve the
/// original order.
fn first_digit_at(n: i64) -> i64 {
    if n < 10 { n } else { first_digit_at(n / 10) }
}
fn digit_sum_at(n: i64, acc: i64) -> i64 {
    if n == 0 { acc } else { digit_sum_at(n / 10, acc + n % 10) }
}
fn signed_digit_sum(n: i64) -> i64 {
    if n == 0 { 0 }
    else if n > 0 { digit_sum_at(n, 0) }
    else { let m = -n; digit_sum_at(m, 0) - 2 * first_digit_at(m) }
}

fn insert_stable(v: Vec<i64>, x: i64) -> Vec<i64> {
    let kx = signed_digit_sum(x);
    let mut r: Vec<i64> = Vec::new();
    let mut i = 0usize;
    let mut done = false;
    while i < v.len() {
        // Insert x before the first element with a strictly greater key.
        if !done && signed_digit_sum(v[i]) > kx { r.push(x); done = true; }
        r.push(v[i]); i += 1;
    }
    if !done { r.push(x); }
    r
}

fn sort_at(l: &[i64], i: usize, s: Vec<i64>) -> Vec<i64> {
    if i >= l.len() { s } else { sort_at(l, i + 1, insert_stable(s, l[i])) }
}

pub fn order_by_points(nums: &[i64]) -> Vec<i64> {
    sort_at(nums, 0, Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known() {
        // ds: 1→1, 11→2, -1→-1, -11→(-1+1)=0, 0→0
        // sorted asc, stable: -1(-1), then ties at 0 in input order (-11, 0),
        // then 1, then 11.
        assert_eq!(order_by_points(&[1, 11, -1, -11, 0]), vec![-1, -11, 0, 1, 11]);
    }
}
