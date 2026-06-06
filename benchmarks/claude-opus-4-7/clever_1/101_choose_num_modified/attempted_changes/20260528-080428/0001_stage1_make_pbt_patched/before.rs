/// HumanEval/102 / CLEVER 101 — `choose_num(x, y)`.  Return the largest
/// even integer in `[x, y]`, or `-1` if there is none.  Returns -1 if
/// `x > y`.  i64 chosen because of the -1 sentinel.
pub fn choose_num(x: i64, y: i64) -> i64 {
    if x > y { -1 }
    else if y % 2 == 0 { y }
    else if y - 1 >= x { y - 1 }
    else { -1 }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known() {
        assert_eq!(choose_num(12, 15), 14);
        assert_eq!(choose_num(13, 12), -1);
        assert_eq!(choose_num(0, 0), 0);
        assert_eq!(choose_num(1, 1), -1);
    }
}
