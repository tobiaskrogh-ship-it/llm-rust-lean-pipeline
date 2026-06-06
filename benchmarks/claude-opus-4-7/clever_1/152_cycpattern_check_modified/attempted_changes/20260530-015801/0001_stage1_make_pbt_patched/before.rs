/// CLEVER 152 — `cycpattern_check(a, b)`.  The canonical CLEVER
/// signature is `pub fn cycpattern_check(String a: i64, String b: i64)
/// -> bool`, which is syntactically broken Rust (mixes `String` and
/// `i64`).  The HumanEval problem is string-based (test whether any
/// rotation of `b` is a substring of `a`); no faithful integer
/// adaptation exists.  Returning `false` as a degenerate stub;
/// flagged upstream in CLEVER's prompt set.
pub fn cycpattern_check(a: i64, b: i64) -> bool {
    let _ = a;
    let _ = b;
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn stub_returns_false() {
        assert!(!cycpattern_check(0, 0));
        assert!(!cycpattern_check(123, 456));
    }
}
