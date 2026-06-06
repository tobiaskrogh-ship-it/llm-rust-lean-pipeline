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
    use proptest::prelude::*;

    // Sanity unit test — fixed inputs, including edge values for `i64`.
    #[test]
    fn stub_returns_false_on_fixed_inputs() {
        assert!(!cycpattern_check(0, 0));
        assert!(!cycpattern_check(123, 456));
        assert!(!cycpattern_check(i64::MIN, i64::MAX));
        assert!(!cycpattern_check(i64::MAX, i64::MIN));
        assert!(!cycpattern_check(-1, 1));
    }

    proptest! {
        // The only contract clause for this degenerate stub:
        // for every pair of `i64` inputs the function totalises to `false`.
        // This single postcondition simultaneously captures:
        //   * totality (no panic / no overflow on any `i64`),
        //   * the constant-`false` return value,
        //   * input-independence (both arguments are ignored).
        #[test]
        fn always_returns_false(a in any::<i64>(), b in any::<i64>()) {
            prop_assert!(!cycpattern_check(a, b));
        }
    }
}
