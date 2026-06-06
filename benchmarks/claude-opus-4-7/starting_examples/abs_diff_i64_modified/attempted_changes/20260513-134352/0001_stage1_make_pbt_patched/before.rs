/// Absolute difference of two signed integers.
///
/// Minimal demonstration of the conditional-subtraction pattern that avoids
/// `i64::abs` (unmodeled in the Hax Lean prelude) and `-i64::MIN` (which
/// would overflow). The proof obligation is:
///   - if branch `a > b`: show `a -? b = pure (a - b)` (no signed overflow).
///   - else branch:       show `b -? a = pure (b - a)` (no signed overflow).
/// Both subtractions are bounded by the branch condition, so the overflow
/// obligation discharges from the hypothesis.
pub fn abs_diff(a: i64, b: i64) -> i64 {
    if a > b {
        a - b
    } else {
        b - a
    }
}
