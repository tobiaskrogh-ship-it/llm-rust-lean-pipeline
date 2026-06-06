/// CLEVER 128 — `split_words(txt)`.  The canonical CLEVER signature is
/// `pub fn split_words(txt: i64) -> i64`, which has no relationship to
/// the HumanEval/128 string-splitting problem.  No faithful integer
/// implementation exists; returning `txt` unchanged as a degenerate
/// stub.  Flagged upstream in CLEVER's prompt set.
pub fn split_words(txt: i64) -> i64 {
    txt
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    // Concrete sanity checks pinning a few representative points of the
    // i64 domain, including the boundaries where a buggy implementation
    // (e.g. one that overflowed via negation or saturating arithmetic)
    // would most plausibly diverge from the identity contract.
    #[test]
    fn stub_identity_boundaries() {
        assert_eq!(split_words(0), 0);
        assert_eq!(split_words(42), 42);
        assert_eq!(split_words(-1), -1);
        assert_eq!(split_words(i64::MAX), i64::MAX);
        assert_eq!(split_words(i64::MIN), i64::MIN);
    }

    proptest! {
        // Postcondition: split_words is the identity on i64.
        //
        // This is the entire contract of the stub: the function is total
        // (no precondition), never fails (no panic / overflow path), and
        // returns its input unchanged. Any independent claim about the
        // result — sign, magnitude, parity, involution, monotonicity —
        // is a derived consequence of identity and would not catch any
        // bug that the identity check itself misses, so it is omitted.
        #[test]
        fn prop_returns_input_unchanged(txt in any::<i64>()) {
            prop_assert_eq!(split_words(txt), txt);
        }
    }
}
