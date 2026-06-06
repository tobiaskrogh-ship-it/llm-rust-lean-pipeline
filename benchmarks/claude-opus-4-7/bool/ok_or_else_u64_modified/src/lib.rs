//! Extracted from `core::bool` — inlined `bool::ok_or_else`, monomorphized to `u64`.

/// Returns `Ok(())` if `b` is `true`, or `Err(f())` otherwise.
#[inline]
pub fn ok_or_else<F: FnOnce() -> u64>(b: bool, f: F) -> Result<(), u64> {
    if b { Ok(()) } else { Err(f()) }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Representative `u64` inputs: zero, small typical values, a mid-range
    /// value, and the boundary at `u64::MAX`. These stand in for the universal
    /// quantifier "forall v: u64" in the property tests below — `ok_or_else`
    /// performs no arithmetic on `v`, so any non-monotonic edge cases would
    /// have to come from the boundary itself.
    const SAMPLES: [u64; 8] = [
        0,
        1,
        2,
        42,
        1u64 << 32,
        u64::MAX / 2,
        u64::MAX - 1,
        u64::MAX,
    ];

    /// Postcondition (success branch).
    /// `b == true` ⟹ result is `Ok(())`. The value the closure *would* return
    /// is irrelevant on this branch — the success result carries no payload —
    /// so we vary the closure's body across `SAMPLES` to ensure the result
    /// does not accidentally depend on it.
    #[test]
    fn true_branch_returns_ok_regardless_of_closure_value() {
        for &v in SAMPLES.iter() {
            assert_eq!(ok_or_else(true, || v), Ok(()));
        }
    }

    /// Postcondition (failure branch).
    /// `b == false` ⟹ result is `Err(v)`, where `v` is *exactly* the closure's
    /// return value — no transformation, clamping, masking, or substitution.
    /// This is the value-forwarding contract; a buggy implementation that
    /// returned, say, `Err(0)` or `Err(v.wrapping_add(1))` would still satisfy
    /// the weaker "is_err() iff !b" claim but would fail here.
    #[test]
    fn false_branch_forwards_closure_value_verbatim() {
        for &v in SAMPLES.iter() {
            assert_eq!(ok_or_else(false, || v), Err(v));
        }
    }

    /// Closure-call semantics — independent of the result value.
    /// `b == true`  ⟹ `f` is invoked 0 times (laziness on the success path).
    /// `b == false` ⟹ `f` is invoked exactly once (not zero, not twice).
    /// A buggy implementation could produce a correct `Result` while still
    /// evaluating `f` on the success path, or evaluating it twice on the
    /// failure path; neither would be caught by the postcondition tests above,
    /// so this is a genuinely independent contract clause.
    #[test]
    fn closure_called_exactly_once_iff_false() {
        let mut count_true = 0u32;
        let _ = ok_or_else(true, || {
            count_true += 1;
            0u64
        });
        assert_eq!(count_true, 0, "closure must not run when b == true");

        let mut count_false = 0u32;
        let _ = ok_or_else(false, || {
            count_false += 1;
            0u64
        });
        assert_eq!(count_false, 1, "closure must run exactly once when b == false");
    }
}
