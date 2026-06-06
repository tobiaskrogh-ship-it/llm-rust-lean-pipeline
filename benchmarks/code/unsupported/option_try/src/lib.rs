//! Unsupported (likely): the `?` operator desugaring through the `Try`
//! trait. `Try` has an associated `Output` and `Residual` on a parent
//! trait, which surfaces another variant of the parent-trait
//! associated-type-equality issue (hax#1923).

pub fn sum_options(a: Option<u64>, b: Option<u64>) -> Option<u64> {
    let x = a?;
    let y = b?;
    Some(x + y)
}
