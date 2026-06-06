//! Unsupported: higher-ranked trait bound (HRTB) `for<'a> Fn(&'a T) -> &'a T`.
//! Quantifies a closure trait bound over a lifetime parameter. Hax erases
//! lifetimes and has no HRTB encoding in the Lean printer.

pub fn pick<F>(f: F) -> u64
where
    F: for<'a> Fn(&'a u64) -> &'a u64,
{
    *f(&7)
}
