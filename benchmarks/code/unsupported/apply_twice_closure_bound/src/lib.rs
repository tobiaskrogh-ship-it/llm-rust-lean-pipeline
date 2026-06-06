//! Unsupported: closure trait bound `F: Fn(T) -> T`.
//! Triggers `[HAX0001] Unsupported equality constraints on associated
//! types of parent trait` (hax#1923). `Fn(T) -> T` desugars to
//! `Fn<(T,), Output = T>`; the `Output = T` equality lives on
//! `FnOnce` (parent of `Fn`) and the Lean printer cannot emit it.

pub fn apply_twice<T, F>(x: T, f: F) -> T
where
    T: Copy,
    F: Fn(T) -> T,
{
    f(f(x))
}
