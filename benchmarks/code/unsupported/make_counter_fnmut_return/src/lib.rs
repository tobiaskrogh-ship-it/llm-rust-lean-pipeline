//! Unsupported: returning `impl FnMut() -> T` that captures local state.
//! Same family as `apply_twice_closure_bound`, but on the return side:
//! the function returns an anonymous type bounded by `FnMut() -> u64`,
//! which carries an associated-type equality the Lean printer cannot emit.
//! A capturing closure cannot be replaced by a `fn` pointer (see
//! `rewrite_patterns/return_impl_fnmut_unfixable.rs`).

pub fn make_counter(start: u64) -> impl FnMut() -> u64 {
    let mut n = start;
    move || {
        let cur = n;
        n += 1;
        cur
    }
}
