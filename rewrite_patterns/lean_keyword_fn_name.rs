// unsupported: a Rust item name that is a Lean keyword — e.g. `then`,
// `else`, `match`, `let`, `do`, `fun`, `where`, `if`, `by`. Hax extracts
// the function as `def <fn-name> ...` in Lean, and Lean's parser rejects
// the keyword in identifier position. `cargo hax into lean` succeeds, but
// `lake build` fails with e.g.:
//     error: <file>.lean:NN:C: unexpected token 'then'; expected identifier
// Workaround: rename the Rust item to a non-keyword (typically a
// descriptive `<name>_some` / `<name>_value` / `<name>_impl` form) and
// add a `pub use self::<new> as <old>;` re-export so call sites in the
// rest of the crate — including `#[cfg(test)] mod tests { use super::*; }`
// — keep compiling unchanged. The re-export is a Rust-level alias and is
// invisible to Hax, so only the keyword-free `def <new>` is extracted.

// before

/// Returns `Some(f())` if `b` is `true`, or `None` otherwise.
#[inline]
pub fn then<F: FnOnce() -> u64>(b: bool, f: F) -> Option<u64> {
    if b { Some(f()) } else { None }
}

// after

/// Returns `Some(f())` if `b` is `true`, or `None` otherwise.
//
// `then` is a Lean keyword (used in `if _ then _ else _`), so Hax's
// emitted `def then` is rejected by `lake build`. Rename to a
// non-keyword and re-export under the original name so test/call sites
// stay unchanged.
#[inline]
pub fn then_some<F: FnOnce() -> u64>(b: bool, f: F) -> Option<u64> {
    if b { Some(f()) } else { None }
}

pub use self::then_some as then;
