// unsupported: a function that RETURNS `impl FnMut(...) -> T` (i.e. returns a
// closure) — Hax's Lean printer fails with
//   error: [HAX0001] something is not implemented yet.
//   Unsupported equality constraints on associated types of parent trait
//   (https://github.com/hacspec/hax/issues/1923)
// because `FnMut` (and `Fn`) extends `FnOnce`, whose `Output` associated type
// produces an equality constraint `FnOnce::Output = T` that the Lean printer
// does not yet handle.
//
// Distinction from sibling patterns:
//   * `assoc_type_equality_on_parent.rs` fixes the same HAX0001 by replacing
//     an `impl Fn*(X) -> Y` *parameter* with a `fn(X) -> Y` pointer. That fix
//     does NOT generalise to the *return type*: a closure (the only way to
//     produce a value of `impl FnMut(...)`) cannot be coerced to a `fn(...)`
//     pointer if it captures any state, and even a non-capturing closure
//     coerced to `fn(...)` would change the public API in ways tests may
//     not tolerate.
//   * `iter_fold_to_while_loop.rs` fixes the same HAX0001 on helpers that
//     return `impl FnMut(...)` by *deleting* the helper and inlining the
//     fold at the call site. That fix does NOT apply when the helper IS the
//     public API and downstream tests call it directly — there is no call
//     site to inline into.
//   * `impl_fn_once_anonymous_generic.rs` addresses a different failure
//     mode (lake-build identifier mangling like `impl_FnOnce()_-__u64`) by
//     replacing anonymous `impl Trait` with a named generic `F: Trait`.
//     That rewrite does NOT help here: named generics produce the identical
//     HAX0001 error on the same line range, because the issue is the parent
//     trait `FnOnce::Output` equality, not the type-parameter spelling.
//
// Verified failure mode (this crate, May 2026):
//   pub fn map_fold(
//       mut f: impl FnMut(u64) -> u64,
//       mut g: impl FnMut(u64, u64) -> u64,
//   ) -> impl FnMut(u64, u64) -> u64 {
//       move |acc, elt| g(acc, f(elt))
//   }
// and the named-generic rewrite
//   pub fn map_fold<F, G>(mut f: F, mut g: G) -> impl FnMut(u64, u64) -> u64
//   where F: FnMut(u64) -> u64, G: FnMut(u64, u64) -> u64 { ... }
// BOTH produce:
//   error: [HAX0001] Unsupported equality constraints on associated types
//   of parent trait
//   Note: the error was labeled with context `Lean Printer`.
//
// No source-level fix preserves both the test contract AND fixes Hax. The
// crate's tests use closures capturing `&Cell<u64>` (interior-mutable
// counters that observe per-call invocation counts of `f` and `g`), which
// cannot be coerced to `fn(...)` pointers. Any rewrite that replaces the
// closure parameters with `fn(...)` pointers breaks those tests.
//
// before  (no working "after" — flag as Hax-degenerate and stop)
//
// pub fn map_fold(
//     mut f: impl FnMut(u64) -> u64,
//     mut g: impl FnMut(u64, u64) -> u64,
// ) -> impl FnMut(u64, u64) -> u64 {
//     move |acc, elt| g(acc, f(elt))
// }
//
// Recommended handling:
//   1. Leave the Rust source unchanged.
//   2. Report the HAX0001 error in the stage's final output and stop —
//      `lake build` cannot proceed because extraction itself failed
//      (the extracted file's body is `(pure sorry)`).
//   3. The proof stage must treat `map_fold` as having no usable extracted
//      definition. The natural workaround is to model `map_fold f g` in
//      Lean directly as the pointwise composition `fun acc elt => g acc (f elt)`,
//      bypassing Hax's failed extraction, and prove the contract against
//      that hand-written model. This is upstream of Hax issue #1923.
