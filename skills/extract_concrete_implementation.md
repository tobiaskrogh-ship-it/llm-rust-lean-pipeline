---
name: extract_concrete_implementation
description: Inline one function from a source Rust crate into a fresh self-contained crate, monomorphized to a concrete type, with the source's tests transferred.
---

## Goal

Take a function from a real-world Rust crate and produce a small standalone crate that contains the same function inlined, monomorphic to a single concrete type. The result must:

1. Compile and pass tests (`cargo test` exit 0, with at least one transferred test from the source).
2. Be self-contained: `[dependencies]` is empty.

That's the whole job.

## Available tools

- Built-in `Read`, `Grep`, `Glob` for inspection of the source crate
- `Bash` — flexible shell for ad-hoc inspection (`find`, `wc`, inline `python3 -c ...`) beyond what `Read`/`Grep`/`Glob` cover.
- `TodoWrite` — track multi-step extraction as a checklist; mark each off as you finish.
- `Agent` / `Task` — spawn a sub-agent for broad searches when a single Grep+Read loop won't cover it.
- `write_working_file` for creating new files
- `apply_file_patch_tool` for edits
- `run_cargo_test` to verify the new crate compiles and tests pass

## Working rules

### Inline, monomorphize, transfer tests

You may:

- **Monomorphize generics.** Replace every `<T: Trait>` with the concrete type from the prompt (default `u64` for unsigned-integer contexts, `i64` for signed). Replace `Self` accordingly. Replace `T::zero()`, `T::one()`, `T::MAX` with literal `0`, `1`, `<type>::MAX`.
- **Inline private helpers** the function calls. Copy each into `src/lib.rs` as a private function and monomorphize the same way.
- **Inline trait method calls** (`x.gcd(&y)` → the body of the impl for the concrete type, often inside a `macro_rules!` macro the source uses to generate per-type impls).
- **Inline external-crate methods** the function calls (e.g. when extracting `BigEndian::read_u32` from byteorder, copy the body of the matching `impl ByteOrder for BigEndian` block as a free `pub fn read_u32(...)`).
- **Drop `.clone()` on `Copy` types** and collapse `as Self` casts only when keeping them would prevent compilation.

That is the entire set of transformations available. Inlining a body verbatim is the default; the transformations above exist to make the inlining concrete and self-contained. Do not rewrite the algorithm itself.

### Transfer tests verbatim

Pull the source's tests into the new crate so `cargo test` actually verifies behavior. **Check all three places** — a function may have tests in one, several, or none of them:

1. **`#[cfg(test)] mod tests { ... }` blocks anywhere in `src/**.rs`** (not just `src/lib.rs`). Tests are often inside macros — read the macro definition and substitute manually for the concrete type.
2. **Doc-tests in the function's `///` doc-comment.** Every ` ``` ` block in a `///` comment is a runnable test. Transfer each as either (a) a regular `#[test] fn doctest_<n>() { ... }`, or (b) keep it in the doc-comment on the function in the new crate — `cargo test` runs both. Pick whichever is easier; if the doc-test uses method syntax (`x.foo()`) you'll have to either rewrite it to the free-function call (`foo(x)`) or convert to `#[test] fn`.
3. **Files in the source crate's `tests/` directory.** These are integration tests, often organized by module (e.g. `tests/bool.rs` for tests touching `src/bool.rs`). A single `#[test] fn` here can exercise *many* functions — `grep` the file for any call to the function you're extracting (method-call shape `x.foo(...)` or free-call shape `foo(...)`); transfer only the `#[test] fn` blocks (or assertions within them) that touch your function. If a test mixes your function with many others, copy just the relevant assertions into a new `#[test] fn`.

If after checking all three you find zero relevant tests, write a minimum of one trivial test exercising the function so `cargo test` has something to run.

For each transferred test:

- Monomorphize to the concrete type (replace `$T` macro params, generic-type method calls, `as $T` casts).
- Rewrite the call site: source uses method shape (`x.foo(args)`) or qualified path (`<source_crate>::foo(x, args)`); your local function is a free `pub fn foo(x, args)`. Update the call accordingly. Leave the test body and assertions otherwise unchanged.

Do not add new tests beyond what the source already has (except the single trivial test mentioned above when no source test exists).

Run `run_cargo_test` after each change and once at the end. Don't stop until the suite passes.

### Crate structure and Cargo.toml

Extracted crates live one per function under a folder named after the source crate:

```
benchmarks/code/<source-folder>/          # e.g. num-integer-0.1.46
├── <fn-name>_<type>/                     # one crate per extracted function
│   ├── Cargo.toml
│   └── src/lib.rs
├── <other-fn>_<type>/
│   └── ...
└── ...
```

The Cargo.toml is minimal:

```toml
[package]
name = "<fn-name>_<type>"
version = "0.1.0"
edition = "2024"

[package.metadata.extracted_from]
crate = "<source-crate-published-name>"      # e.g. "num-integer", "byteorder"
version = "<source-crate-version>"           # e.g. "0.1.46"
function = "<fn-name>"                       # e.g. "gcd"
type = "<concrete-type>"                     # e.g. "u64"
function_path = "<source_crate::path::to::fn>"   # e.g. "num_integer::gcd"
```

No `[dependencies]` section.

### When to stop and report instead

If the function genuinely can't be made self-contained by inlining (depends on an async runtime, `proc_macro` machinery, FFI bindings), or if the chosen concrete type is fundamentally wrong for the function's domain (`u64` for a function operating on strings / slices of arbitrary `T`), **stop and report** without creating the destination.

If a transferred test exercises behavior that requires inlining a function transitively forever, drop just that one test with a one-line note. Don't drop the function.

## Final output

One paragraph:

- Path of the new crate
- Source function file:line
- Private helpers inlined (and from where)
- Any tests you couldn't transfer (with one-line reason each)
- Any function you couldn't extract (with one-line reason)
