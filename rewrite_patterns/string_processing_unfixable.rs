// unsupported: any function whose public signature pins `&str` / `String` /
// `Vec<String>` and whose body performs character iteration or string
// construction. The Hax Lean prelude (`Hax/core_models/epilogue/string.lean`)
// defines `alloc.string.String` as a bare type abbreviation with **zero**
// operations — no constructor, no mutation, no conversion. The companion
// gaps in adjacent namespaces compound this:
//
//   - `alloc.string.Impl.new`     (String::new)     — undefined
//   - `alloc.string.Impl.push`    (String::push)    — undefined
//   - `alloc.string.Impl.clear`   (String::clear)   — undefined
//   - `alloc.string.Impl.from_utf8` (String::from_utf8) — undefined
//   - `core_models.str.Impl.chars`     (&str::chars)     — undefined
//   - `core_models.str.Impl.as_bytes`  (&str::as_bytes)  — undefined
//   - `core_models.str.iter.Chars`     (the Chars iter type) — undefined
//   - `core_models.iter.traits.iterator.Iterator.fold` (extraction target
//     for `for c in s.chars()`) — undefined
//   - `alloc.vec.Impl_1.push`     (Vec::push)        — undefined
//   - `core_models.clone.Clone.clone` instantiated at String — undefined
//   - `Cast u8 Char` typeclass instance — missing
//   - `PartialEq Char` instance — missing
//
// `Hax.core_models.epilogue.alloc` does model `Vec::new`, `Vec::len`, and
// `Vec::extend_from_slice`, but NOT `Vec::push`. So even building a
// `Vec<T>` element-by-element is outside the modeled fragment.
//
// Distinction from sibling patterns:
//   * `f64_signature_to_i64.rs` covers a similar shape — a public signature
//     pinned to an unmodeled primitive type (`f64`) — but offers a real
//     rewrite (translate the signature to `i64`). String signatures do not
//     have an analogous integer fallback: the test contract typically
//     uses `String::concat` / `.chars().filter()` / interleaved space
//     insertion, none of which can be retargeted to bytes or integers
//     without rewriting the tests (which the rules forbid).
//   * `iter_chain_to_recursion.rs` and `iter_fold_to_while_loop.rs` cover
//     iterator chains over slices and ranges — the rewrites use index-based
//     `while` / recursion, which works because `&[u8]` / `Range` are
//     modeled. The same trick does not work on `&str` because
//     `&str::as_bytes` itself is unmodeled, and even with bytes in hand the
//     output container `Vec<String>` cannot be populated (`Vec::push` and
//     `String::new` / `String::push` are all missing).
//   * `return_impl_fnmut_unfixable.rs` is the canonical "no source-level
//     fix" pattern for HAX0001 issues with closure-return types. This
//     pattern follows the same shape but for string-processing functions.
//
// Verified failure mode (this crate, May 2026):
//
//   pub fn separate_paren_groups(paren_string: &str) -> Vec<String> {
//       let mut result: Vec<String> = Vec::new();
//       let mut current = String::new();
//       let mut depth: i64 = 0;
//       for c in paren_string.chars() {
//           if c == ' ' { continue; }
//           if c == '(' { depth += 1; current.push(c); }
//           else if c == ')' {
//               depth -= 1; current.push(c);
//               if depth == 0 { result.push(current.clone()); current.clear(); }
//           }
//       }
//       result
//   }
//
// `cargo hax into lean` extracts cleanly. `lake build` then fails with:
//   error: Unknown identifier `alloc.string.Impl.new`
//   error: Unknown identifier `core_models.str.Impl.chars`
//   error: Unknown identifier `core_models.str.iter.Chars`
//   error: Unknown constant   `core_models.iter.traits.iterator.Iterator.fold`
//   error: Invalid `⟨...⟩` notation (cascade from the missing fold's tuple state)
//   warning: declaration uses `sorry`
//
// Attempted rewrite — convert the for-loop to a byte-indexed while loop —
// strictly increased the error count (12 vs 5). It removed the
// `Iterator.fold` / `Chars` errors but introduced
// `core_models.str.Impl.as_bytes`, `Cast u8 Char`, and `PartialEq Char`
// gaps on top of the same `String::new` / `String::push` / `Vec::push` /
// `Clone::clone` gaps. There is no Rust-side rewrite that preserves the
// `&str -> Vec<String>` signature AND removes every unmodeled identifier
// from the body. The closest one could come is to maintain `Vec<(usize,
// usize)>` of group boundaries — but the function must return
// `Vec<String>`, and there is no Hax-modeled way to construct a `String`
// value at all.
//
// before  (no working "after" — flag as Hax-degenerate and stop)
//
// pub fn separate_paren_groups(paren_string: &str) -> Vec<String> { ... }
//
// Recommended handling:
//   1. Leave the Rust source as-is (the natural for-loop / String-building
//      form, which is clean Rust and matches the test contract).
//   2. Report the unmodeled identifiers in the stage's final output and
//      stop — `lake build` cannot succeed because the extracted Lean
//      references symbols the Hax prelude does not provide.
//   3. The proof stage must treat `separate_paren_groups` as having no
//      usable extracted definition. The natural workaround is to model
//      the function in Lean directly as a recursive function over
//      `List Char` (with an explicit `String -> List Char` axiom for the
//      input bridge and a `List String -> List String` identity for the
//      output), and prove the contract — concat / balanced / primitive
//      / space-invariant — against that hand-written model. This is
//      upstream of the Hax prelude's missing string operations.
