---
name: generate_property_based_tests
description: Generate property-based tests for a crate in Rust based on the provided crate.
---

## Goal

Generate property-based tests that capture the function's **contract**:

- when the function may be called (preconditions on inputs),
- what value it returns when called validly (postconditions),
- when and how it fails (panic / `Option::None` / `Result::Err` / overflow conditions).

Add the tests to `src/lib.rs` in a `#[cfg(test)] mod tests { ... }` block.

## Available tools

- Built-in `Read`, `Grep`, `Glob` for inspection (read files, search content, find paths)
- `Bash` — flexible shell for ad-hoc inspection (`find`, `wc`, inline `python3 -c ...`) beyond what `Read`/`Grep`/`Glob` cover.
- `TodoWrite` — track each property test you're writing as a checklist; mark off as `run_cargo_test` confirms it.
- `Agent` / `Task` — spawn a sub-agent for broad searches when a single Grep+Read loop won't cover it.
- `apply_file_patch_tool` for edits to existing files
- `write_working_file` for creating new files
- `run_cargo_test` to verify the suite

## Working rules

- **Aim for a small, focused suite.** A handful of tests that pin down the contract is better than a long list of tests that pin down derived properties. These tests will be turned into proof obligations downstream — every extra test means an extra theorem to prove.
- **Don't test derived mathematical facts about the result.** If the function returns `x * x`, don't separately test parity preservation, monotonicity, quadratic-residue identities, non-contraction, etc. — those follow from properties of multiplication and don't tell you anything new about the implementation. The same applies to commutativity, associativity, and other algebraic identities of well-known operations on the result.
- **Do test independent semantic claims.** For functions where multiple distinct properties are part of the contract (e.g. `gcd` returns *the greatest* common divisor, not just *a* common divisor — the "greatest" part is independent of the "common divisor" part), each independent claim deserves its own test.
- A useful sanity check: ask "would a buggy implementation that produces a different valid output, or that misbehaves on edge cases, be caught by this test?" If yes, the test is earning its place. If the test would still pass on any implementation that returns the correct value, it's redundant.
- **Assume the provided implementation is correct** When you have added the property tests, use `run_cargo_test` to verify that the crate still passes. If the tests don't pass, then something is wrong with the tests, not the implementation.

## Final output

When the task is complete, provide a short summary of:

- which contract clauses each test captures (precondition / postcondition / failure condition)
- properties you considered but did not include, and why (especially derived facts)
