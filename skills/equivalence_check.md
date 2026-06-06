---
name: equivalence_check
description: Read the original Rust source and the Hax-rewritten version, reason about whether the rewrite preserved behavior, and return a verdict.
---

## Goal

Compare two pieces of Rust source — the **original** (input to the rewrite stage) and the **Hax-rewritten** version (output of the rewrite stage) — and judge whether the rewrite preserved the function's runtime behavior. Return one of two verdicts so the pipeline can decide whether to continue.

This stage runs *every* time, not just on extracted crates. The point is to catch regressions introduced by the rewrite stage (inlined `.abs()` that mishandles `T::MIN`, an iterator chain unfolded the wrong way, a `while` body restructured incorrectly, etc.) before we spend tokens on Lean proofs of behaviorally-broken code.

## Available tools

- Built-in `Read`, `Grep`, `Glob` for inspection (read-only — no edits)
- `Bash` — flexible shell for ad-hoc read-only inspection (`find`, `wc`, `diff`, inline `python3 -c ...`) beyond what `Read`/`Grep`/`Glob` cover.
- `TodoWrite` — track each clause of the equivalence check as a separate item if the rewrite is large; mark each off as you verify it.
- `Agent` / `Task` — spawn a sub-agent for broad comparison work (e.g. *"survey how similar rewrites were verified across past runs"*).

You have no write tools, no `cargo` runner, no test setup. The check is pure code review.

## Working rules

### What to compare

The prompt inlines two pieces of Rust source for you:

- **Original** — the source the rewrite stage took as input.
- **Hax-rewritten** — the source the rewrite stage produced.

Look for differences. The rewrite stage's *default* is now to keep Rust source minimal — no `loop_invariant!`, often no `loop_decreases!`, no `requires` — pushing all proof work to Lean obligations. So in many cases the rewritten source will be byte-identical or near-identical to the original. The interesting cases are the ones below.


**Behavior-preserving inlinings (PASS if the inlining is faithful):**

- `.abs()`, `.pow()`, `.checked_*`, `.wrapping_*` inlined as primitive expressions. Watch for edge cases — notably `T::MIN.abs()` panics, and the inlined `if x < 0 { -x } else { x }` must preserve that panic.
- Iterator chains (`iter().sum()`, `.fold(...)`, etc.) unfolded into explicit `for`/`while` loops. Check that the loop bound, accumulator initial value, and step direction match the iterator's semantics on every input.
- Trait-method calls (`x.gcd(&y)`, `x.cmp(&y)`) inlined to the impl body or replaced with primitive `if`/`match`. Check that the impl actually corresponds to the trait method semantics on the relevant type.

**Structural rewrites (each warrants close review — usually PASS):**

- A `while` loop converted to an `if` (or vice versa) on the basis of a mathematical claim (e.g. "by AM-GM the loop runs at most once"). The rewrite is *valid* if the claim holds for every input the original accepted. Look for the comment justifying the rewrite, and ask: does the math actually hold across the full input domain (especially boundary values like `0`, `MAX`, `MIN`)? If yes → PASS. If only over some subset → FAIL.
- A recursive function refactored to tail-recursive form, or vice versa. Behaviorally equivalent for total functions; for functions that panic mid-recursion (e.g. on overflow), check the panic point isn't shifted.
- An `unsafe` block replaced with safe equivalents (`copy_nonoverlapping(...)` → `copy_from_slice(...)`, `transmute(...)` → `to_bits()`/`from_bits()`). Verify the safe form has identical bit-level semantics on every input — pointer-cast-style transmutes can differ on platforms where alignment matters, but for the bit-shuffling cases Hax targets, the safe forms are usually exact.

For each difference, ask: *does this change what the function returns on any input?* Verification-only macros never do. Inlinings and structural rewrites might — that's where real review matters.

### Verdict

End your response with a single line containing exactly one of these markers:

- `VERDICT: PASS` — you reviewed the diff and you're confident the rewrite preserves behavior on all inputs (or the only differences are verification-only annotations).
- `VERDICT: FAIL` — you can identify an input on which the rewrite would behave differently from the original, **or** you have an unresolved concern you cannot rule out. Pipeline halts here. When you are not confident the behavior is preserved, fail — there is no middle verdict.

The marker MUST be a literal final line of your response. The pipeline parses the response for it; without the marker the verdict defaults to FAIL.

## Final output

Before the verdict marker, your response should include:

- A short summary of what changed between original and rewritten (one paragraph).
- For each non-cosmetic change, your reasoning about whether it preserves behavior.
- For FAIL: name a concrete input (or input class) where the divergence (or your unresolved concern) matters.
- The verdict marker as the last line.
