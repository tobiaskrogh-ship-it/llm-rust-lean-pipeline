---
name: generate_lean_obligations
description: Generate proof obligations directly in Lean for extracted Rust code.
---

## Goal

Generate the formal obligations as theorem statements in the companion file. Each property of the function's contract becomes one independent `theorem`, with `sorry` as a placeholder; proofs are filled in by a later pipeline stage.

The contract has three kinds of clause:

- **precondition** — when may the function be called
- **postcondition** — what does it return when called validly
- **failure condition** — when and how does it fail / panic / overflow

## Where the contract comes from

- The **property tests in the Rust source** are authoritative for *which* clauses exist. Every contract-style test (a test that asserts a postcondition the function should satisfy or a failure mode it should produce) must correspond to at least one theorem in the obligations file.
- **Crate documentation** (README, doc-comments) supplements when the docs assert a property the tests don't cover.
- The **extracted Lean module** shows what the function reduces to mechanically — consult it so theorem statements use the right Lean shapes.

## Feasibility check before stating each theorem

A proptest is necessarily bounded (`vec(_, 0..50)`, etc.), but the natural Lean generalisation quantifies over *all* inputs the model permits (`RustSlice` with `size < 2^64`, full `u64`/`i64` ranges). For functions that overflow, panic, or otherwise fail on inputs the proptest excludes, the universal Lean theorem is **false in the model** even though the test passes — handing the proof stage an unprovable obligation that can only exit as `sorry`.

Before finalising each statement, check feasibility:

1. **Look at the function's behaviour at the model's edges.** Does it overflow on huge inputs? Does a wrapping cast (`len() as i64`) flip a sign for `size ≥ 2^63`? Does an accumulator hit `2^64` before the recursion terminates?
2. **If the natural universal statement still holds**, state it universally — that's the strongest honest contract.
3. **If it does not, add the minimal precondition that restores truth.** Aim for the **strongest claim that's actually true in the Lean model**, not the literal proptest scope. The proptest's bound is a hint that such a precondition exists, not the precondition itself.

Examples of the principle:

- A function that builds a `Vec` of size `2n − 1` via `extend_from_slice`: the universal totality theorem is false (the push fails for `2n − 1 ≥ 2^64`). Add precondition `2 * s.val.size − 1 < 2^64`.
- A function that divides by `numbers.len() as i64` and claims non-negativity: for `size ≥ 2^63` the cast wraps negative and the result can be negative. Add precondition `s.val.size < 2^63`.
- A recursive multiplicative loop where the proptest sets `n ≤ 67` because `C(67, k) < 2^64`: the universal `binomial n k = ok r` is unprovable outside that range. Add precondition `n.toNat ≤ 67`.

What this rule is NOT:

- **Not test-domain mimicry.** Don't copy `0..50` from the proptest into Lean just because the proptest used it. The proptest samples a bounded slice of the *real* truth domain; you state the real domain.
- **Not over-restriction.** Don't add preconditions that exclude cases where the property genuinely holds. Excluding a true case is as wrong as missing a needed one.
- **Not a substitute for the soundness valve.** If the analysis is uncertain, prefer the more permissive statement; the proof stage's `sorry` exit remains as the safety net.

When uncertain, state the universal version and flag the uncertainty in the final output.

## Available tools

- Built-in `Read`, `Grep`, `Glob` for inspection — consult reference examples first; explore the Hax prelude only when references don't cover what you need
- `Bash` — flexible shell for ad-hoc inspection (`find`, `wc`, inline `python3 -c ...`) beyond what `Read`/`Grep`/`Glob` cover.
- `TodoWrite` — track multi-step work as a checklist; useful when you're generating several obligations and want to mark each off as it type-checks.
- `Agent` / `Task` — spawn a sub-agent for broad searches (e.g. *"survey how similar contracts are stated across `proof_patterns/`"*).
- `apply_file_patch_tool` for edits to the companion file
- **Lean LSP tools** (`mcp__lean__lean_*`) — fast feedback without a `lake build`: `lean_diagnostic_messages` shows type errors in the companion file the moment you patch it (the VS Code squiggles); `lean_hover_info` / `lean_declaration_file` inspect prelude types/definitions so your statements reference the right names. Read-only and incremental — call `lean_diagnostic_messages` after each patch. **`file_path` convention**: pass just the filename (e.g. `Cbrt_u64Obligations.lean`) or a correct absolute path. Paths resolve against the obligations extraction directory (the LSP's project root), NOT your `cwd`, so a relative path like `proofs/lean/extraction/Cbrt_u64Obligations.lean` will not resolve. If the LSP returns nothing when you expect errors, check the path before falling back to `run_lake_build`.
- `run_lake_build` as the ground-truth check that statements are well-typed

## Rules

- The companion file `<Crate>Obligations.lean` has been pre-created with the right imports and a `namespace <Crate>Obligations` wrapper. Edit this file to add your theorems. **The extracted Hax module (`<crate>.lean`) is off-limits — the harness rejects writes there during this stage.** It's Hax output; edits to it produce obligations that no longer correspond to what Hax actually generated from the Rust source. You may edit other files (e.g. `lakefile.toml`) if genuinely needed, but the extracted module never.
- One theorem per independent contract clause. No bundling into conjunctions.
- **Every contract-style property test in the Rust source MUST appear as at least one theorem.** Do not omit a clause because the proof seems hard or impossible — that's the proof stage's problem. If the proof can't close, the proof stage admits the theorem with `sorry`; the contract surface stays intact. *Coverage of the contract is non-negotiable.*
- The single legitimate reason to skip a property test is that it asserts a **derived mathematical fact about the result**, not a contract clause. Examples of derived facts (skip): "result preserves parity", "result is non-decreasing", "result is a quadratic residue mod 4", "operation is commutative". These follow from functional correctness plus algebra; they add no verification value. Examples of contract clauses (do *not* skip): "result divides both inputs", "result equals the closed form", "function panics when x = 255". When in doubt, include it.
- Avoid trivial obligations (`True`, `False → ...`).
- Iterate with `lean_diagnostic_messages` (fast, per-patch); confirm with `run_lake_build` before finishing. Proofs are `sorry`; only statement well-typedness matters at this stage. If the LSP and `lake build` disagree, `lake build` wins.

## Notes on `RustM`

Extracted functions are wrapped in `RustM` (e.g. `def square : u8 → RustM u8 := do (x *? x)`).

- For postconditions where the precondition is `True` (or trivially holds in the safe range), state theorems in **equational form**: `f x args = RustM.ok ...` or `f x args = RustM.fail ...`. This is easier to prove than Hoare triples and matches the existing reference style.
- Use Hoare triples (`⦃ ⌜pre⌝ ⦄ f x args ⦃ ⇓ r => ⌜post⌝ ⦄`) only when there's a non-trivial precondition that meaningfully constrains the proof.

## Final output

- Which file you edited
- The theorems added — one line per theorem naming the contract clause it captures
- Any property test you classified as a derived fact (with reasoning)
- Any theorem statement you're uncertain about (well-formed but with a question on the framing)
