---
name: select_relevant_proof_examples
description: Pick up to 5 worked examples from the example library whose verification challenges most closely match the target crate.
---

## Goal

Inspect the target crate (extracted Lean is the primary signal; Rust source is secondary) and pick up to **5** examples from `proof_patterns/` whose verification challenges are closest to the target's. The selected paths are passed to the proof stage as in-context references.

Fewer than 5 is fine — irrelevant picks mislead the proof agent more than missing picks do.

## Library layout

Each example lives at `proof_patterns/<name>/` and contains at least:

- `src/lib.rs` — Rust source
- `proofs/lean/extraction/<crate>.lean` — extracted module
- `proofs/lean/extraction/<Crate>Obligations.lean` — obligations file with **closed** proofs (no `sorry`)
- `manifest.json` — `{"features": ["..."], "summary": "one-line description"}`

Some examples also carry a `README.md` documenting the canonical proof pattern for an archetype (e.g. while-loop targets, recursive targets). When present, the proof stage reads it before attempting tactics.

`features` is a list of short tags describing what makes the example interesting to verify. Typical tags: `overflow-u8`, `overflow-i32`, `signed-abs`, `if-branch`, `match`, `bool-result`, `panic`, `recursion`, `loop-mut`, `slice-index`, `bit-manip`, `saturating`, `wrapping`, `pure-arithmetic`. The exact vocabulary lives in the manifests themselves — read them, don't assume.

## Available tools

- Built-in `Read`, `Grep`, `Glob` for inspection
- `Bash` — flexible shell for ad-hoc read-only inspection (`find`, `wc`, `diff`, inline `python3 -c ...`) beyond what `Read`/`Grep`/`Glob` cover.
- `TodoWrite` — track each candidate pattern you're evaluating as a checklist item; useful when comparing many references.
- `Agent` / `Task` — spawn a sub-agent for broad surveys (e.g. *"scan all `proof_patterns/*/manifest.json` and rank by feature overlap with this target"*).

No edits, no builds — selection is read-only.

## Working rules

- **Lean is the primary signal.** Read `<target>/proofs/lean/extraction/<target>.lean` first. The extraction shape (`RustM`, `+?` / `*?`, `if … then … else`, recursion, loop encoding) tells you what proof patterns will be needed.
- **Rust source is secondary.** Skim `<target>/src/lib.rs` for surface features the extraction may obscure (signed vs unsigned types, library calls that were inlined, the property tests that pinned the contract).
- **Match on verification difficulty, not surface similarity.** Two functions that both compute over `u8` are not necessarily similar to prove — what matters is whether they share the same proof obstacles (overflow branches, panic conditions, recursion structure, etc.).
- **Read each candidate's `manifest.json` first**, only open `src/lib.rs` / the Lean files for examples that look promising from their tags + summary. Don't read every example end-to-end.
- **Rank, then cap.** Score candidates roughly by how many of the target's features they cover and how prominent that feature is in their proof. Take the top 5; drop any whose match is weak.
- **Don't pick for breadth.** If only 2 examples are clearly relevant, return 2. A weak 3rd–5th pick is worse than no pick.

## Final output

- **Selected paths**, one per line, as `proof_patterns/<name>` (relative to the working directory). At most 5.
- **Per pick: a one-line rationale** naming the specific feature(s) that drove the match (e.g. "overflow-u8 + if-branch on overflow flag — same proof shape as target").
- **Gaps**: any feature in the target that no example covers. These are signals for which examples to add to the library next.
- **Rejections**: examples you considered but did not pick, with a one-phrase reason (e.g. "recursion — target is non-recursive").
