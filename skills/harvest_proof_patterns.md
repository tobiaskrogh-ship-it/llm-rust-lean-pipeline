---
name: harvest_proof_patterns
description: Decide whether the just-verified working crate's proof contributes a new pattern to `proof_patterns/`, and if so add it via `add_proof_pattern`.
---

## Goal

You are invoked at the very end of the pipeline, after `make_proof` has closed every theorem in the obligations file (the harness has already verified no `sorry` remains outside comments). Your job: read the working crate and the existing library, decide whether this proof's obstacles add value, and if so call `add_proof_pattern` to install it.

The library exists to help future targets find structurally similar proofs. A new entry earns its keep only if it carries a verification obstacle the existing entries don't already cover — or solves an existing obstacle with a meaningfully cleaner / more representative shape.

You only *write* via `add_proof_pattern`. You do not edit the working crate, the source, or anything else.

## Available tools

- Built-in `Read`, `Grep`, `Glob` for inspection
- `Bash` — flexible shell for ad-hoc inspection (`find`, `wc`, `diff`, inline `python3 -c ...`) beyond what `Read`/`Grep`/`Glob` cover.
- `TodoWrite` — track the features you're considering tagging and whether each is already covered by an existing entry.
- `Agent` / `Task` — spawn a sub-agent for broad surveys (e.g. *"index existing manifests by feature tag and report overlap with this target"*).
- `add_proof_pattern` to install a new entry.

## What you're reading (in the prompt)

- The target's `src/lib.rs`
- The target's full obligations file (`<Crate>Obligations.lean`) — proofs included, sorry-free
- Every existing library entry's `manifest.json`

## What counts as a new pattern

Add the entry if **AT LEAST ONE** holds:

- The proof's verification obstacle (a tag you'd assign to its manifest) does not appear in any existing manifest.
- The proof solves an existing obstacle via a *structurally distinct* tactic shape (rare — a judgement call; only assert this when you can name a specific structural difference, e.g. "uses `Nat.strongRecOn` instead of `Nat.rec`").

Do **NOT** add when:

- Every tag the entry would carry already appears in ≥2 existing entries with similar proof structure.
- The proof is trivial (closeable by `rfl` / `decide` / a single `unfold` / `omega` only).
- The proof copies an existing library entry's tactic skeleton line-for-line.
- You're genuinely uncertain. Over-additions dilute selection — lean toward no.

## Workflow

1. **Read existing library manifests** (provided in the prompt). For each, note the `features` tags and the `summary`. Build a mental index of what's already covered.
2. **Read the target's obligations file** end-to-end. Identify the proof obstacles — what made each `theorem` non-trivial to close. Note the tactics used (`Spec.MonoLoopCombinator.while_loop`, `Nat.strongRecOn`, `bv_decide`, manual induction, etc.).
3. **Read the target's `src/lib.rs`** briefly — for surface features that contextualise the obstacles (signed vs unsigned, recursion vs loop, partial ops, etc.).
4. **Judge.** Compare the target's tags against the library. If new tag(s) exist or the proof shape is structurally distinct, decide ADD. Otherwise, decide SKIP.
5. **Execute.**
   - If ADD: call `add_proof_pattern` with `name`, `features`, `summary`. The harness will copy the working crate into `proof_patterns/<name>/` and write the manifest.
   - If SKIP: report in your final text which existing entry(ies) already cover this pattern. Do not call the tool.

## Tag vocabulary

Use the EXISTING vocabulary from the library manifests. Invent a new tag only when no existing tag captures the obstacle. Tags follow the same rules as `generate_example_manifest`:

- Tags name **proof obstacles**, not surface attributes of the source.
- One tag per obstacle.
- Lower-case, hyphenated (e.g. `loop-invariant`, `bv-nat-bridge`, `recursive-equation-unfold`).

## Naming

- The default `name` argument is the working crate's leaf folder name verbatim (the prompt names it). Use that unless you have a specific structural reason to override.
- Names must be `snake_case` and stay distinct from existing entries.

## Rules

- The only writable tool you have is `add_proof_pattern`. You cannot modify the working crate or the source.
- Call `add_proof_pattern` at most once per session (only one working crate to consider).
- If you call `add_proof_pattern`, do so once your judgment is final — its effect (copy + manifest) is the contribution, not a draft.
- Quality over quantity. One well-tagged entry is worth more than several borderline ones.

## Final output

- One sentence: ADDED `<name>` / SKIPPED.
- If added: the features list and one-line summary you supplied.
- If skipped: which existing library entry(ies) already cover this pattern.
- Any observations about the proof structure worth flagging to a human reader.
