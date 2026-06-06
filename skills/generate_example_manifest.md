---
name: generate_example_manifest
description: Populate proof_patterns/<name>/manifest.json with the proof obstacles and a one-line summary for a closed-proof crate.
---

## Goal

Inspect a closed-proof example under `proof_patterns/<name>/` and write its `manifest.json`. The manifest's job is to let the selection skill rank this example as a relevant reference for *future* target crates — so the features must name the **proof obstacles** that actually made the proof non-trivial, *not* surface attributes of the source and *not* the tactics used to close goals.

## Available tools

- Built-in `Read`, `Grep`, `Glob` for inspection
- `Bash` — flexible shell for ad-hoc inspection beyond what `Read`/`Grep`/`Glob` cover.
- `TodoWrite` — track the tags you're collecting as a checklist while scanning the proof.
- `Agent` / `Task` — spawn a sub-agent for broad surveys (e.g. *"compare features across existing manifests in `proof_patterns/`"*).
- `apply_file_patch_tool` to overwrite the placeholder manifest

## What a useful tag looks like

A tag names something that the *next* analogous proof will also need to deal with. The highest-value tags name **transferable proof moves** — a non-trivial helper lemma the author invented, a bridge between two semantic domains, a structural trick. Those are usually the things that took the most thought to discover, and surfacing them lets a future selection LLM route the next bitwise/recursion/whatever proof to the right reference.

Lower-value but still legitimate tags name **obstacle categories**: the kind of failure case (`overflow-u8`), the control-flow shape (`if-branch-on-overflow`, `nested-if`), the result shape (`bool-result`, `option-result`), or the structural feature of the function (`recursion`, `loop-mut`, `bit-manip`).

## Three categories of bad tags

Reject these, in increasing subtlety:

1. **Surface attributes** — describe the function, not the proof: `takes-a-u8`, `one-argument`, `no-allocations`, `under-50-lines`. These don't correlate with proof difficulty.

2. **Tactic names** — describe *how* a goal was closed, not *why* it was hard: `bv-decide-proof`, `simp-proof`, `omega-proof`, `rfl-proof`, `decide-proof`. Most closed proofs use `bv_decide` somewhere; tagging by tactic creates near-universal noise. **Exception:** when the *obstacle* is needing a specific lemma family or technique, name the family/technique (e.g. `bv-nat-bridge`, `width-extension-lift`, `subtraction-no-underflow`) — not the tactic that consumed it.

3. **Coverage-too-broad tags** — true of half the library and therefore useless for discrimination: `functional-correctness` (every postcondition theorem qualifies), `total-function` (true of every function without a precondition). The runner gives you a frequency table; tags marked WEAK (≥40% library coverage) should be added at most once, and only when they're *literally the entry's most distinctive feature*. Usually there's a sharper tag available.

## Tag vocabulary (illustrative — not exhaustive)

These are the kinds of buckets useful tags fall into. Reuse vocabulary when it fits; coin new tags when the obstacle is genuinely not yet represented (the library should grow vocabulary over time, not calcify).

- *Integer-arithmetic obstacles* — e.g. `overflow-u8`, `overflow-u64`, `wrapping`, `saturating`, `signed-abs`, `subtraction-no-underflow`, `ceiling-division`, `division-by-zero`, `residue-invariant` (algebraic `(x-b)%b = x%b` style)
- *Bitvector / domain-bridge obstacles* — e.g. `bit-manip`, `shift`, `bv-nat-bridge` (BitVec.toNat → omega style reasoning), `bv-width-extension-lift` (proving an n-bit identity by lifting to n+k bits), `half-adder-identity` (Nat lemma `2(a∧b) + (a⊕b) = a+b`)
- *Control-flow obstacles* — e.g. `if-branch-on-overflow`, `match`, `early-return`, `nested-if`, `panic-branch`
- *Result-shape obstacles* — e.g. `bool-result`, `option-result`, `result-err`, `pure-arithmetic`, `disjunctive-postcondition`
- *Structural obstacles* — e.g. `recursion`, `loop-mut`, `loop-invariant` (manual `Spec.MonoLoopCombinator.while_loop` application), `slice-index`, `partial-fixpoint` (Hax-extracted recursion), `strong-induction` (`Nat.strongRecOn` over a `toNat` measure)
- *Spec-shape obstacles* — e.g. `precondition-bounded`, `overflow-avoidance` (function deliberately written to avoid overflow), `panic-freedom-only` (postcondition not proved, only no-failure), `lean-side-invariant-strengthening` (weak Rust invariant + strong Lean invariant — the canonical workaround when natural invariant uses partial ops)
- *Proof-mechanics obstacles* — e.g. `triple-to-equation` (`RustM.Triple_iff_BitVec` + RustM case-split to convert a Hoare triple to an `RustM.ok` equation), `recursive-equation-unfold` (`unfold f` + `by_cases` on guard for `partial_fixpoint`-style proofs)

## Protocol

Follow this order. Steps 1–4 establish ground truth; steps 5–7 are the reasoning trace you must produce *before* writing the manifest.

1. **Read the obligations file** (`proofs/lean/extraction/*Obligations.lean`) first. The theorem statements show which contract clauses exist; the tactic blocks show which obstacles each one had to discharge (e.g. `if_neg`/`if_pos` rewrites point to `if-branch-on-overflow`; `bv_decide` on a width-(n+k) goal points to `width-extension-lift`; recursion lemmas point to `recursion`; a private helper lemma named after a fact you'd cite to a colleague almost always names a Tier-1 tag).
2. **Read the extracted module** (`proofs/lean/extraction/<crate>.lean`) for the function shape — `RustM`, `+?`/`*?`/`-?` operators, `if … then … else`, recursive calls, loop encoding.
3. **Skim `src/lib.rs`** last for context (signed vs unsigned, library calls inlined). Don't tag from Rust alone — the extraction may have folded the obstacle away.
4. **Verify proofs are closed.** Run `grep -nE '\bsorry\b'` on the obligations file. If any hits, stop and report which theorem is open — don't write the manifest. (Same for `axiom` declarations and `native_decide`, both of which weaken the trust story.)
5. **Scan for transferable moves.** Re-read the proof asking: *what's the clever step a colleague would highlight if they were teaching this proof to someone proving an analogous function?* Private helper lemmas with descriptive names, calls into BitVec/Nat conversion lemma sets, width-extension or domain-lift tricks, custom inequalities — each is a candidate Tier-1 tag. If the proof has no clever step, the proof is genuinely a one-liner and you'll only find Tier-2/Tier-3 tags.
6. **Survey existing tag distribution.** The runner surfaces a frequency table classifying tags as WEAK / STANDARD / FRESH. Don't pile up WEAK tags; treat them as filler.
7. **Selectivity check, per candidate tag.** Name one plausible future function whose proof would need this tag, *and* one that wouldn't. If you can't think of either, the tag is too generic or too narrow — revise it. This is the single best filter against "tag everything is total" mistakes.

After steps 5–7 produce the trace described below, then write the manifest.

### Heuristics for shape of the final tag set

- **3–6 features is typical.** Fewer than 3 means you're under-tagging; more than 6 usually means surface attributes or tactic names slipped in.
- **Aim to include at least one transferable-move tag** if the proof had a clever step. These are the highest-value entries because they let future analogous proofs find this one.
- **Avoid stacking WEAK tags.** At most one, and only if it really is the entry's defining property.
- **New vocabulary is good** when an existing tag would be a near-synonym that loses precision. The library is meant to grow vocabulary as the proof corpus diversifies.

## Reasoning trace (output before writing the manifest)

Print, in order:

- **Transferable moves found** — list each helper lemma / domain bridge / structural trick from the proof, with the line range it appears on. Note whether existing library vocabulary already covers it or whether you'll need to coin a tag.
- **Tag candidates** — for each, state (a) the obligations-file or extracted-module line that grounds it, (b) which category from the vocabulary above it falls into, (c) the selectivity check (one future fn that would fire, one that wouldn't).
- **Rejected candidates** — tactic-name candidates, coverage-too-broad candidates, and surface attributes you considered but cut, with a one-line reason each.
- **Final tag set** — 3–6 tags, and whether each is reused library vocabulary or freshly coined (with a one-line justification for any new tags).
- **Summary line** — one line, ≤120 chars, naming what the function does *and* its main failure mode if any.

Then call `apply_file_patch_tool` to overwrite `manifest.json`.

## Output format

```json
{
  "features": ["tag1", "tag2", "..."],
  "summary": "One-line description including the failure mode if any."
}
```

## Final output

After writing, restate (in 5–10 lines max):

- the chosen tags, with a one-phrase justification per tag (which line of the obligations file or extracted module the tag is grounded in)
- which tags are new vocabulary vs reused; what existing tags you considered but rejected as near-synonyms
- if `sorry` / `axiom` / `native_decide` was found: don't write the manifest; report which theorem is open
