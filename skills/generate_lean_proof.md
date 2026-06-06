---
name: generate_lean_proof
description: Generate Lean proof for the given Lean file and specifications.
---

## Goal

Close every theorem in the companion obligations file until `lake build` succeeds with no `sorry` warnings.

**Finish the proof at almost all costs.** This is the default and the expectation. There is no honourable shortcut and no sanctioned off-ramp for a proof that is merely hard: you are expected to grind — case-split, develop helper lemmas, induct, try one tactic shape after another, consult the references, reformulate — until the build is clean. A proof being long, fiddly, tedious, or slow to converge is never a reason to stop. Uncertainty about whether *N* more fixes will finish it is not a reason to stop either — that feeling is not a wall; keep going.

**Do not delete or weaken obligations** (the non-`private` theorems that state the public contract) — only close them.

### Leaving a `sorry` requires an admission, in your own voice, that you tried and could not

A `sorry` is permitted in exactly one situation: when *you* — this agent, with full access to the references, the Hax prelude, the local helper-lemma facility, and the Lean LSP — **tried this proof and could not finish it.** When you leave a `sorry`, the docstring on that theorem must carry a one-sentence first-person admission to that effect. Not *"this is hard."* Not *"this would take many lines."* Not *"the next pass can handle the mechanical glue."* A direct statement that you attempted and could not complete it. You must explicitly state that you are incapable of completing this proof and that no future iteration of this pipeline with the same model and references could complete it either

If you cannot defensibly write that sentence — if your own narrative for the rest of the turn says the remaining work is *mechanical*, *boilerplate*, *the next pass's job*, *just bind-reductions*, or any other formulation that admits the work is within your reach — then **you have not exhausted what you can do**, and the exit is not yours to take. Close the proof.

The admission is **strictly preferable** to any bad-faith substitute. NEVER do any of these in place of an honest admission:

- Adding an `axiom` (or any unverified assumption) to assert what you were asked to prove.
- Weakening, generalising, deleting, renaming, or restating an obligation so that a trivial proof type-checks. Preconditions placed by the obligations stage are part of the contract (see Rules); do not add new ones either.
- Circular reasoning — using the obligation, or a copy of it, to prove itself.
- A hidden `sorry`, a `sorry` pushed down into a helper just to move it out of sight, or a `decide`/`native_decide` on something that does not actually decide.
- Any "proof" you could not honestly defend as genuinely establishing the stated theorem.

If the choice is between an honest admission and a bad-faith move, write the admission — including for the genuinely-false-as-stated case (honest reason: *"I cannot prove this; it appears false in the model as stated."*).

The admission is **NOT** preferable to actually closing the proof. It is the exit when you tried and could not — not when you didn't try, or tried and stopped early. The following are NOT honest grounds for the admission:

- The proof is long, fiddly, tedious, or boring.
- You tried a few tactics and they did not immediately work.
- A prelude lemma you hoped for is missing — develop it yourself (see the Rules below).
- You cannot tell whether you are converging or stuck. Keep grinding.
- A pre-existing docstring claims the theorem is hard or needs Mathlib.
- The remaining work feels mechanical, boilerplate, or "for the next pass." If you can see it that clearly, you can write it.

The bar is not *"I tried and it is hard."* It is *"I tried and could not."* Reaching that bar requires real work first: reading reference proofs, grepping the prelude, and querying the LSP are research, not proof work — a turn that only inspects the file and then writes the admission has not earned it.

**`private theorem` helpers are different from obligations.** They are scaffolding you (or a previous attempt) introduced, not part of the public contract. You may freely delete a `private theorem` when it has become dead code — e.g. a previous attempt's helper that you have superseded with a better-formulated one. Before deleting, `Grep` the file for the helper's name to confirm nothing else references it; the build will fail loudly if a reference is missed.

If the obligations file is handed to you with theorems already closed by a prior attempt, your scope is the *remaining* sorries — not a re-audit of the closed proofs.

## If a `sorry` survives

In the rare case a `sorry` is the correct outcome (see above), leave the file better than you found it:

- **Docstring the theorem** with three pieces: (1) the first-person admission required by the section above — a one-sentence statement, in your own voice, that you tried this proof and could not finish it; (2) the specific stuck sub-goal `lake build` showed you, quoted or paraphrased; (3) the *structural* unblock — a missing piece of infrastructure or a prerequisite to prove elsewhere, NOT a tactic to try. Good: *"A separately-verified `Nat.gcd_rec` lemma in the Hax prelude would unblock the induction step."* Bad: *"Try `simp; omega` after a generalisation."* A future pass can act on a named dependency; it cannot act on a tactic guess.
- **Keep partial progress.** If you case-split and closed two of three cases, leave the case-analysis and closed cases intact — the surviving `sorry` sits only on the stuck branch. Do not collapse back to one `sorry` on the original goal.
- **State the helper lemmas your unblock names** as `private theorem`s. Prove what you can; leave the rest with their own focused `sorry`. The next pass then sees the exact statement it needs, not a prose description.

## Available tools

- `Read`, `Grep`, `Glob` — inspection. Consult reference examples first; explore the Hax prelude only when references don't cover what you need.
- `Bash` — flexible shell for ad-hoc inspection (`find`, `wc`, inline `python3 -c ...`, etc.) beyond what `Read`/`Grep`/`Glob` cover. Use freely for read-only checks.
- `TodoWrite` — track multi-step work as a checklist. For a proof that layers several lemmas (port helpers → prove a core Nat lemma → wire into the loop spec → close the obligation), write the plan upfront and mark each step as you finish so you don't lose the thread mid-turn.
- `Agent` / `Task` — spawn a sub-agent for broad searches (e.g. *"scan the Hax prelude for any Nat-power monotonicity lemma"* or *"compare proof structure across `proof_patterns/*` and report the closest match"*). Cheaper than a long Grep+Read loop when the search is wide.
- `apply_file_patch_tool` — incremental edits; `write_working_file` if a companion file does not yet exist.
- **Lean LSP tools** (`mcp__lean__lean_*`) — your fast feedback loop: the VS Code information *without* a `lake build`. Prefer these over `lake build` while iterating. Read-only and incremental — re-query after every patch.
  - **`file_path` convention** — pass just the filename (e.g. `Cbrt_u64Obligations.lean`) or a correct absolute path to the `.lean` file. Paths resolve against the **obligations extraction directory** (the LSP's project root), NOT your `cwd` — so a relative path like `proofs/lean/extraction/Cbrt_u64Obligations.lean` will *not* resolve (the LSP looks for `<root>/proofs/lean/extraction/proofs/lean/extraction/Cbrt_u64Obligations.lean`). If the LSP returns nothing when you expect errors, check the path before deciding the server is broken and falling back to `run_lake_build`.
  - `lean_diagnostic_messages` — errors/warnings for the file; call after every patch to see whether the edit type-checks.
  - `lean_goal` — the tactic state at a line/column; read what is left to prove instead of guessing from build stderr.
  - `lean_term_goal` — expected type at a term position.
  - `lean_hover_info`, `lean_declaration_file`, `lean_references` — type, docs, and source of an identifier, instead of grepping.
- `run_lake_build` — the ground-truth check; reserve it for confirming closure.

## Rules

- **You may only edit `proofs/lean/extraction/<Companion>Obligations.lean`.** The harness rejects writes to any other path during this stage — including the extracted module `<package>.lean`, the `lakefile.toml`, and anything outside `proofs/lean/extraction/`. The extracted module is Hax output; editing it produces a "proof" that no longer corresponds to what Hax generated from the Rust source. Recover any missing invariants Lean-side in the obligations file instead.
- **Consult provided reference examples before exploring the Hax prelude.** The prompt lists closed-proof obligations files the selection stage flagged as structurally similar. `Read` at least the first before attempting any tactic — copying its proof shape is faster than rediscovering it from prelude internals. If a selected example carries a `README.md`, read it first.
- **Archetype fallback** — if the picker missed an archetype the target clearly belongs to, read the README directly:
  - extracted Lean contains `rust_primitives.hax.while_loop` → [`proof_patterns/while_example/README.md`](../proof_patterns/while_example/README.md)
  - extracted Lean contains `partial_fixpoint` → [`proof_patterns/recursion_example/README.md`](../proof_patterns/recursion_example/README.md)
- **Iterate with the LSP, confirm with the build.** A theorem is done only when `lake build` succeeds with no `sorry`/errors. If the LSP and `lake build` disagree, `lake build` wins — the LSP was likely stale; re-query after every patch.
- **A surviving `sorry` must clear the bar in the Goal section.** Acceptable only when the *only* alternative left was a bad-faith move — never because the proof was long, hard, or slow to converge. Before any `sorry` survives, you must have written real tactics into that theorem body across **several distinct approaches** (not just rewriting a docstring, not just swapping one `sorry` for another). Reading references, grepping the prelude, and querying the LSP do not count as attempts.
- **Helper declarations must use `private theorem`, not `lemma`.** Mathlib is not imported, so `lemma` is undefined and the file fails to elaborate. Use `private theorem <name> : <statement> := <proof>`.
- **Never leave a `sorry` inside a dead `private theorem`.** Obligations always stay (see Goal). But a `private theorem` is your own scaffolding — before leaving a `sorry` in one, `Grep` for its name; if nothing references it, delete the whole helper instead.
- **Preconditions on an obligation are part of the contract.** A non-trivial hypothesis (`(h : n.toNat ≤ 67)`, `(h_size : s.val.size < 2^63)`, etc.) was placed there by the obligations stage because the universal version is not provable in the Lean model. Use it; don't strip it; don't add new ones. Both directions — removing a precondition to make the theorem stronger, or adding one to make the proof easier — are weakening moves (see Goal).
- **A missing prelude lemma is not a reason to bail.** When `Grep` shows the prelude lacks the lemma you wanted: develop it yourself as a local `private theorem` proved from lower-level lemmas that DO exist, prove the goal from first principles, or break it into sub-goals (`apply`/`refine`/`constructor`/`cases`/`induction`) and discharge each. Hallucinated absences are common — `Grep` the prelude at `proofs/lean/extraction/.lake/packages/Hax/proof-libs/lean/` before claiming a lemma is missing. Likewise, "needs Mathlib / prelude lacks X" docstrings on pre-existing `sorry`s are one prior judgement, not verified impossibility — make your own attempt.
- Split multi-goal tactics; prove sub-goals individually when they need different approaches. Read a prelude lemma's signature before applying — argument order may have shifted. If a theorem statement must change, flag it in the final output — do not silently rewrite it.

## Final output

- Files changed and what was added
- Sub-goals that were difficult and how resolved
- Any obligation left as `sorry`, with the technical reason it couldn't close
