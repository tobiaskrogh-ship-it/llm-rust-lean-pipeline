# Notes: why the proof agent gives up — discussion + design conclusions

Written before a `/compact` to preserve a design discussion whose reasoning
(not just its gist) would otherwise be lost. The **code** from this session is
all on disk and safe regardless of compaction; what this file preserves is the
**conversational reasoning** and the **not-yet-implemented proposals**.

To reacquire this context after a compaction: just say *"read
proof-agent-giveup-notes.md"*.

---

## 1. Session state (where things are, on disk)

Earlier this session (all done, verified):
- Reverted model-scoping of the pattern libraries — `proof_patterns/` and
  `rewrite_patterns/` are a single shared pool again.
- Added a `--no-harvest` flag to `pipeline.py` + `run_batch.py` (skips the two
  harvest stages; for benchmarking against a frozen library).
- Added `incomplete_stages/<crate>.json` — written when the pipeline halts on a
  failed check; cleared on a fully successful run.
- Added the Lean LSP MCP integration: `lean-lsp-mcp` as a second stdio MCP
  server for the `make_lean_obligations` / `make_proof` stages (8 read-only
  tools allowed, 14 disabled). Pinned `0.26.2`; `run_agent` prefers an installed
  `uv tool` entrypoint, falls back to `uvx`. Mathlib deliberately NOT adopted.

The proof work (the subject of the discussion below):
- Built `benchmarks/code/starting_examples/trailing_zeros_u64/` and
  `.../max_odd_part/` as missing reference patterns. Pipeline proved both
  (0 sorries); both harvested to `proof_patterns/`.
- Re-ran `gcd_stein_u64`: went 3 → 2 sorries using those references.
- Hand-finished `gcd_stein_u64`'s last 2 sorries — `gcd_stein_loop_spec` (both
  step cases) and `gcd_stein_postcondition` case (iii). The obligations file
  `benchmarks/claude-opus-4-7/num-integer-0.1.46/gcd_stein_u64_modified/proofs/lean/extraction/Gcd_stein_u64Obligations.lean`
  now builds clean with **0 sorries**. Took ~12 `lake build` iterations.
- Harvested it to `proof_patterns/gcd_stein_u64_modified/` (with `manifest.json`).

---

## 2. The discussion — "why does the proof agent give up?"

The pipeline's `make_proof` agent and the interactive Claude are the **same
model**. The question: why did interactive-Claude finish the `gcd_stein` proof
when the pipeline agent left `sorry`s?

**User:** "Why do you think that the agent gives up. is it because it does not
have access to as much context as you. Is the skill not descriptive enough. or
does it actually just need a lot more tries. why were you able and it was not"

First answer ranked three hypotheses: iteration budget dominant, warm start
partly, skill mostly not the problem (the agent's own `sorry` docstrings are
accurate roadmaps — it understood the task). — This framing was then corrected
twice by the user, see below.

**User:** "but it also seems like you have a lot more context than it. i mean
you have all that proof material PLUS this conversation"

Conceded. The key distinction: most of *this conversation* is NOT load-bearing
for the proof. The operative advantage was narrow — interactive-Claude had the
tactic patterns **digested** (it had just hand-built `trailing_zeros_u64` and
`max_odd_part`, so `RustM_ok_bind`, the `>>>?` reduction shape, the
`tz_nonzero_spec` extraction were copy-paste-ready). The agent had *access* to
the same references (they're selectable examples) but "access to a 750-line
file" ≠ "digested in working context." Two kinds of context: (a) information you
can be handed in a prompt — the agent largely had this; (b) digested working
memory of having *done* the adjacent proof — cannot be handed over in a prompt;
a transcript of building `max_odd_part` ≠ having built it. The irreducible part.

**User:** "yes, but the agent doesnt have just 2 tries. it has as many tries as
it wants --- twice"

Conceded — imprecise. Within one `make_proof` attempt the agent can iterate
`edit → lake build → fix` freely; "2 attempts" ≠ "2 cycles." So the agent
*chooses* to stop. Why, given free iteration? (1) It can't tell "converging"
from "blocked" — mid-grind, "10 fixes from done" looks identical to
"fundamentally stuck." Interactive-Claude could *see* the errors shrinking each
build; the agent has to guess and guesses conservatively. (2) The skill hands it
an honorable exit (leave a documented `sorry`) and rewards it over over-claiming
— so a well-behaved agent under uncertainty takes the sanctioned off-ramp.

**User:** "So maybe we dont give the agent an out. maybe we just tell it to make
the proof. maybe instead of doing 2 tries, like we do now. we prompt the agent
to keep going twice"

Split into two parts. "Keep going" instead of fresh restarts — good instinct
(fixes "twice = two restarts, not double depth"; a fresh attempt loses attempt
1's discovered lemma names). But a *naive* continuation hits the context limit
(raw build logs pile up — which is *why* the pipeline does fresh attempts: to
reset context). Right mechanism = a **digested handoff**: carry forward the
working memory (discovered lemma names, what's proven, precise stuck goal,
partial tactic blocks), drop the raw build-log bloat. "Don't give it an out" —
pushed back: for a *verification* pipeline the honest `sorry` is a feature, not
a bug. Remove it and a stuck agent must produce *something* worse — a broken
build, a weakened/deleted obligation, or a faked proof (e.g. `axiom`, hidden
`sorry`, circular reasoning). At least one obligation we found
(`mean_absolute_deviation`) is genuinely false-as-stated — "no out" would force
faking a proof of something false. The `sorry`-out is the soundness valve.

**User:** "but i very much doubt its hitting a context wall. because you were at
50% context before making all of this. and now you are at 96% so i highly doubt
its running out of context"

Conceded — and this is the decisive correction. The whole `gcd_stein` grind cost
~46% of a context window. There was room to spare. So **context-window overflow
is not the constraint**, and neither is the try count (free iteration). Both
*resource* explanations are dead.

---

## 3. Where we landed (the conclusion)

With both resource explanations ruled out, the surviving answer:

**The agent does not give up from any resource limit. It gives up by
*decision*** — with tries to spare and context to spare. The decision is driven
by exactly two things:

1. **Its instructions bless stopping.** The skill explicitly offers the
   documented-`sorry` as a legitimate outcome. Interactive-Claude's instruction
   ("finish the proof", "push on") had no such clause.
2. **It cannot tell convergence from a wall.** Under genuine uncertainty about
   whether N more fixes will finish it, with a sanctioned exit available, a
   well-behaved agent takes the exit.

So the user's *first* instinct in the thread was the correct one: **it is the
"out", not the budget.** The count (`MAX_PROOF_ATTEMPTS = 2`) was never the real
lever, and context room is not either. Same model, blessed exit → it exits;
same model, "push on" with no exit and visible convergence → it grinds 12
cycles. One attempt already has the context room for all 12 cycles — the fix is
making the agent *not bail within the attempt it already has*, not adding
attempts.

---

## 4. Proposed — NOT yet implemented (action items)

These are the concrete changes discussed but not made. They live only here.

1. **Raise the bar on the `sorry`; do NOT remove it entirely.** Keep a narrow
   honest fallback (soundness valve; needed for genuinely-impossible obligations
   — false-as-stated ones, Mathlib-needing ones). But make `sorry` *expensive to
   reach*: before it is allowed, require the agent to (a) have consulted the
   selected references and *named why they don't transfer*, and (b) tried
   several distinct tactic approaches against a specific named stuck goal.
   Simultaneously **re-state the anti-cheat rule loudly**: a documented `sorry`
   is acceptable; a broken build, a weakened/deleted obligation, or a faked
   proof is NOT. (Otherwise raising the bar just pushes the agent from the
   honest exit to a dishonest one.)
   → Edit `skills/generate_lean_proof.md`, the `sorry` clause.

2. **Digested retry handoff, not cold restart.** Each `make_proof` attempt is
   currently a fresh session that loses the prior attempt's working memory.
   `_make_proof_retry_context` (in `pipeline.py`) should carry the *digested*
   state: discovered lemma names, what's already proven, the precise stuck goal,
   partial tactic blocks — compaction-style, not raw build-log continuation
   (overflow) and not a cold restart (loses learnings). → Check what
   `_make_proof_retry_context` currently carries and enrich it.

3. The count (`MAX_PROOF_ATTEMPTS = 2`) likely does **not** need changing — if
   the agent stops bailing within an attempt, the room is already there.

4. **The bigger lever is still the library.** A proof that *adapts a closed
   reference* removes the convergence uncertainty (the agent knows it's on
   track), so it won't take the exit. `gcd_stein` moved 3→2 purely because
   `trailing_zeros_u64` / `max_odd_part` existed. Keep harvesting closed proofs
   so hard proofs become cheap adaptations that fit inside the budget.

Both code changes (1 and 2) were offered as small, surgical edits — pending the
user's go-ahead.
