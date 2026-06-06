-- Companion obligations file for the `from_mut_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import from_mut_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace From_mut_u64Obligations

open from_mut_u64

/-- Generic structural fact about `RustM`: a computation whose `isOk` flag is
    `true` returns some value. Proved by case analysis on the underlying
    `Option (Except Error α)`; it contains no `sorry` and never inspects the
    success payload, so applying it does not drag the extraction's opaque
    `sorry` term into a caller's proof term. -/
private theorem rustM_isOk_exists {α : Type} (x : RustM α) (h : x.isOk = true) :
    ∃ v, x = RustM.ok v := by
  cases x with
  | none => simp [RustM.isOk] at h
  | some e =>
    cases e with
    | error err => simp [RustM.isOk] at h
    | ok v => exact ⟨v, rfl⟩

/-- Totality / no-panic.

    `from_mut` is the reborrow `(&mut u64) -> &mut [u64; 1]` (Rust
    `&mut *(s as *mut u64).cast::<[u64; 1]>()`). It is a `const fn`
    performing only a pointer cast / reborrow — no fallible operation —
    so for every input `s` the call succeeds: it never panics, never
    overflows, never diverges.

    Every contract-style property test in the Rust source
    (`array_from_mut`, `prop_element_reads_original`,
    `prop_write_propagates_to_original`) calls `from_mut(&mut value)`
    and then inspects / writes through the returned reference; each of
    them implicitly depends on this call returning a value rather than
    panicking. This theorem is the well-typed surface of that shared
    dependency, and the strongest statement the (degenerate) extraction
    admits — see the note at the end of this file for why the read- and
    write-aliasing postconditions cannot be stated against a `RustM
    sorry` return type.

    PROOF STATUS — closed, but a transitive `sorry` warning is
    unavoidable.

    This obligation is *proved*: the body is
    `rustM_isOk_exists (from_mut s) (by rfl)` — a total proof term with
    no `sorry` tactic and no `sorry` placeholder. `rustM_isOk_exists`
    is a generic, sorry-free `RustM` fact; `by rfl` discharges
    `(from_mut s).isOk = true`, which holds because `isOk` inspects only
    the `Option/Except` constructor and never the success payload.

    `lake build` nonetheless emits `declaration uses 'sorry'` on this
    theorem. That warning is *structural*, not a proof gap: the
    extracted signature is `from_mut (s : u64) : RustM sorry`, so the
    obligation's own statement type — `∃ v, from_mut s = RustM.ok v` —
    binds `v : sorry` and the implicit type argument `sorryAx Type`
    appears as a literal node in the elaborated statement. Lean flags
    any declaration whose *type or value* contains a `sorryAx` node;
    here it is the type, inherited from the off-limits extracted module,
    that carries it. No proof-side change can remove it: the only
    editable file is this obligations companion, the obligation may not
    be weakened or removed, and every non-trivial proposition mentioning
    `from_mut s` is forced through the `RustM sorry` return type.

    Stuck sub-goal: none — the goal `∃ v, from_mut s = RustM.ok v` is
    closed. The residual `declaration uses 'sorry'` is a transitive
    artifact of the extracted type `RustM sorry`.

    Structural unblock: a non-degenerate Hax extraction of the
    `&mut u64 -> &mut [u64; 1]` reborrow giving
    `from_mut : (s : u64) -> RustM (RustArray u64 1)` (or a model that
    preserves the aliasing link to the input) with a body that returns
    the actual view. With a concrete return type the statement type no
    longer contains `sorryAx`, this proof closes verbatim with zero
    warnings, and the two currently unstateable postconditions (read /
    write aliasing) become expressible. This is the same upstream defect
    the selector flagged as the "no array→slice aliasing model / broken
    extraction" gap. -/
theorem from_mut_total (s : u64) :
    ∃ v, from_mut s = RustM.ok v :=
  rustM_isOk_exists (from_mut s) (by rfl)

/- NOTE — contract clauses that cannot be stated against this extraction.

   Hax produced a degenerate extraction for the `&mut u64 -> &mut
   [u64; 1]` reborrow:

       def from_mut (s : u64) : RustM sorry :=
         do (pure sorry)

   Both the return type and the body are `sorry`. The intended return
   type is `RustArray u64 1` (a `&mut [u64; 1]`), but the extracted type
   is the opaque `sorry`, and the body `pure sorry` does not even
   mention the input `s`.

   Consequently the two postcondition clauses exercised by the Rust
   property tests are *not derived facts* — they are genuine contract
   clauses — yet they have no well-typed Lean statement here:

   * `prop_element_reads_original`      — "the returned reference
       observes the original value: `from_mut(&mut x)[0] == x`"
   * `prop_write_propagates_to_original`/`array_from_mut`
                                        — "a write through the returned
       reference is observable on the original `u64` (no copy is made)"

   Stating either of them requires equating `from_mut s` with a
   concrete `RustM (RustArray u64 1)` value (e.g. `from_mut s =
   RustM.ok arr` with `arr : RustArray u64 1`, then asserting
   `arr[0] = s`). That fails to type-check: `RustM.ok arr` has type
   `RustM (RustArray u64 1)`, which does not unify with the
   extraction's `RustM sorry`. (`lake build` rejects it: "Type mismatch
   … but is expected to have type RustM sorry".) The opaque result type
   carries no indexing structure, and `pure sorry` carries no link back
   to `s`, so no Hoare-triple or equational phrasing recovers them
   either. The write-aliasing clause is doubly unstateable: the
   extraction has no model of mutation-through-reborrow at all.

   These clauses are therefore left uncovered by construction, not by
   choice — they are the "broken extraction" gap flagged by the
   selector. `from_mut_total` is the only contract clause that
   survives. -/

end From_mut_u64Obligations
