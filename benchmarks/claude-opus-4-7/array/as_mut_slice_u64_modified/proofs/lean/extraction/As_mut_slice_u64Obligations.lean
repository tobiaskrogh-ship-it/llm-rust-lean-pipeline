-- Companion obligations file for the `as_mut_slice_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import as_mut_slice_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace As_mut_slice_u64Obligations

open as_mut_slice_u64

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

    `as_mut_slice` is the identity/coercion `(&mut [u64; N]) -> &mut [u64]`
    (Rust `&mut s[..]`). A pure array→slice view performs no fallible
    operation, so for every length `N` and every array `a` the call
    succeeds — it never panics, never overflows, never diverges.

    Every contract-style property test in the Rust source
    (`prop_length_equals_n`, `prop_elements_match_in_order`,
    `prop_mutation_writes_through`) calls `as_mut_slice(&mut a)` and then
    inspects the returned slice; each of them implicitly depends on this
    call returning a value rather than panicking. This theorem is the
    well-typed surface of that shared dependency, and the strongest
    statement the (degenerate) extraction admits — see the note at the end
    of this file for why the length/elements/aliasing postconditions cannot
    be stated against a `RustM sorry` return type.

    PROOF STATUS — closed, but a transitive `sorry` warning is unavoidable.

    This obligation is *proved*: the body is
    `rustM_isOk_exists (as_mut_slice N a) (by rfl)` — a total proof term
    with no `sorry` tactic and no `sorry` placeholder. `rustM_isOk_exists`
    is a generic, sorry-free `RustM` fact; `by rfl` discharges
    `(as_mut_slice N a).isOk = true`, which holds because `isOk` inspects
    only the `Option/Except` constructor and never the success payload.

    `lake build` nonetheless emits `declaration uses 'sorry'` on this
    theorem. That warning is *structural*, not a proof gap: the extracted
    signature is `as_mut_slice (N) (a) : RustM sorry`, so the obligation's
    own statement type — `∃ v, as_mut_slice N a = RustM.ok v` — binds
    `v : sorry` and the implicit type argument `sorryAx Type` appears as a
    literal node in the elaborated statement. Lean flags any declaration
    whose *type or value* contains a `sorryAx` node; here it is the type,
    inherited from the off-limits extracted module, that carries it. No
    proof-side change can remove it: the only editable file is this
    obligations companion, the obligation may not be weakened or removed,
    and every non-trivial proposition mentioning `as_mut_slice N a` is
    forced through the `RustM sorry` return type.

    Stuck sub-goal: none — the goal `∃ v, as_mut_slice N a = RustM.ok v`
    is closed. The residual `declaration uses 'sorry'` is a transitive
    artifact of the extracted type `RustM sorry`.

    Structural unblock: a non-degenerate Hax extraction of the array→slice
    reborrow giving `as_mut_slice : (N) (a : RustArray u64 N) -> RustM
    (RustSlice u64)` with a body that returns the actual view. With a
    concrete return type the statement type no longer contains `sorryAx`,
    this proof closes verbatim with zero warnings, and the three currently
    unstateable postconditions (length / elements / aliasing) become
    expressible. This is the same upstream defect the selector flagged as
    the "no array→slice aliasing model / broken extraction" gap. -/
theorem as_mut_slice_total (N : usize) (a : RustArray u64 N) :
    ∃ v, as_mut_slice N a = RustM.ok v :=
  rustM_isOk_exists (as_mut_slice N a) (by rfl)

/- NOTE — contract clauses that cannot be stated against this extraction.

   Hax produced a degenerate extraction for the array→slice reborrow:

       def as_mut_slice (N : usize) (a : RustArray u64 N) : RustM sorry :=
         do (pure sorry)

   Both the return type and the body are `sorry`. The intended return type
   is `RustSlice u64`, but the extracted type is the opaque `sorry`, and the
   body `pure sorry` does not even mention the input `a`.

   Consequently the three postcondition clauses exercised by the Rust
   property tests are *not derived facts* — they are genuine contract
   clauses — yet they have no well-typed Lean statement here:

   * `prop_length_equals_n`        — "returned slice has length N"
   * `prop_elements_match_in_order`— "slice = array elements, in order"
   * `prop_mutation_writes_through`— "writing the slice writes the array"

   Stating any of them requires equating `as_mut_slice N a` with a concrete
   `RustM (RustSlice u64)` value (e.g. `as_mut_slice N a = RustM.ok s` with
   `s : RustSlice u64`). That fails to type-check: `RustM.ok s` has type
   `RustM (RustSlice u64)`, which does not unify with the extraction's
   `RustM sorry`. (`lake build` rejects it: "Type mismatch … but is
   expected to have type RustM sorry".) The opaque result type carries no
   `.val`/`.size`/indexing structure, and `pure sorry` carries no link back
   to `a`, so no Hoare-triple or equational phrasing recovers them either.

   These clauses are therefore left uncovered by construction, not by
   choice — they are the "broken extraction" gap flagged by the selector.
   `as_mut_slice_total` is the only contract clause that survives. -/

end As_mut_slice_u64Obligations
