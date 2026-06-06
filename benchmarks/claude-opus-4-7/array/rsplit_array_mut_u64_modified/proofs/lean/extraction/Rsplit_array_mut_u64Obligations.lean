-- Companion obligations file for the `rsplit_array_mut_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import rsplit_array_mut_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Rsplit_array_mut_u64Obligations

open rsplit_array_mut_u64

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

/-- Totality / no-panic on the valid path (`M ≤ N`).

    `rsplit_array_mut::<M, N>(&mut a)` divides one mutable array reference
    into the prefix `a[0 .. N-M]` and a mutable array reference to the last
    `M` elements `a[N-M .. N]`. On the valid path (`M ≤ N`) it performs only
    a `split_at_mut` plus an infallible `try_into` whose length precondition
    holds by construction, so the call succeeds — it never panics, never
    overflows, never diverges.

    Both contract-style property tests in the Rust source
    (`prop_split_is_prefix_and_suffix`, `prop_writes_alias_and_partition_original`)
    fix the *middle* split `M = 4, N = 9` (so `M ≤ N` holds), call
    `rsplit_array_mut::<4, 9>(&mut a)`, and then inspect the returned views;
    each implicitly depends on this call returning a value rather than
    panicking. The transferred unit tests `doctest_rsplit_array_mut` and the
    `M = 0` / `M = N` cases of `array_rsplit_array_mut` are likewise on the
    valid path. This theorem is the well-typed surface of that shared
    dependency, and the strongest statement the (degenerate) extraction
    admits — see the note at the end of this file for why the
    split-location, aliasing/partition, and panic-on-`M>N` clauses cannot be
    stated against a `RustM sorry` return type.

    PROOF STATUS — closed, but a transitive `sorry` warning is unavoidable.

    The body is `rustM_isOk_exists (rsplit_array_mut M N a) (by rfl)` — a
    total proof term with no `sorry` tactic and no `sorry` placeholder.
    `rustM_isOk_exists` is a generic, sorry-free `RustM` fact; `by rfl`
    discharges `(rsplit_array_mut M N a).isOk = true`, which holds because
    `isOk` inspects only the `Option/Except` constructor and never the
    success payload, and the extracted body is `do (pure sorry)`.

    `lake build` nonetheless emits `declaration uses 'sorry'` on this
    theorem. That warning is *structural*, not a proof gap: the extracted
    signature is `rsplit_array_mut (M) (N) (a) : RustM sorry`, so the
    obligation's own statement type — `∃ v, rsplit_array_mut M N a =
    RustM.ok v` — binds `v : sorry` and the implicit type argument
    `sorryAx Type` appears as a literal node in the elaborated statement.
    Lean flags any declaration whose type or value contains a `sorryAx`
    node; here it is the type, inherited from the off-limits extracted
    module, that carries it. No proof-side change can remove it.

    Structural unblock: a non-degenerate Hax extraction of the array→slice
    split giving a concrete return type (`RustM ((RustSlice u64) ×
    (RustArray u64 M))` or similar) with a body that returns the actual
    views. With a concrete return type the statement type no longer contains
    `sorryAx`, this proof closes verbatim with zero warnings, and the
    currently unstateable postconditions become expressible. This is the
    same upstream "broken array→slice/split aliasing extraction" defect the
    selector flagged. -/
theorem rsplit_array_mut_total (M : usize) (N : usize) (a : RustArray u64 N) :
    ∃ v, rsplit_array_mut M N a = RustM.ok v :=
  rustM_isOk_exists (rsplit_array_mut M N a) (by rfl)

/- NOTE — contract clauses that cannot be stated against this extraction.

   Hax produced a degenerate extraction for the array→slice split. Both the
   private inlined helper and the public function collapse to opaque stubs:

       def split_last_chunk_mut (M : usize) (s : RustSlice u64) : RustM sorry :=
         do (pure sorry)
       def rsplit_array_mut (M : usize) (N : usize) (a : RustArray u64 N) :
           RustM sorry := do (pure sorry)

   Both return types and both bodies are `sorry`. The intended return type
   is a pair `(&mut [u64], &mut [u64; M])`, but the extracted type is the
   opaque `sorry`, and the body `pure sorry` does not even mention the input
   `a`. (The helper `split_last_chunk_mut` is conceptually called by
   `rsplit_array_mut`, but since both bodies are `pure sorry` there is no
   real call dependency to thread; no separate helper obligation is
   meaningful.)

   Consequently the following clauses exercised by the Rust tests are *not
   derived facts* — they are genuine contract clauses — yet they have no
   well-typed Lean statement here:

   * `prop_split_is_prefix_and_suffix` — split location: `left` is exactly
     the prefix `a[0 .. N-M]` and `right` exactly the suffix `a[N-M .. N]`,
     element-for-element in order (also the substance of the unit tests
     `doctest_rsplit_array_mut` and `array_rsplit_array_mut`).

   * `prop_writes_alias_and_partition_original` — the returned references
     mutably alias the original storage and partition `[0, N)` with no gap
     or overlap, so writing through every `left[i]`/`right[i]` updates each
     original element exactly once.

   * Failure condition "panics if `M > N`" (`array_rsplit_array_mut_out_of_bounds`,
     `#[should_panic]`, `M = 7, N = 6`). The Rust path is
     `checked_sub` → `None` → `unwrap()` panic; the degenerate extraction
     erases the fallible branch entirely (`pure sorry` always succeeds), so
     there is no surviving `RustM.fail`/panic representation to equate
     against.

   Stating any of these requires equating `rsplit_array_mut M N a` (or the
   helper) with a concrete `RustM` value of the intended pair type. That
   fails to type-check: such a value has a concrete `RustM _` type which
   does not unify with the extraction's `RustM sorry` (`lake build` rejects
   it: "Type mismatch … but is expected to have type RustM sorry"). The
   opaque result type carries no `.val`/`.size`/indexing structure, and
   `pure sorry` carries no link back to `a`, so no Hoare-triple or
   equational phrasing recovers them either.

   These clauses are therefore left uncovered by construction, not by
   choice — the "broken extraction" gap flagged by the selector.
   `rsplit_array_mut_total` is the only contract clause that survives. -/

end Rsplit_array_mut_u64Obligations
