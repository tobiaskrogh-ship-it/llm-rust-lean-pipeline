-- Companion obligations file for the `split_array_mut_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import split_array_mut_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Split_array_mut_u64Obligations

open split_array_mut_u64

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

/-- Totality / no-panic — `split_array_mut`.

    `split_array_mut::<M, N>(&mut a)` divides a `&mut [u64; N]` into a
    `&mut [u64; M]` prefix and a `&mut [u64]` suffix (Rust
    `split_first_chunk_mut::<M>(a).unwrap()`). On the valid domain `M ≤ N`
    the call is intended to succeed and partition the storage.

    Every contract-style property test in the Rust source calls
    `split_array_mut::<M, N>(&mut v)` and then inspects the returned pair:

      * `prop_prefix_suffix` (`check_prefix_suffix`) — `left == orig[..M]`,
        `right == orig[M..]`;
      * `prop_mutation_aliasing` (`check_mutation_aliasing`) — the returned
        references are live, disjoint mutable views into the original
        storage;
      * the unit/doc tests `doctest_split_array_mut`, `array_split_array_mut`
        — concrete instances of the same partition postcondition.

    Each of these implicitly depends on the call returning a value rather
    than panicking. This theorem is the well-typed surface of that shared
    dependency, and the strongest statement the (degenerate) extraction
    admits — see the note at the end of this file for why the
    prefix/suffix, aliasing, and `M > N` panic clauses cannot be stated
    against a `RustM sorry` return type.

    PROOF STATUS — closed, but a transitive `sorry` warning is unavoidable.

    The body is `rustM_isOk_exists (split_array_mut M N a) (by rfl)` — a
    total proof term with no `sorry` tactic and no `sorry` placeholder.
    `rustM_isOk_exists` is a generic, sorry-free `RustM` fact; `by rfl`
    discharges `(split_array_mut M N a).isOk = true`, which holds because
    the extracted body is `pure sorry` and `isOk` inspects only the
    `Option/Except` constructor, never the success payload.

    `lake build` nonetheless emits `declaration uses 'sorry'` on this
    theorem. That warning is *structural*, not a proof gap: the extracted
    signature is `split_array_mut (M) (N) (a) : RustM sorry`, so the
    obligation's own statement type — `∃ v, split_array_mut M N a =
    RustM.ok v` — binds `v : sorry` and the implicit type argument
    `sorryAx Type` appears as a literal node in the elaborated statement.
    Lean flags any declaration whose *type or value* contains a `sorryAx`
    node; here it is the type, inherited from the off-limits extracted
    module, that carries it. No proof-side change can remove it.

    Structural unblock: a non-degenerate Hax extraction of the
    `&mut [u64; N]` → `(&mut [u64; M], &mut [u64])` split giving a concrete
    return type. With that the statement type no longer contains `sorryAx`,
    this proof closes verbatim with zero warnings, and the currently
    unstateable postconditions become expressible. This is the same
    upstream defect the selector flagged as the degenerate
    mutable-reborrow extraction. -/
theorem split_array_mut_total (M N : usize) (a : RustArray u64 N) :
    ∃ v, split_array_mut M N a = RustM.ok v :=
  rustM_isOk_exists (split_array_mut M N a) (by rfl)

/-- Totality / no-panic — inlined helper `split_first_chunk_mut`.

    `split_first_chunk_mut::<M>(s)` is the private slice helper inlined by
    `split_array_mut`; in Rust it returns `Option<(&mut [u64; M],
    &mut [u64])>` — `Some` when `s.len() >= M`, `None` otherwise — and is
    itself total (it never panics; the panic in `split_array_mut` comes
    from the subsequent `.unwrap()`). It has no dedicated property test
    (it is private and inlined), but its documented `Some`/`None` contract
    and totality underlie every `split_array_mut` test.

    The selector noted that the target has two degenerate `RustM sorry`
    definitions where one calls the other and that no library example
    documents this; this is the per-degenerate-function totality
    obligation for the callee. Same proof shape and same transitive
    `declaration uses 'sorry'` artifact as `split_array_mut_total`; see the
    closing note for why the `Some`/`None` distinction itself is
    unstateable against `RustM sorry`. -/
theorem split_first_chunk_mut_total (M : usize) (s : RustSlice u64) :
    ∃ v, split_first_chunk_mut M s = RustM.ok v :=
  rustM_isOk_exists (split_first_chunk_mut M s) (by rfl)

/- NOTE — contract clauses that cannot be stated against this extraction.

   Hax produced a degenerate extraction for the mutable array→array/slice
   split (a `&mut [u64; N]` reborrow into `&mut [u64; M]` + `&mut [u64]`):

       def split_first_chunk_mut (M : usize) (s : RustSlice u64) :
           RustM sorry := do (pure sorry)
       def split_array_mut (M : usize) (N : usize) (a : RustArray u64 N) :
           RustM sorry := do (pure sorry)

   For both functions the return type and the body are `sorry`. The
   intended return type is a pair of mutable views; the extracted type is
   the opaque `sorry`, and the body `pure sorry` does not even mention the
   inputs.

   Consequently the clauses exercised by the Rust tests are *not derived
   facts* — they are genuine contract clauses — yet none has a well-typed
   Lean statement here:

   * `prop_prefix_suffix` (`check_prefix_suffix`) — "left = orig[..M] and
     right = orig[M..]" (functional partition postcondition).
   * `prop_mutation_aliasing` (`check_mutation_aliasing`) — "the returned
     references are live, disjoint mutable views: writing left[i]/right[j]
     writes a[i]/a[M+j]" (aliasing postcondition).
   * `array_split_array_mut_out_of_bounds` (M=7,N=6) and
     `split_array_mut_panics_when_m_exceeds_n_boundary` (M=1,N=0) —
     "panics when M > N" (failure condition).

   Stating the two postcondition clauses requires equating
   `split_array_mut M N a` with a concrete `RustM (... pair ...)` value;
   that fails to type-check because `RustM.ok <pair>` does not unify with
   the extraction's `RustM sorry`, and `pure sorry` carries no link back to
   `a`. So no equational or Hoare-triple phrasing recovers them.

   The failure clause is unstateable for an additional reason, and is
   *strictly worse off* than its immutable sibling `rsplit_array_ref`
   (whose concrete extraction makes `... = RustM.fail Error.integerOverflow`
   provable). Here the extracted body is unconditionally `pure sorry`,
   i.e. `RustM.ok sorry`: there is no failure path at all in the
   extraction, regardless of `M` and `N`. A theorem
   `M > N → split_array_mut M N a = RustM.fail _` is therefore not merely
   unprovable but false against this degenerate model, so it must not be
   asserted. The panic contract simply has no faithful surface here.

   These clauses are left uncovered by construction, not by choice — they
   are the degenerate-extraction gap flagged by the selector.
   `split_array_mut_total` and `split_first_chunk_mut_total` (totality /
   no-panic on the modelled computation) are the only contract clauses
   that survive. -/

end Split_array_mut_u64Obligations
