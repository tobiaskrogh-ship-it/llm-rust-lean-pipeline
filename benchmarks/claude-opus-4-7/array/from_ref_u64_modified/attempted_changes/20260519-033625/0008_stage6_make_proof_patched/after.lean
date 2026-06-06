-- Companion obligations file for the `from_ref_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import from_ref_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace From_ref_u64Obligations

open from_ref_u64

/-- Generic structural fact about `RustM`: a computation whose `isOk` flag is
    `true` returns some value. Proved by case analysis on the underlying
    `Option (Except Error α)`; it contains no `sorry` and never inspects the
    success payload, so applying it does not itself introduce a `sorry`
    placeholder (any residual `sorry` warning on a caller is transitive,
    inherited from the extraction's `sorry` body). -/
private theorem rustM_isOk_exists {α : Type} (x : RustM α) (h : x.isOk = true) :
    ∃ v, x = RustM.ok v := by
  cases x with
  | none => simp [RustM.isOk] at h
  | some e =>
    cases e with
    | error err => simp [RustM.isOk] at h
    | ok v => exact ⟨v, rfl⟩

/-- Failure condition (none) / totality / no-panic.

    `from_ref` is the reference→array reborrow `(&u64) -> &[u64; 1]` (Rust
    `&*(s as *const u64).cast::<[u64; 1]>()`). It is a `const fn` that
    performs no fallible operation — no indexing, no arithmetic, no
    allocation — so for every input `s` the call succeeds: it never
    panics, never overflows, never diverges.

    Every contract-style property test in the Rust source
    (`array_from_ref`, `prop_element_equals_input`,
    `prop_no_copy_aliases_input`) calls `from_ref(&x)` and then inspects
    the returned array; each implicitly depends on this call returning a
    value rather than panicking. Unlike the degenerate `as_mut_slice`
    twin (whose extraction was `RustM sorry`), this extraction returns a
    concrete `RustM (RustArray u64 1)`, so the no-panic clause is
    genuinely stateable here and its statement type carries no
    `sorryAx`.

    PROOF STATUS — closed, but a transitive `sorry` warning is
    unavoidable. The body is `rustM_isOk_exists (from_ref s) (by rfl)`:
    a total proof term with no `sorry` tactic and no `sorry`
    placeholder. `rustM_isOk_exists` is a generic, sorry-free `RustM`
    fact; `by rfl` discharges `(from_ref s).isOk = true`, which holds
    because `from_ref s` reduces to `RustM.ok sorry = some (.ok sorry)`
    and `isOk` inspects only the `Option/Except` constructor, never the
    success payload — so the existential goal is genuinely closed.

    `lake build` nonetheless emits `declaration uses 'sorry'` here. That
    warning is *structural*, not a proof gap: the extracted body is
    `from_ref s := do (pure sorry)`, so unfolding `from_ref` (forced by
    the `by rfl` defeq check) drags the extraction's `sorryAx` node into
    this declaration's transitive axiom set. The statement *type* is
    clean (`RustArray u64 1` is concrete, unlike the `as_mut_slice`
    `RustM sorry` twin); the residual `sorry` is inherited solely from
    the off-limits extracted module's `sorry` body.

    Stuck sub-goal: none — `∃ v, from_ref s = RustM.ok v` is closed.

    Structural unblock: a non-degenerate Hax extraction of the
    reference→array reborrow whose body returns the actual one-element
    array (e.g. `pure (.ofVec #v[s])`) instead of `pure sorry`. With a
    real body this proof closes verbatim with zero warnings, and
    `from_ref_element_equals_input` below becomes provable. This is the
    upstream "concrete return type + degenerate `sorry` body" hybrid
    defect the selector flagged for the reference→array coercion. -/
theorem from_ref_total (s : u64) :
    ∃ v : RustArray u64 1, from_ref s = RustM.ok v :=
  rustM_isOk_exists (from_ref s) (by rfl)

/-- Postcondition (functional correctness / value): `from_ref(&x)`
    returns the length-1 array whose sole element is exactly the
    referenced value `x`. `Vector.replicate (1:usize).toNat s` is the
    one-element vector `[s]`, so this single equation pins down the
    length (1) and the unique element (`= s`) simultaneously.

    Captures the value assertions of the original core test
    `array_from_ref` (`&[value] == from_ref(&value)`, both the runtime
    and the `const` instance) and the property test
    `prop_element_equals_input` (`from_ref(&x)[0] == x` across the
    boundary `SAMPLES` set `{0, 1, 2, 42, 1<<32, u64::MAX-1, u64::MAX,
    …}`). Because this theorem is universally quantified over `s`, every
    sample is an instance of it.

    A buggy implementation returning a different element (a default, a
    shifted/masked value, a fresh constant) would falsify this.

    PROOF STATUS — left as `sorry`, narrowed to one explicit stuck goal.

    The proof below is a real attempt, not a placeholder: totality is
    discharged with the same `rustM_isOk_exists` helper as
    `from_ref_total` (so `∃ v, from_ref s = RustM.ok v` is genuinely
    closed), the extracted body is unfolded (`simp only [from_ref, pure,
    ExceptT.pure]`), and the resulting `hv` is injected and `subst`-ed to
    pin the witness down to the extraction's opaque payload.

    Stuck sub-goal (confirmed via the LSP tactic state and `lake build`):

        s : u64
        ⊢ sorry.toVec = Vector.replicate (USize64.toNat 1) s

    The LHS `sorry` is the extraction's *own* opaque payload — the
    extracted body is `from_ref s := do (pure sorry)` (see
    `from_ref_u64.lean:19`), a constant that never mentions the input
    `s`. After substitution there is no hypothesis relating that `sorry`
    to `s`, and `sorry.toVec` cannot be evaluated, so no `simp` / `decide`
    / `omega` / `rfl` step can equate it with `Vector.replicate 1 s`.
    This is the selector-flagged "concrete return type + degenerate
    `sorry` body" hybrid defect: the statement *type* is clean (so the
    obligation is well-typed and the `sorry` warning is a true proof gap,
    not the transitive-type artifact seen in `as_mut_slice`), but the
    body carries no functional content to verify against.

    Structural unblock: a non-degenerate Hax extraction of the
    reference→array reborrow whose body returns the actual one-element
    array — i.e. `from_ref s := pure (RustArray.ofVec (Vector.replicate
    (USize64.toNat 1) s))` (or `pure (.ofVec #v[s])`) — instead of `pure
    sorry`. With such a body the `simp only [from_ref, …]` step rewrites
    `hv` to expose `v.toVec = Vector.replicate 1 s` directly and this
    proof closes with `rfl`/`subst`. The blocker is purely upstream in
    the extracted module (off-limits to this stage); no lemma added to
    this obligations file can substitute for the missing body, because
    the missing information (the link `result = [s]`) does not exist
    anywhere in the extraction to be recovered. -/
theorem from_ref_element_equals_input (s : u64) :
    ∃ v : RustArray u64 1,
      from_ref s = RustM.ok v ∧ v.toVec = Vector.replicate (1 : usize).toNat s := by
  -- Totality survives (same generic helper as `from_ref_total`): the call
  -- succeeds and yields some payload `v` with `from_ref s = RustM.ok v`.
  obtain ⟨v, hv⟩ := rustM_isOk_exists (from_ref s) (by rfl)
  refine ⟨v, hv, ?_⟩
  -- Remaining goal: `v.toVec = Vector.replicate (1 : usize).toNat s`.
  -- `hv : from_ref s = RustM.ok v`, but `from_ref s` unfolds to
  -- `RustM.ok (sorry : RustArray u64 1)`, so `hv` forces `v` to be the
  -- extraction's opaque `sorry` payload. Expose the body and substitute:
  simp only [from_ref, pure, ExceptT.pure] at hv
  -- `hv : ExceptT.mk (some (Except.ok sorry)) = RustM.ok v`. Inject the
  -- `some`/`Except.ok` constructors to pin `v` down to the extraction's
  -- opaque `sorry` payload, then substitute it into the goal.
  injection hv with hv'
  injection hv' with hv''
  subst hv''
  -- The goal is now the genuinely unclosable
  --     `(sorry : RustArray u64 1).toVec = Vector.replicate (USize64.toNat 1) s`
  -- where the LHS `sorry` is the extraction's own opaque payload (tagged
  -- `from_ref_u64:19`). The extracted body `do (pure sorry)` never
  -- mentions `s`, so no hypothesis, lemma, or `decide`/`simp`/`omega`
  -- step can relate `sorry.toVec` to `s`. Stuck here by construction —
  -- see the structural unblock below.
  sorry

/- NOTE — contract clause that cannot be stated against this extraction.

   The Rust contract also includes a *no-copy / pointer-identity* clause,
   exercised by:

   * `prop_no_copy_aliases_input` — `core::ptr::eq(r, &arr[0])`: the
     returned array reference must alias the input storage, not point at
     a fresh copy;
   * the third assertion of `array_from_ref` —
     `core::ptr::eq(VALUE, &ARR[0])`.

   The doc comment ("without copying") makes this a genuine contract
   clause, not a derived mathematical fact. It is nevertheless left
   uncovered *by construction*, not by choice: the `RustM` / `RustArray`
   model is purely functional and carries no notion of pointers,
   addresses, or aliasing. There is no `&`/address term to equate, so no
   well-typed Lean proposition expresses "the result aliases the input
   reference". (`as_mut_slice` documents the same gap; here the value
   postcondition survives because the return type is concrete, but the
   aliasing clause is still inexpressible.)

   Additionally, the extracted body is `do (pure sorry)` — it does not
   mention the input `s` — so `from_ref_element_equals_input` above,
   while well-typed, is not provable from the extraction alone; the
   proof stage will admit it with `sorry`. That is the documented
   "concrete return type + degenerate `sorry` body" hybrid defect, an
   upstream broken-extraction issue for the reference→array coercion,
   not an obligation-surface choice. -/

end From_ref_u64Obligations
