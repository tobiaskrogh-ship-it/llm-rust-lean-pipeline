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

/-- Postcondition (element equality): `from_ref s` returns a length-1 array
    whose sole element equals the input `s`.

    Captures the Rust property test `prop_element_equals_input`
    (and the corresponding clause of `array_from_ref`):
    `from_ref(&x)[0] == x` for every `u64` input.

    I tried this proof and could not finish it: after `unfold from_ref`
    and `congr 1` the residual goal is `sorry = { toVec := #v[s] }`,
    where the LHS is the opaque `sorryAx (RustArray u64 1) false` term
    Hax inserted because it cannot translate the Rust `unsafe` pointer
    cast `&*(s as *const u64).cast::<[u64; 1]>()`. No tactic available
    in the Hax prelude (and no Lean tactic in general) can prove
    `sorryAx _ false = c` for a concrete `c`, because the axiom asserts
    only the existence of some inhabitant. I am incapable of closing
    this obligation, and no future iteration of this pipeline running
    against the same extracted module — whose body literally is `pure
    sorry` — can close it either, because the information identifying
    the returned array with `#v[s]` was lost upstream during Hax
    extraction.

    The structural unblock lives in the Hax extraction backend: it would
    need to recognise `core::array::from_ref` (or the `&*(_ as *const _).cast`
    pointer-cast idiom) and emit `pure (RustArray.ofVec #v[s])` for the
    body instead of `pure sorry`. With that change, this theorem would
    close by `unfold from_ref; rfl`. No Lean-side helper lemma can
    substitute for that fix, because the missing fact is the body's own
    definitional equality. -/
theorem from_ref_element_equals_input (s : u64) :
    from_ref s = RustM.ok (RustArray.ofVec #v[s]) := by
  unfold from_ref
  -- Attempted approaches (all reduce to the unprovable equation
  -- `sorry = { toVec := #v[s] }`, where the LHS is the opaque
  -- `sorryAx (RustArray u64 1) false` Hax emitted for the body):
  --   `rfl` — fails, `pure sorry` ≠ `RustM.ok ⟨#v[s]⟩` definitionally.
  --   `congr 1` — leaves `sorry = { toVec := #v[s] }`.
  --   `simp [from_ref]` — leaves `pure sorry = RustM.ok ⟨#v[s]⟩`.
  --   `hax_mvcgen [from_ref]` — fails to synthesise PropAsSPredTautology
  --     (mvcgen wants Hoare-triple goals, not raw equations).
  --   `simp only [pure, ExceptT.pure, RustM.ok]; congr 1` — same residual.
  --   `show RustM.ok (sorry : RustArray u64 1) = …; rfl` — fails: even
  --     `pure sorry` and `RustM.ok sorry` are not defeq through the
  --     instMonad/ExceptT layers without `simp` unfolding.
  -- See docstring for the structural unblock (Hax extraction backend).
  sorry

/-- Totality / no-panic: for every `u64` input, `from_ref` returns
    successfully (no panic, no overflow, no out-of-bounds error).

    `from_ref` is a `const fn` performing a single (in Rust) `unsafe`
    pointer reinterpretation with no fallible operation; in the
    extracted model it is `pure sorry`, which is structurally
    `RustM.ok _`. A buggy implementation that introduced a fallible
    step (e.g. a checked indexing on the resulting array before
    returning it) would falsify this. -/
theorem from_ref_total (s : u64) :
    ∃ v : RustArray u64 1, from_ref s = RustM.ok v := by
  exact ⟨_, rfl⟩

end From_ref_u64Obligations
