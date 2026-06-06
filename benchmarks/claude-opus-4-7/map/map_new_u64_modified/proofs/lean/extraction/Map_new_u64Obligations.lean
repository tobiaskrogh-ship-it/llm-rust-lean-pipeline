-- Companion obligations file for the `map_new_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import map_new_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Map_new_u64Obligations

open map_new_u64

/-- Functional spec: `Impl.new iter f` returns `ok` of the freshly built
    `Map` whose `iter` and `f` are exactly the inputs.

    The Rust function is a pure two-field struct constructor with no
    precondition and no fallible operation in its body. This single
    equation pins down the entire behaviour, and individual field
    preservations follow as projections.

    The equational form is preferred here (precondition is `True`) and
    closes by `rfl` since `Impl.new` unfolds to `pure (Map.mk iter f)`
    in `RustM`, which is `RustM.ok (Map.mk iter f)`. -/
theorem Impl_new_spec
    (iter : core_models.ops.range.Range u64)
    (f : u64 → RustM u64) :
    Impl.new iter f = RustM.ok (Map.mk iter f) := rfl

/-- (P1) Postcondition — `iter` field preserved verbatim.

    Captures `prop_iter_field_preserved`: for every `Range<u64>`
    (including degenerate ranges with `start ≥ _end` and the `u64::MAX`
    boundary cases), the constructed `Map`'s `iter` is exactly the
    input range — both `start` and `_end`. A buggy implementation that
    swapped fields or stored a default range would falsify this. -/
theorem Impl_new_preserves_iter
    (iter : core_models.ops.range.Range u64)
    (f : u64 → RustM u64) :
    ⦃ ⌜ True ⌝ ⦄ Impl.new iter f ⦃ ⇓ r => ⌜ r.iter = iter ⌝ ⦄ := by
  hax_mvcgen [Impl.new]
  all_goals grind

/-- (P2) Postcondition — `f` field preserved verbatim.

    Captures both `prop_f_field_behaves_identically` (extensional: the
    stored mapper produces the same outputs as the input on every probe)
    and `prop_f_field_is_same_pointer` (intensional: the stored mapper
    *is* the input function). In the Lean model, function equality at
    type `u64 → RustM u64` collapses these to the same statement: the
    stored field equals the input function. A buggy implementation that
    wrapped the input in a thunk or stored a default would falsify this. -/
theorem Impl_new_preserves_f
    (iter : core_models.ops.range.Range u64)
    (f : u64 → RustM u64) :
    ⦃ ⌜ True ⌝ ⦄ Impl.new iter f ⦃ ⇓ r => ⌜ r.f = f ⌝ ⦄ := by
  hax_mvcgen [Impl.new]
  all_goals grind

end Map_new_u64Obligations
