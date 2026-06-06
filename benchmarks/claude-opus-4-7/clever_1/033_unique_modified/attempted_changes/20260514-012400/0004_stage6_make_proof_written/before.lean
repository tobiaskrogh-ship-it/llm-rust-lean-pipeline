-- Companion obligations file for the `clever_033_unique` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_033_unique

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_033_uniqueObligations

/-! ## Top-level obligations on `unique`.

Each theorem corresponds to one independent property test in the Rust source.
Signatures take the function's `RustM.ok v` result as a hypothesis (where
relevant), so they speak about the value the function actually returns
whenever it succeeds. The empty-input clause additionally asserts success.

Proofs are deferred to the proof stage. -/

/-- Empty-input base case: `unique` on an empty slice succeeds and
    returns an empty `Vec`. Captures the unit test
    `empty_input_yields_empty_output` in the Rust source. -/
theorem empty_input_yields_empty_output
    (l : RustSlice i64)
    (hempty : l.val.size = 0) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_033_unique.unique l = RustM.ok v ∧ v.val.size = 0 := by
  sorry

/-- Strict-monotonicity postcondition: the output is strictly increasing
    (in the signed `i64` ordering, via `.toInt`). A single strict-order
    invariant simultaneously captures "sorted ascending" and "no
    duplicates" (strict ordering rules out repeats). Captures the
    proptest `output_is_strictly_increasing` in the Rust source. -/
theorem output_is_strictly_increasing
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_033_unique.unique l = RustM.ok v)
    (k₁ k₂ : Nat)
    (hk₁ : k₁ < v.val.size) (hk₂ : k₂ < v.val.size)
    (hlt : k₁ < k₂) :
    (v.val[k₁]'hk₁).toInt < (v.val[k₂]'hk₂).toInt := by
  sorry

/-- Completeness postcondition: every input element appears at some
    output position. Captures the proptest
    `output_contains_every_input_element` in the Rust source. -/
theorem output_contains_every_input_element
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_033_unique.unique l = RustM.ok v)
    (i : Nat) (hi : i < l.val.size) :
    ∃ k : Nat, ∃ (hk : k < v.val.size), v.val[k]'hk = l.val[i]'hi := by
  sorry

/-- Soundness postcondition: every output element occurs at some input
    position (the output introduces no spurious elements). Captures the
    proptest `output_only_contains_input_elements` in the Rust source. -/
theorem output_only_contains_input_elements
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_033_unique.unique l = RustM.ok v)
    (k : Nat) (hk : k < v.val.size) :
    ∃ i : Nat, ∃ (hi : i < l.val.size), l.val[i]'hi = v.val[k]'hk := by
  sorry

end Clever_033_uniqueObligations
