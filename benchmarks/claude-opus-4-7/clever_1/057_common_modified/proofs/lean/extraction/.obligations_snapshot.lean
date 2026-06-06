-- Companion obligations file for the `clever_057_common` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_057_common

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_057_commonObligations

/-! ## Top-level obligations on `common`.

`common l1 l2` returns the unique elements appearing in both inputs.

Rust property tests under `mod tests`:
  * `output_set_equals_intersection` — the set of output values equals the
    set-theoretic intersection of `l1` and `l2`.
  * `output_has_no_duplicates` — distinct output positions carry distinct values.

The set-equality test is split into its two independent inclusion directions,
and the soundness direction is further split into "appears in `l1`" and
"appears in `l2`" — two separate facts, each falsifiable on its own. This
yields four independent obligations below. -/

/-- Soundness (output ⊆ l1): every output element occurs somewhere in `l1`.
    Captures one half of the proptest `output_set_equals_intersection`
    (the `⊆` direction, restricted to membership in `l1`). -/
theorem output_element_in_l1
    (l1 l2 : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_057_common.common l1 l2 = RustM.ok v)
    (k : Nat) (hk : k < v.val.size) :
    ∃ i : Nat, ∃ (hi : i < l1.val.size), l1.val[i]'hi = v.val[k]'hk := by
  sorry

/-- Soundness (output ⊆ l2): every output element occurs somewhere in `l2`.
    Captures the other half of the proptest `output_set_equals_intersection`
    (the `⊆` direction, restricted to membership in `l2`). -/
theorem output_element_in_l2
    (l1 l2 : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_057_common.common l1 l2 = RustM.ok v)
    (k : Nat) (hk : k < v.val.size) :
    ∃ j : Nat, ∃ (hj : j < l2.val.size), l2.val[j]'hj = v.val[k]'hk := by
  sorry

/-- Completeness (l1 ∩ l2 ⊆ output): every value appearing in both `l1`
    and `l2` occurs somewhere in the output. Captures the `⊇` direction of
    the proptest `output_set_equals_intersection`. -/
theorem intersection_element_in_output
    (l1 l2 : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_057_common.common l1 l2 = RustM.ok v)
    (x : i64)
    (h1 : ∃ i : Nat, ∃ (hi : i < l1.val.size), l1.val[i]'hi = x)
    (h2 : ∃ j : Nat, ∃ (hj : j < l2.val.size), l2.val[j]'hj = x) :
    ∃ k : Nat, ∃ (hk : k < v.val.size), v.val[k]'hk = x := by
  sorry

/-- Uniqueness: the output contains no duplicates — distinct positions
    carry distinct values. Captures the proptest `output_has_no_duplicates`. -/
theorem output_has_no_duplicates
    (l1 l2 : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_057_common.common l1 l2 = RustM.ok v)
    (k₁ k₂ : Nat) (hk₁ : k₁ < v.val.size) (hk₂ : k₂ < v.val.size)
    (h : v.val[k₁]'hk₁ = v.val[k₂]'hk₂) :
    k₁ = k₂ := by
  sorry

end Clever_057_commonObligations
