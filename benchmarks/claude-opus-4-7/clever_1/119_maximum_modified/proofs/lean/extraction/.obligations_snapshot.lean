-- Companion obligations file for the `clever_119_maximum` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_119_maximum

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_119_maximumObligations

/-! ## Reference oracles for stating the contract.

The four proptests assert four properties of `maximum arr k`:
1. `k = 0` ⟹ the result is empty;
2. `arr.is_empty()` ⟹ the result is empty;
3. the length of the result is `min(k, arr.len())`;
4. the result is sorted ascending;
5. the result is the suffix of an ascending sort of `arr` of length `min(k, arr.len())`
   — equivalently, the `k` largest elements of `arr` (as a multiset), in ascending order.

To phrase (5) cleanly we need an independent reference sort: a list-based ascending
insertion sort. To phrase (4) we use a standard `sorted_asc` predicate on the result
array. -/

/-- List-based ascending insertion: insert `x` into a list, preserving ascending order. -/
private def insert_asc_list : List u64 → u64 → List u64
  | [],      x => [x]
  | y :: ys, x => if x ≤ y then x :: y :: ys else y :: insert_asc_list ys x

/-- List-based ascending insertion sort. Reference oracle for the content claim. -/
private def sort_asc_list : List u64 → List u64
  | []      => []
  | x :: xs => insert_asc_list (sort_asc_list xs) x

/-- Non-strict ascending order on a `u64` array. -/
private def sorted_asc (arr : Array u64) : Prop :=
  ∀ (k₁ k₂ : Nat) (h₁ : k₁ < arr.size) (h₂ : k₂ < arr.size),
    k₁ ≤ k₂ → (arr[k₁]'h₁).toNat ≤ (arr[k₂]'h₂).toNat

/-! ## Obligations. -/

/-- Special-case clause: `k = 0` ⟹ the function succeeds and returns the empty `Vec`.
    Captures the `k == 0` arm of the proptest `prop_empty_on_zero_k_or_empty_arr`. -/
theorem maximum_zero_k_returns_empty
    (arr : RustSlice u64) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_119_maximum.maximum arr (0 : u64) = RustM.ok v ∧
      v.val.size = 0 := by
  sorry

/-- Special-case clause: `arr` empty ⟹ the function succeeds and returns the empty `Vec`.
    Captures the `arr.is_empty()` arm of the proptest `prop_empty_on_zero_k_or_empty_arr`. -/
theorem maximum_empty_arr_returns_empty
    (arr : RustSlice u64) (k : u64) (hempty : arr.val.size = 0) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_119_maximum.maximum arr k = RustM.ok v ∧
      v.val.size = 0 := by
  sorry

/-- Length postcondition: `result.len() = min(k, arr.len())`.
    Captures the proptest `prop_length_is_min_k_len`. -/
theorem maximum_length_is_min_k_arr_size
    (arr : RustSlice u64) (k : u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_119_maximum.maximum arr k = RustM.ok v) :
    v.val.size = min k.toNat arr.val.size := by
  sorry

/-- Sortedness postcondition: the result is sorted ascending.
    Captures the proptest `prop_result_sorted_ascending`. -/
theorem maximum_result_sorted_ascending
    (arr : RustSlice u64) (k : u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_119_maximum.maximum arr k = RustM.ok v) :
    sorted_asc v.val := by
  sorry

/-- Content postcondition: the result is the suffix of length `min(k, arr.len())`
    of an ascending sort of `arr`. Equivalently, the `k` largest elements of `arr`
    (as a multiset), in ascending order.
    Captures the proptest `prop_result_is_k_largest`. -/
theorem maximum_result_is_k_largest
    (arr : RustSlice u64) (k : u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_119_maximum.maximum arr k = RustM.ok v) :
    v.val.toList =
      (sort_asc_list arr.val.toList).drop
        (arr.val.size - min k.toNat arr.val.size) := by
  sorry

end Clever_119_maximumObligations
