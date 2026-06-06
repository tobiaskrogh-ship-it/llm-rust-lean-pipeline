-- Companion obligations file for the `clever_087_sort_array` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_087_sort_array

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_087_sort_arrayObligations

/-! ## Specification oracles for the multiset and sortedness clauses.

`vec_count s target k` counts the indices `j < k` for which `s[j] = target`.
The `dite` on `j < s.size` keeps the definition total — every theorem
below uses `k = s.size`, so the bounded indices always exist. Pattern
reused from `clever_069_strange_sort_list`'s `vec_count`. -/

private def vec_count (s : Array u64) (target : u64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      if h : k < s.size then
        (if (s[k]'h) = target then 1 else 0) + vec_count s target k
      else
        vec_count s target k

/-- Non-strict ascending order on a `u64` array. -/
private def sorted_asc (arr : Array u64) : Prop :=
  ∀ (k₁ k₂ : Nat) (h₁ : k₁ < arr.size) (h₂ : k₂ < arr.size),
    k₁ ≤ k₂ → (arr[k₁]'h₁).toNat ≤ (arr[k₂]'h₂).toNat

/-- Non-strict descending order on a `u64` array. -/
private def sorted_desc (arr : Array u64) : Prop :=
  ∀ (k₁ k₂ : Nat) (h₁ : k₁ < arr.size) (h₂ : k₂ < arr.size),
    k₁ ≤ k₂ → (arr[k₂]'h₂).toNat ≤ (arr[k₁]'h₁).toNat

/-! ## Obligation theorems — proofs deferred. -/

/-- Anchor: empty input yields a successful empty output. Captures the
    Rust unit test `empty_input_returns_empty`. -/
theorem sort_array_empty_input_returns_empty
    (lst : RustSlice u64) (hempty : lst.val.size = 0) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_087_sort_array.sort_array lst = RustM.ok v ∧
      v.val.size = 0 := by
  sorry

/-- Multiset-preservation postcondition: every value occurs the same
    number of times in the output as in the input. Captures the Rust
    proptest `output_is_permutation_of_input`. -/
theorem sort_array_output_is_permutation_of_input
    (lst : RustSlice u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_087_sort_array.sort_array lst = RustM.ok v)
    (target : u64) :
    vec_count v.val target v.val.size = vec_count lst.val target lst.val.size := by
  sorry

/-- Sortedness postcondition (odd parity branch): when the sum
    `lst[0] % 2 + lst[last] % 2` is odd, the output is sorted in
    non-decreasing order. Captures the Rust proptest
    `ascending_when_sum_is_odd`. -/
theorem sort_array_ascending_when_sum_is_odd
    (lst : RustSlice u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hne : 0 < lst.val.size)
    (hres : clever_087_sort_array.sort_array lst = RustM.ok v)
    (hparity :
      ((lst.val[0]'hne).toNat % 2
        + (lst.val[lst.val.size - 1]'(by omega)).toNat % 2) % 2 ≠ 0) :
    sorted_asc v.val := by
  sorry

/-- Sortedness postcondition (even parity branch): when the sum
    `lst[0] % 2 + lst[last] % 2` is even, the output is sorted in
    non-increasing order. Captures the Rust proptest
    `descending_when_sum_is_even`. -/
theorem sort_array_descending_when_sum_is_even
    (lst : RustSlice u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hne : 0 < lst.val.size)
    (hres : clever_087_sort_array.sort_array lst = RustM.ok v)
    (hparity :
      ((lst.val[0]'hne).toNat % 2
        + (lst.val[lst.val.size - 1]'(by omega)).toNat % 2) % 2 = 0) :
    sorted_desc v.val := by
  sorry

end Clever_087_sort_arrayObligations
