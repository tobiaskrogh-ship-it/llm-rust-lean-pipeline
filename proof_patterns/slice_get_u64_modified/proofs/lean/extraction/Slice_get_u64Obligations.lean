-- Companion obligations file for the `slice_get_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import slice_get_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Slice_get_u64Obligations

open slice_get_u64

/-- Postcondition (in-bounds): when `index.toNat < numbers.val.size`,
    `slice_get` returns the element at that position.

    Captures the property test `in_bounds_returns_indexed_element`:
    `slice_get(&numbers, index) == numbers[index]` whenever `index < numbers.len()`.
    A buggy implementation that performed an off-by-one read, returned the
    sentinel `0` on a valid index, or panicked on the in-bounds branch would
    falsify this. -/
theorem slice_get_in_bounds (numbers : RustSlice u64) (index : usize)
    (h : index.toNat < numbers.val.size) :
    slice_get numbers index = RustM.ok (numbers.val[index.toNat]'h) := by
  conv => lhs; unfold slice_get
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' numbers.size_lt_usizeSize
  have h_cond : decide (index < USize64.ofNat numbers.val.size) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.lt_iff_toNat_lt, h_ofNat]
    exact h
  have h_idx : (numbers[index]_? : RustM u64) = RustM.ok (numbers.val[index.toNat]'h) := by
    show (if h : index.toNat < numbers.val.size then pure (numbers.val[index])
            else .fail .arrayOutOfBounds)
        = RustM.ok (numbers.val[index.toNat]'h)
    rw [dif_pos h]
    rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.lt, pure_bind,
             h_cond, ↓reduceIte, h_idx]

/-- Postcondition (out-of-bounds): when `numbers.val.size ≤ index.toNat`,
    `slice_get` returns the sentinel value `0` instead of panicking.

    Captures the property test `out_of_bounds_returns_zero`:
    `slice_get(&numbers, index) == 0` whenever `index >= numbers.len()`
    (which subsumes the empty-slice case). A buggy implementation that
    let the unguarded indexing through, returned a non-zero sentinel, or
    failed/panicked on the else-branch would falsify this. -/
theorem slice_get_out_of_bounds (numbers : RustSlice u64) (index : usize)
    (h : numbers.val.size ≤ index.toNat) :
    slice_get numbers index = RustM.ok (0 : u64) := by
  conv => lhs; unfold slice_get
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' numbers.size_lt_usizeSize
  have h_cond : decide (index < USize64.ofNat numbers.val.size) = false := by
    rw [decide_eq_false_iff_not]
    intro hlt
    rw [USize64.lt_iff_toNat_lt, h_ofNat] at hlt
    omega
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.lt, pure_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- Totality / no-panic: for every slice and every index, `slice_get`
    returns some value successfully. The explicit length guard makes the
    function total — the partial slice operator is only reached on the
    in-bounds branch, and the else-branch yields the sentinel `0`. A
    buggy implementation that indexed before checking the length would
    falsify this on out-of-bounds inputs. -/
theorem slice_get_total (numbers : RustSlice u64) (index : usize) :
    ∃ v : u64, slice_get numbers index = RustM.ok v := by
  by_cases h : index.toNat < numbers.val.size
  · exact ⟨numbers.val[index.toNat]'h, slice_get_in_bounds numbers index h⟩
  · have hle : numbers.val.size ≤ index.toNat := Nat.le_of_not_lt h
    exact ⟨0, slice_get_out_of_bounds numbers index hle⟩

end Slice_get_u64Obligations
