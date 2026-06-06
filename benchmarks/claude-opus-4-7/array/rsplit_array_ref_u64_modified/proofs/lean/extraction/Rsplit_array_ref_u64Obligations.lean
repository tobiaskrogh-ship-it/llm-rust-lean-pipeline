-- Companion obligations file for the `rsplit_array_ref_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import rsplit_array_ref_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Rsplit_array_ref_u64Obligations

open rsplit_array_ref_u64

/-- Definitional unfolding of the partial `usize` subtraction (the
    `hax_sub_def_usize` trick from the `max_size_for_align` reference):
    `x -? y` is, by `rfl`, the overflow-guarded `if`. -/
private theorem hax_sub_def_usize (x y : usize) :
    x -? y = if USize64.subOverflow x y
             then RustM.fail Error.integerOverflow
             else pure (x - y) := rfl

/-- Master reduction: under the valid domain `M ≤ N`, `rsplit_array_ref`
    succeeds and returns the pair whose left slice is the length-`(N-M)`
    prefix of `a` and whose right array is the length-`M` suffix of `a`.
    The three contract obligations below project out of this one lemma. -/
private theorem rsplit_spec (M N : usize) (a : RustArray u64 N) (h : M ≤ N) :
    ∃ (left : RustSlice u64) (right : RustArray u64 M),
      rsplit_array_ref M N a = RustM.ok (rust_primitives.hax.Tuple2.mk left right)
      ∧ left.val = a.toVec.toArray.take (N.toNat - M.toNat)
      ∧ right.toVec.toArray = a.toVec.toArray.drop (N.toNat - M.toNat) := by
  have hMN : M.toNat ≤ N.toNat := USize64.le_iff_toNat_le.mp h
  have hsize : a.toVec.toArray.size = N.toNat := by simp
  have hlt : a.toVec.toArray.size < USize64.size := by
    rw [hsize]; exact USize64.toNat_lt_size N
  have hofNat : (USize64.ofNat a.toVec.toArray.size).toNat = a.toVec.toArray.size :=
    USize64.toNat_ofNat_of_lt' hlt
  have hsubfalse : USize64.subOverflow (USize64.ofNat a.toVec.toArray.size) M = false := by
    rw [Bool.eq_false_iff, ne_eq, USize64.subOverflow_iff, hofNat, hsize]
    omega
  have hMle : M ≤ USize64.ofNat a.toVec.toArray.size := by
    rw [USize64.le_iff_toNat_le, hofNat]; omega
  have hidxNat : (USize64.ofNat a.toVec.toArray.size - M).toNat
      = a.toVec.toArray.size - M.toNat := by
    rw [USize64.toNat_sub_of_le _ _ hMle, hofNat]
  have hsplitcond : (USize64.ofNat a.toVec.toArray.size - M
      ≤ USize64.ofNat a.toVec.toArray.size) := by
    rw [USize64.le_iff_toNat_le, hidxNat, hofNat]; omega
  unfold rsplit_array_ref split_last_chunk
  simp only [rust_primitives.unsize, core_models.slice.Impl.len,
             rust_primitives.slice.slice_length, pure_bind, hax_sub_def_usize,
             hsubfalse, Bool.false_eq_true, ↓reduceIte,
             core_models.slice.Impl.split_at, rust_primitives.slice.slice_split_at,
             if_pos hsplitcond, hidxNat]
  have hdropsize : (a.toVec.toArray.drop (a.toVec.toArray.size - M.toNat)).size
      = M.toNat := by
    grind
  simp only [core_models.convert.TryInto.try_into, core_models.result.Impl.unwrap,
             dif_pos hdropsize, pure_bind]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · simp [hsize]
  · simp [hsize]

/-- Totality / no-panic on the valid domain.

    When `M ≤ N` the unsized slice has length `N ≥ M`, so the internal
    `len -? M` subtraction does not underflow and `split_at` is called at the
    in-bounds index `N - M`; the subsequent `try_into().unwrap()` then succeeds
    because the suffix slice has exactly length `M`. Hence `rsplit_array_ref`
    returns a value rather than panicking. -/
theorem rsplit_array_ref_total (M N : usize) (a : RustArray u64 N) (h : M ≤ N) :
    ∃ r : rust_primitives.hax.Tuple2 (RustSlice u64) (RustArray u64 M),
      rsplit_array_ref M N a = RustM.ok r := by
  obtain ⟨left, right, heq, _, _⟩ := rsplit_spec M N a h
  exact ⟨_, heq⟩

/-- Postcondition — left half (functional correctness, first claim).

    Captures the first assertion of the property test
    `rsplit_partitions_at_n_minus_m`: when `M ≤ N`, `left == &a[0 .. N-M]`. -/
theorem rsplit_array_ref_left_is_prefix (M N : usize) (a : RustArray u64 N)
    (h : M ≤ N) :
    ∃ (left : RustSlice u64) (right : RustArray u64 M),
      rsplit_array_ref M N a
          = RustM.ok (rust_primitives.hax.Tuple2.mk left right)
      ∧ left.val = a.toVec.toArray.take (N.toNat - M.toNat) := by
  obtain ⟨left, right, heq, hleft, _⟩ := rsplit_spec M N a h
  exact ⟨left, right, heq, hleft⟩

/-- Postcondition — right half (functional correctness, second claim).

    Captures the second assertion of the property test
    `rsplit_partitions_at_n_minus_m`: when `M ≤ N`, `right == &a[N-M .. N]`. -/
theorem rsplit_array_ref_right_is_suffix (M N : usize) (a : RustArray u64 N)
    (h : M ≤ N) :
    ∃ (left : RustSlice u64) (right : RustArray u64 M),
      rsplit_array_ref M N a
          = RustM.ok (rust_primitives.hax.Tuple2.mk left right)
      ∧ right.toVec.toArray = a.toVec.toArray.drop (N.toNat - M.toNat) := by
  obtain ⟨left, right, heq, _, hright⟩ := rsplit_spec M N a h
  exact ⟨left, right, heq, hright⟩

/-- Failure condition.

    Captures the unit test `array_rsplit_array_ref_out_of_bounds`
    (`rsplit_array_ref::<7, 6>`): when `M > N` the slice is shorter than `M`,
    so the internal `len -? M` subtraction underflows and the function panics.
    The Rust panic is modelled by `RustM.fail Error.integerOverflow`. -/
theorem rsplit_array_ref_out_of_bounds (M N : usize) (a : RustArray u64 N)
    (h : N < M) :
    rsplit_array_ref M N a = RustM.fail Error.integerOverflow := by
  have hsize : a.toVec.toArray.size = N.toNat := by simp
  have hlt : a.toVec.toArray.size < USize64.size := by
    rw [hsize]; exact USize64.toNat_lt_size N
  have hofNat : (USize64.ofNat a.toVec.toArray.size).toNat = a.toVec.toArray.size :=
    USize64.toNat_ofNat_of_lt' hlt
  have hsubtrue : USize64.subOverflow (USize64.ofNat a.toVec.toArray.size) M = true := by
    rw [USize64.subOverflow_iff, hofNat, hsize]
    exact USize64.lt_iff_toNat_lt.mp h
  unfold rsplit_array_ref split_last_chunk
  simp only [rust_primitives.unsize, core_models.slice.Impl.len,
             rust_primitives.slice.slice_length, pure_bind, hax_sub_def_usize,
             hsubtrue, ↓reduceIte]
  rfl

end Rsplit_array_ref_u64Obligations
