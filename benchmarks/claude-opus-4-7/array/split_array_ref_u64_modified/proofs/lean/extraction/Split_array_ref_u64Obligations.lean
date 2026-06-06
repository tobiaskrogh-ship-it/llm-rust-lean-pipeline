-- Companion obligations file for the `split_array_ref_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import split_array_ref_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Split_array_ref_u64Obligations

open split_array_ref_u64

/-- Master reduction: under the valid domain `M ≤ N`, `split_array_ref`
    succeeds and returns the pair whose left array is the length-`M`
    prefix of `a` and whose right slice is the length-`(N-M)` suffix of
    `a`. The postcondition obligations below project out of this one
    lemma (mirrors the `rsplit_array_ref_u64` reference, with the tuple
    halves swapped: here the *left* component is the fixed-size array and
    the *right* component is the trailing slice, and the split index is
    `M` directly rather than `N - M`). -/
private theorem split_spec (M N : usize) (a : RustArray u64 N) (h : M ≤ N) :
    ∃ (left : RustArray u64 M) (right : RustSlice u64),
      split_array_ref M N a = RustM.ok (rust_primitives.hax.Tuple2.mk left right)
      ∧ left.toVec.toArray = a.toVec.toArray.take M.toNat
      ∧ right.val = a.toVec.toArray.drop M.toNat := by
  have hMN : M.toNat ≤ N.toNat := USize64.le_iff_toNat_le.mp h
  have hsize : a.toVec.toArray.size = N.toNat := by simp
  have hlt : a.toVec.toArray.size < USize64.size := by
    rw [hsize]; exact USize64.toNat_lt_size N
  have hofNat : (USize64.ofNat a.toVec.toArray.size).toNat = a.toVec.toArray.size :=
    USize64.toNat_ofNat_of_lt' hlt
  have hsplitcond : M ≤ USize64.ofNat a.toVec.toArray.size := by
    rw [USize64.le_iff_toNat_le, hofNat, hsize]; omega
  unfold split_array_ref split_first_chunk
  simp only [rust_primitives.unsize, pure_bind,
             core_models.slice.Impl.split_at, rust_primitives.slice.slice_split_at,
             if_pos hsplitcond]
  have htakesize : (a.toVec.toArray.take M.toNat).size = M.toNat := by grind
  simp only [core_models.convert.TryInto.try_into, core_models.result.Impl.unwrap,
             dif_pos htakesize, pure_bind]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · simp
  · simp [hsize]

/-- Totality / no-panic on the valid domain.

    When `M ≤ N` the unsized slice has length `N ≥ M`, so the internal
    `split_at M` is called at an in-bounds index; the subsequent
    `try_into().unwrap()` then succeeds because the prefix slice has
    exactly length `M`. Hence `split_array_ref` returns a value rather
    than panicking.

    Captures the implicit no-panic precondition shared by every valid-call
    property test: `prop_split_array_ref_interior` (`M=3, N=8`),
    `prop_split_array_ref_empty_left` (`M=0, N=8`),
    `prop_split_array_ref_empty_right` (`M=8, N=8`), and the
    `doctest_split_array_ref` instances (`M ∈ {0,2,6}, N=6`). -/
theorem split_array_ref_total (M N : usize) (a : RustArray u64 N) (h : M ≤ N) :
    ∃ r : rust_primitives.hax.Tuple2 (RustArray u64 M) (RustSlice u64),
      split_array_ref M N a = RustM.ok r := by
  obtain ⟨left, right, heq, _, _⟩ := split_spec M N a h
  exact ⟨_, heq⟩

/-- Postcondition — left half (functional correctness, first claim).

    Captures the first half of the property test `prop_split_contract`
    (used by `prop_split_array_ref_interior`, `_empty_left`,
    `_empty_right`, and the `doctest_split_array_ref` instances): when
    `M ≤ N`, `left.len() == M` and `&left[..] == &a[..M]`. The length is
    pinned structurally by the result type `RustArray u64 M`; the content
    equation `left.toVec.toArray = a.toVec.toArray.take M.toNat` pins
    every element in order. A split at the wrong index, or any
    reordering, would falsify this. -/
theorem split_array_ref_left_is_prefix (M N : usize) (a : RustArray u64 N)
    (h : M ≤ N) :
    ∃ (left : RustArray u64 M) (right : RustSlice u64),
      split_array_ref M N a
          = RustM.ok (rust_primitives.hax.Tuple2.mk left right)
      ∧ left.toVec.toArray = a.toVec.toArray.take M.toNat := by
  obtain ⟨left, right, heq, hleft, _⟩ := split_spec M N a h
  exact ⟨left, right, heq, hleft⟩

/-- Postcondition — right half (functional correctness, second claim).

    Captures the second half of the property test `prop_split_contract`
    (used by `prop_split_array_ref_interior`, `_empty_left`,
    `_empty_right`, and the `doctest_split_array_ref` instances): when
    `M ≤ N`, `right.len() == N - M` and `right == &a[M..]`. The equation
    `right.val = a.toVec.toArray.drop M.toNat` simultaneously pins the
    length (`N - M`) and every trailing element in order. A split at the
    wrong index, or any reordering, would falsify this. -/
theorem split_array_ref_right_is_suffix (M N : usize) (a : RustArray u64 N)
    (h : M ≤ N) :
    ∃ (left : RustArray u64 M) (right : RustSlice u64),
      split_array_ref M N a
          = RustM.ok (rust_primitives.hax.Tuple2.mk left right)
      ∧ right.val = a.toVec.toArray.drop M.toNat := by
  obtain ⟨left, right, heq, _, hright⟩ := split_spec M N a h
  exact ⟨left, right, heq, hright⟩

/-- Failure condition.

    Captures the unit test `array_split_array_ref_out_of_bounds`
    (`split_array_ref::<7, 6>`): when `M > N` the unsized slice is shorter
    than `M`, so the internal `split_at M` is out of bounds and the
    function panics. Unlike the `rsplit` reference (whose panic is routed
    through a `len -? M` subtraction underflow → `Error.integerOverflow`),
    here the failure flows directly through `slice_split_at`'s else
    branch, so the Rust panic is modelled by
    `RustM.fail Error.arrayOutOfBounds`. -/
theorem split_array_ref_out_of_bounds (M N : usize) (a : RustArray u64 N)
    (h : N < M) :
    split_array_ref M N a = RustM.fail Error.arrayOutOfBounds := by
  have hsize : a.toVec.toArray.size = N.toNat := by simp
  have hlt : a.toVec.toArray.size < USize64.size := by
    rw [hsize]; exact USize64.toNat_lt_size N
  have hofNat : (USize64.ofNat a.toVec.toArray.size).toNat = a.toVec.toArray.size :=
    USize64.toNat_ofNat_of_lt' hlt
  have hsplitcond : ¬ (M ≤ USize64.ofNat a.toVec.toArray.size) := by
    rw [USize64.le_iff_toNat_le, hofNat, hsize]
    have := USize64.lt_iff_toNat_lt.mp h
    omega
  unfold split_array_ref split_first_chunk
  simp only [rust_primitives.unsize, pure_bind,
             core_models.slice.Impl.split_at, rust_primitives.slice.slice_split_at,
             if_neg hsplitcond]
  rfl

end Split_array_ref_u64Obligations
