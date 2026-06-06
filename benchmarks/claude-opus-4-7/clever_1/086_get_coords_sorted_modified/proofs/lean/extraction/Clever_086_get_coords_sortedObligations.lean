-- Companion obligations file for the `clever_086_get_coords_sorted` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_086_get_coords_sorted

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Clever_086_get_coords_sortedObligations

/-! ## Standard scaffolding (transferred from `clever_009_rolling_max`,
     `clever_025_remove_duplicates`, `clever_057_common`,
     `clever_069_strange_sort_list`). -/

/-- `RustM.ok x >>= f = f x`. The library's `pure_bind` simp lemma only
    matches literal `Pure.pure`; this rewrite handles the `RustM.ok` form
    produced after reducing definitions. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_zero_toNat : (0 : usize).toNat = 0 := rfl

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide

private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

private theorem usize_add_one_no_bv (i : usize) (h : i.toNat + 1 < 2^64) :
    BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
  generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
  cases bo with
  | false => rfl
  | true =>
    exfalso
    have hi := (USize64.uaddOverflow_iff i 1).mp hbo
    rw [usize_one_toNat] at hi
    omega

private theorem usize_sub_one_ok (i : usize) (h : 0 < i.toNat) :
    (i -? (1 : usize) : RustM usize) = RustM.ok (i - 1) := by
  show (rust_primitives.ops.arith.Sub.sub i 1 : RustM usize) = RustM.ok (i - 1)
  show (if BitVec.usubOverflow i.toBitVec (1 : usize).toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure (i - 1)) = _
  have h_no_bv :
      BitVec.usubOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.usubOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have h_sub_ov : USize64.subOverflow i 1 = true := hbo
      have hii : i.toNat < (1 : usize).toNat := USize64.subOverflow_iff.mp h_sub_ov
      rw [usize_one_toNat] at hii
      omega
  rw [h_no_bv]; rfl

private theorem usize_sub_one_toNat (i : usize) (h : 0 < i.toNat) :
    (i - 1).toNat = i.toNat - 1 := by
  have h_pre : (1 : usize).toNat ≤ i.toNat := by rw [usize_one_toNat]; omega
  rw [USize64.toNat_sub_of_le' h_pre, usize_one_toNat]

/-! ## i64 cast helpers. -/

/-- Bridge: for a `usize` whose value fits in the positive `Int64` range,
    `(cast_op u : RustM i64) = RustM.ok` with the matching `Int64`. -/
private theorem cast_op_usize_to_i64 (u : usize) (h : u.toNat < 2^63) :
    (rust_primitives.hax.cast_op u : RustM i64) = RustM.ok (USize64.toInt64 u) := by
  show (Cast.cast u : RustM i64) = _
  rfl

/-- The `toInt` of `USize64.toInt64 u` equals `(u.toNat : Int)` when `u.toNat < 2^63`. -/
private theorem usize_toInt64_toInt (u : usize) (h : u.toNat < 2^63) :
    (USize64.toInt64 u).toInt = (u.toNat : Int) := by
  show (Int64.ofNat u.toNat).toInt = (u.toNat : Int)
  exact Int64.toInt_ofNat_of_lt h

/-! ## Vec push helper for `(i64, i64)` tuples. -/

private abbrev Pair := rust_primitives.hax.Tuple2 i64 i64

private def push_pair
    (acc : alloc.vec.Vec Pair alloc.alloc.Global) (p : Pair)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec Pair alloc.alloc.Global :=
  ⟨acc.val ++ #[p], by
    have h_size : (acc.val ++ #[p]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

@[simp]
private theorem push_pair_size
    (acc : alloc.vec.Vec Pair alloc.alloc.Global) (p : Pair)
    (h : acc.val.size + 1 < USize64.size) :
    (push_pair acc p h).val.size = acc.val.size + 1 := by
  show (acc.val ++ #[p]).size = acc.val.size + 1
  rw [Array.size_append]; rfl

private theorem push_pair_val
    (acc : alloc.vec.Vec Pair alloc.alloc.Global) (p : Pair)
    (h : acc.val.size + 1 < USize64.size) :
    (push_pair acc p h).val = acc.val ++ #[p] := rfl

/-! ## `is_empty` evaluation lemmas. -/

private theorem is_empty_eq_size_zero (s : RustSlice i64) :
    (core_models.slice.Impl.is_empty i64 s : RustM Bool)
      = RustM.ok (decide (s.val.size = 0)) := by
  unfold core_models.slice.Impl.is_empty core_models.slice.Impl.len
         rust_primitives.slice.slice_length
  simp only [bind_pure_comp, pure_bind]
  show RustM.ok (USize64.ofNat s.val.size == (0 : usize)) =
       RustM.ok (decide (s.val.size = 0))
  congr 1
  have h_ofNat : (USize64.ofNat s.val.size).toNat = s.val.size :=
    USize64.toNat_ofNat_of_lt' s.size_lt_usizeSize
  rw [show (USize64.ofNat s.val.size == (0 : usize)) = decide (USize64.ofNat s.val.size = 0) from rfl]
  by_cases h : s.val.size = 0
  · rw [decide_eq_true h]
    apply decide_eq_true
    apply USize64.toNat_inj.mp
    rw [h_ofNat, h]; rfl
  · rw [decide_eq_false h]
    apply decide_eq_false
    intro heq
    apply h
    have h_nat : (USize64.ofNat s.val.size).toNat = (0 : usize).toNat := by rw [heq]
    rw [h_ofNat] at h_nat
    show s.val.size = 0
    have h_zero : (0 : usize).toNat = 0 := rfl
    omega

/-! ## Step lemmas for `scan_row_desc`. -/

/-- `j = 0`, row empty → return acc. -/
private theorem scan_row_desc_zero_empty
    (row : RustSlice i64) (r : i64) (x : i64)
    (acc : alloc.vec.Vec Pair alloc.alloc.Global)
    (hempty : row.val.size = 0) :
    clever_086_get_coords_sorted.scan_row_desc row r x (0 : usize) acc = RustM.ok acc := by
  conv => lhs; unfold clever_086_get_coords_sorted.scan_row_desc
  have h_beq_zero : (((0 : usize) == (0 : usize)) : Bool) = true := by decide
  have h_is_empty : (core_models.slice.Impl.is_empty i64 row : RustM Bool) = RustM.ok true := by
    rw [is_empty_eq_size_zero]
    rw [decide_eq_true hempty]
  simp only [rust_primitives.cmp.eq, h_beq_zero, RustM_ok_bind, ↓reduceIte, pure_bind]
  simp only [h_is_empty, RustM_ok_bind]
  simp only [rust_primitives.hax.logical_op.not, pure_bind]
  show (if (!true) = true then _ else (pure acc : RustM _)) = _
  rw [if_neg (by decide)]
  rfl

/-- `j = 0`, row non-empty, `row[0] = x` → push (r, 0). -/
private theorem scan_row_desc_zero_match
    (row : RustSlice i64) (r : i64) (x : i64)
    (acc : alloc.vec.Vec Pair alloc.alloc.Global)
    (hne : 0 < row.val.size)
    (heq : (row.val[0]'hne) = x)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_086_get_coords_sorted.scan_row_desc row r x (0 : usize) acc =
      RustM.ok (push_pair acc (rust_primitives.hax.Tuple2.mk r (0 : i64)) h_acc) := by
  conv => lhs; unfold clever_086_get_coords_sorted.scan_row_desc
  have h_beq_zero : (((0 : usize) == (0 : usize)) : Bool) = true := by decide
  have h_size_ne_zero : row.val.size ≠ 0 := by omega
  have h_is_empty : (core_models.slice.Impl.is_empty i64 row : RustM Bool) = RustM.ok false := by
    rw [is_empty_eq_size_zero, decide_eq_false h_size_ne_zero]
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have hne' : (0 : usize).toNat < row.val.size := by rw [h_zero_toNat]; exact hne
  have h_idx : (row[(0 : usize)]_? : RustM i64) = RustM.ok (row.val[0]'hne) := by
    show (if h : (0 : usize).toNat < row.val.size then pure (row.val[(0 : usize)]) else .fail .arrayOutOfBounds)
        = RustM.ok (row.val[0]'hne)
    rw [dif_pos hne']; rfl
  have h_eq_x : (row.val[0]'hne == x) = true := by rw [beq_iff_eq]; exact heq
  have h_app_size :
      acc.val.size + (#[rust_primitives.hax.Tuple2.mk r (0 : i64)] : Array Pair).size < USize64.size := by
    show acc.val.size + 1 < USize64.size
    exact h_acc
  simp only [rust_primitives.cmp.eq, h_beq_zero, RustM_ok_bind, ↓reduceIte, pure_bind]
  simp only [h_is_empty, RustM_ok_bind]
  simp only [rust_primitives.hax.logical_op.not, pure_bind]
  show (if (!false) = true then _ else (pure acc : RustM _)) = _
  rw [if_pos (by decide)]
  simp only [h_idx, RustM_ok_bind, rust_primitives.cmp.eq, h_eq_x, ↓reduceIte, pure_bind]
  rw [show (rust_primitives.unsize
            (RustArray.ofVec #v[rust_primitives.hax.Tuple2.mk r (0 : i64)] : RustArray Pair 1)
            : RustM (rust_primitives.sequence.Seq Pair))
          = RustM.ok ⟨#[rust_primitives.hax.Tuple2.mk r (0 : i64)], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [show (alloc.vec.Impl_2.extend_from_slice Pair alloc.alloc.Global acc
              ⟨#[rust_primitives.hax.Tuple2.mk r (0 : i64)], one_lt_usize_size⟩
            : RustM (alloc.vec.Vec Pair alloc.alloc.Global))
        = RustM.ok (push_pair acc (rust_primitives.hax.Tuple2.mk r (0 : i64)) h_acc) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  rfl

/-- `j = 0`, row non-empty, `row[0] ≠ x` → return acc. -/
private theorem scan_row_desc_zero_nomatch
    (row : RustSlice i64) (r : i64) (x : i64)
    (acc : alloc.vec.Vec Pair alloc.alloc.Global)
    (hne : 0 < row.val.size)
    (hne_x : (row.val[0]'hne) ≠ x) :
    clever_086_get_coords_sorted.scan_row_desc row r x (0 : usize) acc = RustM.ok acc := by
  conv => lhs; unfold clever_086_get_coords_sorted.scan_row_desc
  have h_beq_zero : (((0 : usize) == (0 : usize)) : Bool) = true := by decide
  have h_size_ne_zero : row.val.size ≠ 0 := by omega
  have h_is_empty : (core_models.slice.Impl.is_empty i64 row : RustM Bool) = RustM.ok false := by
    rw [is_empty_eq_size_zero, decide_eq_false h_size_ne_zero]
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have hne' : (0 : usize).toNat < row.val.size := by rw [h_zero_toNat]; exact hne
  have h_idx : (row[(0 : usize)]_? : RustM i64) = RustM.ok (row.val[0]'hne) := by
    show (if h : (0 : usize).toNat < row.val.size then pure (row.val[(0 : usize)]) else .fail .arrayOutOfBounds)
        = RustM.ok (row.val[0]'hne)
    rw [dif_pos hne']; rfl
  have h_eq_x : (row.val[0]'hne == x) = false := by rw [beq_eq_false_iff_ne]; exact hne_x
  simp only [rust_primitives.cmp.eq, h_beq_zero, RustM_ok_bind, ↓reduceIte, pure_bind]
  simp only [h_is_empty, RustM_ok_bind]
  simp only [rust_primitives.hax.logical_op.not, pure_bind]
  show (if (!false) = true then _ else (pure acc : RustM _)) = _
  rw [if_pos (by decide)]
  simp only [h_idx, RustM_ok_bind, rust_primitives.cmp.eq, h_eq_x, ↓reduceIte, pure_bind]
  rfl

/-- `j > 0`, `row[j-1] = x` → push (r, (j-1).toInt64) then recurse with `j-1`. -/
private theorem scan_row_desc_succ_match
    (row : RustSlice i64) (r : i64) (x : i64) (j : usize)
    (acc : alloc.vec.Vec Pair alloc.alloc.Global)
    (hj_pos : 0 < j.toNat)
    (hj_le : j.toNat ≤ row.val.size)
    (h_idx : (j.toNat - 1) < row.val.size)
    (heq : (row.val[j.toNat - 1]'h_idx) = x)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_086_get_coords_sorted.scan_row_desc row r x j acc =
      clever_086_get_coords_sorted.scan_row_desc row r x (j - (1 : usize))
        (push_pair acc
          (rust_primitives.hax.Tuple2.mk r (USize64.toInt64 (j - (1 : usize))))
          h_acc) := by
  conv => lhs; unfold clever_086_get_coords_sorted.scan_row_desc
  have h_beq_zero : ((j == (0 : usize)) : Bool) = false := by
    rw [show (j == (0 : usize)) = decide (j = 0) from rfl]
    rw [decide_eq_false_iff_not]
    intro heq0
    have : j.toNat = (0 : usize).toNat := by rw [heq0]
    show False
    have h_zero : (0 : usize).toNat = 0 := rfl
    omega
  have h_sub_ok : (j -? (1 : usize) : RustM usize) = RustM.ok (j - 1) :=
    usize_sub_one_ok j hj_pos
  have h_sub_toNat : (j - 1).toNat = j.toNat - 1 := usize_sub_one_toNat j hj_pos
  have h_col_lt_row : (j - 1).toNat < row.val.size := by rw [h_sub_toNat]; omega
  have h_idx_get : (row[(j - 1)]_? : RustM i64) = RustM.ok (row.val[(j - 1).toNat]'h_col_lt_row) := by
    show (if h : (j - 1).toNat < row.val.size then pure (row.val[(j - 1)]) else .fail .arrayOutOfBounds)
        = RustM.ok (row.val[(j - 1).toNat]'h_col_lt_row)
    rw [dif_pos h_col_lt_row]; rfl
  have h_eq_eq : (row.val[(j - 1).toNat]'h_col_lt_row) = x := by
    rw [show row.val[(j - 1).toNat]'h_col_lt_row = row.val[j.toNat - 1]'h_idx from
        getElem_congr_idx h_sub_toNat]
    exact heq
  have h_beq_x : (row.val[(j - 1).toNat]'h_col_lt_row == x) = true := by
    rw [beq_iff_eq]; exact h_eq_eq
  have h_cast : (rust_primitives.hax.cast_op (j - 1) : RustM i64) = RustM.ok (USize64.toInt64 (j - 1)) := by
    show (Cast.cast (j - 1) : RustM i64) = _
    rfl
  have h_app_size :
      acc.val.size + (#[rust_primitives.hax.Tuple2.mk r (USize64.toInt64 (j - 1))] : Array Pair).size < USize64.size := by
    show acc.val.size + 1 < USize64.size
    exact h_acc
  simp only [rust_primitives.cmp.eq, h_beq_zero, RustM_ok_bind, ↓reduceIte, pure_bind]
  show (do
          let col ← (j -? (1 : usize) : RustM usize)
          let __do_lift ← (row[col]_? : RustM i64)
          let __do_lift ← __do_lift ==? x
          let __do_jp := fun acc' => clever_086_get_coords_sorted.scan_row_desc row r x col acc'
          if __do_lift = true then do
              let __do_lift ← rust_primitives.hax.cast_op col
              let __do_lift ← rust_primitives.unsize
                  ({ toVec := #v[{ _0 := r, _1 := __do_lift }] } : RustArray Pair 1)
              let acc ← alloc.vec.Impl_2.extend_from_slice Pair alloc.alloc.Global acc __do_lift
              let y ← pure acc
              __do_jp y
            else do
              let y ← pure acc
              __do_jp y) = _
  rw [h_sub_ok]
  simp only [RustM_ok_bind, h_idx_get, rust_primitives.cmp.eq, h_beq_x, ↓reduceIte, pure_bind]
  rw [h_cast]
  simp only [RustM_ok_bind]
  rw [show (rust_primitives.unsize
            (RustArray.ofVec #v[rust_primitives.hax.Tuple2.mk r (USize64.toInt64 (j - 1))] : RustArray Pair 1)
            : RustM (rust_primitives.sequence.Seq Pair))
          = RustM.ok ⟨#[rust_primitives.hax.Tuple2.mk r (USize64.toInt64 (j - 1))], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [show (alloc.vec.Impl_2.extend_from_slice Pair alloc.alloc.Global acc
              ⟨#[rust_primitives.hax.Tuple2.mk r (USize64.toInt64 (j - 1))], one_lt_usize_size⟩
            : RustM (alloc.vec.Vec Pair alloc.alloc.Global))
        = RustM.ok (push_pair acc (rust_primitives.hax.Tuple2.mk r (USize64.toInt64 (j - 1))) h_acc) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  rfl

/-- `j > 0`, `row[j-1] ≠ x` → recurse with `j-1`, acc unchanged. -/
private theorem scan_row_desc_succ_nomatch
    (row : RustSlice i64) (r : i64) (x : i64) (j : usize)
    (acc : alloc.vec.Vec Pair alloc.alloc.Global)
    (hj_pos : 0 < j.toNat)
    (hj_le : j.toNat ≤ row.val.size)
    (h_idx : (j.toNat - 1) < row.val.size)
    (hne_x : (row.val[j.toNat - 1]'h_idx) ≠ x) :
    clever_086_get_coords_sorted.scan_row_desc row r x j acc =
      clever_086_get_coords_sorted.scan_row_desc row r x (j - (1 : usize)) acc := by
  conv => lhs; unfold clever_086_get_coords_sorted.scan_row_desc
  have h_beq_zero : ((j == (0 : usize)) : Bool) = false := by
    rw [show (j == (0 : usize)) = decide (j = 0) from rfl]
    rw [decide_eq_false_iff_not]
    intro heq0
    have : j.toNat = (0 : usize).toNat := by rw [heq0]
    have h_zero : (0 : usize).toNat = 0 := rfl
    omega
  have h_sub_ok : (j -? (1 : usize) : RustM usize) = RustM.ok (j - 1) :=
    usize_sub_one_ok j hj_pos
  have h_sub_toNat : (j - 1).toNat = j.toNat - 1 := usize_sub_one_toNat j hj_pos
  have h_col_lt_row : (j - 1).toNat < row.val.size := by rw [h_sub_toNat]; omega
  have h_idx_get : (row[(j - 1)]_? : RustM i64) = RustM.ok (row.val[(j - 1).toNat]'h_col_lt_row) := by
    show (if h : (j - 1).toNat < row.val.size then pure (row.val[(j - 1)]) else .fail .arrayOutOfBounds)
        = RustM.ok (row.val[(j - 1).toNat]'h_col_lt_row)
    rw [dif_pos h_col_lt_row]; rfl
  have h_ne_eq : (row.val[(j - 1).toNat]'h_col_lt_row) ≠ x := by
    rw [show row.val[(j - 1).toNat]'h_col_lt_row = row.val[j.toNat - 1]'h_idx from
        getElem_congr_idx h_sub_toNat]
    exact hne_x
  have h_beq_x : (row.val[(j - 1).toNat]'h_col_lt_row == x) = false := by
    rw [beq_eq_false_iff_ne]; exact h_ne_eq
  simp only [rust_primitives.cmp.eq, h_beq_zero, RustM_ok_bind, ↓reduceIte, pure_bind]
  show (do
          let col ← (j -? (1 : usize) : RustM usize)
          let __do_lift ← (row[col]_? : RustM i64)
          let __do_lift ← __do_lift ==? x
          let __do_jp := fun acc' => clever_086_get_coords_sorted.scan_row_desc row r x col acc'
          if __do_lift = true then _ else do
              let y ← pure acc
              __do_jp y) = _
  rw [h_sub_ok]
  simp only [RustM_ok_bind, h_idx_get, rust_primitives.cmp.eq, h_beq_x, ↓reduceIte, pure_bind]
  rfl

/-! ## Extend-from-slice bound derivation. -/

/-- If `extend_from_slice acc y` succeeds, then `acc.val.size + y.val.size < USize64.size`. -/
private theorem extend_from_slice_ok_size_bound {α : Type}
    (acc : alloc.vec.Vec α alloc.alloc.Global) (y : rust_primitives.sequence.Seq α)
    (z : alloc.vec.Vec α alloc.alloc.Global)
    (h : alloc.vec.Impl_2.extend_from_slice α alloc.alloc.Global acc y = RustM.ok z) :
    acc.val.size + y.val.size < USize64.size := by
  unfold alloc.vec.Impl_2.extend_from_slice at h
  by_cases hsize : acc.val.size + y.val.size < USize64.size
  · exact hsize
  · exfalso; rw [dif_neg hsize] at h
    -- h : RustM.fail .maximumSizeExceeded = RustM.ok z; contradiction
    cases h

/-! ## Step lemmas for `scan_at`. -/

/-- `i ≥ lst.size` → return acc. -/
private theorem scan_at_oob
    (lst : RustSlice (RustSlice i64)) (x : i64) (i : usize)
    (acc : alloc.vec.Vec Pair alloc.alloc.Global)
    (hi : lst.val.size ≤ i.toNat) :
    clever_086_get_coords_sorted.scan_at lst x i acc = RustM.ok acc := by
  conv => lhs; unfold clever_086_get_coords_sorted.scan_at
  have h_ofNat : (USize64.ofNat lst.val.size).toNat = lst.val.size :=
    USize64.toNat_ofNat_of_lt' lst.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat lst.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- `i < lst.size`, no overflow on i+1 → call scan_row_desc and recurse with i+1. -/
private theorem scan_at_step
    (lst : RustSlice (RustSlice i64)) (x : i64) (i : usize)
    (acc : alloc.vec.Vec Pair alloc.alloc.Global)
    (hi : i.toNat < lst.val.size) :
    clever_086_get_coords_sorted.scan_at lst x i acc =
      ((clever_086_get_coords_sorted.scan_row_desc
          (lst.val[i.toNat]'hi)
          (USize64.toInt64 i)
          x
          (USize64.ofNat (lst.val[i.toNat]'hi).val.size)
          acc) >>= fun next =>
        clever_086_get_coords_sorted.scan_at lst x (i + 1) next) := by
  conv => lhs; unfold clever_086_get_coords_sorted.scan_at
  have h_size_lt : lst.val.size < USize64.size := lst.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat lst.val.size).toNat = lst.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat lst.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (lst[i]_? : RustM (RustSlice i64)) = RustM.ok (lst.val[i.toNat]'hi) := by
    show (if h : i.toNat < lst.val.size then pure (lst.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (lst.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_cast : (rust_primitives.hax.cast_op i : RustM i64) = RustM.ok (USize64.toInt64 i) := by
    show (Cast.cast i : RustM i64) = _
    rfl
  have h_row_len :
      (core_models.slice.Impl.len i64 (lst.val[i.toNat]'hi) : RustM usize)
        = RustM.ok (USize64.ofNat (lst.val[i.toNat]'hi).val.size) := by
    unfold core_models.slice.Impl.len rust_primitives.slice.slice_length
    rfl
  have h_no_ov_i : i.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_size_lt; omega
  have h_no_bv_i :
      BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false :=
    usize_add_one_no_bv i h_no_ov_i
  have h_add_i : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
    show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
    show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
          then (.fail .integerOverflow : RustM usize)
          else pure (i + 1)) = _
    rw [h_no_bv_i]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_cast]
  congr 1
  funext next
  rw [h_add_i]
  rfl

/-- Inner-call fail propagates: if scan_row_desc fails, scan_at fails. -/
private theorem scan_at_step_inner_fail
    (lst : RustSlice (RustSlice i64)) (x : i64) (i : usize)
    (acc : alloc.vec.Vec Pair alloc.alloc.Global)
    (hi : i.toNat < lst.val.size)
    (e : Error)
    (h_row :
      clever_086_get_coords_sorted.scan_row_desc
        (lst.val[i.toNat]'hi)
        (USize64.toInt64 i)
        x
        (USize64.ofNat (lst.val[i.toNat]'hi).val.size)
        acc = RustM.fail e) :
    clever_086_get_coords_sorted.scan_at lst x i acc = RustM.fail e := by
  rw [scan_at_step lst x i acc hi]
  rw [h_row]
  rfl

/-- Inner-call div propagates: if scan_row_desc diverges, scan_at diverges. -/
private theorem scan_at_step_inner_div
    (lst : RustSlice (RustSlice i64)) (x : i64) (i : usize)
    (acc : alloc.vec.Vec Pair alloc.alloc.Global)
    (hi : i.toNat < lst.val.size)
    (h_row :
      clever_086_get_coords_sorted.scan_row_desc
        (lst.val[i.toNat]'hi)
        (USize64.toInt64 i)
        x
        (USize64.ofNat (lst.val[i.toNat]'hi).val.size)
        acc = RustM.div) :
    clever_086_get_coords_sorted.scan_at lst x i acc = RustM.div := by
  rw [scan_at_step lst x i acc hi]
  rw [h_row]
  rfl

/-! ## Specification lists for the output.

`desc_cols_lt row x j` is the list of col indices `c < j` with `row[c] = x`,
in *descending* order of `c`. This captures the order in which
`scan_row_desc` (descending loop from `j-1` down to `0`) emits pushes
through its `j > 0` branch.

`ezo_col row x` is the single extra push the function makes when it
re-enters the `j = 0` branch from `j = 1`: an extra `(r, 0)` if the row
is non-empty and `row[0] = x`. This is the source of the "double
emission" the contract's `cols_non_increasing_within_row` documents.

The full list of cols (descending then ezo) appended by
`scan_row_desc row r x j acc` is `desc_cols_lt row.val x j ++ ezo_col row.val x`.
-/

private def desc_cols_lt (row : Array i64) (x : i64) : Nat → List Nat
  | 0 => []
  | j + 1 =>
      (if h : j < row.size then
         (if (row[j]'h) = x then [j] else [])
       else []) ++ desc_cols_lt row x j

private def ezo_col (row : Array i64) (x : i64) : List Nat :=
  if h : 0 < row.size then
    (if (row[0]'h) = x then [0] else [])
  else []

private def row_appended_cols (row : Array i64) (x : i64) (j : Nat) : List Nat :=
  desc_cols_lt row x j ++ ezo_col row x

/-- Encode a `(r, c)` pair (with `r : i64`, `c : Nat`) into the `Pair`
    used by the extraction. -/
private def encode_pair (r : i64) (c : Nat) : Pair :=
  rust_primitives.hax.Tuple2.mk r (Int64.ofNat c)

@[simp]
private theorem encode_pair_fst (r : i64) (c : Nat) :
    (encode_pair r c)._0 = r := rfl

@[simp]
private theorem encode_pair_snd (r : i64) (c : Nat) :
    (encode_pair r c)._1 = Int64.ofNat c := rfl

/-! ### Basic combinatorial lemmas about `desc_cols_lt` and `ezo_col`. -/

private theorem desc_cols_lt_lt (row : Array i64) (x : i64) :
    ∀ (j : Nat) (c : Nat), c ∈ desc_cols_lt row x j → c < j := by
  intro j
  induction j with
  | zero =>
    intro c hc; simp [desc_cols_lt] at hc
  | succ j ih =>
    intro c hc
    show c < j + 1
    have : desc_cols_lt row x (j + 1) =
        (if h : j < row.size then
           (if (row[j]'h) = x then [j] else [])
         else []) ++ desc_cols_lt row x j := rfl
    rw [this, List.mem_append] at hc
    rcases hc with h_head | h_tail
    · by_cases hj_lt : j < row.size
      · rw [dif_pos hj_lt] at h_head
        by_cases heq : (row[j]'hj_lt) = x
        · rw [if_pos heq] at h_head; simp at h_head; omega
        · rw [if_neg heq] at h_head; simp at h_head
      · rw [dif_neg hj_lt] at h_head; simp at h_head
    · have := ih c h_tail; omega

private theorem desc_cols_lt_bound (row : Array i64) (x : i64) :
    ∀ (j : Nat) (hj : j ≤ row.size) (c : Nat), c ∈ desc_cols_lt row x j → c < row.size := by
  intro j hj c hc
  have h1 : c < j := desc_cols_lt_lt row x j c hc
  omega

private theorem desc_cols_lt_matches (row : Array i64) (x : i64) :
    ∀ (j : Nat) (hj : j ≤ row.size) (c : Nat) (hc : c < row.size),
      c ∈ desc_cols_lt row x j → (row[c]'hc) = x := by
  intro j
  induction j with
  | zero =>
    intro hj c hc hmem; simp [desc_cols_lt] at hmem
  | succ j ih =>
    intro hj c hc hmem
    have hj' : j ≤ row.size := by omega
    have hj_lt : j < row.size := by omega
    have hbody : desc_cols_lt row x (j + 1) =
        (if (row[j]'hj_lt) = x then [j] else []) ++ desc_cols_lt row x j := by
      show (if h : j < row.size then
             (if (row[j]'h) = x then [j] else [])
           else []) ++ desc_cols_lt row x j = _
      rw [dif_pos hj_lt]
    rw [hbody, List.mem_append] at hmem
    rcases hmem with h_head | h_tail
    · by_cases hjx : (row[j]'hj_lt) = x
      · rw [if_pos hjx] at h_head; simp at h_head; subst h_head; exact hjx
      · rw [if_neg hjx] at h_head; simp at h_head
    · exact ih hj' c hc h_tail

private theorem desc_cols_lt_complete (row : Array i64) (x : i64) :
    ∀ (j : Nat) (c : Nat) (hc : c < row.size),
      c < j → (row[c]'hc) = x → c ∈ desc_cols_lt row x j := by
  intro j
  induction j with
  | zero =>
    intro c hc hlt _; omega
  | succ j ih =>
    intro c hc hlt heq
    by_cases hj_lt : j < row.size
    · have hbody : desc_cols_lt row x (j + 1) =
          (if (row[j]'hj_lt) = x then [j] else []) ++ desc_cols_lt row x j := by
        show (if h : j < row.size then
               (if (row[j]'h) = x then [j] else [])
             else []) ++ desc_cols_lt row x j = _
        rw [dif_pos hj_lt]
      rw [hbody, List.mem_append]
      by_cases h_eq_j : c = j
      · left
        have heq' : (row[j]'hj_lt) = x := by
          have h_idx_eq : (row[j]'hj_lt) = (row[c]'hc) :=
            getElem_congr_idx h_eq_j.symm
          rw [h_idx_eq]; exact heq
        rw [if_pos heq']
        exact List.mem_singleton.mpr h_eq_j
      · have hlt' : c < j := by omega
        right; exact ih c hc hlt' heq
    · -- j ≥ row.size: c < j+1 but c < row.size, so c < j or c = j.
      -- Either way, c < j is what we need.
      have hlt' : c < j := by omega
      have hbody : desc_cols_lt row x (j + 1) =
          [] ++ desc_cols_lt row x j := by
        show (if h : j < row.size then
               (if (row[j]'h) = x then [j] else [])
             else []) ++ desc_cols_lt row x j = _
        rw [dif_neg hj_lt]
      rw [hbody]
      simp only [List.nil_append]
      exact ih c hc hlt' heq

private theorem desc_cols_lt_pairwise_gt (row : Array i64) (x : i64) :
    ∀ (j : Nat), (desc_cols_lt row x j).Pairwise (· > ·) := by
  intro j
  induction j with
  | zero => simp [desc_cols_lt]
  | succ j ih =>
    have hbody : desc_cols_lt row x (j + 1) =
        (if h : j < row.size then
           (if (row[j]'h) = x then [j] else [])
         else []) ++ desc_cols_lt row x j := rfl
    rw [hbody]
    by_cases hj_lt : j < row.size
    · rw [dif_pos hj_lt]
      by_cases heq : (row[j]'hj_lt) = x
      · rw [if_pos heq]
        rw [List.pairwise_append]
        refine ⟨List.pairwise_singleton _ _, ih, ?_⟩
        intro a ha b hb
        have ha' : a = j := by simp at ha; exact ha
        have hb_lt : b < j := desc_cols_lt_lt row x j b hb
        show a > b
        omega
      · rw [if_neg heq]; rw [List.nil_append]; exact ih
    · rw [dif_neg hj_lt]; rw [List.nil_append]; exact ih

/-! ### Helper: spec-list `getElem` and indexing. -/

private theorem list_getD_append_left {α} (L M : List α) (k : Nat) (d : α)
    (h : k < L.length) : (L ++ M).getD k d = L.getD k d := by
  have h_lt_app : k < (L ++ M).length := by
    rw [List.length_append]; omega
  rw [(List.getElem_eq_getD (l := L ++ M) (i := k) (h := h_lt_app) d).symm]
  rw [(List.getElem_eq_getD (l := L) (i := k) (h := h) d).symm]
  exact List.getElem_append_left h

/-! ## Bridge: `scan_row_desc` output equals `acc ++ encoded spec list`. -/

/-- Helper: array-form of `acc ++ list-encoded pairs`. -/
private def append_encoded (acc : Array Pair) (r : i64) (cs : List Nat) : Array Pair :=
  acc ++ (cs.map (encode_pair r)).toArray

@[simp]
private theorem append_encoded_nil (acc : Array Pair) (r : i64) :
    append_encoded acc r [] = acc := by
  show acc ++ (([] : List Nat).map (encode_pair r)).toArray = acc
  simp

private theorem append_encoded_cons (acc : Array Pair) (r : i64) (c : Nat) (cs : List Nat) :
    append_encoded acc r (c :: cs) =
      append_encoded (acc ++ #[encode_pair r c]) r cs := by
  show acc ++ ((c :: cs).map (encode_pair r)).toArray =
       (acc ++ #[encode_pair r c]) ++ (cs.map (encode_pair r)).toArray
  rw [List.map_cons, List.toArray_cons, Array.append_assoc]

private theorem append_encoded_append (acc : Array Pair) (r : i64) (L1 L2 : List Nat) :
    append_encoded acc r (L1 ++ L2) =
      append_encoded (append_encoded acc r L1) r L2 := by
  show acc ++ ((L1 ++ L2).map (encode_pair r)).toArray =
       (acc ++ (L1.map (encode_pair r)).toArray) ++ (L2.map (encode_pair r)).toArray
  rw [List.map_append]
  have h_split : (L1.map (encode_pair r) ++ L2.map (encode_pair r)).toArray
               = (L1.map (encode_pair r)).toArray ++ (L2.map (encode_pair r)).toArray := by
    have h := @Array.toArray_append _ (L1.map (encode_pair r))
                ((L2.map (encode_pair r)).toArray)
    rw [List.toList_toArray] at h
    exact h.symm
  rw [h_split, Array.append_assoc]

private theorem append_encoded_size (acc : Array Pair) (r : i64) (cs : List Nat) :
    (append_encoded acc r cs).size = acc.size + cs.length := by
  show (acc ++ (cs.map (encode_pair r)).toArray).size = acc.size + cs.length
  simp [Array.size_append]

private theorem append_encoded_get_left (acc : Array Pair) (r : i64) (cs : List Nat)
    (k : Nat) (hk : k < acc.size)
    (hk' : k < (append_encoded acc r cs).size) :
    (append_encoded acc r cs)[k]'hk' = acc[k]'hk := by
  show (acc ++ (cs.map (encode_pair r)).toArray)[k]'hk' = acc[k]'hk
  exact Array.getElem_append_left hk

private theorem append_encoded_get_right (acc : Array Pair) (r : i64) (cs : List Nat)
    (k : Nat) (h_lo : acc.size ≤ k)
    (hk' : k < (append_encoded acc r cs).size) :
    ∃ (hk_cs : k - acc.size < cs.length),
        (append_encoded acc r cs)[k]'hk' = encode_pair r (cs[k - acc.size]'hk_cs) := by
  have h_size : (append_encoded acc r cs).size = acc.size + cs.length :=
    append_encoded_size acc r cs
  have hk_cs : k - acc.size < cs.length := by
    have : k < acc.size + cs.length := by rw [← h_size]; exact hk'
    omega
  refine ⟨hk_cs, ?_⟩
  show (acc ++ (cs.map (encode_pair r)).toArray)[k]'hk' = encode_pair r (cs[k - acc.size]'hk_cs)
  rw [Array.getElem_append_right h_lo]
  have h_map_size : (cs.map (encode_pair r)).toArray.size = cs.length := by
    simp
  have h_map_lt : k - acc.size < (cs.map (encode_pair r)).toArray.size := by
    rw [h_map_size]; exact hk_cs
  -- Use List.getElem_toArray to bridge.
  have h_map_lt_len : k - acc.size < (cs.map (encode_pair r)).length := by
    rw [List.length_map]; exact hk_cs
  have h_get_bridge :
      (cs.map (encode_pair r)).toArray[k - acc.size]'h_map_lt =
        (cs.map (encode_pair r))[k - acc.size]'h_map_lt_len := by
    rw [List.getElem_toArray]
  rw [h_get_bridge]
  rw [List.getElem_map]

/-! ## Fail-form step lemmas for overflow contradictions. -/

/-- Zero branch with row[0] = x and overflow on the push: scan_row_desc fails. -/
private theorem scan_row_desc_zero_match_fail
    (row : RustSlice i64) (r : i64) (x : i64)
    (acc : alloc.vec.Vec Pair alloc.alloc.Global)
    (hne : 0 < row.val.size)
    (heq : (row.val[0]'hne) = x)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_086_get_coords_sorted.scan_row_desc row r x (0 : usize) acc
      = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_086_get_coords_sorted.scan_row_desc
  have h_beq_zero : (((0 : usize) == (0 : usize)) : Bool) = true := by decide
  have h_size_ne_zero : row.val.size ≠ 0 := by omega
  have h_is_empty : (core_models.slice.Impl.is_empty i64 row : RustM Bool) = RustM.ok false := by
    rw [is_empty_eq_size_zero, decide_eq_false h_size_ne_zero]
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have hne' : (0 : usize).toNat < row.val.size := by rw [h_zero_toNat]; exact hne
  have h_idx : (row[(0 : usize)]_? : RustM i64) = RustM.ok (row.val[0]'hne) := by
    show (if h : (0 : usize).toNat < row.val.size then pure (row.val[(0 : usize)]) else .fail .arrayOutOfBounds)
        = RustM.ok (row.val[0]'hne)
    rw [dif_pos hne']; rfl
  have h_eq_x : (row.val[0]'hne == x) = true := by rw [beq_iff_eq]; exact heq
  have h_app_size_neg :
      ¬ acc.val.size + (#[rust_primitives.hax.Tuple2.mk r (0 : i64)] : Array Pair).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_ext_fail :
      (alloc.vec.Impl_2.extend_from_slice Pair alloc.alloc.Global acc
          ⟨#[rust_primitives.hax.Tuple2.mk r (0 : i64)], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec Pair alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [rust_primitives.cmp.eq, h_beq_zero, RustM_ok_bind, ↓reduceIte, pure_bind]
  simp only [h_is_empty, RustM_ok_bind]
  simp only [rust_primitives.hax.logical_op.not, pure_bind]
  show (if (!false) = true then _ else (pure acc : RustM _)) = _
  rw [if_pos (by decide)]
  simp only [h_idx, RustM_ok_bind, rust_primitives.cmp.eq, h_eq_x, ↓reduceIte, pure_bind]
  rw [show (rust_primitives.unsize
            (RustArray.ofVec #v[rust_primitives.hax.Tuple2.mk r (0 : i64)] : RustArray Pair 1)
            : RustM (rust_primitives.sequence.Seq Pair))
          = RustM.ok ⟨#[rust_primitives.hax.Tuple2.mk r (0 : i64)], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_ext_fail]
  rfl

/-- Succ branch with row[j-1] = x and overflow on the push: scan_row_desc fails. -/
private theorem scan_row_desc_succ_match_fail
    (row : RustSlice i64) (r : i64) (x : i64) (j : usize)
    (acc : alloc.vec.Vec Pair alloc.alloc.Global)
    (hj_pos : 0 < j.toNat)
    (hj_le : j.toNat ≤ row.val.size)
    (h_idx : (j.toNat - 1) < row.val.size)
    (heq : (row.val[j.toNat - 1]'h_idx) = x)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_086_get_coords_sorted.scan_row_desc row r x j acc
      = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_086_get_coords_sorted.scan_row_desc
  have h_beq_zero : ((j == (0 : usize)) : Bool) = false := by
    rw [show (j == (0 : usize)) = decide (j = 0) from rfl]
    rw [decide_eq_false_iff_not]
    intro heq0
    have : j.toNat = (0 : usize).toNat := by rw [heq0]
    have h_zero : (0 : usize).toNat = 0 := rfl
    omega
  have h_sub_ok : (j -? (1 : usize) : RustM usize) = RustM.ok (j - 1) :=
    usize_sub_one_ok j hj_pos
  have h_sub_toNat : (j - 1).toNat = j.toNat - 1 := usize_sub_one_toNat j hj_pos
  have h_col_lt_row : (j - 1).toNat < row.val.size := by rw [h_sub_toNat]; omega
  have h_idx_get : (row[(j - 1)]_? : RustM i64) = RustM.ok (row.val[(j - 1).toNat]'h_col_lt_row) := by
    show (if h : (j - 1).toNat < row.val.size then pure (row.val[(j - 1)]) else .fail .arrayOutOfBounds)
        = RustM.ok (row.val[(j - 1).toNat]'h_col_lt_row)
    rw [dif_pos h_col_lt_row]; rfl
  have h_eq_eq : (row.val[(j - 1).toNat]'h_col_lt_row) = x := by
    rw [show row.val[(j - 1).toNat]'h_col_lt_row = row.val[j.toNat - 1]'h_idx from
        getElem_congr_idx h_sub_toNat]
    exact heq
  have h_beq_x : (row.val[(j - 1).toNat]'h_col_lt_row == x) = true := by
    rw [beq_iff_eq]; exact h_eq_eq
  have h_cast : (rust_primitives.hax.cast_op (j - 1) : RustM i64) = RustM.ok (USize64.toInt64 (j - 1)) := by
    show (Cast.cast (j - 1) : RustM i64) = _
    rfl
  have h_app_size_neg :
      ¬ acc.val.size + (#[rust_primitives.hax.Tuple2.mk r (USize64.toInt64 (j - 1))] : Array Pair).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_ext_fail :
      (alloc.vec.Impl_2.extend_from_slice Pair alloc.alloc.Global acc
          ⟨#[rust_primitives.hax.Tuple2.mk r (USize64.toInt64 (j - 1))], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec Pair alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [rust_primitives.cmp.eq, h_beq_zero, RustM_ok_bind, ↓reduceIte, pure_bind]
  show (do
          let col ← (j -? (1 : usize) : RustM usize)
          let __do_lift ← (row[col]_? : RustM i64)
          let __do_lift ← __do_lift ==? x
          let __do_jp := fun acc' => clever_086_get_coords_sorted.scan_row_desc row r x col acc'
          if __do_lift = true then do
              let __do_lift ← rust_primitives.hax.cast_op col
              let __do_lift ← rust_primitives.unsize
                  ({ toVec := #v[{ _0 := r, _1 := __do_lift }] } : RustArray Pair 1)
              let acc ← alloc.vec.Impl_2.extend_from_slice Pair alloc.alloc.Global acc __do_lift
              let y ← pure acc
              __do_jp y
            else do
              let y ← pure acc
              __do_jp y) = _
  rw [h_sub_ok]
  simp only [RustM_ok_bind, h_idx_get, rust_primitives.cmp.eq, h_beq_x, ↓reduceIte, pure_bind]
  rw [h_cast]
  simp only [RustM_ok_bind]
  rw [show (rust_primitives.unsize
            (RustArray.ofVec #v[rust_primitives.hax.Tuple2.mk r (USize64.toInt64 (j - 1))] : RustArray Pair 1)
            : RustM (rust_primitives.sequence.Seq Pair))
          = RustM.ok ⟨#[rust_primitives.hax.Tuple2.mk r (USize64.toInt64 (j - 1))], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_ext_fail]
  rfl

/-! ## Strong induction characterizing `scan_row_desc`'s output. -/

/-- If `scan_row_desc row r x j acc` returns `RustM.ok res`, then `res.val`
    equals `acc.val` with the descending matches in `[0, j)` appended (in
    descending order), followed by the optional ezo `(r, 0)`. -/
private theorem scan_row_desc_correct (row : RustSlice i64) (r : i64) (x : i64) :
    ∀ (n : Nat) (j : usize) (acc res : alloc.vec.Vec Pair alloc.alloc.Global),
      j.toNat ≤ n →
      j.toNat ≤ row.val.size →
      clever_086_get_coords_sorted.scan_row_desc row r x j acc = RustM.ok res →
      res.val = append_encoded acc.val r (row_appended_cols row.val x j.toNat) := by
  intro n
  induction n with
  | zero =>
    intro j acc res hn hj_le hres
    have hj_zero : j.toNat = 0 := by omega
    -- We have j = (0 : usize) since j.toNat = 0
    have hj_eq : j = 0 := USize64.toNat_inj.mp (by rw [hj_zero]; rfl)
    subst hj_eq
    -- Now in the j = 0 branch.
    by_cases hsize_zero : row.val.size = 0
    · -- Empty row case: scan_row_desc_zero_empty.
      rw [scan_row_desc_zero_empty row r x acc hsize_zero] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      show acc.val = append_encoded acc.val r (row_appended_cols row.val x (0 : usize).toNat)
      have h_zero : (0 : usize).toNat = 0 := rfl
      rw [h_zero]
      show acc.val = append_encoded acc.val r (desc_cols_lt row.val x 0 ++ ezo_col row.val x)
      show acc.val = append_encoded acc.val r ([] ++ ezo_col row.val x)
      have h_ezo : ezo_col row.val x = [] := by
        show (if h : 0 < row.val.size then (if (row.val[0]'h) = x then [0] else []) else []) = []
        rw [dif_neg (by omega)]
      rw [h_ezo]
      simp [append_encoded_nil]
    · have h_size_pos : 0 < row.val.size := Nat.pos_of_ne_zero hsize_zero
      by_cases hmatch : (row.val[0]'h_size_pos) = x
      · -- Match case: scan_row_desc_zero_match (need acc size bound).
        -- Derive size bound from hres.
        -- First, observe: in this branch, the function emits acc ++ [(r, 0)] iff acc.val.size + 1 < USize64.size.
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [scan_row_desc_zero_match row r x acc h_size_pos hmatch h_acc] at hres
          injection hres with h_eq
          injection h_eq with h_eq'
          subst h_eq'
          show (push_pair acc (rust_primitives.hax.Tuple2.mk r (0 : i64)) h_acc).val =
                append_encoded acc.val r (row_appended_cols row.val x (0 : usize).toNat)
          have h_zero : (0 : usize).toNat = 0 := rfl
          rw [h_zero]
          have h_ezo : ezo_col row.val x = [0] := by
            show (if h : 0 < row.val.size then (if (row.val[0]'h) = x then [0] else []) else []) = [0]
            rw [dif_pos h_size_pos, if_pos hmatch]
          show (acc.val ++ #[rust_primitives.hax.Tuple2.mk r (0 : i64)]) =
                append_encoded acc.val r (desc_cols_lt row.val x 0 ++ ezo_col row.val x)
          show (acc.val ++ #[rust_primitives.hax.Tuple2.mk r (0 : i64)]) =
                append_encoded acc.val r ([] ++ ezo_col row.val x)
          rw [h_ezo, List.nil_append]
          rfl
        · -- Overflow: would fail. Derive contradiction.
          exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          -- Unfold scan_row_desc at zero-match case and show it fails.
          -- We need a fail-form lemma for the zero-match overflow case.
          -- Alternative: unfold directly here.
          conv at hres => lhs; unfold clever_086_get_coords_sorted.scan_row_desc
          have h_beq_zero : (((0 : usize) == (0 : usize)) : Bool) = true := by decide
          have h_size_ne_zero : row.val.size ≠ 0 := by omega
          have h_is_empty : (core_models.slice.Impl.is_empty i64 row : RustM Bool) = RustM.ok false := by
            rw [is_empty_eq_size_zero, decide_eq_false h_size_ne_zero]
          have h_zero_toNat : (0 : usize).toNat = 0 := rfl
          have hne' : (0 : usize).toNat < row.val.size := by rw [h_zero_toNat]; exact h_size_pos
          have h_idx : (row[(0 : usize)]_? : RustM i64) = RustM.ok (row.val[0]'h_size_pos) := by
            show (if h : (0 : usize).toNat < row.val.size then pure (row.val[(0 : usize)]) else .fail .arrayOutOfBounds)
                = RustM.ok (row.val[0]'h_size_pos)
            rw [dif_pos hne']; rfl
          have h_eq_x : (row.val[0]'h_size_pos == x) = true := by rw [beq_iff_eq]; exact hmatch
          have h_app_size_neg :
              ¬ acc.val.size + (#[rust_primitives.hax.Tuple2.mk r (0 : i64)] : Array Pair).size < USize64.size := by
            show ¬ acc.val.size + 1 < USize64.size
            omega
          have h_ext_fail :
              (alloc.vec.Impl_2.extend_from_slice Pair alloc.alloc.Global acc
                  ⟨#[rust_primitives.hax.Tuple2.mk r (0 : i64)], one_lt_usize_size⟩
                : RustM (alloc.vec.Vec Pair alloc.alloc.Global))
              = RustM.fail .maximumSizeExceeded := by
            unfold alloc.vec.Impl_2.extend_from_slice
            rw [dif_neg h_app_size_neg]
          simp only [rust_primitives.cmp.eq, h_beq_zero, RustM_ok_bind, ↓reduceIte, pure_bind] at hres
          simp only [h_is_empty, RustM_ok_bind] at hres
          simp only [rust_primitives.hax.logical_op.not, pure_bind] at hres
          rw [show ((!false) = true) from by decide] at hres
          simp only [↓reduceIte] at hres
          simp only [h_idx, RustM_ok_bind, rust_primitives.cmp.eq, h_eq_x, ↓reduceIte, pure_bind] at hres
          rw [show (rust_primitives.unsize
                    (RustArray.ofVec #v[rust_primitives.hax.Tuple2.mk r (0 : i64)] : RustArray Pair 1)
                    : RustM (rust_primitives.sequence.Seq Pair))
                  = RustM.ok ⟨#[rust_primitives.hax.Tuple2.mk r (0 : i64)], one_lt_usize_size⟩ from rfl] at hres
          simp only [RustM_ok_bind] at hres
          rw [h_ext_fail] at hres
          cases hres
      · -- No-match case: scan_row_desc_zero_nomatch.
        rw [scan_row_desc_zero_nomatch row r x acc h_size_pos hmatch] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        show acc.val = append_encoded acc.val r (row_appended_cols row.val x (0 : usize).toNat)
        have h_zero : (0 : usize).toNat = 0 := rfl
        rw [h_zero]
        show acc.val = append_encoded acc.val r (desc_cols_lt row.val x 0 ++ ezo_col row.val x)
        show acc.val = append_encoded acc.val r ([] ++ ezo_col row.val x)
        have h_ezo : ezo_col row.val x = [] := by
          show (if h : 0 < row.val.size then (if (row.val[0]'h) = x then [0] else []) else []) = []
          rw [dif_pos h_size_pos, if_neg hmatch]
        rw [h_ezo]
        simp [append_encoded_nil]
  | succ n ih =>
    intro j acc res hn hj_le hres
    by_cases hj_zero : j.toNat = 0
    · -- Same as base case
      have hj_eq : j = 0 := USize64.toNat_inj.mp (by rw [hj_zero]; rfl)
      subst hj_eq
      by_cases hsize_zero : row.val.size = 0
      · rw [scan_row_desc_zero_empty row r x acc hsize_zero] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        show acc.val = append_encoded acc.val r (row_appended_cols row.val x (0 : usize).toNat)
        have h_zero : (0 : usize).toNat = 0 := rfl
        rw [h_zero]
        show acc.val = append_encoded acc.val r (desc_cols_lt row.val x 0 ++ ezo_col row.val x)
        show acc.val = append_encoded acc.val r ([] ++ ezo_col row.val x)
        have h_ezo : ezo_col row.val x = [] := by
          show (if h : 0 < row.val.size then (if (row.val[0]'h) = x then [0] else []) else []) = []
          rw [dif_neg (by omega)]
        rw [h_ezo]; simp [append_encoded_nil]
      · have h_size_pos : 0 < row.val.size := Nat.pos_of_ne_zero hsize_zero
        by_cases hmatch : (row.val[0]'h_size_pos) = x
        · by_cases h_acc : acc.val.size + 1 < USize64.size
          · rw [scan_row_desc_zero_match row r x acc h_size_pos hmatch h_acc] at hres
            injection hres with h_eq
            injection h_eq with h_eq'
            subst h_eq'
            show (push_pair acc (rust_primitives.hax.Tuple2.mk r (0 : i64)) h_acc).val =
                  append_encoded acc.val r (row_appended_cols row.val x (0 : usize).toNat)
            have h_zero : (0 : usize).toNat = 0 := rfl
            rw [h_zero]
            show (acc.val ++ #[rust_primitives.hax.Tuple2.mk r (0 : i64)]) =
                  append_encoded acc.val r (desc_cols_lt row.val x 0 ++ ezo_col row.val x)
            show (acc.val ++ #[rust_primitives.hax.Tuple2.mk r (0 : i64)]) =
                  append_encoded acc.val r ([] ++ ezo_col row.val x)
            have h_ezo : ezo_col row.val x = [0] := by
              show (if h : 0 < row.val.size then (if (row.val[0]'h) = x then [0] else []) else []) = [0]
              rw [dif_pos h_size_pos, if_pos hmatch]
            rw [h_ezo]
            simp only [List.nil_append]
            show (acc.val ++ #[rust_primitives.hax.Tuple2.mk r (0 : i64)]) =
                  append_encoded acc.val r [0]
            rfl
          · exfalso
            -- Inline contradiction: scan_row_desc returns fail.
            have h_big : USize64.size ≤ acc.val.size + 1 := by omega
            conv at hres => lhs; unfold clever_086_get_coords_sorted.scan_row_desc
            have h_beq_zero : (((0 : usize) == (0 : usize)) : Bool) = true := by decide
            have h_size_ne_zero : row.val.size ≠ 0 := by omega
            have h_is_empty : (core_models.slice.Impl.is_empty i64 row : RustM Bool) = RustM.ok false := by
              rw [is_empty_eq_size_zero, decide_eq_false h_size_ne_zero]
            have hne' : (0 : usize).toNat < row.val.size := h_size_pos
            have h_idx : (row[(0 : usize)]_? : RustM i64) = RustM.ok (row.val[0]'h_size_pos) := by
              show (if h : (0 : usize).toNat < row.val.size then pure (row.val[(0 : usize)]) else .fail .arrayOutOfBounds)
                  = RustM.ok (row.val[0]'h_size_pos)
              rw [dif_pos hne']; rfl
            have h_eq_x : (row.val[0]'h_size_pos == x) = true := by rw [beq_iff_eq]; exact hmatch
            have h_app_size_neg :
                ¬ acc.val.size + (#[rust_primitives.hax.Tuple2.mk r (0 : i64)] : Array Pair).size < USize64.size := by
              show ¬ acc.val.size + 1 < USize64.size; omega
            have h_ext_fail :
                (alloc.vec.Impl_2.extend_from_slice Pair alloc.alloc.Global acc
                    ⟨#[rust_primitives.hax.Tuple2.mk r (0 : i64)], one_lt_usize_size⟩
                  : RustM (alloc.vec.Vec Pair alloc.alloc.Global))
                = RustM.fail .maximumSizeExceeded := by
              unfold alloc.vec.Impl_2.extend_from_slice
              rw [dif_neg h_app_size_neg]
            simp only [rust_primitives.cmp.eq, h_beq_zero, RustM_ok_bind, ↓reduceIte, pure_bind] at hres
            simp only [h_is_empty, RustM_ok_bind] at hres
            simp only [rust_primitives.hax.logical_op.not, pure_bind] at hres
            rw [show ((!false) = true) from by decide] at hres
            simp only [↓reduceIte] at hres
            simp only [h_idx, RustM_ok_bind, rust_primitives.cmp.eq, h_eq_x, ↓reduceIte, pure_bind] at hres
            rw [show (rust_primitives.unsize
                      (RustArray.ofVec #v[rust_primitives.hax.Tuple2.mk r (0 : i64)] : RustArray Pair 1)
                      : RustM (rust_primitives.sequence.Seq Pair))
                    = RustM.ok ⟨#[rust_primitives.hax.Tuple2.mk r (0 : i64)], one_lt_usize_size⟩ from rfl] at hres
            simp only [RustM_ok_bind] at hres
            rw [h_ext_fail] at hres
            cases hres
        · rw [scan_row_desc_zero_nomatch row r x acc h_size_pos hmatch] at hres
          injection hres with h_eq
          injection h_eq with h_eq'
          subst h_eq'
          show acc.val = append_encoded acc.val r (row_appended_cols row.val x (0 : usize).toNat)
          have h_zero : (0 : usize).toNat = 0 := rfl
          rw [h_zero]
          show acc.val = append_encoded acc.val r (desc_cols_lt row.val x 0 ++ ezo_col row.val x)
          show acc.val = append_encoded acc.val r ([] ++ ezo_col row.val x)
          have h_ezo : ezo_col row.val x = [] := by
            show (if h : 0 < row.val.size then (if (row.val[0]'h) = x then [0] else []) else []) = []
            rw [dif_pos h_size_pos, if_neg hmatch]
          rw [h_ezo]; simp [append_encoded_nil]
    · -- j.toNat > 0 case.
      have hj_pos : 0 < j.toNat := Nat.pos_of_ne_zero hj_zero
      have h_idx : (j.toNat - 1) < row.val.size := by omega
      have h_sub_toNat : (j - 1).toNat = j.toNat - 1 := usize_sub_one_toNat j hj_pos
      have h_meas : (j - 1).toNat ≤ n := by rw [h_sub_toNat]; omega
      have h_sub_le : (j - 1).toNat ≤ row.val.size := by rw [h_sub_toNat]; omega
      by_cases hmatch : (row.val[j.toNat - 1]'h_idx) = x
      · by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [scan_row_desc_succ_match row r x j acc hj_pos hj_le h_idx hmatch h_acc] at hres
          have ih_app := ih (j - 1) _ res h_meas h_sub_le hres
          rw [h_sub_toNat] at ih_app
          have h_step :
              row_appended_cols row.val x j.toNat =
              [(j.toNat - 1)] ++ row_appended_cols row.val x (j.toNat - 1) := by
            have hjj : j.toNat = (j.toNat - 1) + 1 := by omega
            rw [hjj]
            show desc_cols_lt row.val x ((j.toNat - 1) + 1) ++ ezo_col row.val x =
                [(j.toNat - 1)] ++ (desc_cols_lt row.val x (j.toNat - 1) ++ ezo_col row.val x)
            have h_dc : desc_cols_lt row.val x ((j.toNat - 1) + 1) =
                [(j.toNat - 1)] ++ desc_cols_lt row.val x (j.toNat - 1) := by
              have : desc_cols_lt row.val x ((j.toNat - 1) + 1) =
                  (if h : (j.toNat - 1) < row.val.size then
                     (if (row.val[(j.toNat - 1)]'h) = x then [(j.toNat - 1)] else [])
                   else []) ++ desc_cols_lt row.val x (j.toNat - 1) := rfl
              rw [this, dif_pos h_idx, if_pos hmatch]
            rw [h_dc]; rw [List.append_assoc]
          rw [h_step]
          rw [append_encoded_append]
          show res.val = append_encoded
                          (append_encoded acc.val r [(j.toNat - 1)]) r
                          (row_appended_cols row.val x (j.toNat - 1))
          -- ih_app says: res.val = append_encoded (acc ++ [(r, j-1)]).val r (row_appended_cols row.val x (j.toNat - 1))
          -- where (acc ++ [(r, j-1)]).val = acc.val ++ #[(r, j-1)] = append_encoded acc.val r [j.toNat - 1]
          -- since encode_pair r (j.toNat - 1) = Tuple2.mk r (Int64.ofNat (j.toNat - 1))
          -- vs the actual push uses Tuple2.mk r (USize64.toInt64 (j - 1))
          -- These are equal if (Int64.ofNat (j.toNat - 1) = USize64.toInt64 (j - 1)).
          -- USize64.toInt64 (j - 1) = Int64.ofNat (j - 1).toNat = Int64.ofNat (j.toNat - 1). Equal!
          have h_int64_eq : USize64.toInt64 (j - 1) = Int64.ofNat (j.toNat - 1) := by
            show Int64.ofNat (j - 1).toNat = Int64.ofNat (j.toNat - 1)
            rw [h_sub_toNat]
          have h_acc_eq :
              (push_pair acc (rust_primitives.hax.Tuple2.mk r (USize64.toInt64 (j - 1))) h_acc).val =
              append_encoded acc.val r [j.toNat - 1] := by
            show acc.val ++ #[rust_primitives.hax.Tuple2.mk r (USize64.toInt64 (j - 1))] =
                  acc.val ++ (([j.toNat - 1] : List Nat).map (encode_pair r)).toArray
            rw [h_int64_eq]
            congr 1
          rw [← h_acc_eq]
          exact ih_app
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [scan_row_desc_succ_match_fail row r x j acc hj_pos hj_le h_idx hmatch h_big] at hres
          cases hres
      · rw [scan_row_desc_succ_nomatch row r x j acc hj_pos hj_le h_idx hmatch] at hres
        have ih_app := ih (j - 1) acc res h_meas h_sub_le hres
        rw [h_sub_toNat] at ih_app
        have h_step :
            row_appended_cols row.val x j.toNat =
            row_appended_cols row.val x (j.toNat - 1) := by
          have hjj : j.toNat = (j.toNat - 1) + 1 := by omega
          rw [hjj]
          show desc_cols_lt row.val x ((j.toNat - 1) + 1) ++ ezo_col row.val x =
              desc_cols_lt row.val x (j.toNat - 1) ++ ezo_col row.val x
          have h_dc : desc_cols_lt row.val x ((j.toNat - 1) + 1) =
              desc_cols_lt row.val x (j.toNat - 1) := by
            have : desc_cols_lt row.val x ((j.toNat - 1) + 1) =
                (if h : (j.toNat - 1) < row.val.size then
                   (if (row.val[(j.toNat - 1)]'h) = x then [(j.toNat - 1)] else [])
                 else []) ++ desc_cols_lt row.val x (j.toNat - 1) := rfl
            rw [this, dif_pos h_idx, if_neg hmatch]
            rw [List.nil_append]
          rw [h_dc]
        rw [h_step]
        exact ih_app

/-! ## Spec list for `scan_at`: all coords emitted across rows. -/

/-- For rows `[i, i + n)` of `lst`, the full list of pairs emitted (matching
    the order produced by `scan_at`). `n` is fuel; the canonical use is
    `n = lst.size - i`. The encoding uses `Int64.ofNat i` for the row index
    (definitionally equal to `USize64.toInt64 i_usize` when
    `i_usize.toNat = i`, which it is during execution). -/
private def matrix_emit_list (lst : Array (RustSlice i64)) (x : i64) :
    Nat → Nat → List Pair
  | 0, _ => []
  | n + 1, i =>
      if h : i < lst.size then
        ((row_appended_cols (lst[i]'h).val x (lst[i]'h).val.size).map
            (encode_pair (Int64.ofNat i)))
          ++ matrix_emit_list lst x n (i + 1)
      else
        []

/-! ## Strong induction characterizing `scan_at`'s output. -/

private theorem scan_at_correct (lst : RustSlice (RustSlice i64)) (x : i64) :
    ∀ (n : Nat) (i : usize) (acc res : alloc.vec.Vec Pair alloc.alloc.Global),
      lst.val.size - i.toNat ≤ n →
      i.toNat ≤ lst.val.size →
      clever_086_get_coords_sorted.scan_at lst x i acc = RustM.ok res →
      res.val = acc.val ++ (matrix_emit_list lst.val x n i.toNat).toArray := by
  intro n
  induction n with
  | zero =>
    intro i acc res hm hi_le hres
    have hi_ge : lst.val.size ≤ i.toNat := by omega
    rw [scan_at_oob lst x i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    show acc.val = acc.val ++ ((matrix_emit_list lst.val x 0 i.toNat).toArray)
    have h_emit : matrix_emit_list lst.val x 0 i.toNat = [] := rfl
    rw [h_emit]
    show acc.val = acc.val ++ (([] : List Pair).toArray)
    rfl
  | succ n ih =>
    intro i acc res hm hi_le hres
    by_cases hi_ge : lst.val.size ≤ i.toNat
    · rw [scan_at_oob lst x i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      show acc.val = acc.val ++ ((matrix_emit_list lst.val x (n + 1) i.toNat).toArray)
      have h_emit : matrix_emit_list lst.val x (n + 1) i.toNat = [] := by
        show (if h : i.toNat < lst.val.size then _ else ([] : List Pair)) = []
        rw [dif_neg (by omega)]
      rw [h_emit]
      show acc.val = acc.val ++ (([] : List Pair).toArray)
      rfl
    · have hi_lt : i.toNat < lst.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : lst.val.size < USize64.size := lst.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ lst.val.size := by rw [h_i1]; omega
      have h_meas : lst.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      rw [scan_at_step lst x i acc hi_lt] at hres
      generalize h_row_def :
        clever_086_get_coords_sorted.scan_row_desc
          (lst.val[i.toNat]'hi_lt)
          (USize64.toInt64 i)
          x
          (USize64.ofNat (lst.val[i.toNat]'hi_lt).val.size)
          acc = row_res at hres
      cases row_res with
      | none =>
        exfalso
        have hh : (do let acc' ← (none : RustM (alloc.vec.Vec Pair alloc.alloc.Global));
                       clever_086_get_coords_sorted.scan_at lst x (i + 1) acc')
                  = RustM.ok res := hres
        cases hh
      | some res' =>
        cases res' with
        | error e =>
          exfalso
          have hh : (do let acc' ← (some (Except.error e) :
                                    RustM (alloc.vec.Vec Pair alloc.alloc.Global));
                         clever_086_get_coords_sorted.scan_at lst x (i + 1) acc')
                    = RustM.ok res := hres
          cases hh
        | ok next =>
          have h_row_ok :
              clever_086_get_coords_sorted.scan_row_desc
                (lst.val[i.toNat]'hi_lt)
                (USize64.toInt64 i)
                x
                (USize64.ofNat (lst.val[i.toNat]'hi_lt).val.size)
                acc = RustM.ok next := h_row_def
          simp only [RustM_ok_bind] at hres
          have h_row_size_lt : (lst.val[i.toNat]'hi_lt).val.size < USize64.size :=
            (lst.val[i.toNat]'hi_lt).size_lt_usizeSize
          have h_j_eq :
              (USize64.ofNat (lst.val[i.toNat]'hi_lt).val.size).toNat
                = (lst.val[i.toNat]'hi_lt).val.size :=
            USize64.toNat_ofNat_of_lt' h_row_size_lt
          have h_j_le :
              (USize64.ofNat (lst.val[i.toNat]'hi_lt).val.size).toNat
                ≤ (lst.val[i.toNat]'hi_lt).val.size := by
            rw [h_j_eq]; exact Nat.le_refl _
          have h_row_correct := scan_row_desc_correct
              (lst.val[i.toNat]'hi_lt) (USize64.toInt64 i) x
              (lst.val[i.toNat]'hi_lt).val.size
              (USize64.ofNat (lst.val[i.toNat]'hi_lt).val.size)
              acc next h_j_le h_j_le h_row_ok
          rw [h_j_eq] at h_row_correct
          have ih_app := ih (i + 1) next res h_meas h_i1_le hres
          rw [h_i1] at ih_app
          rw [ih_app, h_row_correct]
          have h_emit_succ :
              matrix_emit_list lst.val x (n + 1) i.toNat =
              ((row_appended_cols (lst.val[i.toNat]'hi_lt).val x
                 (lst.val[i.toNat]'hi_lt).val.size).map
                (encode_pair (Int64.ofNat i.toNat)))
                ++ matrix_emit_list lst.val x n (i.toNat + 1) := by
            show (if h : i.toNat < lst.val.size then _ else ([] : List Pair)) = _
            rw [dif_pos hi_lt]
          rw [h_emit_succ]
          have h_enc_eq :
              (encode_pair (USize64.toInt64 i) :
                Nat → Pair) = encode_pair (Int64.ofNat i.toNat) := rfl
          show append_encoded acc.val (USize64.toInt64 i)
                  (row_appended_cols (lst.val[i.toNat]'hi_lt).val x
                    (lst.val[i.toNat]'hi_lt).val.size)
                ++ (matrix_emit_list lst.val x n (i.toNat + 1)).toArray
              = acc.val
                ++ (((row_appended_cols (lst.val[i.toNat]'hi_lt).val x
                       (lst.val[i.toNat]'hi_lt).val.size).map
                      (encode_pair (Int64.ofNat i.toNat)))
                  ++ matrix_emit_list lst.val x n (i.toNat + 1)).toArray
          show (acc.val
                ++ ((row_appended_cols (lst.val[i.toNat]'hi_lt).val x
                     (lst.val[i.toNat]'hi_lt).val.size).map
                    (encode_pair (USize64.toInt64 i))).toArray)
                ++ (matrix_emit_list lst.val x n (i.toNat + 1)).toArray
              = acc.val
                ++ (((row_appended_cols (lst.val[i.toNat]'hi_lt).val x
                       (lst.val[i.toNat]'hi_lt).val.size).map
                      (encode_pair (Int64.ofNat i.toNat)))
                  ++ matrix_emit_list lst.val x n (i.toNat + 1)).toArray
          rw [h_enc_eq]
          have h_split :
              (((row_appended_cols (lst.val[i.toNat]'hi_lt).val x
                  (lst.val[i.toNat]'hi_lt).val.size).map
                  (encode_pair (Int64.ofNat i.toNat)))
                ++ matrix_emit_list lst.val x n (i.toNat + 1)).toArray
                = ((row_appended_cols (lst.val[i.toNat]'hi_lt).val x
                    (lst.val[i.toNat]'hi_lt).val.size).map
                    (encode_pair (Int64.ofNat i.toNat))).toArray
                  ++ (matrix_emit_list lst.val x n (i.toNat + 1)).toArray := by
            have h := @Array.toArray_append _
                ((row_appended_cols (lst.val[i.toNat]'hi_lt).val x
                    (lst.val[i.toNat]'hi_lt).val.size).map
                    (encode_pair (Int64.ofNat i.toNat)))
                ((matrix_emit_list lst.val x n (i.toNat + 1)).toArray)
            rw [List.toList_toArray] at h
            exact h.symm
          rw [h_split, Array.append_assoc]

/-! ## Specialization to `get_coords_sorted`. -/

private theorem get_coords_sorted_correct (lst : RustSlice (RustSlice i64)) (x : i64)
    (v : alloc.vec.Vec Pair alloc.alloc.Global)
    (hres : clever_086_get_coords_sorted.get_coords_sorted lst x = RustM.ok v) :
    v.val = (matrix_emit_list lst.val x lst.val.size 0).toArray := by
  unfold clever_086_get_coords_sorted.get_coords_sorted at hres
  have h_new : (alloc.vec.Impl.new (rust_primitives.hax.Tuple2 i64 i64)
                  rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec Pair alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new, RustM_ok_bind] at hres
  let acc0 : alloc.vec.Vec Pair alloc.alloc.Global := ⟨(List.nil).toArray, by grind⟩
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_meas : lst.val.size - (0 : usize).toNat ≤ lst.val.size := by
    rw [h_zero_toNat]; omega
  have h_i_le : (0 : usize).toNat ≤ lst.val.size := by rw [h_zero_toNat]; omega
  have h_acc0 := scan_at_correct lst x lst.val.size (0 : usize) acc0 v
                    h_meas h_i_le hres
  rw [h_zero_toNat] at h_acc0
  have h_acc0_val : acc0.val = #[] := rfl
  rw [h_acc0_val] at h_acc0
  show v.val = (matrix_emit_list lst.val x lst.val.size 0).toArray
  rw [h_acc0]
  show #[] ++ (matrix_emit_list lst.val x lst.val.size 0).toArray =
        (matrix_emit_list lst.val x lst.val.size 0).toArray
  simp

/-! ## Lookup lemmas for `matrix_emit_list`.

Bridge index access into `matrix_emit_list lst x n i_start` to the
sub-pieces (`row_pairs` for `i_start` and the recursive `matrix_emit_list`
for `i_start + 1`). -/

/-- Row's emit list as a definition for ergonomic reasoning. -/
private def row_pairs (lst : Array (RustSlice i64)) (x : i64) (i : Nat) (h : i < lst.size) :
    List Pair :=
  (row_appended_cols (lst[i]'h).val x (lst[i]'h).val.size).map (encode_pair (Int64.ofNat i))

/-- Step equation: `matrix_emit_list lst x (n+1) i = row_pairs lst x i h ++ matrix_emit_list lst x n (i+1)` when `i < lst.size`. -/
private theorem matrix_emit_list_step
    (lst : Array (RustSlice i64)) (x : i64) (n i : Nat) (h : i < lst.size) :
    matrix_emit_list lst x (n + 1) i =
      row_pairs lst x i h ++ matrix_emit_list lst x n (i + 1) := by
  show (if hi : i < lst.size then
          ((row_appended_cols (lst[i]'hi).val x (lst[i]'hi).val.size).map
              (encode_pair (Int64.ofNat i)))
            ++ matrix_emit_list lst x n (i + 1)
        else []) = _
  rw [dif_pos h]; rfl

/-- Step equation for OOB. -/
private theorem matrix_emit_list_step_oob
    (lst : Array (RustSlice i64)) (x : i64) (n i : Nat) (h : lst.size ≤ i) :
    matrix_emit_list lst x (n + 1) i = [] := by
  show (if hi : i < lst.size then _ else ([] : List Pair)) = []
  rw [dif_neg (by omega)]

/-- Row pairs length. -/
private theorem row_pairs_length (lst : Array (RustSlice i64)) (x : i64) (i : Nat) (h : i < lst.size) :
    (row_pairs lst x i h).length =
      (row_appended_cols (lst[i]'h).val x (lst[i]'h).val.size).length := by
  unfold row_pairs; rw [List.length_map]

/-- Soundness of `row_pairs`. -/
private theorem row_pairs_sound (lst : Array (RustSlice i64)) (x : i64) (i : Nat) (h : i < lst.size)
    (k : Nat) (hk : k < (row_pairs lst x i h).length) :
    ∃ (j : Nat) (hj : j < (lst[i]'h).val.size),
      ((row_pairs lst x i h)[k]'hk)._0 = Int64.ofNat i ∧
      ((row_pairs lst x i h)[k]'hk)._1 = Int64.ofNat j ∧
      ((lst[i]'h).val[j]'hj) = x := by
  have hk_len : k < (row_appended_cols (lst[i]'h).val x (lst[i]'h).val.size).length := by
    rw [← row_pairs_length]; exact hk
  let c := (row_appended_cols (lst[i]'h).val x (lst[i]'h).val.size)[k]'hk_len
  have h_c_def : c = (row_appended_cols (lst[i]'h).val x (lst[i]'h).val.size)[k]'hk_len := rfl
  have h_c_mem : c ∈ row_appended_cols (lst[i]'h).val x (lst[i]'h).val.size :=
    List.getElem_mem _
  have h_mem : c ∈ (desc_cols_lt (lst[i]'h).val x (lst[i]'h).val.size)
              ∨ c ∈ (ezo_col (lst[i]'h).val x) := by
    have : c ∈ desc_cols_lt (lst[i]'h).val x (lst[i]'h).val.size
        ++ ezo_col (lst[i]'h).val x := h_c_mem
    exact List.mem_append.mp this
  have h_c_in_size : c < (lst[i]'h).val.size := by
    rcases h_mem with h_d | h_e
    · have h := desc_cols_lt_lt (lst[i]'h).val x (lst[i]'h).val.size c h_d
      omega
    · unfold ezo_col at h_e
      by_cases h0 : 0 < (lst[i]'h).val.size
      · rw [dif_pos h0] at h_e
        by_cases hrow_x : ((lst[i]'h).val[0]'h0) = x
        · rw [if_pos hrow_x] at h_e
          have : c = 0 := List.mem_singleton.mp h_e
          rw [this]; exact h0
        · rw [if_neg hrow_x] at h_e
          exact absurd h_e List.not_mem_nil
      · rw [dif_neg h0] at h_e
        exact absurd h_e List.not_mem_nil
  have h_c_match : ((lst[i]'h).val[c]'h_c_in_size) = x := by
    rcases h_mem with h_d | h_e
    · exact desc_cols_lt_matches (lst[i]'h).val x (lst[i]'h).val.size
              (Nat.le_refl _) c h_c_in_size h_d
    · unfold ezo_col at h_e
      by_cases h0 : 0 < (lst[i]'h).val.size
      · rw [dif_pos h0] at h_e
        by_cases hrow_x : ((lst[i]'h).val[0]'h0) = x
        · rw [if_pos hrow_x] at h_e
          have h_c_zero : c = 0 := List.mem_singleton.mp h_e
          have h_get_eq : ((lst[i]'h).val[c]'h_c_in_size) = ((lst[i]'h).val[0]'h0) :=
            getElem_congr_idx h_c_zero
          rw [h_get_eq]; exact hrow_x
        · rw [if_neg hrow_x] at h_e
          exact absurd h_e List.not_mem_nil
      · rw [dif_neg h0] at h_e
        exact absurd h_e List.not_mem_nil
  refine ⟨c, h_c_in_size, ?_, ?_, h_c_match⟩
  · show ((row_pairs lst x i h)[k]'hk)._0 = Int64.ofNat i
    unfold row_pairs
    rw [List.getElem_map]
    rfl
  · show ((row_pairs lst x i h)[k]'hk)._1 = Int64.ofNat c
    unfold row_pairs
    rw [List.getElem_map]
    rfl

/-- Completeness of `row_pairs`: every `j` with `row[j] = x` is reported. -/
private theorem row_pairs_complete (lst : Array (RustSlice i64)) (x : i64) (i : Nat) (h : i < lst.size)
    (j : Nat) (hj : j < (lst[i]'h).val.size) (hval : ((lst[i]'h).val[j]'hj) = x) :
    ∃ (k : Nat) (hk : k < (row_pairs lst x i h).length),
      ((row_pairs lst x i h)[k]'hk)._0 = Int64.ofNat i ∧
      ((row_pairs lst x i h)[k]'hk)._1 = Int64.ofNat j := by
  have h_j_in_dc : j ∈ desc_cols_lt (lst[i]'h).val x (lst[i]'h).val.size :=
    desc_cols_lt_complete (lst[i]'h).val x (lst[i]'h).val.size j hj hj hval
  have h_j_in : j ∈ row_appended_cols (lst[i]'h).val x (lst[i]'h).val.size := by
    unfold row_appended_cols
    rw [List.mem_append]; left; exact h_j_in_dc
  obtain ⟨k, hk_lt, hk_eq⟩ := List.mem_iff_getElem.mp h_j_in
  have hk_len : k < (row_pairs lst x i h).length := by
    rw [row_pairs_length]; exact hk_lt
  refine ⟨k, hk_len, ?_, ?_⟩
  · unfold row_pairs
    rw [List.getElem_map]
    rfl
  · unfold row_pairs
    rw [List.getElem_map]
    show Int64.ofNat ((row_appended_cols (lst[i]'h).val x (lst[i]'h).val.size)[k]'_) = Int64.ofNat j
    have h_idx_eq : ((row_appended_cols (lst[i]'h).val x (lst[i]'h).val.size)[k]'(by rw [← List.length_map]; exact hk_len)) = j := by
      have hk_lt' : k < (row_appended_cols (lst[i]'h).val x (lst[i]'h).val.size).length := by
        rw [← row_pairs_length]; exact hk_len
      have := hk_eq
      simp at this
      exact this
    rw [h_idx_eq]

/-- Get an element at index `k < (row_pairs).length` in `matrix_emit_list (n+1) i_start`. -/
private theorem matrix_emit_list_get_at_row
    (lst : Array (RustSlice i64)) (x : i64) (n i_start : Nat) (h : i_start < lst.size)
    (k : Nat) (hk_row : k < (row_pairs lst x i_start h).length)
    (hk_full : k < (matrix_emit_list lst x (n + 1) i_start).length) :
    (matrix_emit_list lst x (n + 1) i_start)[k]'hk_full
      = (row_pairs lst x i_start h)[k]'hk_row := by
  have h_step := matrix_emit_list_step lst x n i_start h
  rw [List.getElem_of_eq h_step]
  exact List.getElem_append_left hk_row

/-- Get an element at index `k ≥ (row_pairs).length` in `matrix_emit_list (n+1) i_start`. -/
private theorem matrix_emit_list_get_at_rest
    (lst : Array (RustSlice i64)) (x : i64) (n i_start : Nat) (h : i_start < lst.size)
    (k : Nat) (hk_ge : (row_pairs lst x i_start h).length ≤ k)
    (hk_full : k < (matrix_emit_list lst x (n + 1) i_start).length)
    (hk_rest : k - (row_pairs lst x i_start h).length < (matrix_emit_list lst x n (i_start + 1)).length) :
    (matrix_emit_list lst x (n + 1) i_start)[k]'hk_full
      = (matrix_emit_list lst x n (i_start + 1))[k - (row_pairs lst x i_start h).length]'hk_rest := by
  have h_step := matrix_emit_list_step lst x n i_start h
  rw [List.getElem_of_eq h_step]
  exact List.getElem_append_right hk_ge

/-- Length of `matrix_emit_list (n+1) i_start` when in-range. -/
private theorem matrix_emit_list_length_succ
    (lst : Array (RustSlice i64)) (x : i64) (n i_start : Nat) (h : i_start < lst.size) :
    (matrix_emit_list lst x (n + 1) i_start).length
      = (row_pairs lst x i_start h).length + (matrix_emit_list lst x n (i_start + 1)).length := by
  rw [matrix_emit_list_step lst x n i_start h, List.length_append]

/-- Soundness of `matrix_emit_list`: each pair at position `k` corresponds to a
    valid `(i, j)` with `lst[i][j] = x` and `i_start ≤ i`. -/
private theorem matrix_emit_list_sound (lst : Array (RustSlice i64)) (x : i64) :
    ∀ (n i_start k : Nat),
      ∀ (hk : k < (matrix_emit_list lst x n i_start).length),
      ∃ (i : Nat) (j : Nat) (hi : i < lst.size)
        (hj : j < (lst[i]'hi).val.size),
        i_start ≤ i ∧
        ((matrix_emit_list lst x n i_start)[k]'hk)._0 = Int64.ofNat i ∧
        ((matrix_emit_list lst x n i_start)[k]'hk)._1 = Int64.ofNat j ∧
        ((lst[i]'hi).val[j]'hj) = x := by
  intro n
  induction n with
  | zero =>
    intro i_start k hk
    simp [matrix_emit_list] at hk
  | succ n ih =>
    intro i_start k hk
    by_cases hi_lt : i_start < lst.size
    · rw [matrix_emit_list_length_succ lst x n i_start hi_lt] at hk
      by_cases h_in_row : k < (row_pairs lst x i_start hi_lt).length
      · have hk_full : k < (matrix_emit_list lst x (n + 1) i_start).length := by
          rw [matrix_emit_list_length_succ lst x n i_start hi_lt]; omega
        obtain ⟨j, hj, h_fst, h_snd, h_val⟩ :=
          row_pairs_sound lst x i_start hi_lt k h_in_row
        refine ⟨i_start, j, hi_lt, hj, Nat.le_refl _, ?_, ?_, h_val⟩
        · rw [matrix_emit_list_get_at_row lst x n i_start hi_lt k h_in_row hk_full]
          exact h_fst
        · rw [matrix_emit_list_get_at_row lst x n i_start hi_lt k h_in_row hk_full]
          exact h_snd
      · have h_in_row_ge : (row_pairs lst x i_start hi_lt).length ≤ k := by
          omega
        have hk_rest :
            k - (row_pairs lst x i_start hi_lt).length
              < (matrix_emit_list lst x n (i_start + 1)).length := by omega
        have hk_full : k < (matrix_emit_list lst x (n + 1) i_start).length := by
          rw [matrix_emit_list_length_succ lst x n i_start hi_lt]; omega
        obtain ⟨i, j, hi, hj, h_lo, h_fst, h_snd, h_val⟩ :=
          ih (i_start + 1) (k - (row_pairs lst x i_start hi_lt).length) hk_rest
        refine ⟨i, j, hi, hj, by omega, ?_, ?_, h_val⟩
        · rw [matrix_emit_list_get_at_rest lst x n i_start hi_lt k h_in_row_ge hk_full hk_rest]
          exact h_fst
        · rw [matrix_emit_list_get_at_rest lst x n i_start hi_lt k h_in_row_ge hk_full hk_rest]
          exact h_snd
    · rw [matrix_emit_list_step_oob lst x n i_start (by omega)] at hk
      simp at hk

/-- Completeness of `matrix_emit_list`: every cell `(i, j)` with `lst[i][j] = x`
    and `i_start ≤ i` is reported. -/
private theorem matrix_emit_list_complete (lst : Array (RustSlice i64)) (x : i64) :
    ∀ (n i_start : Nat),
      lst.size - i_start ≤ n → i_start ≤ lst.size →
      ∀ (i j : Nat) (hi : i < lst.size) (hj : j < (lst[i]'hi).val.size),
        ((lst[i]'hi).val[j]'hj) = x →
        i_start ≤ i →
        ∃ (k : Nat) (hk : k < (matrix_emit_list lst x n i_start).length),
          ((matrix_emit_list lst x n i_start)[k]'hk)._0 = Int64.ofNat i ∧
          ((matrix_emit_list lst x n i_start)[k]'hk)._1 = Int64.ofNat j := by
  intro n
  induction n with
  | zero =>
    intro i_start k_meas hi_le i j hi hj hval h_lo
    exfalso; omega
  | succ n ih =>
    intro i_start k_meas hi_le i j hi hj hval h_lo
    by_cases hi_lt : i_start < lst.size
    · by_cases h_eq : i = i_start
      · -- Row found! Use row_pairs_complete.
        have h_j_match : ((lst[i_start]'hi_lt).val[j]'(h_eq ▸ hj)) = x := h_eq ▸ hval
        obtain ⟨k, hk_row, h_fst, h_snd⟩ :=
          row_pairs_complete lst x i_start hi_lt j (h_eq ▸ hj) h_j_match
        have hk_full : k < (matrix_emit_list lst x (n + 1) i_start).length := by
          rw [matrix_emit_list_length_succ lst x n i_start hi_lt]; omega
        refine ⟨k, hk_full, ?_, ?_⟩
        · rw [matrix_emit_list_get_at_row lst x n i_start hi_lt k hk_row hk_full]
          rw [h_fst]; rw [h_eq]
        · rw [matrix_emit_list_get_at_row lst x n i_start hi_lt k hk_row hk_full]
          exact h_snd
      · have h_lo' : i_start + 1 ≤ i := by omega
        have h_meas' : lst.size - (i_start + 1) ≤ n := by omega
        have h_i1_le : i_start + 1 ≤ lst.size := by omega
        obtain ⟨k', hk', h_fst, h_snd⟩ :=
          ih (i_start + 1) h_meas' h_i1_le i j hi hj hval h_lo'
        refine ⟨(row_pairs lst x i_start hi_lt).length + k', ?_, ?_, ?_⟩
        · rw [matrix_emit_list_length_succ lst x n i_start hi_lt]; omega
        · have h_full_lt :
              (row_pairs lst x i_start hi_lt).length + k'
                < (matrix_emit_list lst x (n + 1) i_start).length := by
            rw [matrix_emit_list_length_succ lst x n i_start hi_lt]; omega
          have h_ge : (row_pairs lst x i_start hi_lt).length
                ≤ (row_pairs lst x i_start hi_lt).length + k' := by omega
          have hk_rest :
              (row_pairs lst x i_start hi_lt).length + k'
                - (row_pairs lst x i_start hi_lt).length
                < (matrix_emit_list lst x n (i_start + 1)).length := by
            have : (row_pairs lst x i_start hi_lt).length + k'
                  - (row_pairs lst x i_start hi_lt).length = k' := by omega
            rw [this]; exact hk'
          rw [matrix_emit_list_get_at_rest lst x n i_start hi_lt _ h_ge h_full_lt hk_rest]
          have h_get_eq :
              (matrix_emit_list lst x n (i_start + 1))[(row_pairs lst x i_start hi_lt).length + k'
                - (row_pairs lst x i_start hi_lt).length]'hk_rest
              = (matrix_emit_list lst x n (i_start + 1))[k']'hk' := by
            congr 1; omega
          rw [h_get_eq]; exact h_fst
        · have h_full_lt :
              (row_pairs lst x i_start hi_lt).length + k'
                < (matrix_emit_list lst x (n + 1) i_start).length := by
            rw [matrix_emit_list_length_succ lst x n i_start hi_lt]; omega
          have h_ge : (row_pairs lst x i_start hi_lt).length
                ≤ (row_pairs lst x i_start hi_lt).length + k' := by omega
          have hk_rest :
              (row_pairs lst x i_start hi_lt).length + k'
                - (row_pairs lst x i_start hi_lt).length
                < (matrix_emit_list lst x n (i_start + 1)).length := by
            have : (row_pairs lst x i_start hi_lt).length + k'
                  - (row_pairs lst x i_start hi_lt).length = k' := by omega
            rw [this]; exact hk'
          rw [matrix_emit_list_get_at_rest lst x n i_start hi_lt _ h_ge h_full_lt hk_rest]
          have h_get_eq :
              (matrix_emit_list lst x n (i_start + 1))[(row_pairs lst x i_start hi_lt).length + k'
                - (row_pairs lst x i_start hi_lt).length]'hk_rest
              = (matrix_emit_list lst x n (i_start + 1))[k']'hk' := by
            congr 1; omega
          rw [h_get_eq]; exact h_snd
    · exfalso; omega

/-! ## Additional structural helpers for the ordering obligations. -/

/-- desc_cols_lt is non-increasing (weakening of strict descending). -/
private theorem desc_cols_lt_pairwise_ge (row : Array i64) (x : i64) (j : Nat) :
    (desc_cols_lt row x j).Pairwise (· ≥ ·) :=
  (desc_cols_lt_pairwise_gt row x j).imp Nat.le_of_lt

/-- row_appended_cols (= desc_cols_lt ++ ezo_col) is non-increasing. -/
private theorem row_appended_cols_pairwise_ge (row : Array i64) (x : i64) (j : Nat) :
    (row_appended_cols row x j).Pairwise (· ≥ ·) := by
  unfold row_appended_cols
  rw [List.pairwise_append]
  refine ⟨desc_cols_lt_pairwise_ge row x j, ?_, ?_⟩
  · unfold ezo_col
    by_cases h0 : 0 < row.size
    · rw [dif_pos h0]
      by_cases hr : (row[0]'h0) = x
      · rw [if_pos hr]; exact List.pairwise_singleton _ _
      · rw [if_neg hr]; exact List.Pairwise.nil
    · rw [dif_neg h0]; exact List.Pairwise.nil
  · intro a _ b hb
    unfold ezo_col at hb
    by_cases h0 : 0 < row.size
    · rw [dif_pos h0] at hb
      by_cases hr : (row[0]'h0) = x
      · rw [if_pos hr] at hb
        have hb_eq : b = 0 := List.mem_singleton.mp hb
        rw [hb_eq]
        show a ≥ 0
        omega
      · rw [if_neg hr] at hb; exact absurd hb List.not_mem_nil
    · rw [dif_neg h0] at hb; exact absurd hb List.not_mem_nil

/-- All entries of `row_pairs lst x i h` have `._0 = Int64.ofNat i`. -/
private theorem row_pairs_all_row_eq (lst : Array (RustSlice i64)) (x : i64)
    (i : Nat) (h : i < lst.size) (k : Nat) (hk : k < (row_pairs lst x i h).length) :
    ((row_pairs lst x i h)[k]'hk)._0 = Int64.ofNat i := by
  unfold row_pairs
  have hk_len : k < (row_appended_cols (lst[i]'h).val x (lst[i]'h).val.size).length := by
    rw [← row_pairs_length]; exact hk
  rw [List.getElem_map]
  rfl

/-- `row_pairs[k]._1 = Int64.ofNat (row_appended_cols[k])` -/
private theorem row_pairs_col_eq (lst : Array (RustSlice i64)) (x : i64)
    (i : Nat) (h : i < lst.size) (k : Nat) (hk : k < (row_pairs lst x i h).length) :
    ∃ (hk_app : k < (row_appended_cols (lst[i]'h).val x (lst[i]'h).val.size).length),
      ((row_pairs lst x i h)[k]'hk)._1 = Int64.ofNat
        ((row_appended_cols (lst[i]'h).val x (lst[i]'h).val.size)[k]'hk_app) := by
  have hk_app : k < (row_appended_cols (lst[i]'h).val x (lst[i]'h).val.size).length := by
    rw [← row_pairs_length]; exact hk
  refine ⟨hk_app, ?_⟩
  unfold row_pairs
  rw [List.getElem_map]
  rfl

/-- The actual `Nat` col value at position `k` in `row_pairs lst x i h`. -/
private noncomputable def row_pairs_col_at (lst : Array (RustSlice i64)) (x : i64)
    (i : Nat) (h : i < lst.size) (k : Nat) (hk : k < (row_pairs lst x i h).length) : Nat :=
  (row_appended_cols (lst[i]'h).val x (lst[i]'h).val.size)[k]'(by
    rw [← row_pairs_length]; exact hk)

/-- Row index in matrix_emit_list is bounded below by i_start. -/
private theorem matrix_emit_list_row_lb (lst : Array (RustSlice i64)) (x : i64) :
    ∀ (n i_start k : Nat) (hk : k < (matrix_emit_list lst x n i_start).length),
      ∃ (i : Nat) (_ : i < lst.size),
        i_start ≤ i ∧
        ((matrix_emit_list lst x n i_start)[k]'hk)._0 = Int64.ofNat i := by
  intro n i_start k hk
  obtain ⟨i, _, hi, _, h_lo, h_fst, _, _⟩ := matrix_emit_list_sound lst x n i_start k hk
  exact ⟨i, hi, h_lo, h_fst⟩

/-- Row indices are non-decreasing across positions in matrix_emit_list. -/
private theorem matrix_emit_list_rows_le_succ (lst : Array (RustSlice i64)) (x : i64)
    (hrows : lst.size ≤ 2^63) :
    ∀ (n i_start k : Nat) (hk : k + 1 < (matrix_emit_list lst x n i_start).length),
      ∀ (i_k i_k1 : Nat),
        ((matrix_emit_list lst x n i_start)[k]'(Nat.lt_of_succ_lt hk))._0 = Int64.ofNat i_k →
        ((matrix_emit_list lst x n i_start)[k + 1]'hk)._0 = Int64.ofNat i_k1 →
        i_k < lst.size → i_k1 < lst.size →
        i_k ≤ i_k1 := by
  intro n
  induction n with
  | zero =>
    intro i_start k hk i_k i_k1 _ _ _ _
    exfalso; simp [matrix_emit_list] at hk
  | succ n ih =>
    intro i_start k hk i_k i_k1 h_k_eq h_k1_eq hi_k hi_k1
    by_cases hi_lt : i_start < lst.size
    · rw [matrix_emit_list_length_succ lst x n i_start hi_lt] at hk
      by_cases h_in_k : k < (row_pairs lst x i_start hi_lt).length
      · by_cases h_in_k1 : k + 1 < (row_pairs lst x i_start hi_lt).length
        · -- Both in row_pairs: rows equal to i_start.
          have hk_full : k < (matrix_emit_list lst x (n + 1) i_start).length := by
            rw [matrix_emit_list_length_succ lst x n i_start hi_lt]; omega
          have hk1_full : k + 1 < (matrix_emit_list lst x (n + 1) i_start).length := by
            rw [matrix_emit_list_length_succ lst x n i_start hi_lt]; omega
          rw [matrix_emit_list_get_at_row lst x n i_start hi_lt k h_in_k hk_full] at h_k_eq
          rw [matrix_emit_list_get_at_row lst x n i_start hi_lt (k+1) h_in_k1 hk1_full] at h_k1_eq
          have h_row_k := row_pairs_all_row_eq lst x i_start hi_lt k h_in_k
          have h_row_k1 := row_pairs_all_row_eq lst x i_start hi_lt (k+1) h_in_k1
          rw [h_row_k] at h_k_eq
          rw [h_row_k1] at h_k1_eq
          -- Both = Int64.ofNat i_start
          have h_ofNat_inj : ∀ (a b : Nat), a < 2^63 → b < 2^63 →
                                Int64.ofNat a = Int64.ofNat b → a = b := by
            intro a b ha hb heq
            have ha' := Int64.toInt_ofNat_of_lt ha
            have hb' := Int64.toInt_ofNat_of_lt hb
            have : (Int64.ofNat a).toInt = (Int64.ofNat b).toInt := by rw [heq]
            rw [ha', hb'] at this
            exact Int.ofNat.inj this
          have h_i_k_eq : i_k = i_start := h_ofNat_inj i_k i_start (by omega) (by omega) h_k_eq.symm
          have h_i_k1_eq : i_k1 = i_start := h_ofNat_inj i_k1 i_start (by omega) (by omega) h_k1_eq.symm
          omega
        · -- k in row_pairs, k+1 in rest. row[k] = i_start, row[k+1] ≥ i_start + 1.
          have h_in_k1_ge_pre : (row_pairs lst x i_start hi_lt).length ≤ k + 1 := by omega
          have hk_full : k < (matrix_emit_list lst x (n + 1) i_start).length := by
            rw [matrix_emit_list_length_succ lst x n i_start hi_lt]; omega
          rw [matrix_emit_list_get_at_row lst x n i_start hi_lt k h_in_k hk_full] at h_k_eq
          have h_row_k := row_pairs_all_row_eq lst x i_start hi_lt k h_in_k
          rw [h_row_k] at h_k_eq
          have h_ofNat_inj : ∀ (a b : Nat), a < 2^63 → b < 2^63 →
                                Int64.ofNat a = Int64.ofNat b → a = b := by
            intro a b ha hb heq
            have ha' := Int64.toInt_ofNat_of_lt ha
            have hb' := Int64.toInt_ofNat_of_lt hb
            have : (Int64.ofNat a).toInt = (Int64.ofNat b).toInt := by rw [heq]
            rw [ha', hb'] at this
            exact Int.ofNat.inj this
          have h_i_k_eq : i_k = i_start := h_ofNat_inj i_k i_start (by omega) (by omega) h_k_eq.symm
          -- Now show i_k1 ≥ i_start + 1
          have hk1_full : k + 1 < (matrix_emit_list lst x (n + 1) i_start).length := by
            rw [matrix_emit_list_length_succ lst x n i_start hi_lt]; omega
          have h_in_k1_ge : (row_pairs lst x i_start hi_lt).length ≤ k + 1 := h_in_k1_ge_pre
          have hk1_rest : k + 1 - (row_pairs lst x i_start hi_lt).length
                          < (matrix_emit_list lst x n (i_start + 1)).length := by omega
          rw [matrix_emit_list_get_at_rest lst x n i_start hi_lt (k+1) h_in_k1_ge hk1_full hk1_rest] at h_k1_eq
          obtain ⟨i_k1', _, h_lo', h_fst'⟩ := matrix_emit_list_row_lb lst x n (i_start + 1)
              (k + 1 - (row_pairs lst x i_start hi_lt).length) hk1_rest
          rw [h_fst'] at h_k1_eq
          have h_i_k1_eq : i_k1 = i_k1' :=
            h_ofNat_inj i_k1 i_k1' (by omega) (by omega) h_k1_eq.symm
          omega
      · -- k in rest, then k+1 also in rest
        have h_in_k_ge : (row_pairs lst x i_start hi_lt).length ≤ k := by omega
        have h_in_k1_ge : (row_pairs lst x i_start hi_lt).length ≤ k + 1 := by omega
        have hk_rest : k - (row_pairs lst x i_start hi_lt).length
                        < (matrix_emit_list lst x n (i_start + 1)).length := by omega
        have hk1_rest : k + 1 - (row_pairs lst x i_start hi_lt).length
                        < (matrix_emit_list lst x n (i_start + 1)).length := by omega
        have hk_full : k < (matrix_emit_list lst x (n + 1) i_start).length := by
          rw [matrix_emit_list_length_succ lst x n i_start hi_lt]; omega
        have hk1_full : k + 1 < (matrix_emit_list lst x (n + 1) i_start).length := by
          rw [matrix_emit_list_length_succ lst x n i_start hi_lt]; omega
        rw [matrix_emit_list_get_at_rest lst x n i_start hi_lt k h_in_k_ge hk_full hk_rest] at h_k_eq
        rw [matrix_emit_list_get_at_rest lst x n i_start hi_lt (k+1) h_in_k1_ge hk1_full hk1_rest] at h_k1_eq
        have h_idx_eq :
            k + 1 - (row_pairs lst x i_start hi_lt).length
              = (k - (row_pairs lst x i_start hi_lt).length) + 1 := by omega
        have h_k1_eq' :
            ((matrix_emit_list lst x n (i_start + 1))[(k - (row_pairs lst x i_start hi_lt).length) + 1]'(by rw [← h_idx_eq]; exact hk1_rest))._0 = Int64.ofNat i_k1 := by
          have := h_k1_eq
          rw [show (matrix_emit_list lst x n (i_start + 1))[(k - (row_pairs lst x i_start hi_lt).length) + 1]'(by rw [← h_idx_eq]; exact hk1_rest)
              = (matrix_emit_list lst x n (i_start + 1))[k + 1 - (row_pairs lst x i_start hi_lt).length]'hk1_rest from
              getElem_congr_idx h_idx_eq.symm]
          exact this
        exact ih (i_start + 1) (k - (row_pairs lst x i_start hi_lt).length)
                (by rw [← h_idx_eq]; exact hk1_rest) i_k i_k1 h_k_eq h_k1_eq' hi_k hi_k1
    · exfalso
      rw [matrix_emit_list_step_oob lst x n i_start (by omega)] at hk
      simp at hk

/-! ## Injectivity of Int64.ofNat on small Nats. -/

private theorem Int64_ofNat_inj_small (a b : Nat) (ha : a < 2^63) (hb : b < 2^63)
    (heq : Int64.ofNat a = Int64.ofNat b) : a = b := by
  have ha' := Int64.toInt_ofNat_of_lt ha
  have hb' := Int64.toInt_ofNat_of_lt hb
  have : (Int64.ofNat a).toInt = (Int64.ofNat b).toInt := by rw [heq]
  rw [ha', hb'] at this
  exact Int.ofNat.inj this

/-- Any element of `row_appended_cols row x j` is `< row.size`. -/
private theorem row_appended_cols_elem_lt (row : Array i64) (x : i64) (j : Nat)
    (hj : j ≤ row.size) (c : Nat) (hc : c ∈ row_appended_cols row x j) : c < row.size := by
  unfold row_appended_cols at hc
  rw [List.mem_append] at hc
  rcases hc with h_d | h_e
  · have := desc_cols_lt_lt row x j c h_d; omega
  · unfold ezo_col at h_e
    by_cases h0 : 0 < row.size
    · rw [dif_pos h0] at h_e
      by_cases hr : (row[0]'h0) = x
      · rw [if_pos hr] at h_e
        have : c = 0 := List.mem_singleton.mp h_e
        rw [this]; exact h0
      · rw [if_neg hr] at h_e; exact absurd h_e List.not_mem_nil
    · rw [dif_neg h0] at h_e; exact absurd h_e List.not_mem_nil

/-! ## Cols-within-row helper. -/

private theorem matrix_emit_list_cols_within_row (lst : Array (RustSlice i64)) (x : i64)
    (hrows : lst.size ≤ 2^63)
    (hcols : ∀ (k : Nat) (hk : k < lst.size), (lst[k]'hk).val.size ≤ 2^63) :
    ∀ (n i_start k : Nat) (hk : k + 1 < (matrix_emit_list lst x n i_start).length),
      ((matrix_emit_list lst x n i_start)[k]'(Nat.lt_of_succ_lt hk))._0
        = ((matrix_emit_list lst x n i_start)[k + 1]'hk)._0 →
      ∀ (c_k c_k1 : Nat),
        ((matrix_emit_list lst x n i_start)[k]'(Nat.lt_of_succ_lt hk))._1 = Int64.ofNat c_k →
        ((matrix_emit_list lst x n i_start)[k + 1]'hk)._1 = Int64.ofNat c_k1 →
        c_k < 2^63 → c_k1 < 2^63 →
        c_k1 ≤ c_k := by
  intro n
  induction n with
  | zero =>
    intro i_start k hk _ c_k c_k1 _ _ _ _
    exfalso; simp [matrix_emit_list] at hk
  | succ n ih =>
    intro i_start k hk hrow_eq c_k c_k1 h_c_k h_c_k1 hc_k_63 hc_k1_63
    by_cases hi_lt : i_start < lst.size
    · rw [matrix_emit_list_length_succ lst x n i_start hi_lt] at hk
      have hi_lt_63 : i_start < 2^63 := by omega
      have h_in_k1_full : k + 1 < (matrix_emit_list lst x (n + 1) i_start).length := by
        rw [matrix_emit_list_length_succ lst x n i_start hi_lt]; omega
      have h_in_k_full : k < (matrix_emit_list lst x (n + 1) i_start).length := by
        rw [matrix_emit_list_length_succ lst x n i_start hi_lt]; omega
      by_cases h_in_k1 : k + 1 < (row_pairs lst x i_start hi_lt).length
      · -- Both k and k+1 in row_pairs.
        have h_in_k : k < (row_pairs lst x i_start hi_lt).length := by omega
        rw [matrix_emit_list_get_at_row lst x n i_start hi_lt k h_in_k h_in_k_full] at h_c_k
        rw [matrix_emit_list_get_at_row lst x n i_start hi_lt (k+1) h_in_k1 h_in_k1_full] at h_c_k1
        obtain ⟨hk_app, h_eq_k⟩ := row_pairs_col_eq lst x i_start hi_lt k h_in_k
        obtain ⟨hk1_app, h_eq_k1⟩ := row_pairs_col_eq lst x i_start hi_lt (k+1) h_in_k1
        rw [h_eq_k] at h_c_k
        rw [h_eq_k1] at h_c_k1
        -- h_c_k : Int64.ofNat (row_appended_cols ...)[k] = Int64.ofNat c_k
        have h_row_size_le : (lst[i_start]'hi_lt).val.size ≤ 2^63 := hcols i_start hi_lt
        have h_app_k_lt : (row_appended_cols (lst[i_start]'hi_lt).val x
                            (lst[i_start]'hi_lt).val.size)[k]'hk_app
                          < (lst[i_start]'hi_lt).val.size :=
          row_appended_cols_elem_lt _ x _ (Nat.le_refl _) _ (List.getElem_mem _)
        have h_app_k_63 : (row_appended_cols (lst[i_start]'hi_lt).val x
                            (lst[i_start]'hi_lt).val.size)[k]'hk_app < 2^63 := by omega
        have h_app_k1_lt : (row_appended_cols (lst[i_start]'hi_lt).val x
                              (lst[i_start]'hi_lt).val.size)[k+1]'hk1_app
                            < (lst[i_start]'hi_lt).val.size :=
          row_appended_cols_elem_lt _ x _ (Nat.le_refl _) _ (List.getElem_mem _)
        have h_app_k1_63 : (row_appended_cols (lst[i_start]'hi_lt).val x
                              (lst[i_start]'hi_lt).val.size)[k+1]'hk1_app < 2^63 := by omega
        have h_c_k_eq : c_k = (row_appended_cols (lst[i_start]'hi_lt).val x
                                (lst[i_start]'hi_lt).val.size)[k]'hk_app :=
          Int64_ofNat_inj_small _ _ hc_k_63 h_app_k_63 h_c_k.symm
        have h_c_k1_eq : c_k1 = (row_appended_cols (lst[i_start]'hi_lt).val x
                                  (lst[i_start]'hi_lt).val.size)[k+1]'hk1_app :=
          Int64_ofNat_inj_small _ _ hc_k1_63 h_app_k1_63 h_c_k1.symm
        -- pairwise non-increasing
        have h_pw := row_appended_cols_pairwise_ge (lst[i_start]'hi_lt).val x
                      (lst[i_start]'hi_lt).val.size
        have h_ge : (row_appended_cols (lst[i_start]'hi_lt).val x
                      (lst[i_start]'hi_lt).val.size)[k]'hk_app ≥
                    (row_appended_cols (lst[i_start]'hi_lt).val x
                      (lst[i_start]'hi_lt).val.size)[k+1]'hk1_app :=
          List.pairwise_iff_getElem.mp h_pw k (k+1) hk_app hk1_app (by omega)
        rw [h_c_k_eq, h_c_k1_eq]; exact h_ge
      · -- k+1 in rest
        have h_in_k1_ge : (row_pairs lst x i_start hi_lt).length ≤ k + 1 := by omega
        have hk1_rest : k + 1 - (row_pairs lst x i_start hi_lt).length
                        < (matrix_emit_list lst x n (i_start + 1)).length := by omega
        by_cases h_in_k : k < (row_pairs lst x i_start hi_lt).length
        · -- k in row_pairs, k+1 in rest. Rows differ — contradicts hrow_eq.
          exfalso
          rw [matrix_emit_list_get_at_row lst x n i_start hi_lt k h_in_k h_in_k_full] at hrow_eq
          have h_row_k := row_pairs_all_row_eq lst x i_start hi_lt k h_in_k
          rw [h_row_k] at hrow_eq
          rw [matrix_emit_list_get_at_rest lst x n i_start hi_lt (k+1) h_in_k1_ge
                h_in_k1_full hk1_rest] at hrow_eq
          obtain ⟨i_k1', hi_k1', h_lo', h_fst'⟩ := matrix_emit_list_row_lb lst x n (i_start + 1)
              (k + 1 - (row_pairs lst x i_start hi_lt).length) hk1_rest
          rw [h_fst'] at hrow_eq
          have h_i_k1_63 : i_k1' < 2^63 := by omega
          have h_eq_nat : i_start = i_k1' :=
            Int64_ofNat_inj_small i_start i_k1' hi_lt_63 h_i_k1_63 hrow_eq
          omega
        · -- both in rest. Recurse.
          have h_in_k_ge : (row_pairs lst x i_start hi_lt).length ≤ k := by omega
          have hk_rest : k - (row_pairs lst x i_start hi_lt).length
                          < (matrix_emit_list lst x n (i_start + 1)).length := by omega
          have h_idx_eq : k + 1 - (row_pairs lst x i_start hi_lt).length
                        = (k - (row_pairs lst x i_start hi_lt).length) + 1 := by omega
          -- Translate h_c_k, h_c_k1, hrow_eq to be about matrix_emit_list lst x n (i_start+1)
          rw [matrix_emit_list_get_at_rest lst x n i_start hi_lt k h_in_k_ge
                h_in_k_full hk_rest] at h_c_k
          rw [matrix_emit_list_get_at_rest lst x n i_start hi_lt (k+1) h_in_k1_ge
                h_in_k1_full hk1_rest] at h_c_k1
          rw [matrix_emit_list_get_at_rest lst x n i_start hi_lt k h_in_k_ge
                h_in_k_full hk_rest] at hrow_eq
          rw [matrix_emit_list_get_at_rest lst x n i_start hi_lt (k+1) h_in_k1_ge
                h_in_k1_full hk1_rest] at hrow_eq
          -- Now reformulate the +1 index in h_c_k1 and hrow_eq
          have hk1_rest' : (k - (row_pairs lst x i_start hi_lt).length) + 1
                          < (matrix_emit_list lst x n (i_start + 1)).length := by
            rw [← h_idx_eq]; exact hk1_rest
          have h_c_k1' : ((matrix_emit_list lst x n (i_start + 1))[(k - (row_pairs lst x i_start hi_lt).length) + 1]'hk1_rest')._1 = Int64.ofNat c_k1 := by
            rw [show (matrix_emit_list lst x n (i_start + 1))[(k - (row_pairs lst x i_start hi_lt).length) + 1]'hk1_rest'
                  = (matrix_emit_list lst x n (i_start + 1))[k + 1 - (row_pairs lst x i_start hi_lt).length]'hk1_rest
                from getElem_congr_idx h_idx_eq.symm]
            exact h_c_k1
          have hrow_eq' : ((matrix_emit_list lst x n (i_start + 1))[k - (row_pairs lst x i_start hi_lt).length]'hk_rest)._0
                        = ((matrix_emit_list lst x n (i_start + 1))[(k - (row_pairs lst x i_start hi_lt).length) + 1]'hk1_rest')._0 := by
            rw [show (matrix_emit_list lst x n (i_start + 1))[(k - (row_pairs lst x i_start hi_lt).length) + 1]'hk1_rest'
                  = (matrix_emit_list lst x n (i_start + 1))[k + 1 - (row_pairs lst x i_start hi_lt).length]'hk1_rest
                from getElem_congr_idx h_idx_eq.symm]
            exact hrow_eq
          exact ih (i_start + 1) (k - (row_pairs lst x i_start hi_lt).length)
                hk1_rest' hrow_eq' c_k c_k1 h_c_k h_c_k1' hc_k_63 hc_k1_63
    · exfalso
      rw [matrix_emit_list_step_oob lst x n i_start (by omega)] at hk
      simp at hk

/-! ## Specification of `get_coords_sorted`.

The Rust function walks a jagged matrix `lst : &[&[i64]]` and returns the
list of `(row, col)` coordinates of every cell whose value equals `x`,
sorted by row ascending and (within a row) by column descending.

Because the emitted indices are `i64` values obtained from `usize` casts,
the natural Lean theorems are only true when both the row count and every
row length fit in the positive `i64` range — otherwise the cast wraps and
breaks both the equality with the original index and the comparison order.
Each theorem therefore takes:

* `hres   : ... = RustM.ok v`                 — successful execution,
* `hrows  : lst.val.size ≤ 2^63`              — row index cast preserves value,
* `hcols  : ∀ i hi, (lst.val[i]'hi).val.size ≤ 2^63` — column cast preserves value.

These are the minimal conditions under which the universal statement holds.
-/

/-- **Soundness** (proptest `returned_coords_point_to_x`).

Every output coordinate `(r, c)` in `v` corresponds to a valid cell of `lst`
whose value is `x`. Bundling the bounds and the value-equality is forced by
the dependency between them: you need the row index in range to look up the
row, and the column index in range to look up the value. -/
theorem returned_coords_point_to_x
    (lst : RustSlice (RustSlice i64)) (x : i64)
    (v : alloc.vec.Vec (rust_primitives.hax.Tuple2 i64 i64) alloc.alloc.Global)
    (hres : clever_086_get_coords_sorted.get_coords_sorted lst x = RustM.ok v)
    (hrows : lst.val.size ≤ 2^63)
    (hcols : ∀ (i : Nat) (hi : i < lst.val.size), (lst.val[i]'hi).val.size ≤ 2^63)
    (k : Nat) (hk : k < v.val.size) :
    ∃ (i : Nat) (j : Nat) (hi : i < lst.val.size)
      (hj : j < (lst.val[i]'hi).val.size),
      (v.val[k]'hk)._0.toInt = (i : Int) ∧
      (v.val[k]'hk)._1.toInt = (j : Int) ∧
      ((lst.val[i]'hi).val[j]'hj) = x := by
  have h_v_eq := get_coords_sorted_correct lst x v hres
  have h_size : v.val.size = (matrix_emit_list lst.val x lst.val.size 0).length := by
    rw [h_v_eq]; simp
  have hk_list : k < (matrix_emit_list lst.val x lst.val.size 0).length := by
    rw [← h_size]; exact hk
  have h_get_eq : v.val[k]'hk
                = (matrix_emit_list lst.val x lst.val.size 0)[k]'hk_list := by
    rw [getElem_congr_coll h_v_eq]
    exact List.getElem_toArray _
  obtain ⟨i, j, hi, hj, _, h_fst, h_snd, h_val⟩ :=
    matrix_emit_list_sound lst.val x lst.val.size 0 k hk_list
  refine ⟨i, j, hi, hj, ?_, ?_, h_val⟩
  · rw [h_get_eq, h_fst]
    have hi_lt_63 : i < 2^63 := by omega
    exact Int64.toInt_ofNat_of_lt hi_lt_63
  · rw [h_get_eq, h_snd]
    have hj_lt_63 : j < 2^63 := by
      have := hcols i hi; omega
    exact Int64.toInt_ofNat_of_lt hj_lt_63

/-- **Completeness** (proptest `every_occurrence_is_reported`).

Every cell of `lst` containing `x` is reported in `v` as a coordinate
whose `i64` projections match the (cast of the) cell's natural-number
indices. Combined with soundness this pins down the output multiset. -/
theorem every_occurrence_is_reported
    (lst : RustSlice (RustSlice i64)) (x : i64)
    (v : alloc.vec.Vec (rust_primitives.hax.Tuple2 i64 i64) alloc.alloc.Global)
    (hres : clever_086_get_coords_sorted.get_coords_sorted lst x = RustM.ok v)
    (hrows : lst.val.size ≤ 2^63)
    (hcols : ∀ (i : Nat) (hi : i < lst.val.size), (lst.val[i]'hi).val.size ≤ 2^63)
    (i j : Nat) (hi : i < lst.val.size) (hj : j < (lst.val[i]'hi).val.size)
    (hval : ((lst.val[i]'hi).val[j]'hj) = x) :
    ∃ (k : Nat) (hk : k < v.val.size),
      (v.val[k]'hk)._0.toInt = (i : Int) ∧
      (v.val[k]'hk)._1.toInt = (j : Int) := by
  have h_v_eq := get_coords_sorted_correct lst x v hres
  have h_size : v.val.size = (matrix_emit_list lst.val x lst.val.size 0).length := by
    rw [h_v_eq]; simp
  have h_meas : lst.val.size - 0 ≤ lst.val.size := by omega
  have h_lo : 0 ≤ lst.val.size := by omega
  obtain ⟨k, hk_list, h_fst, h_snd⟩ :=
    matrix_emit_list_complete lst.val x lst.val.size 0 h_meas h_lo i j hi hj hval (by omega)
  have hk : k < v.val.size := by rw [h_size]; exact hk_list
  have h_get_eq : v.val[k]'hk
                = (matrix_emit_list lst.val x lst.val.size 0)[k]'hk_list := by
    rw [getElem_congr_coll h_v_eq]
    exact List.getElem_toArray _
  refine ⟨k, hk, ?_, ?_⟩
  · rw [h_get_eq, h_fst]
    have hi_lt_63 : i < 2^63 := by omega
    exact Int64.toInt_ofNat_of_lt hi_lt_63
  · rw [h_get_eq, h_snd]
    have hj_lt_63 : j < 2^63 := by
      have := hcols i hi; omega
    exact Int64.toInt_ofNat_of_lt hj_lt_63

/-- **Row order** (proptest `rows_are_non_decreasing`).

Consecutive entries in the output have non-decreasing row indices.
Stated directly on the emitted `i64` values; under `hrows` the i64 order
agrees with the underlying `Nat` order. -/
theorem rows_are_non_decreasing
    (lst : RustSlice (RustSlice i64)) (x : i64)
    (v : alloc.vec.Vec (rust_primitives.hax.Tuple2 i64 i64) alloc.alloc.Global)
    (hres : clever_086_get_coords_sorted.get_coords_sorted lst x = RustM.ok v)
    (hrows : lst.val.size ≤ 2^63)
    (k : Nat) (hk : k + 1 < v.val.size) :
    (v.val[k]'(Nat.lt_of_succ_lt hk))._0.toInt ≤ (v.val[k + 1]'hk)._0.toInt := by
  have h_v_eq := get_coords_sorted_correct lst x v hres
  have h_size : v.val.size = (matrix_emit_list lst.val x lst.val.size 0).length := by
    rw [h_v_eq]; simp
  have hk_list : k + 1 < (matrix_emit_list lst.val x lst.val.size 0).length := by
    rw [← h_size]; exact hk
  have h_get_k : v.val[k]'(Nat.lt_of_succ_lt hk)
               = (matrix_emit_list lst.val x lst.val.size 0)[k]'(Nat.lt_of_succ_lt hk_list) := by
    rw [getElem_congr_coll h_v_eq]
    exact List.getElem_toArray _
  have h_get_k1 : v.val[k + 1]'hk
                = (matrix_emit_list lst.val x lst.val.size 0)[k + 1]'hk_list := by
    rw [getElem_congr_coll h_v_eq]
    exact List.getElem_toArray _
  obtain ⟨i_k, _, hi_k, _, _, h_fst_k, _, _⟩ :=
    matrix_emit_list_sound lst.val x lst.val.size 0 k (Nat.lt_of_succ_lt hk_list)
  obtain ⟨i_k1, _, hi_k1, _, _, h_fst_k1, _, _⟩ :=
    matrix_emit_list_sound lst.val x lst.val.size 0 (k + 1) hk_list
  have h_le_nat : i_k ≤ i_k1 :=
    matrix_emit_list_rows_le_succ lst.val x hrows lst.val.size 0 k hk_list
      i_k i_k1 h_fst_k h_fst_k1 hi_k hi_k1
  rw [h_get_k, h_fst_k]
  rw [h_get_k1, h_fst_k1]
  have hi_k_63 : i_k < 2^63 := by omega
  have hi_k1_63 : i_k1 < 2^63 := by omega
  rw [Int64.toInt_ofNat_of_lt hi_k_63, Int64.toInt_ofNat_of_lt hi_k1_63]
  exact_mod_cast h_le_nat

/-- **Within-row column order** (proptest `cols_non_increasing_within_row`).

For consecutive entries sharing a row, the column index does not
increase. Non-strict (`≥`) rather than strict (`>`) because the
implementation may emit the same coordinate twice for a single-element
row whose only element matches `x` (the `j = 0` branch falls through to
the explicit `if !is_empty then if row[0] == x then push (r,0)` after the
recursive call with `col = 0` has already pushed `(r,0)`). -/
theorem cols_non_increasing_within_row
    (lst : RustSlice (RustSlice i64)) (x : i64)
    (v : alloc.vec.Vec (rust_primitives.hax.Tuple2 i64 i64) alloc.alloc.Global)
    (hres : clever_086_get_coords_sorted.get_coords_sorted lst x = RustM.ok v)
    (hrows : lst.val.size ≤ 2^63)
    (hcols : ∀ (i : Nat) (hi : i < lst.val.size), (lst.val[i]'hi).val.size ≤ 2^63)
    (k : Nat) (hk : k + 1 < v.val.size)
    (hrow_eq :
      (v.val[k]'(Nat.lt_of_succ_lt hk))._0 = (v.val[k + 1]'hk)._0) :
    (v.val[k + 1]'hk)._1.toInt ≤
      (v.val[k]'(Nat.lt_of_succ_lt hk))._1.toInt := by
  have h_v_eq := get_coords_sorted_correct lst x v hres
  have h_size : v.val.size = (matrix_emit_list lst.val x lst.val.size 0).length := by
    rw [h_v_eq]; simp
  have hk_list : k + 1 < (matrix_emit_list lst.val x lst.val.size 0).length := by
    rw [← h_size]; exact hk
  have h_get_k : v.val[k]'(Nat.lt_of_succ_lt hk)
                = (matrix_emit_list lst.val x lst.val.size 0)[k]'(Nat.lt_of_succ_lt hk_list) := by
    rw [getElem_congr_coll h_v_eq]
    exact List.getElem_toArray _
  have h_get_k1 : v.val[k + 1]'hk
                = (matrix_emit_list lst.val x lst.val.size 0)[k + 1]'hk_list := by
    rw [getElem_congr_coll h_v_eq]
    exact List.getElem_toArray _
  -- Extract the cols
  obtain ⟨i_k, c_k, hi_k, hc_k, _, _, h_snd_k, h_val_k⟩ :=
    matrix_emit_list_sound lst.val x lst.val.size 0 k (Nat.lt_of_succ_lt hk_list)
  obtain ⟨i_k1, c_k1, hi_k1, hc_k1, _, _, h_snd_k1, h_val_k1⟩ :=
    matrix_emit_list_sound lst.val x lst.val.size 0 (k + 1) hk_list
  have hc_k_63 : c_k < 2^63 := by have := hcols i_k hi_k; omega
  have hc_k1_63 : c_k1 < 2^63 := by have := hcols i_k1 hi_k1; omega
  -- Apply matrix_emit_list_cols_within_row
  have hrow_eq_list : ((matrix_emit_list lst.val x lst.val.size 0)[k]'(Nat.lt_of_succ_lt hk_list))._0
                    = ((matrix_emit_list lst.val x lst.val.size 0)[k + 1]'hk_list)._0 := by
    rw [← h_get_k, ← h_get_k1]; exact hrow_eq
  have h_le_nat : c_k1 ≤ c_k :=
    matrix_emit_list_cols_within_row lst.val x hrows hcols
      lst.val.size 0 k hk_list hrow_eq_list c_k c_k1 h_snd_k h_snd_k1 hc_k_63 hc_k1_63
  rw [h_get_k, h_snd_k]
  rw [h_get_k1, h_snd_k1]
  rw [Int64.toInt_ofNat_of_lt hc_k_63, Int64.toInt_ofNat_of_lt hc_k1_63]
  exact_mod_cast h_le_nat

end Clever_086_get_coords_sortedObligations
