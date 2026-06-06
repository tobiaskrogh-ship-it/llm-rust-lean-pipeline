-- Companion obligations file for the `clever_069_strange_sort_list` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_069_strange_sort_list

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_069_strange_sort_listObligations

/-! ## Specification oracle for the multiset clause. -/

private def vec_count (s : Array i64) (target : i64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      if h : k < s.size then
        (if (s[k]'h) = target then 1 else 0) + vec_count s target k
      else
        vec_count s target k

/-! ## Standard scaffolding. -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

private theorem usize_zero_toNat : (0 : usize).toNat = 0 := rfl

private theorem usize_two_toNat : (2 : usize).toNat = 2 := rfl

private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide

private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide

private theorem two_lt_usize_size : (2 : Nat) < USize64.size := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

private theorem usize_add_one_ok (i : usize) (h : i.toNat + 1 < 2^64) :
    (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
  show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
  show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure (i + 1)) = _
  have h_no_bv :
      BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hii := (USize64.uaddOverflow_iff i 1).mp hbo
      rw [usize_one_toNat] at hii
      omega
  rw [h_no_bv]; rfl

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

private theorem usize_sub_ok (a b : usize) (h : b.toNat ≤ a.toNat) :
    (a -? b : RustM usize) = RustM.ok (a - b) := by
  show (rust_primitives.ops.arith.Sub.sub a b : RustM usize) = RustM.ok (a - b)
  show (if BitVec.usubOverflow a.toBitVec b.toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure (a - b)) = _
  have h_no_bv :
      BitVec.usubOverflow a.toBitVec b.toBitVec = false := by
    generalize hbo : BitVec.usubOverflow a.toBitVec b.toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have h_sub_ov : USize64.subOverflow a b = true := hbo
      have hii : a.toNat < b.toNat := USize64.subOverflow_iff.mp h_sub_ov
      omega
  rw [h_no_bv]; rfl

private theorem usize_sub_toNat (a b : usize) (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  rw [USize64.toNat_sub_of_le' h]

/-- Push a single element. -/
private def push_one (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec i64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

/-- Push two elements. -/
private def push_two (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x y : i64)
    (h : acc.val.size + 2 < USize64.size) :
    alloc.vec.Vec i64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x, y], by
    have h_size : (acc.val ++ #[x, y]).size = acc.val.size + 2 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

/-! ## `vec_count` append lemmas. -/

private theorem vec_count_succ (s : Array i64) (target : i64) (k : Nat) (hk : k < s.size) :
    vec_count s target (k + 1) =
      (if (s[k]'hk) = target then 1 else 0) + vec_count s target k := by
  show (if h : k < s.size then
          (if (s[k]'h) = target then 1 else 0) + vec_count s target k
        else vec_count s target k) = _
  rw [dif_pos hk]

private theorem vec_count_prefix (acc : Array i64) (y target : i64) :
    ∀ k, k ≤ acc.size →
      vec_count (acc ++ #[y]) target k = vec_count acc target k := by
  have h_size_app : (acc ++ #[y]).size = acc.size + 1 := by rw [Array.size_append]; rfl
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk_lt : k < acc.size := by omega
    have hk_lt_app : k < (acc ++ #[y]).size := by rw [h_size_app]; omega
    have h_app : (acc ++ #[y])[k]'hk_lt_app = acc[k]'hk_lt :=
      Array.getElem_append_left hk_lt
    show (if h : k < (acc ++ #[y]).size then
            (if ((acc ++ #[y])[k]'h) = target then 1 else 0)
              + vec_count (acc ++ #[y]) target k
          else vec_count (acc ++ #[y]) target k) = _
    rw [dif_pos hk_lt_app, h_app, ih (Nat.le_of_lt hk)]
    show _ = (if h : k < acc.size then
                (if (acc[k]'h) = target then 1 else 0) + vec_count acc target k
              else vec_count acc target k)
    rw [dif_pos hk_lt]

private theorem vec_count_append_singleton (acc : Array i64) (y target : i64) :
    vec_count (acc ++ #[y]) target (acc.size + 1) =
      vec_count acc target acc.size + (if y = target then 1 else 0) := by
  have h_size_app : (acc ++ #[y]).size = acc.size + 1 := by rw [Array.size_append]; rfl
  have h_lt : acc.size < (acc ++ #[y]).size := by rw [h_size_app]; omega
  have h_get : (acc ++ #[y])[acc.size]'h_lt = y := by
    rw [Array.getElem_append_right (Nat.le_refl _)]
    simp
  have h_step := vec_count_succ (acc ++ #[y]) target acc.size h_lt
  rw [h_step, h_get, vec_count_prefix acc y target acc.size (Nat.le_refl _)]
  omega

private theorem vec_count_append_pair (acc : Array i64) (x y target : i64) :
    vec_count (acc ++ #[x, y]) target (acc.size + 2) =
      vec_count acc target acc.size + (if x = target then 1 else 0) + (if y = target then 1 else 0) := by
  have h_size_app : (acc ++ #[x, y]).size = acc.size + 2 := by rw [Array.size_append]; rfl
  have h_lt_succ : acc.size + 1 < (acc ++ #[x, y]).size := by rw [h_size_app]; omega
  have h_lt : acc.size < (acc ++ #[x, y]).size := by rw [h_size_app]; omega
  have h_get_x : (acc ++ #[x, y])[acc.size]'h_lt = x := by
    rw [Array.getElem_append_right (Nat.le_refl _)]
    simp
  have h_get_y : (acc ++ #[x, y])[acc.size + 1]'h_lt_succ = y := by
    rw [Array.getElem_append_right (Nat.le_add_right _ 1)]
    have h_sub : acc.size + 1 - acc.size = 1 := by omega
    simp [h_sub]
  have h_step2 := vec_count_succ (acc ++ #[x, y]) target (acc.size + 1) h_lt_succ
  rw [h_step2, h_get_y]
  have h_step1 := vec_count_succ (acc ++ #[x, y]) target acc.size h_lt
  rw [h_step1, h_get_x]
  have h_prefix : vec_count (acc ++ #[x, y]) target acc.size = vec_count acc target acc.size := by
    suffices h : ∀ k, k ≤ acc.size → vec_count (acc ++ #[x, y]) target k = vec_count acc target k by
      exact h acc.size (Nat.le_refl _)
    intro k hk_le
    induction k with
    | zero => rfl
    | succ k ih =>
      have hk_lt : k < acc.size := by omega
      have hk_lt_app : k < (acc ++ #[x, y]).size := by rw [h_size_app]; omega
      have h_app : (acc ++ #[x, y])[k]'hk_lt_app = acc[k]'hk_lt :=
        Array.getElem_append_left hk_lt
      show (if h : k < (acc ++ #[x, y]).size then
              (if ((acc ++ #[x, y])[k]'h) = target then 1 else 0)
                + vec_count (acc ++ #[x, y]) target k
            else vec_count (acc ++ #[x, y]) target k) = _
      rw [dif_pos hk_lt_app, h_app, ih (Nat.le_of_lt hk_le)]
      show _ = (if h : k < acc.size then
                  (if (acc[k]'h) = target then 1 else 0) + vec_count acc target k
                else vec_count acc target k)
      rw [dif_pos hk_lt]
  rw [h_prefix]
  omega

/-! ## OOB / step / fail lemmas for `insert_sorted_at` (arg order matches target). -/

private theorem insert_sorted_at_oob_inserted (v : RustSlice i64) (x : i64)
    (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat) :
    clever_069_strange_sort_list.insert_sorted_at v x i true acc = RustM.ok acc := by
  unfold clever_069_strange_sort_list.insert_sorted_at
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat v.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]; rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, ↓reduceIte,
             rust_primitives.hax.logical_op.not, Bool.not_true,
             Bool.false_eq_true]
  rfl

private theorem insert_sorted_at_oob_not_inserted (v : RustSlice i64) (x : i64)
    (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_069_strange_sort_list.insert_sorted_at v x i false acc =
      RustM.ok (push_one acc x h_acc) := by
  unfold clever_069_strange_sort_list.insert_sorted_at
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat v.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]; rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  have h_app_size :
      acc.val.size + (#[x] : Array i64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  have h_extend :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[x], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.ok (push_one acc x h_acc) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, ↓reduceIte,
             rust_primitives.hax.logical_op.not, Bool.not_false,
             ↓reduceIte]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[x] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[x], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend]
  rfl

private theorem insert_sorted_at_oob_not_inserted_fail (v : RustSlice i64) (x : i64)
    (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_069_strange_sort_list.insert_sorted_at v x i false acc
      = RustM.fail .maximumSizeExceeded := by
  unfold clever_069_strange_sort_list.insert_sorted_at
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat v.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]; rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  have h_app_size_neg :
      ¬ acc.val.size + (#[x] : Array i64).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[x], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, ↓reduceIte,
             rust_primitives.hax.logical_op.not, Bool.not_false,
             ↓reduceIte]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[x] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[x], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

private theorem insert_sorted_at_step_insert (v : RustSlice i64) (x : i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_vi : (v.val[i.toNat]'hi).toInt ≥ x.toInt)
    (h_acc : acc.val.size + 2 < USize64.size) :
    clever_069_strange_sort_list.insert_sorted_at v x i false acc =
      clever_069_strange_sort_list.insert_sorted_at v x (i + 1) true
        (push_two acc x (v.val[i.toNat]'hi) h_acc) := by
  conv => lhs; unfold clever_069_strange_sort_list.insert_sorted_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM i64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_ge_true : (decide ((v.val[i.toNat]'hi) ≥ x)) = true := by
    rw [decide_eq_true_iff]
    rw [show ((v.val[i.toNat]'hi) ≥ x) = (x ≤ (v.val[i.toNat]'hi)) from rfl]
    rw [Int64.le_iff_toInt_le]
    exact h_vi
  have h_add : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := usize_add_one_ok i h_no_ov_i
  have h_app_size :
      acc.val.size + (#[x, v.val[i.toNat]'hi] : Array i64).size < USize64.size := by
    show acc.val.size + 2 < USize64.size; exact h_acc
  have h_extend :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[x, v.val[i.toNat]'hi], two_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.ok (push_two acc x (v.val[i.toNat]'hi) h_acc) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.hax.logical_op.not, Bool.not_false,
             rust_primitives.hax.logical_op.and, h_ge_true,
             Bool.true_and, ↓reduceIte]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[x, v.val[i.toNat]'hi] : RustArray i64 2)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[x, v.val[i.toNat]'hi], two_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend]
  simp only [RustM_ok_bind]
  rw [h_add]
  simp only [RustM_ok_bind]

private theorem insert_sorted_at_step_insert_fail (v : RustSlice i64) (x : i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_vi : (v.val[i.toNat]'hi).toInt ≥ x.toInt)
    (h_big : USize64.size ≤ acc.val.size + 2) :
    clever_069_strange_sort_list.insert_sorted_at v x i false acc = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_069_strange_sort_list.insert_sorted_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM i64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_ge_true : (decide ((v.val[i.toNat]'hi) ≥ x)) = true := by
    rw [decide_eq_true_iff]
    rw [show ((v.val[i.toNat]'hi) ≥ x) = (x ≤ (v.val[i.toNat]'hi)) from rfl]
    rw [Int64.le_iff_toInt_le]
    exact h_vi
  have h_app_size_neg :
      ¬ acc.val.size + (#[x, v.val[i.toNat]'hi] : Array i64).size < USize64.size := by
    show ¬ acc.val.size + 2 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[x, v.val[i.toNat]'hi], two_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.hax.logical_op.not, Bool.not_false,
             rust_primitives.hax.logical_op.and, h_ge_true,
             Bool.true_and, ↓reduceIte]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[x, v.val[i.toNat]'hi] : RustArray i64 2)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[x, v.val[i.toNat]'hi], two_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

private theorem insert_sorted_at_step_pass (v : RustSlice i64) (x : i64) (i : usize)
    (inserted : Bool) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_skip : inserted = true ∨ (v.val[i.toNat]'hi).toInt < x.toInt)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_069_strange_sort_list.insert_sorted_at v x i inserted acc =
      clever_069_strange_sort_list.insert_sorted_at v x (i + 1) inserted
        (push_one acc (v.val[i.toNat]'hi) h_acc) := by
  conv => lhs; unfold clever_069_strange_sort_list.insert_sorted_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM i64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_and_false : ((!inserted) && decide ((v.val[i.toNat]'hi) ≥ x)) = false := by
    cases h_skip with
    | inl h_ins_true => subst h_ins_true; rfl
    | inr h_lt =>
      have h_not_ge : ¬ ((v.val[i.toNat]'hi) ≥ x) := by
        rw [show ((v.val[i.toNat]'hi) ≥ x) = (x ≤ (v.val[i.toNat]'hi)) from rfl]
        rw [Int64.le_iff_toInt_le]
        omega
      rw [decide_eq_false h_not_ge]
      exact Bool.and_false _
  have h_add : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := usize_add_one_ok i h_no_ov_i
  have h_app_size :
      acc.val.size + (#[v.val[i.toNat]'hi] : Array i64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  have h_extend :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[v.val[i.toNat]'hi], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.ok (push_one acc (v.val[i.toNat]'hi) h_acc) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.hax.logical_op.not,
             rust_primitives.hax.logical_op.and]
  rw [h_and_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[v.val[i.toNat]'hi] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[v.val[i.toNat]'hi], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend]
  simp only [RustM_ok_bind]
  rw [h_add]
  simp only [RustM_ok_bind]

private theorem insert_sorted_at_step_pass_fail (v : RustSlice i64) (x : i64) (i : usize)
    (inserted : Bool) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_skip : inserted = true ∨ (v.val[i.toNat]'hi).toInt < x.toInt)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_069_strange_sort_list.insert_sorted_at v x i inserted acc = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_069_strange_sort_list.insert_sorted_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM i64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_and_false : ((!inserted) && decide ((v.val[i.toNat]'hi) ≥ x)) = false := by
    cases h_skip with
    | inl h_ins_true => subst h_ins_true; rfl
    | inr h_lt =>
      have h_not_ge : ¬ ((v.val[i.toNat]'hi) ≥ x) := by
        rw [show ((v.val[i.toNat]'hi) ≥ x) = (x ≤ (v.val[i.toNat]'hi)) from rfl]
        rw [Int64.le_iff_toInt_le]
        omega
      rw [decide_eq_false h_not_ge]
      exact Bool.and_false _
  have h_app_size_neg :
      ¬ acc.val.size + (#[v.val[i.toNat]'hi] : Array i64).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[v.val[i.toNat]'hi], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.hax.logical_op.not,
             rust_primitives.hax.logical_op.and]
  rw [h_and_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[v.val[i.toNat]'hi] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[v.val[i.toNat]'hi], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

/-! ## Invariant for `insert_sorted_at`: size and vec_count. -/

private theorem insert_sorted_at_inv :
    ∀ (n : Nat) (v : RustSlice i64) (x : i64) (i : usize) (inserted : Bool)
      (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global) (target : i64),
      v.val.size - i.toNat ≤ n →
      i.toNat ≤ v.val.size →
      clever_069_strange_sort_list.insert_sorted_at v x i inserted acc = RustM.ok r →
      r.val.size = acc.val.size + (v.val.size - i.toNat) + (if inserted then 0 else 1) ∧
      vec_count r.val target r.val.size + vec_count v.val target i.toNat =
        vec_count acc.val target acc.val.size + vec_count v.val target v.val.size
          + (if inserted then 0 else (if x = target then 1 else 0)) := by
  intro n
  induction n with
  | zero =>
    intro v x i inserted acc r target hm hi_le hres
    have hi_ge : v.val.size ≤ i.toNat := by omega
    have hi_eq : i.toNat = v.val.size := by omega
    cases inserted with
    | true =>
      rw [insert_sorted_at_oob_inserted v x i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      refine ⟨?_, ?_⟩
      · simp [hi_eq]
      · rw [hi_eq]; simp
    | false =>
      by_cases h_acc : acc.val.size + 1 < USize64.size
      · rw [insert_sorted_at_oob_not_inserted v x i acc hi_ge h_acc] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        refine ⟨?_, ?_⟩
        · show (acc.val ++ #[x]).size = acc.val.size + (v.val.size - i.toNat) + 1
          rw [Array.size_append]; simp; omega
        · show vec_count (acc.val ++ #[x]) target (acc.val ++ #[x]).size + vec_count v.val target i.toNat
              = vec_count acc.val target acc.val.size + vec_count v.val target v.val.size
                + (if x = target then 1 else 0)
          have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by rw [Array.size_append]; rfl
          rw [h_size, vec_count_append_singleton, hi_eq]
          omega
      · exfalso
        have h_big : USize64.size ≤ acc.val.size + 1 := by omega
        rw [insert_sorted_at_oob_not_inserted_fail v x i acc hi_ge h_big] at hres
        cases hres
  | succ n ih =>
    intro v x i inserted acc r target hm hi_le hres
    by_cases hi_ge : v.val.size ≤ i.toNat
    · have hi_eq : i.toNat = v.val.size := by omega
      cases inserted with
      | true =>
        rw [insert_sorted_at_oob_inserted v x i acc hi_ge] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        refine ⟨?_, ?_⟩
        · simp [hi_eq]
        · rw [hi_eq]; simp
      | false =>
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [insert_sorted_at_oob_not_inserted v x i acc hi_ge h_acc] at hres
          injection hres with h_eq
          injection h_eq with h_eq'
          subst h_eq'
          refine ⟨?_, ?_⟩
          · show (acc.val ++ #[x]).size = acc.val.size + (v.val.size - i.toNat) + 1
            rw [Array.size_append]; simp; omega
          · show vec_count (acc.val ++ #[x]) target (acc.val ++ #[x]).size + vec_count v.val target i.toNat
                = vec_count acc.val target acc.val.size + vec_count v.val target v.val.size
                  + (if x = target then 1 else 0)
            have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by rw [Array.size_append]; rfl
            rw [h_size, vec_count_append_singleton, hi_eq]
            omega
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_sorted_at_oob_not_inserted_fail v x i acc hi_ge h_big] at hres
          cases hres
    · have hi_lt : i.toNat < v.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ v.val.size := by rw [h_i1]; omega
      have h_meas : v.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      have h_vec_succ_v :
          vec_count v.val target (i.toNat + 1) =
            (if v.val[i.toNat]'hi_lt = target then 1 else 0) + vec_count v.val target i.toNat :=
        vec_count_succ v.val target i.toNat hi_lt
      cases inserted with
      | true =>
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [insert_sorted_at_step_pass v x i true acc hi_lt (Or.inl rfl) h_acc] at hres
          have h_push_size :
              (push_one acc (v.val[i.toNat]'hi_lt) h_acc).val.size = acc.val.size + 1 := by
            show (acc.val ++ #[v.val[i.toNat]'hi_lt]).size = acc.val.size + 1
            rw [Array.size_append]; rfl
          have h_count_pushed :
              vec_count (push_one acc (v.val[i.toNat]'hi_lt) h_acc).val target
                (acc.val.size + 1) =
              vec_count acc.val target acc.val.size +
                (if v.val[i.toNat]'hi_lt = target then 1 else 0) := by
            show vec_count (acc.val ++ #[v.val[i.toNat]'hi_lt]) target (acc.val.size + 1) = _
            exact vec_count_append_singleton acc.val (v.val[i.toNat]'hi_lt) target
          have ih_app := ih v x (i + 1) true (push_one acc (v.val[i.toNat]'hi_lt) h_acc) r target
            h_meas h_i1_le hres
          rw [h_i1] at ih_app
          obtain ⟨h_size_eq, h_count_eq⟩ := ih_app
          rw [h_push_size] at h_size_eq h_count_eq
          simp only [if_true, if_pos rfl] at h_size_eq h_count_eq
          refine ⟨?_, ?_⟩
          · simp only [if_true, if_pos rfl]; rw [h_size_eq]
            have : 0 < v.val.size - i.toNat := by omega
            omega
          · simp only [if_true, if_pos rfl]
            rw [h_count_pushed] at h_count_eq
            rw [h_vec_succ_v] at h_count_eq
            omega
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_sorted_at_step_pass_fail v x i true acc hi_lt (Or.inl rfl) h_big] at hres
          cases hres
      | false =>
        by_cases h_vi : (v.val[i.toNat]'hi_lt).toInt ≥ x.toInt
        · by_cases h_acc : acc.val.size + 2 < USize64.size
          · rw [insert_sorted_at_step_insert v x i acc hi_lt h_vi h_acc] at hres
            have h_push_size :
                (push_two acc x (v.val[i.toNat]'hi_lt) h_acc).val.size = acc.val.size + 2 := by
              show (acc.val ++ #[x, v.val[i.toNat]'hi_lt]).size = acc.val.size + 2
              rw [Array.size_append]; rfl
            have h_count_pushed :
                vec_count (push_two acc x (v.val[i.toNat]'hi_lt) h_acc).val target
                  (acc.val.size + 2) =
                vec_count acc.val target acc.val.size + (if x = target then 1 else 0) +
                  (if v.val[i.toNat]'hi_lt = target then 1 else 0) := by
              show vec_count (acc.val ++ #[x, v.val[i.toNat]'hi_lt]) target (acc.val.size + 2) = _
              exact vec_count_append_pair acc.val x (v.val[i.toNat]'hi_lt) target
            have ih_app := ih v x (i + 1) true (push_two acc x (v.val[i.toNat]'hi_lt) h_acc) r target
              h_meas h_i1_le hres
            rw [h_i1] at ih_app
            obtain ⟨h_size_eq, h_count_eq⟩ := ih_app
            rw [h_push_size] at h_size_eq h_count_eq
            rw [if_pos (rfl : true = true)] at h_size_eq h_count_eq
            rw [if_neg (Bool.false_ne_true), if_neg (Bool.false_ne_true)]
            rw [h_count_pushed] at h_count_eq
            rw [h_vec_succ_v] at h_count_eq
            refine ⟨?_, ?_⟩
            · rw [h_size_eq]
              have : 0 < v.val.size - i.toNat := by omega
              omega
            · omega
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 2 := by omega
            rw [insert_sorted_at_step_insert_fail v x i acc hi_lt h_vi h_big] at hres
            cases hres
        · have h_lt : (v.val[i.toNat]'hi_lt).toInt < x.toInt := by omega
          by_cases h_acc : acc.val.size + 1 < USize64.size
          · rw [insert_sorted_at_step_pass v x i false acc hi_lt (Or.inr h_lt) h_acc] at hres
            have h_push_size :
                (push_one acc (v.val[i.toNat]'hi_lt) h_acc).val.size = acc.val.size + 1 := by
              show (acc.val ++ #[v.val[i.toNat]'hi_lt]).size = acc.val.size + 1
              rw [Array.size_append]; rfl
            have h_count_pushed :
                vec_count (push_one acc (v.val[i.toNat]'hi_lt) h_acc).val target
                  (acc.val.size + 1) =
                vec_count acc.val target acc.val.size +
                  (if v.val[i.toNat]'hi_lt = target then 1 else 0) := by
              show vec_count (acc.val ++ #[v.val[i.toNat]'hi_lt]) target (acc.val.size + 1) = _
              exact vec_count_append_singleton acc.val (v.val[i.toNat]'hi_lt) target
            have ih_app := ih v x (i + 1) false (push_one acc (v.val[i.toNat]'hi_lt) h_acc) r target
              h_meas h_i1_le hres
            rw [h_i1] at ih_app
            obtain ⟨h_size_eq, h_count_eq⟩ := ih_app
            rw [h_push_size] at h_size_eq h_count_eq
            rw [if_neg (Bool.false_ne_true)] at h_size_eq h_count_eq
            rw [if_neg (Bool.false_ne_true), if_neg (Bool.false_ne_true)]
            rw [h_count_pushed] at h_count_eq
            rw [h_vec_succ_v] at h_count_eq
            refine ⟨?_, ?_⟩
            · rw [h_size_eq]
              have : 0 < v.val.size - i.toNat := by omega
              omega
            · omega
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 1 := by omega
            rw [insert_sorted_at_step_pass_fail v x i false acc hi_lt (Or.inr h_lt) h_big] at hres
            cases hres

/-- Specialization: insert_sorted v x has size v.size + 1, vec_count adds 1 if x = target. -/
private theorem insert_sorted_inv (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (r : alloc.vec.Vec i64 alloc.alloc.Global) (target : i64)
    (hres : clever_069_strange_sort_list.insert_sorted v x = RustM.ok r) :
    r.val.size = v.val.size + 1 ∧
    vec_count r.val target r.val.size =
      vec_count v.val target v.val.size + (if x = target then 1 else 0) := by
  unfold clever_069_strange_sort_list.insert_sorted at hres
  have h_deref :
      (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec i64 alloc.alloc.Global) v : RustM _) = RustM.ok v := rfl
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_deref, h_new] at hres
  simp only [RustM_ok_bind] at hres
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_meas : v.val.size - (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  have h_le : (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  have inv := insert_sorted_at_inv v.val.size v x (0 : usize) false
    ⟨(List.nil).toArray, by grind⟩ r target h_meas h_le hres
  obtain ⟨h_size_eq, h_count_eq⟩ := inv
  have h_empty_size : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
  rw [h_empty_size, h_zero_toNat] at h_size_eq
  rw [h_empty_size, h_zero_toNat] at h_count_eq
  have h_empty_count : vec_count ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val target 0 = 0 := rfl
  refine ⟨?_, ?_⟩
  · rw [h_size_eq]; simp
  · rw [h_empty_count] at h_count_eq
    have h_total_zero : vec_count v.val target 0 = 0 := rfl
    rw [h_total_zero] at h_count_eq
    simp at h_count_eq
    omega

/-! ## `sort_at` OOB + step lemmas. -/

private theorem sort_at_oob (l : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : l.val.size ≤ i.toNat) :
    clever_069_strange_sort_list.sort_at l i acc = RustM.ok acc := by
  unfold clever_069_strange_sort_list.sort_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

private theorem sort_at_step (l : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < l.val.size) :
    clever_069_strange_sort_list.sort_at l i acc =
      (do
        let acc' ← clever_069_strange_sort_list.insert_sorted acc (l.val[i.toNat]'hi)
        clever_069_strange_sort_list.sort_at l (i + 1) acc') := by
  conv => lhs; unfold clever_069_strange_sort_list.sort_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_add : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := usize_add_one_ok i h_no_ov_i
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx]
  rw [h_add]
  simp only [RustM_ok_bind]

/-- `sort_at` preserves size and multiset count: the output has the count of acc plus
    the count over l[i..]. Stated additively to avoid Nat subtraction issues. -/
private theorem sort_at_inv :
    ∀ (n : Nat) (l : RustSlice i64) (i : usize)
      (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global) (target : i64),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      clever_069_strange_sort_list.sort_at l i acc = RustM.ok r →
      r.val.size = acc.val.size + (l.val.size - i.toNat) ∧
      vec_count r.val target r.val.size + vec_count l.val target i.toNat =
        vec_count acc.val target acc.val.size + vec_count l.val target l.val.size := by
  intro n
  induction n with
  | zero =>
    intro l i acc r target hm hi_le hres
    have hi_ge : l.val.size ≤ i.toNat := by omega
    have hi_eq : i.toNat = l.val.size := by omega
    rw [sort_at_oob l i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    refine ⟨?_, ?_⟩
    · rw [hi_eq]; omega
    · rw [hi_eq]
  | succ n ih =>
    intro l i acc r target hm hi_le hres
    by_cases hi_ge : l.val.size ≤ i.toNat
    · have hi_eq : i.toNat = l.val.size := by omega
      rw [sort_at_oob l i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      refine ⟨?_, ?_⟩
      · rw [hi_eq]; omega
      · rw [hi_eq]
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_meas : l.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      have h_vec_succ_l :
          vec_count l.val target (i.toNat + 1) =
            (if l.val[i.toNat]'hi_lt = target then 1 else 0) + vec_count l.val target i.toNat :=
        vec_count_succ l.val target i.toNat hi_lt
      rw [sort_at_step l i acc hi_lt] at hres
      generalize h_ins : clever_069_strange_sort_list.insert_sorted acc (l.val[i.toNat]'hi_lt) = ins_res at hres
      cases ins_res with
      | none =>
        exfalso
        have hh : (do let acc' ← (none : RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                       clever_069_strange_sort_list.sort_at l (i + 1) acc')
                  = RustM.ok r := hres
        cases hh
      | some res' =>
        cases res' with
        | error e =>
          exfalso
          have hh : (do let acc' ← (some (Except.error e) :
                                      RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                         clever_069_strange_sort_list.sort_at l (i + 1) acc')
                    = RustM.ok r := hres
          cases hh
        | ok acc' =>
          have h_ins_ok : clever_069_strange_sort_list.insert_sorted acc (l.val[i.toNat]'hi_lt) = RustM.ok acc' := h_ins
          simp only [RustM_ok_bind] at hres
          have h_ins_inv := insert_sorted_inv acc (l.val[i.toNat]'hi_lt) acc' target h_ins_ok
          obtain ⟨h_acc'_size, h_acc'_count⟩ := h_ins_inv
          have ih_app := ih l (i + 1) acc' r target h_meas h_i1_le hres
          rw [h_i1] at ih_app
          obtain ⟨h_size_eq, h_count_eq⟩ := ih_app
          rw [h_acc'_size] at h_size_eq
          rw [h_acc'_count] at h_count_eq
          rw [h_vec_succ_l] at h_count_eq
          refine ⟨?_, ?_⟩
          · rw [h_size_eq]; omega
          · omega

/-! ## Sortedness predicate. -/

private def sorted_asc (arr : Array i64) : Prop :=
  ∀ (k₁ k₂ : Nat) (h₁ : k₁ < arr.size) (h₂ : k₂ < arr.size),
    k₁ ≤ k₂ → (arr[k₁]'h₁).toInt ≤ (arr[k₂]'h₂).toInt

private theorem sorted_asc_empty : sorted_asc #[] := by
  intro k₁ k₂ h₁ _ _
  have : (#[] : Array i64).size = 0 := rfl
  omega

private theorem sorted_asc_append_singleton (acc : Array i64) (y : i64)
    (h_acc : sorted_asc acc)
    (h_le : ∀ (k : Nat) (hk : k < acc.size), (acc[k]'hk).toInt ≤ y.toInt) :
    sorted_asc (acc ++ #[y]) := by
  intro k₁ k₂ h₁ h₂ hle12
  rw [Array.size_append] at h₁ h₂
  have h_one : (#[y] : Array i64).size = 1 := rfl
  by_cases h_k1_lt : k₁ < acc.size
  · by_cases h_k2_lt : k₂ < acc.size
    · rw [Array.getElem_append_left h_k1_lt, Array.getElem_append_left h_k2_lt]
      exact h_acc k₁ k₂ h_k1_lt h_k2_lt hle12
    · have h_k2_ge : acc.size ≤ k₂ := by omega
      rw [Array.getElem_append_left h_k1_lt]
      rw [Array.getElem_append_right h_k2_ge]
      have h_idx : k₂ - acc.size = 0 := by omega
      have h_zero : (0 : Nat) < (#[y] : Array i64).size := by rw [h_one]; omega
      rw [show ((#[y] : Array i64)[k₂ - acc.size]'(by rw [h_idx]; exact h_zero))
              = (#[y] : Array i64)[0]'h_zero from by simp [h_idx]]
      show (acc[k₁]'h_k1_lt).toInt ≤ y.toInt
      exact h_le k₁ h_k1_lt
  · have h_k1_ge : acc.size ≤ k₁ := by omega
    have h_k2_ge : acc.size ≤ k₂ := by omega
    rw [Array.getElem_append_right h_k1_ge, Array.getElem_append_right h_k2_ge]
    have h_k1_idx : k₁ - acc.size = 0 := by omega
    have h_k2_idx : k₂ - acc.size = 0 := by omega
    have h_zero : (0 : Nat) < (#[y] : Array i64).size := by rw [h_one]; omega
    rw [show ((#[y] : Array i64)[k₁ - acc.size]'(by rw [h_k1_idx]; exact h_zero))
            = (#[y] : Array i64)[0]'h_zero from by simp [h_k1_idx]]
    rw [show ((#[y] : Array i64)[k₂ - acc.size]'(by rw [h_k2_idx]; exact h_zero))
            = (#[y] : Array i64)[0]'h_zero from by simp [h_k2_idx]]
    exact Int.le_refl _

private theorem sorted_asc_append_pair (acc : Array i64) (a b : i64)
    (h_acc : sorted_asc acc)
    (h_le_a : ∀ (k : Nat) (hk : k < acc.size), (acc[k]'hk).toInt ≤ a.toInt)
    (h_le_ab : a.toInt ≤ b.toInt) :
    sorted_asc (acc ++ #[a, b]) := by
  intro k₁ k₂ h₁ h₂ hle12
  rw [Array.size_append] at h₁ h₂
  have h_two : (#[a, b] : Array i64).size = 2 := rfl
  by_cases h_k1_lt : k₁ < acc.size
  · by_cases h_k2_lt : k₂ < acc.size
    · rw [Array.getElem_append_left h_k1_lt, Array.getElem_append_left h_k2_lt]
      exact h_acc k₁ k₂ h_k1_lt h_k2_lt hle12
    · have h_k2_ge : acc.size ≤ k₂ := by omega
      rw [Array.getElem_append_left h_k1_lt, Array.getElem_append_right h_k2_ge]
      have h_acc_k1 := h_le_a k₁ h_k1_lt
      by_cases h_k2_sub_eq : k₂ - acc.size = 0
      · have h_zero : (0 : Nat) < (#[a, b] : Array i64).size := by rw [h_two]; omega
        rw [show ((#[a, b] : Array i64)[k₂ - acc.size]'(by rw [h_k2_sub_eq]; exact h_zero))
                = (#[a, b] : Array i64)[0]'h_zero from by simp [h_k2_sub_eq]]
        show (acc[k₁]'h_k1_lt).toInt ≤ a.toInt
        exact h_acc_k1
      · have h_k2_sub_eq1 : k₂ - acc.size = 1 := by omega
        have h_one_lt : (1 : Nat) < (#[a, b] : Array i64).size := by rw [h_two]; omega
        rw [show ((#[a, b] : Array i64)[k₂ - acc.size]'(by rw [h_k2_sub_eq1]; exact h_one_lt))
                = (#[a, b] : Array i64)[1]'h_one_lt from by simp [h_k2_sub_eq1]]
        show (acc[k₁]'h_k1_lt).toInt ≤ b.toInt
        omega
  · have h_k1_ge : acc.size ≤ k₁ := by omega
    have h_k2_ge : acc.size ≤ k₂ := by omega
    rw [Array.getElem_append_right h_k1_ge, Array.getElem_append_right h_k2_ge]
    by_cases h_k1_eq : k₁ - acc.size = 0
    · have h_zero : (0 : Nat) < (#[a, b] : Array i64).size := by rw [h_two]; omega
      rw [show ((#[a, b] : Array i64)[k₁ - acc.size]'(by rw [h_k1_eq]; exact h_zero))
              = (#[a, b] : Array i64)[0]'h_zero from by simp [h_k1_eq]]
      by_cases h_k2_eq : k₂ - acc.size = 0
      · rw [show ((#[a, b] : Array i64)[k₂ - acc.size]'(by rw [h_k2_eq]; exact h_zero))
                = (#[a, b] : Array i64)[0]'h_zero from by simp [h_k2_eq]]
        show a.toInt ≤ a.toInt
        exact Int.le_refl _
      · have h_k2_eq1 : k₂ - acc.size = 1 := by omega
        have h_one_lt : (1 : Nat) < (#[a, b] : Array i64).size := by rw [h_two]; omega
        rw [show ((#[a, b] : Array i64)[k₂ - acc.size]'(by rw [h_k2_eq1]; exact h_one_lt))
                = (#[a, b] : Array i64)[1]'h_one_lt from by simp [h_k2_eq1]]
        show a.toInt ≤ b.toInt
        exact h_le_ab
    · have h_k1_eq1 : k₁ - acc.size = 1 := by omega
      have h_k2_eq1 : k₂ - acc.size = 1 := by omega
      have h_one_lt : (1 : Nat) < (#[a, b] : Array i64).size := by rw [h_two]; omega
      rw [show ((#[a, b] : Array i64)[k₁ - acc.size]'(by rw [h_k1_eq1]; exact h_one_lt))
              = (#[a, b] : Array i64)[1]'h_one_lt from by simp [h_k1_eq1]]
      rw [show ((#[a, b] : Array i64)[k₂ - acc.size]'(by rw [h_k2_eq1]; exact h_one_lt))
              = (#[a, b] : Array i64)[1]'h_one_lt from by simp [h_k2_eq1]]
      show b.toInt ≤ b.toInt
      exact Int.le_refl _

/-! ## `insert_sorted_at` produces sorted output. -/

private theorem insert_sorted_at_sorted (v : RustSlice i64) (x : i64)
    (h_v_sorted : sorted_asc v.val) :
    ∀ (n : Nat) (i : usize) (inserted : Bool)
      (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      v.val.size - i.toNat ≤ n →
      i.toNat ≤ v.val.size →
      clever_069_strange_sort_list.insert_sorted_at v x i inserted acc = RustM.ok r →
      sorted_asc acc.val →
      (∀ (k : Nat) (hk : k < acc.val.size) (hi_lt : i.toNat < v.val.size),
          (acc.val[k]'hk).toInt ≤ (v.val[i.toNat]'hi_lt).toInt) →
      (inserted = false →
          ∀ (k : Nat) (hk : k < acc.val.size), (acc.val[k]'hk).toInt ≤ x.toInt) →
      sorted_asc r.val := by
  intro n
  induction n with
  | zero =>
    intro i inserted acc r hm hi_le hres h_acc_sorted h_acc_le_vi h_acc_le_x
    have hi_ge : v.val.size ≤ i.toNat := by omega
    cases inserted with
    | true =>
      rw [insert_sorted_at_oob_inserted v x i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      exact h_acc_sorted
    | false =>
      by_cases h_acc : acc.val.size + 1 < USize64.size
      · rw [insert_sorted_at_oob_not_inserted v x i acc hi_ge h_acc] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        show sorted_asc (acc.val ++ #[x])
        apply sorted_asc_append_singleton acc.val x h_acc_sorted
        exact h_acc_le_x rfl
      · exfalso
        have h_big : USize64.size ≤ acc.val.size + 1 := by omega
        rw [insert_sorted_at_oob_not_inserted_fail v x i acc hi_ge h_big] at hres
        cases hres
  | succ n ih =>
    intro i inserted acc r hm hi_le hres h_acc_sorted h_acc_le_vi h_acc_le_x
    by_cases hi_ge : v.val.size ≤ i.toNat
    · cases inserted with
      | true =>
        rw [insert_sorted_at_oob_inserted v x i acc hi_ge] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        exact h_acc_sorted
      | false =>
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [insert_sorted_at_oob_not_inserted v x i acc hi_ge h_acc] at hres
          injection hres with h_eq
          injection h_eq with h_eq'
          subst h_eq'
          show sorted_asc (acc.val ++ #[x])
          apply sorted_asc_append_singleton acc.val x h_acc_sorted
          exact h_acc_le_x rfl
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_sorted_at_oob_not_inserted_fail v x i acc hi_ge h_big] at hres
          cases hres
    · have hi_lt : i.toNat < v.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ v.val.size := by rw [h_i1]; omega
      have h_meas : v.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      cases inserted with
      | true =>
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [insert_sorted_at_step_pass v x i true acc hi_lt (Or.inl rfl) h_acc] at hres
          have h_new_sorted : sorted_asc (acc.val ++ #[v.val[i.toNat]'hi_lt]) := by
            apply sorted_asc_append_singleton acc.val (v.val[i.toNat]'hi_lt) h_acc_sorted
            intro k hk
            exact h_acc_le_vi k hk hi_lt
          have h_new_le_vi :
              ∀ (k : Nat) (hk : k < (acc.val ++ #[v.val[i.toNat]'hi_lt]).size)
                (hi_i1 : (i + 1).toNat < v.val.size),
                ((acc.val ++ #[v.val[i.toNat]'hi_lt])[k]'hk).toInt
                  ≤ (v.val[(i + 1).toNat]'hi_i1).toInt := by
            intro k hk hi_i1
            rw [Array.size_append] at hk
            have h_one : (#[v.val[i.toNat]'hi_lt] : Array i64).size = 1 := rfl
            by_cases h_k_lt : k < acc.val.size
            · rw [Array.getElem_append_left h_k_lt]
              have h_acc_k := h_acc_le_vi k h_k_lt hi_lt
              have h_v_step : (v.val[i.toNat]'hi_lt).toInt ≤ (v.val[(i + 1).toNat]'hi_i1).toInt := by
                have h_le : i.toNat ≤ (i + 1).toNat := by rw [h_i1]; omega
                exact h_v_sorted i.toNat (i + 1).toNat hi_lt hi_i1 h_le
              omega
            · have h_k_ge : acc.val.size ≤ k := by omega
              rw [Array.getElem_append_right h_k_ge]
              have h_idx : k - acc.val.size = 0 := by omega
              have h_zero_lt : (0 : Nat) < (#[v.val[i.toNat]'hi_lt] : Array i64).size := by
                rw [h_one]; omega
              rw [show ((#[v.val[i.toNat]'hi_lt] : Array i64)[k - acc.val.size]'(by rw [h_idx]; exact h_zero_lt))
                      = (#[v.val[i.toNat]'hi_lt] : Array i64)[0]'h_zero_lt from by simp [h_idx]]
              show (v.val[i.toNat]'hi_lt).toInt ≤ (v.val[(i + 1).toNat]'hi_i1).toInt
              have h_le : i.toNat ≤ (i + 1).toNat := by rw [h_i1]; omega
              exact h_v_sorted i.toNat (i + 1).toNat hi_lt hi_i1 h_le
          exact ih (i + 1) true _ r h_meas h_i1_le hres h_new_sorted h_new_le_vi
            (fun h => by cases h)
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_sorted_at_step_pass_fail v x i true acc hi_lt (Or.inl rfl) h_big] at hres
          cases hres
      | false =>
        by_cases h_vi_ge : (v.val[i.toNat]'hi_lt).toInt ≥ x.toInt
        · by_cases h_acc : acc.val.size + 2 < USize64.size
          · rw [insert_sorted_at_step_insert v x i acc hi_lt h_vi_ge h_acc] at hres
            have h_new_sorted : sorted_asc (acc.val ++ #[x, v.val[i.toNat]'hi_lt]) := by
              apply sorted_asc_append_pair acc.val x (v.val[i.toNat]'hi_lt) h_acc_sorted
              · intro k hk; exact h_acc_le_x rfl k hk
              · exact h_vi_ge
            have h_new_le_vi :
                ∀ (k : Nat) (hk : k < (acc.val ++ #[x, v.val[i.toNat]'hi_lt]).size)
                  (hi_i1 : (i + 1).toNat < v.val.size),
                  ((acc.val ++ #[x, v.val[i.toNat]'hi_lt])[k]'hk).toInt
                    ≤ (v.val[(i + 1).toNat]'hi_i1).toInt := by
              intro k hk hi_i1
              rw [Array.size_append] at hk
              have h_two : (#[x, v.val[i.toNat]'hi_lt] : Array i64).size = 2 := rfl
              have h_v_step : (v.val[i.toNat]'hi_lt).toInt ≤ (v.val[(i + 1).toNat]'hi_i1).toInt := by
                have h_le : i.toNat ≤ (i + 1).toNat := by rw [h_i1]; omega
                exact h_v_sorted i.toNat (i + 1).toNat hi_lt hi_i1 h_le
              by_cases h_k_lt : k < acc.val.size
              · rw [Array.getElem_append_left h_k_lt]
                have h_acc_k := h_acc_le_vi k h_k_lt hi_lt
                omega
              · have h_k_ge : acc.val.size ≤ k := by omega
                rw [Array.getElem_append_right h_k_ge]
                by_cases h_k_eq0 : k - acc.val.size = 0
                · have h_zero_lt : (0 : Nat) < (#[x, v.val[i.toNat]'hi_lt] : Array i64).size := by
                    rw [h_two]; omega
                  rw [show ((#[x, v.val[i.toNat]'hi_lt] : Array i64)[k - acc.val.size]'(by rw [h_k_eq0]; exact h_zero_lt))
                          = (#[x, v.val[i.toNat]'hi_lt] : Array i64)[0]'h_zero_lt from by simp [h_k_eq0]]
                  show x.toInt ≤ (v.val[(i + 1).toNat]'hi_i1).toInt
                  omega
                · have h_k_eq1 : k - acc.val.size = 1 := by omega
                  have h_one_lt : (1 : Nat) < (#[x, v.val[i.toNat]'hi_lt] : Array i64).size := by
                    rw [h_two]; omega
                  rw [show ((#[x, v.val[i.toNat]'hi_lt] : Array i64)[k - acc.val.size]'(by rw [h_k_eq1]; exact h_one_lt))
                          = (#[x, v.val[i.toNat]'hi_lt] : Array i64)[1]'h_one_lt from by simp [h_k_eq1]]
                  show (v.val[i.toNat]'hi_lt).toInt ≤ (v.val[(i + 1).toNat]'hi_i1).toInt
                  exact h_v_step
            exact ih (i + 1) true _ r h_meas h_i1_le hres h_new_sorted h_new_le_vi
              (fun h => by cases h)
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 2 := by omega
            rw [insert_sorted_at_step_insert_fail v x i acc hi_lt h_vi_ge h_big] at hres
            cases hres
        · have h_lt : (v.val[i.toNat]'hi_lt).toInt < x.toInt := by omega
          by_cases h_acc : acc.val.size + 1 < USize64.size
          · rw [insert_sorted_at_step_pass v x i false acc hi_lt (Or.inr h_lt) h_acc] at hres
            have h_new_sorted : sorted_asc (acc.val ++ #[v.val[i.toNat]'hi_lt]) := by
              apply sorted_asc_append_singleton acc.val (v.val[i.toNat]'hi_lt) h_acc_sorted
              intro k hk
              exact h_acc_le_vi k hk hi_lt
            have h_new_le_vi :
                ∀ (k : Nat) (hk : k < (acc.val ++ #[v.val[i.toNat]'hi_lt]).size)
                  (hi_i1 : (i + 1).toNat < v.val.size),
                  ((acc.val ++ #[v.val[i.toNat]'hi_lt])[k]'hk).toInt
                    ≤ (v.val[(i + 1).toNat]'hi_i1).toInt := by
              intro k hk hi_i1
              rw [Array.size_append] at hk
              have h_one : (#[v.val[i.toNat]'hi_lt] : Array i64).size = 1 := rfl
              have h_v_step : (v.val[i.toNat]'hi_lt).toInt ≤ (v.val[(i + 1).toNat]'hi_i1).toInt := by
                have h_le : i.toNat ≤ (i + 1).toNat := by rw [h_i1]; omega
                exact h_v_sorted i.toNat (i + 1).toNat hi_lt hi_i1 h_le
              by_cases h_k_lt : k < acc.val.size
              · rw [Array.getElem_append_left h_k_lt]
                have h_acc_k := h_acc_le_vi k h_k_lt hi_lt
                omega
              · have h_k_ge : acc.val.size ≤ k := by omega
                rw [Array.getElem_append_right h_k_ge]
                have h_idx : k - acc.val.size = 0 := by omega
                have h_zero_lt : (0 : Nat) < (#[v.val[i.toNat]'hi_lt] : Array i64).size := by
                  rw [h_one]; omega
                rw [show ((#[v.val[i.toNat]'hi_lt] : Array i64)[k - acc.val.size]'(by rw [h_idx]; exact h_zero_lt))
                        = (#[v.val[i.toNat]'hi_lt] : Array i64)[0]'h_zero_lt from by simp [h_idx]]
                exact h_v_step
            have h_new_le_x :
                false = false → ∀ (k : Nat) (hk : k < (acc.val ++ #[v.val[i.toNat]'hi_lt]).size),
                  ((acc.val ++ #[v.val[i.toNat]'hi_lt])[k]'hk).toInt ≤ x.toInt := by
              intro _ k hk
              rw [Array.size_append] at hk
              have h_one : (#[v.val[i.toNat]'hi_lt] : Array i64).size = 1 := rfl
              by_cases h_k_lt : k < acc.val.size
              · rw [Array.getElem_append_left h_k_lt]
                exact h_acc_le_x rfl k h_k_lt
              · have h_k_ge : acc.val.size ≤ k := by omega
                rw [Array.getElem_append_right h_k_ge]
                have h_idx : k - acc.val.size = 0 := by omega
                have h_zero_lt : (0 : Nat) < (#[v.val[i.toNat]'hi_lt] : Array i64).size := by
                  rw [h_one]; omega
                rw [show ((#[v.val[i.toNat]'hi_lt] : Array i64)[k - acc.val.size]'(by rw [h_idx]; exact h_zero_lt))
                        = (#[v.val[i.toNat]'hi_lt] : Array i64)[0]'h_zero_lt from by simp [h_idx]]
                show (v.val[i.toNat]'hi_lt).toInt ≤ x.toInt
                omega
            exact ih (i + 1) false _ r h_meas h_i1_le hres h_new_sorted h_new_le_vi h_new_le_x
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 1 := by omega
            rw [insert_sorted_at_step_pass_fail v x i false acc hi_lt (Or.inr h_lt) h_big] at hres
            cases hres

private theorem insert_sorted_sorted (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (r : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_069_strange_sort_list.insert_sorted v x = RustM.ok r)
    (h_v_sorted : sorted_asc v.val) :
    sorted_asc r.val := by
  unfold clever_069_strange_sort_list.insert_sorted at hres
  have h_deref :
      (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec i64 alloc.alloc.Global) v : RustM _) = RustM.ok v := rfl
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_deref, h_new] at hres
  simp only [RustM_ok_bind] at hres
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_meas : v.val.size - (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  have h_le : (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  have h_empty_sorted : sorted_asc ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val := by
    intro k₁ k₂ h₁ _ _
    have : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  have h_empty_le_vi :
      ∀ (k : Nat) (hk : k < ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size)
        (_ : (0 : usize).toNat < v.val.size),
      (((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val[k]'hk).toInt
        ≤ (v.val[(0 : usize).toNat]'(by assumption)).toInt := by
    intro k hk _
    have h_empty : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  have h_empty_le_x : false = false →
      ∀ (k : Nat) (hk : k < ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size),
      (((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val[k]'hk).toInt ≤ x.toInt := by
    intro _ k hk
    have h_empty : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  exact insert_sorted_at_sorted v x h_v_sorted v.val.size (0 : usize) false
    ⟨(List.nil).toArray, by grind⟩ r h_meas h_le hres h_empty_sorted h_empty_le_vi h_empty_le_x

/-- `sort_at` produces a sorted output. -/
private theorem sort_at_sorted :
    ∀ (n : Nat) (l : RustSlice i64)
      (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      clever_069_strange_sort_list.sort_at l i acc = RustM.ok r →
      sorted_asc acc.val →
      sorted_asc r.val := by
  intro n
  induction n with
  | zero =>
    intro l i acc r hm hi_le hres h_acc_sorted
    have hi_ge : l.val.size ≤ i.toNat := by omega
    rw [sort_at_oob l i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    exact h_acc_sorted
  | succ n ih =>
    intro l i acc r hm hi_le hres h_acc_sorted
    by_cases hi_ge : l.val.size ≤ i.toNat
    · rw [sort_at_oob l i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      exact h_acc_sorted
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_meas : l.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      rw [sort_at_step l i acc hi_lt] at hres
      generalize h_ins : clever_069_strange_sort_list.insert_sorted acc (l.val[i.toNat]'hi_lt) = ins_res at hres
      cases ins_res with
      | none =>
        exfalso
        have hh : (do let acc' ← (none : RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                       clever_069_strange_sort_list.sort_at l (i + 1) acc')
                  = RustM.ok r := hres
        cases hh
      | some res' =>
        cases res' with
        | error e =>
          exfalso
          have hh : (do let acc' ← (some (Except.error e) :
                                      RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                         clever_069_strange_sort_list.sort_at l (i + 1) acc')
                    = RustM.ok r := hres
          cases hh
        | ok acc' =>
          have h_ins_ok : clever_069_strange_sort_list.insert_sorted acc (l.val[i.toNat]'hi_lt) = RustM.ok acc' := h_ins
          simp only [RustM_ok_bind] at hres
          have h_acc'_sorted : sorted_asc acc'.val :=
            insert_sorted_sorted acc (l.val[i.toNat]'hi_lt) acc' h_ins_ok h_acc_sorted
          exact ih l (i + 1) acc' r h_meas h_i1_le hres h_acc'_sorted

/-- Get-element congruence: if two indices are equal as Nats, the looked-up element is the same. -/
private theorem array_get_idx_eq {α : Type} (a : Array α) (i j : Nat)
    (hi : i < a.size) (hj : j < a.size) (h : i = j) :
    a[i]'hi = a[j]'hj := by
  subst h; rfl

/-! ## Modular and div-by-two helpers for `build_strange_at`. -/

private theorem usize_mod_two_ok (i : usize) :
    (i %? (2 : usize) : RustM usize) = RustM.ok (i % (2 : usize)) := by
  show (rust_primitives.ops.arith.Rem.rem i (2 : usize) : RustM usize) = RustM.ok _
  show (if (2 : usize) = 0 then (.fail .divisionByZero : RustM usize)
         else pure (i % 2)) = _
  have h_ne : (2 : usize) ≠ 0 := by decide
  rw [if_neg h_ne]; rfl

private theorem usize_mod_two_toNat (i : usize) :
    (i % (2 : usize)).toNat = i.toNat % 2 := by
  show ((⟨i.toBitVec % (2 : usize).toBitVec⟩ : USize64)).toNat = _
  show (i.toBitVec % (2 : usize).toBitVec).toNat = i.toNat % 2
  rw [BitVec.toNat_umod]
  rfl

private theorem usize_mod_two_eq_zero_iff (i : usize) :
    ((i % (2 : usize)) == (0 : usize)) = decide (i.toNat % 2 = 0) := by
  by_cases h : i.toNat % 2 = 0
  · rw [decide_eq_true h]
    have : i % (2 : usize) = (0 : usize) := by
      apply USize64.toNat_inj.mp
      rw [usize_mod_two_toNat, usize_zero_toNat]
      exact h
    rw [this]; rfl
  · rw [decide_eq_false h]
    have h_ne : i % (2 : usize) ≠ (0 : usize) := by
      intro heq
      apply h
      have := congrArg USize64.toNat heq
      rw [usize_mod_two_toNat, usize_zero_toNat] at this
      exact this
    rw [show ((i % (2 : usize)) == (0 : usize)) = false from by
          rw [beq_eq_false_iff_ne]; exact h_ne]

private theorem usize_div_two_ok (i : usize) :
    (i /? (2 : usize) : RustM usize) = RustM.ok (i / (2 : usize)) := by
  show (rust_primitives.ops.arith.Div.div i (2 : usize) : RustM usize) = RustM.ok _
  show (if (2 : usize) = 0 then (.fail .divisionByZero : RustM usize)
         else pure (i / 2)) = _
  have h_ne : (2 : usize) ≠ 0 := by decide
  rw [if_neg h_ne]; rfl

private theorem usize_div_two_toNat (i : usize) :
    (i / (2 : usize)).toNat = i.toNat / 2 := by
  show ((⟨i.toBitVec / (2 : usize).toBitVec⟩ : USize64)).toNat = _
  show (i.toBitVec / (2 : usize).toBitVec).toNat = i.toNat / 2
  rw [BitVec.toNat_udiv]
  rfl

/-! ## `build_strange_at` OOB + step lemmas. -/

private theorem build_strange_at_oob (sorted : RustSlice i64) (taken : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : sorted.val.size ≤ taken.toNat) :
    clever_069_strange_sort_list.build_strange_at sorted taken acc = RustM.ok acc := by
  unfold clever_069_strange_sort_list.build_strange_at
  have h_ofNat : (USize64.ofNat sorted.val.size).toNat = sorted.val.size :=
    USize64.toNat_ofNat_of_lt' sorted.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat sorted.val.size ≤ taken) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- Even-taken step: when taken.toNat < n and even, push sorted[(taken/2).toNat] and recurse.

    Indexed by `(taken / (2 : usize)).toNat`; callers use `usize_div_two_toNat` to
    convert to `taken.toNat / 2` form. -/
private theorem build_strange_at_step_even (sorted : RustSlice i64) (taken : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : taken.toNat < sorted.val.size)
    (heven : taken.toNat % 2 = 0)
    (hj : (taken / (2 : usize)).toNat < sorted.val.size)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_069_strange_sort_list.build_strange_at sorted taken acc =
      clever_069_strange_sort_list.build_strange_at sorted (taken + 1)
        (push_one acc (sorted.val[(taken / (2 : usize)).toNat]'hj) h_acc) := by
  conv => lhs; unfold clever_069_strange_sort_list.build_strange_at
  have h_size_lt : sorted.val.size < USize64.size := sorted.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_t : taken.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat sorted.val.size).toNat = sorted.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat sorted.val.size ≤ taken) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_div : (taken /? (2 : usize) : RustM usize) = RustM.ok (taken / (2 : usize)) :=
    usize_div_two_ok taken
  have h_mod : (taken %? (2 : usize) : RustM usize) = RustM.ok (taken % (2 : usize)) :=
    usize_mod_two_ok taken
  have h_mod_zero : ((taken % (2 : usize)) == (0 : usize)) = true := by
    rw [usize_mod_two_eq_zero_iff]; exact decide_eq_true heven
  have h_idx : (sorted[(taken / (2 : usize))]_? : RustM i64) =
                RustM.ok (sorted.val[(taken / (2 : usize)).toNat]'hj) := by
    show (if h : (taken / (2 : usize)).toNat < sorted.val.size then pure (sorted.val[taken / (2 : usize)])
            else .fail .arrayOutOfBounds)
        = RustM.ok (sorted.val[(taken / (2 : usize)).toNat]'hj)
    rw [dif_pos hj]; rfl
  have h_add : (taken +? (1 : usize) : RustM usize) = RustM.ok (taken + 1) :=
    usize_add_one_ok taken h_no_ov_t
  have h_app_size :
      acc.val.size + (#[sorted.val[(taken / (2 : usize)).toNat]'hj] : Array i64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  have h_extend :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[sorted.val[(taken / (2 : usize)).toNat]'hj], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.ok (push_one acc (sorted.val[(taken / (2 : usize)).toNat]'hj) h_acc) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_div, h_mod, rust_primitives.cmp.eq, h_mod_zero, ↓reduceIte,
             h_idx]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[sorted.val[(taken / (2 : usize)).toNat]'hj] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[sorted.val[(taken / (2 : usize)).toNat]'hj], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend]
  simp only [RustM_ok_bind]
  rw [h_add]
  simp only [RustM_ok_bind]

/-- Odd-taken step: when taken.toNat < n and odd, push sorted[((n-1) - taken/2).toNat] and recurse.

    Indexed by the usize-arithmetic-derived `((USize64.ofNat sorted.val.size) - 1 - (taken / 2)).toNat`;
    callers convert to `sorted.val.size - 1 - taken.toNat / 2` via the helpers. -/
private theorem build_strange_at_step_odd (sorted : RustSlice i64) (taken : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : taken.toNat < sorted.val.size)
    (hodd : taken.toNat % 2 = 1)
    (hj : ((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat < sorted.val.size)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_069_strange_sort_list.build_strange_at sorted taken acc =
      clever_069_strange_sort_list.build_strange_at sorted (taken + 1)
        (push_one acc
          (sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj)
          h_acc) := by
  conv => lhs; unfold clever_069_strange_sort_list.build_strange_at
  have h_size_lt : sorted.val.size < USize64.size := sorted.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_t : taken.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat sorted.val.size).toNat = sorted.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat sorted.val.size ≤ taken) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_div : (taken /? (2 : usize) : RustM usize) = RustM.ok (taken / (2 : usize)) :=
    usize_div_two_ok taken
  have h_mod : (taken %? (2 : usize) : RustM usize) = RustM.ok (taken % (2 : usize)) :=
    usize_mod_two_ok taken
  have h_mod_one : ((taken % (2 : usize)) == (0 : usize)) = false := by
    rw [usize_mod_two_eq_zero_iff]
    exact decide_eq_false (by omega)
  have h_half_toNat : (taken / (2 : usize)).toNat = taken.toNat / 2 := usize_div_two_toNat taken
  have h_n_pos : 0 < sorted.val.size := by omega
  have h_n_minus_one_sub_one_pos : (0 : Nat) < (USize64.ofNat sorted.val.size).toNat := by
    rw [h_ofNat]; exact h_n_pos
  have h_sub_1 : ((USize64.ofNat sorted.val.size) -? (1 : usize) : RustM usize)
                  = RustM.ok ((USize64.ofNat sorted.val.size) - 1) :=
    usize_sub_one_ok _ h_n_minus_one_sub_one_pos
  have h_sub_1_toNat : ((USize64.ofNat sorted.val.size) - 1).toNat = sorted.val.size - 1 := by
    rw [usize_sub_one_toNat _ h_n_minus_one_sub_one_pos, h_ofNat]
  have h_half_le : (taken / (2 : usize)).toNat ≤ ((USize64.ofNat sorted.val.size) - 1).toNat := by
    rw [h_half_toNat, h_sub_1_toNat]
    omega
  have h_sub_2 : ((USize64.ofNat sorted.val.size) - 1 -? (taken / (2 : usize)) : RustM usize)
                  = RustM.ok ((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))) :=
    usize_sub_ok _ _ h_half_le
  have h_idx : (sorted[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize)))]_? : RustM i64)
                = RustM.ok (sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj) := by
    show (if h : ((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat < sorted.val.size
              then pure (sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize)))])
            else .fail .arrayOutOfBounds)
        = RustM.ok (sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj)
    rw [dif_pos hj]; rfl
  have h_add : (taken +? (1 : usize) : RustM usize) = RustM.ok (taken + 1) :=
    usize_add_one_ok taken h_no_ov_t
  have h_app_size :
      acc.val.size + (#[sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj] : Array i64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  have h_extend :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.ok (push_one acc (sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj) h_acc) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_div, h_mod, rust_primitives.cmp.eq, h_mod_one, ↓reduceIte,
             h_sub_1, h_sub_2, h_idx]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend]
  simp only [RustM_ok_bind]
  rw [h_add]
  simp only [RustM_ok_bind]

/-! ### Fail variants for `build_strange_at`. -/

private theorem build_strange_at_step_even_size_fail (sorted : RustSlice i64) (taken : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : taken.toNat < sorted.val.size)
    (heven : taken.toNat % 2 = 0)
    (hj : (taken / (2 : usize)).toNat < sorted.val.size)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_069_strange_sort_list.build_strange_at sorted taken acc =
      RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_069_strange_sort_list.build_strange_at
  have h_ofNat : (USize64.ofNat sorted.val.size).toNat = sorted.val.size :=
    USize64.toNat_ofNat_of_lt' sorted.size_lt_usizeSize
  have h_cond_outer : decide (USize64.ofNat sorted.val.size ≤ taken) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_div : (taken /? (2 : usize) : RustM usize) = RustM.ok (taken / (2 : usize)) :=
    usize_div_two_ok taken
  have h_mod : (taken %? (2 : usize) : RustM usize) = RustM.ok (taken % (2 : usize)) :=
    usize_mod_two_ok taken
  have h_mod_zero : ((taken % (2 : usize)) == (0 : usize)) = true := by
    rw [usize_mod_two_eq_zero_iff]; exact decide_eq_true heven
  have h_idx : (sorted[(taken / (2 : usize))]_? : RustM i64) =
                RustM.ok (sorted.val[(taken / (2 : usize)).toNat]'hj) := by
    show (if h : (taken / (2 : usize)).toNat < sorted.val.size then pure (sorted.val[taken / (2 : usize)])
            else .fail .arrayOutOfBounds)
        = RustM.ok (sorted.val[(taken / (2 : usize)).toNat]'hj)
    rw [dif_pos hj]; rfl
  have h_app_size_neg :
      ¬ acc.val.size + (#[sorted.val[(taken / (2 : usize)).toNat]'hj] : Array i64).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[sorted.val[(taken / (2 : usize)).toNat]'hj], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_div, h_mod, rust_primitives.cmp.eq, h_mod_zero, ↓reduceIte,
             h_idx]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[sorted.val[(taken / (2 : usize)).toNat]'hj] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[sorted.val[(taken / (2 : usize)).toNat]'hj], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

private theorem build_strange_at_step_odd_size_fail (sorted : RustSlice i64) (taken : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : taken.toNat < sorted.val.size)
    (hodd : taken.toNat % 2 = 1)
    (hj : ((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat < sorted.val.size)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_069_strange_sort_list.build_strange_at sorted taken acc =
      RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_069_strange_sort_list.build_strange_at
  have h_size_lt : sorted.val.size < USize64.size := sorted.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat sorted.val.size).toNat = sorted.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat sorted.val.size ≤ taken) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_div : (taken /? (2 : usize) : RustM usize) = RustM.ok (taken / (2 : usize)) :=
    usize_div_two_ok taken
  have h_mod : (taken %? (2 : usize) : RustM usize) = RustM.ok (taken % (2 : usize)) :=
    usize_mod_two_ok taken
  have h_mod_one : ((taken % (2 : usize)) == (0 : usize)) = false := by
    rw [usize_mod_two_eq_zero_iff]
    exact decide_eq_false (by omega)
  have h_half_toNat : (taken / (2 : usize)).toNat = taken.toNat / 2 := usize_div_two_toNat taken
  have h_n_pos : 0 < sorted.val.size := by omega
  have h_n_minus_one_sub_one_pos : (0 : Nat) < (USize64.ofNat sorted.val.size).toNat := by
    rw [h_ofNat]; exact h_n_pos
  have h_sub_1 : ((USize64.ofNat sorted.val.size) -? (1 : usize) : RustM usize)
                  = RustM.ok ((USize64.ofNat sorted.val.size) - 1) :=
    usize_sub_one_ok _ h_n_minus_one_sub_one_pos
  have h_sub_1_toNat : ((USize64.ofNat sorted.val.size) - 1).toNat = sorted.val.size - 1 := by
    rw [usize_sub_one_toNat _ h_n_minus_one_sub_one_pos, h_ofNat]
  have h_half_le : (taken / (2 : usize)).toNat ≤ ((USize64.ofNat sorted.val.size) - 1).toNat := by
    rw [h_half_toNat, h_sub_1_toNat]
    omega
  have h_sub_2 : ((USize64.ofNat sorted.val.size) - 1 -? (taken / (2 : usize)) : RustM usize)
                  = RustM.ok ((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))) :=
    usize_sub_ok _ _ h_half_le
  have h_idx : (sorted[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize)))]_? : RustM i64)
                = RustM.ok (sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj) := by
    show (if h : ((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat < sorted.val.size
              then pure (sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize)))])
            else .fail .arrayOutOfBounds)
        = RustM.ok (sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj)
    rw [dif_pos hj]; rfl
  have h_app_size_neg :
      ¬ acc.val.size + (#[sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj] : Array i64).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_div, h_mod, rust_primitives.cmp.eq, h_mod_one, ↓reduceIte,
             h_sub_1, h_sub_2, h_idx]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

/-! ## `build_strange_at` size invariant. -/

private theorem build_strange_at_size :
    ∀ (n : Nat) (sorted : RustSlice i64) (taken : usize)
      (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      sorted.val.size - taken.toNat ≤ n →
      taken.toNat ≤ sorted.val.size →
      clever_069_strange_sort_list.build_strange_at sorted taken acc = RustM.ok r →
      r.val.size = acc.val.size + (sorted.val.size - taken.toNat) := by
  intro n
  induction n with
  | zero =>
    intro sorted taken acc r hm hi_le hres
    have hi_ge : sorted.val.size ≤ taken.toNat := by omega
    rw [build_strange_at_oob sorted taken acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    omega
  | succ n ih =>
    intro sorted taken acc r hm hi_le hres
    by_cases hi_ge : sorted.val.size ≤ taken.toNat
    · rw [build_strange_at_oob sorted taken acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      omega
    · have hi_lt : taken.toNat < sorted.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : sorted.val.size < USize64.size := sorted.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_t : taken.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_t1 : (taken + 1).toNat = taken.toNat + 1 := usize_add_one_toNat taken h_no_ov_t
      have h_t1_le : (taken + 1).toNat ≤ sorted.val.size := by rw [h_t1]; omega
      have h_meas : sorted.val.size - (taken + 1).toNat ≤ n := by rw [h_t1]; omega
      have h_half_toNat : (taken / (2 : usize)).toNat = taken.toNat / 2 := usize_div_two_toNat taken
      by_cases heven : taken.toNat % 2 = 0
      · -- Even case: index = (taken/2).toNat = taken.toNat / 2 < sorted.size
        have hj_e : (taken / (2 : usize)).toNat < sorted.val.size := by
          rw [h_half_toNat]; omega
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [build_strange_at_step_even sorted taken acc hi_lt heven hj_e h_acc] at hres
          have h_push_size :
              (push_one acc (sorted.val[(taken / (2 : usize)).toNat]'hj_e) h_acc).val.size = acc.val.size + 1 := by
            show (acc.val ++ #[sorted.val[(taken / (2 : usize)).toNat]'hj_e]).size = acc.val.size + 1
            rw [Array.size_append]; rfl
          have h_ind := ih sorted (taken + 1)
            (push_one acc (sorted.val[(taken / (2 : usize)).toNat]'hj_e) h_acc) r h_meas h_t1_le hres
          rw [h_push_size, h_t1] at h_ind
          omega
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [build_strange_at_step_even_size_fail sorted taken acc hi_lt heven hj_e h_big] at hres
          cases hres
      · -- Odd case
        have hodd : taken.toNat % 2 = 1 := by omega
        have h_ofNat : (USize64.ofNat sorted.val.size).toNat = sorted.val.size :=
          USize64.toNat_ofNat_of_lt' h_size_lt
        have h_n_pos : 0 < (USize64.ofNat sorted.val.size).toNat := by rw [h_ofNat]; omega
        have h_sub_1_toNat : ((USize64.ofNat sorted.val.size) - 1).toNat = sorted.val.size - 1 := by
          rw [usize_sub_one_toNat _ h_n_pos, h_ofNat]
        have h_half_le : (taken / (2 : usize)).toNat ≤ ((USize64.ofNat sorted.val.size) - 1).toNat := by
          rw [h_half_toNat, h_sub_1_toNat]; omega
        have h_sub_2_toNat : ((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat
                              = sorted.val.size - 1 - taken.toNat / 2 := by
          rw [usize_sub_toNat _ _ h_half_le, h_sub_1_toNat, h_half_toNat]
        have hj_o : ((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat
                      < sorted.val.size := by
          rw [h_sub_2_toNat]; omega
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [build_strange_at_step_odd sorted taken acc hi_lt hodd hj_o h_acc] at hres
          have h_push_size :
              (push_one acc (sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o) h_acc).val.size
                = acc.val.size + 1 := by
            show (acc.val ++ #[sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o]).size
                  = acc.val.size + 1
            rw [Array.size_append]; rfl
          have h_ind := ih sorted (taken + 1)
            (push_one acc (sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o) h_acc) r h_meas h_t1_le hres
          rw [h_push_size, h_t1] at h_ind
          omega
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [build_strange_at_step_odd_size_fail sorted taken acc hi_lt hodd hj_o h_big] at hres
          cases hres

/-! ## `build_strange_at` prefix preservation. -/

private theorem build_strange_at_prefix_preserved :
    ∀ (n : Nat) (sorted : RustSlice i64) (taken : usize)
      (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      sorted.val.size - taken.toNat ≤ n →
      taken.toNat ≤ sorted.val.size →
      clever_069_strange_sort_list.build_strange_at sorted taken acc = RustM.ok r →
      ∀ (k : Nat) (hk_acc : k < acc.val.size) (hk_r : k < r.val.size),
        r.val[k]'hk_r = acc.val[k]'hk_acc := by
  intro n
  induction n with
  | zero =>
    intro sorted taken acc r hm hi_le hres k hk_acc hk_r
    have hi_ge : sorted.val.size ≤ taken.toNat := by omega
    rw [build_strange_at_oob sorted taken acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    rfl
  | succ n ih =>
    intro sorted taken acc r hm hi_le hres k hk_acc hk_r
    by_cases hi_ge : sorted.val.size ≤ taken.toNat
    · rw [build_strange_at_oob sorted taken acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      rfl
    · have hi_lt : taken.toNat < sorted.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : sorted.val.size < USize64.size := sorted.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_t : taken.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_t1 : (taken + 1).toNat = taken.toNat + 1 := usize_add_one_toNat taken h_no_ov_t
      have h_t1_le : (taken + 1).toNat ≤ sorted.val.size := by rw [h_t1]; omega
      have h_meas : sorted.val.size - (taken + 1).toNat ≤ n := by rw [h_t1]; omega
      have h_half_toNat : (taken / (2 : usize)).toNat = taken.toNat / 2 := usize_div_two_toNat taken
      by_cases heven : taken.toNat % 2 = 0
      · have hj_e : (taken / (2 : usize)).toNat < sorted.val.size := by
          rw [h_half_toNat]; omega
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [build_strange_at_step_even sorted taken acc hi_lt heven hj_e h_acc] at hres
          have h_push_size :
              (push_one acc (sorted.val[(taken / (2 : usize)).toNat]'hj_e) h_acc).val.size = acc.val.size + 1 := by
            show (acc.val ++ #[sorted.val[(taken / (2 : usize)).toNat]'hj_e]).size = acc.val.size + 1
            rw [Array.size_append]; rfl
          have hk_push : k < (push_one acc (sorted.val[(taken / (2 : usize)).toNat]'hj_e) h_acc).val.size := by
            rw [h_push_size]; omega
          have h_ih := ih sorted (taken + 1)
            (push_one acc (sorted.val[(taken / (2 : usize)).toNat]'hj_e) h_acc) r h_meas h_t1_le hres
            k hk_push hk_r
          rw [h_ih]
          show ((acc.val ++ #[sorted.val[(taken / (2 : usize)).toNat]'hj_e])[k]'(by
            rw [Array.size_append]
            have : (#[sorted.val[(taken / (2 : usize)).toNat]'hj_e] : Array i64).size = 1 := rfl
            omega)) = acc.val[k]'hk_acc
          exact Array.getElem_append_left hk_acc
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [build_strange_at_step_even_size_fail sorted taken acc hi_lt heven hj_e h_big] at hres
          cases hres
      · have hodd : taken.toNat % 2 = 1 := by omega
        have h_ofNat : (USize64.ofNat sorted.val.size).toNat = sorted.val.size :=
          USize64.toNat_ofNat_of_lt' h_size_lt
        have h_n_pos : 0 < (USize64.ofNat sorted.val.size).toNat := by rw [h_ofNat]; omega
        have h_sub_1_toNat : ((USize64.ofNat sorted.val.size) - 1).toNat = sorted.val.size - 1 := by
          rw [usize_sub_one_toNat _ h_n_pos, h_ofNat]
        have h_half_le : (taken / (2 : usize)).toNat ≤ ((USize64.ofNat sorted.val.size) - 1).toNat := by
          rw [h_half_toNat, h_sub_1_toNat]; omega
        have h_sub_2_toNat : ((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat
                              = sorted.val.size - 1 - taken.toNat / 2 := by
          rw [usize_sub_toNat _ _ h_half_le, h_sub_1_toNat, h_half_toNat]
        have hj_o : ((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat
                      < sorted.val.size := by
          rw [h_sub_2_toNat]; omega
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [build_strange_at_step_odd sorted taken acc hi_lt hodd hj_o h_acc] at hres
          have h_push_size :
              (push_one acc (sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o) h_acc).val.size
                = acc.val.size + 1 := by
            show (acc.val ++ #[sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o]).size
                  = acc.val.size + 1
            rw [Array.size_append]; rfl
          have hk_push : k < (push_one acc (sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o) h_acc).val.size := by
            rw [h_push_size]; omega
          have h_ih := ih sorted (taken + 1)
            (push_one acc (sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o) h_acc) r h_meas h_t1_le hres
            k hk_push hk_r
          rw [h_ih]
          show ((acc.val ++ #[sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o])[k]'(by
            rw [Array.size_append]
            have : (#[sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o] : Array i64).size = 1 := rfl
            omega)) = acc.val[k]'hk_acc
          exact Array.getElem_append_left hk_acc
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [build_strange_at_step_odd_size_fail sorted taken acc hi_lt hodd hj_o h_big] at hres
          cases hres

/-! ## `build_strange_at` even-position formula: r[k] = sorted[k/2] when k even. -/

private theorem build_strange_at_even_position :
    ∀ (n : Nat) (sorted : RustSlice i64) (taken : usize)
      (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      sorted.val.size - taken.toNat ≤ n →
      taken.toNat ≤ sorted.val.size →
      acc.val.size = taken.toNat →
      clever_069_strange_sort_list.build_strange_at sorted taken acc = RustM.ok r →
      ∀ (k : Nat) (hk_r : k < r.val.size) (heven : k % 2 = 0)
        (hk_ge_t : taken.toNat ≤ k) (hk_lt_n : k < sorted.val.size),
        ∃ (hj : k / 2 < sorted.val.size), r.val[k]'hk_r = sorted.val[k / 2]'hj := by
  intro n
  induction n with
  | zero =>
    intro sorted taken acc r hm hi_le h_acc_eq hres k hk_r heven hk_ge_t hk_lt_n
    exfalso; omega
  | succ n ih =>
    intro sorted taken acc r hm hi_le h_acc_eq hres k hk_r heven hk_ge_t hk_lt_n
    by_cases hi_ge : sorted.val.size ≤ taken.toNat
    · exfalso; omega
    · have hi_lt : taken.toNat < sorted.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : sorted.val.size < USize64.size := sorted.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_t : taken.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_t1 : (taken + 1).toNat = taken.toNat + 1 := usize_add_one_toNat taken h_no_ov_t
      have h_t1_le : (taken + 1).toNat ≤ sorted.val.size := by rw [h_t1]; omega
      have h_meas : sorted.val.size - (taken + 1).toNat ≤ n := by rw [h_t1]; omega
      have h_half_toNat : (taken / (2 : usize)).toNat = taken.toNat / 2 := usize_div_two_toNat taken
      by_cases ht_even : taken.toNat % 2 = 0
      · -- Even taken: index is taken.toNat / 2.
        have hj_e : (taken / (2 : usize)).toNat < sorted.val.size := by
          rw [h_half_toNat]; omega
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [build_strange_at_step_even sorted taken acc hi_lt ht_even hj_e h_acc] at hres
          have h_push_size :
              (push_one acc (sorted.val[(taken / (2 : usize)).toNat]'hj_e) h_acc).val.size = acc.val.size + 1 := by
            show (acc.val ++ #[sorted.val[(taken / (2 : usize)).toNat]'hj_e]).size = acc.val.size + 1
            rw [Array.size_append]; rfl
          have h_acc_new_eq :
              (push_one acc (sorted.val[(taken / (2 : usize)).toNat]'hj_e) h_acc).val.size = (taken + 1).toNat := by
            rw [h_push_size, h_acc_eq, h_t1]
          by_cases h_eq_k : k = taken.toNat
          · subst h_eq_k
            have hk_push : taken.toNat < (push_one acc (sorted.val[(taken / (2 : usize)).toNat]'hj_e) h_acc).val.size := by
              rw [h_push_size, h_acc_eq]; omega
            have h_prefix := build_strange_at_prefix_preserved _ sorted (taken + 1)
              (push_one acc (sorted.val[(taken / (2 : usize)).toNat]'hj_e) h_acc) r (Nat.le_refl _) h_t1_le hres
              taken.toNat hk_push hk_r
            rw [h_prefix]
            have h_acc_le_t : acc.val.size ≤ taken.toNat := by rw [h_acc_eq]; exact Nat.le_refl _
            have h_get_push :
                ((push_one acc (sorted.val[(taken / (2 : usize)).toNat]'hj_e) h_acc).val[taken.toNat]'hk_push)
                = sorted.val[(taken / (2 : usize)).toNat]'hj_e := by
              show ((acc.val ++ #[sorted.val[(taken / (2 : usize)).toNat]'hj_e])[taken.toNat]'hk_push) = _
              rw [Array.getElem_append_right h_acc_le_t]
              have h_sub_zero : taken.toNat - acc.val.size = 0 := by rw [h_acc_eq]; omega
              simp [h_sub_zero]
            rw [h_get_push]
            have hj_target : taken.toNat / 2 < sorted.val.size := by
              rw [← h_half_toNat]; exact hj_e
            refine ⟨hj_target, ?_⟩
            exact array_get_idx_eq sorted.val (taken / (2 : usize)).toNat (taken.toNat / 2) hj_e hj_target h_half_toNat
          · -- k > taken.toNat. k is even, taken.toNat is even, so k ≥ taken.toNat + 2.
            have hk_ge_t1 : (taken + 1).toNat ≤ k := by rw [h_t1]; omega
            exact ih sorted (taken + 1)
              (push_one acc (sorted.val[(taken / (2 : usize)).toNat]'hj_e) h_acc) r h_meas h_t1_le
              h_acc_new_eq hres k hk_r heven hk_ge_t1 hk_lt_n
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [build_strange_at_step_even_size_fail sorted taken acc hi_lt ht_even hj_e h_big] at hres
          cases hres
      · -- Odd taken: index is sorted.size - 1 - taken/2 — but k is even, so k ≠ taken.toNat.
        have ht_odd : taken.toNat % 2 = 1 := by omega
        have h_ofNat : (USize64.ofNat sorted.val.size).toNat = sorted.val.size :=
          USize64.toNat_ofNat_of_lt' h_size_lt
        have h_n_pos : 0 < (USize64.ofNat sorted.val.size).toNat := by rw [h_ofNat]; omega
        have h_sub_1_toNat : ((USize64.ofNat sorted.val.size) - 1).toNat = sorted.val.size - 1 := by
          rw [usize_sub_one_toNat _ h_n_pos, h_ofNat]
        have h_half_le : (taken / (2 : usize)).toNat ≤ ((USize64.ofNat sorted.val.size) - 1).toNat := by
          rw [h_half_toNat, h_sub_1_toNat]; omega
        have h_sub_2_toNat : ((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat
                              = sorted.val.size - 1 - taken.toNat / 2 := by
          rw [usize_sub_toNat _ _ h_half_le, h_sub_1_toNat, h_half_toNat]
        have hj_o : ((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat
                      < sorted.val.size := by
          rw [h_sub_2_toNat]; omega
        have hk_ne_t : k ≠ taken.toNat := by
          intro h; rw [h] at heven; omega
        have hk_ge_t1 : (taken + 1).toNat ≤ k := by rw [h_t1]; omega
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [build_strange_at_step_odd sorted taken acc hi_lt ht_odd hj_o h_acc] at hres
          have h_push_size :
              (push_one acc (sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o) h_acc).val.size = acc.val.size + 1 := by
            show (acc.val ++ #[sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o]).size = acc.val.size + 1
            rw [Array.size_append]; rfl
          have h_acc_new_eq :
              (push_one acc (sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o) h_acc).val.size = (taken + 1).toNat := by
            rw [h_push_size, h_acc_eq, h_t1]
          exact ih sorted (taken + 1)
            (push_one acc (sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o) h_acc) r h_meas h_t1_le
            h_acc_new_eq hres k hk_r heven hk_ge_t1 hk_lt_n
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [build_strange_at_step_odd_size_fail sorted taken acc hi_lt ht_odd hj_o h_big] at hres
          cases hres

/-! ## `build_strange_at` odd-position formula: r[k] = sorted[n-1-k/2] when k odd. -/

private theorem build_strange_at_odd_position :
    ∀ (n : Nat) (sorted : RustSlice i64) (taken : usize)
      (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      sorted.val.size - taken.toNat ≤ n →
      taken.toNat ≤ sorted.val.size →
      acc.val.size = taken.toNat →
      clever_069_strange_sort_list.build_strange_at sorted taken acc = RustM.ok r →
      ∀ (k : Nat) (hk_r : k < r.val.size) (hodd : k % 2 = 1)
        (hk_ge_t : taken.toNat ≤ k) (hk_lt_n : k < sorted.val.size),
        ∃ (hj : sorted.val.size - 1 - k / 2 < sorted.val.size),
          r.val[k]'hk_r = sorted.val[sorted.val.size - 1 - k / 2]'hj := by
  intro n
  induction n with
  | zero =>
    intro sorted taken acc r hm hi_le h_acc_eq hres k hk_r hodd hk_ge_t hk_lt_n
    exfalso; omega
  | succ n ih =>
    intro sorted taken acc r hm hi_le h_acc_eq hres k hk_r hodd hk_ge_t hk_lt_n
    by_cases hi_ge : sorted.val.size ≤ taken.toNat
    · exfalso; omega
    · have hi_lt : taken.toNat < sorted.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : sorted.val.size < USize64.size := sorted.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_t : taken.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_t1 : (taken + 1).toNat = taken.toNat + 1 := usize_add_one_toNat taken h_no_ov_t
      have h_t1_le : (taken + 1).toNat ≤ sorted.val.size := by rw [h_t1]; omega
      have h_meas : sorted.val.size - (taken + 1).toNat ≤ n := by rw [h_t1]; omega
      have h_half_toNat : (taken / (2 : usize)).toNat = taken.toNat / 2 := usize_div_two_toNat taken
      by_cases ht_even : taken.toNat % 2 = 0
      · -- Even taken: index is taken.toNat / 2 — but k is odd, so k ≠ taken.toNat.
        have hj_e : (taken / (2 : usize)).toNat < sorted.val.size := by
          rw [h_half_toNat]; omega
        have hk_ne_t : k ≠ taken.toNat := by
          intro h; rw [h] at hodd; omega
        have hk_ge_t1 : (taken + 1).toNat ≤ k := by rw [h_t1]; omega
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [build_strange_at_step_even sorted taken acc hi_lt ht_even hj_e h_acc] at hres
          have h_push_size :
              (push_one acc (sorted.val[(taken / (2 : usize)).toNat]'hj_e) h_acc).val.size = acc.val.size + 1 := by
            show (acc.val ++ #[sorted.val[(taken / (2 : usize)).toNat]'hj_e]).size = acc.val.size + 1
            rw [Array.size_append]; rfl
          have h_acc_new_eq :
              (push_one acc (sorted.val[(taken / (2 : usize)).toNat]'hj_e) h_acc).val.size = (taken + 1).toNat := by
            rw [h_push_size, h_acc_eq, h_t1]
          exact ih sorted (taken + 1)
            (push_one acc (sorted.val[(taken / (2 : usize)).toNat]'hj_e) h_acc) r h_meas h_t1_le
            h_acc_new_eq hres k hk_r hodd hk_ge_t1 hk_lt_n
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [build_strange_at_step_even_size_fail sorted taken acc hi_lt ht_even hj_e h_big] at hres
          cases hres
      · -- Odd taken: index is sorted.size - 1 - taken/2. k may equal taken.toNat.
        have ht_odd : taken.toNat % 2 = 1 := by omega
        have h_ofNat : (USize64.ofNat sorted.val.size).toNat = sorted.val.size :=
          USize64.toNat_ofNat_of_lt' h_size_lt
        have h_n_pos : 0 < (USize64.ofNat sorted.val.size).toNat := by rw [h_ofNat]; omega
        have h_sub_1_toNat : ((USize64.ofNat sorted.val.size) - 1).toNat = sorted.val.size - 1 := by
          rw [usize_sub_one_toNat _ h_n_pos, h_ofNat]
        have h_half_le : (taken / (2 : usize)).toNat ≤ ((USize64.ofNat sorted.val.size) - 1).toNat := by
          rw [h_half_toNat, h_sub_1_toNat]; omega
        have h_sub_2_toNat : ((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat
                              = sorted.val.size - 1 - taken.toNat / 2 := by
          rw [usize_sub_toNat _ _ h_half_le, h_sub_1_toNat, h_half_toNat]
        have hj_o : ((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat
                      < sorted.val.size := by
          rw [h_sub_2_toNat]; omega
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [build_strange_at_step_odd sorted taken acc hi_lt ht_odd hj_o h_acc] at hres
          have h_push_size :
              (push_one acc (sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o) h_acc).val.size = acc.val.size + 1 := by
            show (acc.val ++ #[sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o]).size = acc.val.size + 1
            rw [Array.size_append]; rfl
          have h_acc_new_eq :
              (push_one acc (sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o) h_acc).val.size = (taken + 1).toNat := by
            rw [h_push_size, h_acc_eq, h_t1]
          by_cases h_eq_k : k = taken.toNat
          · subst h_eq_k
            have hk_push : taken.toNat < (push_one acc (sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o) h_acc).val.size := by
              rw [h_push_size, h_acc_eq]; omega
            have h_prefix := build_strange_at_prefix_preserved _ sorted (taken + 1)
              (push_one acc (sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o) h_acc) r (Nat.le_refl _) h_t1_le hres
              taken.toNat hk_push hk_r
            rw [h_prefix]
            have h_acc_le_t : acc.val.size ≤ taken.toNat := by rw [h_acc_eq]; exact Nat.le_refl _
            have h_get_push :
                ((push_one acc (sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o) h_acc).val[taken.toNat]'hk_push)
                = sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o := by
              show ((acc.val ++ #[sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o])[taken.toNat]'hk_push) = _
              rw [Array.getElem_append_right h_acc_le_t]
              have h_sub_zero : taken.toNat - acc.val.size = 0 := by rw [h_acc_eq]; omega
              simp [h_sub_zero]
            rw [h_get_push]
            have hj_target : sorted.val.size - 1 - taken.toNat / 2 < sorted.val.size := by omega
            refine ⟨hj_target, ?_⟩
            exact array_get_idx_eq sorted.val
              ((USize64.ofNat sorted.val.size - 1 - (taken / (2 : usize))).toNat)
              (sorted.val.size - 1 - taken.toNat / 2) hj_o hj_target h_sub_2_toNat
          · -- k ≠ taken.toNat, so k > taken.toNat (since k ≥ taken.toNat).
            have hk_ge_t1 : (taken + 1).toNat ≤ k := by rw [h_t1]; omega
            exact ih sorted (taken + 1)
              (push_one acc (sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o) h_acc) r h_meas h_t1_le
              h_acc_new_eq hres k hk_r hodd hk_ge_t1 hk_lt_n
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [build_strange_at_step_odd_size_fail sorted taken acc hi_lt ht_odd hj_o h_big] at hres
          cases hres

/-! ## `build_strange_at` multiset (vec_count) invariant.

  Phrased additively to avoid Nat subtraction. The key bijection:
  * Even outputs from steps [0, taken) consume sorted[0..(taken+1)/2).
  * Odd outputs from steps [0, taken) consume sorted[n - taken/2..n).
  These two ranges are disjoint and together cover sorted[0..taken positions]. -/
private theorem build_strange_at_count :
    ∀ (n_meas : Nat) (sorted : RustSlice i64) (taken : usize)
      (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global) (target : i64),
      sorted.val.size - taken.toNat ≤ n_meas →
      taken.toNat ≤ sorted.val.size →
      clever_069_strange_sort_list.build_strange_at sorted taken acc = RustM.ok r →
      vec_count r.val target r.val.size + vec_count sorted.val target ((taken.toNat + 1) / 2) =
        vec_count acc.val target acc.val.size +
          vec_count sorted.val target (sorted.val.size - taken.toNat / 2) := by
  intro n_meas
  induction n_meas with
  | zero =>
    intro sorted taken acc r target hm hi_le hres
    have hi_ge : sorted.val.size ≤ taken.toNat := by omega
    have hi_eq : taken.toNat = sorted.val.size := by omega
    rw [build_strange_at_oob sorted taken acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    -- Goal: vec_count acc target acc.size + vec_count sorted target ((n+1)/2)
    --       = vec_count acc target acc.size + vec_count sorted target (n - n/2)
    -- For Nat, (n+1)/2 = n - n/2 always.
    have h_idx_eq : (taken.toNat + 1) / 2 = sorted.val.size - taken.toNat / 2 := by
      rw [hi_eq]; omega
    rw [h_idx_eq]
  | succ n_meas ih =>
    intro sorted taken acc r target hm hi_le hres
    by_cases hi_ge : sorted.val.size ≤ taken.toNat
    · have hi_eq : taken.toNat = sorted.val.size := by omega
      rw [build_strange_at_oob sorted taken acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      have h_idx_eq : (taken.toNat + 1) / 2 = sorted.val.size - taken.toNat / 2 := by
        rw [hi_eq]; omega
      rw [h_idx_eq]
    · have hi_lt : taken.toNat < sorted.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : sorted.val.size < USize64.size := sorted.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_t : taken.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_t1 : (taken + 1).toNat = taken.toNat + 1 := usize_add_one_toNat taken h_no_ov_t
      have h_t1_le : (taken + 1).toNat ≤ sorted.val.size := by rw [h_t1]; omega
      have h_meas : sorted.val.size - (taken + 1).toNat ≤ n_meas := by rw [h_t1]; omega
      have h_half_toNat : (taken / (2 : usize)).toNat = taken.toNat / 2 := usize_div_two_toNat taken
      by_cases ht_even : taken.toNat % 2 = 0
      · -- Even step: pushes sorted[taken.toNat / 2]
        have hj_e : (taken / (2 : usize)).toNat < sorted.val.size := by
          rw [h_half_toNat]; omega
        have hj_e_nat : taken.toNat / 2 < sorted.val.size := by
          rw [← h_half_toNat]; exact hj_e
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [build_strange_at_step_even sorted taken acc hi_lt ht_even hj_e h_acc] at hres
          -- The pushed element is sorted.val[(taken/2).toNat] = sorted.val[taken.toNat/2]
          have h_push_size :
              (push_one acc (sorted.val[(taken / (2 : usize)).toNat]'hj_e) h_acc).val.size = acc.val.size + 1 := by
            show (acc.val ++ #[sorted.val[(taken / (2 : usize)).toNat]'hj_e]).size = acc.val.size + 1
            rw [Array.size_append]; rfl
          have ih_app := ih sorted (taken + 1) _ r target h_meas h_t1_le hres
          rw [h_t1] at ih_app
          -- The count of acc' = count of acc + (pushed = target ? 1 : 0)
          have h_count_pushed :
              vec_count (push_one acc (sorted.val[(taken / (2 : usize)).toNat]'hj_e) h_acc).val target
                (acc.val.size + 1) =
              vec_count acc.val target acc.val.size +
                (if sorted.val[(taken / (2 : usize)).toNat]'hj_e = target then 1 else 0) := by
            show vec_count (acc.val ++ #[sorted.val[(taken / (2 : usize)).toNat]'hj_e]) target (acc.val.size + 1) = _
            exact vec_count_append_singleton acc.val (sorted.val[(taken / (2 : usize)).toNat]'hj_e) target
          rw [h_push_size, h_count_pushed] at ih_app
          -- For even taken: (taken+1)/2 = taken/2; (taken+2)/2 = taken/2 + 1
          have h_idx_succ : (taken.toNat + 1 + 1) / 2 = taken.toNat / 2 + 1 := by omega
          have h_idx_eq : (taken.toNat + 1) / 2 = taken.toNat / 2 := by omega
          -- For even taken (taken+1)/2 = taken/2; (taken+1+1)/2 = taken/2 + 1
          -- vec_count sorted t (taken/2 + 1) = (sorted[taken/2] = t ? 1 : 0) + vec_count sorted t (taken/2)
          have h_vec_succ :
              vec_count sorted.val target (taken.toNat / 2 + 1) =
                (if sorted.val[taken.toNat / 2]'hj_e_nat = target then 1 else 0) +
                  vec_count sorted.val target (taken.toNat / 2) :=
            vec_count_succ sorted.val target (taken.toNat / 2) hj_e_nat
          -- The pushed value equals sorted[taken.toNat / 2]
          have h_val_eq :
              (if sorted.val[(taken / (2 : usize)).toNat]'hj_e = target then 1 else 0) =
              (if sorted.val[taken.toNat / 2]'hj_e_nat = target then 1 else 0) := by
            have h_elem_eq : sorted.val[(taken / (2 : usize)).toNat]'hj_e
                              = sorted.val[taken.toNat / 2]'hj_e_nat :=
              array_get_idx_eq sorted.val (taken / (2 : usize)).toNat (taken.toNat / 2)
                hj_e hj_e_nat h_half_toNat
            rw [h_elem_eq]
          -- For even taken: (n - (taken+1)/2) = (n - taken/2). So no change in the right side index.
          have h_n_taken1 : sorted.val.size - (taken.toNat + 1) / 2 = sorted.val.size - taken.toNat / 2 := by omega
          rw [h_n_taken1, h_idx_succ] at ih_app
          rw [h_vec_succ] at ih_app
          rw [h_idx_eq]
          rw [h_val_eq] at ih_app
          omega
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [build_strange_at_step_even_size_fail sorted taken acc hi_lt ht_even hj_e h_big] at hres
          cases hres
      · -- Odd step: pushes sorted[n - 1 - taken.toNat / 2]
        have ht_odd : taken.toNat % 2 = 1 := by omega
        have h_ofNat : (USize64.ofNat sorted.val.size).toNat = sorted.val.size :=
          USize64.toNat_ofNat_of_lt' h_size_lt
        have h_n_pos : 0 < (USize64.ofNat sorted.val.size).toNat := by rw [h_ofNat]; omega
        have h_sub_1_toNat : ((USize64.ofNat sorted.val.size) - 1).toNat = sorted.val.size - 1 := by
          rw [usize_sub_one_toNat _ h_n_pos, h_ofNat]
        have h_half_le : (taken / (2 : usize)).toNat ≤ ((USize64.ofNat sorted.val.size) - 1).toNat := by
          rw [h_half_toNat, h_sub_1_toNat]; omega
        have h_sub_2_toNat : ((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat
                              = sorted.val.size - 1 - taken.toNat / 2 := by
          rw [usize_sub_toNat _ _ h_half_le, h_sub_1_toNat, h_half_toNat]
        have hj_o : ((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat
                      < sorted.val.size := by
          rw [h_sub_2_toNat]; omega
        have hj_o_nat : sorted.val.size - 1 - taken.toNat / 2 < sorted.val.size := by omega
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [build_strange_at_step_odd sorted taken acc hi_lt ht_odd hj_o h_acc] at hres
          have h_push_size :
              (push_one acc (sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o) h_acc).val.size
                = acc.val.size + 1 := by
            show (acc.val ++ #[sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o]).size
                  = acc.val.size + 1
            rw [Array.size_append]; rfl
          have ih_app := ih sorted (taken + 1) _ r target h_meas h_t1_le hres
          rw [h_t1] at ih_app
          have h_count_pushed :
              vec_count (push_one acc (sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o) h_acc).val target
                (acc.val.size + 1) =
              vec_count acc.val target acc.val.size +
                (if sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o = target then 1 else 0) := by
            show vec_count (acc.val ++ #[sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o]) target (acc.val.size + 1) = _
            exact vec_count_append_singleton acc.val (sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o) target
          rw [h_push_size, h_count_pushed] at ih_app
          -- For odd taken: (taken+1)/2 = taken/2 + 1 = (taken+2)/2
          -- so vec_count sorted ((taken+1+1)/2) = vec_count sorted ((taken+1)/2)
          have h_idx_succ : (taken.toNat + 1 + 1) / 2 = taken.toNat / 2 + 1 := by omega
          have h_idx_eq : (taken.toNat + 1) / 2 = taken.toNat / 2 + 1 := by omega
          -- And (n - (taken+1)/2) = (n - taken/2 - 1). Then vec_count sorted (n - taken/2) = (sorted[n-1-taken/2] = target ? 1 : 0) + vec_count sorted (n - taken/2 - 1)
          have h_n_taken1 : sorted.val.size - (taken.toNat + 1) / 2 = sorted.val.size - taken.toNat / 2 - 1 := by omega
          have h_succ_n_taken : sorted.val.size - taken.toNat / 2 = (sorted.val.size - taken.toNat / 2 - 1) + 1 := by omega
          have h_idx_lt : sorted.val.size - taken.toNat / 2 - 1 < sorted.val.size := by omega
          have h_vec_succ :
              vec_count sorted.val target (sorted.val.size - taken.toNat / 2 - 1 + 1) =
                (if sorted.val[sorted.val.size - taken.toNat / 2 - 1]'h_idx_lt = target then 1 else 0) +
                  vec_count sorted.val target (sorted.val.size - taken.toNat / 2 - 1) :=
            vec_count_succ sorted.val target (sorted.val.size - taken.toNat / 2 - 1) h_idx_lt
          -- The pushed value equals sorted[n - 1 - taken.toNat / 2] = sorted[n - taken.toNat/2 - 1]
          have h_val_eq :
              (if sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o = target then 1 else 0) =
              (if sorted.val[sorted.val.size - taken.toNat / 2 - 1]'h_idx_lt = target then 1 else 0) := by
            have h_combined : ((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat
                            = sorted.val.size - taken.toNat / 2 - 1 := by
              rw [h_sub_2_toNat]; omega
            have h_elem_eq :
                sorted.val[((USize64.ofNat sorted.val.size) - 1 - (taken / (2 : usize))).toNat]'hj_o
                  = sorted.val[sorted.val.size - taken.toNat / 2 - 1]'h_idx_lt :=
              array_get_idx_eq sorted.val
                ((USize64.ofNat sorted.val.size - 1 - (taken / (2 : usize))).toNat)
                (sorted.val.size - taken.toNat / 2 - 1) hj_o h_idx_lt h_combined
            rw [h_elem_eq]
          rw [h_idx_succ, h_n_taken1] at ih_app
          rw [h_idx_eq]
          rw [show sorted.val.size - taken.toNat / 2 = (sorted.val.size - taken.toNat / 2 - 1) + 1 from h_succ_n_taken,
              h_vec_succ]
          rw [h_val_eq] at ih_app
          omega
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [build_strange_at_step_odd_size_fail sorted taken acc hi_lt ht_odd hj_o h_big] at hres
          cases hres

/-! ## Six obligation theorems — proofs deferred. -/

/-- Anchor: empty input yields a successful empty output. -/
theorem strange_sort_list_empty_input_yields_empty_output
    (l : RustSlice i64) (hempty : l.val.size = 0) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_069_strange_sort_list.strange_sort_list l = RustM.ok v ∧
      v.val.size = 0 := by
  refine ⟨⟨#[], by decide⟩, ?_, rfl⟩
  unfold clever_069_strange_sort_list.strange_sort_list
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new]
  simp only [RustM_ok_bind]
  have h_zero_le : l.val.size ≤ (0 : usize).toNat := by
    rw [usize_zero_toNat]; omega
  have h_sort_oob :
      clever_069_strange_sort_list.sort_at l (0 : usize)
        ⟨(List.nil).toArray, by grind⟩
      = RustM.ok ⟨(List.nil).toArray, by grind⟩ :=
    sort_at_oob l (0 : usize) ⟨(List.nil).toArray, by grind⟩ h_zero_le
  rw [h_sort_oob]
  simp only [RustM_ok_bind]
  have h_deref :
      (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec i64 alloc.alloc.Global)
        ⟨(List.nil).toArray, by grind⟩ :
        RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
        RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_deref]
  simp only [RustM_ok_bind]
  -- Goal: build_strange_at deref(empty sorted) 0 #[] = ok #[]
  have h_sorted_size : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
  have h_zero_le_s : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size ≤ (0 : usize).toNat := by
    rw [usize_zero_toNat, h_sorted_size]; omega
  exact build_strange_at_oob ⟨(List.nil).toArray, by grind⟩ (0 : usize)
      ⟨(List.nil).toArray, by grind⟩ h_zero_le_s

theorem strange_sort_list_length_preserved
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_069_strange_sort_list.strange_sort_list l = RustM.ok v) :
    v.val.size = l.val.size := by
  unfold clever_069_strange_sort_list.strange_sort_list at hres
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  generalize h_sort :
      clever_069_strange_sort_list.sort_at l (0 : usize) ⟨(List.nil).toArray, by grind⟩ = sa_res at hres
  cases sa_res with
  | none =>
    exfalso
    have hh : (do let sorted ← (none : RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                  let sorted_deref ← (core_models.ops.deref.Deref.deref
                    (alloc.vec.Vec i64 alloc.alloc.Global) sorted :
                    RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                  let acc0 ← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                              RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                  clever_069_strange_sort_list.build_strange_at sorted_deref (0 : usize) acc0)
              = RustM.ok v := hres
    cases hh
  | some sa_res' =>
    cases sa_res' with
    | error e =>
      exfalso
      have hh : (do let sorted ← (some (Except.error e) :
                                    RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                    let sorted_deref ← (core_models.ops.deref.Deref.deref
                      (alloc.vec.Vec i64 alloc.alloc.Global) sorted :
                      RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                    let acc0 ← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                                RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                    clever_069_strange_sort_list.build_strange_at sorted_deref (0 : usize) acc0)
                = RustM.ok v := hres
      cases hh
    | ok sorted =>
      simp only [RustM_ok_bind] at hres
      have h_deref :
          (core_models.ops.deref.Deref.deref
            (alloc.vec.Vec i64 alloc.alloc.Global) sorted : RustM _) = RustM.ok sorted := rfl
      rw [h_deref] at hres
      simp only [RustM_ok_bind] at hres
      -- hres : build_strange_at sorted 0 #[] = ok v
      -- Use sort_at_inv to relate sorted.size to l.size, then build_strange_at_size.
      have h_zero_toNat : (0 : usize).toNat = 0 := rfl
      have h_meas_s : l.val.size - (0 : usize).toNat ≤ l.val.size := by rw [h_zero_toNat]; omega
      have h_le_s : (0 : usize).toNat ≤ l.val.size := by rw [h_zero_toNat]; omega
      have h_sort_ok :
          clever_069_strange_sort_list.sort_at l (0 : usize) ⟨(List.nil).toArray, by grind⟩
            = RustM.ok sorted := h_sort
      have h_sort_size := (sort_at_inv l.val.size l (0 : usize)
        ⟨(List.nil).toArray, by grind⟩ sorted (0 : i64)
        h_meas_s h_le_s h_sort_ok).1
      have h_empty : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
      rw [h_empty, h_zero_toNat] at h_sort_size
      have h_meas_b : sorted.val.size - (0 : usize).toNat ≤ sorted.val.size := by rw [h_zero_toNat]; omega
      have h_le_b : (0 : usize).toNat ≤ sorted.val.size := by rw [h_zero_toNat]; omega
      have h_b_size := build_strange_at_size sorted.val.size sorted (0 : usize)
        ⟨(List.nil).toArray, by grind⟩ v h_meas_b h_le_b hres
      rw [h_empty, h_zero_toNat] at h_b_size
      omega

theorem strange_sort_list_multiset_preserved
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_069_strange_sort_list.strange_sort_list l = RustM.ok v)
    (target : i64) :
    vec_count v.val target v.val.size = vec_count l.val target l.val.size := by
  unfold clever_069_strange_sort_list.strange_sort_list at hres
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  generalize h_sort :
      clever_069_strange_sort_list.sort_at l (0 : usize) ⟨(List.nil).toArray, by grind⟩ = sa_res at hres
  cases sa_res with
  | none => exfalso; cases hres
  | some sa_res' =>
    cases sa_res' with
    | error e => exfalso; cases hres
    | ok sorted =>
      simp only [RustM_ok_bind] at hres
      have h_deref :
          (core_models.ops.deref.Deref.deref
            (alloc.vec.Vec i64 alloc.alloc.Global) sorted : RustM _) = RustM.ok sorted := rfl
      rw [h_deref] at hres
      simp only [RustM_ok_bind] at hres
      -- hres : build_strange_at sorted 0 #[] = ok v
      have h_zero_toNat : (0 : usize).toNat = 0 := rfl
      have h_meas_s : l.val.size - (0 : usize).toNat ≤ l.val.size := by rw [h_zero_toNat]; omega
      have h_le_s : (0 : usize).toNat ≤ l.val.size := by rw [h_zero_toNat]; omega
      have h_sort_ok :
          clever_069_strange_sort_list.sort_at l (0 : usize) ⟨(List.nil).toArray, by grind⟩
            = RustM.ok sorted := h_sort
      -- sort_at_inv: vec_count sorted target sorted.size + vec_count l target 0 = 0 + vec_count l target l.size
      have h_sort_inv := (sort_at_inv l.val.size l (0 : usize)
        ⟨(List.nil).toArray, by grind⟩ sorted target h_meas_s h_le_s h_sort_ok).2
      have h_empty_size : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
      rw [h_empty_size, h_zero_toNat] at h_sort_inv
      have h_empty_count : vec_count ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val target 0 = 0 := rfl
      rw [h_empty_count] at h_sort_inv
      have h_l_zero : vec_count l.val target 0 = 0 := rfl
      rw [h_l_zero] at h_sort_inv
      -- h_sort_inv : vec_count sorted target sorted.size + 0 = 0 + vec_count l target l.size
      have h_sort_count : vec_count sorted.val target sorted.val.size = vec_count l.val target l.val.size := by omega
      -- Now apply build_strange_at_count
      have h_meas_b : sorted.val.size - (0 : usize).toNat ≤ sorted.val.size := by rw [h_zero_toNat]; omega
      have h_le_b : (0 : usize).toNat ≤ sorted.val.size := by rw [h_zero_toNat]; omega
      have h_b_count := build_strange_at_count sorted.val.size sorted (0 : usize)
        ⟨(List.nil).toArray, by grind⟩ v target h_meas_b h_le_b hres
      -- At taken = 0: vec_count r r.size + vec_count sorted ((0+1)/2) = vec_count #[] 0 + vec_count sorted (n - 0/2)
      -- (0+1)/2 = 0, n - 0 = n
      have h_zero_div : (USize64.toNat (0 : usize) + 1) / 2 = 0 := by rw [h_zero_toNat]
      have h_zero_div2 : USize64.toNat (0 : usize) / 2 = 0 := by rw [h_zero_toNat]
      rw [h_zero_div, h_zero_div2, Nat.sub_zero] at h_b_count
      have h_empty_count2 : vec_count ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val target 0 = 0 := rfl
      have h_empty_size2 : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
      rw [h_empty_size2, h_empty_count2] at h_b_count
      have h_sorted_zero : vec_count sorted.val target 0 = 0 := rfl
      rw [h_sorted_zero] at h_b_count
      -- h_b_count : vec_count v target v.size + 0 = 0 + vec_count sorted target sorted.size
      omega

theorem strange_sort_list_even_indices_ascending
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_069_strange_sort_list.strange_sort_list l = RustM.ok v)
    (k : Nat) (hk : k + 2 < v.val.size) (heven : k % 2 = 0) :
    (v.val[k]'(Nat.lt_of_succ_lt (Nat.lt_of_succ_lt hk))).toInt ≤
      (v.val[k + 2]'hk).toInt := by
  unfold clever_069_strange_sort_list.strange_sort_list at hres
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  generalize h_sort :
      clever_069_strange_sort_list.sort_at l (0 : usize) ⟨(List.nil).toArray, by grind⟩ = sa_res at hres
  cases sa_res with
  | none => exfalso; cases hres
  | some sa_res' =>
    cases sa_res' with
    | error e => exfalso; cases hres
    | ok sorted =>
      simp only [RustM_ok_bind] at hres
      have h_deref :
          (core_models.ops.deref.Deref.deref
            (alloc.vec.Vec i64 alloc.alloc.Global) sorted : RustM _) = RustM.ok sorted := rfl
      rw [h_deref] at hres
      simp only [RustM_ok_bind] at hres
      have h_zero_toNat : (0 : usize).toNat = 0 := rfl
      have h_meas_s : l.val.size - (0 : usize).toNat ≤ l.val.size := by rw [h_zero_toNat]; omega
      have h_le_s : (0 : usize).toNat ≤ l.val.size := by rw [h_zero_toNat]; omega
      have h_sort_ok :
          clever_069_strange_sort_list.sort_at l (0 : usize) ⟨(List.nil).toArray, by grind⟩
            = RustM.ok sorted := h_sort
      have h_meas_b : sorted.val.size - (0 : usize).toNat ≤ sorted.val.size := by rw [h_zero_toNat]; omega
      have h_le_b : (0 : usize).toNat ≤ sorted.val.size := by rw [h_zero_toNat]; omega
      have h_empty_size : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
      have h_acc_eq_zero : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = (0 : usize).toNat := by
        rw [h_empty_size, h_zero_toNat]
      have h_b_size := build_strange_at_size sorted.val.size sorted (0 : usize)
        ⟨(List.nil).toArray, by grind⟩ v h_meas_b h_le_b hres
      rw [h_empty_size, h_zero_toNat] at h_b_size
      -- v.val.size = 0 + (sorted.val.size - 0) = sorted.val.size
      have h_v_eq_s : v.val.size = sorted.val.size := by omega
      have hk_lt_s : k + 2 < sorted.val.size := by rw [← h_v_eq_s]; exact hk
      have hk_l_s : k < sorted.val.size := by omega
      have hk2_l_s : k + 2 < sorted.val.size := hk_lt_s
      -- sortedness of sorted
      have h_empty_sorted : sorted_asc ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val :=
        sorted_asc_empty
      have h_sorted_sorted : sorted_asc sorted.val :=
        sort_at_sorted l.val.size l (0 : usize) ⟨(List.nil).toArray, by grind⟩
          sorted h_meas_s h_le_s h_sort_ok h_empty_sorted
      have hk_r : k < v.val.size := Nat.lt_of_succ_lt (Nat.lt_of_succ_lt hk)
      have hk_ge_zero : (0 : usize).toNat ≤ k := by rw [h_zero_toNat]; omega
      have hk_ge_zero2 : (0 : usize).toNat ≤ k + 2 := by rw [h_zero_toNat]; omega
      -- Apply build_strange_at_even_position
      obtain ⟨hj_k, h_val_k⟩ := build_strange_at_even_position sorted.val.size sorted (0 : usize)
        ⟨(List.nil).toArray, by grind⟩ v h_meas_b h_le_b h_acc_eq_zero hres
        k hk_r heven hk_ge_zero hk_l_s
      have h_k2_even : (k + 2) % 2 = 0 := by omega
      obtain ⟨hj_k2, h_val_k2⟩ := build_strange_at_even_position sorted.val.size sorted (0 : usize)
        ⟨(List.nil).toArray, by grind⟩ v h_meas_b h_le_b h_acc_eq_zero hres
        (k + 2) hk h_k2_even hk_ge_zero2 hk2_l_s
      -- (k+2) / 2 = k/2 + 1 (since k even)
      have h_idx_k2 : (k + 2) / 2 = k / 2 + 1 := by omega
      have hj_k2' : k / 2 + 1 < sorted.val.size := by rw [← h_idx_k2]; exact hj_k2
      have h_val_k2' : v.val[k + 2]'hk = sorted.val[k / 2 + 1]'hj_k2' := by
        rw [h_val_k2]
        exact array_get_idx_eq sorted.val ((k + 2) / 2) (k / 2 + 1) hj_k2 hj_k2' h_idx_k2
      rw [h_val_k, h_val_k2']
      exact h_sorted_sorted (k / 2) (k / 2 + 1) hj_k hj_k2' (Nat.le_succ _)

theorem strange_sort_list_odd_indices_descending
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_069_strange_sort_list.strange_sort_list l = RustM.ok v)
    (k : Nat) (hk : k + 2 < v.val.size) (hodd : k % 2 = 1) :
    (v.val[k + 2]'hk).toInt ≤
      (v.val[k]'(Nat.lt_of_succ_lt (Nat.lt_of_succ_lt hk))).toInt := by
  unfold clever_069_strange_sort_list.strange_sort_list at hres
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  generalize h_sort :
      clever_069_strange_sort_list.sort_at l (0 : usize) ⟨(List.nil).toArray, by grind⟩ = sa_res at hres
  cases sa_res with
  | none => exfalso; cases hres
  | some sa_res' =>
    cases sa_res' with
    | error e => exfalso; cases hres
    | ok sorted =>
      simp only [RustM_ok_bind] at hres
      have h_deref :
          (core_models.ops.deref.Deref.deref
            (alloc.vec.Vec i64 alloc.alloc.Global) sorted : RustM _) = RustM.ok sorted := rfl
      rw [h_deref] at hres
      simp only [RustM_ok_bind] at hres
      have h_zero_toNat : (0 : usize).toNat = 0 := rfl
      have h_meas_s : l.val.size - (0 : usize).toNat ≤ l.val.size := by rw [h_zero_toNat]; omega
      have h_le_s : (0 : usize).toNat ≤ l.val.size := by rw [h_zero_toNat]; omega
      have h_sort_ok :
          clever_069_strange_sort_list.sort_at l (0 : usize) ⟨(List.nil).toArray, by grind⟩
            = RustM.ok sorted := h_sort
      have h_meas_b : sorted.val.size - (0 : usize).toNat ≤ sorted.val.size := by rw [h_zero_toNat]; omega
      have h_le_b : (0 : usize).toNat ≤ sorted.val.size := by rw [h_zero_toNat]; omega
      have h_empty_size : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
      have h_acc_eq_zero : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = (0 : usize).toNat := by
        rw [h_empty_size, h_zero_toNat]
      have h_b_size := build_strange_at_size sorted.val.size sorted (0 : usize)
        ⟨(List.nil).toArray, by grind⟩ v h_meas_b h_le_b hres
      rw [h_empty_size, h_zero_toNat] at h_b_size
      have h_v_eq_s : v.val.size = sorted.val.size := by omega
      have hk_lt_s : k + 2 < sorted.val.size := by rw [← h_v_eq_s]; exact hk
      have hk_l_s : k < sorted.val.size := by omega
      have hk_r : k < v.val.size := Nat.lt_of_succ_lt (Nat.lt_of_succ_lt hk)
      have hk_ge_zero : (0 : usize).toNat ≤ k := by rw [h_zero_toNat]; omega
      have hk_ge_zero2 : (0 : usize).toNat ≤ k + 2 := by rw [h_zero_toNat]; omega
      have h_k2_odd : (k + 2) % 2 = 1 := by omega
      -- v[k] = sorted[n-1-k/2]
      obtain ⟨hj_k, h_val_k⟩ := build_strange_at_odd_position sorted.val.size sorted (0 : usize)
        ⟨(List.nil).toArray, by grind⟩ v h_meas_b h_le_b h_acc_eq_zero hres
        k hk_r hodd hk_ge_zero hk_l_s
      -- v[k+2] = sorted[n-1-(k+2)/2] = sorted[n-1-k/2-1]
      obtain ⟨hj_k2, h_val_k2⟩ := build_strange_at_odd_position sorted.val.size sorted (0 : usize)
        ⟨(List.nil).toArray, by grind⟩ v h_meas_b h_le_b h_acc_eq_zero hres
        (k + 2) hk h_k2_odd hk_ge_zero2 hk_lt_s
      have h_idx_k2 : (k + 2) / 2 = k / 2 + 1 := by omega
      have hj_k2' : sorted.val.size - 1 - (k / 2 + 1) < sorted.val.size := by omega
      have h_val_k2' : v.val[k + 2]'hk = sorted.val[sorted.val.size - 1 - (k / 2 + 1)]'hj_k2' := by
        rw [h_val_k2]
        exact array_get_idx_eq sorted.val (sorted.val.size - 1 - (k + 2) / 2) (sorted.val.size - 1 - (k / 2 + 1)) hj_k2 hj_k2'
          (by rw [h_idx_k2])
      rw [h_val_k, h_val_k2']
      -- sortedness: indices sorted.size - 1 - (k/2 + 1) ≤ sorted.size - 1 - k/2
      -- so sorted[sorted.size - 1 - (k/2+1)] ≤ sorted[sorted.size - 1 - k/2]
      have h_sorted_sorted : sorted_asc sorted.val :=
        sort_at_sorted l.val.size l (0 : usize) ⟨(List.nil).toArray, by grind⟩
          sorted h_meas_s h_le_s h_sort_ok sorted_asc_empty
      -- Show n - 1 - (k/2+1) ≤ n - 1 - k/2
      have h_idx_le : sorted.val.size - 1 - (k / 2 + 1) ≤ sorted.val.size - 1 - k / 2 := by omega
      exact h_sorted_sorted (sorted.val.size - 1 - (k / 2 + 1)) (sorted.val.size - 1 - k / 2)
        hj_k2' hj_k h_idx_le

theorem strange_sort_list_even_le_adjacent_odd
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_069_strange_sort_list.strange_sort_list l = RustM.ok v)
    (k : Nat) (hk : 2 * k + 1 < v.val.size) :
    (v.val[2 * k]'(Nat.lt_of_succ_lt hk)).toInt ≤
      (v.val[2 * k + 1]'hk).toInt := by
  unfold clever_069_strange_sort_list.strange_sort_list at hres
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  generalize h_sort :
      clever_069_strange_sort_list.sort_at l (0 : usize) ⟨(List.nil).toArray, by grind⟩ = sa_res at hres
  cases sa_res with
  | none => exfalso; cases hres
  | some sa_res' =>
    cases sa_res' with
    | error e => exfalso; cases hres
    | ok sorted =>
      simp only [RustM_ok_bind] at hres
      have h_deref :
          (core_models.ops.deref.Deref.deref
            (alloc.vec.Vec i64 alloc.alloc.Global) sorted : RustM _) = RustM.ok sorted := rfl
      rw [h_deref] at hres
      simp only [RustM_ok_bind] at hres
      have h_zero_toNat : (0 : usize).toNat = 0 := rfl
      have h_meas_s : l.val.size - (0 : usize).toNat ≤ l.val.size := by rw [h_zero_toNat]; omega
      have h_le_s : (0 : usize).toNat ≤ l.val.size := by rw [h_zero_toNat]; omega
      have h_sort_ok :
          clever_069_strange_sort_list.sort_at l (0 : usize) ⟨(List.nil).toArray, by grind⟩
            = RustM.ok sorted := h_sort
      have h_meas_b : sorted.val.size - (0 : usize).toNat ≤ sorted.val.size := by rw [h_zero_toNat]; omega
      have h_le_b : (0 : usize).toNat ≤ sorted.val.size := by rw [h_zero_toNat]; omega
      have h_empty_size : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
      have h_acc_eq_zero : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = (0 : usize).toNat := by
        rw [h_empty_size, h_zero_toNat]
      have h_b_size := build_strange_at_size sorted.val.size sorted (0 : usize)
        ⟨(List.nil).toArray, by grind⟩ v h_meas_b h_le_b hres
      rw [h_empty_size, h_zero_toNat] at h_b_size
      have h_v_eq_s : v.val.size = sorted.val.size := by omega
      have hk_lt_s : 2 * k + 1 < sorted.val.size := by rw [← h_v_eq_s]; exact hk
      have hk_e_lt_s : 2 * k < sorted.val.size := by omega
      have hk_e_r : 2 * k < v.val.size := Nat.lt_of_succ_lt hk
      have hk_o_r : 2 * k + 1 < v.val.size := hk
      have h_even_2k : (2 * k) % 2 = 0 := by omega
      have h_odd_2k1 : (2 * k + 1) % 2 = 1 := by omega
      have hk_ge_zero_e : (0 : usize).toNat ≤ 2 * k := by rw [h_zero_toNat]; omega
      have hk_ge_zero_o : (0 : usize).toNat ≤ 2 * k + 1 := by rw [h_zero_toNat]; omega
      -- v[2k] = sorted[(2k)/2] = sorted[k]
      obtain ⟨hj_e, h_val_e⟩ := build_strange_at_even_position sorted.val.size sorted (0 : usize)
        ⟨(List.nil).toArray, by grind⟩ v h_meas_b h_le_b h_acc_eq_zero hres
        (2 * k) hk_e_r h_even_2k hk_ge_zero_e hk_e_lt_s
      -- v[2k+1] = sorted[n - 1 - (2k+1)/2] = sorted[n - 1 - k]
      obtain ⟨hj_o, h_val_o⟩ := build_strange_at_odd_position sorted.val.size sorted (0 : usize)
        ⟨(List.nil).toArray, by grind⟩ v h_meas_b h_le_b h_acc_eq_zero hres
        (2 * k + 1) hk_o_r h_odd_2k1 hk_ge_zero_o hk_lt_s
      have h_idx_e : (2 * k) / 2 = k := by omega
      have h_idx_o : (2 * k + 1) / 2 = k := by omega
      have hj_e' : k < sorted.val.size := by rw [← h_idx_e]; exact hj_e
      have hj_o' : sorted.val.size - 1 - k < sorted.val.size := by omega
      have h_val_e' : v.val[2 * k]'(Nat.lt_of_succ_lt hk) = sorted.val[k]'hj_e' := by
        rw [h_val_e]
        exact array_get_idx_eq sorted.val ((2 * k) / 2) k hj_e hj_e' h_idx_e
      have h_val_o' : v.val[2 * k + 1]'hk = sorted.val[sorted.val.size - 1 - k]'hj_o' := by
        rw [h_val_o]
        exact array_get_idx_eq sorted.val (sorted.val.size - 1 - (2 * k + 1) / 2)
          (sorted.val.size - 1 - k) hj_o hj_o' (by rw [h_idx_o])
      rw [h_val_e', h_val_o']
      have h_sorted_sorted : sorted_asc sorted.val :=
        sort_at_sorted l.val.size l (0 : usize) ⟨(List.nil).toArray, by grind⟩
          sorted h_meas_s h_le_s h_sort_ok sorted_asc_empty
      have h_idx_le : k ≤ sorted.val.size - 1 - k := by omega
      exact h_sorted_sorted k (sorted.val.size - 1 - k) hj_e' hj_o' h_idx_le

end Clever_069_strange_sort_listObligations
