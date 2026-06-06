-- Companion obligations file for the `clever_087_sort_array` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

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

/-! ## Specification oracle for the multiset clause. -/

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
private def push_one (acc : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec u64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

/-- Push two elements. -/
private def push_two (acc : alloc.vec.Vec u64 alloc.alloc.Global) (x y : u64)
    (h : acc.val.size + 2 < USize64.size) :
    alloc.vec.Vec u64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x, y], by
    have h_size : (acc.val ++ #[x, y]).size = acc.val.size + 2 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

/-! ## `vec_count` append lemmas. -/

private theorem vec_count_succ (s : Array u64) (target : u64) (k : Nat) (hk : k < s.size) :
    vec_count s target (k + 1) =
      (if (s[k]'hk) = target then 1 else 0) + vec_count s target k := by
  show (if h : k < s.size then
          (if (s[k]'h) = target then 1 else 0) + vec_count s target k
        else vec_count s target k) = _
  rw [dif_pos hk]

private theorem vec_count_prefix (acc : Array u64) (y target : u64) :
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

private theorem vec_count_append_singleton (acc : Array u64) (y target : u64) :
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

private theorem vec_count_append_pair (acc : Array u64) (x y target : u64) :
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

/-! ## Sortedness predicates: empty + append lemmas. -/

private theorem sorted_asc_empty : sorted_asc #[] := by
  intro k₁ k₂ h₁ _ _
  have : (#[] : Array u64).size = 0 := rfl
  omega

private theorem sorted_asc_append_singleton (acc : Array u64) (y : u64)
    (h_acc : sorted_asc acc)
    (h_le : ∀ (k : Nat) (hk : k < acc.size), (acc[k]'hk).toNat ≤ y.toNat) :
    sorted_asc (acc ++ #[y]) := by
  intro k₁ k₂ h₁ h₂ hle12
  rw [Array.size_append] at h₁ h₂
  have h_one : (#[y] : Array u64).size = 1 := rfl
  by_cases h_k1_lt : k₁ < acc.size
  · by_cases h_k2_lt : k₂ < acc.size
    · rw [Array.getElem_append_left h_k1_lt, Array.getElem_append_left h_k2_lt]
      exact h_acc k₁ k₂ h_k1_lt h_k2_lt hle12
    · have h_k2_ge : acc.size ≤ k₂ := by omega
      rw [Array.getElem_append_left h_k1_lt]
      rw [Array.getElem_append_right h_k2_ge]
      have h_idx : k₂ - acc.size = 0 := by omega
      have h_zero : (0 : Nat) < (#[y] : Array u64).size := by rw [h_one]; omega
      rw [show ((#[y] : Array u64)[k₂ - acc.size]'(by rw [h_idx]; exact h_zero))
              = (#[y] : Array u64)[0]'h_zero from by simp [h_idx]]
      show (acc[k₁]'h_k1_lt).toNat ≤ y.toNat
      exact h_le k₁ h_k1_lt
  · have h_k1_ge : acc.size ≤ k₁ := by omega
    have h_k2_ge : acc.size ≤ k₂ := by omega
    rw [Array.getElem_append_right h_k1_ge, Array.getElem_append_right h_k2_ge]
    have h_k1_idx : k₁ - acc.size = 0 := by omega
    have h_k2_idx : k₂ - acc.size = 0 := by omega
    have h_zero : (0 : Nat) < (#[y] : Array u64).size := by rw [h_one]; omega
    rw [show ((#[y] : Array u64)[k₁ - acc.size]'(by rw [h_k1_idx]; exact h_zero))
            = (#[y] : Array u64)[0]'h_zero from by simp [h_k1_idx]]
    rw [show ((#[y] : Array u64)[k₂ - acc.size]'(by rw [h_k2_idx]; exact h_zero))
            = (#[y] : Array u64)[0]'h_zero from by simp [h_k2_idx]]
    exact Nat.le_refl _

private theorem sorted_asc_append_pair (acc : Array u64) (a b : u64)
    (h_acc : sorted_asc acc)
    (h_le_a : ∀ (k : Nat) (hk : k < acc.size), (acc[k]'hk).toNat ≤ a.toNat)
    (h_le_ab : a.toNat ≤ b.toNat) :
    sorted_asc (acc ++ #[a, b]) := by
  intro k₁ k₂ h₁ h₂ hle12
  rw [Array.size_append] at h₁ h₂
  have h_two : (#[a, b] : Array u64).size = 2 := rfl
  by_cases h_k1_lt : k₁ < acc.size
  · by_cases h_k2_lt : k₂ < acc.size
    · rw [Array.getElem_append_left h_k1_lt, Array.getElem_append_left h_k2_lt]
      exact h_acc k₁ k₂ h_k1_lt h_k2_lt hle12
    · have h_k2_ge : acc.size ≤ k₂ := by omega
      rw [Array.getElem_append_left h_k1_lt, Array.getElem_append_right h_k2_ge]
      have h_acc_k1 := h_le_a k₁ h_k1_lt
      by_cases h_k2_sub_eq : k₂ - acc.size = 0
      · have h_zero : (0 : Nat) < (#[a, b] : Array u64).size := by rw [h_two]; omega
        rw [show ((#[a, b] : Array u64)[k₂ - acc.size]'(by rw [h_k2_sub_eq]; exact h_zero))
                = (#[a, b] : Array u64)[0]'h_zero from by simp [h_k2_sub_eq]]
        show (acc[k₁]'h_k1_lt).toNat ≤ a.toNat
        exact h_acc_k1
      · have h_k2_sub_eq1 : k₂ - acc.size = 1 := by omega
        have h_one_lt : (1 : Nat) < (#[a, b] : Array u64).size := by rw [h_two]; omega
        rw [show ((#[a, b] : Array u64)[k₂ - acc.size]'(by rw [h_k2_sub_eq1]; exact h_one_lt))
                = (#[a, b] : Array u64)[1]'h_one_lt from by simp [h_k2_sub_eq1]]
        show (acc[k₁]'h_k1_lt).toNat ≤ b.toNat
        omega
  · have h_k1_ge : acc.size ≤ k₁ := by omega
    have h_k2_ge : acc.size ≤ k₂ := by omega
    rw [Array.getElem_append_right h_k1_ge, Array.getElem_append_right h_k2_ge]
    by_cases h_k1_eq : k₁ - acc.size = 0
    · have h_zero : (0 : Nat) < (#[a, b] : Array u64).size := by rw [h_two]; omega
      rw [show ((#[a, b] : Array u64)[k₁ - acc.size]'(by rw [h_k1_eq]; exact h_zero))
              = (#[a, b] : Array u64)[0]'h_zero from by simp [h_k1_eq]]
      by_cases h_k2_eq : k₂ - acc.size = 0
      · rw [show ((#[a, b] : Array u64)[k₂ - acc.size]'(by rw [h_k2_eq]; exact h_zero))
                = (#[a, b] : Array u64)[0]'h_zero from by simp [h_k2_eq]]
        show a.toNat ≤ a.toNat
        exact Nat.le_refl _
      · have h_k2_eq1 : k₂ - acc.size = 1 := by omega
        have h_one_lt : (1 : Nat) < (#[a, b] : Array u64).size := by rw [h_two]; omega
        rw [show ((#[a, b] : Array u64)[k₂ - acc.size]'(by rw [h_k2_eq1]; exact h_one_lt))
                = (#[a, b] : Array u64)[1]'h_one_lt from by simp [h_k2_eq1]]
        show a.toNat ≤ b.toNat
        exact h_le_ab
    · have h_k1_eq1 : k₁ - acc.size = 1 := by omega
      have h_k2_eq1 : k₂ - acc.size = 1 := by omega
      have h_one_lt : (1 : Nat) < (#[a, b] : Array u64).size := by rw [h_two]; omega
      rw [show ((#[a, b] : Array u64)[k₁ - acc.size]'(by rw [h_k1_eq1]; exact h_one_lt))
              = (#[a, b] : Array u64)[1]'h_one_lt from by simp [h_k1_eq1]]
      rw [show ((#[a, b] : Array u64)[k₂ - acc.size]'(by rw [h_k2_eq1]; exact h_one_lt))
              = (#[a, b] : Array u64)[1]'h_one_lt from by simp [h_k2_eq1]]
      show b.toNat ≤ b.toNat
      exact Nat.le_refl _

/-! ## OOB / step / fail lemmas for `insert_asc_at`. -/

private theorem insert_asc_at_oob_inserted (v : RustSlice u64) (x : u64)
    (i : usize) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat) :
    clever_087_sort_array.insert_asc_at v x i true acc = RustM.ok acc := by
  unfold clever_087_sort_array.insert_asc_at
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat v.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]; rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, ↓reduceIte]
  rfl

private theorem insert_asc_at_oob_not_inserted (v : RustSlice u64) (x : u64)
    (i : usize) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_087_sort_array.insert_asc_at v x i false acc =
      RustM.ok (push_one acc x h_acc) := by
  unfold clever_087_sort_array.insert_asc_at
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat v.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]; rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  have h_app_size :
      acc.val.size + (#[x] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  have h_extend :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[x], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.ok (push_one acc x h_acc) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, ↓reduceIte,
             Bool.false_eq_true]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[x] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[x], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend]
  rfl

private theorem insert_asc_at_oob_not_inserted_fail (v : RustSlice u64) (x : u64)
    (i : usize) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_087_sort_array.insert_asc_at v x i false acc
      = RustM.fail .maximumSizeExceeded := by
  unfold clever_087_sort_array.insert_asc_at
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat v.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]; rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  have h_app_size_neg :
      ¬ acc.val.size + (#[x] : Array u64).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[x], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, ↓reduceIte,
             Bool.false_eq_true]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[x] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[x], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

private theorem insert_asc_at_step_insert (v : RustSlice u64) (x : u64) (i : usize)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_vi : (v.val[i.toNat]'hi).toNat ≥ x.toNat)
    (h_acc : acc.val.size + 2 < USize64.size) :
    clever_087_sort_array.insert_asc_at v x i false acc =
      clever_087_sort_array.insert_asc_at v x (i + 1) true
        (push_two acc x (v.val[i.toNat]'hi) h_acc) := by
  conv => lhs; unfold clever_087_sort_array.insert_asc_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM u64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_ge_true : (decide ((v.val[i.toNat]'hi) ≥ x)) = true := by
    rw [decide_eq_true_iff]
    rw [show ((v.val[i.toNat]'hi) ≥ x) = (x ≤ (v.val[i.toNat]'hi)) from rfl]
    rw [UInt64.le_iff_toNat_le]
    exact h_vi
  have h_add : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := usize_add_one_ok i h_no_ov_i
  have h_app_size :
      acc.val.size + (#[x, v.val[i.toNat]'hi] : Array u64).size < USize64.size := by
    show acc.val.size + 2 < USize64.size; exact h_acc
  have h_extend :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[x, v.val[i.toNat]'hi], two_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
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
              (RustArray.ofVec #v[x, v.val[i.toNat]'hi] : RustArray u64 2)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[x, v.val[i.toNat]'hi], two_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend]
  simp only [RustM_ok_bind]
  rw [h_add]
  simp only [RustM_ok_bind]

private theorem insert_asc_at_step_insert_fail (v : RustSlice u64) (x : u64) (i : usize)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_vi : (v.val[i.toNat]'hi).toNat ≥ x.toNat)
    (h_big : USize64.size ≤ acc.val.size + 2) :
    clever_087_sort_array.insert_asc_at v x i false acc = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_087_sort_array.insert_asc_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM u64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_ge_true : (decide ((v.val[i.toNat]'hi) ≥ x)) = true := by
    rw [decide_eq_true_iff]
    rw [show ((v.val[i.toNat]'hi) ≥ x) = (x ≤ (v.val[i.toNat]'hi)) from rfl]
    rw [UInt64.le_iff_toNat_le]
    exact h_vi
  have h_app_size_neg :
      ¬ acc.val.size + (#[x, v.val[i.toNat]'hi] : Array u64).size < USize64.size := by
    show ¬ acc.val.size + 2 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[x, v.val[i.toNat]'hi], two_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
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
              (RustArray.ofVec #v[x, v.val[i.toNat]'hi] : RustArray u64 2)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[x, v.val[i.toNat]'hi], two_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

private theorem insert_asc_at_step_pass (v : RustSlice u64) (x : u64) (i : usize)
    (inserted : Bool) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_skip : inserted = true ∨ (v.val[i.toNat]'hi).toNat < x.toNat)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_087_sort_array.insert_asc_at v x i inserted acc =
      clever_087_sort_array.insert_asc_at v x (i + 1) inserted
        (push_one acc (v.val[i.toNat]'hi) h_acc) := by
  conv => lhs; unfold clever_087_sort_array.insert_asc_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM u64) = RustM.ok (v.val[i.toNat]'hi) := by
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
        rw [UInt64.le_iff_toNat_le]
        omega
      rw [decide_eq_false h_not_ge]
      exact Bool.and_false _
  have h_add : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := usize_add_one_ok i h_no_ov_i
  have h_app_size :
      acc.val.size + (#[v.val[i.toNat]'hi] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  have h_extend :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[v.val[i.toNat]'hi], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
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
              (RustArray.ofVec #v[v.val[i.toNat]'hi] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[v.val[i.toNat]'hi], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend]
  simp only [RustM_ok_bind]
  rw [h_add]
  simp only [RustM_ok_bind]

private theorem insert_asc_at_step_pass_fail (v : RustSlice u64) (x : u64) (i : usize)
    (inserted : Bool) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_skip : inserted = true ∨ (v.val[i.toNat]'hi).toNat < x.toNat)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_087_sort_array.insert_asc_at v x i inserted acc = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_087_sort_array.insert_asc_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM u64) = RustM.ok (v.val[i.toNat]'hi) := by
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
        rw [UInt64.le_iff_toNat_le]
        omega
      rw [decide_eq_false h_not_ge]
      exact Bool.and_false _
  have h_app_size_neg :
      ¬ acc.val.size + (#[v.val[i.toNat]'hi] : Array u64).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[v.val[i.toNat]'hi], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
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
              (RustArray.ofVec #v[v.val[i.toNat]'hi] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[v.val[i.toNat]'hi], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

/-! ## Invariant for `insert_asc_at`: size and vec_count. -/

private theorem insert_asc_at_inv :
    ∀ (n : Nat) (v : RustSlice u64) (x : u64) (i : usize) (inserted : Bool)
      (acc : alloc.vec.Vec u64 alloc.alloc.Global)
      (r : alloc.vec.Vec u64 alloc.alloc.Global) (target : u64),
      v.val.size - i.toNat ≤ n →
      i.toNat ≤ v.val.size →
      clever_087_sort_array.insert_asc_at v x i inserted acc = RustM.ok r →
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
      rw [insert_asc_at_oob_inserted v x i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      refine ⟨?_, ?_⟩
      · simp [hi_eq]
      · rw [hi_eq]; simp
    | false =>
      by_cases h_acc : acc.val.size + 1 < USize64.size
      · rw [insert_asc_at_oob_not_inserted v x i acc hi_ge h_acc] at hres
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
        rw [insert_asc_at_oob_not_inserted_fail v x i acc hi_ge h_big] at hres
        cases hres
  | succ n ih =>
    intro v x i inserted acc r target hm hi_le hres
    by_cases hi_ge : v.val.size ≤ i.toNat
    · have hi_eq : i.toNat = v.val.size := by omega
      cases inserted with
      | true =>
        rw [insert_asc_at_oob_inserted v x i acc hi_ge] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        refine ⟨?_, ?_⟩
        · simp [hi_eq]
        · rw [hi_eq]; simp
      | false =>
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [insert_asc_at_oob_not_inserted v x i acc hi_ge h_acc] at hres
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
          rw [insert_asc_at_oob_not_inserted_fail v x i acc hi_ge h_big] at hres
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
        · rw [insert_asc_at_step_pass v x i true acc hi_lt (Or.inl rfl) h_acc] at hres
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
          rw [insert_asc_at_step_pass_fail v x i true acc hi_lt (Or.inl rfl) h_big] at hres
          cases hres
      | false =>
        by_cases h_vi : (v.val[i.toNat]'hi_lt).toNat ≥ x.toNat
        · by_cases h_acc : acc.val.size + 2 < USize64.size
          · rw [insert_asc_at_step_insert v x i acc hi_lt h_vi h_acc] at hres
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
            rw [insert_asc_at_step_insert_fail v x i acc hi_lt h_vi h_big] at hres
            cases hres
        · have h_lt : (v.val[i.toNat]'hi_lt).toNat < x.toNat := by omega
          by_cases h_acc : acc.val.size + 1 < USize64.size
          · rw [insert_asc_at_step_pass v x i false acc hi_lt (Or.inr h_lt) h_acc] at hres
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
            rw [insert_asc_at_step_pass_fail v x i false acc hi_lt (Or.inr h_lt) h_big] at hres
            cases hres

/-- Specialization: insert_asc v x has size v.size + 1, vec_count adds 1 if x = target. -/
private theorem insert_asc_inv (v : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (r : alloc.vec.Vec u64 alloc.alloc.Global) (target : u64)
    (hres : clever_087_sort_array.insert_asc v x = RustM.ok r) :
    r.val.size = v.val.size + 1 ∧
    vec_count r.val target r.val.size =
      vec_count v.val target v.val.size + (if x = target then 1 else 0) := by
  unfold clever_087_sort_array.insert_asc at hres
  have h_deref :
      (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u64 alloc.alloc.Global) v : RustM _) = RustM.ok v := rfl
  have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_deref, h_new] at hres
  simp only [RustM_ok_bind] at hres
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_meas : v.val.size - (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  have h_le : (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  have inv := insert_asc_at_inv v.val.size v x (0 : usize) false
    ⟨(List.nil).toArray, by grind⟩ r target h_meas h_le hres
  obtain ⟨h_size_eq, h_count_eq⟩ := inv
  have h_empty_size : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size = 0 := rfl
  rw [h_empty_size, h_zero_toNat] at h_size_eq
  rw [h_empty_size, h_zero_toNat] at h_count_eq
  have h_empty_count : vec_count ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val target 0 = 0 := rfl
  refine ⟨?_, ?_⟩
  · rw [h_size_eq]; simp
  · rw [h_empty_count] at h_count_eq
    have h_total_zero : vec_count v.val target 0 = 0 := rfl
    rw [h_total_zero] at h_count_eq
    simp at h_count_eq
    omega

/-! ## `insert_asc_at` produces sorted output. -/

private theorem insert_asc_at_sorted (v : RustSlice u64) (x : u64)
    (h_v_sorted : sorted_asc v.val) :
    ∀ (n : Nat) (i : usize) (inserted : Bool)
      (acc : alloc.vec.Vec u64 alloc.alloc.Global)
      (r : alloc.vec.Vec u64 alloc.alloc.Global),
      v.val.size - i.toNat ≤ n →
      i.toNat ≤ v.val.size →
      clever_087_sort_array.insert_asc_at v x i inserted acc = RustM.ok r →
      sorted_asc acc.val →
      (∀ (k : Nat) (hk : k < acc.val.size) (hi_lt : i.toNat < v.val.size),
          (acc.val[k]'hk).toNat ≤ (v.val[i.toNat]'hi_lt).toNat) →
      (inserted = false →
          ∀ (k : Nat) (hk : k < acc.val.size), (acc.val[k]'hk).toNat ≤ x.toNat) →
      sorted_asc r.val := by
  intro n
  induction n with
  | zero =>
    intro i inserted acc r hm hi_le hres h_acc_sorted h_acc_le_vi h_acc_le_x
    have hi_ge : v.val.size ≤ i.toNat := by omega
    cases inserted with
    | true =>
      rw [insert_asc_at_oob_inserted v x i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      exact h_acc_sorted
    | false =>
      by_cases h_acc : acc.val.size + 1 < USize64.size
      · rw [insert_asc_at_oob_not_inserted v x i acc hi_ge h_acc] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        show sorted_asc (acc.val ++ #[x])
        apply sorted_asc_append_singleton acc.val x h_acc_sorted
        exact h_acc_le_x rfl
      · exfalso
        have h_big : USize64.size ≤ acc.val.size + 1 := by omega
        rw [insert_asc_at_oob_not_inserted_fail v x i acc hi_ge h_big] at hres
        cases hres
  | succ n ih =>
    intro i inserted acc r hm hi_le hres h_acc_sorted h_acc_le_vi h_acc_le_x
    by_cases hi_ge : v.val.size ≤ i.toNat
    · cases inserted with
      | true =>
        rw [insert_asc_at_oob_inserted v x i acc hi_ge] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        exact h_acc_sorted
      | false =>
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [insert_asc_at_oob_not_inserted v x i acc hi_ge h_acc] at hres
          injection hres with h_eq
          injection h_eq with h_eq'
          subst h_eq'
          show sorted_asc (acc.val ++ #[x])
          apply sorted_asc_append_singleton acc.val x h_acc_sorted
          exact h_acc_le_x rfl
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_asc_at_oob_not_inserted_fail v x i acc hi_ge h_big] at hres
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
        · rw [insert_asc_at_step_pass v x i true acc hi_lt (Or.inl rfl) h_acc] at hres
          have h_new_sorted : sorted_asc (acc.val ++ #[v.val[i.toNat]'hi_lt]) := by
            apply sorted_asc_append_singleton acc.val (v.val[i.toNat]'hi_lt) h_acc_sorted
            intro k hk
            exact h_acc_le_vi k hk hi_lt
          have h_new_le_vi :
              ∀ (k : Nat) (hk : k < (acc.val ++ #[v.val[i.toNat]'hi_lt]).size)
                (hi_i1 : (i + 1).toNat < v.val.size),
                ((acc.val ++ #[v.val[i.toNat]'hi_lt])[k]'hk).toNat
                  ≤ (v.val[(i + 1).toNat]'hi_i1).toNat := by
            intro k hk hi_i1
            rw [Array.size_append] at hk
            have h_one : (#[v.val[i.toNat]'hi_lt] : Array u64).size = 1 := rfl
            by_cases h_k_lt : k < acc.val.size
            · rw [Array.getElem_append_left h_k_lt]
              have h_acc_k := h_acc_le_vi k h_k_lt hi_lt
              have h_v_step : (v.val[i.toNat]'hi_lt).toNat ≤ (v.val[(i + 1).toNat]'hi_i1).toNat := by
                have h_le : i.toNat ≤ (i + 1).toNat := by rw [h_i1]; omega
                exact h_v_sorted i.toNat (i + 1).toNat hi_lt hi_i1 h_le
              omega
            · have h_k_ge : acc.val.size ≤ k := by omega
              rw [Array.getElem_append_right h_k_ge]
              have h_idx : k - acc.val.size = 0 := by omega
              have h_zero_lt : (0 : Nat) < (#[v.val[i.toNat]'hi_lt] : Array u64).size := by
                rw [h_one]; omega
              rw [show ((#[v.val[i.toNat]'hi_lt] : Array u64)[k - acc.val.size]'(by rw [h_idx]; exact h_zero_lt))
                      = (#[v.val[i.toNat]'hi_lt] : Array u64)[0]'h_zero_lt from by simp [h_idx]]
              show (v.val[i.toNat]'hi_lt).toNat ≤ (v.val[(i + 1).toNat]'hi_i1).toNat
              have h_le : i.toNat ≤ (i + 1).toNat := by rw [h_i1]; omega
              exact h_v_sorted i.toNat (i + 1).toNat hi_lt hi_i1 h_le
          exact ih (i + 1) true _ r h_meas h_i1_le hres h_new_sorted h_new_le_vi
            (fun h => by cases h)
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_asc_at_step_pass_fail v x i true acc hi_lt (Or.inl rfl) h_big] at hres
          cases hres
      | false =>
        by_cases h_vi_ge : (v.val[i.toNat]'hi_lt).toNat ≥ x.toNat
        · by_cases h_acc : acc.val.size + 2 < USize64.size
          · rw [insert_asc_at_step_insert v x i acc hi_lt h_vi_ge h_acc] at hres
            have h_new_sorted : sorted_asc (acc.val ++ #[x, v.val[i.toNat]'hi_lt]) := by
              apply sorted_asc_append_pair acc.val x (v.val[i.toNat]'hi_lt) h_acc_sorted
              · intro k hk; exact h_acc_le_x rfl k hk
              · exact h_vi_ge
            have h_new_le_vi :
                ∀ (k : Nat) (hk : k < (acc.val ++ #[x, v.val[i.toNat]'hi_lt]).size)
                  (hi_i1 : (i + 1).toNat < v.val.size),
                  ((acc.val ++ #[x, v.val[i.toNat]'hi_lt])[k]'hk).toNat
                    ≤ (v.val[(i + 1).toNat]'hi_i1).toNat := by
              intro k hk hi_i1
              rw [Array.size_append] at hk
              have h_two : (#[x, v.val[i.toNat]'hi_lt] : Array u64).size = 2 := rfl
              have h_v_step : (v.val[i.toNat]'hi_lt).toNat ≤ (v.val[(i + 1).toNat]'hi_i1).toNat := by
                have h_le : i.toNat ≤ (i + 1).toNat := by rw [h_i1]; omega
                exact h_v_sorted i.toNat (i + 1).toNat hi_lt hi_i1 h_le
              by_cases h_k_lt : k < acc.val.size
              · rw [Array.getElem_append_left h_k_lt]
                have h_acc_k := h_acc_le_vi k h_k_lt hi_lt
                omega
              · have h_k_ge : acc.val.size ≤ k := by omega
                rw [Array.getElem_append_right h_k_ge]
                by_cases h_k_eq0 : k - acc.val.size = 0
                · have h_zero_lt : (0 : Nat) < (#[x, v.val[i.toNat]'hi_lt] : Array u64).size := by
                    rw [h_two]; omega
                  rw [show ((#[x, v.val[i.toNat]'hi_lt] : Array u64)[k - acc.val.size]'(by rw [h_k_eq0]; exact h_zero_lt))
                          = (#[x, v.val[i.toNat]'hi_lt] : Array u64)[0]'h_zero_lt from by simp [h_k_eq0]]
                  show x.toNat ≤ (v.val[(i + 1).toNat]'hi_i1).toNat
                  omega
                · have h_k_eq1 : k - acc.val.size = 1 := by omega
                  have h_one_lt : (1 : Nat) < (#[x, v.val[i.toNat]'hi_lt] : Array u64).size := by
                    rw [h_two]; omega
                  rw [show ((#[x, v.val[i.toNat]'hi_lt] : Array u64)[k - acc.val.size]'(by rw [h_k_eq1]; exact h_one_lt))
                          = (#[x, v.val[i.toNat]'hi_lt] : Array u64)[1]'h_one_lt from by simp [h_k_eq1]]
                  show (v.val[i.toNat]'hi_lt).toNat ≤ (v.val[(i + 1).toNat]'hi_i1).toNat
                  exact h_v_step
            exact ih (i + 1) true _ r h_meas h_i1_le hres h_new_sorted h_new_le_vi
              (fun h => by cases h)
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 2 := by omega
            rw [insert_asc_at_step_insert_fail v x i acc hi_lt h_vi_ge h_big] at hres
            cases hres
        · have h_lt : (v.val[i.toNat]'hi_lt).toNat < x.toNat := by omega
          by_cases h_acc : acc.val.size + 1 < USize64.size
          · rw [insert_asc_at_step_pass v x i false acc hi_lt (Or.inr h_lt) h_acc] at hres
            have h_new_sorted : sorted_asc (acc.val ++ #[v.val[i.toNat]'hi_lt]) := by
              apply sorted_asc_append_singleton acc.val (v.val[i.toNat]'hi_lt) h_acc_sorted
              intro k hk
              exact h_acc_le_vi k hk hi_lt
            have h_new_le_vi :
                ∀ (k : Nat) (hk : k < (acc.val ++ #[v.val[i.toNat]'hi_lt]).size)
                  (hi_i1 : (i + 1).toNat < v.val.size),
                  ((acc.val ++ #[v.val[i.toNat]'hi_lt])[k]'hk).toNat
                    ≤ (v.val[(i + 1).toNat]'hi_i1).toNat := by
              intro k hk hi_i1
              rw [Array.size_append] at hk
              have h_one : (#[v.val[i.toNat]'hi_lt] : Array u64).size = 1 := rfl
              have h_v_step : (v.val[i.toNat]'hi_lt).toNat ≤ (v.val[(i + 1).toNat]'hi_i1).toNat := by
                have h_le : i.toNat ≤ (i + 1).toNat := by rw [h_i1]; omega
                exact h_v_sorted i.toNat (i + 1).toNat hi_lt hi_i1 h_le
              by_cases h_k_lt : k < acc.val.size
              · rw [Array.getElem_append_left h_k_lt]
                have h_acc_k := h_acc_le_vi k h_k_lt hi_lt
                omega
              · have h_k_ge : acc.val.size ≤ k := by omega
                rw [Array.getElem_append_right h_k_ge]
                have h_idx : k - acc.val.size = 0 := by omega
                have h_zero_lt : (0 : Nat) < (#[v.val[i.toNat]'hi_lt] : Array u64).size := by
                  rw [h_one]; omega
                rw [show ((#[v.val[i.toNat]'hi_lt] : Array u64)[k - acc.val.size]'(by rw [h_idx]; exact h_zero_lt))
                        = (#[v.val[i.toNat]'hi_lt] : Array u64)[0]'h_zero_lt from by simp [h_idx]]
                exact h_v_step
            have h_new_le_x :
                false = false → ∀ (k : Nat) (hk : k < (acc.val ++ #[v.val[i.toNat]'hi_lt]).size),
                  ((acc.val ++ #[v.val[i.toNat]'hi_lt])[k]'hk).toNat ≤ x.toNat := by
              intro _ k hk
              rw [Array.size_append] at hk
              have h_one : (#[v.val[i.toNat]'hi_lt] : Array u64).size = 1 := rfl
              by_cases h_k_lt : k < acc.val.size
              · rw [Array.getElem_append_left h_k_lt]
                exact h_acc_le_x rfl k h_k_lt
              · have h_k_ge : acc.val.size ≤ k := by omega
                rw [Array.getElem_append_right h_k_ge]
                have h_idx : k - acc.val.size = 0 := by omega
                have h_zero_lt : (0 : Nat) < (#[v.val[i.toNat]'hi_lt] : Array u64).size := by
                  rw [h_one]; omega
                rw [show ((#[v.val[i.toNat]'hi_lt] : Array u64)[k - acc.val.size]'(by rw [h_idx]; exact h_zero_lt))
                        = (#[v.val[i.toNat]'hi_lt] : Array u64)[0]'h_zero_lt from by simp [h_idx]]
                show (v.val[i.toNat]'hi_lt).toNat ≤ x.toNat
                omega
            exact ih (i + 1) false _ r h_meas h_i1_le hres h_new_sorted h_new_le_vi h_new_le_x
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 1 := by omega
            rw [insert_asc_at_step_pass_fail v x i false acc hi_lt (Or.inr h_lt) h_big] at hres
            cases hres

private theorem insert_asc_sorted (v : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (r : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_087_sort_array.insert_asc v x = RustM.ok r)
    (h_v_sorted : sorted_asc v.val) :
    sorted_asc r.val := by
  unfold clever_087_sort_array.insert_asc at hres
  have h_deref :
      (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u64 alloc.alloc.Global) v : RustM _) = RustM.ok v := rfl
  have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_deref, h_new] at hres
  simp only [RustM_ok_bind] at hres
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_meas : v.val.size - (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  have h_le : (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  have h_empty_sorted : sorted_asc ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val := by
    intro k₁ k₂ h₁ _ _
    have : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  have h_empty_le_vi :
      ∀ (k : Nat) (hk : k < ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size)
        (_ : (0 : usize).toNat < v.val.size),
      (((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val[k]'hk).toNat
        ≤ (v.val[(0 : usize).toNat]'(by assumption)).toNat := by
    intro k hk _
    have h_empty : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  have h_empty_le_x : false = false →
      ∀ (k : Nat) (hk : k < ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size),
      (((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val[k]'hk).toNat ≤ x.toNat := by
    intro _ k hk
    have h_empty : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  exact insert_asc_at_sorted v x h_v_sorted v.val.size (0 : usize) false
    ⟨(List.nil).toArray, by grind⟩ r h_meas h_le hres h_empty_sorted h_empty_le_vi h_empty_le_x

/-! ## `sort_at` OOB + step lemmas. -/

private theorem sort_at_oob (l : RustSlice u64) (i : usize)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : l.val.size ≤ i.toNat) :
    clever_087_sort_array.sort_at l i acc = RustM.ok acc := by
  unfold clever_087_sort_array.sort_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

private theorem sort_at_step (l : RustSlice u64) (i : usize)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : i.toNat < l.val.size) :
    clever_087_sort_array.sort_at l i acc =
      (do
        let acc' ← clever_087_sort_array.insert_asc acc (l.val[i.toNat]'hi)
        clever_087_sort_array.sort_at l (i + 1) acc') := by
  conv => lhs; unfold clever_087_sort_array.sort_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (l[i]_? : RustM u64) = RustM.ok (l.val[i.toNat]'hi) := by
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

/-- `sort_at` preserves size and multiset count. -/
private theorem sort_at_inv :
    ∀ (n : Nat) (l : RustSlice u64) (i : usize)
      (acc : alloc.vec.Vec u64 alloc.alloc.Global)
      (r : alloc.vec.Vec u64 alloc.alloc.Global) (target : u64),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      clever_087_sort_array.sort_at l i acc = RustM.ok r →
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
      generalize h_ins : clever_087_sort_array.insert_asc acc (l.val[i.toNat]'hi_lt) = ins_res at hres
      cases ins_res with
      | none =>
        exfalso
        have hh : (do let acc' ← (none : RustM (alloc.vec.Vec u64 alloc.alloc.Global));
                       clever_087_sort_array.sort_at l (i + 1) acc')
                  = RustM.ok r := hres
        cases hh
      | some res' =>
        cases res' with
        | error e =>
          exfalso
          have hh : (do let acc' ← (some (Except.error e) :
                                      RustM (alloc.vec.Vec u64 alloc.alloc.Global));
                         clever_087_sort_array.sort_at l (i + 1) acc')
                    = RustM.ok r := hres
          cases hh
        | ok acc' =>
          have h_ins_ok : clever_087_sort_array.insert_asc acc (l.val[i.toNat]'hi_lt) = RustM.ok acc' := h_ins
          simp only [RustM_ok_bind] at hres
          have h_ins_inv := insert_asc_inv acc (l.val[i.toNat]'hi_lt) acc' target h_ins_ok
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

/-- `sort_at` produces a sorted output. -/
private theorem sort_at_sorted :
    ∀ (n : Nat) (l : RustSlice u64)
      (i : usize) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
      (r : alloc.vec.Vec u64 alloc.alloc.Global),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      clever_087_sort_array.sort_at l i acc = RustM.ok r →
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
      generalize h_ins : clever_087_sort_array.insert_asc acc (l.val[i.toNat]'hi_lt) = ins_res at hres
      cases ins_res with
      | none =>
        exfalso
        have hh : (do let acc' ← (none : RustM (alloc.vec.Vec u64 alloc.alloc.Global));
                       clever_087_sort_array.sort_at l (i + 1) acc')
                  = RustM.ok r := hres
        cases hh
      | some res' =>
        cases res' with
        | error e =>
          exfalso
          have hh : (do let acc' ← (some (Except.error e) :
                                      RustM (alloc.vec.Vec u64 alloc.alloc.Global));
                         clever_087_sort_array.sort_at l (i + 1) acc')
                    = RustM.ok r := hres
          cases hh
        | ok acc' =>
          have h_ins_ok : clever_087_sort_array.insert_asc acc (l.val[i.toNat]'hi_lt) = RustM.ok acc' := h_ins
          simp only [RustM_ok_bind] at hres
          have h_acc'_sorted : sorted_asc acc'.val :=
            insert_asc_sorted acc (l.val[i.toNat]'hi_lt) acc' h_ins_ok h_acc_sorted
          exact ih l (i + 1) acc' r h_meas h_i1_le hres h_acc'_sorted

/-- Get-element congruence: if two indices are equal as Nats, the looked-up element is the same. -/
private theorem array_get_idx_eq {α : Type} (a : Array α) (i j : Nat)
    (hi : i < a.size) (hj : j < a.size) (h : i = j) :
    a[i]'hi = a[j]'hj := by
  subst h; rfl

/-! ## `reverse_at` OOB + step lemmas.

    `reverse_at s i acc` pushes `s[s.size - 1 - i]` to `acc` and recurses on `i + 1`. -/

private theorem reverse_at_oob (s : RustSlice u64) (i : usize)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : s.val.size ≤ i.toNat) :
    clever_087_sort_array.reverse_at s i acc = RustM.ok acc := by
  unfold clever_087_sort_array.reverse_at
  have h_ofNat : (USize64.ofNat s.val.size).toNat = s.val.size :=
    USize64.toNat_ofNat_of_lt' s.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat s.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- Step lemma for `reverse_at`. The index used is `(n - 1 - i)` via usize subtractions. -/
private theorem reverse_at_step (s : RustSlice u64) (i : usize)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : i.toNat < s.val.size)
    (hj : ((USize64.ofNat s.val.size) - 1 - i).toNat < s.val.size)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_087_sort_array.reverse_at s i acc =
      clever_087_sort_array.reverse_at s (i + 1)
        (push_one acc (s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj) h_acc) := by
  conv => lhs; unfold clever_087_sort_array.reverse_at
  have h_size_lt : s.val.size < USize64.size := s.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat s.val.size).toNat = s.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat s.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_n_pos : 0 < s.val.size := by omega
  have h_n_pos_us : (0 : Nat) < (USize64.ofNat s.val.size).toNat := by
    rw [h_ofNat]; exact h_n_pos
  have h_sub_1 : ((USize64.ofNat s.val.size) -? (1 : usize) : RustM usize)
                  = RustM.ok ((USize64.ofNat s.val.size) - 1) :=
    usize_sub_one_ok _ h_n_pos_us
  have h_sub_1_toNat : ((USize64.ofNat s.val.size) - 1).toNat = s.val.size - 1 := by
    rw [usize_sub_one_toNat _ h_n_pos_us, h_ofNat]
  have h_i_le : i.toNat ≤ ((USize64.ofNat s.val.size) - 1).toNat := by
    rw [h_sub_1_toNat]; omega
  have h_sub_2 : ((USize64.ofNat s.val.size) - 1 -? i : RustM usize)
                  = RustM.ok ((USize64.ofNat s.val.size) - 1 - i) :=
    usize_sub_ok _ _ h_i_le
  have h_idx : (s[((USize64.ofNat s.val.size) - 1 - i)]_? : RustM u64) =
                RustM.ok (s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj) := by
    show (if h : ((USize64.ofNat s.val.size) - 1 - i).toNat < s.val.size
              then pure (s.val[(USize64.ofNat s.val.size) - 1 - i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj)
    rw [dif_pos hj]; rfl
  have h_add : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
    usize_add_one_ok i h_no_ov_i
  have h_app_size :
      acc.val.size + (#[s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  have h_extend :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.ok (push_one acc (s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj) h_acc) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_sub_1, h_sub_2, h_idx]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend]
  simp only [RustM_ok_bind]
  rw [h_add]
  simp only [RustM_ok_bind]

private theorem reverse_at_step_size_fail (s : RustSlice u64) (i : usize)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : i.toNat < s.val.size)
    (hj : ((USize64.ofNat s.val.size) - 1 - i).toNat < s.val.size)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_087_sort_array.reverse_at s i acc = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_087_sort_array.reverse_at
  have h_size_lt : s.val.size < USize64.size := s.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat s.val.size).toNat = s.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat s.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_n_pos : 0 < s.val.size := by omega
  have h_n_pos_us : (0 : Nat) < (USize64.ofNat s.val.size).toNat := by
    rw [h_ofNat]; exact h_n_pos
  have h_sub_1 : ((USize64.ofNat s.val.size) -? (1 : usize) : RustM usize)
                  = RustM.ok ((USize64.ofNat s.val.size) - 1) :=
    usize_sub_one_ok _ h_n_pos_us
  have h_sub_1_toNat : ((USize64.ofNat s.val.size) - 1).toNat = s.val.size - 1 := by
    rw [usize_sub_one_toNat _ h_n_pos_us, h_ofNat]
  have h_i_le : i.toNat ≤ ((USize64.ofNat s.val.size) - 1).toNat := by
    rw [h_sub_1_toNat]; omega
  have h_sub_2 : ((USize64.ofNat s.val.size) - 1 -? i : RustM usize)
                  = RustM.ok ((USize64.ofNat s.val.size) - 1 - i) :=
    usize_sub_ok _ _ h_i_le
  have h_idx : (s[((USize64.ofNat s.val.size) - 1 - i)]_? : RustM u64) =
                RustM.ok (s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj) := by
    show (if h : ((USize64.ofNat s.val.size) - 1 - i).toNat < s.val.size
              then pure (s.val[(USize64.ofNat s.val.size) - 1 - i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj)
    rw [dif_pos hj]; rfl
  have h_app_size_neg :
      ¬ acc.val.size + (#[s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj] : Array u64).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_sub_1, h_sub_2, h_idx]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

/-! ## `reverse_at` size + positional + count invariants. -/

/-- `reverse_at s i acc`: size of result is acc.size + (s.size - i). -/
private theorem reverse_at_size :
    ∀ (n : Nat) (s : RustSlice u64) (i : usize)
      (acc : alloc.vec.Vec u64 alloc.alloc.Global)
      (r : alloc.vec.Vec u64 alloc.alloc.Global),
      s.val.size - i.toNat ≤ n →
      i.toNat ≤ s.val.size →
      clever_087_sort_array.reverse_at s i acc = RustM.ok r →
      r.val.size = acc.val.size + (s.val.size - i.toNat) := by
  intro n
  induction n with
  | zero =>
    intro s i acc r hm hi_le hres
    have hi_ge : s.val.size ≤ i.toNat := by omega
    have hi_eq : i.toNat = s.val.size := by omega
    rw [reverse_at_oob s i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    rw [hi_eq]; omega
  | succ n ih =>
    intro s i acc r hm hi_le hres
    by_cases hi_ge : s.val.size ≤ i.toNat
    · have hi_eq : i.toNat = s.val.size := by omega
      rw [reverse_at_oob s i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      rw [hi_eq]; omega
    · have hi_lt : i.toNat < s.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : s.val.size < USize64.size := s.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ s.val.size := by rw [h_i1]; omega
      have h_meas : s.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      have h_n_pos : 0 < s.val.size := by omega
      have h_ofNat : (USize64.ofNat s.val.size).toNat = s.val.size :=
        USize64.toNat_ofNat_of_lt' h_size_lt
      have h_n_pos_us : (0 : Nat) < (USize64.ofNat s.val.size).toNat := by
        rw [h_ofNat]; exact h_n_pos
      have h_sub_1_toNat : ((USize64.ofNat s.val.size) - 1).toNat = s.val.size - 1 := by
        rw [usize_sub_one_toNat _ h_n_pos_us, h_ofNat]
      have h_i_le : i.toNat ≤ ((USize64.ofNat s.val.size) - 1).toNat := by
        rw [h_sub_1_toNat]; omega
      have h_sub_2_toNat : ((USize64.ofNat s.val.size) - 1 - i).toNat = s.val.size - 1 - i.toNat := by
        rw [usize_sub_toNat _ _ h_i_le, h_sub_1_toNat]
      have hj : ((USize64.ofNat s.val.size) - 1 - i).toNat < s.val.size := by
        rw [h_sub_2_toNat]; omega
      by_cases h_acc : acc.val.size + 1 < USize64.size
      · rw [reverse_at_step s i acc hi_lt hj h_acc] at hres
        have h_push_size :
            (push_one acc (s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj) h_acc).val.size
              = acc.val.size + 1 := by
          show (acc.val ++ #[_]).size = acc.val.size + 1
          rw [Array.size_append]; rfl
        have ih_app := ih s (i + 1) _ r h_meas h_i1_le hres
        rw [h_i1] at ih_app
        rw [h_push_size] at ih_app
        rw [ih_app]; omega
      · exfalso
        have h_big : USize64.size ≤ acc.val.size + 1 := by omega
        rw [reverse_at_step_size_fail s i acc hi_lt hj h_big] at hres
        cases hres

/-- `reverse_at s i acc`: positional formula r[k] = sorted[n - 1 - k] (for the back half). -/
private theorem reverse_at_get :
    ∀ (n : Nat) (s : RustSlice u64) (i : usize)
      (acc : alloc.vec.Vec u64 alloc.alloc.Global)
      (r : alloc.vec.Vec u64 alloc.alloc.Global),
      s.val.size - i.toNat ≤ n →
      i.toNat ≤ s.val.size →
      clever_087_sort_array.reverse_at s i acc = RustM.ok r →
      acc.val.size = i.toNat →
      (∀ (k : Nat) (hk_acc : k < acc.val.size) (hk_r : k < r.val.size),
          r.val[k]'hk_r = acc.val[k]'hk_acc) ∧
      ∀ (k : Nat) (hk_ge : i.toNat ≤ k) (hk_r : k < r.val.size),
        ∃ (hidx : s.val.size - 1 - k < s.val.size),
          r.val[k]'hk_r = s.val[s.val.size - 1 - k]'hidx := by
  intro n
  induction n with
  | zero =>
    intro s i acc r hm hi_le hres h_acc_size
    have hi_ge : s.val.size ≤ i.toNat := by omega
    have hi_eq : i.toNat = s.val.size := by omega
    rw [reverse_at_oob s i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    refine ⟨?_, ?_⟩
    · intro k hk_acc hk_r; rfl
    · intro k hk_ge hk_r
      exfalso
      rw [h_acc_size, hi_eq] at hk_r
      omega
  | succ n ih =>
    intro s i acc r hm hi_le hres h_acc_size
    by_cases hi_ge : s.val.size ≤ i.toNat
    · have hi_eq : i.toNat = s.val.size := by omega
      rw [reverse_at_oob s i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      refine ⟨?_, ?_⟩
      · intro k hk_acc hk_r; rfl
      · intro k hk_ge hk_r
        exfalso
        rw [h_acc_size, hi_eq] at hk_r
        omega
    · have hi_lt : i.toNat < s.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : s.val.size < USize64.size := s.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ s.val.size := by rw [h_i1]; omega
      have h_meas : s.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      have h_n_pos : 0 < s.val.size := by omega
      have h_ofNat : (USize64.ofNat s.val.size).toNat = s.val.size :=
        USize64.toNat_ofNat_of_lt' h_size_lt
      have h_n_pos_us : (0 : Nat) < (USize64.ofNat s.val.size).toNat := by
        rw [h_ofNat]; exact h_n_pos
      have h_sub_1_toNat : ((USize64.ofNat s.val.size) - 1).toNat = s.val.size - 1 := by
        rw [usize_sub_one_toNat _ h_n_pos_us, h_ofNat]
      have h_i_le : i.toNat ≤ ((USize64.ofNat s.val.size) - 1).toNat := by
        rw [h_sub_1_toNat]; omega
      have h_sub_2_toNat : ((USize64.ofNat s.val.size) - 1 - i).toNat = s.val.size - 1 - i.toNat := by
        rw [usize_sub_toNat _ _ h_i_le, h_sub_1_toNat]
      have hj : ((USize64.ofNat s.val.size) - 1 - i).toNat < s.val.size := by
        rw [h_sub_2_toNat]; omega
      by_cases h_acc : acc.val.size + 1 < USize64.size
      · rw [reverse_at_step s i acc hi_lt hj h_acc] at hres
        have h_push_size :
            (push_one acc (s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj) h_acc).val.size
              = acc.val.size + 1 := by
          show (acc.val ++ #[_]).size = acc.val.size + 1
          rw [Array.size_append]; rfl
        have h_acc'_size :
            (push_one acc (s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj) h_acc).val.size
              = (i + 1).toNat := by
          rw [h_push_size, h_i1, h_acc_size]
        obtain ⟨h_prefix_acc', h_back_acc'⟩ :=
          ih s (i + 1) _ r h_meas h_i1_le hres h_acc'_size
        refine ⟨?_, ?_⟩
        · intro k hk_acc hk_r
          have hk_acc'_lt : k < (push_one acc (s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj) h_acc).val.size := by
            rw [h_push_size]; omega
          rw [h_prefix_acc' k hk_acc'_lt hk_r]
          show (acc.val ++ #[_])[k]'hk_acc'_lt = acc.val[k]'hk_acc
          rw [Array.getElem_append_left hk_acc]
        · intro k hk_ge hk_r
          by_cases hk_eq : k = i.toNat
          · subst hk_eq
            have h_k_lt_acc' : i.toNat < (push_one acc (s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj) h_acc).val.size := by
              rw [h_push_size, h_acc_size]; omega
            have h_get_pushed :
                (push_one acc (s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj) h_acc).val[i.toNat]'h_k_lt_acc'
                  = s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj := by
              show (acc.val ++ #[s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj])[i.toNat]
                  = s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj
              have h_acc_idx_eq : acc.val.size = i.toNat := h_acc_size
              rw [Array.getElem_append_right (by rw [h_acc_idx_eq]; exact Nat.le_refl _)]
              simp [h_acc_idx_eq]
            have h_idx_eq : ((USize64.ofNat s.val.size) - 1 - i).toNat = s.val.size - 1 - i.toNat :=
              h_sub_2_toNat
            have hidx : s.val.size - 1 - i.toNat < s.val.size := by omega
            refine ⟨hidx, ?_⟩
            rw [h_prefix_acc' i.toNat h_k_lt_acc' hk_r]
            rw [h_get_pushed]
            exact array_get_idx_eq s.val _ (s.val.size - 1 - i.toNat) hj hidx h_idx_eq
          · have hk_ge' : (i + 1).toNat ≤ k := by rw [h_i1]; omega
            exact h_back_acc' k hk_ge' hk_r
      · exfalso
        have h_big : USize64.size ≤ acc.val.size + 1 := by omega
        rw [reverse_at_step_size_fail s i acc hi_lt hj h_big] at hres
        cases hres

/-- `reverse_at` preserves multiset count. At state `(i, acc)`, the returned `r`
    has count equal to `acc`'s count plus the count of `s[0..s.size - i.toNat)`. -/
private theorem reverse_at_count :
    ∀ (n : Nat) (s : RustSlice u64) (i : usize)
      (acc : alloc.vec.Vec u64 alloc.alloc.Global)
      (r : alloc.vec.Vec u64 alloc.alloc.Global) (target : u64),
      s.val.size - i.toNat ≤ n →
      i.toNat ≤ s.val.size →
      clever_087_sort_array.reverse_at s i acc = RustM.ok r →
      vec_count r.val target r.val.size =
        vec_count acc.val target acc.val.size + vec_count s.val target (s.val.size - i.toNat) := by
  intro n
  induction n with
  | zero =>
    intro s i acc r target hm hi_le hres
    have hi_ge : s.val.size ≤ i.toNat := by omega
    have hi_eq : i.toNat = s.val.size := by omega
    rw [reverse_at_oob s i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    rw [hi_eq, Nat.sub_self]
    show vec_count acc.val target acc.val.size
          = vec_count acc.val target acc.val.size + 0
    omega
  | succ n ih =>
    intro s i acc r target hm hi_le hres
    by_cases hi_ge : s.val.size ≤ i.toNat
    · have hi_eq : i.toNat = s.val.size := by omega
      rw [reverse_at_oob s i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      rw [hi_eq, Nat.sub_self]
      show vec_count acc.val target acc.val.size
            = vec_count acc.val target acc.val.size + 0
      omega
    · have hi_lt : i.toNat < s.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : s.val.size < USize64.size := s.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ s.val.size := by rw [h_i1]; omega
      have h_meas : s.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      have h_n_pos : 0 < s.val.size := by omega
      have h_ofNat : (USize64.ofNat s.val.size).toNat = s.val.size :=
        USize64.toNat_ofNat_of_lt' h_size_lt
      have h_n_pos_us : (0 : Nat) < (USize64.ofNat s.val.size).toNat := by
        rw [h_ofNat]; exact h_n_pos
      have h_sub_1_toNat : ((USize64.ofNat s.val.size) - 1).toNat = s.val.size - 1 := by
        rw [usize_sub_one_toNat _ h_n_pos_us, h_ofNat]
      have h_i_le : i.toNat ≤ ((USize64.ofNat s.val.size) - 1).toNat := by
        rw [h_sub_1_toNat]; omega
      have h_sub_2_toNat : ((USize64.ofNat s.val.size) - 1 - i).toNat = s.val.size - 1 - i.toNat := by
        rw [usize_sub_toNat _ _ h_i_le, h_sub_1_toNat]
      have hj : ((USize64.ofNat s.val.size) - 1 - i).toNat < s.val.size := by
        rw [h_sub_2_toNat]; omega
      by_cases h_acc : acc.val.size + 1 < USize64.size
      · rw [reverse_at_step s i acc hi_lt hj h_acc] at hres
        have h_push_size :
            (push_one acc (s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj) h_acc).val.size
              = acc.val.size + 1 := by
          show (acc.val ++ #[_]).size = acc.val.size + 1
          rw [Array.size_append]; rfl
        have h_count_pushed :
            vec_count (push_one acc (s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj) h_acc).val target
              (acc.val.size + 1)
              = vec_count acc.val target acc.val.size +
                (if (s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj) = target then 1 else 0) := by
          show vec_count (acc.val ++ #[_]) target (acc.val.size + 1) = _
          exact vec_count_append_singleton acc.val (s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj) target
        have ih_app := ih s (i + 1) _ r target h_meas h_i1_le hres
        rw [h_i1, h_push_size, h_count_pushed] at ih_app
        -- At (i+1, push_one acc s[n-1-i]): vec_count r = vec_count new_acc + vec_count s (n - (i+1)).
        -- Now express vec_count s (n - i) in terms of vec_count s (n - (i+1)) + the pushed element.
        have h_sub_succ : s.val.size - i.toNat = (s.val.size - (i.toNat + 1)) + 1 := by omega
        have h_idx_lt : s.val.size - (i.toNat + 1) < s.val.size := by omega
        have h_vec_succ_s :
            vec_count s.val target ((s.val.size - (i.toNat + 1)) + 1) =
              (if s.val[s.val.size - (i.toNat + 1)]'h_idx_lt = target then 1 else 0)
                + vec_count s.val target (s.val.size - (i.toNat + 1)) :=
          vec_count_succ s.val target (s.val.size - (i.toNat + 1)) h_idx_lt
        -- The pushed element equals s[s.size - 1 - i.toNat] = s[s.size - (i.toNat + 1)]
        have h_idx_eq : ((USize64.ofNat s.val.size) - 1 - i).toNat = s.val.size - (i.toNat + 1) := by
          rw [h_sub_2_toNat]; omega
        have h_elem_eq :
            s.val[((USize64.ofNat s.val.size) - 1 - i).toNat]'hj
              = s.val[s.val.size - (i.toNat + 1)]'h_idx_lt :=
          array_get_idx_eq s.val _ (s.val.size - (i.toNat + 1)) hj h_idx_lt h_idx_eq
        rw [h_elem_eq] at ih_app
        rw [h_sub_succ, h_vec_succ_s]
        omega
      · exfalso
        have h_big : USize64.size ≤ acc.val.size + 1 := by omega
        rw [reverse_at_step_size_fail s i acc hi_lt hj h_big] at hres
        cases hres

/-! ## `reverse_at` produces a descending result when input is ascending. -/

private theorem reverse_at_sorted_desc
    (s : RustSlice u64) (h_s_sorted : sorted_asc s.val)
    (r : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_087_sort_array.reverse_at s (0 : usize)
              ⟨(List.nil).toArray, by grind⟩ = RustM.ok r) :
    sorted_desc r.val := by
  -- size of r
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_meas : s.val.size - (0 : usize).toNat ≤ s.val.size := by rw [h_zero_toNat]; omega
  have h_le : (0 : usize).toNat ≤ s.val.size := by rw [h_zero_toNat]; omega
  have h_empty_size : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size = 0 := rfl
  have h_acc_eq_zero : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size = (0 : usize).toNat := by
    rw [h_empty_size, h_zero_toNat]
  have h_size := reverse_at_size s.val.size s (0 : usize) ⟨(List.nil).toArray, by grind⟩ r h_meas h_le hres
  rw [h_empty_size, h_zero_toNat] at h_size
  -- h_size : r.val.size = s.val.size
  have ⟨_, h_back⟩ :=
    reverse_at_get s.val.size s (0 : usize) ⟨(List.nil).toArray, by grind⟩ r h_meas h_le hres h_acc_eq_zero
  -- Now show sorted_desc r.val using sortedness of s.
  intro k₁ k₂ h₁ h₂ h_le12
  have hk1_ge : (0 : usize).toNat ≤ k₁ := by rw [h_zero_toNat]; omega
  have hk2_ge : (0 : usize).toNat ≤ k₂ := by rw [h_zero_toNat]; omega
  obtain ⟨hidx1, hval1⟩ := h_back k₁ hk1_ge h₁
  obtain ⟨hidx2, hval2⟩ := h_back k₂ hk2_ge h₂
  rw [hval1, hval2]
  have h_idx_le : s.val.size - 1 - k₂ ≤ s.val.size - 1 - k₁ := by omega
  exact h_s_sorted (s.val.size - 1 - k₂) (s.val.size - 1 - k₁) hidx2 hidx1 h_idx_le

/-! ## Obligation theorems. -/

/-- `is_empty` evaluates to `ok (lst.val.size = 0 as Bool)`. -/
private theorem is_empty_eq (lst : RustSlice u64) :
    (core_models.slice.Impl.is_empty u64 lst : RustM Bool)
      = RustM.ok (decide (lst.val.size = 0)) := by
  unfold core_models.slice.Impl.is_empty
  have h_len : (core_models.slice.Impl.len u64 lst : RustM usize)
                = RustM.ok (USize64.ofNat lst.val.size) := rfl
  have h_ofNat : (USize64.ofNat lst.val.size).toNat = lst.val.size :=
    USize64.toNat_ofNat_of_lt' lst.size_lt_usizeSize
  rw [h_len]
  simp only [RustM_ok_bind]
  show (USize64.ofNat lst.val.size ==? (0 : usize) : RustM Bool) = _
  show pure (USize64.ofNat lst.val.size == (0 : usize) : Bool) = _
  have h_eq : (USize64.ofNat lst.val.size == (0 : usize) : Bool)
                = decide (lst.val.size = 0) := by
    by_cases h : lst.val.size = 0
    · have h_us : USize64.ofNat lst.val.size = (0 : usize) := by
        apply USize64.toNat_inj.mp
        rw [h_ofNat]; exact h
      rw [h_us]; simp [h]
    · have h_us_ne : USize64.ofNat lst.val.size ≠ (0 : usize) := by
        intro hus
        apply h
        have := congrArg USize64.toNat hus
        rw [h_ofNat] at this
        exact this
      simp [h_us_ne, h]
  rw [h_eq]; rfl

/-- Anchor: empty input yields a successful empty output. -/
theorem sort_array_empty_input_returns_empty
    (lst : RustSlice u64) (hempty : lst.val.size = 0) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_087_sort_array.sort_array lst = RustM.ok v ∧
      v.val.size = 0 := by
  refine ⟨⟨#[], by decide⟩, ?_, rfl⟩
  unfold clever_087_sort_array.sort_array
  rw [is_empty_eq]
  simp only [RustM_ok_bind, decide_eq_true hempty, if_true, ↓reduceIte]
  rfl

/-- `sort_array_eval`: given `sort_at` succeeds, sort_array equals one of two outcomes
    depending on parity. -/
private theorem sort_array_eval_nonempty
    (lst : RustSlice u64) (hne : 0 < lst.val.size)
    (sorted : alloc.vec.Vec u64 alloc.alloc.Global)
    (h_sort_ok :
      clever_087_sort_array.sort_at lst (0 : usize) ⟨(List.nil).toArray, by grind⟩
        = RustM.ok sorted) :
    clever_087_sort_array.sort_array lst =
      (if ((lst.val[0]'hne).toNat % 2
            + (lst.val[lst.val.size - 1]'(by omega)).toNat % 2) % 2 ≠ 0
       then RustM.ok sorted
       else clever_087_sort_array.reverse_at sorted (0 : usize)
              ⟨(List.nil).toArray, by grind⟩) := by
  unfold clever_087_sort_array.sort_array
  have h_size_lt : lst.val.size < USize64.size := lst.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_lst_size_lt : lst.val.size < 2^64 := by rw [h_usize_size] at h_size_lt; exact h_size_lt
  have h_ofNat : (USize64.ofNat lst.val.size).toNat = lst.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have hempty_ne : lst.val.size ≠ 0 := by omega
  rw [is_empty_eq]
  simp only [RustM_ok_bind, decide_eq_false hempty_ne, ↓reduceIte, Bool.false_eq_true]
  have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new]
  simp only [RustM_ok_bind]
  rw [h_sort_ok]
  simp only [RustM_ok_bind]
  -- Now reduce the parity chain. Order matters: RIGHT operand of `+?` first (its inner chain),
  -- then LEFT operand, then `+?`, then `%? 2`, then `!=? 0`.
  have h_len : (core_models.slice.Impl.len u64 lst : RustM usize)
                = RustM.ok (USize64.ofNat lst.val.size) := rfl
  have h_n_pos_us : (0 : Nat) < (USize64.ofNat lst.val.size).toNat := by
    rw [h_ofNat]; exact hne
  have h_sub_1_ok : ((USize64.ofNat lst.val.size) -? (1 : usize) : RustM usize)
                    = RustM.ok ((USize64.ofNat lst.val.size) - 1) :=
    usize_sub_one_ok _ h_n_pos_us
  have h_sub_1_toNat : ((USize64.ofNat lst.val.size) - 1).toNat = lst.val.size - 1 := by
    rw [usize_sub_one_toNat _ h_n_pos_us, h_ofNat]
  have h_lst_last_lt' : lst.val.size - 1 < lst.val.size := by omega
  have h_lst_last_lt : ((USize64.ofNat lst.val.size) - 1).toNat < lst.val.size := by
    rw [h_sub_1_toNat]; omega
  have h_lst_get_last :
      (lst[((USize64.ofNat lst.val.size) - 1)]_? : RustM u64)
        = RustM.ok (lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt) := by
    show (if h : ((USize64.ofNat lst.val.size) - 1).toNat < lst.val.size
            then pure (lst.val[(USize64.ofNat lst.val.size) - 1])
            else .fail .arrayOutOfBounds)
        = RustM.ok (lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt)
    rw [dif_pos h_lst_last_lt]; rfl
  have h_idx_last_eq :
      lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt
        = lst.val[lst.val.size - 1]'h_lst_last_lt' :=
    array_get_idx_eq lst.val _ (lst.val.size - 1) h_lst_last_lt h_lst_last_lt' h_sub_1_toNat
  have h_mod_zero_r :
      ((lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt) %? (2 : u64) : RustM u64)
        = RustM.ok ((lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt) % (2 : u64)) := by
    show (rust_primitives.ops.arith.Rem.rem _ 2 : RustM u64) = _
    show (if (2 : u64) = 0 then (.fail .divisionByZero : RustM u64) else pure _) = _
    rw [if_neg (by decide)]; rfl
  have h_lst_get_0 : (lst[(0 : usize)]_? : RustM u64) = RustM.ok (lst.val[0]'hne) := by
    show (if h : (0 : usize).toNat < lst.val.size then pure (lst.val[(0 : usize)])
            else .fail .arrayOutOfBounds)
        = RustM.ok (lst.val[0]'hne)
    rw [dif_pos (show (0 : usize).toNat < lst.val.size from hne)]; rfl
  have h_mod_zero_l : ((lst.val[0]'hne) %? (2 : u64) : RustM u64)
                      = RustM.ok ((lst.val[0]'hne) % (2 : u64)) := by
    show (rust_primitives.ops.arith.Rem.rem (lst.val[0]'hne) 2 : RustM u64) = _
    show (if (2 : u64) = 0 then (.fail .divisionByZero : RustM u64) else pure _) = _
    rw [if_neg (by decide)]; rfl
  have h_add_no_ov :
      (((lst.val[0]'hne) % (2 : u64)).toNat
          + ((lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt) % (2 : u64)).toNat) < 2^64 := by
    have h1 : ((lst.val[0]'hne) % (2 : u64)).toNat < 2 := by
      show ((lst.val[0]'hne).toNat % 2) < 2; omega
    have h2 : ((lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt) % (2 : u64)).toNat < 2 := by
      show ((lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt).toNat % 2) < 2; omega
    omega
  have h_add_ok :
      (((lst.val[0]'hne) % (2 : u64))
        +? ((lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt) % (2 : u64)) : RustM u64)
        = RustM.ok ((lst.val[0]'hne) % (2 : u64)
                    + (lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt) % (2 : u64)) := by
    show (rust_primitives.ops.arith.Add.add _ _ : RustM u64) = _
    show (if BitVec.uaddOverflow _ _
          then (.fail .integerOverflow : RustM u64)
          else pure _) = _
    have h_no_bv : BitVec.uaddOverflow (((lst.val[0]'hne) % (2 : u64))).toBitVec (((lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt) % (2 : u64))).toBitVec = false := by
      -- BitVec.uaddOverflow x.toBitVec y.toBitVec is defeq to UInt64.addOverflow x y.
      -- Use UInt64.addOverflow_iff to bridge to a Nat-level overflow check.
      show UInt64.addOverflow ((lst.val[0]'hne) % (2 : u64))
            ((lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt) % (2 : u64)) = false
      cases hov : UInt64.addOverflow ((lst.val[0]'hne) % (2 : u64))
                    ((lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt) % (2 : u64)) with
      | false => rfl
      | true =>
        exfalso
        have := UInt64.addOverflow_iff.mp hov
        omega
    rw [h_no_bv]; rfl
  have h_mod_zero_final :
    (((lst.val[0]'hne) % (2 : u64) + (lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt) % (2 : u64)) %? (2 : u64) : RustM u64)
      = RustM.ok (((lst.val[0]'hne) % (2 : u64) + (lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt) % (2 : u64)) % (2 : u64)) := by
    show (rust_primitives.ops.arith.Rem.rem _ 2 : RustM u64) = _
    show (if (2 : u64) = 0 then (.fail .divisionByZero : RustM u64) else pure _) = _
    rw [if_neg (by decide)]; rfl
  -- Use `generalize` to give the parity expression a name (since `set` is Mathlib-only).
  have h_parity_toNat :
      (((lst.val[0]'hne) % (2 : u64) + (lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt) % (2 : u64)) % (2 : u64)).toNat
        = ((lst.val[0]'hne).toNat % 2 + (lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt).toNat % 2) % 2 := by
    have h1 : ((lst.val[0]'hne) % (2 : u64)).toNat = (lst.val[0]'hne).toNat % 2 := by
      show ((lst.val[0]'hne).toNat % 2) = _; rfl
    have h2 : ((lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt) % (2 : u64)).toNat
                = (lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt).toNat % 2 := by
      show ((lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt).toNat % 2) = _; rfl
    have h3 : (((lst.val[0]'hne) % (2 : u64)
                    + (lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt) % (2 : u64))).toNat
                = ((lst.val[0]'hne).toNat % 2 + (lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt).toNat % 2) := by
      rw [UInt64.toNat_add_of_lt (by rw [h1, h2]; exact h_add_no_ov)]
      rw [h1, h2]
    show (((lst.val[0]'hne) % (2 : u64) + (lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt) % (2 : u64)).toNat % 2) = _
    rw [h3]
  have h_neq_def_pre :
      ∀ (p : u64), (p !=? (0 : u64) : RustM Bool) = RustM.ok (decide (p ≠ 0)) := by
    intro p
    show (rust_primitives.cmp.ne p 0 : RustM Bool) = _
    show pure (p != (0 : u64) : Bool) = _
    rw [show (p != (0 : u64) : Bool) = decide (p ≠ 0) from by
      by_cases h : p = 0
      · rw [h]; decide
      · simp [h]]
    rfl
  -- Perform reductions in LEFT-first order (matches Lean's do-block desugaring).
  rw [h_lst_get_0]; simp only [RustM_ok_bind]
  rw [h_mod_zero_l]; simp only [RustM_ok_bind]
  rw [h_len]; simp only [RustM_ok_bind]
  rw [h_sub_1_ok]; simp only [RustM_ok_bind]
  rw [h_lst_get_last]; simp only [RustM_ok_bind]
  rw [h_mod_zero_r]; simp only [RustM_ok_bind]
  rw [h_add_ok]; simp only [RustM_ok_bind]
  rw [h_mod_zero_final]; simp only [RustM_ok_bind]
  rw [h_neq_def_pre]; simp only [RustM_ok_bind]
  -- Goal: if (decide ((u64 parity ≠ 0))) = true then RustM.ok sorted else (deref >>= reverse_at)
  --     = if (Nat parity ≠ 0) then RustM.ok sorted else reverse_at sorted 0 #[]
  -- Bridge u64 ≠ 0 to Nat ≠ 0 via h_parity_toNat.
  have h_parity_eq_zero_iff :
      (((lst.val[0]'hne) % (2 : u64) + (lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt) % (2 : u64)) % (2 : u64) = 0) ↔
      ((lst.val[0]'hne).toNat % 2 + (lst.val[lst.val.size - 1]'h_lst_last_lt').toNat % 2) % 2 = 0 := by
    rw [← h_idx_last_eq]
    constructor
    · intro h
      have := congrArg UInt64.toNat h
      rw [h_parity_toNat] at this
      exact this
    · intro h
      apply (UInt64.toNat_inj).mp
      rw [h_parity_toNat]; exact h
  by_cases h_par_nat : ((lst.val[0]'hne).toNat % 2 + (lst.val[lst.val.size - 1]'h_lst_last_lt').toNat % 2) % 2 = 0
  · -- Even parity branch
    have h_par_nat_ne : ¬ ((lst.val[0]'hne).toNat % 2 + (lst.val[lst.val.size - 1]'h_lst_last_lt').toNat % 2) % 2 ≠ 0 := by
      intro h; exact h h_par_nat
    rw [if_neg h_par_nat_ne]
    have h_par_u64_eq : ((lst.val[0]'hne) % (2 : u64) + (lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt) % (2 : u64)) % (2 : u64) = 0 :=
      h_parity_eq_zero_iff.mpr h_par_nat
    have h_dec_false :
        decide (((lst.val[0]'hne) % (2 : u64) + (lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt) % (2 : u64)) % (2 : u64) ≠ 0)
          = false := by
      rw [decide_eq_false_iff_not]
      intro h; exact h h_par_u64_eq
    rw [h_dec_false]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have h_deref :
        (core_models.ops.deref.Deref.deref
          (alloc.vec.Vec u64 alloc.alloc.Global) sorted : RustM _) = RustM.ok sorted := rfl
    rw [h_deref]
    simp only [RustM_ok_bind]
  · -- Odd parity: both sides should reduce to RustM.ok sorted
    have h_par_nat_ne : ((lst.val[0]'hne).toNat % 2 + (lst.val[lst.val.size - 1]'h_lst_last_lt').toNat % 2) % 2 ≠ 0 := h_par_nat
    rw [if_pos h_par_nat_ne]
    have h_par_u64_ne : ((lst.val[0]'hne) % (2 : u64) + (lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt) % (2 : u64)) % (2 : u64) ≠ 0 := by
      intro h
      exact h_par_nat (h_parity_eq_zero_iff.mp h)
    have h_dec_true :
        decide (((lst.val[0]'hne) % (2 : u64) + (lst.val[((USize64.ofNat lst.val.size) - 1).toNat]'h_lst_last_lt) % (2 : u64)) % (2 : u64) ≠ 0)
          = true := decide_eq_true h_par_u64_ne
    rw [h_dec_true]
    rfl

/-- Helper: when `sort_array lst = ok v` and `lst` is non-empty, `sort_at` must succeed. -/
private theorem sort_array_extract_sort_at
    (lst : RustSlice u64) (hne : 0 < lst.val.size)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_087_sort_array.sort_array lst = RustM.ok v) :
    ∃ sorted : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_087_sort_array.sort_at lst (0 : usize)
        ⟨(List.nil).toArray, by grind⟩ = RustM.ok sorted := by
  have hempty_ne : lst.val.size ≠ 0 := by omega
  unfold clever_087_sort_array.sort_array at hres
  rw [is_empty_eq] at hres
  simp only [RustM_ok_bind, decide_eq_false hempty_ne, ↓reduceIte, Bool.false_eq_true] at hres
  have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  generalize h_sort :
      clever_087_sort_array.sort_at lst (0 : usize) ⟨(List.nil).toArray, by grind⟩ = sa_res at hres
  cases sa_res with
  | none => exfalso; cases hres
  | some sa_res' =>
    cases sa_res' with
    | error e => exfalso; cases hres
    | ok sorted =>
      -- After `generalize ... at hres`, the goal also has `sort_at lst ...` replaced
      -- by `some (Except.ok sorted)`. Since `RustM.ok x ≡ some (Except.ok x)`, rfl closes it.
      exact ⟨sorted, rfl⟩

/-- Generic decomposition: `sort_array lst = RustM.ok v` implies the existence of a sorted
    intermediate, and one of the two parity-branch outcomes for `v`. -/
private theorem sort_array_decompose
    (lst : RustSlice u64) (hne : 0 < lst.val.size)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_087_sort_array.sort_array lst = RustM.ok v) :
    ∃ sorted : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_087_sort_array.sort_at lst (0 : usize) ⟨(List.nil).toArray, by grind⟩
        = RustM.ok sorted ∧
      (((lst.val[0]'hne).toNat % 2
          + (lst.val[lst.val.size - 1]'(by omega)).toNat % 2) % 2 ≠ 0 → v = sorted) ∧
      (((lst.val[0]'hne).toNat % 2
          + (lst.val[lst.val.size - 1]'(by omega)).toNat % 2) % 2 = 0 →
        clever_087_sort_array.reverse_at sorted (0 : usize)
          ⟨(List.nil).toArray, by grind⟩ = RustM.ok v) := by
  obtain ⟨sorted, h_sort_ok⟩ := sort_array_extract_sort_at lst hne v hres
  have h_eval := sort_array_eval_nonempty lst hne sorted h_sort_ok
  rw [h_eval] at hres
  refine ⟨sorted, h_sort_ok, ?_, ?_⟩
  · intro h_par
    rw [if_pos h_par] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    exact h_eq'.symm
  · intro h_par
    have h_not : ¬ ((lst.val[0]'hne).toNat % 2 + (lst.val[lst.val.size - 1]'(by omega)).toNat % 2) % 2 ≠ 0 := by
      intro h; exact h h_par
    rw [if_neg h_not] at hres
    exact hres

theorem sort_array_output_is_permutation_of_input
    (lst : RustSlice u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_087_sort_array.sort_array lst = RustM.ok v)
    (target : u64) :
    vec_count v.val target v.val.size = vec_count lst.val target lst.val.size := by
  by_cases hempty : lst.val.size = 0
  · -- Empty case
    unfold clever_087_sort_array.sort_array at hres
    rw [is_empty_eq] at hres
    simp only [RustM_ok_bind, decide_eq_true hempty, if_true, ↓reduceIte] at hres
    have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                    RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                  RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
    rw [h_new] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    rw [hempty]
    show vec_count (List.nil : List u64).toArray target 0 = 0
    rfl
  · have hne : 0 < lst.val.size := by omega
    obtain ⟨sorted, h_sort_ok, h_odd, h_even⟩ := sort_array_decompose lst hne v hres
    -- vec_count sorted target sorted.size = vec_count lst target lst.size (from sort_at_inv)
    have h_zero_toNat : (0 : usize).toNat = 0 := rfl
    have h_meas_s : lst.val.size - (0 : usize).toNat ≤ lst.val.size := by rw [h_zero_toNat]; omega
    have h_le_s : (0 : usize).toNat ≤ lst.val.size := by rw [h_zero_toNat]; omega
    have h_sort_inv := (sort_at_inv lst.val.size lst (0 : usize)
      ⟨(List.nil).toArray, by grind⟩ sorted target h_meas_s h_le_s h_sort_ok).2
    have h_empty_size : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size = 0 := rfl
    have h_empty_count : vec_count ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val target 0 = 0 := rfl
    rw [h_empty_size, h_zero_toNat] at h_sort_inv
    rw [h_empty_count] at h_sort_inv
    have h_lst_zero : vec_count lst.val target 0 = 0 := rfl
    rw [h_lst_zero] at h_sort_inv
    have h_sort_count : vec_count sorted.val target sorted.val.size = vec_count lst.val target lst.val.size := by
      omega
    by_cases h_par_nat : ((lst.val[0]'hne).toNat % 2 + (lst.val[lst.val.size - 1]'(by omega)).toNat % 2) % 2 = 0
    · -- Even parity: v = reverse_at sorted 0 #[]
      have h_rev_ok := h_even h_par_nat
      have h_meas_r : sorted.val.size - (0 : usize).toNat ≤ sorted.val.size := by rw [h_zero_toNat]; omega
      have h_le_r : (0 : usize).toNat ≤ sorted.val.size := by rw [h_zero_toNat]; omega
      have h_rev_count := reverse_at_count sorted.val.size sorted (0 : usize)
        ⟨(List.nil).toArray, by grind⟩ v target h_meas_r h_le_r h_rev_ok
      rw [h_zero_toNat, Nat.sub_zero] at h_rev_count
      have h_empty_count2 : vec_count ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val target 0 = 0 := rfl
      rw [h_empty_size, h_empty_count2] at h_rev_count
      -- h_rev_count : vec_count v target v.size = 0 + vec_count sorted target sorted.size
      rw [h_rev_count, Nat.zero_add]
      exact h_sort_count
    · -- Odd parity: v = sorted
      have h_par_ne : ((lst.val[0]'hne).toNat % 2 + (lst.val[lst.val.size - 1]'(by omega)).toNat % 2) % 2 ≠ 0 := h_par_nat
      have h_v_eq : v = sorted := h_odd h_par_ne
      subst h_v_eq
      exact h_sort_count

theorem sort_array_ascending_when_sum_is_odd
    (lst : RustSlice u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hne : 0 < lst.val.size)
    (hres : clever_087_sort_array.sort_array lst = RustM.ok v)
    (hparity :
      ((lst.val[0]'hne).toNat % 2
        + (lst.val[lst.val.size - 1]'(by omega)).toNat % 2) % 2 ≠ 0) :
    sorted_asc v.val := by
  obtain ⟨sorted, h_sort_ok, h_odd, _⟩ := sort_array_decompose lst hne v hres
  have h_v_eq : v = sorted := h_odd hparity
  subst h_v_eq
  -- Now: sorted_asc v.val where v = sorted; use sort_at_sorted.
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_meas : lst.val.size - (0 : usize).toNat ≤ lst.val.size := by rw [h_zero_toNat]; omega
  have h_le : (0 : usize).toNat ≤ lst.val.size := by rw [h_zero_toNat]; omega
  exact sort_at_sorted lst.val.size lst (0 : usize) ⟨(List.nil).toArray, by grind⟩ v
    h_meas h_le h_sort_ok sorted_asc_empty

theorem sort_array_descending_when_sum_is_even
    (lst : RustSlice u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hne : 0 < lst.val.size)
    (hres : clever_087_sort_array.sort_array lst = RustM.ok v)
    (hparity :
      ((lst.val[0]'hne).toNat % 2
        + (lst.val[lst.val.size - 1]'(by omega)).toNat % 2) % 2 = 0) :
    sorted_desc v.val := by
  obtain ⟨sorted, h_sort_ok, _, h_even⟩ := sort_array_decompose lst hne v hres
  have h_rev_ok : clever_087_sort_array.reverse_at sorted (0 : usize)
                    ⟨(List.nil).toArray, by grind⟩ = RustM.ok v := h_even hparity
  -- Sortedness of sorted (asc) from sort_at_sorted; then reverse_at_sorted_desc.
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_meas : lst.val.size - (0 : usize).toNat ≤ lst.val.size := by rw [h_zero_toNat]; omega
  have h_le : (0 : usize).toNat ≤ lst.val.size := by rw [h_zero_toNat]; omega
  have h_sorted_asc : sorted_asc sorted.val :=
    sort_at_sorted lst.val.size lst (0 : usize) ⟨(List.nil).toArray, by grind⟩ sorted
      h_meas h_le h_sort_ok sorted_asc_empty
  -- Vec u64 Global = RustSlice u64 = Seq u64 (all are abbrevs for the same Seq); pass `sorted` directly.
  exact reverse_at_sorted_desc sorted h_sorted_asc v h_rev_ok

end Clever_087_sort_arrayObligations
