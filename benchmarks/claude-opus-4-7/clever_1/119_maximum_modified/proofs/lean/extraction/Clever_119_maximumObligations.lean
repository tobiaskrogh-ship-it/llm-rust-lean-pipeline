-- Companion obligations file for the `clever_119_maximum` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

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

The proptests assert properties of `maximum arr k`:
1. `k = 0` ⟹ the result is empty;
2. `arr.is_empty()` ⟹ the result is empty;
3. the length of the result is `min(k, arr.len())`;
4. the result is sorted ascending;
5. the result is the suffix of an ascending sort of `arr` of length `min(k, arr.len())`. -/

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

/-! ## Standard scaffolding. -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

private theorem usize_zero_toNat : (0 : usize).toNat = 0 := rfl

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

/-- u64 subtraction in RustM without underflow. -/
private theorem u64_sub_ok (a b : u64) (h : b.toNat ≤ a.toNat) :
    (a -? b : RustM u64) = RustM.ok (a - b) := by
  show (rust_primitives.ops.arith.Sub.sub a b : RustM u64) = RustM.ok (a - b)
  show (if BitVec.usubOverflow a.toBitVec b.toBitVec
        then (.fail .integerOverflow : RustM u64)
        else pure (a - b)) = _
  have h_no_bv :
      BitVec.usubOverflow a.toBitVec b.toBitVec = false := by
    generalize hbo : BitVec.usubOverflow a.toBitVec b.toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have h_sub_ov : UInt64.subOverflow a b = true := hbo
      have hii : a.toNat < b.toNat := UInt64.subOverflow_iff.mp h_sub_ov
      omega
  rw [h_no_bv]; rfl

private theorem u64_sub_toNat (a b : u64) (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  rw [UInt64.toNat_sub_of_le' h]

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

/-- Get-element congruence: if two indices are equal as Nats, the looked-up element is the same. -/
private theorem array_get_idx_eq {α : Type} (a : Array α) (i j : Nat)
    (hi : i < a.size) (hj : j < a.size) (h : i = j) :
    a[i]'hi = a[j]'hj := by
  subst h; rfl

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
    clever_119_maximum.insert_asc_at v x i true acc = RustM.ok acc := by
  unfold clever_119_maximum.insert_asc_at
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
    clever_119_maximum.insert_asc_at v x i false acc =
      RustM.ok (push_one acc x h_acc) := by
  unfold clever_119_maximum.insert_asc_at
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
    clever_119_maximum.insert_asc_at v x i false acc
      = RustM.fail .maximumSizeExceeded := by
  unfold clever_119_maximum.insert_asc_at
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
    clever_119_maximum.insert_asc_at v x i false acc =
      clever_119_maximum.insert_asc_at v x (i + 1) true
        (push_two acc x (v.val[i.toNat]'hi) h_acc) := by
  conv => lhs; unfold clever_119_maximum.insert_asc_at
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
    clever_119_maximum.insert_asc_at v x i false acc = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_119_maximum.insert_asc_at
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
    (done : Bool) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_skip : done = true ∨ (v.val[i.toNat]'hi).toNat < x.toNat)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_119_maximum.insert_asc_at v x i done acc =
      clever_119_maximum.insert_asc_at v x (i + 1) done
        (push_one acc (v.val[i.toNat]'hi) h_acc) := by
  conv => lhs; unfold clever_119_maximum.insert_asc_at
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
  have h_and_false : ((!done) && decide ((v.val[i.toNat]'hi) ≥ x)) = false := by
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
    (done : Bool) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_skip : done = true ∨ (v.val[i.toNat]'hi).toNat < x.toNat)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_119_maximum.insert_asc_at v x i done acc = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_119_maximum.insert_asc_at
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
  have h_and_false : ((!done) && decide ((v.val[i.toNat]'hi) ≥ x)) = false := by
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

/-! ## `insert_asc_at` size + toList content invariant. -/

private theorem insert_asc_at_inv :
    ∀ (n : Nat) (v : RustSlice u64) (x : u64) (i : usize) (done : Bool)
      (acc : alloc.vec.Vec u64 alloc.alloc.Global)
      (r : alloc.vec.Vec u64 alloc.alloc.Global),
      v.val.size - i.toNat ≤ n →
      i.toNat ≤ v.val.size →
      clever_119_maximum.insert_asc_at v x i done acc = RustM.ok r →
      r.val.size = acc.val.size + (v.val.size - i.toNat) + (if done then 0 else 1) ∧
      r.val.toList = acc.val.toList ++
        (if done then v.val.toList.drop i.toNat
         else insert_asc_list (v.val.toList.drop i.toNat) x) := by
  intro n
  induction n with
  | zero =>
    intro v x i done acc r hm hi_le hres
    have hi_ge : v.val.size ≤ i.toNat := by omega
    have hi_eq : i.toNat = v.val.size := by omega
    cases done with
    | true =>
      rw [insert_asc_at_oob_inserted v x i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      refine ⟨?_, ?_⟩
      · simp [hi_eq]
      · simp only [if_true, if_pos rfl]
        have h_drop_nil : v.val.toList.drop i.toNat = [] := by
          rw [hi_eq]
          have : v.val.toList.length = v.val.size := by simp [Array.length_toList]
          rw [List.drop_eq_nil_iff]
          omega
        rw [h_drop_nil]; simp
    | false =>
      by_cases h_acc : acc.val.size + 1 < USize64.size
      · rw [insert_asc_at_oob_not_inserted v x i acc hi_ge h_acc] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        refine ⟨?_, ?_⟩
        · show (acc.val ++ #[x]).size = acc.val.size + (v.val.size - i.toNat) + 1
          rw [Array.size_append]; simp; omega
        · simp only [if_neg Bool.false_ne_true]
          show (acc.val ++ #[x]).toList = acc.val.toList ++ insert_asc_list (v.val.toList.drop i.toNat) x
          have h_drop_nil : v.val.toList.drop i.toNat = [] := by
            rw [hi_eq]
            rw [List.drop_eq_nil_iff]
            simp [Array.length_toList]
          rw [h_drop_nil]
          show (acc.val ++ #[x]).toList = acc.val.toList ++ [x]
          simp [Array.toList_append]
      · exfalso
        have h_big : USize64.size ≤ acc.val.size + 1 := by omega
        rw [insert_asc_at_oob_not_inserted_fail v x i acc hi_ge h_big] at hres
        cases hres
  | succ n ih =>
    intro v x i done acc r hm hi_le hres
    by_cases hi_ge : v.val.size ≤ i.toNat
    · have hi_eq : i.toNat = v.val.size := by omega
      cases done with
      | true =>
        rw [insert_asc_at_oob_inserted v x i acc hi_ge] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        refine ⟨?_, ?_⟩
        · simp [hi_eq]
        · simp only [if_true, if_pos rfl]
          have h_drop_nil : v.val.toList.drop i.toNat = [] := by
            rw [hi_eq]
            rw [List.drop_eq_nil_iff]
            simp [Array.length_toList]
          rw [h_drop_nil]; simp
      | false =>
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [insert_asc_at_oob_not_inserted v x i acc hi_ge h_acc] at hres
          injection hres with h_eq
          injection h_eq with h_eq'
          subst h_eq'
          refine ⟨?_, ?_⟩
          · show (acc.val ++ #[x]).size = acc.val.size + (v.val.size - i.toNat) + 1
            rw [Array.size_append]; simp; omega
          · simp only [if_neg Bool.false_ne_true]
            show (acc.val ++ #[x]).toList = acc.val.toList ++ insert_asc_list (v.val.toList.drop i.toNat) x
            have h_drop_nil : v.val.toList.drop i.toNat = [] := by
              rw [hi_eq]
              rw [List.drop_eq_nil_iff]
              simp [Array.length_toList]
            rw [h_drop_nil]
            show (acc.val ++ #[x]).toList = acc.val.toList ++ [x]
            simp [Array.toList_append]
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
      -- v.toList.drop i = v[i] :: v.toList.drop (i+1)
      have h_v_toList_length : v.val.toList.length = v.val.size := by simp [Array.length_toList]
      have h_drop_cons : v.val.toList.drop i.toNat
                          = (v.val[i.toNat]'hi_lt) :: v.val.toList.drop (i.toNat + 1) := by
        have h_len_lt : i.toNat < v.val.toList.length := by rw [h_v_toList_length]; exact hi_lt
        rw [List.drop_eq_getElem_cons h_len_lt, Array.getElem_toList]; rfl
      cases done with
      | true =>
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [insert_asc_at_step_pass v x i true acc hi_lt (Or.inl rfl) h_acc] at hres
          have h_push_size :
              (push_one acc (v.val[i.toNat]'hi_lt) h_acc).val.size = acc.val.size + 1 := by
            show (acc.val ++ #[v.val[i.toNat]'hi_lt]).size = acc.val.size + 1
            rw [Array.size_append]; rfl
          have h_push_toList :
              (push_one acc (v.val[i.toNat]'hi_lt) h_acc).val.toList
                = acc.val.toList ++ [v.val[i.toNat]'hi_lt] := by
            show (acc.val ++ #[v.val[i.toNat]'hi_lt]).toList = _
            simp [Array.toList_append]
          have ih_app := ih v x (i + 1) true (push_one acc (v.val[i.toNat]'hi_lt) h_acc) r
            h_meas h_i1_le hres
          rw [h_i1] at ih_app
          obtain ⟨h_size_eq, h_toList_eq⟩ := ih_app
          rw [h_push_size] at h_size_eq
          rw [h_push_toList] at h_toList_eq
          simp only [if_true, if_pos rfl] at h_size_eq h_toList_eq
          refine ⟨?_, ?_⟩
          · simp only [if_true, if_pos rfl]; rw [h_size_eq]
            have : 0 < v.val.size - i.toNat := by omega
            omega
          · simp only [if_true, if_pos rfl]
            rw [h_toList_eq]
            rw [h_drop_cons]
            simp [List.append_assoc]
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
            have h_push_toList :
                (push_two acc x (v.val[i.toNat]'hi_lt) h_acc).val.toList
                  = acc.val.toList ++ [x, v.val[i.toNat]'hi_lt] := by
              show (acc.val ++ #[x, v.val[i.toNat]'hi_lt]).toList = _
              simp [Array.toList_append]
            have ih_app := ih v x (i + 1) true (push_two acc x (v.val[i.toNat]'hi_lt) h_acc) r
              h_meas h_i1_le hres
            rw [h_i1] at ih_app
            obtain ⟨h_size_eq, h_toList_eq⟩ := ih_app
            rw [h_push_size] at h_size_eq
            rw [h_push_toList] at h_toList_eq
            rw [if_pos (rfl : true = true)] at h_size_eq h_toList_eq
            rw [if_neg (Bool.false_ne_true)]
            refine ⟨?_, ?_⟩
            · rw [h_size_eq]
              have : 0 < v.val.size - i.toNat := by omega
              omega
            · rw [h_toList_eq]
              rw [h_drop_cons]
              -- insert_asc_list (v[i] :: tail) x = (if x ≤ v[i] then x :: v[i] :: tail else v[i] :: insert_asc_list tail x)
              show acc.val.toList ++ [x, v.val[i.toNat]'hi_lt] ++ v.val.toList.drop (i.toNat + 1)
                  = acc.val.toList ++ insert_asc_list ((v.val[i.toNat]'hi_lt) :: v.val.toList.drop (i.toNat + 1)) x
              have h_x_le : x ≤ v.val[i.toNat]'hi_lt := by
                rw [UInt64.le_iff_toNat_le]; omega
              show _ = acc.val.toList ++
                  (if x ≤ v.val[i.toNat]'hi_lt then x :: (v.val[i.toNat]'hi_lt) :: v.val.toList.drop (i.toNat + 1)
                   else (v.val[i.toNat]'hi_lt) :: insert_asc_list (v.val.toList.drop (i.toNat + 1)) x)
              rw [if_pos h_x_le]
              simp [List.append_assoc]
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
            have h_push_toList :
                (push_one acc (v.val[i.toNat]'hi_lt) h_acc).val.toList
                  = acc.val.toList ++ [v.val[i.toNat]'hi_lt] := by
              show (acc.val ++ #[v.val[i.toNat]'hi_lt]).toList = _
              simp [Array.toList_append]
            have ih_app := ih v x (i + 1) false (push_one acc (v.val[i.toNat]'hi_lt) h_acc) r
              h_meas h_i1_le hres
            rw [h_i1] at ih_app
            obtain ⟨h_size_eq, h_toList_eq⟩ := ih_app
            rw [h_push_size] at h_size_eq
            rw [h_push_toList] at h_toList_eq
            rw [if_neg (Bool.false_ne_true)] at h_size_eq h_toList_eq
            rw [if_neg (Bool.false_ne_true)]
            refine ⟨?_, ?_⟩
            · rw [h_size_eq]
              have : 0 < v.val.size - i.toNat := by omega
              omega
            · rw [h_toList_eq]
              rw [h_drop_cons]
              show acc.val.toList ++ [v.val[i.toNat]'hi_lt] ++ insert_asc_list (v.val.toList.drop (i.toNat + 1)) x
                  = acc.val.toList ++ insert_asc_list ((v.val[i.toNat]'hi_lt) :: v.val.toList.drop (i.toNat + 1)) x
              have h_x_nle : ¬ x ≤ v.val[i.toNat]'hi_lt := by
                rw [UInt64.le_iff_toNat_le]; omega
              show _ = acc.val.toList ++
                  (if x ≤ v.val[i.toNat]'hi_lt then x :: (v.val[i.toNat]'hi_lt) :: v.val.toList.drop (i.toNat + 1)
                   else (v.val[i.toNat]'hi_lt) :: insert_asc_list (v.val.toList.drop (i.toNat + 1)) x)
              rw [if_neg h_x_nle]
              simp [List.append_assoc]
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 1 := by omega
            rw [insert_asc_at_step_pass_fail v x i false acc hi_lt (Or.inr h_lt) h_big] at hres
            cases hres

/-- Specialization: insert_asc v x has size v.size + 1 and result toList = insert_asc_list v.toList x. -/
private theorem insert_asc_inv (v : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (r : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_119_maximum.insert_asc v x = RustM.ok r) :
    r.val.size = v.val.size + 1 ∧
    r.val.toList = insert_asc_list v.val.toList x := by
  unfold clever_119_maximum.insert_asc at hres
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
    ⟨(List.nil).toArray, by grind⟩ r h_meas h_le hres
  obtain ⟨h_size_eq, h_toList_eq⟩ := inv
  have h_empty_size : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size = 0 := rfl
  have h_empty_toList : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.toList = [] := by
    show (List.nil : List u64).toArray.toList = []
    simp
  rw [h_empty_size, h_zero_toNat] at h_size_eq
  rw [h_empty_toList, h_zero_toNat] at h_toList_eq
  simp at h_toList_eq
  refine ⟨?_, ?_⟩
  · rw [h_size_eq]; simp
  · exact h_toList_eq

/-! ## `insert_asc_at` produces sorted output. -/

private theorem insert_asc_at_sorted (v : RustSlice u64) (x : u64)
    (h_v_sorted : sorted_asc v.val) :
    ∀ (n : Nat) (i : usize) (done : Bool)
      (acc : alloc.vec.Vec u64 alloc.alloc.Global)
      (r : alloc.vec.Vec u64 alloc.alloc.Global),
      v.val.size - i.toNat ≤ n →
      i.toNat ≤ v.val.size →
      clever_119_maximum.insert_asc_at v x i done acc = RustM.ok r →
      sorted_asc acc.val →
      (∀ (k : Nat) (hk : k < acc.val.size) (hi_lt : i.toNat < v.val.size),
          (acc.val[k]'hk).toNat ≤ (v.val[i.toNat]'hi_lt).toNat) →
      (done = false →
          ∀ (k : Nat) (hk : k < acc.val.size), (acc.val[k]'hk).toNat ≤ x.toNat) →
      sorted_asc r.val := by
  intro n
  induction n with
  | zero =>
    intro i done acc r hm hi_le hres h_acc_sorted h_acc_le_vi h_acc_le_x
    have hi_ge : v.val.size ≤ i.toNat := by omega
    cases done with
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
    intro i done acc r hm hi_le hres h_acc_sorted h_acc_le_vi h_acc_le_x
    by_cases hi_ge : v.val.size ≤ i.toNat
    · cases done with
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
      cases done with
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
    (hres : clever_119_maximum.insert_asc v x = RustM.ok r)
    (h_v_sorted : sorted_asc v.val) :
    sorted_asc r.val := by
  unfold clever_119_maximum.insert_asc at hres
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
    clever_119_maximum.sort_at l i acc = RustM.ok acc := by
  unfold clever_119_maximum.sort_at
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
    clever_119_maximum.sort_at l i acc =
      (do
        let acc' ← clever_119_maximum.insert_asc acc (l.val[i.toNat]'hi)
        clever_119_maximum.sort_at l (i + 1) acc') := by
  conv => lhs; unfold clever_119_maximum.sort_at
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

/-! ## `sort_at` invariant: size + toList correctness.

The invariant states that `sort_at l i acc = ok r` implies
`r.val.toList = foldl insert_asc_list acc.val.toList (l.val.toList.drop i.toNat)`.

We use a different invariant that is more directly useful: we want
`r.val.toList` to equal the result of sorting prefix-by-prefix.

The cleanest bridge: any `sort_at l i acc = ok r` produces an `r.val.toList` that
is the FoldL of `insert_asc_list` starting from `acc.toList` over the suffix `l.toList.drop i`. -/

private def sort_aux : List u64 → List u64 → List u64
  | acc, [] => acc
  | acc, x :: xs => sort_aux (insert_asc_list acc x) xs

private theorem sort_aux_nil (acc : List u64) : sort_aux acc [] = acc := rfl

private theorem sort_aux_cons (acc : List u64) (x : u64) (xs : List u64) :
    sort_aux acc (x :: xs) = sort_aux (insert_asc_list acc x) xs := rfl

private theorem sort_at_inv :
    ∀ (n : Nat) (l : RustSlice u64) (i : usize)
      (acc : alloc.vec.Vec u64 alloc.alloc.Global)
      (r : alloc.vec.Vec u64 alloc.alloc.Global),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      clever_119_maximum.sort_at l i acc = RustM.ok r →
      r.val.size = acc.val.size + (l.val.size - i.toNat) ∧
      r.val.toList = sort_aux acc.val.toList (l.val.toList.drop i.toNat) := by
  intro n
  induction n with
  | zero =>
    intro l i acc r hm hi_le hres
    have hi_ge : l.val.size ≤ i.toNat := by omega
    have hi_eq : i.toNat = l.val.size := by omega
    rw [sort_at_oob l i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    refine ⟨?_, ?_⟩
    · rw [hi_eq]; omega
    · have h_drop_nil : l.val.toList.drop i.toNat = [] := by
        rw [hi_eq]; rw [List.drop_eq_nil_iff]; simp [Array.length_toList]
      rw [h_drop_nil]; rfl
  | succ n ih =>
    intro l i acc r hm hi_le hres
    by_cases hi_ge : l.val.size ≤ i.toNat
    · have hi_eq : i.toNat = l.val.size := by omega
      rw [sort_at_oob l i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      refine ⟨?_, ?_⟩
      · rw [hi_eq]; omega
      · have h_drop_nil : l.val.toList.drop i.toNat = [] := by
          rw [hi_eq]; rw [List.drop_eq_nil_iff]; simp [Array.length_toList]
        rw [h_drop_nil]; rfl
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_meas : l.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      have h_l_toList_length : l.val.toList.length = l.val.size := by simp [Array.length_toList]
      have h_drop_cons : l.val.toList.drop i.toNat
                          = (l.val[i.toNat]'hi_lt) :: l.val.toList.drop (i.toNat + 1) := by
        have h_len_lt : i.toNat < l.val.toList.length := by rw [h_l_toList_length]; exact hi_lt
        rw [List.drop_eq_getElem_cons h_len_lt, Array.getElem_toList]; rfl
      rw [sort_at_step l i acc hi_lt] at hres
      generalize h_ins : clever_119_maximum.insert_asc acc (l.val[i.toNat]'hi_lt) = ins_res at hres
      cases ins_res with
      | none =>
        exfalso
        have hh : (do let acc' ← (none : RustM (alloc.vec.Vec u64 alloc.alloc.Global));
                       clever_119_maximum.sort_at l (i + 1) acc')
                  = RustM.ok r := hres
        cases hh
      | some res' =>
        cases res' with
        | error e =>
          exfalso
          have hh : (do let acc' ← (some (Except.error e) :
                                      RustM (alloc.vec.Vec u64 alloc.alloc.Global));
                         clever_119_maximum.sort_at l (i + 1) acc')
                    = RustM.ok r := hres
          cases hh
        | ok acc' =>
          have h_ins_ok : clever_119_maximum.insert_asc acc (l.val[i.toNat]'hi_lt) = RustM.ok acc' := h_ins
          simp only [RustM_ok_bind] at hres
          have h_ins_inv := insert_asc_inv acc (l.val[i.toNat]'hi_lt) acc' h_ins_ok
          obtain ⟨h_acc'_size, h_acc'_toList⟩ := h_ins_inv
          have ih_app := ih l (i + 1) acc' r h_meas h_i1_le hres
          rw [h_i1] at ih_app
          obtain ⟨h_size_eq, h_toList_eq⟩ := ih_app
          rw [h_acc'_size] at h_size_eq
          rw [h_acc'_toList] at h_toList_eq
          refine ⟨?_, ?_⟩
          · rw [h_size_eq]; omega
          · rw [h_toList_eq]
            rw [h_drop_cons]
            rw [sort_aux_cons]

/-- `sort_at` produces a sorted output. -/
private theorem sort_at_sorted :
    ∀ (n : Nat) (l : RustSlice u64)
      (i : usize) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
      (r : alloc.vec.Vec u64 alloc.alloc.Global),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      clever_119_maximum.sort_at l i acc = RustM.ok r →
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
      generalize h_ins : clever_119_maximum.insert_asc acc (l.val[i.toNat]'hi_lt) = ins_res at hres
      cases ins_res with
      | none =>
        exfalso
        have hh : (do let acc' ← (none : RustM (alloc.vec.Vec u64 alloc.alloc.Global));
                       clever_119_maximum.sort_at l (i + 1) acc')
                  = RustM.ok r := hres
        cases hh
      | some res' =>
        cases res' with
        | error e =>
          exfalso
          have hh : (do let acc' ← (some (Except.error e) :
                                      RustM (alloc.vec.Vec u64 alloc.alloc.Global));
                         clever_119_maximum.sort_at l (i + 1) acc')
                    = RustM.ok r := hres
          cases hh
        | ok acc' =>
          have h_ins_ok : clever_119_maximum.insert_asc acc (l.val[i.toNat]'hi_lt) = RustM.ok acc' := h_ins
          simp only [RustM_ok_bind] at hres
          have h_acc'_sorted : sorted_asc acc'.val :=
            insert_asc_sorted acc (l.val[i.toNat]'hi_lt) acc' h_ins_ok h_acc_sorted
          exact ih l (i + 1) acc' r h_meas h_i1_le hres h_acc'_sorted

/-! ## Bridging `sort_aux [] xs = sort_asc_list xs`.

`sort_aux acc xs` folds insertion sort from the LEFT (processing xs head-first into acc),
while `sort_asc_list xs` recurses from the RIGHT (sort tail, then insert head).
Both compute the same permutation. We prove this via two lemmas:
(a) `sort_aux acc xs ≡ insert all of xs into acc, in some order` — formally:
    `insert_asc_list_commute`: order of two insertions into a sorted list does not matter;
(b) `sort_asc_list (xs ++ [y]) = insert_asc_list (sort_asc_list xs) y` — derived from (a).

The actual statement we need is `sort_aux [] xs = sort_asc_list xs`, which follows
from a tail-cum-head reformulation. -/

/-- Insertion into the empty list yields a singleton. -/
private theorem insert_asc_list_nil (x : u64) :
    insert_asc_list [] x = [x] := rfl

/-- Two insertions commute on any list. -/
private theorem insert_asc_list_comm (xs : List u64) (a b : u64) :
    insert_asc_list (insert_asc_list xs a) b = insert_asc_list (insert_asc_list xs b) a := by
  induction xs with
  | nil =>
    by_cases hab : a ≤ b
    · by_cases hba : b ≤ a
      · have h_eq : a = b := UInt64.le_antisymm hab hba
        subst h_eq; rfl
      · simp only [insert_asc_list, if_pos hab, if_neg hba]
    · have hba : b ≤ a := by
        rw [UInt64.le_iff_toNat_le]
        rw [UInt64.le_iff_toNat_le] at hab
        omega
      have hab' : ¬ a ≤ b := hab
      simp only [insert_asc_list, if_pos hba, if_neg hab']
  | cons y ys ih =>
    by_cases hay : a ≤ y
    · by_cases hby : b ≤ y
      · -- both ≤ y
        by_cases hab : a ≤ b
        · by_cases hba : b ≤ a
          · have h_eq : a = b := UInt64.le_antisymm hab hba
            subst h_eq; rfl
          · -- a < b: top-level insert b into (a :: y :: ys), b ≤ a is false.
            simp only [insert_asc_list, if_pos hay, if_pos hby, if_neg hba, if_pos hab]
        · -- ¬ a ≤ b: then b ≤ a
          have hba : b ≤ a := by
            rw [UInt64.le_iff_toNat_le]
            rw [UInt64.le_iff_toNat_le] at hab
            omega
          have hab' : ¬ a ≤ b := hab
          simp only [insert_asc_list, if_pos hay, if_pos hby, if_pos hba, if_neg hab']
      · -- a ≤ y, ¬ b ≤ y → a < b
        have hab : a ≤ b := by
          rw [UInt64.le_iff_toNat_le]
          rw [UInt64.le_iff_toNat_le] at hay
          have hby_gt : ¬ b ≤ y := hby
          rw [UInt64.le_iff_toNat_le] at hby_gt
          omega
        have hba : ¬ b ≤ a := by
          intro h
          have h_eq : a = b := UInt64.le_antisymm hab h
          subst h_eq
          exact hby hay
        simp only [insert_asc_list, if_pos hay, if_neg hby, if_neg hba, if_pos hay, if_neg hby]
    · by_cases hby : b ≤ y
      · -- ¬ a ≤ y, b ≤ y → b < a
        have hba : b ≤ a := by
          have hay_gt : ¬ a ≤ y := hay
          rw [UInt64.le_iff_toNat_le]
          rw [UInt64.le_iff_toNat_le] at hay_gt
          rw [UInt64.le_iff_toNat_le] at hby
          omega
        have hab : ¬ a ≤ b := by
          intro h
          have h_eq : a = b := UInt64.le_antisymm h hba
          subst h_eq
          exact hay hby
        simp only [insert_asc_list, if_neg hay, if_pos hby, if_pos hba, if_neg hab,
                   if_neg hay, if_pos hby]
      · -- ¬ a ≤ y, ¬ b ≤ y: recurse via ih
        simp only [insert_asc_list, if_neg hay, if_neg hby]
        rw [ih]

/-- `sort_asc_list (xs ++ [y]) = insert_asc_list (sort_asc_list xs) y` via commutativity. -/
private theorem sort_asc_list_append_singleton (xs : List u64) (y : u64) :
    sort_asc_list (xs ++ [y]) = insert_asc_list (sort_asc_list xs) y := by
  induction xs with
  | nil =>
    show insert_asc_list (sort_asc_list []) y = insert_asc_list (sort_asc_list []) y
    rfl
  | cons x xs ih =>
    show insert_asc_list (sort_asc_list (xs ++ [y])) x
        = insert_asc_list (insert_asc_list (sort_asc_list xs) x) y
    rw [ih]
    exact insert_asc_list_comm _ y x

/-- `sort_aux acc xs = sort_asc_list (acc.reverse ++ xs)`?

Actually the cleaner statement: `sort_aux acc xs = sort_aux (insert_asc_list acc x) xs'`
where we've already inserted `x`. We want a foldl-like statement.

Better approach: prove `sort_aux acc xs = foldl insert_asc_list acc xs` (definitional)
and then use a fold-reverse trick.

For the bridge to sort_asc_list, we use:
`sort_aux [] (xs ++ [y]) = insert_asc_list (sort_aux [] xs) y`.

Then by induction, `sort_aux [] xs = sort_asc_list xs`. -/

private theorem sort_aux_append (acc : List u64) (xs : List u64) (y : u64) :
    sort_aux acc (xs ++ [y]) = insert_asc_list (sort_aux acc xs) y := by
  induction xs generalizing acc with
  | nil =>
    show sort_aux acc [y] = insert_asc_list (sort_aux acc []) y
    show sort_aux (insert_asc_list acc y) [] = insert_asc_list acc y
    rfl
  | cons x xs ih =>
    show sort_aux acc (x :: (xs ++ [y])) = insert_asc_list (sort_aux acc (x :: xs)) y
    rw [sort_aux_cons, sort_aux_cons]
    exact ih (insert_asc_list acc x)

/-- The bridge: `sort_aux [] xs = sort_asc_list xs` proved by strong induction on length. -/
private theorem sort_aux_nil_eq_sort_asc_list_aux :
    ∀ (n : Nat) (xs : List u64), xs.length = n → sort_aux [] xs = sort_asc_list xs := by
  intro n
  induction n with
  | zero =>
    intro xs h
    have h_nil : xs = [] := List.length_eq_zero_iff.mp h
    subst h_nil; rfl
  | succ n ih =>
    intro xs h
    have h_ne : xs ≠ [] := by
      intro h'; subst h'; simp at h
    have h_split : xs = xs.dropLast ++ [xs.getLast h_ne] :=
      (List.dropLast_concat_getLast h_ne).symm
    have h_len_dl : xs.dropLast.length = n := by
      have hh : xs.dropLast.length = xs.length - 1 := List.length_dropLast
      rw [h] at hh; omega
    have ih_app := ih xs.dropLast h_len_dl
    rw [h_split, sort_aux_append, ih_app, sort_asc_list_append_singleton]

private theorem sort_aux_nil_eq_sort_asc_list (xs : List u64) :
    sort_aux [] xs = sort_asc_list xs :=
  sort_aux_nil_eq_sort_asc_list_aux xs.length xs rfl

/-! ## `tail_from` OOB + step + fail lemmas.

`tail_from s start acc` copies `s[start..]` into `acc`. Same shape as `reverse_at` from
the clever_087 reference, but the index pushed is `s[start]` directly (no `n - 1 - i` arithmetic). -/

private theorem tail_from_oob (s : RustSlice u64) (start : usize)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : s.val.size ≤ start.toNat) :
    clever_119_maximum.tail_from s start acc = RustM.ok acc := by
  unfold clever_119_maximum.tail_from
  have h_ofNat : (USize64.ofNat s.val.size).toNat = s.val.size :=
    USize64.toNat_ofNat_of_lt' s.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat s.val.size ≤ start) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

private theorem tail_from_step (s : RustSlice u64) (start : usize)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : start.toNat < s.val.size)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_119_maximum.tail_from s start acc =
      clever_119_maximum.tail_from s (start + 1)
        (push_one acc (s.val[start.toNat]'hi) h_acc) := by
  conv => lhs; unfold clever_119_maximum.tail_from
  have h_size_lt : s.val.size < USize64.size := s.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : start.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat s.val.size).toNat = s.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat s.val.size ≤ start) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (s[start]_? : RustM u64) = RustM.ok (s.val[start.toNat]'hi) := by
    show (if h : start.toNat < s.val.size then pure (s.val[start])
            else .fail .arrayOutOfBounds)
        = RustM.ok (s.val[start.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_add : (start +? (1 : usize) : RustM usize) = RustM.ok (start + 1) :=
    usize_add_one_ok start h_no_ov_i
  have h_app_size :
      acc.val.size + (#[s.val[start.toNat]'hi] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  have h_extend :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[s.val[start.toNat]'hi], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.ok (push_one acc (s.val[start.toNat]'hi) h_acc) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[s.val[start.toNat]'hi] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[s.val[start.toNat]'hi], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend]
  simp only [RustM_ok_bind]
  rw [h_add]
  simp only [RustM_ok_bind]

private theorem tail_from_step_size_fail (s : RustSlice u64) (start : usize)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : start.toNat < s.val.size)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_119_maximum.tail_from s start acc = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_119_maximum.tail_from
  have h_size_lt : s.val.size < USize64.size := s.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat s.val.size).toNat = s.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat s.val.size ≤ start) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (s[start]_? : RustM u64) = RustM.ok (s.val[start.toNat]'hi) := by
    show (if h : start.toNat < s.val.size then pure (s.val[start])
            else .fail .arrayOutOfBounds)
        = RustM.ok (s.val[start.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_app_size_neg :
      ¬ acc.val.size + (#[s.val[start.toNat]'hi] : Array u64).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[s.val[start.toNat]'hi], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[s.val[start.toNat]'hi] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[s.val[start.toNat]'hi], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

/-! ## `tail_from` invariants: size + toList + sortedness. -/

/-- `tail_from s start acc` produces a result of size `acc.size + (s.size - start)` with toList
    being `acc.toList ++ s.toList.drop start`. -/
private theorem tail_from_inv :
    ∀ (n : Nat) (s : RustSlice u64) (start : usize)
      (acc : alloc.vec.Vec u64 alloc.alloc.Global)
      (r : alloc.vec.Vec u64 alloc.alloc.Global),
      s.val.size - start.toNat ≤ n →
      start.toNat ≤ s.val.size →
      clever_119_maximum.tail_from s start acc = RustM.ok r →
      r.val.size = acc.val.size + (s.val.size - start.toNat) ∧
      r.val.toList = acc.val.toList ++ s.val.toList.drop start.toNat := by
  intro n
  induction n with
  | zero =>
    intro s start acc r hm hi_le hres
    have hi_ge : s.val.size ≤ start.toNat := by omega
    have hi_eq : start.toNat = s.val.size := by omega
    rw [tail_from_oob s start acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    refine ⟨?_, ?_⟩
    · rw [hi_eq]; omega
    · have h_drop_nil : s.val.toList.drop start.toNat = [] := by
        rw [hi_eq]; rw [List.drop_eq_nil_iff]; simp [Array.length_toList]
      rw [h_drop_nil]; simp
  | succ n ih =>
    intro s start acc r hm hi_le hres
    by_cases hi_ge : s.val.size ≤ start.toNat
    · have hi_eq : start.toNat = s.val.size := by omega
      rw [tail_from_oob s start acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      refine ⟨?_, ?_⟩
      · rw [hi_eq]; omega
      · have h_drop_nil : s.val.toList.drop start.toNat = [] := by
          rw [hi_eq]; rw [List.drop_eq_nil_iff]; simp [Array.length_toList]
        rw [h_drop_nil]; simp
    · have hi_lt : start.toNat < s.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : s.val.size < USize64.size := s.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : start.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (start + 1).toNat = start.toNat + 1 := usize_add_one_toNat start h_no_ov_i
      have h_i1_le : (start + 1).toNat ≤ s.val.size := by rw [h_i1]; omega
      have h_meas : s.val.size - (start + 1).toNat ≤ n := by rw [h_i1]; omega
      have h_s_toList_length : s.val.toList.length = s.val.size := by simp [Array.length_toList]
      have h_drop_cons : s.val.toList.drop start.toNat
                          = (s.val[start.toNat]'hi_lt) :: s.val.toList.drop (start.toNat + 1) := by
        have h_len_lt : start.toNat < s.val.toList.length := by
          rw [h_s_toList_length]; exact hi_lt
        rw [List.drop_eq_getElem_cons h_len_lt, Array.getElem_toList]; rfl
      by_cases h_acc : acc.val.size + 1 < USize64.size
      · rw [tail_from_step s start acc hi_lt h_acc] at hres
        have h_push_size :
            (push_one acc (s.val[start.toNat]'hi_lt) h_acc).val.size = acc.val.size + 1 := by
          show (acc.val ++ #[_]).size = acc.val.size + 1
          rw [Array.size_append]; rfl
        have h_push_toList :
            (push_one acc (s.val[start.toNat]'hi_lt) h_acc).val.toList
              = acc.val.toList ++ [s.val[start.toNat]'hi_lt] := by
          show (acc.val ++ #[_]).toList = _
          simp [Array.toList_append]
        have ih_app := ih s (start + 1) _ r h_meas h_i1_le hres
        rw [h_i1] at ih_app
        rw [h_push_size] at ih_app
        rw [h_push_toList] at ih_app
        obtain ⟨h_size_eq, h_toList_eq⟩ := ih_app
        refine ⟨?_, ?_⟩
        · rw [h_size_eq]; omega
        · rw [h_toList_eq, h_drop_cons]
          simp [List.append_assoc]
      · exfalso
        have h_big : USize64.size ≤ acc.val.size + 1 := by omega
        rw [tail_from_step_size_fail s start acc hi_lt h_big] at hres
        cases hres

/-- `tail_from` from a sorted slice produces a sorted result, when acc is already sorted
    and every acc element is ≤ s[start] (the next element pushed). -/
private theorem tail_from_sorted (s : RustSlice u64) (h_s_sorted : sorted_asc s.val) :
    ∀ (n : Nat) (start : usize) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
      (r : alloc.vec.Vec u64 alloc.alloc.Global),
      s.val.size - start.toNat ≤ n →
      start.toNat ≤ s.val.size →
      clever_119_maximum.tail_from s start acc = RustM.ok r →
      sorted_asc acc.val →
      (∀ (k : Nat) (hk : k < acc.val.size) (hi_lt : start.toNat < s.val.size),
          (acc.val[k]'hk).toNat ≤ (s.val[start.toNat]'hi_lt).toNat) →
      sorted_asc r.val := by
  intro n
  induction n with
  | zero =>
    intro start acc r hm hi_le hres h_acc_sorted h_acc_le_s
    have hi_ge : s.val.size ≤ start.toNat := by omega
    rw [tail_from_oob s start acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    exact h_acc_sorted
  | succ n ih =>
    intro start acc r hm hi_le hres h_acc_sorted h_acc_le_s
    by_cases hi_ge : s.val.size ≤ start.toNat
    · rw [tail_from_oob s start acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      exact h_acc_sorted
    · have hi_lt : start.toNat < s.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : s.val.size < USize64.size := s.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : start.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (start + 1).toNat = start.toNat + 1 := usize_add_one_toNat start h_no_ov_i
      have h_i1_le : (start + 1).toNat ≤ s.val.size := by rw [h_i1]; omega
      have h_meas : s.val.size - (start + 1).toNat ≤ n := by rw [h_i1]; omega
      by_cases h_acc : acc.val.size + 1 < USize64.size
      · rw [tail_from_step s start acc hi_lt h_acc] at hres
        have h_new_sorted : sorted_asc (acc.val ++ #[s.val[start.toNat]'hi_lt]) := by
          apply sorted_asc_append_singleton acc.val (s.val[start.toNat]'hi_lt) h_acc_sorted
          intro k hk; exact h_acc_le_s k hk hi_lt
        have h_new_le_s :
            ∀ (k : Nat) (hk : k < (acc.val ++ #[s.val[start.toNat]'hi_lt]).size)
              (hi_i1 : (start + 1).toNat < s.val.size),
              ((acc.val ++ #[s.val[start.toNat]'hi_lt])[k]'hk).toNat
                ≤ (s.val[(start + 1).toNat]'hi_i1).toNat := by
          intro k hk hi_i1
          rw [Array.size_append] at hk
          have h_one : (#[s.val[start.toNat]'hi_lt] : Array u64).size = 1 := rfl
          have h_v_step : (s.val[start.toNat]'hi_lt).toNat ≤ (s.val[(start + 1).toNat]'hi_i1).toNat := by
            have h_le : start.toNat ≤ (start + 1).toNat := by rw [h_i1]; omega
            exact h_s_sorted start.toNat (start + 1).toNat hi_lt hi_i1 h_le
          by_cases h_k_lt : k < acc.val.size
          · rw [Array.getElem_append_left h_k_lt]
            have h_acc_k := h_acc_le_s k h_k_lt hi_lt
            omega
          · have h_k_ge : acc.val.size ≤ k := by omega
            rw [Array.getElem_append_right h_k_ge]
            have h_idx : k - acc.val.size = 0 := by omega
            have h_zero_lt : (0 : Nat) < (#[s.val[start.toNat]'hi_lt] : Array u64).size := by
              rw [h_one]; omega
            rw [show ((#[s.val[start.toNat]'hi_lt] : Array u64)[k - acc.val.size]'(by rw [h_idx]; exact h_zero_lt))
                    = (#[s.val[start.toNat]'hi_lt] : Array u64)[0]'h_zero_lt from by simp [h_idx]]
            exact h_v_step
        exact ih (start + 1) _ r h_meas h_i1_le hres h_new_sorted h_new_le_s
      · exfalso
        have h_big : USize64.size ≤ acc.val.size + 1 := by omega
        rw [tail_from_step_size_fail s start acc hi_lt h_big] at hres
        cases hres

/-! ## Top-level wrapper helpers. -/

/-- `is_empty` evaluates to `RustM.ok (decide (arr.val.size = 0))`. -/
private theorem is_empty_eq (arr : RustSlice u64) :
    (core_models.slice.Impl.is_empty u64 arr : RustM Bool)
      = RustM.ok (decide (arr.val.size = 0)) := by
  unfold core_models.slice.Impl.is_empty
  have h_len : (core_models.slice.Impl.len u64 arr : RustM usize)
                = RustM.ok (USize64.ofNat arr.val.size) := rfl
  have h_ofNat : (USize64.ofNat arr.val.size).toNat = arr.val.size :=
    USize64.toNat_ofNat_of_lt' arr.size_lt_usizeSize
  rw [h_len]
  simp only [RustM_ok_bind]
  show (USize64.ofNat arr.val.size ==? (0 : usize) : RustM Bool) = _
  show pure (USize64.ofNat arr.val.size == (0 : usize) : Bool) = _
  have h_eq : (USize64.ofNat arr.val.size == (0 : usize) : Bool)
                = decide (arr.val.size = 0) := by
    by_cases h : arr.val.size = 0
    · have h_us : USize64.ofNat arr.val.size = (0 : usize) := by
        apply USize64.toNat_inj.mp
        rw [h_ofNat]; exact h
      rw [h_us]; simp [h]
    · have h_us_ne : USize64.ofNat arr.val.size ≠ (0 : usize) := by
        intro hus
        apply h
        have := congrArg USize64.toNat hus
        rw [h_ofNat] at this
        exact this
      simp [h_us_ne, h]
  rw [h_eq]; rfl

/-- `(k ==? (0 : u64))` evaluates to `RustM.ok (k == 0)`. -/
private theorem u64_beq_zero_eq (k : u64) :
    (k ==? (0 : u64) : RustM Bool) = RustM.ok (k == 0) := rfl

/-- For `(k ==? 0)` when `k = 0`. -/
private theorem u64_beq_zero_of_zero :
    ((0 : u64) ==? (0 : u64) : RustM Bool) = RustM.ok true := rfl

/-- For `(k ==? 0)` when `k ≠ 0`. -/
private theorem u64_beq_zero_of_ne (k : u64) (hk : k ≠ 0) :
    (k ==? (0 : u64) : RustM Bool) = RustM.ok false := by
  show pure (k == (0 : u64)) = _
  rw [show (k == (0 : u64)) = false from by
    have : ¬ (k = (0 : u64)) := hk
    simp [this]]
  rfl

/-- `cast_op` from `usize` to `u64` is `USize64.toUInt64`. -/
private theorem cast_usize_to_u64 (a : usize) :
    (rust_primitives.hax.cast_op a : RustM u64) = RustM.ok (USize64.toUInt64 a) := rfl

/-- `cast_op` from `u64` to `usize` is `UInt64.toUSize64`. -/
private theorem cast_u64_to_usize (a : u64) :
    (rust_primitives.hax.cast_op a : RustM usize) = RustM.ok (UInt64.toUSize64 a) := rfl

/-- `(k >=? n)` evaluates as a comparison on u64. -/
private theorem u64_geq (k n : u64) :
    (k >=? n : RustM Bool) = RustM.ok (decide (n ≤ k)) := by
  show pure (decide (n ≤ k)) = _
  rfl

/-- Internal lemma: when `k = 0` the wrapper returns an empty Vec. -/
private theorem maximum_zero_k_eq (arr : RustSlice u64) :
    clever_119_maximum.maximum arr (0 : u64) = RustM.ok ⟨(List.nil).toArray, by grind⟩ := by
  unfold clever_119_maximum.maximum
  rw [u64_beq_zero_of_zero]
  simp only [RustM_ok_bind]
  rw [is_empty_eq]
  simp only [RustM_ok_bind]
  show (rust_primitives.hax.logical_op.or true _ : RustM Bool) >>= _ = _
  show pure (true || _ : Bool) >>= _ = _
  simp only [Bool.true_or, RustM_ok_bind, if_pos rfl]
  rfl

/-- Internal lemma: when `arr` is empty, the wrapper returns an empty Vec. -/
private theorem maximum_empty_arr_eq (arr : RustSlice u64) (k : u64) (hempty : arr.val.size = 0) :
    clever_119_maximum.maximum arr k = RustM.ok ⟨(List.nil).toArray, by grind⟩ := by
  unfold clever_119_maximum.maximum
  rw [u64_beq_zero_eq, is_empty_eq]
  simp only [RustM_ok_bind, decide_eq_true hempty]
  show (rust_primitives.hax.logical_op.or _ true : RustM Bool) >>= _ = _
  show pure (_ || true : Bool) >>= _ = _
  simp only [Bool.or_true, RustM_ok_bind, if_pos rfl]
  rfl

theorem maximum_zero_k_returns_empty
    (arr : RustSlice u64) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_119_maximum.maximum arr (0 : u64) = RustM.ok v ∧
      v.val.size = 0 := by
  refine ⟨⟨(List.nil).toArray, by grind⟩, ?_, ?_⟩
  · exact maximum_zero_k_eq arr
  · rfl

theorem maximum_empty_arr_returns_empty
    (arr : RustSlice u64) (k : u64) (hempty : arr.val.size = 0) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_119_maximum.maximum arr k = RustM.ok v ∧
      v.val.size = 0 := by
  refine ⟨⟨(List.nil).toArray, by grind⟩, ?_, ?_⟩
  · exact maximum_empty_arr_eq arr k hempty
  · rfl

/-- USize64.toUInt64 (USize64.ofNat n) = UInt64.ofNat n when n < 2^64. -/
private theorem usize_ofNat_toUInt64 (n : Nat) (h : n < 2^64) :
    USize64.toUInt64 (USize64.ofNat n) = UInt64.ofNat n := by
  show (USize64.ofNat n).toNat.toUInt64 = UInt64.ofNat n
  rw [USize64.toNat_ofNat_of_lt' (by show n < USize64.size; rw [usize_size_eq]; exact h)]

/-- UInt64.toUSize64 a = USize64.ofNat a.toNat. -/
private theorem u64_toUSize64_eq (a : u64) :
    UInt64.toUSize64 a = USize64.ofNat a.toNat := rfl

/-- The main reduction lemma: assuming the sort succeeds with `sorted`, the wrapper reduces to
    a `tail_from sorted start []` call. -/
private theorem maximum_eval_nonempty
    (arr : RustSlice u64) (k : u64)
    (hk_ne : k ≠ 0) (hne : 0 < arr.val.size)
    (sorted : alloc.vec.Vec u64 alloc.alloc.Global)
    (h_sort_ok :
      clever_119_maximum.sort_at arr (0 : usize) ⟨(List.nil).toArray, by grind⟩
        = RustM.ok sorted) :
    clever_119_maximum.maximum arr k =
      clever_119_maximum.tail_from sorted
        (if (UInt64.ofNat sorted.val.size) ≤ k then (0 : usize)
         else USize64.ofNat (sorted.val.size - k.toNat))
        ⟨(List.nil).toArray, by grind⟩ := by
  unfold clever_119_maximum.maximum
  rw [u64_beq_zero_of_ne k hk_ne, is_empty_eq]
  have hempty_ne : arr.val.size ≠ 0 := by omega
  simp only [RustM_ok_bind, decide_eq_false hempty_ne,
             rust_primitives.hax.logical_op.or, Bool.or_self, pure_bind,
             Bool.false_eq_true, ↓reduceIte]
  have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new]
  simp only [RustM_ok_bind]
  rw [h_sort_ok]
  simp only [RustM_ok_bind]
  have h_len : (alloc.vec.Impl_1.len u64 alloc.alloc.Global sorted : RustM usize)
                = RustM.ok (USize64.ofNat sorted.val.size) := rfl
  rw [h_len]
  simp only [RustM_ok_bind]
  rw [cast_usize_to_u64]
  simp only [RustM_ok_bind]
  have h_size_lt : sorted.val.size < USize64.size := sorted.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_sorted_size_lt : sorted.val.size < 2^64 := by rw [h_usize_size] at h_size_lt; exact h_size_lt
  rw [usize_ofNat_toUInt64 sorted.val.size h_sorted_size_lt]
  rw [u64_geq]
  simp only [RustM_ok_bind]
  have h_n_toNat : (UInt64.ofNat sorted.val.size).toNat = sorted.val.size :=
    UInt64.toNat_ofNat_of_lt' (by show sorted.val.size < UInt64.size; exact h_sorted_size_lt)
  have h_deref :
      (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u64 alloc.alloc.Global) sorted : RustM _) = RustM.ok sorted := rfl
  by_cases h_ge : (UInt64.ofNat sorted.val.size) ≤ k
  · rw [if_pos h_ge]
    rw [show decide ((UInt64.ofNat sorted.val.size) ≤ k) = true from decide_eq_true h_ge]
    simp only [↓reduceIte, pure_bind]
    rw [h_deref]
    simp only [RustM_ok_bind]
  · rw [if_neg h_ge]
    rw [show decide ((UInt64.ofNat sorted.val.size) ≤ k) = false from decide_eq_false h_ge]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have h_kn : k.toNat < (UInt64.ofNat sorted.val.size).toNat := by
      have h_nk_le_lt : ¬ (UInt64.ofNat sorted.val.size) ≤ k := h_ge
      rw [UInt64.le_iff_toNat_le] at h_nk_le_lt
      omega
    have h_sub_ok : ((UInt64.ofNat sorted.val.size) -? k : RustM u64)
                      = RustM.ok ((UInt64.ofNat sorted.val.size) - k) :=
      u64_sub_ok _ k (Nat.le_of_lt h_kn)
    rw [h_sub_ok]
    simp only [RustM_ok_bind]
    rw [cast_u64_to_usize]
    simp only [RustM_ok_bind]
    rw [h_deref]
    simp only [RustM_ok_bind]
    have h_sub_toNat : ((UInt64.ofNat sorted.val.size) - k).toNat = sorted.val.size - k.toNat := by
      rw [u64_sub_toNat _ k (Nat.le_of_lt h_kn), h_n_toNat]
    rw [u64_toUSize64_eq, h_sub_toNat]

/-- Extract sort_at and tail_from successes from a `maximum arr k = ok v` result. -/
private theorem maximum_decompose
    (arr : RustSlice u64) (k : u64) (hk_ne : k ≠ 0) (hne : 0 < arr.val.size)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_119_maximum.maximum arr k = RustM.ok v) :
    ∃ sorted : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_119_maximum.sort_at arr (0 : usize) ⟨(List.nil).toArray, by grind⟩
        = RustM.ok sorted ∧
      clever_119_maximum.tail_from sorted
        (if (UInt64.ofNat sorted.val.size) ≤ k then (0 : usize)
         else USize64.ofNat (sorted.val.size - k.toNat))
        ⟨(List.nil).toArray, by grind⟩
        = RustM.ok v := by
  -- Step 1: extract sort_at success
  have hempty_ne : arr.val.size ≠ 0 := by omega
  unfold clever_119_maximum.maximum at hres
  rw [u64_beq_zero_of_ne k hk_ne, is_empty_eq] at hres
  simp only [RustM_ok_bind, decide_eq_false hempty_ne,
             rust_primitives.hax.logical_op.or, Bool.or_self, pure_bind,
             Bool.false_eq_true, ↓reduceIte] at hres
  have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  generalize h_sort : clever_119_maximum.sort_at arr (0 : usize) ⟨(List.nil).toArray, by grind⟩
                          = sa_res at hres
  cases sa_res with
  | none => exfalso; cases hres
  | some res' =>
    cases res' with
    | error e => exfalso; cases hres
    | ok sorted =>
      refine ⟨sorted, rfl, ?_⟩
      have h_eval := maximum_eval_nonempty arr k hk_ne hne sorted h_sort
      unfold clever_119_maximum.maximum at h_eval
      rw [u64_beq_zero_of_ne k hk_ne, is_empty_eq] at h_eval
      simp only [RustM_ok_bind, decide_eq_false hempty_ne,
                 rust_primitives.hax.logical_op.or, Bool.or_self, pure_bind,
                 Bool.false_eq_true, ↓reduceIte] at h_eval
      rw [h_new] at h_eval
      simp only [RustM_ok_bind] at h_eval
      rw [h_sort] at h_eval
      simp only [RustM_ok_bind] at h_eval
      rw [← h_eval]
      -- hres has form: do { ... rest } = RustM.ok v
      -- after our rewrites, both sides have the same do-block prefix; the rest matches.
      exact hres

/-! ## Length, sortedness, and content obligations (universal: no `k = 0` / empty preconditions). -/

theorem maximum_length_is_min_k_arr_size
    (arr : RustSlice u64) (k : u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_119_maximum.maximum arr k = RustM.ok v) :
    v.val.size = min k.toNat arr.val.size := by
  by_cases hk : k = 0
  · subst hk
    rw [maximum_zero_k_eq arr] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    show 0 = min 0 arr.val.size
    simp
  · by_cases hempty : arr.val.size = 0
    · rw [maximum_empty_arr_eq arr k hempty] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      show 0 = min k.toNat arr.val.size
      rw [hempty]; simp
    · have hne : 0 < arr.val.size := by omega
      obtain ⟨sorted, h_sort_ok, h_tail_ok⟩ := maximum_decompose arr k hk hne v hres
      -- size of sorted = arr.size
      have h_zero_toNat : (0 : usize).toNat = 0 := rfl
      have h_meas : arr.val.size - (0 : usize).toNat ≤ arr.val.size := by rw [h_zero_toNat]; omega
      have h_le : (0 : usize).toNat ≤ arr.val.size := by rw [h_zero_toNat]; omega
      have h_sort_inv := sort_at_inv arr.val.size arr (0 : usize)
        ⟨(List.nil).toArray, by grind⟩ sorted h_meas h_le h_sort_ok
      obtain ⟨h_sorted_size, _⟩ := h_sort_inv
      have h_empty_size : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size = 0 := rfl
      rw [h_empty_size, h_zero_toNat] at h_sorted_size
      have h_sorted_size' : sorted.val.size = arr.val.size := by rw [h_sorted_size]; omega
      -- Now case on (UInt64.ofNat sorted.val.size) ≤ k
      have h_sorted_size_lt : sorted.val.size < 2^64 := by
        have h_size_lt : sorted.val.size < USize64.size := sorted.size_lt_usizeSize
        rw [usize_size_eq] at h_size_lt; exact h_size_lt
      have h_n_toNat : (UInt64.ofNat sorted.val.size).toNat = sorted.val.size :=
        UInt64.toNat_ofNat_of_lt' (by show sorted.val.size < UInt64.size; exact h_sorted_size_lt)
      by_cases h_ge : (UInt64.ofNat sorted.val.size) ≤ k
      · -- start = 0; tail_from gives the whole sorted slice
        rw [if_pos h_ge] at h_tail_ok
        have h_tail_inv := tail_from_inv sorted.val.size sorted (0 : usize)
          ⟨(List.nil).toArray, by grind⟩ v (by rw [h_zero_toNat]; omega)
          (by rw [h_zero_toNat]; omega) h_tail_ok
        obtain ⟨h_v_size, _⟩ := h_tail_inv
        rw [h_empty_size, h_zero_toNat] at h_v_size
        rw [h_v_size]
        have h_kn : sorted.val.size ≤ k.toNat := by
          rw [UInt64.le_iff_toNat_le] at h_ge
          rw [h_n_toNat] at h_ge
          exact h_ge
        rw [h_sorted_size']
        rw [show min k.toNat arr.val.size = arr.val.size from by
          rw [← h_sorted_size']
          exact Nat.min_eq_right h_kn]
        omega
      · rw [if_neg h_ge] at h_tail_ok
        have h_start_toNat : (USize64.ofNat (sorted.val.size - k.toNat)).toNat
                              = sorted.val.size - k.toNat := by
          apply USize64.toNat_ofNat_of_lt'
          show sorted.val.size - k.toNat < USize64.size
          rw [usize_size_eq]
          have : sorted.val.size - k.toNat ≤ sorted.val.size := Nat.sub_le _ _
          omega
        have h_start_le : (USize64.ofNat (sorted.val.size - k.toNat)).toNat ≤ sorted.val.size := by
          rw [h_start_toNat]; exact Nat.sub_le _ _
        have h_meas' : sorted.val.size - (USize64.ofNat (sorted.val.size - k.toNat)).toNat ≤ sorted.val.size := by
          rw [h_start_toNat]; omega
        have h_tail_inv := tail_from_inv sorted.val.size sorted
          (USize64.ofNat (sorted.val.size - k.toNat))
          ⟨(List.nil).toArray, by grind⟩ v h_meas' h_start_le h_tail_ok
        obtain ⟨h_v_size, _⟩ := h_tail_inv
        rw [h_empty_size, h_start_toNat] at h_v_size
        rw [h_v_size]
        -- v.size = 0 + (sorted.size - (sorted.size - k.toNat)) = k.toNat (if k.toNat ≤ sorted.size)
        have h_kn : k.toNat < sorted.val.size := by
          have h_nk_le_lt : ¬ (UInt64.ofNat sorted.val.size) ≤ k := h_ge
          rw [UInt64.le_iff_toNat_le] at h_nk_le_lt
          rw [h_n_toNat] at h_nk_le_lt
          omega
        rw [h_sorted_size']
        rw [show min k.toNat arr.val.size = k.toNat from
          Nat.min_eq_left (by rw [← h_sorted_size']; exact Nat.le_of_lt h_kn)]
        omega

theorem maximum_result_sorted_ascending
    (arr : RustSlice u64) (k : u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_119_maximum.maximum arr k = RustM.ok v) :
    sorted_asc v.val := by
  by_cases hk : k = 0
  · subst hk
    rw [maximum_zero_k_eq arr] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    intro k₁ k₂ h₁ h₂ _
    have h0 : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size = 0 := rfl
    rw [h0] at h₁
    omega
  · by_cases hempty : arr.val.size = 0
    · rw [maximum_empty_arr_eq arr k hempty] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      intro k₁ k₂ h₁ h₂ _
      have h0 : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size = 0 := rfl
      rw [h0] at h₁
      omega
    · have hne : 0 < arr.val.size := by omega
      obtain ⟨sorted, h_sort_ok, h_tail_ok⟩ := maximum_decompose arr k hk hne v hres
      -- sorted is sorted
      have h_zero_toNat : (0 : usize).toNat = 0 := rfl
      have h_meas : arr.val.size - (0 : usize).toNat ≤ arr.val.size := by rw [h_zero_toNat]; omega
      have h_le : (0 : usize).toNat ≤ arr.val.size := by rw [h_zero_toNat]; omega
      have h_sorted_sorted : sorted_asc sorted.val :=
        sort_at_sorted arr.val.size arr (0 : usize) ⟨(List.nil).toArray, by grind⟩ sorted
          h_meas h_le h_sort_ok sorted_asc_empty
      have h_empty_sorted : sorted_asc ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val := by
        intro k₁ k₂ h₁ _ _
        have h0 : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size = 0 := rfl
        omega
      have h_empty_size : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size = 0 := rfl
      by_cases h_ge : (UInt64.ofNat sorted.val.size) ≤ k
      · rw [if_pos h_ge] at h_tail_ok
        have h_empty_le_s :
            ∀ (k₀ : Nat) (hk : k₀ < ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size)
              (hi_lt : (0 : usize).toNat < sorted.val.size),
            (((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val[k₀]'hk).toNat
              ≤ (sorted.val[(0 : usize).toNat]'hi_lt).toNat := by
          intro k₀ hk _
          rw [h_empty_size] at hk
          omega
        exact tail_from_sorted sorted h_sorted_sorted sorted.val.size (0 : usize)
          ⟨(List.nil).toArray, by grind⟩ v (by rw [h_zero_toNat]; omega)
          (by rw [h_zero_toNat]; omega) h_tail_ok h_empty_sorted h_empty_le_s
      · rw [if_neg h_ge] at h_tail_ok
        have h_sorted_size_lt : sorted.val.size < 2^64 := by
          have h_size_lt : sorted.val.size < USize64.size := sorted.size_lt_usizeSize
          rw [usize_size_eq] at h_size_lt; exact h_size_lt
        have h_n_toNat : (UInt64.ofNat sorted.val.size).toNat = sorted.val.size :=
          UInt64.toNat_ofNat_of_lt' h_sorted_size_lt
        have h_kn : k.toNat < sorted.val.size := by
          have h_nk_le_lt : ¬ (UInt64.ofNat sorted.val.size) ≤ k := h_ge
          rw [UInt64.le_iff_toNat_le] at h_nk_le_lt
          rw [h_n_toNat] at h_nk_le_lt
          omega
        have h_start_toNat : (USize64.ofNat (sorted.val.size - k.toNat)).toNat
                              = sorted.val.size - k.toNat := by
          apply USize64.toNat_ofNat_of_lt'
          show sorted.val.size - k.toNat < USize64.size
          rw [usize_size_eq]
          have : sorted.val.size - k.toNat ≤ sorted.val.size := Nat.sub_le _ _
          omega
        have h_start_le : (USize64.ofNat (sorted.val.size - k.toNat)).toNat ≤ sorted.val.size := by
          rw [h_start_toNat]; exact Nat.sub_le _ _
        have h_meas' : sorted.val.size - (USize64.ofNat (sorted.val.size - k.toNat)).toNat ≤ sorted.val.size := by
          rw [h_start_toNat]; omega
        have h_empty_le_s :
            ∀ (k₀ : Nat) (hk : k₀ < ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size)
              (hi_lt : (USize64.ofNat (sorted.val.size - k.toNat)).toNat < sorted.val.size),
            (((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val[k₀]'hk).toNat
              ≤ (sorted.val[(USize64.ofNat (sorted.val.size - k.toNat)).toNat]'hi_lt).toNat := by
          intro k₀ hk _
          rw [h_empty_size] at hk
          omega
        exact tail_from_sorted sorted h_sorted_sorted sorted.val.size
          (USize64.ofNat (sorted.val.size - k.toNat))
          ⟨(List.nil).toArray, by grind⟩ v h_meas' h_start_le h_tail_ok h_empty_sorted h_empty_le_s

theorem maximum_result_is_k_largest
    (arr : RustSlice u64) (k : u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_119_maximum.maximum arr k = RustM.ok v) :
    v.val.toList =
      (sort_asc_list arr.val.toList).drop
        (arr.val.size - min k.toNat arr.val.size) := by
  by_cases hk : k = 0
  · subst hk
    rw [maximum_zero_k_eq arr] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    show (List.nil : List u64).toArray.toList
        = (sort_asc_list arr.val.toList).drop (arr.val.size - min 0 arr.val.size)
    show ([] : List u64) = _
    simp only [Nat.zero_min, Nat.sub_zero]
    symm
    rw [List.drop_eq_nil_iff]
    have h_len : (sort_asc_list arr.val.toList).length = arr.val.toList.length := by
      -- length is preserved by sort_asc_list (proved by induction)
      have : ∀ xs : List u64, (sort_asc_list xs).length = xs.length := by
        intro xs
        induction xs with
        | nil => rfl
        | cons x xs ih =>
          show (insert_asc_list (sort_asc_list xs) x).length = (x :: xs).length
          have h_ins_len : ∀ ys : List u64, ∀ y : u64,
              (insert_asc_list ys y).length = ys.length + 1 := by
            intro ys y
            induction ys with
            | nil => rfl
            | cons z zs ihz =>
              show (if y ≤ z then y :: z :: zs else z :: insert_asc_list zs y).length = (z :: zs).length + 1
              by_cases h : y ≤ z
              · rw [if_pos h]; rfl
              · rw [if_neg h]
                show (insert_asc_list zs y).length + 1 = zs.length + 1 + 1
                rw [ihz]
          rw [h_ins_len, ih]
          rfl
      rw [this, Array.length_toList]
    rw [h_len, Array.length_toList]
    exact Nat.le_refl _
  · by_cases hempty : arr.val.size = 0
    · rw [maximum_empty_arr_eq arr k hempty] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      show (List.nil : List u64).toArray.toList = _
      show ([] : List u64) = _
      have h_arr_nil : arr.val.toList = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro x hx
        have := List.length_pos_of_mem hx
        rw [Array.length_toList] at this
        omega
      rw [h_arr_nil]
      show ([] : List u64) = (sort_asc_list []).drop _
      simp [sort_asc_list]
    · have hne : 0 < arr.val.size := by omega
      obtain ⟨sorted, h_sort_ok, h_tail_ok⟩ := maximum_decompose arr k hk hne v hres
      have h_zero_toNat : (0 : usize).toNat = 0 := rfl
      have h_meas : arr.val.size - (0 : usize).toNat ≤ arr.val.size := by rw [h_zero_toNat]; omega
      have h_le : (0 : usize).toNat ≤ arr.val.size := by rw [h_zero_toNat]; omega
      have h_sort_inv := sort_at_inv arr.val.size arr (0 : usize)
        ⟨(List.nil).toArray, by grind⟩ sorted h_meas h_le h_sort_ok
      obtain ⟨h_sorted_size, h_sorted_toList⟩ := h_sort_inv
      have h_empty_size : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size = 0 := rfl
      have h_empty_toList : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.toList = [] := by
        show (List.nil : List u64).toArray.toList = []
        simp
      rw [h_empty_size, h_zero_toNat] at h_sorted_size
      have h_sorted_size' : sorted.val.size = arr.val.size := by rw [h_sorted_size]; omega
      rw [h_empty_toList, h_zero_toNat] at h_sorted_toList
      have h_sorted_toList' : sorted.val.toList = sort_asc_list arr.val.toList := by
        rw [h_sorted_toList]; simp [sort_aux_nil_eq_sort_asc_list]
      have h_sorted_size_lt : sorted.val.size < 2^64 := by
        have h_size_lt : sorted.val.size < USize64.size := sorted.size_lt_usizeSize
        rw [usize_size_eq] at h_size_lt; exact h_size_lt
      have h_n_toNat : (UInt64.ofNat sorted.val.size).toNat = sorted.val.size :=
        UInt64.toNat_ofNat_of_lt' h_sorted_size_lt
      by_cases h_ge : (UInt64.ofNat sorted.val.size) ≤ k
      · rw [if_pos h_ge] at h_tail_ok
        have h_tail_inv := tail_from_inv sorted.val.size sorted (0 : usize)
          ⟨(List.nil).toArray, by grind⟩ v (by rw [h_zero_toNat]; omega)
          (by rw [h_zero_toNat]; omega) h_tail_ok
        obtain ⟨_, h_v_toList⟩ := h_tail_inv
        rw [h_empty_toList, h_zero_toNat] at h_v_toList
        have h_kn : sorted.val.size ≤ k.toNat := by
          rw [UInt64.le_iff_toNat_le] at h_ge
          rw [h_n_toNat] at h_ge
          exact h_ge
        rw [h_v_toList]
        show [] ++ sorted.val.toList.drop 0
            = (sort_asc_list arr.val.toList).drop (arr.val.size - min k.toNat arr.val.size)
        rw [List.drop_zero, h_sorted_toList']
        rw [show min k.toNat arr.val.size = arr.val.size from
          Nat.min_eq_right (by rw [← h_sorted_size']; exact h_kn)]
        rw [Nat.sub_self]
        simp
      · rw [if_neg h_ge] at h_tail_ok
        have h_kn : k.toNat < sorted.val.size := by
          have h_nk_le_lt : ¬ (UInt64.ofNat sorted.val.size) ≤ k := h_ge
          rw [UInt64.le_iff_toNat_le] at h_nk_le_lt
          rw [h_n_toNat] at h_nk_le_lt
          omega
        have h_start_toNat : (USize64.ofNat (sorted.val.size - k.toNat)).toNat
                              = sorted.val.size - k.toNat := by
          apply USize64.toNat_ofNat_of_lt'
          show sorted.val.size - k.toNat < USize64.size
          rw [usize_size_eq]
          have : sorted.val.size - k.toNat ≤ sorted.val.size := Nat.sub_le _ _
          omega
        have h_start_le : (USize64.ofNat (sorted.val.size - k.toNat)).toNat ≤ sorted.val.size := by
          rw [h_start_toNat]; exact Nat.sub_le _ _
        have h_meas' : sorted.val.size - (USize64.ofNat (sorted.val.size - k.toNat)).toNat ≤ sorted.val.size := by
          rw [h_start_toNat]; omega
        have h_tail_inv := tail_from_inv sorted.val.size sorted
          (USize64.ofNat (sorted.val.size - k.toNat))
          ⟨(List.nil).toArray, by grind⟩ v h_meas' h_start_le h_tail_ok
        obtain ⟨_, h_v_toList⟩ := h_tail_inv
        rw [h_empty_toList, h_start_toNat] at h_v_toList
        rw [h_v_toList]
        show [] ++ sorted.val.toList.drop (sorted.val.size - k.toNat) = _
        rw [List.nil_append, h_sorted_toList']
        rw [show min k.toNat arr.val.size = k.toNat from
          Nat.min_eq_left (by rw [← h_sorted_size']; exact Nat.le_of_lt h_kn)]
        rw [h_sorted_size']

end Clever_119_maximumObligations
