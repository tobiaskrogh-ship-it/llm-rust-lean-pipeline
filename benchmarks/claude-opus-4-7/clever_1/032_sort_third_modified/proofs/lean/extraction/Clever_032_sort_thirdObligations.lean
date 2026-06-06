-- Companion obligations file for the `clever_032_sort_third` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_032_sort_third

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_032_sort_thirdObligations

/-! ## Sortedness helper. -/

/-- An array is "sorted" iff its `toInt` projection is non-decreasing. -/
private def arr_sorted (a : Array i64) : Prop :=
  ∀ (i j : Nat) (hi : i < a.size) (hj : j < a.size),
    i ≤ j → (a[i]'hi).toInt ≤ (a[j]'hj).toInt

/-- The empty array is trivially sorted. -/
private theorem arr_sorted_empty : arr_sorted (([] : List i64).toArray) := by
  intro i j hi hj _
  exfalso
  have h0 : (([] : List i64).toArray).size = 0 := rfl
  rw [h0] at hi; omega

/-- Appending a single element to a sorted array preserves sortedness iff
    the new element is ≥ all existing elements. -/
private theorem arr_sorted_append_singleton (a : Array i64) (c : i64)
    (h_sorted : arr_sorted a)
    (h_ge : ∀ (k : Nat) (hk : k < a.size), (a[k]'hk).toInt ≤ c.toInt) :
    arr_sorted (a ++ #[c]) := by
  intro i j hi hj hij
  have h_sz : (a ++ #[c]).size = a.size + 1 := by rw [Array.size_append]; rfl
  by_cases hj_lt : j < a.size
  · -- both i, j in the original array
    have hi_lt : i < a.size := by omega
    rw [Array.getElem_append_left hi_lt, Array.getElem_append_left hj_lt]
    exact h_sorted i j hi_lt hj_lt hij
  · -- j = a.size (the new element)
    have hj_ge : a.size ≤ j := by omega
    have hj_eq : j = a.size := by omega
    rw [Array.getElem_append_right hj_ge]
    have h_sub_j : j - a.size = 0 := by omega
    simp only [h_sub_j]
    by_cases hi_lt : i < a.size
    · rw [Array.getElem_append_left hi_lt]
      exact h_ge i hi_lt
    · -- i = a.size = j: i = j
      have hi_ge : a.size ≤ i := by omega
      rw [Array.getElem_append_right hi_ge]
      have h_sub_i : i - a.size = 0 := by omega
      simp [h_sub_i]

/-! ## Counting helpers. -/

/-- Count occurrences of `y` at indices `< k` in array `a`. -/
private def vec_count (a : Array i64) (y : i64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      if h : k < a.size then
        (if (a[k]'h) = y then 1 else 0) + vec_count a y k
      else
        vec_count a y k

/-- Count of `y` in `a` at indices `0..n` for `n ≤ a.size`. -/
private theorem vec_count_le_self (a : Array i64) (y : i64) :
    ∀ k : Nat, vec_count a y k ≤ k := by
  intro k
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    show (if h : k < a.size then (if (a[k]'h) = y then 1 else 0) + vec_count a y k
          else vec_count a y k) ≤ k + 1
    by_cases hk : k < a.size
    · rw [dif_pos hk]
      by_cases h_eq : (a[k]'hk) = y
      · rw [if_pos h_eq]; omega
      · rw [if_neg h_eq]; omega
    · rw [dif_neg hk]; omega

/-! ## Spec helper: count of "third indices" (k with k % 3 = 0) below n. -/

private def thirdIdxCount : Nat → Nat
  | 0     => 0
  | k + 1 => if k % 3 = 0 then thirdIdxCount k + 1 else thirdIdxCount k

private theorem thirdIdxCount_mono : ∀ a b : Nat, a ≤ b → thirdIdxCount a ≤ thirdIdxCount b := by
  intro a b hab
  induction b with
  | zero =>
    have : a = 0 := Nat.le_zero.mp hab
    subst this; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with h | h
    · have ha_le_b : a ≤ b := Nat.lt_succ_iff.mp h
      have hib := ih ha_le_b
      show thirdIdxCount a ≤ thirdIdxCount (b + 1)
      show thirdIdxCount a ≤ if b % 3 = 0 then thirdIdxCount b + 1 else thirdIdxCount b
      by_cases hb : b % 3 = 0
      · rw [if_pos hb]; omega
      · rw [if_neg hb]; exact hib
    · have ha_eq : a = b + 1 := by omega
      subst ha_eq; exact Nat.le_refl _

private theorem thirdIdxCount_le_self : ∀ k : Nat, thirdIdxCount k ≤ k := by
  intro k
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    show (if k % 3 = 0 then thirdIdxCount k + 1 else thirdIdxCount k) ≤ k + 1
    by_cases hk : k % 3 = 0
    · rw [if_pos hk]; omega
    · rw [if_neg hk]; omega

/-! ## Specification oracle: count occurrences of a value at third-divisible
     indices of a slice/array. -/

private def third_count (a : Array i64) (x : i64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      if h : k < a.size then
        (if k % 3 = 0 ∧ (a[k]'h) = x then 1 else 0) + third_count a x k
      else
        third_count a x k

/-! ## Standard scaffolding (transferred from `clever_009_rolling_max`,
     `clever_021_rescale_to_unit`, `clever_025_remove_duplicates`). -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_zero_toNat : (0 : usize).toNat = 0 := rfl
private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl
private theorem usize_three_toNat : (3 : usize).toNat = 3 := rfl
private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide
private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

/-! ## Push helper for `Vec` (`extend_from_slice` of a 1-element chunk). -/

private def push_one (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec i64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

/-! ## Step lemmas for `rebuild_at`.

The three branches of the recursive body, packaged so subsequent
induction can rewrite directly. Pattern mirrors
`clever_021_rescale_to_unit`'s `shift_at_*`. -/

/-- Out-of-bounds step: `rebuild_at` returns the accumulator. -/
private theorem rebuild_at_oob
    (l sorted : RustSlice i64) (i j : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : l.val.size ≤ i.toNat) :
    clever_032_sort_third.rebuild_at l sorted i j acc = RustM.ok acc := by
  conv => lhs; unfold clever_032_sort_third.rebuild_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- The `i %? 3` operation reduces to `pure (i % 3)`. -/
private theorem usize_mod_three_pure (i : usize) :
    (i %? (3 : usize) : RustM usize) = RustM.ok (i % 3) := by
  show (rust_primitives.ops.arith.Rem.rem i (3 : usize) : RustM usize) = RustM.ok (i % 3)
  show (if (3 : usize) = 0 then (.fail .divisionByZero : RustM usize) else pure (i % 3))
       = RustM.ok (i % 3)
  have h_ne : (3 : usize) ≠ (0 : usize) := by decide
  rw [if_neg h_ne]; rfl

/-- Modulo by 3 in usize matches Nat-level modulo. -/
private theorem usize_mod_three_toNat (i : usize) :
    (i % (3 : usize)).toNat = i.toNat % 3 := by
  show (i % (3 : usize)).toBitVec.toNat = i.toBitVec.toNat % 3
  show (i.toBitVec % (3 : usize).toBitVec).toNat = i.toBitVec.toNat % 3
  rw [BitVec.toNat_umod]
  rfl

private theorem usize_eq_zero_iff_toNat (i : usize) : i = (0 : usize) ↔ i.toNat = 0 := by
  constructor
  · intro h; rw [h]; rfl
  · intro h
    apply USize64.toNat_inj.mp
    rw [h]; rfl

/-- The check `(i % 3) ==? 0` reduces by Nat semantics. -/
private theorem mod3_eq_zero_pure (i : usize) :
    ((i % (3 : usize)) ==? (0 : usize) : RustM Bool) =
      RustM.ok (decide (i.toNat % 3 = 0)) := by
  show (rust_primitives.cmp.eq (i % (3 : usize)) (0 : usize) : RustM Bool) =
        RustM.ok (decide (i.toNat % 3 = 0))
  show pure (decide ((i % (3 : usize)) = (0 : usize))) =
        RustM.ok (decide (i.toNat % 3 = 0))
  have h_iff : ((i % (3 : usize)) = (0 : usize)) ↔ (i.toNat % 3 = 0) := by
    rw [usize_eq_zero_iff_toNat, usize_mod_three_toNat]
  rw [decide_eq_decide.mpr h_iff]
  rfl

/-- Step lemma when `i % 3 = 0`: pulls one element from `sorted[j]`. -/
private theorem rebuild_at_step_third
    (l sorted : RustSlice i64) (i j : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < l.val.size)
    (hmod : i.toNat % 3 = 0)
    (hj : j.toNat < sorted.val.size)
    (h_acc : acc.val.size + 1 < USize64.size)
    (h_j_ok : j.toNat + 1 < 2 ^ 64) :
    clever_032_sort_third.rebuild_at l sorted i j acc =
      clever_032_sort_third.rebuild_at l sorted (i + 1) (j + 1)
        (push_one acc (sorted.val[j.toNat]'hj) h_acc) := by
  conv => lhs; unfold clever_032_sort_third.rebuild_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx_sorted : (sorted[j]_? : RustM i64) =
        RustM.ok (sorted.val[j.toNat]'hj) := by
    show (if h : j.toNat < sorted.val.size then pure (sorted.val[j])
            else .fail .arrayOutOfBounds)
        = RustM.ok (sorted.val[j.toNat]'hj)
    rw [dif_pos hj]; rfl
  have h_no_ov_i : i.toNat + 1 < 2 ^ 64 := by
    rw [h_usize_size] at h_size_lt; omega
  have h_no_bv_i :
      BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hii := (USize64.uaddOverflow_iff i 1).mp hbo
      rw [usize_one_toNat] at hii
      omega
  have h_add_i : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
    show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
    show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
          then (.fail .integerOverflow : RustM usize)
          else pure (i + 1)) = _
    rw [h_no_bv_i]; rfl
  have h_no_bv_j :
      BitVec.uaddOverflow j.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow j.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hjj := (USize64.uaddOverflow_iff j 1).mp hbo
      rw [usize_one_toNat] at hjj
      omega
  have h_add_j : (j +? (1 : usize) : RustM usize) = RustM.ok (j + 1) := by
    show (rust_primitives.ops.arith.Add.add j 1 : RustM usize) = RustM.ok (j + 1)
    show (if BitVec.uaddOverflow j.toBitVec (1 : usize).toBitVec
          then (.fail .integerOverflow : RustM usize)
          else pure (j + 1)) = _
    rw [h_no_bv_j]; rfl
  have h_mod_eq : decide (i.toNat % 3 = 0) = true := decide_eq_true hmod
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             usize_mod_three_pure, mod3_eq_zero_pure, h_mod_eq,
             h_idx_sorted]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[sorted.val[j.toNat]'hj] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
            = RustM.ok ⟨#[sorted.val[j.toNat]'hj], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size :
      acc.val.size +
        (#[sorted.val[j.toNat]'hj] : Array i64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  rw [show (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
              ⟨#[sorted.val[j.toNat]'hj], one_lt_usize_size⟩
            : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
        = RustM.ok (push_one acc (sorted.val[j.toNat]'hj) h_acc) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  simp only [RustM_ok_bind]
  rw [h_add_i, h_add_j]
  rfl

/-- Step lemma when `i % 3 ≠ 0`: pulls element from `l[i]`. -/
private theorem rebuild_at_step_other
    (l sorted : RustSlice i64) (i j : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < l.val.size)
    (hmod : i.toNat % 3 ≠ 0)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_032_sort_third.rebuild_at l sorted i j acc =
      clever_032_sort_third.rebuild_at l sorted (i + 1) j
        (push_one acc (l.val[i.toNat]'hi) h_acc) := by
  conv => lhs; unfold clever_032_sort_third.rebuild_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx_l : (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_no_ov_i : i.toNat + 1 < 2 ^ 64 := by
    rw [h_usize_size] at h_size_lt; omega
  have h_no_bv_i :
      BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hii := (USize64.uaddOverflow_iff i 1).mp hbo
      rw [usize_one_toNat] at hii
      omega
  have h_add_i : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
    show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
    show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
          then (.fail .integerOverflow : RustM usize)
          else pure (i + 1)) = _
    rw [h_no_bv_i]; rfl
  have h_mod_eq : decide (i.toNat % 3 = 0) = false :=
    decide_eq_false hmod
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             usize_mod_three_pure, mod3_eq_zero_pure, h_mod_eq,
             h_idx_l]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[l.val[i.toNat]'hi] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
            = RustM.ok ⟨#[l.val[i.toNat]'hi], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size :
      acc.val.size +
        (#[l.val[i.toNat]'hi] : Array i64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  rw [show (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
              ⟨#[l.val[i.toNat]'hi], one_lt_usize_size⟩
            : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
        = RustM.ok (push_one acc (l.val[i.toNat]'hi) h_acc) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  simp only [RustM_ok_bind]
  rw [h_add_i]
  rfl

/-- Fail step: when i % 3 = 0 and j out of bounds, rebuild_at fails. -/
private theorem rebuild_at_step_third_fail
    (l sorted : RustSlice i64) (i j : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < l.val.size)
    (hmod : i.toNat % 3 = 0)
    (hj : sorted.val.size ≤ j.toNat) :
    clever_032_sort_third.rebuild_at l sorted i j acc =
      RustM.fail Error.arrayOutOfBounds := by
  conv => lhs; unfold clever_032_sort_third.rebuild_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx_sorted_fail :
      (sorted[j]_? : RustM i64) = RustM.fail Error.arrayOutOfBounds := by
    show (if h : j.toNat < sorted.val.size then pure (sorted.val[j])
            else .fail .arrayOutOfBounds) = RustM.fail Error.arrayOutOfBounds
    rw [dif_neg (Nat.not_lt.mpr hj)]
  have h_mod_eq : decide (i.toNat % 3 = 0) = true := decide_eq_true hmod
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             usize_mod_three_pure, mod3_eq_zero_pure, h_mod_eq,
             h_idx_sorted_fail]
  rfl

/-! ## Strong induction for `rebuild_at`.

Given a `sorted` slice with at least `thirdIdxCount l.val.size` elements,
`rebuild_at l sorted i j acc` succeeds whenever:
- `i.toNat ≤ l.val.size`
- `j.toNat = thirdIdxCount i.toNat`
- `acc.val.size = i.toNat`
- `acc` agrees with the spec on its filled positions.

The final result has size `l.val.size`, matches `l` at non-third indices,
and matches `sorted[thirdIdxCount k]` at third indices `k`. -/

private theorem rebuild_at_correct (l sorted : RustSlice i64)
    (hsorted_sz : thirdIdxCount l.val.size ≤ sorted.val.size) :
    ∀ (n : Nat) (i j : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      j.toNat = thirdIdxCount i.toNat →
      acc.val.size = i.toNat →
      (∀ (k : Nat) (hk : k < acc.val.size),
          if k % 3 = 0 then
            ∃ (hj : thirdIdxCount k < sorted.val.size),
              acc.val[k]'hk = sorted.val[thirdIdxCount k]'hj
          else
            ∃ (hl : k < l.val.size),
              acc.val[k]'hk = l.val[k]'hl) →
      ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
        clever_032_sort_third.rebuild_at l sorted i j acc = RustM.ok v ∧
        v.val.size = l.val.size ∧
        (∀ (k : Nat) (hk : k < v.val.size),
            if k % 3 = 0 then
              ∃ (hj : thirdIdxCount k < sorted.val.size),
                v.val[k]'hk = sorted.val[thirdIdxCount k]'hj
            else
              ∃ (hl : k < l.val.size),
                v.val[k]'hk = l.val[k]'hl) := by
  intro n
  induction n with
  | zero =>
    intro i j acc hn hi_le hj_eq h_acc_sz h_acc_inv
    have hi_eq : i.toNat = l.val.size := by omega
    have hi_ge : l.val.size ≤ i.toNat := by omega
    refine ⟨acc, rebuild_at_oob l sorted i j acc hi_ge, ?_, ?_⟩
    · rw [h_acc_sz, hi_eq]
    · intro k hk
      have hk_lt_l : k < l.val.size := by rw [h_acc_sz, hi_eq] at hk; exact hk
      exact h_acc_inv k (by rw [h_acc_sz, hi_eq]; exact hk_lt_l)
  | succ n ih =>
    intro i j acc hn hi_le hj_eq h_acc_sz h_acc_inv
    by_cases hi_ge : l.val.size ≤ i.toNat
    · have hi_eq : i.toNat = l.val.size := by omega
      refine ⟨acc, rebuild_at_oob l sorted i j acc hi_ge, ?_, ?_⟩
      · rw [h_acc_sz, hi_eq]
      · intro k hk
        have hk_lt_l : k < l.val.size := by rw [h_acc_sz, hi_eq] at hk; exact hk
        exact h_acc_inv k (by rw [h_acc_sz, hi_eq]; exact hk_lt_l)
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2 ^ 64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_meas : l.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      have h_acc_succ : acc.val.size + 1 < USize64.size := by
        rw [h_acc_sz, h_usize_size]; omega
      by_cases hmod : i.toNat % 3 = 0
      · -- third index branch
        have hj_lt : j.toNat < sorted.val.size := by
          have h1 : thirdIdxCount (i.toNat + 1) = thirdIdxCount i.toNat + 1 := by
            show (if i.toNat % 3 = 0 then thirdIdxCount i.toNat + 1 else thirdIdxCount i.toNat) = _
            rw [if_pos hmod]
          have h2 : thirdIdxCount (i.toNat + 1) ≤ thirdIdxCount l.val.size :=
            thirdIdxCount_mono _ _ hi_lt
          have h3 : thirdIdxCount i.toNat + 1 ≤ sorted.val.size := by
            calc thirdIdxCount i.toNat + 1 = thirdIdxCount (i.toNat + 1) := h1.symm
              _ ≤ thirdIdxCount l.val.size := h2
              _ ≤ sorted.val.size := hsorted_sz
          rw [hj_eq]; omega
        have h_no_ov_j : j.toNat + 1 < 2 ^ 64 := by
          have h_ss_lt : sorted.val.size < USize64.size := sorted.size_lt_usizeSize
          rw [h_usize_size] at h_ss_lt; omega
        have h_j1 : (j + 1).toNat = j.toNat + 1 := usize_add_one_toNat j h_no_ov_j
        have h_step := rebuild_at_step_third l sorted i j acc hi_lt hmod hj_lt h_acc_succ h_no_ov_j
        rw [h_step]
        let acc' := push_one acc (sorted.val[j.toNat]'hj_lt) h_acc_succ
        have h_acc'_sz : acc'.val.size = (i + 1).toNat := by
          show (acc.val ++ #[sorted.val[j.toNat]'hj_lt]).size = (i + 1).toNat
          rw [Array.size_append, h_acc_sz, h_i1]; rfl
        have h_j1_eq : (j + 1).toNat = thirdIdxCount (i + 1).toNat := by
          rw [h_j1, h_i1, hj_eq]
          show thirdIdxCount i.toNat + 1 = thirdIdxCount (i.toNat + 1)
          show thirdIdxCount i.toNat + 1 =
                  if i.toNat % 3 = 0 then thirdIdxCount i.toNat + 1 else thirdIdxCount i.toNat
          rw [if_pos hmod]
        have h_acc'_inv :
            ∀ (k : Nat) (hk : k < acc'.val.size),
              if k % 3 = 0 then
                ∃ (hj' : thirdIdxCount k < sorted.val.size),
                  acc'.val[k]'hk = sorted.val[thirdIdxCount k]'hj'
              else
                ∃ (hl : k < l.val.size),
                  acc'.val[k]'hk = l.val[k]'hl := by
          intro k hk
          show (if k % 3 = 0 then _ else _)
          show (if k % 3 = 0 then ∃ (hj' : thirdIdxCount k < sorted.val.size),
                  (acc.val ++ #[sorted.val[j.toNat]'hj_lt])[k]'hk =
                    sorted.val[thirdIdxCount k]'hj'
                else ∃ (hl : k < l.val.size),
                  (acc.val ++ #[sorted.val[j.toNat]'hj_lt])[k]'hk = l.val[k]'hl)
          by_cases hk_lt_acc : k < acc.val.size
          · rw [Array.getElem_append_left hk_lt_acc]
            exact h_acc_inv k hk_lt_acc
          · have h_size_raw :
                (acc.val ++ #[sorted.val[j.toNat]'hj_lt]).size = acc.val.size + 1 := by
              rw [Array.size_append]; rfl
            have hk_eq : k = acc.val.size := by
              rw [h_acc'_sz, h_i1] at hk
              rw [h_acc_sz] at hk_lt_acc
              omega
            have hk_eq_i : k = i.toNat := by rw [hk_eq, h_acc_sz]
            have hk_mod : k % 3 = 0 := by rw [hk_eq_i]; exact hmod
            rw [if_pos hk_mod]
            have h_tic_k : thirdIdxCount k = j.toNat := by rw [hk_eq_i, hj_eq]
            refine ⟨by rw [h_tic_k]; exact hj_lt, ?_⟩
            subst hk_eq
            rw [Array.getElem_append_right (Nat.le_refl _)]
            simp only [Nat.sub_self]
            have h_tic_acc : thirdIdxCount acc.val.size = j.toNat := by
              rw [h_acc_sz, hj_eq]
            rw [show sorted.val[thirdIdxCount acc.val.size]'(by rw [h_tic_acc]; exact hj_lt)
                  = sorted.val[j.toNat]'hj_lt from getElem_congr_idx h_tic_acc]
            rfl
        exact ih (i + 1) (j + 1) acc' h_meas h_i1_le h_j1_eq h_acc'_sz h_acc'_inv
      · -- non-third index branch
        have h_step := rebuild_at_step_other l sorted i j acc hi_lt hmod h_acc_succ
        rw [h_step]
        let acc' := push_one acc (l.val[i.toNat]'hi_lt) h_acc_succ
        have h_acc'_sz : acc'.val.size = (i + 1).toNat := by
          show (acc.val ++ #[l.val[i.toNat]'hi_lt]).size = (i + 1).toNat
          rw [Array.size_append, h_acc_sz, h_i1]; rfl
        have h_j_eq' : j.toNat = thirdIdxCount (i + 1).toNat := by
          rw [h_i1, hj_eq]
          show thirdIdxCount i.toNat = if i.toNat % 3 = 0 then thirdIdxCount i.toNat + 1 else thirdIdxCount i.toNat
          rw [if_neg hmod]
        have h_acc'_inv :
            ∀ (k : Nat) (hk : k < acc'.val.size),
              if k % 3 = 0 then
                ∃ (hj' : thirdIdxCount k < sorted.val.size),
                  acc'.val[k]'hk = sorted.val[thirdIdxCount k]'hj'
              else
                ∃ (hl : k < l.val.size),
                  acc'.val[k]'hk = l.val[k]'hl := by
          intro k hk
          show (if k % 3 = 0 then ∃ (hj' : thirdIdxCount k < sorted.val.size),
                  (acc.val ++ #[l.val[i.toNat]'hi_lt])[k]'hk =
                    sorted.val[thirdIdxCount k]'hj'
                else ∃ (hl : k < l.val.size),
                  (acc.val ++ #[l.val[i.toNat]'hi_lt])[k]'hk = l.val[k]'hl)
          by_cases hk_lt_acc : k < acc.val.size
          · rw [Array.getElem_append_left hk_lt_acc]
            exact h_acc_inv k hk_lt_acc
          · have h_size_raw :
                (acc.val ++ #[l.val[i.toNat]'hi_lt]).size = acc.val.size + 1 := by
              rw [Array.size_append]; rfl
            have hk_eq : k = acc.val.size := by
              rw [h_acc'_sz, h_i1] at hk
              rw [h_acc_sz] at hk_lt_acc
              omega
            have hk_eq_i : k = i.toNat := by rw [hk_eq, h_acc_sz]
            have hk_mod : k % 3 ≠ 0 := by rw [hk_eq_i]; exact hmod
            rw [if_neg hk_mod]
            refine ⟨by rw [hk_eq_i]; exact hi_lt, ?_⟩
            have h_k_ge : acc.val.size ≤ k := by omega
            rw [Array.getElem_append_right h_k_ge]
            have h_sub_zero : k - acc.val.size = 0 := by omega
            have h_k_eq_i : k = i.toNat := hk_eq_i
            simp only [h_sub_zero]
            rw [show l.val[k]'(by rw [h_k_eq_i]; exact hi_lt) = l.val[i.toNat]'hi_lt from
                getElem_congr_idx h_k_eq_i]
            rfl
        exact ih (i + 1) j acc' h_meas h_i1_le h_j_eq' h_acc'_sz h_acc'_inv

/-! ## hres-input form: rebuild_at correctness from a success hypothesis. -/

private theorem rebuild_at_hres_correct (l sorted : RustSlice i64) :
    ∀ (n : Nat) (i j : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (v : alloc.vec.Vec i64 alloc.alloc.Global),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      j.toNat = thirdIdxCount i.toNat →
      acc.val.size = i.toNat →
      (∀ (k : Nat) (hk : k < acc.val.size),
          k % 3 ≠ 0 →
          ∃ (hl : k < l.val.size), acc.val[k]'hk = l.val[k]'hl) →
      clever_032_sort_third.rebuild_at l sorted i j acc = RustM.ok v →
      v.val.size = l.val.size ∧
      (∀ (k : Nat) (hk : k < v.val.size),
          k % 3 ≠ 0 →
          ∃ (hl : k < l.val.size), v.val[k]'hk = l.val[k]'hl) := by
  intro n
  induction n with
  | zero =>
    intro i j acc v hn hi_le hj_eq h_acc_sz h_acc_inv hres
    have hi_eq : i.toNat = l.val.size := by omega
    have hi_ge : l.val.size ≤ i.toNat := by omega
    rw [rebuild_at_oob l sorted i j acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    refine ⟨?_, ?_⟩
    · rw [h_acc_sz, hi_eq]
    · intro k hk hkm
      have hk_lt_l : k < l.val.size := by rw [h_acc_sz, hi_eq] at hk; exact hk
      exact h_acc_inv k (by rw [h_acc_sz, hi_eq]; exact hk_lt_l) hkm
  | succ n ih =>
    intro i j acc v hn hi_le hj_eq h_acc_sz h_acc_inv hres
    by_cases hi_ge : l.val.size ≤ i.toNat
    · have hi_eq : i.toNat = l.val.size := by omega
      rw [rebuild_at_oob l sorted i j acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      refine ⟨?_, ?_⟩
      · rw [h_acc_sz, hi_eq]
      · intro k hk hkm
        have hk_lt_l : k < l.val.size := by rw [h_acc_sz, hi_eq] at hk; exact hk
        exact h_acc_inv k (by rw [h_acc_sz, hi_eq]; exact hk_lt_l) hkm
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2 ^ 64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_meas : l.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      have h_acc_succ : acc.val.size + 1 < USize64.size := by
        rw [h_acc_sz, h_usize_size]; omega
      by_cases hmod : i.toNat % 3 = 0
      · by_cases hj_lt : j.toNat < sorted.val.size
        · have h_ss_lt : sorted.val.size < USize64.size := sorted.size_lt_usizeSize
          have h_no_ov_j : j.toNat + 1 < 2 ^ 64 := by
            rw [h_usize_size] at h_ss_lt; omega
          have h_j1 : (j + 1).toNat = j.toNat + 1 := usize_add_one_toNat j h_no_ov_j
          have h_step := rebuild_at_step_third l sorted i j acc hi_lt hmod hj_lt h_acc_succ h_no_ov_j
          rw [h_step] at hres
          let acc' := push_one acc (sorted.val[j.toNat]'hj_lt) h_acc_succ
          have h_acc'_sz : acc'.val.size = (i + 1).toNat := by
            show (acc.val ++ #[sorted.val[j.toNat]'hj_lt]).size = (i + 1).toNat
            rw [Array.size_append, h_acc_sz, h_i1]; rfl
          have h_j1_eq : (j + 1).toNat = thirdIdxCount (i + 1).toNat := by
            rw [h_j1, h_i1, hj_eq]
            show thirdIdxCount i.toNat + 1 =
                  if i.toNat % 3 = 0 then thirdIdxCount i.toNat + 1 else thirdIdxCount i.toNat
            rw [if_pos hmod]
          have h_acc'_inv :
              ∀ (k : Nat) (hk : k < acc'.val.size),
                k % 3 ≠ 0 →
                ∃ (hl : k < l.val.size), acc'.val[k]'hk = l.val[k]'hl := by
            intro k hk hkm
            show ∃ (hl : k < l.val.size),
                  (acc.val ++ #[sorted.val[j.toNat]'hj_lt])[k]'hk = l.val[k]'hl
            by_cases hk_lt_acc : k < acc.val.size
            · obtain ⟨hl, hkeq⟩ := h_acc_inv k hk_lt_acc hkm
              refine ⟨hl, ?_⟩
              rw [Array.getElem_append_left hk_lt_acc]
              exact hkeq
            · exfalso
              have hk_eq : k = acc.val.size := by
                rw [h_acc'_sz, h_i1] at hk; rw [h_acc_sz] at hk_lt_acc; omega
              have hk_eq_i : k = i.toNat := by rw [hk_eq, h_acc_sz]
              apply hkm; rw [hk_eq_i]; exact hmod
          exact ih (i + 1) (j + 1) acc' v h_meas h_i1_le h_j1_eq h_acc'_sz h_acc'_inv hres
        · exfalso
          have hj_ge : sorted.val.size ≤ j.toNat := Nat.le_of_not_lt hj_lt
          rw [rebuild_at_step_third_fail l sorted i j acc hi_lt hmod hj_ge] at hres
          cases hres
      · have h_step := rebuild_at_step_other l sorted i j acc hi_lt hmod h_acc_succ
        rw [h_step] at hres
        let acc' := push_one acc (l.val[i.toNat]'hi_lt) h_acc_succ
        have h_acc'_sz : acc'.val.size = (i + 1).toNat := by
          show (acc.val ++ #[l.val[i.toNat]'hi_lt]).size = (i + 1).toNat
          rw [Array.size_append, h_acc_sz, h_i1]; rfl
        have h_j_eq' : j.toNat = thirdIdxCount (i + 1).toNat := by
          rw [h_i1, hj_eq]
          show thirdIdxCount i.toNat =
                  if i.toNat % 3 = 0 then thirdIdxCount i.toNat + 1 else thirdIdxCount i.toNat
          rw [if_neg hmod]
        have h_acc'_inv :
            ∀ (k : Nat) (hk : k < acc'.val.size),
              k % 3 ≠ 0 →
              ∃ (hl : k < l.val.size), acc'.val[k]'hk = l.val[k]'hl := by
          intro k hk hkm
          show ∃ (hl : k < l.val.size),
                (acc.val ++ #[l.val[i.toNat]'hi_lt])[k]'hk = l.val[k]'hl
          by_cases hk_lt_acc : k < acc.val.size
          · obtain ⟨hl, hkeq⟩ := h_acc_inv k hk_lt_acc hkm
            refine ⟨hl, ?_⟩
            rw [Array.getElem_append_left hk_lt_acc]
            exact hkeq
          · have hk_eq : k = acc.val.size := by
              rw [h_acc'_sz, h_i1] at hk; rw [h_acc_sz] at hk_lt_acc; omega
            have hk_eq_i : k = i.toNat := by rw [hk_eq, h_acc_sz]
            refine ⟨by rw [hk_eq_i]; exact hi_lt, ?_⟩
            have h_k_ge : acc.val.size ≤ k := by omega
            rw [Array.getElem_append_right h_k_ge]
            have h_sub_zero : k - acc.val.size = 0 := by omega
            simp only [h_sub_zero]
            rw [show l.val[k]'(by rw [hk_eq_i]; exact hi_lt) = l.val[i.toNat]'hi_lt from
                getElem_congr_idx hk_eq_i]
            rfl
        exact ih (i + 1) j acc' v h_meas h_i1_le h_j_eq' h_acc'_sz h_acc'_inv hres

/-! ## Insert_sorted: while-loop infrastructure for totality. -/

open rust_primitives.hax (Tuple3 Tuple2)

private def isInv (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (s : Tuple3 usize Bool (alloc.vec.Vec i64 alloc.alloc.Global)) : Prop :=
  s._0.toNat ≤ v.val.size ∧
  s._2.val.size = s._0.toNat + (if s._1 then 1 else 0)

private def isTerm (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (s : Tuple3 usize Bool (alloc.vec.Vec i64 alloc.alloc.Global)) : Nat :=
  v.val.size - s._0.toNat

private abbrev isCond (v : alloc.vec.Vec i64 alloc.alloc.Global) :
    Tuple3 usize Bool (alloc.vec.Vec i64 alloc.alloc.Global) → Bool :=
  fun s => decide (s._0.toNat < (USize64.ofNat v.val.size).toNat)

private abbrev isBody (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64) :
    Tuple3 usize Bool (alloc.vec.Vec i64 alloc.alloc.Global) →
      RustM (Tuple3 usize Bool (alloc.vec.Vec i64 alloc.alloc.Global)) :=
  fun ⟨i, inserted, result⟩ =>
    (do
      let ⟨inserted, result⟩ ←
        if (← ((← (!? inserted)) &&? (← ((← v[i]_?) >=? x)))) then do
          let chunk : (RustArray i64 1) := (RustArray.ofVec #v[x]);
          let result : (alloc.vec.Vec i64 alloc.alloc.Global) ←
            (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
              result
              (← (rust_primitives.unsize chunk)));
          let inserted : Bool := true;
          (pure (rust_primitives.hax.Tuple2.mk inserted result))
        else do
          (pure (rust_primitives.hax.Tuple2.mk inserted result));
      let chunk : (RustArray i64 1) := (RustArray.ofVec #v[(← v[i]_?)]);
      let result : (alloc.vec.Vec i64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
          result
          (← (rust_primitives.unsize chunk)));
      let i : usize ← (i +? (1 : usize));
      (pure (rust_primitives.hax.Tuple3.mk i inserted result)) :
      RustM
      (rust_primitives.hax.Tuple3
        usize
        Bool
        (alloc.vec.Vec i64 alloc.alloc.Global)))

private abbrev isLoop (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64) :
    RustM (Tuple3 usize Bool (alloc.vec.Vec i64 alloc.alloc.Global)) :=
  Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk (isCond v)
    (rust_primitives.hax.Tuple3.mk (0 : usize) false
      ⟨([] : List i64).toArray, by grind⟩)
    (isBody v x)

private theorem vec_get_pure (v : alloc.vec.Vec i64 alloc.alloc.Global) (i : usize)
    (hi : i.toNat < v.val.size) :
    (v[i]_? : RustM i64) = RustM.ok (v.val[i.toNat]'hi) := by
  show (if h : i.toNat < v.val.size then pure (v.val[i])
          else .fail .arrayOutOfBounds)
      = RustM.ok (v.val[i.toNat]'hi)
  rw [dif_pos hi]; rfl

private theorem i64_ge_pure (a b : i64) :
    (a >=? b : RustM Bool) = pure (decide (a ≥ b)) := rfl

private theorem usize_add_one_pure (i : usize) (h : i.toNat + 1 < 2 ^ 64) :
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

private theorem unsize_singleton (c : i64) :
    (rust_primitives.unsize (RustArray.ofVec #v[c] : RustArray i64 1) :
      RustM (rust_primitives.sequence.Seq i64)) =
      RustM.ok ⟨#[c], one_lt_usize_size⟩ := rfl

private theorem extend_from_slice_singleton
    (acc : alloc.vec.Vec i64 alloc.alloc.Global) (c : i64)
    (h_acc : acc.val.size + 1 < USize64.size) :
    (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[c], one_lt_usize_size⟩ :
        RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.ok (push_one acc c h_acc) := by
  unfold alloc.vec.Impl_2.extend_from_slice
  have h_app_size : acc.val.size + (#[c] : Array i64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  rw [dif_pos h_app_size]
  rfl

private theorem is_body_step (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h_v_sz : v.val.size + 1 < USize64.size)
    (s : Tuple3 usize Bool (alloc.vec.Vec i64 alloc.alloc.Global))
    (hcond : isCond v s = true) (hinv : isInv v s) :
    ⦃⌜ isInv v s ⌝⦄
      isBody v x s
    ⦃⇓ s' => spred(⌜ isTerm v s' < isTerm v s ⌝ ∧ ⌜ isInv v s' ⌝)⦄ := by
  cases s with
  | mk i ins result =>
    have h_ofNat_v : (USize64.ofNat v.val.size).toNat = v.val.size :=
      USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
    have hi_lt : i.toNat < v.val.size := by
      have h : decide (i.toNat < (USize64.ofNat v.val.size).toNat) = true := hcond
      rw [h_ofNat_v] at h
      exact decide_eq_true_iff.mp h
    have hi_le : i.toNat ≤ v.val.size := hinv.1
    have h_r_sz : result.val.size = i.toNat + (if ins then 1 else 0) := hinv.2
    have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
    have h_v_sz' : v.val.size + 1 < 2 ^ 64 := by rw [h_usize_size] at h_v_sz; exact h_v_sz
    have h_no_ov_i : i.toNat + 1 < 2 ^ 64 := by omega
    have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
    have h_vi : (v[i]_? : RustM i64) = RustM.ok (v.val[i.toNat]'hi_lt) :=
      vec_get_pure v i hi_lt
    have h_add_i : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
      usize_add_one_pure i h_no_ov_i
    have h_r_sz_le : result.val.size ≤ i.toNat + 1 := by
      rw [h_r_sz]; by_cases h : ins
      · simp [h]
      · simp [h]
    have h_r_first_ok : result.val.size + 1 < USize64.size := by
      rw [h_usize_size]; omega
    dsimp only [isBody]
    have h_not_ins : (!? ins : RustM Bool) = pure (!ins) := rfl
    have h_vi_ge_x : ((v.val[i.toNat]'hi_lt) >=? x : RustM Bool) =
                      pure (decide ((v.val[i.toNat]'hi_lt) ≥ x)) := rfl
    rw [h_not_ins, pure_bind, h_vi, RustM_ok_bind, h_vi_ge_x, pure_bind]
    rw [show (rust_primitives.hax.logical_op.and (!ins) (decide ((v.val[i.toNat]'hi_lt) ≥ x))
              : RustM Bool) = pure (!ins && decide ((v.val[i.toNat]'hi_lt) ≥ x)) from rfl]
    rw [pure_bind]
    by_cases h_branch : (!ins && decide ((v.val[i.toNat]'hi_lt) ≥ x)) = true
    · have h_ins_false : ins = false := by
        cases ins
        · rfl
        · simp at h_branch
      have h_r_sz_init : result.val.size = i.toNat := by
        rw [h_r_sz, h_ins_false]; simp
      have h_r_first_ok' : result.val.size + 1 < USize64.size := by
        rw [h_r_sz_init, h_usize_size]; omega
      rw [if_pos h_branch]
      rw [unsize_singleton, RustM_ok_bind,
          extend_from_slice_singleton result x h_r_first_ok', RustM_ok_bind, pure_bind]
      simp only [h_vi, RustM_ok_bind, unsize_singleton]
      simp only [extend_from_slice_singleton _ _
                  (by show (push_one result x h_r_first_ok').val.size + 1 < USize64.size
                      show (result.val ++ #[x]).size + 1 < USize64.size
                      rw [Array.size_append, h_r_sz_init, h_usize_size]
                      show i.toNat + 1 + 1 < 2 ^ 64; omega),
                 RustM_ok_bind, h_add_i, RustM_ok_bind]
      apply Triple.pure
      simp only [SPred.entails_true_intro]
      intro _
      refine ⟨?_, ?_⟩
      · show v.val.size - (i + 1).toNat < v.val.size - i.toNat
        rw [h_i1]; omega
      · refine ⟨by rw [h_i1]; omega, ?_⟩
        show ((push_one result x h_r_first_ok').val ++ #[v.val[i.toNat]'hi_lt]).size =
              (i + 1).toNat + (if true then 1 else 0)
        show ((result.val ++ #[x]) ++ #[v.val[i.toNat]'hi_lt]).size = (i + 1).toNat + 1
        rw [Array.size_append, Array.size_append, h_r_sz_init, h_i1]; rfl
    · rw [if_neg h_branch]
      rw [pure_bind]
      simp only [h_vi, RustM_ok_bind, unsize_singleton]
      simp only [extend_from_slice_singleton _ _ h_r_first_ok,
                 RustM_ok_bind, h_add_i, RustM_ok_bind]
      apply Triple.pure
      simp only [SPred.entails_true_intro]
      intro _
      refine ⟨?_, ?_⟩
      · show v.val.size - (i + 1).toNat < v.val.size - i.toNat
        rw [h_i1]; omega
      · refine ⟨by rw [h_i1]; omega, ?_⟩
        show (result.val ++ #[v.val[i.toNat]'hi_lt]).size =
              (i + 1).toNat + (if ins then 1 else 0)
        rw [Array.size_append, h_r_sz, h_i1]
        show i.toNat + (if ins then 1 else 0) + 1 = (i.toNat + 1) + (if ins then 1 else 0)
        omega

private theorem is_loop_triple (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h_v_sz : v.val.size + 1 < USize64.size) :
    ⦃⌜ isInv v ⟨(0 : usize), false, ⟨([] : List i64).toArray, by grind⟩⟩ ⌝⦄
      isLoop v x
    ⦃⇓ r => ⌜ isInv v r ∧ ¬ isCond v r = true ⌝⦄ := by
  apply Std.Do.Spec.MonoLoopCombinator.while_loop
    (rust_primitives.hax.Tuple3.mk (0 : usize) false
      ⟨([] : List i64).toArray, by grind⟩) Lean.Loop.mk
    (isCond v) (isBody v x) (isInv v) (isTerm v)
  intro s hcond hinv
  have h := is_body_step v x h_v_sz s hcond hinv
  exact h hinv

private instance : Inhabited (Tuple3 usize Bool (alloc.vec.Vec i64 alloc.alloc.Global)) :=
  ⟨rust_primitives.hax.Tuple3.mk (0 : usize) false ⟨([] : List i64).toArray, by grind⟩⟩

private theorem is_loop_total (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h_v_sz : v.val.size + 1 < USize64.size) :
    ∃ r : Tuple3 usize Bool (alloc.vec.Vec i64 alloc.alloc.Global),
      isLoop v x = RustM.ok r ∧
      r._2.val.size = v.val.size + (if r._1 then 1 else 0) := by
  classical
  have h_init_inv : isInv v ⟨(0 : usize), false, ⟨([] : List i64).toArray, by grind⟩⟩ := by
    refine ⟨?_, ?_⟩
    · show (0 : usize).toNat ≤ v.val.size; rw [usize_zero_toNat]; omega
    · show (([] : List i64).toArray).size = (0 : usize).toNat + (if false then 1 else 0)
      simp [usize_zero_toNat]
  have h_loop := is_loop_triple v x h_v_sz
  have h_loop_size :
      ⦃⌜ isInv v ⟨(0 : usize), false, ⟨([] : List i64).toArray, by grind⟩⟩ ⌝⦄
        isLoop v x
      ⦃⇓ r => ⌜ r._2.val.size = v.val.size + (if r._1 then 1 else 0) ⌝⦄ := by
    apply Triple.of_entails_right _ _ _ _ h_loop
    apply PostCond.entails.of_left_entails
    intro r ⟨hinv, hncond⟩
    have hi_le : r._0.toNat ≤ v.val.size := hinv.1
    have h_r_sz : r._2.val.size = r._0.toNat + (if r._1 then 1 else 0) := hinv.2
    have h_ofNat_v : (USize64.ofNat v.val.size).toNat = v.val.size :=
      USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
    have h_not_cond : ¬ decide (r._0.toNat < (USize64.ofNat v.val.size).toNat) = true := hncond
    have hi_ge : v.val.size ≤ r._0.toNat := by
      rw [h_ofNat_v, decide_eq_true_iff] at h_not_cond; omega
    have hi_eq : r._0.toNat = v.val.size := by omega
    show r._2.val.size = v.val.size + (if r._1 then 1 else 0)
    rw [h_r_sz, hi_eq]
  have h_loop_size' :
      ⦃⌜ True ⌝⦄
        isLoop v x
      ⦃⇓ r => ⌜ r._2.val.size = v.val.size + (if r._1 then 1 else 0) ⌝⦄ := by
    apply Triple.of_entails_left _ _ _ _ h_loop_size
    intro _; exact h_init_inv
  rw [RustM.Triple_iff_BitVec] at h_loop_size'
  simp only [decide_true, Bool.not_true, Bool.false_or,
             Bool.and_eq_true, decide_eq_true_eq] at h_loop_size'
  obtain ⟨hok, hpost⟩ := h_loop_size'
  cases hf : isLoop v x with
  | none => rw [hf] at hok; simp [RustM.toBVRustM] at hok
  | some result =>
    cases result with
    | ok r =>
      rw [hf] at hpost
      simp only [RustM.toBVRustM] at hpost
      exact ⟨r, rfl, hpost⟩
    | error e =>
      rw [hf] at hok
      cases e <;> simp [RustM.toBVRustM] at hok

/-! ## vec_count helpers. -/

private theorem vec_count_append_le (a b : Array i64) (y : i64) :
    ∀ k : Nat, k ≤ a.size →
      vec_count (a ++ b) y k = vec_count a y k := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk_le : k ≤ a.size := by omega
    have hk_lt_a : k < a.size := by omega
    have hk_lt_ab : k < (a ++ b).size := by
      rw [Array.size_append]; omega
    have h_unfold_ab :
        vec_count (a ++ b) y (k + 1) =
          (if h : k < (a ++ b).size then
            (if ((a ++ b)[k]'h) = y then 1 else 0) + vec_count (a ++ b) y k
          else vec_count (a ++ b) y k) := rfl
    have h_unfold_a :
        vec_count a y (k + 1) =
          (if h : k < a.size then
            (if (a[k]'h) = y then 1 else 0) + vec_count a y k
          else vec_count a y k) := rfl
    rw [h_unfold_ab, h_unfold_a, dif_pos hk_lt_ab, dif_pos hk_lt_a]
    rw [Array.getElem_append_left hk_lt_a]
    rw [ih hk_le]

private theorem vec_count_append_singleton (a : Array i64) (c y : i64) :
    vec_count (a ++ #[c]) y (a ++ #[c]).size =
      vec_count a y a.size + (if c = y then 1 else 0) := by
  have h_sz : (a ++ #[c]).size = a.size + 1 := by rw [Array.size_append]; rfl
  rw [h_sz]
  have h_unfold :
      vec_count (a ++ #[c]) y (a.size + 1) =
        (if h : a.size < (a ++ #[c]).size then
          (if ((a ++ #[c])[a.size]'h) = y then 1 else 0) + vec_count (a ++ #[c]) y a.size
        else vec_count (a ++ #[c]) y a.size) := rfl
  rw [h_unfold]
  have h_sz_lt : a.size < (a ++ #[c]).size := by rw [h_sz]; omega
  rw [dif_pos h_sz_lt]
  have h_get_c : ((a ++ #[c])[a.size]'h_sz_lt) = c := by
    rw [Array.getElem_append_right (Nat.le_refl _)]
    simp [Nat.sub_self]
  rw [h_get_c]
  rw [vec_count_append_le a #[c] y a.size (Nat.le_refl _)]
  omega

private theorem vec_count_succ (a : Array i64) (y : i64) (k : Nat) (hk : k < a.size) :
    vec_count a y (k + 1) = (if (a[k]'hk) = y then 1 else 0) + vec_count a y k := by
  show (if h : k < a.size then (if (a[k]'h) = y then 1 else 0) + vec_count a y k
        else vec_count a y k) = _
  rw [dif_pos hk]

/-! ## Strengthened invariant: count clause. -/

private def isInvCount (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (s : Tuple3 usize Bool (alloc.vec.Vec i64 alloc.alloc.Global)) : Prop :=
  isInv v s ∧
  (∀ y, vec_count s._2.val y s._2.val.size =
        vec_count v.val y s._0.toNat + (if s._1 ∧ y = x then 1 else 0))

private theorem is_body_step_count (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h_v_sz : v.val.size + 1 < USize64.size)
    (s : Tuple3 usize Bool (alloc.vec.Vec i64 alloc.alloc.Global))
    (hcond : isCond v s = true) (hinv : isInvCount v x s) :
    ⦃⌜ isInvCount v x s ⌝⦄
      isBody v x s
    ⦃⇓ s' => spred(⌜ isTerm v s' < isTerm v s ⌝ ∧ ⌜ isInvCount v x s' ⌝)⦄ := by
  cases s with
  | mk i ins result =>
    obtain ⟨hinv_orig, h_count⟩ := hinv
    have h_ofNat_v : (USize64.ofNat v.val.size).toNat = v.val.size :=
      USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
    have hi_lt : i.toNat < v.val.size := by
      have h : decide (i.toNat < (USize64.ofNat v.val.size).toNat) = true := hcond
      rw [h_ofNat_v] at h
      exact decide_eq_true_iff.mp h
    have hi_le : i.toNat ≤ v.val.size := hinv_orig.1
    have h_r_sz : result.val.size = i.toNat + (if ins then 1 else 0) := hinv_orig.2
    have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
    have h_v_sz' : v.val.size + 1 < 2 ^ 64 := by rw [h_usize_size] at h_v_sz; exact h_v_sz
    have h_no_ov_i : i.toNat + 1 < 2 ^ 64 := by omega
    have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
    have h_vi : (v[i]_? : RustM i64) = RustM.ok (v.val[i.toNat]'hi_lt) :=
      vec_get_pure v i hi_lt
    have h_add_i : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
      usize_add_one_pure i h_no_ov_i
    have h_r_sz_le : result.val.size ≤ i.toNat + 1 := by
      rw [h_r_sz]; by_cases h : ins
      · simp [h]
      · simp [h]
    have h_r_first_ok : result.val.size + 1 < USize64.size := by
      rw [h_usize_size]; omega
    dsimp only [isBody]
    have h_not_ins : (!? ins : RustM Bool) = pure (!ins) := rfl
    have h_vi_ge_x : ((v.val[i.toNat]'hi_lt) >=? x : RustM Bool) =
                      pure (decide ((v.val[i.toNat]'hi_lt) ≥ x)) := rfl
    rw [h_not_ins, pure_bind, h_vi, RustM_ok_bind, h_vi_ge_x, pure_bind]
    rw [show (rust_primitives.hax.logical_op.and (!ins) (decide ((v.val[i.toNat]'hi_lt) ≥ x))
              : RustM Bool) = pure (!ins && decide ((v.val[i.toNat]'hi_lt) ≥ x)) from rfl]
    rw [pure_bind]
    by_cases h_branch : (!ins && decide ((v.val[i.toNat]'hi_lt) ≥ x)) = true
    · have h_ins_false : ins = false := by
        cases ins
        · rfl
        · simp at h_branch
      have h_r_sz_init : result.val.size = i.toNat := by
        rw [h_r_sz, h_ins_false]; simp
      have h_r_first_ok' : result.val.size + 1 < USize64.size := by
        rw [h_r_sz_init, h_usize_size]; omega
      rw [if_pos h_branch]
      rw [unsize_singleton, RustM_ok_bind,
          extend_from_slice_singleton result x h_r_first_ok', RustM_ok_bind, pure_bind]
      simp only [h_vi, RustM_ok_bind, unsize_singleton]
      simp only [extend_from_slice_singleton _ _
                  (by show (push_one result x h_r_first_ok').val.size + 1 < USize64.size
                      show (result.val ++ #[x]).size + 1 < USize64.size
                      rw [Array.size_append, h_r_sz_init, h_usize_size]
                      show i.toNat + 1 + 1 < 2 ^ 64; omega),
                 RustM_ok_bind, h_add_i, RustM_ok_bind]
      apply Triple.pure
      simp only [SPred.entails_true_intro]
      intro _
      refine ⟨?_, ?_, ?_⟩
      · show v.val.size - (i + 1).toNat < v.val.size - i.toNat
        rw [h_i1]; omega
      · refine ⟨by rw [h_i1]; omega, ?_⟩
        show ((result.val ++ #[x]) ++ #[v.val[i.toNat]'hi_lt]).size = (i + 1).toNat + 1
        rw [Array.size_append, Array.size_append, h_r_sz_init, h_i1]; rfl
      · intro y
        show vec_count ((result.val ++ #[x]) ++ #[v.val[i.toNat]'hi_lt]) y
              ((result.val ++ #[x]) ++ #[v.val[i.toNat]'hi_lt]).size =
              vec_count v.val y (i + 1).toNat + (if (true : Bool) = true ∧ y = x then 1 else 0)
        rw [vec_count_append_singleton, vec_count_append_singleton]
        have h_count_app : vec_count result.val y result.val.size =
            vec_count v.val y i.toNat +
              (if (ins : Bool) = true ∧ y = x then 1 else 0) := h_count y
        rw [h_count_app, h_ins_false]
        have h_vc_succ : vec_count v.val y (i + 1).toNat =
            (if (v.val[i.toNat]'hi_lt) = y then 1 else 0) + vec_count v.val y i.toNat := by
          rw [h_i1]; exact vec_count_succ v.val y i.toNat hi_lt
        rw [h_vc_succ]
        simp only [Bool.false_eq_true, false_and, if_false, Nat.add_zero, true_and]
        by_cases h_xy : x = y
        · rw [if_pos h_xy, if_pos h_xy.symm]; omega
        · rw [if_neg h_xy, if_neg (Ne.symm h_xy)]; omega
    · rw [if_neg h_branch]
      rw [pure_bind]
      simp only [h_vi, RustM_ok_bind, unsize_singleton]
      simp only [extend_from_slice_singleton _ _ h_r_first_ok,
                 RustM_ok_bind, h_add_i, RustM_ok_bind]
      apply Triple.pure
      simp only [SPred.entails_true_intro]
      intro _
      refine ⟨?_, ?_, ?_⟩
      · show v.val.size - (i + 1).toNat < v.val.size - i.toNat
        rw [h_i1]; omega
      · refine ⟨by rw [h_i1]; omega, ?_⟩
        show (result.val ++ #[v.val[i.toNat]'hi_lt]).size =
              (i + 1).toNat + (if ins then 1 else 0)
        rw [Array.size_append, h_r_sz, h_i1]
        show i.toNat + (if ins then 1 else 0) + 1 = (i.toNat + 1) + (if ins then 1 else 0)
        omega
      · intro y
        show vec_count (result.val ++ #[v.val[i.toNat]'hi_lt]) y
              (result.val ++ #[v.val[i.toNat]'hi_lt]).size =
              vec_count v.val y (i + 1).toNat + (if (ins : Bool) = true ∧ y = x then 1 else 0)
        rw [vec_count_append_singleton]
        have h_count_app : vec_count result.val y result.val.size =
            vec_count v.val y i.toNat +
              (if (ins : Bool) = true ∧ y = x then 1 else 0) := h_count y
        rw [h_count_app]
        have h_vc_succ : vec_count v.val y (i + 1).toNat =
            (if (v.val[i.toNat]'hi_lt) = y then 1 else 0) + vec_count v.val y i.toNat := by
          rw [h_i1]; exact vec_count_succ v.val y i.toNat hi_lt
        rw [h_vc_succ]
        omega

private theorem is_loop_triple_count (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h_v_sz : v.val.size + 1 < USize64.size) :
    ⦃⌜ isInvCount v x ⟨(0 : usize), false, ⟨([] : List i64).toArray, by grind⟩⟩ ⌝⦄
      isLoop v x
    ⦃⇓ r => ⌜ isInvCount v x r ∧ ¬ isCond v r = true ⌝⦄ := by
  apply Std.Do.Spec.MonoLoopCombinator.while_loop
    (rust_primitives.hax.Tuple3.mk (0 : usize) false
      ⟨([] : List i64).toArray, by grind⟩) Lean.Loop.mk
    (isCond v) (isBody v x) (isInvCount v x) (isTerm v)
  intro s hcond hinv
  have h := is_body_step_count v x h_v_sz s hcond hinv
  exact h hinv

private theorem is_loop_total_count (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h_v_sz : v.val.size + 1 < USize64.size) :
    ∃ r : Tuple3 usize Bool (alloc.vec.Vec i64 alloc.alloc.Global),
      isLoop v x = RustM.ok r ∧
      r._2.val.size = v.val.size + (if r._1 then 1 else 0) ∧
      (∀ y, vec_count r._2.val y r._2.val.size =
            vec_count v.val y v.val.size + (if r._1 ∧ y = x then 1 else 0)) := by
  classical
  have h_init_invc : isInvCount v x ⟨(0 : usize), false, ⟨([] : List i64).toArray, by grind⟩⟩ := by
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · show (0 : usize).toNat ≤ v.val.size; rw [usize_zero_toNat]; omega
      · show (([] : List i64).toArray).size = (0 : usize).toNat + (if false then 1 else 0)
        simp [usize_zero_toNat]
    · intro y
      show vec_count (([] : List i64).toArray) y (([] : List i64).toArray).size =
            vec_count v.val y (0 : usize).toNat + (if (false : Bool) = true ∧ y = x then 1 else 0)
      have : ([] : List i64).toArray.size = 0 := rfl
      rw [this, usize_zero_toNat]
      show 0 = vec_count v.val y 0 + (if False ∧ y = x then 1 else 0)
      simp
      rfl
  have h_loop := is_loop_triple_count v x h_v_sz
  have h_loop_proj :
      ⦃⌜ True ⌝⦄
        isLoop v x
      ⦃⇓ r => ⌜ r._2.val.size = v.val.size + (if r._1 then 1 else 0) ∧
                (∀ y, vec_count r._2.val y r._2.val.size =
                      vec_count v.val y v.val.size + (if r._1 ∧ y = x then 1 else 0)) ⌝⦄ := by
    apply Triple.of_entails_left _ _ _ _ ?_
    · intro _; exact h_init_invc
    apply Triple.of_entails_right _ _ _ _ h_loop
    apply PostCond.entails.of_left_entails
    intro r ⟨hinvc, hncond⟩
    obtain ⟨hinv, h_count⟩ := hinvc
    have h_ofNat_v : (USize64.ofNat v.val.size).toNat = v.val.size :=
      USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
    have h_not_cond : ¬ decide (r._0.toNat < (USize64.ofNat v.val.size).toNat) = true := hncond
    have hi_ge : v.val.size ≤ r._0.toNat := by
      rw [h_ofNat_v, decide_eq_true_iff] at h_not_cond; omega
    have hi_eq : r._0.toNat = v.val.size := by
      have hi_le : r._0.toNat ≤ v.val.size := hinv.1; omega
    refine ⟨?_, ?_⟩
    · rw [hinv.2, hi_eq]
    · intro y; rw [h_count y, hi_eq]
  rw [RustM.Triple_iff_BitVec] at h_loop_proj
  simp only [decide_true, Bool.not_true, Bool.false_or,
             Bool.and_eq_true, decide_eq_true_eq] at h_loop_proj
  obtain ⟨hok, hpost⟩ := h_loop_proj
  cases hf : isLoop v x with
  | none => rw [hf] at hok; simp [RustM.toBVRustM] at hok
  | some result =>
    cases result with
    | ok r =>
      rw [hf] at hpost
      simp only [RustM.toBVRustM] at hpost
      exact ⟨r, rfl, hpost.1, hpost.2⟩
    | error e =>
      rw [hf] at hok
      cases e <;> simp [RustM.toBVRustM] at hok

private theorem insert_sorted_spec (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h_v_sz : v.val.size + 1 < USize64.size) :
    ∃ r : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_032_sort_third.insert_sorted v x = RustM.ok r ∧
      r.val.size = v.val.size + 1 ∧
      (∀ y, vec_count r.val y r.val.size =
            vec_count v.val y v.val.size + (if y = x then 1 else 0)) := by
  obtain ⟨s, h_loop_eq, h_s_sz, h_s_count⟩ := is_loop_total_count v x h_v_sz
  unfold clever_032_sort_third.insert_sorted
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨([] : List i64).toArray, by grind⟩ := rfl
  have h_len : (alloc.vec.Impl_1.len i64 alloc.alloc.Global v :
                  RustM usize) = RustM.ok (USize64.ofNat v.val.size) := rfl
  rw [h_new]
  simp only [RustM_ok_bind]
  rw [h_len]
  simp only [RustM_ok_bind]
  unfold rust_primitives.hax.while_loop
  rw [show
    Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk
      (fun b => decide (USize64.toNat b._0 < (USize64.ofNat v.val.size).toNat))
      (rust_primitives.hax.Tuple3.mk (0 : usize) false
        ⟨([] : List i64).toArray, by grind⟩)
      (isBody v x) = isLoop v x from rfl]
  rw [h_loop_eq]
  simp only [RustM_ok_bind]
  have h_not_s1 : (!? s._1 : RustM Bool) = pure (!s._1) := rfl
  rw [h_not_s1, pure_bind]
  by_cases h_ins : s._1 = true
  · rw [h_ins]
    simp only [Bool.not_true, Bool.false_eq_true, if_false]
    refine ⟨s._2, rfl, ?_, ?_⟩
    · rw [h_s_sz, h_ins]; simp
    · intro y
      have h_c := h_s_count y
      rw [h_ins] at h_c
      simp at h_c
      rw [h_c]
  · have h_ins_false : s._1 = false := by
      cases hs : s._1
      · rfl
      · exfalso; apply h_ins; exact hs
    rw [h_ins_false]
    simp only [Bool.not_false, if_true]
    have h_s2_sz : s._2.val.size = v.val.size := by
      rw [h_s_sz, h_ins_false]; simp
    have h_s2_ok : s._2.val.size + 1 < USize64.size := by
      rw [h_s2_sz]; exact h_v_sz
    rw [show (rust_primitives.unsize ({ toVec := #v[x] } : RustArray i64 1) :
              RustM (rust_primitives.sequence.Seq i64))
              = RustM.ok ⟨#[x], one_lt_usize_size⟩ from rfl]
    simp only [RustM_ok_bind]
    rw [show (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global s._2
                ⟨#[x], one_lt_usize_size⟩ :
                RustM (alloc.vec.Vec i64 alloc.alloc.Global))
              = RustM.ok (push_one s._2 x h_s2_ok) from by
      unfold alloc.vec.Impl_2.extend_from_slice
      rw [dif_pos (show s._2.val.size + (#[x] : Array i64).size < USize64.size from h_s2_ok)]
      rfl]
    simp only [RustM_ok_bind]
    refine ⟨push_one s._2 x h_s2_ok, rfl, ?_, ?_⟩
    · show (s._2.val ++ #[x]).size = v.val.size + 1
      rw [Array.size_append, h_s2_sz]; rfl
    · intro y
      show vec_count (s._2.val ++ #[x]) y (s._2.val ++ #[x]).size =
            vec_count v.val y v.val.size + (if y = x then 1 else 0)
      rw [vec_count_append_singleton]
      have h_c := h_s_count y
      rw [h_ins_false] at h_c
      simp at h_c
      rw [h_c]
      by_cases h_xy : x = y
      · rw [if_pos h_xy, if_pos h_xy.symm]
      · rw [if_neg h_xy, if_neg (Ne.symm h_xy)]

private theorem insert_sorted_total (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h_v_sz : v.val.size + 1 < USize64.size) :
    ∃ r : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_032_sort_third.insert_sorted v x = RustM.ok r ∧
      r.val.size = v.val.size + 1 := by
  obtain ⟨r, h_eq, h_sz, _⟩ := insert_sorted_spec v x h_v_sz
  exact ⟨r, h_eq, h_sz⟩

/-! ## collect_thirds step lemmas. -/

private theorem collect_thirds_oob (l : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : l.val.size ≤ i.toNat) :
    clever_032_sort_third.collect_thirds l i acc = RustM.ok acc := by
  conv => lhs; unfold clever_032_sort_third.collect_thirds
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

private theorem collect_thirds_step_third (l : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < l.val.size)
    (hmod : i.toNat % 3 = 0)
    (acc' : alloc.vec.Vec i64 alloc.alloc.Global)
    (h_ins : clever_032_sort_third.insert_sorted acc (l.val[i.toNat]'hi) = RustM.ok acc') :
    clever_032_sort_third.collect_thirds l i acc =
      clever_032_sort_third.collect_thirds l (i + 1) acc' := by
  conv => lhs; unfold clever_032_sort_third.collect_thirds
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx_l : (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi) :=
    vec_get_pure l i hi
  have h_no_ov_i : i.toNat + 1 < 2 ^ 64 := by
    rw [h_usize_size] at h_size_lt; omega
  have h_add_i : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
    usize_add_one_pure i h_no_ov_i
  have h_mod_eq : decide (i.toNat % 3 = 0) = true := decide_eq_true hmod
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             usize_mod_three_pure, mod3_eq_zero_pure, h_mod_eq,
             h_idx_l, h_ins, h_add_i]

private theorem collect_thirds_step_other (l : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < l.val.size)
    (hmod : i.toNat % 3 ≠ 0) :
    clever_032_sort_third.collect_thirds l i acc =
      clever_032_sort_third.collect_thirds l (i + 1) acc := by
  conv => lhs; unfold clever_032_sort_third.collect_thirds
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_no_ov_i : i.toNat + 1 < 2 ^ 64 := by
    rw [h_usize_size] at h_size_lt; omega
  have h_add_i : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
    usize_add_one_pure i h_no_ov_i
  have h_mod_eq : decide (i.toNat % 3 = 0) = false := decide_eq_false hmod
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             usize_mod_three_pure, mod3_eq_zero_pure, h_mod_eq,
             h_add_i]

/-! ## Spec helper: count of value at third indices in a slice in range [i, k). -/

private def third_count_range (a : Array i64) (x : i64) (i : Nat) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      if h : k < a.size then
        (if i ≤ k ∧ k % 3 = 0 ∧ (a[k]'h) = x then 1 else 0) + third_count_range a x i k
      else
        third_count_range a x i k

private theorem third_count_range_zero (a : Array i64) (x : i64) :
    ∀ k : Nat, third_count_range a x 0 k = third_count a x k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show (if h : k < a.size then
            (if 0 ≤ k ∧ k % 3 = 0 ∧ (a[k]'h) = x then 1 else 0) + third_count_range a x 0 k
          else third_count_range a x 0 k) =
          (if h : k < a.size then
            (if k % 3 = 0 ∧ (a[k]'h) = x then 1 else 0) + third_count a x k
          else third_count a x k)
    by_cases hk : k < a.size
    · rw [dif_pos hk, dif_pos hk, ih]
      have : (0 ≤ k ∧ k % 3 = 0 ∧ (a[k]'hk) = x) ↔ (k % 3 = 0 ∧ (a[k]'hk) = x) := by
        constructor
        · intro ⟨_, h⟩; exact h
        · intro h; exact ⟨Nat.zero_le _, h⟩
      rw [show (if 0 ≤ k ∧ k % 3 = 0 ∧ (a[k]'hk) = x then (1 : Nat) else 0) =
              (if k % 3 = 0 ∧ (a[k]'hk) = x then (1 : Nat) else 0) by
            by_cases h : k % 3 = 0 ∧ (a[k]'hk) = x
            · rw [if_pos h, if_pos (this.mpr h)]
            · rw [if_neg h, if_neg (fun h' => h (this.mp h'))]]
    · rw [dif_neg hk, dif_neg hk, ih]

private theorem third_count_range_eq_third_count (a : Array i64) (x : i64) (k : Nat) :
    third_count_range a x 0 k = third_count a x k :=
  third_count_range_zero a x k

private theorem third_count_range_empty (a : Array i64) (x : i64) :
    ∀ (i k : Nat), k ≤ i → third_count_range a x i k = 0 := by
  intro i k hki
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk_le : k < i := by omega
    have hk_le' : k ≤ i := by omega
    show (if h : k < a.size then
            (if i ≤ k ∧ k % 3 = 0 ∧ (a[k]'h) = x then 1 else 0) + third_count_range a x i k
          else third_count_range a x i k) = 0
    by_cases hk : k < a.size
    · rw [dif_pos hk, ih hk_le']
      have h_not : ¬ (i ≤ k ∧ k % 3 = 0 ∧ (a[k]'hk) = x) := by
        intro ⟨h1, _⟩; omega
      rw [if_neg h_not]
    · rw [dif_neg hk]; exact ih hk_le'

private theorem third_count_split (a : Array i64) (x : i64) (i k : Nat) (hik : i ≤ k) :
    third_count a x k = third_count a x i + third_count_range a x i k := by
  induction k with
  | zero =>
    have : i = 0 := by omega
    rw [this]
    rfl
  | succ k ih =>
    by_cases hi_le_k : i ≤ k
    · have h_unfold_tc :
          third_count a x (k + 1) =
            (if h : k < a.size then
              (if k % 3 = 0 ∧ (a[k]'h) = x then 1 else 0) + third_count a x k
            else third_count a x k) := rfl
      have h_unfold_tcr :
          third_count_range a x i (k + 1) =
            (if h : k < a.size then
              (if i ≤ k ∧ k % 3 = 0 ∧ (a[k]'h) = x then 1 else 0) + third_count_range a x i k
            else third_count_range a x i k) := rfl
      rw [h_unfold_tc, h_unfold_tcr, ih hi_le_k]
      by_cases hk : k < a.size
      · rw [dif_pos hk, dif_pos hk]
        have h_iff : (i ≤ k ∧ k % 3 = 0 ∧ (a[k]'hk) = x) ↔ (k % 3 = 0 ∧ (a[k]'hk) = x) := by
          constructor
          · intro ⟨_, h⟩; exact h
          · intro h; exact ⟨hi_le_k, h⟩
        rw [show (if i ≤ k ∧ k % 3 = 0 ∧ (a[k]'hk) = x then (1 : Nat) else 0) =
                (if k % 3 = 0 ∧ (a[k]'hk) = x then (1 : Nat) else 0) by
              by_cases h : k % 3 = 0 ∧ (a[k]'hk) = x
              · rw [if_pos h, if_pos (h_iff.mpr h)]
              · rw [if_neg h, if_neg (fun h' => h (h_iff.mp h'))]]
        omega
      · rw [dif_neg hk, dif_neg hk]
    · have h_eq : i = k + 1 := by omega
      rw [h_eq]
      rw [third_count_range_empty a x (k + 1) (k + 1) (Nat.le_refl _)]

/-! ## collect_thirds totality and count tracking. -/

private theorem collect_thirds_spec (l : RustSlice i64) :
    ∀ (m : Nat) (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global),
      l.val.size - i.toNat ≤ m →
      i.toNat ≤ l.val.size →
      acc.val.size = thirdIdxCount i.toNat →
      ∃ sorted : alloc.vec.Vec i64 alloc.alloc.Global,
        clever_032_sort_third.collect_thirds l i acc = RustM.ok sorted ∧
        sorted.val.size = thirdIdxCount l.val.size ∧
        (∀ y, vec_count sorted.val y sorted.val.size =
              vec_count acc.val y acc.val.size +
              third_count_range l.val y i.toNat l.val.size) := by
  intro m
  induction m with
  | zero =>
    intro i acc hm hi_le hacc_sz
    have hi_eq : i.toNat = l.val.size := by omega
    have hi_ge : l.val.size ≤ i.toNat := by omega
    refine ⟨acc, collect_thirds_oob l i acc hi_ge, ?_, ?_⟩
    · rw [hacc_sz, hi_eq]
    · intro y
      rw [third_count_range_empty l.val y i.toNat l.val.size (by omega)]
  | succ m ih =>
    intro i acc hm hi_le hacc_sz
    by_cases hi_ge : l.val.size ≤ i.toNat
    · have hi_eq : i.toNat = l.val.size := by omega
      refine ⟨acc, collect_thirds_oob l i acc hi_ge, ?_, ?_⟩
      · rw [hacc_sz, hi_eq]
      · intro y
        rw [third_count_range_empty l.val y i.toNat l.val.size (by omega)]
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2 ^ 64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_meas : l.val.size - (i + 1).toNat ≤ m := by rw [h_i1]; omega
      have h_split_tcr : ∀ y,
          third_count_range l.val y i.toNat l.val.size =
            (if i.toNat % 3 = 0 ∧ (l.val[i.toNat]'hi_lt) = y then 1 else 0) +
            third_count_range l.val y (i.toNat + 1) l.val.size := by
        intro y
        have h1 : third_count l.val y l.val.size =
            third_count l.val y i.toNat + third_count_range l.val y i.toNat l.val.size :=
          third_count_split l.val y i.toNat l.val.size (Nat.le_of_lt hi_lt)
        have h2 : third_count l.val y l.val.size =
            third_count l.val y (i.toNat + 1) + third_count_range l.val y (i.toNat + 1) l.val.size :=
          third_count_split l.val y (i.toNat + 1) l.val.size (by omega)
        have h3 : third_count l.val y (i.toNat + 1) =
            (if i.toNat % 3 = 0 ∧ (l.val[i.toNat]'hi_lt) = y then 1 else 0) +
            third_count l.val y i.toNat := by
          show (if h : i.toNat < l.val.size then
                  (if i.toNat % 3 = 0 ∧ (l.val[i.toNat]'h) = y then 1 else 0) + third_count l.val y i.toNat
                else third_count l.val y i.toNat) = _
          rw [dif_pos hi_lt]
        omega
      by_cases hmod : i.toNat % 3 = 0
      · have hacc_le : acc.val.size ≤ i.toNat := by
          rw [hacc_sz]; exact thirdIdxCount_le_self i.toNat
        have hacc_ok : acc.val.size + 1 < USize64.size := by
          rw [h_usize_size]; omega
        obtain ⟨acc', h_ins, h_acc'_sz, h_acc'_count⟩ :=
          insert_sorted_spec acc (l.val[i.toNat]'hi_lt) hacc_ok
        have h_step := collect_thirds_step_third l i acc hi_lt hmod acc' h_ins
        rw [h_step]
        have h_acc'_sz_new : acc'.val.size = thirdIdxCount (i + 1).toNat := by
          rw [h_acc'_sz, hacc_sz, h_i1]
          show thirdIdxCount i.toNat + 1 =
                if i.toNat % 3 = 0 then thirdIdxCount i.toNat + 1 else thirdIdxCount i.toNat
          rw [if_pos hmod]
        obtain ⟨sorted, h_ct, h_sorted_sz, h_sorted_count⟩ :=
          ih (i + 1) acc' h_meas h_i1_le h_acc'_sz_new
        refine ⟨sorted, h_ct, h_sorted_sz, ?_⟩
        intro y
        rw [h_sorted_count y, h_acc'_count y, h_i1, h_split_tcr y]
        by_cases h_eq : (l.val[i.toNat]'hi_lt) = y
        · have h1 : (if i.toNat % 3 = 0 ∧ (l.val[i.toNat]'hi_lt) = y then (1 : Nat) else 0) = 1 :=
            if_pos ⟨hmod, h_eq⟩
          have h2 : (if y = (l.val[i.toNat]'hi_lt) then (1 : Nat) else 0) = 1 :=
            if_pos h_eq.symm
          rw [h1, h2]; omega
        · have h1 : (if i.toNat % 3 = 0 ∧ (l.val[i.toNat]'hi_lt) = y then (1 : Nat) else 0) = 0 := by
            apply if_neg; intro ⟨_, h⟩; exact h_eq h
          have h2 : (if y = (l.val[i.toNat]'hi_lt) then (1 : Nat) else 0) = 0 := by
            apply if_neg; intro h; exact h_eq h.symm
          rw [h1, h2]; omega
      · rw [collect_thirds_step_other l i acc hi_lt hmod]
        have h_acc'_sz_new : acc.val.size = thirdIdxCount (i + 1).toNat := by
          rw [hacc_sz, h_i1]
          show thirdIdxCount i.toNat =
                if i.toNat % 3 = 0 then thirdIdxCount i.toNat + 1 else thirdIdxCount i.toNat
          rw [if_neg hmod]
        obtain ⟨sorted, h_ct, h_sorted_sz, h_sorted_count⟩ :=
          ih (i + 1) acc h_meas h_i1_le h_acc'_sz_new
        refine ⟨sorted, h_ct, h_sorted_sz, ?_⟩
        intro y
        rw [h_sorted_count y, h_i1, h_split_tcr y]
        have h1 : (if i.toNat % 3 = 0 ∧ (l.val[i.toNat]'hi_lt) = y then (1 : Nat) else 0) = 0 := by
          apply if_neg; intro ⟨h, _⟩; exact hmod h
        rw [h1]; omega

private theorem collect_thirds_total (l : RustSlice i64) :
    ∀ (m : Nat) (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global),
      l.val.size - i.toNat ≤ m →
      i.toNat ≤ l.val.size →
      acc.val.size = thirdIdxCount i.toNat →
      ∃ sorted : alloc.vec.Vec i64 alloc.alloc.Global,
        clever_032_sort_third.collect_thirds l i acc = RustM.ok sorted ∧
        sorted.val.size = thirdIdxCount l.val.size := by
  intro m i acc hm hi_le hacc_sz
  obtain ⟨sorted, h_ct, h_sz, _⟩ := collect_thirds_spec l m i acc hm hi_le hacc_sz
  exact ⟨sorted, h_ct, h_sz⟩

/-! ## Auxiliary: unfold `sort_third`. -/

private theorem sort_third_unfold (l : RustSlice i64) :
    clever_032_sort_third.sort_third l =
      (clever_032_sort_third.collect_thirds l (0 : usize)
        ⟨([] : List i64).toArray, by grind⟩) >>= fun sorted =>
        clever_032_sort_third.rebuild_at l sorted (0 : usize) (0 : usize)
          ⟨([] : List i64).toArray, by grind⟩ := by
  unfold clever_032_sort_third.sort_third
  have h_new :
      (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
        RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
        RustM.ok ⟨([] : List i64).toArray, by grind⟩ := rfl
  rw [h_new, RustM_ok_bind]
  apply bind_congr
  intro sorted
  have h_deref :
      (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec i64 alloc.alloc.Global) sorted :
        RustM (alloc.vec.Vec i64 alloc.alloc.Global)) = RustM.ok sorted := rfl
  rw [h_deref, RustM_ok_bind, RustM_ok_bind]

private theorem sort_third_split (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_032_sort_third.sort_third l = RustM.ok v) :
    ∃ sorted : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_032_sort_third.collect_thirds l (0 : usize)
        ⟨([] : List i64).toArray, by grind⟩ = RustM.ok sorted ∧
      clever_032_sort_third.rebuild_at l sorted (0 : usize) (0 : usize)
        ⟨([] : List i64).toArray, by grind⟩ = RustM.ok v := by
  rw [sort_third_unfold] at hres
  generalize h_ct : clever_032_sort_third.collect_thirds l (0 : usize)
                      ⟨([] : List i64).toArray, by grind⟩ = rct at hres
  cases rct with
  | none =>
    exfalso
    simp only [bind, ExceptT.bind, ExceptT.mk, Option.bind] at hres
    cases hres
  | some res =>
    cases res with
    | error e =>
      exfalso
      simp only [bind, ExceptT.bind, ExceptT.mk, Option.bind] at hres
      cases hres
    | ok sorted =>
      refine ⟨sorted, rfl, ?_⟩
      simp only [bind, ExceptT.bind, ExceptT.mk, Option.bind] at hres
      exact hres

/-! ## Top-level obligations. -/

theorem length_preserved
    (l : RustSlice i64) (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_032_sort_third.sort_third l = RustM.ok v) :
    v.val.size = l.val.size := by
  obtain ⟨sorted, _h_ct, h_rb⟩ := sort_third_split l v hres
  let acc0 : alloc.vec.Vec i64 alloc.alloc.Global :=
    ⟨([] : List i64).toArray, by grind⟩
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_acc0_sz : acc0.val.size = (0 : usize).toNat := rfl
  have h_j_eq : (0 : usize).toNat = thirdIdxCount (0 : usize).toNat := by
    rw [h_zero_toNat]; rfl
  have h_acc0_inv :
      ∀ (k : Nat) (hk : k < acc0.val.size),
        k % 3 ≠ 0 →
        ∃ (hl : k < l.val.size), acc0.val[k]'hk = l.val[k]'hl := by
    intro k hk _
    exfalso
    have : acc0.val.size = 0 := rfl
    rw [this] at hk
    omega
  have h_meas : l.val.size - (0 : usize).toNat ≤ l.val.size := by
    rw [h_zero_toNat]; omega
  have h_i_le : (0 : usize).toNat ≤ l.val.size := by rw [h_zero_toNat]; omega
  obtain ⟨h_v_sz, _⟩ :=
    rebuild_at_hres_correct l sorted l.val.size (0 : usize) (0 : usize) acc0 v
      h_meas h_i_le h_j_eq h_acc0_sz h_acc0_inv h_rb
  exact h_v_sz

theorem non_third_indices_unchanged
    (l : RustSlice i64) (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_032_sort_third.sort_third l = RustM.ok v)
    (i : Nat) (hi_l : i < l.val.size) (hi_v : i < v.val.size)
    (hmod : i % 3 ≠ 0) :
    v.val[i]'hi_v = l.val[i]'hi_l := by
  obtain ⟨sorted, _h_ct, h_rb⟩ := sort_third_split l v hres
  let acc0 : alloc.vec.Vec i64 alloc.alloc.Global :=
    ⟨([] : List i64).toArray, by grind⟩
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_acc0_sz : acc0.val.size = (0 : usize).toNat := rfl
  have h_j_eq : (0 : usize).toNat = thirdIdxCount (0 : usize).toNat := by
    rw [h_zero_toNat]; rfl
  have h_acc0_inv :
      ∀ (k : Nat) (hk : k < acc0.val.size),
        k % 3 ≠ 0 →
        ∃ (hl : k < l.val.size), acc0.val[k]'hk = l.val[k]'hl := by
    intro k hk _
    exfalso
    have : acc0.val.size = 0 := rfl
    rw [this] at hk
    omega
  have h_meas : l.val.size - (0 : usize).toNat ≤ l.val.size := by
    rw [h_zero_toNat]; omega
  have h_i_le : (0 : usize).toNat ≤ l.val.size := by rw [h_zero_toNat]; omega
  obtain ⟨_, h_v_inv⟩ :=
    rebuild_at_hres_correct l sorted l.val.size (0 : usize) (0 : usize) acc0 v
      h_meas h_i_le h_j_eq h_acc0_sz h_acc0_inv h_rb
  obtain ⟨hl, hkeq⟩ := h_v_inv i hi_v hmod
  exact hkeq

theorem sort_third_total (l : RustSlice i64) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_032_sort_third.sort_third l = RustM.ok v := by
  let acc0 : alloc.vec.Vec i64 alloc.alloc.Global := ⟨([] : List i64).toArray, by grind⟩
  have h_acc0_sz : acc0.val.size = thirdIdxCount (0 : usize).toNat := by
    show (([] : List i64).toArray).size = thirdIdxCount 0
    rfl
  have h_zero_le : (0 : usize).toNat ≤ l.val.size := by
    rw [usize_zero_toNat]; omega
  have h_meas : l.val.size - (0 : usize).toNat ≤ l.val.size := by
    rw [usize_zero_toNat]; omega
  obtain ⟨sorted, h_ct, h_sorted_sz⟩ :=
    collect_thirds_total l l.val.size (0 : usize) acc0 h_meas h_zero_le h_acc0_sz
  have h_sorted_sz_le : thirdIdxCount l.val.size ≤ sorted.val.size := by
    rw [h_sorted_sz]; omega
  let acc1 : alloc.vec.Vec i64 alloc.alloc.Global := ⟨([] : List i64).toArray, by grind⟩
  have h_acc1_sz : acc1.val.size = (0 : usize).toNat := by
    show (([] : List i64).toArray).size = 0; rfl
  have h_j_eq : (0 : usize).toNat = thirdIdxCount (0 : usize).toNat := by
    rw [usize_zero_toNat]; rfl
  have h_acc1_inv :
      ∀ (k : Nat) (hk : k < acc1.val.size),
        if k % 3 = 0 then
          ∃ (hj : thirdIdxCount k < sorted.val.size),
            acc1.val[k]'hk = sorted.val[thirdIdxCount k]'hj
        else
          ∃ (hl : k < l.val.size),
            acc1.val[k]'hk = l.val[k]'hl := by
    intro k hk
    exfalso
    have : acc1.val.size = 0 := rfl
    rw [this] at hk; omega
  obtain ⟨v, h_rb, _, _⟩ :=
    rebuild_at_correct l sorted h_sorted_sz_le l.val.size (0 : usize) (0 : usize) acc1
      h_meas h_zero_le h_j_eq h_acc1_sz h_acc1_inv
  refine ⟨v, ?_⟩
  rw [sort_third_unfold]
  show clever_032_sort_third.collect_thirds l (0 : usize) acc0 >>= _ = RustM.ok v
  rw [h_ct]
  simp only [RustM_ok_bind]
  exact h_rb

/-! ## Sortedness infrastructure for insert_sorted's loop. -/

/-- Sortedness invariant: in addition to size/count, the result is sorted,
    every element of the result is ≤ every remaining v[m] (m ≥ i), and if
    not yet inserted, every element of the result is ≤ x. -/
private def isInvAll (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (s : Tuple3 usize Bool (alloc.vec.Vec i64 alloc.alloc.Global)) : Prop :=
  s._0.toNat ≤ v.val.size ∧
  s._2.val.size = s._0.toNat + (if s._1 then 1 else 0) ∧
  (∀ y, vec_count s._2.val y s._2.val.size =
        vec_count v.val y s._0.toNat + (if s._1 ∧ y = x then 1 else 0)) ∧
  arr_sorted s._2.val ∧
  (∀ k (hk : k < s._2.val.size) m, s._0.toNat ≤ m → ∀ (hmv : m < v.val.size),
    (s._2.val[k]'hk).toInt ≤ (v.val[m]'hmv).toInt) ∧
  (s._1 = false →
    ∀ k (hk : k < s._2.val.size), (s._2.val[k]'hk).toInt ≤ x.toInt)

private theorem is_body_step_all (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h_v_sz : v.val.size + 1 < USize64.size)
    (h_v_sorted : arr_sorted v.val)
    (s : Tuple3 usize Bool (alloc.vec.Vec i64 alloc.alloc.Global))
    (hcond : isCond v s = true) (hinv : isInvAll v x s) :
    ⦃⌜ isInvAll v x s ⌝⦄
      isBody v x s
    ⦃⇓ s' => spred(⌜ isTerm v s' < isTerm v s ⌝ ∧ ⌜ isInvAll v x s' ⌝)⦄ := by
  cases s with
  | mk i ins result =>
    obtain ⟨hi_le, h_r_sz, h_count, h_sorted, h_le_v, h_le_x⟩ := hinv
    have h_ofNat_v : (USize64.ofNat v.val.size).toNat = v.val.size :=
      USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
    have hi_lt : i.toNat < v.val.size := by
      have h : decide (i.toNat < (USize64.ofNat v.val.size).toNat) = true := hcond
      rw [h_ofNat_v] at h
      exact decide_eq_true_iff.mp h
    have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
    have h_v_sz' : v.val.size + 1 < 2 ^ 64 := by rw [h_usize_size] at h_v_sz; exact h_v_sz
    have h_no_ov_i : i.toNat + 1 < 2 ^ 64 := by omega
    have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
    have h_vi : (v[i]_? : RustM i64) = RustM.ok (v.val[i.toNat]'hi_lt) :=
      vec_get_pure v i hi_lt
    have h_add_i : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
      usize_add_one_pure i h_no_ov_i
    have h_r_sz_le : result.val.size ≤ i.toNat + 1 := by
      rw [h_r_sz]; by_cases h : ins
      · simp [h]
      · simp [h]
    have h_r_first_ok : result.val.size + 1 < USize64.size := by
      rw [h_usize_size]; omega
    dsimp only [isBody]
    have h_not_ins : (!? ins : RustM Bool) = pure (!ins) := rfl
    have h_vi_ge_x : ((v.val[i.toNat]'hi_lt) >=? x : RustM Bool) =
                      pure (decide ((v.val[i.toNat]'hi_lt) ≥ x)) := rfl
    rw [h_not_ins, pure_bind, h_vi, RustM_ok_bind, h_vi_ge_x, pure_bind]
    rw [show (rust_primitives.hax.logical_op.and (!ins) (decide ((v.val[i.toNat]'hi_lt) ≥ x))
              : RustM Bool) = pure (!ins && decide ((v.val[i.toNat]'hi_lt) ≥ x)) from rfl]
    rw [pure_bind]
    by_cases h_branch : (!ins && decide ((v.val[i.toNat]'hi_lt) ≥ x)) = true
    · -- First-extend branch: ins = false ∧ v[i] ≥ x
      have h_ins_false : ins = false := by
        cases ins
        · rfl
        · simp at h_branch
      have h_vi_ge : (v.val[i.toNat]'hi_lt) ≥ x := by
        rw [h_ins_false] at h_branch
        simp only [Bool.not_false, Bool.true_and] at h_branch
        exact decide_eq_true_iff.mp h_branch
      have h_x_le_vi_int : x.toInt ≤ (v.val[i.toNat]'hi_lt).toInt :=
        Int64.le_iff_toInt_le.mp h_vi_ge
      have h_r_sz_init : result.val.size = i.toNat := by
        rw [h_r_sz, h_ins_false]; simp
      have h_r_first_ok' : result.val.size + 1 < USize64.size := by
        rw [h_r_sz_init, h_usize_size]; omega
      rw [if_pos h_branch]
      rw [unsize_singleton, RustM_ok_bind,
          extend_from_slice_singleton result x h_r_first_ok', RustM_ok_bind, pure_bind]
      simp only [RustM_ok_bind, unsize_singleton]
      simp only [extend_from_slice_singleton _ _
                  (by show (push_one result x h_r_first_ok').val.size + 1 < USize64.size
                      show (result.val ++ #[x]).size + 1 < USize64.size
                      rw [Array.size_append, h_r_sz_init, h_usize_size]
                      show i.toNat + 1 + 1 < 2 ^ 64; omega),
                 RustM_ok_bind, h_add_i, RustM_ok_bind]
      apply Triple.pure
      intro _
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show v.val.size - (i + 1).toNat < v.val.size - i.toNat
        rw [h_i1]; omega
      · rw [h_i1]; omega
      · show ((result.val ++ #[x]) ++ #[v.val[i.toNat]'hi_lt]).size = (i + 1).toNat + 1
        rw [Array.size_append, Array.size_append, h_r_sz_init, h_i1]; rfl
      · intro y
        show vec_count ((result.val ++ #[x]) ++ #[v.val[i.toNat]'hi_lt]) y
              ((result.val ++ #[x]) ++ #[v.val[i.toNat]'hi_lt]).size =
              vec_count v.val y (i + 1).toNat + (if (true : Bool) = true ∧ y = x then 1 else 0)
        rw [vec_count_append_singleton, vec_count_append_singleton]
        have h_count_app : vec_count result.val y result.val.size =
            vec_count v.val y i.toNat +
              (if (ins : Bool) = true ∧ y = x then 1 else 0) := h_count y
        rw [h_count_app, h_ins_false]
        have h_vc_succ : vec_count v.val y (i + 1).toNat =
            (if (v.val[i.toNat]'hi_lt) = y then 1 else 0) + vec_count v.val y i.toNat := by
          rw [h_i1]; exact vec_count_succ v.val y i.toNat hi_lt
        rw [h_vc_succ]
        simp only [Bool.false_eq_true, false_and, if_false, Nat.add_zero, true_and]
        by_cases h_xy : x = y
        · rw [if_pos h_xy, if_pos h_xy.symm]; omega
        · rw [if_neg h_xy, if_neg (Ne.symm h_xy)]; omega
      · show arr_sorted ((result.val ++ #[x]) ++ #[v.val[i.toNat]'hi_lt])
        apply arr_sorted_append_singleton
        · apply arr_sorted_append_singleton _ _ h_sorted
          intro k hk
          exact h_le_x h_ins_false k hk
        · intro k hk
          have h_sz1 : (result.val ++ #[x]).size = result.val.size + 1 := by
            rw [Array.size_append]; rfl
          by_cases hk_in : k < result.val.size
          · rw [Array.getElem_append_left hk_in]
            exact h_le_v k hk_in i.toNat (Nat.le_refl _) hi_lt
          · have hk_eq : k = result.val.size := by rw [h_sz1] at hk; omega
            subst hk_eq
            rw [Array.getElem_append_right (Nat.le_refl _)]
            simp only [Nat.sub_self]
            show x.toInt ≤ (v.val[i.toNat]'hi_lt).toInt
            exact h_x_le_vi_int
      · intro k hk m hm hmv
        change k < ((result.val ++ #[x]) ++ #[v.val[i.toNat]'hi_lt]).size at hk
        change (((result.val ++ #[x]) ++ #[v.val[i.toNat]'hi_lt])[k]'hk).toInt ≤ (v.val[m]'hmv).toInt
        have hm_ge : i.toNat + 1 ≤ m := by
          have hm' : (i + 1).toNat ≤ m := hm
          rw [h_i1] at hm'; exact hm'
        have h_sz1 : (result.val ++ #[x]).size = result.val.size + 1 := by
          rw [Array.size_append]; rfl
        by_cases hk_in1 : k < (result.val ++ #[x]).size
        · rw [Array.getElem_append_left hk_in1]
          by_cases hk_in : k < result.val.size
          · rw [Array.getElem_append_left hk_in]
            exact h_le_v k hk_in m (show i.toNat ≤ m from by omega) hmv
          · have hk_eq : k = result.val.size := by
              rw [h_sz1] at hk_in1
              omega
            subst hk_eq
            rw [Array.getElem_append_right (Nat.le_refl _)]
            simp only [Nat.sub_self]
            show x.toInt ≤ (v.val[m]'hmv).toInt
            have hv_sorted_im : (v.val[i.toNat]'hi_lt).toInt ≤ (v.val[m]'hmv).toInt :=
              h_v_sorted i.toNat m hi_lt hmv (by omega)
            exact Int.le_trans h_x_le_vi_int hv_sorted_im
        · have h_sz_outer : ((result.val ++ #[x]) ++ #[v.val[i.toNat]'hi_lt]).size
                              = result.val.size + 2 := by
            rw [Array.size_append, Array.size_append]; rfl
          have hk_eq : k = (result.val ++ #[x]).size := by
            rw [h_sz_outer] at hk
            rw [h_sz1] at hk_in1
            rw [h_sz1]
            omega
          subst hk_eq
          rw [Array.getElem_append_right (Nat.le_refl _)]
          simp only [Nat.sub_self]
          show (v.val[i.toNat]'hi_lt).toInt ≤ (v.val[m]'hmv).toInt
          exact h_v_sorted i.toNat m hi_lt hmv (by omega)
      · -- le_x: vacuous since new ins = true
        intro h
        exact (Bool.noConfusion h : False).elim
    · -- Skip-first-extend branch
      rw [if_neg h_branch]
      rw [pure_bind]
      simp only [RustM_ok_bind, unsize_singleton]
      simp only [extend_from_slice_singleton _ _ h_r_first_ok,
                 RustM_ok_bind, h_add_i, RustM_ok_bind]
      apply Triple.pure
      intro _
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show v.val.size - (i + 1).toNat < v.val.size - i.toNat
        rw [h_i1]; omega
      · rw [h_i1]; omega
      · show (result.val ++ #[v.val[i.toNat]'hi_lt]).size =
              (i + 1).toNat + (if ins then 1 else 0)
        rw [Array.size_append, h_r_sz, h_i1]
        show i.toNat + (if ins then 1 else 0) + 1 = (i.toNat + 1) + (if ins then 1 else 0)
        omega
      · intro y
        show vec_count (result.val ++ #[v.val[i.toNat]'hi_lt]) y
              (result.val ++ #[v.val[i.toNat]'hi_lt]).size =
              vec_count v.val y (i + 1).toNat + (if (ins : Bool) = true ∧ y = x then 1 else 0)
        rw [vec_count_append_singleton]
        have h_count_app : vec_count result.val y result.val.size =
            vec_count v.val y i.toNat +
              (if (ins : Bool) = true ∧ y = x then 1 else 0) := h_count y
        rw [h_count_app]
        have h_vc_succ : vec_count v.val y (i + 1).toNat =
            (if (v.val[i.toNat]'hi_lt) = y then 1 else 0) + vec_count v.val y i.toNat := by
          rw [h_i1]; exact vec_count_succ v.val y i.toNat hi_lt
        rw [h_vc_succ]
        omega
      · apply arr_sorted_append_singleton _ _ h_sorted
        intro k hk
        exact h_le_v k hk i.toNat (Nat.le_refl _) hi_lt
      · intro k hk m hm hmv
        change k < (result.val ++ #[v.val[i.toNat]'hi_lt]).size at hk
        change ((result.val ++ #[v.val[i.toNat]'hi_lt])[k]'hk).toInt ≤ (v.val[m]'hmv).toInt
        have hm_ge : i.toNat + 1 ≤ m := by
          have hm' : (i + 1).toNat ≤ m := hm
          rw [h_i1] at hm'; exact hm'
        have h_sz_eq : (result.val ++ #[v.val[i.toNat]'hi_lt]).size = result.val.size + 1 := by
          rw [Array.size_append]; rfl
        by_cases hk_in : k < result.val.size
        · rw [Array.getElem_append_left hk_in]
          exact h_le_v k hk_in m (show i.toNat ≤ m from by omega) hmv
        · have hk_eq : k = result.val.size := by
            rw [h_sz_eq] at hk; omega
          subst hk_eq
          rw [Array.getElem_append_right (Nat.le_refl _)]
          simp only [Nat.sub_self]
          show (v.val[i.toNat]'hi_lt).toInt ≤ (v.val[m]'hmv).toInt
          exact h_v_sorted i.toNat m hi_lt hmv (by omega)
      · intro h_ins_false
        change ins = false at h_ins_false
        have h_vi_lt_x_int : (v.val[i.toNat]'hi_lt).toInt < x.toInt := by
          have h_branch_false : ¬ (!ins && decide ((v.val[i.toNat]'hi_lt) ≥ x)) = true := h_branch
          rw [h_ins_false] at h_branch_false
          simp only [Bool.not_false, Bool.true_and] at h_branch_false
          have h_not_ge : ¬ (x ≤ (v.val[i.toNat]'hi_lt)) := by
            intro h_ge; exact h_branch_false (decide_eq_true_iff.mpr h_ge)
          rw [Int64.le_iff_toInt_le] at h_not_ge
          omega
        intro k hk
        change k < (result.val ++ #[v.val[i.toNat]'hi_lt]).size at hk
        change ((result.val ++ #[v.val[i.toNat]'hi_lt])[k]'hk).toInt ≤ x.toInt
        have h_sz_eq : (result.val ++ #[v.val[i.toNat]'hi_lt]).size = result.val.size + 1 := by
          rw [Array.size_append]; rfl
        by_cases hk_in : k < result.val.size
        · rw [Array.getElem_append_left hk_in]
          exact h_le_x h_ins_false k hk_in
        · have hk_eq : k = result.val.size := by
            rw [h_sz_eq] at hk; omega
          subst hk_eq
          rw [Array.getElem_append_right (Nat.le_refl _)]
          simp only [Nat.sub_self]
          show (v.val[i.toNat]'hi_lt).toInt ≤ x.toInt
          exact Int.le_of_lt h_vi_lt_x_int

private theorem is_loop_triple_all (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h_v_sz : v.val.size + 1 < USize64.size)
    (h_v_sorted : arr_sorted v.val) :
    ⦃⌜ isInvAll v x ⟨(0 : usize), false, ⟨([] : List i64).toArray, by grind⟩⟩ ⌝⦄
      isLoop v x
    ⦃⇓ r => ⌜ isInvAll v x r ∧ ¬ isCond v r = true ⌝⦄ := by
  apply Std.Do.Spec.MonoLoopCombinator.while_loop
    (rust_primitives.hax.Tuple3.mk (0 : usize) false
      ⟨([] : List i64).toArray, by grind⟩) Lean.Loop.mk
    (isCond v) (isBody v x) (isInvAll v x) (isTerm v)
  intro s hcond hinv
  have h := is_body_step_all v x h_v_sz h_v_sorted s hcond hinv
  exact h hinv

private theorem is_loop_total_all (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h_v_sz : v.val.size + 1 < USize64.size)
    (h_v_sorted : arr_sorted v.val) :
    ∃ r : Tuple3 usize Bool (alloc.vec.Vec i64 alloc.alloc.Global),
      isLoop v x = RustM.ok r ∧
      r._2.val.size = v.val.size + (if r._1 then 1 else 0) ∧
      arr_sorted r._2.val ∧
      (r._1 = false → ∀ k (hk : k < r._2.val.size), (r._2.val[k]'hk).toInt ≤ x.toInt) := by
  classical
  have h_init_inv : isInvAll v x ⟨(0 : usize), false, ⟨([] : List i64).toArray, by grind⟩⟩ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (0 : usize).toNat ≤ v.val.size; rw [usize_zero_toNat]; omega
    · show (([] : List i64).toArray).size = (0 : usize).toNat + (if false then 1 else 0)
      rw [usize_zero_toNat]; rfl
    · intro y
      show vec_count (([] : List i64).toArray) y (([] : List i64).toArray).size =
            vec_count v.val y (0 : usize).toNat + (if (false : Bool) = true ∧ y = x then 1 else 0)
      have h_sz : ([] : List i64).toArray.size = 0 := rfl
      rw [h_sz, usize_zero_toNat]
      show 0 = vec_count v.val y 0 + (if False ∧ y = x then 1 else 0)
      simp; rfl
    · exact arr_sorted_empty
    · intro k hk m hm hmv
      exfalso
      have : (([] : List i64).toArray).size = 0 := rfl
      rw [this] at hk; omega
    · intro _ k hk
      exfalso
      have : (([] : List i64).toArray).size = 0 := rfl
      rw [this] at hk; omega
  have h_loop := is_loop_triple_all v x h_v_sz h_v_sorted
  have h_loop_proj :
      ⦃⌜ True ⌝⦄
        isLoop v x
      ⦃⇓ r => ⌜ r._2.val.size = v.val.size + (if r._1 then 1 else 0) ∧
                arr_sorted r._2.val ∧
                (r._1 = false → ∀ k (hk : k < r._2.val.size), (r._2.val[k]'hk).toInt ≤ x.toInt) ⌝⦄ := by
    apply Triple.of_entails_left _ _ _ _ ?_
    · intro _; exact h_init_inv
    apply Triple.of_entails_right _ _ _ _ h_loop
    apply PostCond.entails.of_left_entails
    intro r ⟨hinv, hncond⟩
    obtain ⟨hi_le, h_r_sz, _h_count, h_sorted, _h_le_v, h_le_x⟩ := hinv
    have h_ofNat_v : (USize64.ofNat v.val.size).toNat = v.val.size :=
      USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
    have h_not_cond : ¬ decide (r._0.toNat < (USize64.ofNat v.val.size).toNat) = true := hncond
    have hi_ge : v.val.size ≤ r._0.toNat := by
      rw [h_ofNat_v, decide_eq_true_iff] at h_not_cond; omega
    have hi_eq : r._0.toNat = v.val.size := by omega
    refine ⟨?_, h_sorted, h_le_x⟩
    rw [h_r_sz, hi_eq]
  rw [RustM.Triple_iff_BitVec] at h_loop_proj
  simp only [decide_true, Bool.not_true, Bool.false_or,
             Bool.and_eq_true, decide_eq_true_eq] at h_loop_proj
  obtain ⟨hok, hpost⟩ := h_loop_proj
  cases hf : isLoop v x with
  | none => rw [hf] at hok; simp [RustM.toBVRustM] at hok
  | some result =>
    cases result with
    | ok r =>
      rw [hf] at hpost
      simp only [RustM.toBVRustM] at hpost
      exact ⟨r, rfl, hpost.1, hpost.2.1, hpost.2.2⟩
    | error e =>
      rw [hf] at hok
      cases e <;> simp [RustM.toBVRustM] at hok

private theorem insert_sorted_sorted_spec (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h_v_sz : v.val.size + 1 < USize64.size)
    (h_v_sorted : arr_sorted v.val) :
    ∃ r : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_032_sort_third.insert_sorted v x = RustM.ok r ∧
      r.val.size = v.val.size + 1 ∧
      arr_sorted r.val := by
  obtain ⟨s, h_loop_eq, h_s_sz, h_s_sorted, h_s_le_x⟩ := is_loop_total_all v x h_v_sz h_v_sorted
  unfold clever_032_sort_third.insert_sorted
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨([] : List i64).toArray, by grind⟩ := rfl
  have h_len : (alloc.vec.Impl_1.len i64 alloc.alloc.Global v :
                  RustM usize) = RustM.ok (USize64.ofNat v.val.size) := rfl
  rw [h_new]
  simp only [RustM_ok_bind]
  rw [h_len]
  simp only [RustM_ok_bind]
  unfold rust_primitives.hax.while_loop
  rw [show
    Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk
      (fun b => decide (USize64.toNat b._0 < (USize64.ofNat v.val.size).toNat))
      (rust_primitives.hax.Tuple3.mk (0 : usize) false
        ⟨([] : List i64).toArray, by grind⟩)
      (isBody v x) = isLoop v x from rfl]
  rw [h_loop_eq]
  simp only [RustM_ok_bind]
  have h_not_s1 : (!? s._1 : RustM Bool) = pure (!s._1) := rfl
  rw [h_not_s1, pure_bind]
  by_cases h_ins : s._1 = true
  · rw [h_ins]
    simp only [Bool.not_true, Bool.false_eq_true, if_false]
    refine ⟨s._2, rfl, ?_, h_s_sorted⟩
    rw [h_s_sz, h_ins]; simp
  · have h_ins_false : s._1 = false := by
      cases hs : s._1
      · rfl
      · exfalso; apply h_ins; exact hs
    rw [h_ins_false]
    simp only [Bool.not_false, if_true]
    have h_s2_sz : s._2.val.size = v.val.size := by
      rw [h_s_sz, h_ins_false]; simp
    have h_s2_ok : s._2.val.size + 1 < USize64.size := by
      rw [h_s2_sz]; exact h_v_sz
    rw [show (rust_primitives.unsize ({ toVec := #v[x] } : RustArray i64 1) :
              RustM (rust_primitives.sequence.Seq i64))
              = RustM.ok ⟨#[x], one_lt_usize_size⟩ from rfl]
    simp only [RustM_ok_bind]
    rw [show (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global s._2
                ⟨#[x], one_lt_usize_size⟩ :
                RustM (alloc.vec.Vec i64 alloc.alloc.Global))
              = RustM.ok (push_one s._2 x h_s2_ok) from by
      unfold alloc.vec.Impl_2.extend_from_slice
      rw [dif_pos (show s._2.val.size + (#[x] : Array i64).size < USize64.size from h_s2_ok)]
      rfl]
    simp only [RustM_ok_bind]
    refine ⟨push_one s._2 x h_s2_ok, rfl, ?_, ?_⟩
    · show (s._2.val ++ #[x]).size = v.val.size + 1
      rw [Array.size_append, h_s2_sz]; rfl
    · show arr_sorted (s._2.val ++ #[x])
      apply arr_sorted_append_singleton _ _ h_s_sorted
      intro k hk
      exact h_s_le_x h_ins_false k hk

private theorem collect_thirds_sorted (l : RustSlice i64) :
    ∀ (m : Nat) (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global),
      l.val.size - i.toNat ≤ m →
      i.toNat ≤ l.val.size →
      acc.val.size = thirdIdxCount i.toNat →
      arr_sorted acc.val →
      ∃ sorted : alloc.vec.Vec i64 alloc.alloc.Global,
        clever_032_sort_third.collect_thirds l i acc = RustM.ok sorted ∧
        sorted.val.size = thirdIdxCount l.val.size ∧
        arr_sorted sorted.val := by
  intro m
  induction m with
  | zero =>
    intro i acc hm hi_le hacc_sz hacc_sorted
    have hi_eq : i.toNat = l.val.size := by omega
    have hi_ge : l.val.size ≤ i.toNat := by omega
    refine ⟨acc, collect_thirds_oob l i acc hi_ge, ?_, hacc_sorted⟩
    rw [hacc_sz, hi_eq]
  | succ m ih =>
    intro i acc hm hi_le hacc_sz hacc_sorted
    by_cases hi_ge : l.val.size ≤ i.toNat
    · have hi_eq : i.toNat = l.val.size := by omega
      refine ⟨acc, collect_thirds_oob l i acc hi_ge, ?_, hacc_sorted⟩
      rw [hacc_sz, hi_eq]
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2 ^ 64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_meas : l.val.size - (i + 1).toNat ≤ m := by rw [h_i1]; omega
      by_cases hmod : i.toNat % 3 = 0
      · have hacc_le : acc.val.size ≤ i.toNat := by
          rw [hacc_sz]; exact thirdIdxCount_le_self i.toNat
        have hacc_ok : acc.val.size + 1 < USize64.size := by
          rw [h_usize_size]; omega
        obtain ⟨acc', h_ins, h_acc'_sz, h_acc'_sorted⟩ :=
          insert_sorted_sorted_spec acc (l.val[i.toNat]'hi_lt) hacc_ok hacc_sorted
        have h_step := collect_thirds_step_third l i acc hi_lt hmod acc' h_ins
        rw [h_step]
        have h_acc'_sz_new : acc'.val.size = thirdIdxCount (i + 1).toNat := by
          rw [h_acc'_sz, hacc_sz, h_i1]
          show thirdIdxCount i.toNat + 1 =
                if i.toNat % 3 = 0 then thirdIdxCount i.toNat + 1 else thirdIdxCount i.toNat
          rw [if_pos hmod]
        exact ih (i + 1) acc' h_meas h_i1_le h_acc'_sz_new h_acc'_sorted
      · rw [collect_thirds_step_other l i acc hi_lt hmod]
        have h_acc'_sz_new : acc.val.size = thirdIdxCount (i + 1).toNat := by
          rw [hacc_sz, h_i1]
          show thirdIdxCount i.toNat =
                if i.toNat % 3 = 0 then thirdIdxCount i.toNat + 1 else thirdIdxCount i.toNat
          rw [if_neg hmod]
        exact ih (i + 1) acc h_meas h_i1_le h_acc'_sz_new hacc_sorted

private theorem thirdIdxCount_strict_lt (i j : Nat)
    (hi : i % 3 = 0) (hj : j % 3 = 0) (hlt : i < j) :
    thirdIdxCount i < thirdIdxCount j := by
  have h_j_ge : j ≥ i + 3 := by omega
  have h1 : thirdIdxCount (i + 1) = thirdIdxCount i + 1 := by
    show (if i % 3 = 0 then thirdIdxCount i + 1 else thirdIdxCount i) = _
    rw [if_pos hi]
  have h2 : thirdIdxCount (i + 2) = thirdIdxCount (i + 1) := by
    show (if (i + 1) % 3 = 0 then thirdIdxCount (i + 1) + 1 else thirdIdxCount (i + 1)) = _
    have hi1 : (i + 1) % 3 ≠ 0 := by omega
    rw [if_neg hi1]
  have h3 : thirdIdxCount (i + 3) = thirdIdxCount (i + 2) := by
    show (if (i + 2) % 3 = 0 then thirdIdxCount (i + 2) + 1 else thirdIdxCount (i + 2)) = _
    have hi2 : (i + 2) % 3 ≠ 0 := by omega
    rw [if_neg hi2]
  have h_i3 : thirdIdxCount (i + 3) = thirdIdxCount i + 1 := by
    rw [h3, h2, h1]
  calc thirdIdxCount i < thirdIdxCount i + 1 := Nat.lt_succ_self _
    _ = thirdIdxCount (i + 3) := h_i3.symm
    _ ≤ thirdIdxCount j := thirdIdxCount_mono _ _ h_j_ge

/-- Values at indices divisible by 3 are in ascending order in the
    output. Captures the proptest `third_indices_sorted`. -/
theorem third_indices_sorted
    (l : RustSlice i64) (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_032_sort_third.sort_third l = RustM.ok v)
    (i j : Nat) (hi_v : i < v.val.size) (hj_v : j < v.val.size)
    (hi_mod : i % 3 = 0) (hj_mod : j % 3 = 0) (hlt : i < j) :
    (v.val[i]'hi_v).toInt ≤ (v.val[j]'hj_v).toInt := by
  let acc0 : alloc.vec.Vec i64 alloc.alloc.Global := ⟨([] : List i64).toArray, by grind⟩
  have h_acc0_sz : acc0.val.size = thirdIdxCount (0 : usize).toNat := by
    show (([] : List i64).toArray).size = thirdIdxCount 0; rfl
  have h_acc0_sorted : arr_sorted acc0.val := arr_sorted_empty
  have h_zero_le : (0 : usize).toNat ≤ l.val.size := by rw [usize_zero_toNat]; omega
  have h_meas : l.val.size - (0 : usize).toNat ≤ l.val.size := by rw [usize_zero_toNat]; omega
  obtain ⟨sorted, h_ct, h_sorted_sz, h_sorted_sorted⟩ :=
    collect_thirds_sorted l l.val.size (0 : usize) acc0 h_meas h_zero_le h_acc0_sz h_acc0_sorted
  have h_sorted_sz_le : thirdIdxCount l.val.size ≤ sorted.val.size := by rw [h_sorted_sz]; omega
  let acc1 : alloc.vec.Vec i64 alloc.alloc.Global := ⟨([] : List i64).toArray, by grind⟩
  have h_acc1_sz : acc1.val.size = (0 : usize).toNat := by
    show (([] : List i64).toArray).size = 0; rfl
  have h_j_eq : (0 : usize).toNat = thirdIdxCount (0 : usize).toNat := by
    rw [usize_zero_toNat]; rfl
  have h_acc1_inv :
      ∀ (k : Nat) (hk : k < acc1.val.size),
        if k % 3 = 0 then
          ∃ (hj : thirdIdxCount k < sorted.val.size),
            acc1.val[k]'hk = sorted.val[thirdIdxCount k]'hj
        else
          ∃ (hl : k < l.val.size), acc1.val[k]'hk = l.val[k]'hl := by
    intro k hk
    exfalso
    have : acc1.val.size = 0 := rfl
    rw [this] at hk; omega
  obtain ⟨v', h_rb', _h_v'_sz, h_v'_inv⟩ :=
    rebuild_at_correct l sorted h_sorted_sz_le l.val.size (0 : usize) (0 : usize) acc1
      h_meas h_zero_le h_j_eq h_acc1_sz h_acc1_inv
  obtain ⟨sorted2, h_ct2, h_rb⟩ := sort_third_split l v hres
  have h_sorted_eq : sorted2 = sorted := by
    have h_eq : (RustM.ok sorted2 : RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok sorted := by rw [← h_ct2, h_ct]
    injection h_eq with h_eq1
    injection h_eq1
  subst h_sorted_eq
  have h_v_eq : v = v' := by
    have h_inj : (RustM.ok v : RustM (alloc.vec.Vec i64 alloc.alloc.Global)) = RustM.ok v' := by
      rw [← h_rb, h_rb']
    injection h_inj with h_eq1
    injection h_eq1
  subst h_v_eq
  have h_inv_i := h_v'_inv i hi_v
  rw [if_pos hi_mod] at h_inv_i
  obtain ⟨h_tic_i, h_eq_i⟩ := h_inv_i
  have h_inv_j := h_v'_inv j hj_v
  rw [if_pos hj_mod] at h_inv_j
  obtain ⟨h_tic_j, h_eq_j⟩ := h_inv_j
  have h_tic_lt : thirdIdxCount i < thirdIdxCount j :=
    thirdIdxCount_strict_lt i j hi_mod hj_mod hlt
  rw [h_eq_i, h_eq_j]
  exact h_sorted_sorted (thirdIdxCount i) (thirdIdxCount j) h_tic_i h_tic_j (Nat.le_of_lt h_tic_lt)

/-- Bridge: count of `y` at third-divisible indices of `v` equals
    count of `y` in `sorted`, given that `v[k] = sorted[thirdIdxCount k]`
    for each `k % 3 = 0`. -/
private theorem third_to_vec_count_bridge
    (v sorted : Array i64) (y : i64)
    (h_third_eq : ∀ k (hk : k < v.size), k % 3 = 0 →
      ∃ (hj : thirdIdxCount k < sorted.size), v[k]'hk = sorted[thirdIdxCount k]'hj) :
    ∀ K, K ≤ v.size →
      third_count v y K = vec_count sorted y (thirdIdxCount K) := by
  intro K hK
  induction K with
  | zero => rfl
  | succ K ih =>
    have hK_lt : K < v.size := by omega
    have hK_le : K ≤ v.size := by omega
    have h_unfold_tc :
        third_count v y (K + 1) =
          (if hh : K < v.size then
            (if K % 3 = 0 ∧ (v[K]'hh) = y then 1 else 0) + third_count v y K
          else third_count v y K) := rfl
    rw [h_unfold_tc, dif_pos hK_lt]
    by_cases hmod : K % 3 = 0
    · obtain ⟨hj, h_eq⟩ := h_third_eq K hK_lt hmod
      have h_tic_succ : thirdIdxCount (K + 1) = thirdIdxCount K + 1 := by
        show (if K % 3 = 0 then thirdIdxCount K + 1 else thirdIdxCount K) = thirdIdxCount K + 1
        rw [if_pos hmod]
      rw [h_tic_succ]
      have h_vc_succ : vec_count sorted y (thirdIdxCount K + 1) =
          (if (sorted[thirdIdxCount K]'hj) = y then 1 else 0) + vec_count sorted y (thirdIdxCount K) :=
        vec_count_succ sorted y (thirdIdxCount K) hj
      rw [h_vc_succ, ih hK_le]
      have h_vk_eq_sorted : (v[K]'hK_lt) = (sorted[thirdIdxCount K]'hj) := h_eq
      by_cases h_y : (v[K]'hK_lt) = y
      · have h1 : (if K % 3 = 0 ∧ (v[K]'hK_lt) = y then (1 : Nat) else 0) = 1 :=
          if_pos ⟨hmod, h_y⟩
        have h2 : (if (sorted[thirdIdxCount K]'hj) = y then (1 : Nat) else 0) = 1 := by
          apply if_pos; rw [← h_vk_eq_sorted]; exact h_y
        rw [h1, h2]
      · have h1 : (if K % 3 = 0 ∧ (v[K]'hK_lt) = y then (1 : Nat) else 0) = 0 := by
          apply if_neg; intro ⟨_, h⟩; exact h_y h
        have h2 : (if (sorted[thirdIdxCount K]'hj) = y then (1 : Nat) else 0) = 0 := by
          apply if_neg; intro h; apply h_y; rw [h_vk_eq_sorted]; exact h
        rw [h1, h2]
    · have h_tic_succ : thirdIdxCount (K + 1) = thirdIdxCount K := by
        show (if K % 3 = 0 then thirdIdxCount K + 1 else thirdIdxCount K) = thirdIdxCount K
        rw [if_neg hmod]
      rw [h_tic_succ]
      have h_not : ¬ (K % 3 = 0 ∧ (v[K]'hK_lt) = y) := by
        intro ⟨h, _⟩; exact hmod h
      rw [if_neg h_not, ih hK_le]; omega

theorem third_indices_are_permutation
    (l : RustSlice i64) (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_032_sort_third.sort_third l = RustM.ok v)
    (x : i64) :
    third_count v.val x v.val.size = third_count l.val x l.val.size := by
  let acc0 : alloc.vec.Vec i64 alloc.alloc.Global := ⟨([] : List i64).toArray, by grind⟩
  have h_acc0_sz : acc0.val.size = thirdIdxCount (0 : usize).toNat := by
    show (([] : List i64).toArray).size = thirdIdxCount 0; rfl
  have h_zero_le : (0 : usize).toNat ≤ l.val.size := by rw [usize_zero_toNat]; omega
  have h_meas : l.val.size - (0 : usize).toNat ≤ l.val.size := by rw [usize_zero_toNat]; omega
  obtain ⟨sorted, h_ct, h_sorted_sz, h_sorted_count⟩ :=
    collect_thirds_spec l l.val.size (0 : usize) acc0 h_meas h_zero_le h_acc0_sz
  have h_sorted_sz_le : thirdIdxCount l.val.size ≤ sorted.val.size := by rw [h_sorted_sz]; omega
  let acc1 : alloc.vec.Vec i64 alloc.alloc.Global := ⟨([] : List i64).toArray, by grind⟩
  have h_acc1_sz : acc1.val.size = (0 : usize).toNat := by
    show (([] : List i64).toArray).size = 0; rfl
  have h_j_eq : (0 : usize).toNat = thirdIdxCount (0 : usize).toNat := by
    rw [usize_zero_toNat]; rfl
  have h_acc1_inv :
      ∀ (k : Nat) (hk : k < acc1.val.size),
        if k % 3 = 0 then
          ∃ (hj : thirdIdxCount k < sorted.val.size),
            acc1.val[k]'hk = sorted.val[thirdIdxCount k]'hj
        else
          ∃ (hl : k < l.val.size), acc1.val[k]'hk = l.val[k]'hl := by
    intro k hk
    exfalso
    have : acc1.val.size = 0 := rfl
    rw [this] at hk; omega
  obtain ⟨v', h_rb', h_v'_sz, h_v'_inv⟩ :=
    rebuild_at_correct l sorted h_sorted_sz_le l.val.size (0 : usize) (0 : usize) acc1
      h_meas h_zero_le h_j_eq h_acc1_sz h_acc1_inv
  have h_sort_third : clever_032_sort_third.sort_third l = RustM.ok v' := by
    rw [sort_third_unfold]
    show clever_032_sort_third.collect_thirds l (0 : usize) acc0 >>= _ = RustM.ok v'
    rw [h_ct]; simp only [RustM_ok_bind]; exact h_rb'
  have h_v_eq : v = v' := by
    have h_inj : RustM.ok v = (RustM.ok v' : RustM (alloc.vec.Vec i64 alloc.alloc.Global)) := by
      rw [← hres, h_sort_third]
    injection h_inj with h_eq
    injection h_eq
  rw [h_v_eq]
  have h_third_eq :
      ∀ (k : Nat) (hk : k < v'.val.size), k % 3 = 0 →
        ∃ (hj : thirdIdxCount k < sorted.val.size),
          v'.val[k]'hk = sorted.val[thirdIdxCount k]'hj := by
    intro k hk hmod
    have h := h_v'_inv k hk
    rw [if_pos hmod] at h
    exact h
  have h_bridge :=
    third_to_vec_count_bridge v'.val sorted.val x h_third_eq v'.val.size (Nat.le_refl _)
  rw [h_bridge]
  rw [h_v'_sz]
  rw [show thirdIdxCount l.val.size = sorted.val.size from h_sorted_sz.symm]
  have h_sc := h_sorted_count x
  rw [h_sc]
  have h_acc0_zero : vec_count acc0.val x acc0.val.size = 0 := by
    show vec_count (([] : List i64).toArray) x 0 = 0; rfl
  rw [h_acc0_zero]
  rw [Nat.zero_add]
  rw [usize_zero_toNat]
  exact third_count_range_eq_third_count l.val x l.val.size

end Clever_032_sort_thirdObligations
