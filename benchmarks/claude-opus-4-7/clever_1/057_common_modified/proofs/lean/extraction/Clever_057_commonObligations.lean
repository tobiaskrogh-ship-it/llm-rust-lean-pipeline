-- Companion obligations file for the `clever_057_common` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_057_common

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_057_commonObligations

/-! ## Standard scaffolding (transferred from `contains_u64`,
     `clever_009_rolling_max`, `clever_025_remove_duplicates`). -/

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

/-! ## Push helper for `Vec` (`extend_from_slice` of a 1-element chunk). -/

private def push_one (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec i64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

@[simp]
private theorem push_one_size
    (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h : acc.val.size + 1 < USize64.size) :
    (push_one acc x h).val.size = acc.val.size + 1 := by
  show (acc.val ++ #[x]).size = acc.val.size + 1
  simp

private theorem push_one_val
    (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h : acc.val.size + 1 < USize64.size) :
    (push_one acc x h).val = acc.val ++ #[x] := rfl

/-! ## Step lemmas for `contains_at`. Same shape as in `contains_u64`. -/

/-- Out-of-bounds step: when `i.toNat ≥ l.val.size`, returns `false`. -/
private theorem contains_at_oob (l : RustSlice i64) (x : i64) (i : usize)
    (hi : l.val.size ≤ i.toNat) :
    clever_057_common.contains_at l x i = RustM.ok false := by
  conv => lhs; unfold clever_057_common.contains_at
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

/-- Found step: when `i.toNat < l.val.size` and `l[i] = x`, returns `true`. -/
private theorem contains_at_found (l : RustSlice i64) (x : i64) (i : usize)
    (hi : i.toNat < l.val.size) (h : l.val[i.toNat]'hi = x) :
    clever_057_common.contains_at l x i = RustM.ok true := by
  conv => lhs; unfold clever_057_common.contains_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
  have h_beq_true : (l.val[i.toNat]'hi == x) = true := by
    rw [beq_iff_eq]; exact h
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.cmp.eq, h_beq_true]
  rfl

/-- Recursion step: when `i.toNat < l.val.size` and `l[i] ≠ x`, recurses with `i+1`. -/
private theorem contains_at_recurse (l : RustSlice i64) (x : i64) (i : usize)
    (hi : i.toNat < l.val.size) (h : l.val[i.toNat]'hi ≠ x) :
    clever_057_common.contains_at l x i = clever_057_common.contains_at l x (i + 1) := by
  conv => lhs; unfold clever_057_common.contains_at
  have h_size : l.val.size < 2^64 := l.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
  have h_beq_false : (l.val[i.toNat]'hi == x) = false := by
    rw [beq_eq_false_iff_ne]; exact h
  have h_no_overflow : i.toNat + 1 < 2^64 := by omega
  have h_no_bv : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false :=
    usize_add_one_no_bv i h_no_overflow
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.cmp.eq, h_beq_false,
             rust_primitives.ops.arith.Add.add, h_no_bv]

/-! ## Totality of `contains_at`.

`contains_at l x i` always returns `RustM.ok b`, and `b = true` iff
some witness index `j` in `[i.toNat, l.val.size)` has `l[j] = x`.
Proved by strong induction on the measure `l.val.size - i.toNat`. -/

private theorem contains_at_total (l : RustSlice i64) (x : i64) (i : usize) :
    ∃ b : Bool, clever_057_common.contains_at l x i = RustM.ok b ∧
      (b = true ↔
        ∃ j : Nat, i.toNat ≤ j ∧ ∃ (hj : j < l.val.size), l.val[j]'hj = x) := by
  induction hk : (l.val.size - i.toNat) using Nat.strongRecOn generalizing i with
  | _ k ih =>
    by_cases hbound : l.val.size ≤ i.toNat
    · refine ⟨false, contains_at_oob l x i hbound, ?_⟩
      constructor
      · intro h; exact absurd h Bool.false_ne_true
      · rintro ⟨j, hij, hjsize, hjeq⟩
        omega
    · have hbound' : i.toNat < l.val.size := Nat.lt_of_not_le hbound
      by_cases hit : l.val[i.toNat]'hbound' = x
      · refine ⟨true, contains_at_found l x i hbound' hit, ?_⟩
        constructor
        · intro _
          exact ⟨i.toNat, Nat.le_refl _, hbound', hit⟩
        · intro _; rfl
      · have h_size : l.val.size < 2^64 := l.size_lt_usizeSize
        have h_no_overflow : i.toNat + 1 < 2^64 := by omega
        have h_i1_toNat : (i + 1).toNat = i.toNat + 1 :=
          usize_add_one_toNat i h_no_overflow
        have h_measure_lt : l.val.size - (i + 1).toNat < k := by
          rw [h_i1_toNat]; omega
        obtain ⟨b, h_eq, h_iff⟩ := ih (l.val.size - (i + 1).toNat) h_measure_lt (i + 1) rfl
        refine ⟨b, ?_, ?_⟩
        · rw [contains_at_recurse l x i hbound' hit]; exact h_eq
        · constructor
          · intro hb_true
            obtain ⟨j, hij, hjsize, hjeq⟩ := h_iff.mp hb_true
            rw [h_i1_toNat] at hij
            exact ⟨j, by omega, hjsize, hjeq⟩
          · rintro ⟨j, hij, hjsize, hjeq⟩
            apply h_iff.mpr
            rw [h_i1_toNat]
            rcases Nat.lt_or_ge i.toNat j with hlt | hge
            · exact ⟨j, by omega, hjsize, hjeq⟩
            · have hj_eq_i : j = i.toNat := by omega
              exfalso
              apply hit
              rw [← hjeq]
              congr 1
              exact hj_eq_i.symm

/-- Membership predicate over a slice. -/
private def mem_slice (l : RustSlice i64) (x : i64) : Prop :=
  ∃ j : Nat, ∃ (hj : j < l.val.size), l.val[j]'hj = x

/-- `contains_at l x 0 = RustM.ok (decideable membership)`. -/
private theorem contains_at_zero_total (l : RustSlice i64) (x : i64) :
    ∃ b : Bool, clever_057_common.contains_at l x (0 : usize) = RustM.ok b ∧
      (b = true ↔ mem_slice l x) := by
  obtain ⟨b, h_eq, h_iff⟩ := contains_at_total l x (0 : usize)
  refine ⟨b, h_eq, ?_⟩
  constructor
  · intro hb
    obtain ⟨j, _, hjsize, hjeq⟩ := h_iff.mp hb
    exact ⟨j, hjsize, hjeq⟩
  · rintro ⟨j, hjsize, hjeq⟩
    apply h_iff.mpr
    refine ⟨j, ?_, hjsize, hjeq⟩
    rw [usize_zero_toNat]; omega

/-- Decidable form: there exists a Bool `b` such that `contains_at l x 0 = ok b` and
    `b = true ↔ mem_slice l x`. Stated existentially. -/
private theorem contains_at_zero_iff_mem (l : RustSlice i64) (x : i64) :
    clever_057_common.contains_at l x (0 : usize) = RustM.ok true ↔ mem_slice l x := by
  obtain ⟨b, h_eq, h_iff⟩ := contains_at_zero_total l x
  constructor
  · intro h
    rw [h_eq] at h
    injection h with h_eq2
    injection h_eq2 with h_eq3
    exact h_iff.mp h_eq3
  · intro h
    rw [h_eq, h_iff.mpr h]

private theorem contains_at_zero_iff_not_mem (l : RustSlice i64) (x : i64) :
    clever_057_common.contains_at l x (0 : usize) = RustM.ok false ↔ ¬ mem_slice l x := by
  obtain ⟨b, h_eq, h_iff⟩ := contains_at_zero_total l x
  constructor
  · intro h hmem
    have hb_true : b = true := h_iff.mpr hmem
    rw [h_eq, hb_true] at h
    injection h with h_eq2
    injection h_eq2 with h_eq3
    exact Bool.noConfusion h_eq3
  · intro h
    cases hb : b with
    | true =>
      exfalso
      apply h
      apply h_iff.mp
      exact hb
    | false =>
      rw [h_eq, hb]

/-! ## Step lemmas for `build_common_at`.

Three branches:
1. Out-of-bounds: i.toNat ≥ l1.val.size → returns acc.
2. In-bounds, x = l1[i], l1[i] ∈ l2 and l1[i] ∉ acc → push l1[i] and recurse.
3. In-bounds, l1[i] ∉ l2 or l1[i] ∈ acc → recurse without pushing. -/

/-- Out-of-bounds step. -/
private theorem build_common_at_oob (l1 l2 : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : l1.val.size ≤ i.toNat) :
    clever_057_common.build_common_at l1 l2 i acc = RustM.ok acc := by
  conv => lhs; unfold clever_057_common.build_common_at
  have h_ofNat : (USize64.ofNat l1.val.size).toNat = l1.val.size :=
    USize64.toNat_ofNat_of_lt' l1.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l1.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- Push step: in-bounds, l1[i] ∈ l2, l1[i] ∉ acc → extend acc and recurse. -/
private theorem build_common_at_step_push (l1 l2 : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < l1.val.size)
    (h_in_l2 : clever_057_common.contains_at l2 (l1.val[i.toNat]'hi) (0 : usize)
                = RustM.ok true)
    (h_not_in_acc :
      clever_057_common.contains_at acc (l1.val[i.toNat]'hi) (0 : usize)
        = RustM.ok false)
    (h_acc_size : acc.val.size + 1 < USize64.size) :
    clever_057_common.build_common_at l1 l2 i acc =
      clever_057_common.build_common_at l1 l2 (i + 1)
        (push_one acc (l1.val[i.toNat]'hi) h_acc_size) := by
  conv => lhs; unfold clever_057_common.build_common_at
  have h_size_lt : l1.val.size < USize64.size := l1.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat l1.val.size).toNat = l1.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l1.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (l1[i]_? : RustM i64) = RustM.ok (l1.val[i.toNat]'hi) := by
    show (if h : i.toNat < l1.val.size then pure (l1.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (l1.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_deref :
      (core_models.ops.deref.Deref.deref (alloc.vec.Vec i64 alloc.alloc.Global) acc
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global)) = RustM.ok acc := rfl
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
  have h_and_eq :
      (rust_primitives.hax.logical_op.and true true : RustM Bool) = RustM.ok true := rfl
  have h_not_eq :
      (rust_primitives.hax.logical_op.not false : RustM Bool) = RustM.ok true := rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_deref, h_in_l2, h_not_in_acc, h_not_eq, h_and_eq]
  rw [show (rust_primitives.unsize
            (RustArray.ofVec #v[l1.val[i.toNat]'hi] : RustArray i64 1)
            : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[l1.val[i.toNat]'hi], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size :
      acc.val.size + (#[l1.val[i.toNat]'hi] : Array i64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size
    exact h_acc_size
  rw [show (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
              ⟨#[l1.val[i.toNat]'hi], one_lt_usize_size⟩
            : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
        = RustM.ok (push_one acc (l1.val[i.toNat]'hi) h_acc_size) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  simp only [RustM_ok_bind]
  rw [h_add_i]
  rfl

/-- Skip step (not in l2): in-bounds, l1[i] ∉ l2 → recurse without pushing. -/
private theorem build_common_at_step_skip_l2 (l1 l2 : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < l1.val.size)
    (h_in_l2 : clever_057_common.contains_at l2 (l1.val[i.toNat]'hi) (0 : usize)
                = RustM.ok false)
    (b_acc : Bool)
    (h_acc :
      clever_057_common.contains_at acc (l1.val[i.toNat]'hi) (0 : usize)
        = RustM.ok b_acc) :
    clever_057_common.build_common_at l1 l2 i acc =
      clever_057_common.build_common_at l1 l2 (i + 1) acc := by
  conv => lhs; unfold clever_057_common.build_common_at
  have h_size_lt : l1.val.size < USize64.size := l1.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat l1.val.size).toNat = l1.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l1.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (l1[i]_? : RustM i64) = RustM.ok (l1.val[i.toNat]'hi) := by
    show (if h : i.toNat < l1.val.size then pure (l1.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (l1.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_deref :
      (core_models.ops.deref.Deref.deref (alloc.vec.Vec i64 alloc.alloc.Global) acc
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global)) = RustM.ok acc := rfl
  have h_no_ov_i : i.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_size_lt; omega
  have h_no_bv_i :
      BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false :=
    usize_add_one_no_bv i h_no_ov_i
  have h_and_eq_false :
      (rust_primitives.hax.logical_op.and false (! b_acc) : RustM Bool)
        = RustM.ok false := by
    show pure (false && (! b_acc)) = RustM.ok false
    cases b_acc <;> rfl
  have h_not_eq :
      (rust_primitives.hax.logical_op.not b_acc : RustM Bool)
        = RustM.ok (! b_acc) := rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_deref, h_in_l2, h_acc, h_not_eq, h_and_eq_false,
             rust_primitives.ops.arith.Add.add, h_no_bv_i]

/-- Skip step (already in acc): in-bounds, l1[i] ∈ l2 but l1[i] ∈ acc → recurse without pushing. -/
private theorem build_common_at_step_skip_acc (l1 l2 : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < l1.val.size)
    (h_in_l2 : clever_057_common.contains_at l2 (l1.val[i.toNat]'hi) (0 : usize)
                = RustM.ok true)
    (h_in_acc :
      clever_057_common.contains_at acc (l1.val[i.toNat]'hi) (0 : usize)
        = RustM.ok true) :
    clever_057_common.build_common_at l1 l2 i acc =
      clever_057_common.build_common_at l1 l2 (i + 1) acc := by
  conv => lhs; unfold clever_057_common.build_common_at
  have h_size_lt : l1.val.size < USize64.size := l1.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat l1.val.size).toNat = l1.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l1.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (l1[i]_? : RustM i64) = RustM.ok (l1.val[i.toNat]'hi) := by
    show (if h : i.toNat < l1.val.size then pure (l1.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (l1.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_deref :
      (core_models.ops.deref.Deref.deref (alloc.vec.Vec i64 alloc.alloc.Global) acc
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global)) = RustM.ok acc := rfl
  have h_no_ov_i : i.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_size_lt; omega
  have h_no_bv_i :
      BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false :=
    usize_add_one_no_bv i h_no_ov_i
  have h_and_eq :
      (rust_primitives.hax.logical_op.and true false : RustM Bool)
        = RustM.ok false := rfl
  have h_not_eq :
      (rust_primitives.hax.logical_op.not true : RustM Bool)
        = RustM.ok false := rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_deref, h_in_l2, h_in_acc, h_not_eq, h_and_eq,
             rust_primitives.ops.arith.Add.add, h_no_bv_i]

/-! ## Invariant bundle for `build_common_at`.

At any state `(i, acc)` along the recursion, four invariants are
preserved into `v`:
  (A) every acc element comes from l1 — soundness w.r.t. l1.
  (B) every acc element is in l2 — soundness w.r.t. l2.
  (C) every distinct l1[j], j < i, that is in l2, is in acc — completeness.
  (D) no duplicates in acc.

The recursive step preserves all four:
  - If we push l1[i] (which is in l2 and not in acc):
    (A) acc' acquires l1[i]; (B) acc' acquires an l2 element; (C) extends to j=i;
    (D) the new element is not in old acc.
  - If we skip (l1[i] not in l2, or already in acc): all invariants extend
    trivially (for C, when l1[i] not in l2 there's nothing to add; when
    l1[i] is already in acc, the witness is already there). -/

private theorem build_common_at_correct (l1 l2 : RustSlice i64) :
    ∀ (n : Nat) (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (v : alloc.vec.Vec i64 alloc.alloc.Global),
      l1.val.size - i.toNat ≤ n →
      i.toNat ≤ l1.val.size →
      -- (A) every acc[k] comes from l1
      (∀ (k : Nat) (hk : k < acc.val.size),
          ∃ p : Nat, ∃ (hp : p < l1.val.size), l1.val[p]'hp = acc.val[k]'hk) →
      -- (B) every acc[k] is in l2
      (∀ (k : Nat) (hk : k < acc.val.size),
          ∃ q : Nat, ∃ (hq : q < l2.val.size), l2.val[q]'hq = acc.val[k]'hk) →
      -- (C) every l1[j] with j < i, l1[j] ∈ l2 is in acc
      (∀ (j : Nat) (hj : j < l1.val.size), j < i.toNat →
          mem_slice l2 (l1.val[j]'hj) → mem_slice acc (l1.val[j]'hj)) →
      -- (D) no duplicates in acc
      (∀ (k₁ k₂ : Nat) (hk₁ : k₁ < acc.val.size) (hk₂ : k₂ < acc.val.size),
          acc.val[k₁]'hk₁ = acc.val[k₂]'hk₂ → k₁ = k₂) →
      -- (E) acc.val.size ≤ i.toNat (structural bound)
      acc.val.size ≤ i.toNat →
      clever_057_common.build_common_at l1 l2 i acc = RustM.ok v →
      (∀ (k : Nat) (hk : k < v.val.size),
          ∃ p : Nat, ∃ (hp : p < l1.val.size), l1.val[p]'hp = v.val[k]'hk) ∧
      (∀ (k : Nat) (hk : k < v.val.size),
          ∃ q : Nat, ∃ (hq : q < l2.val.size), l2.val[q]'hq = v.val[k]'hk) ∧
      (∀ (j : Nat) (hj : j < l1.val.size),
          mem_slice l2 (l1.val[j]'hj) → mem_slice v (l1.val[j]'hj)) ∧
      (∀ (k₁ k₂ : Nat) (hk₁ : k₁ < v.val.size) (hk₂ : k₂ < v.val.size),
          v.val[k₁]'hk₁ = v.val[k₂]'hk₂ → k₁ = k₂) := by
  intro n
  induction n with
  | zero =>
    intro i acc v hm hi_le inv_A inv_B inv_C inv_D inv_E hres
    have hi_eq : i.toNat = l1.val.size := by omega
    have hi_ge : l1.val.size ≤ i.toNat := by omega
    rw [build_common_at_oob l1 l2 i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    refine ⟨inv_A, inv_B, ?_, inv_D⟩
    intro j hj hmem
    have : j < i.toNat := by rw [hi_eq]; exact hj
    exact inv_C j hj this hmem
  | succ n ih =>
    intro i acc v hm hi_le inv_A inv_B inv_C inv_D inv_E hres
    by_cases hi_ge : l1.val.size ≤ i.toNat
    · have hi_eq : i.toNat = l1.val.size := by omega
      rw [build_common_at_oob l1 l2 i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      refine ⟨inv_A, inv_B, ?_, inv_D⟩
      intro j hj hmem
      have : j < i.toNat := by rw [hi_eq]; exact hj
      exact inv_C j hj this hmem
    · have hi_lt : i.toNat < l1.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l1.val.size < USize64.size := l1.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l1.val.size := by rw [h_i1]; omega
      have h_meas : l1.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      have h_acc_succ : acc.val.size + 1 < USize64.size := by
        rw [h_usize_size]; omega
      -- Case-split on the inner contains_at queries (both totally succeed).
      obtain ⟨b_l2, h_l2_eq, h_l2_iff⟩ := contains_at_zero_total l2 (l1.val[i.toNat]'hi_lt)
      obtain ⟨b_acc, h_acc_eq, h_acc_iff⟩ := contains_at_zero_total acc (l1.val[i.toNat]'hi_lt)
      cases b_l2 with
      | false =>
        -- Skip (not in l2).
        rw [build_common_at_step_skip_l2 l1 l2 i acc hi_lt h_l2_eq b_acc h_acc_eq] at hres
        have h_not_mem_l2 : ¬ mem_slice l2 (l1.val[i.toNat]'hi_lt) := by
          intro hm'
          have h_f : (false : Bool) = true := h_l2_iff.mpr hm'
          exact Bool.noConfusion h_f
        -- Build invariants for the IH.
        have inv_C' :
            ∀ (j : Nat) (hj : j < l1.val.size), j < (i + 1).toNat →
              mem_slice l2 (l1.val[j]'hj) → mem_slice acc (l1.val[j]'hj) := by
          intro j hj h_j_lt hmem
          rw [h_i1] at h_j_lt
          by_cases h_eq_i : j = i.toNat
          · -- j = i.toNat: l1[j] = l1[i.toNat]. But l1[i.toNat] is not in l2.
            exfalso
            have h_lhs_eq : l1.val[j]'hj = l1.val[i.toNat]'hi_lt := by
              congr 1
            rw [h_lhs_eq] at hmem
            exact h_not_mem_l2 hmem
          · have h_j_lt' : j < i.toNat := by omega
            exact inv_C j hj h_j_lt' hmem
        have inv_E' : acc.val.size ≤ (i + 1).toNat := by rw [h_i1]; omega
        exact ih (i + 1) acc v h_meas h_i1_le inv_A inv_B inv_C' inv_D inv_E' hres
      | true =>
        cases b_acc with
        | true =>
          -- Already in acc. Skip.
          rw [build_common_at_step_skip_acc l1 l2 i acc hi_lt h_l2_eq h_acc_eq] at hres
          have h_mem_l2 : mem_slice l2 (l1.val[i.toNat]'hi_lt) := h_l2_iff.mp rfl
          have h_mem_acc : mem_slice acc (l1.val[i.toNat]'hi_lt) := h_acc_iff.mp rfl
          have inv_C' :
              ∀ (j : Nat) (hj : j < l1.val.size), j < (i + 1).toNat →
                mem_slice l2 (l1.val[j]'hj) → mem_slice acc (l1.val[j]'hj) := by
            intro j hj h_j_lt hmem
            rw [h_i1] at h_j_lt
            by_cases h_eq_i : j = i.toNat
            · subst h_eq_i
              exact h_mem_acc
            · have h_j_lt' : j < i.toNat := by omega
              exact inv_C j hj h_j_lt' hmem
          have inv_E' : acc.val.size ≤ (i + 1).toNat := by rw [h_i1]; omega
          exact ih (i + 1) acc v h_meas h_i1_le inv_A inv_B inv_C' inv_D inv_E' hres
        | false =>
          -- Push branch.
          have h_mem_l2 : mem_slice l2 (l1.val[i.toNat]'hi_lt) := h_l2_iff.mp rfl
          have h_not_mem_acc : ¬ mem_slice acc (l1.val[i.toNat]'hi_lt) := by
            intro hm'
            have h_f : (false : Bool) = true := h_acc_iff.mpr hm'
            exact Bool.noConfusion h_f
          rw [build_common_at_step_push l1 l2 i acc hi_lt h_l2_eq h_acc_eq h_acc_succ] at hres
          -- Compute invariants for the pushed acc.
          let acc' := push_one acc (l1.val[i.toNat]'hi_lt) h_acc_succ
          have h_acc'_size : acc'.val.size = acc.val.size + 1 := push_one_size acc _ h_acc_succ
          have h_acc'_val : acc'.val = acc.val ++ #[l1.val[i.toNat]'hi_lt] := push_one_val acc _ h_acc_succ
          -- (A) for acc'
          have inv_A' :
              ∀ (k : Nat) (hk : k < acc'.val.size),
                ∃ p : Nat, ∃ (hp : p < l1.val.size), l1.val[p]'hp = acc'.val[k]'hk := by
            intro k hk
            show ∃ p : Nat, ∃ (hp : p < l1.val.size),
                l1.val[p]'hp = (acc.val ++ #[l1.val[i.toNat]'hi_lt])[k]'_
            by_cases hk_lt : k < acc.val.size
            · rw [Array.getElem_append_left hk_lt]
              exact inv_A k hk_lt
            · have hk_eq : k = acc.val.size := by
                have : k < acc.val.size + 1 := by
                  have hsize_eq : acc'.val.size = acc.val.size + 1 := h_acc'_size
                  rw [hsize_eq] at hk; exact hk
                omega
              subst hk_eq
              rw [Array.getElem_append_right (Nat.le_refl _)]
              simp only [Nat.sub_self]
              exact ⟨i.toNat, hi_lt, rfl⟩
          -- (B) for acc'
          have inv_B' :
              ∀ (k : Nat) (hk : k < acc'.val.size),
                ∃ q : Nat, ∃ (hq : q < l2.val.size), l2.val[q]'hq = acc'.val[k]'hk := by
            intro k hk
            show ∃ q : Nat, ∃ (hq : q < l2.val.size),
                l2.val[q]'hq = (acc.val ++ #[l1.val[i.toNat]'hi_lt])[k]'_
            by_cases hk_lt : k < acc.val.size
            · rw [Array.getElem_append_left hk_lt]
              exact inv_B k hk_lt
            · have hk_eq : k = acc.val.size := by
                have : k < acc.val.size + 1 := by
                  have hsize_eq : acc'.val.size = acc.val.size + 1 := h_acc'_size
                  rw [hsize_eq] at hk; exact hk
                omega
              subst hk_eq
              rw [Array.getElem_append_right (Nat.le_refl _)]
              simp only [Nat.sub_self]
              -- l1[i.toNat] is in l2 by h_mem_l2
              obtain ⟨q, hq, hqeq⟩ := h_mem_l2
              exact ⟨q, hq, hqeq⟩
          -- (C) for acc'
          have inv_C' :
              ∀ (j : Nat) (hj : j < l1.val.size), j < (i + 1).toNat →
                mem_slice l2 (l1.val[j]'hj) → mem_slice acc' (l1.val[j]'hj) := by
            intro j hj h_j_lt hmem
            rw [h_i1] at h_j_lt
            by_cases h_eq_i : j = i.toNat
            · -- j = i.toNat: l1[j] = l1[i.toNat], which is in acc' at position acc.val.size
              subst h_eq_i
              refine ⟨acc.val.size, ?_, ?_⟩
              · show acc.val.size < acc'.val.size
                rw [h_acc'_size]; omega
              · show acc'.val[acc.val.size]'_ = l1.val[i.toNat]'hi_lt
                show (acc.val ++ #[l1.val[i.toNat]'hi_lt])[acc.val.size]'_
                     = l1.val[i.toNat]'hi_lt
                rw [Array.getElem_append_right (Nat.le_refl _)]
                simp only [Nat.sub_self]
                rfl
            · -- j < i.toNat: in old acc, hence in acc'
              have h_j_lt' : j < i.toNat := by omega
              obtain ⟨k, hk, hkeq⟩ := inv_C j hj h_j_lt' hmem
              have hk' : k < acc'.val.size := by rw [h_acc'_size]; omega
              refine ⟨k, hk', ?_⟩
              show acc'.val[k]'hk' = l1.val[j]'hj
              have h_acc'_get :
                  acc'.val[k]'hk' = (acc.val ++ #[l1.val[i.toNat]'hi_lt])[k]'(by
                    rw [Array.size_append]; show k < acc.val.size + _; omega) := by
                show (acc.val ++ #[l1.val[i.toNat]'hi_lt])[k]'_ =
                     (acc.val ++ #[l1.val[i.toNat]'hi_lt])[k]'_
                rfl
              rw [h_acc'_get, Array.getElem_append_left hk]
              exact hkeq
          -- (D) for acc'
          have inv_D' :
              ∀ (k₁ k₂ : Nat) (hk₁ : k₁ < acc'.val.size) (hk₂ : k₂ < acc'.val.size),
                acc'.val[k₁]'hk₁ = acc'.val[k₂]'hk₂ → k₁ = k₂ := by
            intro k₁ k₂ hk₁ hk₂ heq
            show k₁ = k₂
            -- Helper: acc' val
            have h_size_eq : acc'.val.size = acc.val.size + 1 := h_acc'_size
            by_cases hk₁_lt : k₁ < acc.val.size
            · by_cases hk₂_lt : k₂ < acc.val.size
              · -- Both in old acc range
                apply inv_D k₁ k₂ hk₁_lt hk₂_lt
                have ha1 : acc'.val[k₁]'hk₁ = acc.val[k₁]'hk₁_lt := by
                  show (acc.val ++ #[l1.val[i.toNat]'hi_lt])[k₁]'_ = acc.val[k₁]'hk₁_lt
                  rw [Array.getElem_append_left hk₁_lt]
                have ha2 : acc'.val[k₂]'hk₂ = acc.val[k₂]'hk₂_lt := by
                  show (acc.val ++ #[l1.val[i.toNat]'hi_lt])[k₂]'_ = acc.val[k₂]'hk₂_lt
                  rw [Array.getElem_append_left hk₂_lt]
                rw [ha1, ha2] at heq
                exact heq
              · -- k₁ in old acc, k₂ = acc.val.size (new element)
                have hk₂_eq : k₂ = acc.val.size := by omega
                exfalso
                -- acc'[k₁] = acc[k₁], acc'[k₂] = l1[i.toNat]. heq says they're equal.
                -- So l1[i.toNat] = acc[k₁], i.e., l1[i.toNat] ∈ acc. But h_not_mem_acc.
                apply h_not_mem_acc
                refine ⟨k₁, hk₁_lt, ?_⟩
                have ha1 : acc'.val[k₁]'hk₁ = acc.val[k₁]'hk₁_lt := by
                  show (acc.val ++ #[l1.val[i.toNat]'hi_lt])[k₁]'_ = acc.val[k₁]'hk₁_lt
                  rw [Array.getElem_append_left hk₁_lt]
                have ha2 : acc'.val[k₂]'hk₂ = l1.val[i.toNat]'hi_lt := by
                  subst hk₂_eq
                  show (acc.val ++ #[l1.val[i.toNat]'hi_lt])[acc.val.size]'_
                       = l1.val[i.toNat]'hi_lt
                  rw [Array.getElem_append_right (Nat.le_refl _)]
                  simp only [Nat.sub_self]
                  rfl
                rw [ha1] at heq
                rw [ha2] at heq
                exact heq
            · by_cases hk₂_lt : k₂ < acc.val.size
              · -- k₁ = acc.val.size, k₂ in old acc
                have hk₁_eq : k₁ = acc.val.size := by omega
                exfalso
                apply h_not_mem_acc
                refine ⟨k₂, hk₂_lt, ?_⟩
                have ha1 : acc'.val[k₁]'hk₁ = l1.val[i.toNat]'hi_lt := by
                  subst hk₁_eq
                  show (acc.val ++ #[l1.val[i.toNat]'hi_lt])[acc.val.size]'_
                       = l1.val[i.toNat]'hi_lt
                  rw [Array.getElem_append_right (Nat.le_refl _)]
                  simp only [Nat.sub_self]
                  rfl
                have ha2 : acc'.val[k₂]'hk₂ = acc.val[k₂]'hk₂_lt := by
                  show (acc.val ++ #[l1.val[i.toNat]'hi_lt])[k₂]'_ = acc.val[k₂]'hk₂_lt
                  rw [Array.getElem_append_left hk₂_lt]
                rw [ha1] at heq
                rw [ha2] at heq
                exact heq.symm
              · -- Both k₁ = k₂ = acc.val.size
                omega
          have inv_E' : acc'.val.size ≤ (i + 1).toNat := by
            rw [h_acc'_size, h_i1]; omega
          exact ih (i + 1) acc' v h_meas h_i1_le inv_A' inv_B' inv_C' inv_D' inv_E' hres

/-! ## Aux: bundle invariants for `common`. -/

private theorem common_correct
    (l1 l2 : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_057_common.common l1 l2 = RustM.ok v) :
    (∀ (k : Nat) (hk : k < v.val.size),
        ∃ p : Nat, ∃ (hp : p < l1.val.size), l1.val[p]'hp = v.val[k]'hk) ∧
    (∀ (k : Nat) (hk : k < v.val.size),
        ∃ q : Nat, ∃ (hq : q < l2.val.size), l2.val[q]'hq = v.val[k]'hk) ∧
    (∀ (j : Nat) (hj : j < l1.val.size),
        mem_slice l2 (l1.val[j]'hj) → mem_slice v (l1.val[j]'hj)) ∧
    (∀ (k₁ k₂ : Nat) (hk₁ : k₁ < v.val.size) (hk₂ : k₂ < v.val.size),
        v.val[k₁]'hk₁ = v.val[k₂]'hk₂ → k₁ = k₂) := by
  unfold clever_057_common.common at hres
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new, RustM_ok_bind] at hres
  let acc0 : alloc.vec.Vec i64 alloc.alloc.Global := ⟨(List.nil).toArray, by grind⟩
  have h_acc0_size : acc0.val.size = 0 := rfl
  have inv_A0 : ∀ (k : Nat) (hk : k < acc0.val.size),
      ∃ p : Nat, ∃ (hp : p < l1.val.size), l1.val[p]'hp = acc0.val[k]'hk := by
    intro k hk; rw [h_acc0_size] at hk; omega
  have inv_B0 : ∀ (k : Nat) (hk : k < acc0.val.size),
      ∃ q : Nat, ∃ (hq : q < l2.val.size), l2.val[q]'hq = acc0.val[k]'hk := by
    intro k hk; rw [h_acc0_size] at hk; omega
  have inv_C0 : ∀ (j : Nat) (hj : j < l1.val.size), j < (0 : usize).toNat →
      mem_slice l2 (l1.val[j]'hj) → mem_slice acc0 (l1.val[j]'hj) := by
    intro j hj h_lt _hmem
    rw [usize_zero_toNat] at h_lt
    omega
  have inv_D0 : ∀ (k₁ k₂ : Nat) (hk₁ : k₁ < acc0.val.size) (hk₂ : k₂ < acc0.val.size),
      acc0.val[k₁]'hk₁ = acc0.val[k₂]'hk₂ → k₁ = k₂ := by
    intro k₁ k₂ hk₁ _ _; rw [h_acc0_size] at hk₁; omega
  have inv_E0 : acc0.val.size ≤ (0 : usize).toNat := by
    rw [h_acc0_size, usize_zero_toNat]
    exact Nat.le_refl _
  have h_meas : l1.val.size - (0 : usize).toNat ≤ l1.val.size := by
    rw [usize_zero_toNat]; omega
  have h_i_le : (0 : usize).toNat ≤ l1.val.size := by
    rw [usize_zero_toNat]; omega
  exact build_common_at_correct l1 l2 l1.val.size (0 : usize) acc0 v
    h_meas h_i_le inv_A0 inv_B0 inv_C0 inv_D0 inv_E0 hres

/-! ## Top-level obligations on `common`. -/

/-- Soundness (output ⊆ l1): every output element occurs somewhere in `l1`. -/
theorem output_element_in_l1
    (l1 l2 : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_057_common.common l1 l2 = RustM.ok v)
    (k : Nat) (hk : k < v.val.size) :
    ∃ i : Nat, ∃ (hi : i < l1.val.size), l1.val[i]'hi = v.val[k]'hk := by
  obtain ⟨hA, _, _, _⟩ := common_correct l1 l2 v hres
  exact hA k hk

/-- Soundness (output ⊆ l2): every output element occurs somewhere in `l2`. -/
theorem output_element_in_l2
    (l1 l2 : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_057_common.common l1 l2 = RustM.ok v)
    (k : Nat) (hk : k < v.val.size) :
    ∃ j : Nat, ∃ (hj : j < l2.val.size), l2.val[j]'hj = v.val[k]'hk := by
  obtain ⟨_, hB, _, _⟩ := common_correct l1 l2 v hres
  exact hB k hk

/-- Completeness (l1 ∩ l2 ⊆ output). -/
theorem intersection_element_in_output
    (l1 l2 : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_057_common.common l1 l2 = RustM.ok v)
    (x : i64)
    (h1 : ∃ i : Nat, ∃ (hi : i < l1.val.size), l1.val[i]'hi = x)
    (h2 : ∃ j : Nat, ∃ (hj : j < l2.val.size), l2.val[j]'hj = x) :
    ∃ k : Nat, ∃ (hk : k < v.val.size), v.val[k]'hk = x := by
  obtain ⟨_, _, hC, _⟩ := common_correct l1 l2 v hres
  obtain ⟨i, hi, hieq⟩ := h1
  -- mem_slice l2 (l1[i])
  have h_mem_l2 : mem_slice l2 (l1.val[i]'hi) := by
    obtain ⟨j, hj, hjeq⟩ := h2
    refine ⟨j, hj, ?_⟩
    rw [hjeq, ← hieq]
  -- Apply hC to get mem_slice v (l1[i])
  have h_mem_v : mem_slice v (l1.val[i]'hi) := hC i hi h_mem_l2
  obtain ⟨k, hk, hkeq⟩ := h_mem_v
  refine ⟨k, hk, ?_⟩
  rw [hkeq, hieq]

/-- Uniqueness: distinct output positions carry distinct values. -/
theorem output_has_no_duplicates
    (l1 l2 : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_057_common.common l1 l2 = RustM.ok v)
    (k₁ k₂ : Nat) (hk₁ : k₁ < v.val.size) (hk₂ : k₂ < v.val.size)
    (h : v.val[k₁]'hk₁ = v.val[k₂]'hk₂) :
    k₁ = k₂ := by
  obtain ⟨_, _, _, hD⟩ := common_correct l1 l2 v hres
  exact hD k₁ k₂ hk₁ hk₂ h

end Clever_057_commonObligations
