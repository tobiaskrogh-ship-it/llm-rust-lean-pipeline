-- Companion obligations file for the `contains_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import contains_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Contains_u64Obligations

/-- Helper: `RustM.ok x >>= f = f x`. The library's `pure_bind` simp lemma
    only matches literal `Pure.pure`; this rewrite handles the `RustM.ok`
    form that simp produces after reducing definitions. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

/-- Helper: `(1 : usize).toNat = 1`. -/
private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

/-- Helper: `(i + 1).toNat = i.toNat + 1` when no overflow. -/
private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

/-- Out-of-bounds step: when `i.toNat ≥ arr.val.size`, the function returns `false`. -/
private theorem contains_at_oob (arr : RustSlice u64) (target : u64) (i : usize)
    (hi : arr.val.size ≤ i.toNat) :
    contains_u64.contains_at arr target i = RustM.ok false := by
  conv => lhs; unfold contains_u64.contains_at
  have h_ofNat : (USize64.ofNat arr.val.size).toNat = arr.val.size :=
    USize64.toNat_ofNat_of_lt' arr.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat arr.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- Found step: when `i.toNat < arr.val.size` and `arr[i] = target`, returns `true`. -/
private theorem contains_at_found (arr : RustSlice u64) (target : u64) (i : usize)
    (hi : i.toNat < arr.val.size) (h : arr.val[i.toNat]'hi = target) :
    contains_u64.contains_at arr target i = RustM.ok true := by
  conv => lhs; unfold contains_u64.contains_at
  have h_ofNat : (USize64.ofNat arr.val.size).toNat = arr.val.size :=
    USize64.toNat_ofNat_of_lt' arr.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat arr.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (arr[i]_? : RustM u64) = RustM.ok (arr.val[i.toNat]'hi) := by
    show (if h : i.toNat < arr.val.size then pure (arr.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (arr.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
  have h_beq_true : (arr.val[i.toNat]'hi == target) = true := by
    rw [beq_iff_eq]; exact h
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.cmp.eq, h_beq_true]
  rfl

/-- Recursion step: when `i.toNat < arr.val.size` and `arr[i] ≠ target`,
    the function recurses with `i + 1`. -/
private theorem contains_at_recurse (arr : RustSlice u64) (target : u64) (i : usize)
    (hi : i.toNat < arr.val.size) (h : arr.val[i.toNat]'hi ≠ target) :
    contains_u64.contains_at arr target i = contains_u64.contains_at arr target (i + 1) := by
  conv => lhs; unfold contains_u64.contains_at
  have h_ofNat : (USize64.ofNat arr.val.size).toNat = arr.val.size :=
    USize64.toNat_ofNat_of_lt' arr.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat arr.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (arr[i]_? : RustM u64) = RustM.ok (arr.val[i.toNat]'hi) := by
    show (if h : i.toNat < arr.val.size then pure (arr.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (arr.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
  have h_beq_false : (arr.val[i.toNat]'hi == target) = false := by
    rw [beq_eq_false_iff_ne]; exact h
  have h_size : arr.val.size < 2^64 := arr.size_lt_usizeSize
  have h_no_overflow : i.toNat + 1 < 2^64 := by omega
  have h_no_bv : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hi := (USize64.uaddOverflow_iff i 1).mp hbo
      rw [usize_one_toNat] at hi
      omega
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.cmp.eq, h_beq_false,
             rust_primitives.ops.arith.Add.add, h_no_bv]

/-- Workhorse iff lemma: `contains_at arr target i = ok true` iff there is a
    witness index `j` with `i.toNat ≤ j < arr.val.size` and `arr[j] = target`.
    Proved by strong induction on the measure `arr.val.size - i.toNat`. -/
private theorem contains_at_iff (arr : RustSlice u64) (target : u64) (i : usize) :
    contains_u64.contains_at arr target i = RustM.ok true ↔
    ∃ j : Nat, i.toNat ≤ j ∧ ∃ (hj : j < arr.val.size), arr.val[j]'hj = target := by
  induction hk : (arr.val.size - i.toNat) using Nat.strongRecOn generalizing i with
  | _ k ih =>
    by_cases hbound : arr.val.size ≤ i.toNat
    · rw [contains_at_oob arr target i hbound]
      apply iff_of_false
      · intro h
        injection h with h1
        injection h1 with h2
        exact Bool.noConfusion h2
      · rintro ⟨j, hij, hjsize, hjeq⟩
        omega
    · have hbound' : i.toNat < arr.val.size := Nat.lt_of_not_le hbound
      by_cases hit : arr.val[i.toNat]'hbound' = target
      · rw [contains_at_found arr target i hbound' hit]
        constructor
        · intro _
          exact ⟨i.toNat, Nat.le_refl _, hbound', hit⟩
        · intro _
          rfl
      · rw [contains_at_recurse arr target i hbound' hit]
        have h_size : arr.val.size < 2^64 := arr.size_lt_usizeSize
        have h_no_overflow : i.toNat + 1 < 2^64 := by omega
        have h_i1_toNat : (i + 1).toNat = i.toNat + 1 :=
          usize_add_one_toNat i h_no_overflow
        have h_measure_lt : arr.val.size - (i + 1).toNat < k := by
          rw [h_i1_toNat]; omega
        have ih_i1 := ih (arr.val.size - (i + 1).toNat) h_measure_lt (i + 1) rfl
        rw [ih_i1]
        constructor
        · rintro ⟨j, hij, hjsize, hjeq⟩
          refine ⟨j, ?_, hjsize, hjeq⟩
          rw [h_i1_toNat] at hij
          omega
        · rintro ⟨j, hij, hjsize, hjeq⟩
          refine ⟨j, ?_, hjsize, hjeq⟩
          rw [h_i1_toNat]
          rcases Nat.lt_or_ge i.toNat j with hlt | hge
          · omega
          · have hj_eq_i : j = i.toNat := by omega
            exfalso
            apply hit
            rw [← hjeq]
            congr 1
            exact hj_eq_i.symm

/-- Soundness clause of the contract.

    Captures the property test `soundness_true_implies_witness_exists`:
    if `contains arr target` returns `true`, then some index of `arr`
    actually equals `target`. A buggy implementation that ever returns
    `true` without a real witness (e.g. an off-by-one that reads past
    the end, or an always-true short-circuit) would falsify this. -/
theorem contains_sound (arr : RustSlice u64) (target : u64)
    (h : contains_u64.contains arr target = RustM.ok true) :
    ∃ i : Nat, ∃ (hi : i < arr.val.size), arr.val[i]'hi = target := by
  unfold contains_u64.contains at h
  have := (contains_at_iff arr target 0).mp h
  obtain ⟨j, _hij, hjsize, hjeq⟩ := this
  exact ⟨j, hjsize, hjeq⟩

/-- Completeness clause of the contract.

    Captures the property test `completeness_witness_implies_true`:
    if some index of `arr` equals `target`, then `contains arr target`
    returns `true`. A buggy implementation that returns `false` despite
    a real witness (e.g. stops one step early, or always-false) would
    falsify this. -/
theorem contains_complete (arr : RustSlice u64) (target : u64)
    (h : ∃ i : Nat, ∃ (hi : i < arr.val.size), arr.val[i]'hi = target) :
    contains_u64.contains arr target = RustM.ok true := by
  unfold contains_u64.contains
  apply (contains_at_iff arr target 0).mpr
  obtain ⟨j, hjsize, hjeq⟩ := h
  refine ⟨j, ?_, hjsize, hjeq⟩
  show (0 : USize64).toNat ≤ j
  exact Nat.zero_le _

end Contains_u64Obligations
