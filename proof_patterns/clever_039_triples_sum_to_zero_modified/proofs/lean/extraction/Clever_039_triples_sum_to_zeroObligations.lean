-- Companion obligations file for the `clever_039_triples_sum_to_zero` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_039_triples_sum_to_zero

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_039_triples_sum_to_zeroObligations

/-! ## Specification oracle (Nat-valued)

`count_zeros_from numbers i` counts indices `k ∈ [i, numbers.val.size)` with
`numbers.val[k] = 0`. Total on `Nat` and decreasing on `numbers.val.size - i`. -/

private def count_zeros_from (numbers : RustSlice u64) (i : Nat) : Nat :=
  if h : i < numbers.val.size then
    (if numbers.val[i]'h = (0 : u64) then 1 else 0) + count_zeros_from numbers (i + 1)
  else 0
termination_by numbers.val.size - i

/-! ## Helpers (transferred from `contains_u64` reference). -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

private theorem u64_one_toNat : (1 : u64).toNat = 1 := rfl

private theorem u64_add_one_toNat (a : u64) (h : a.toNat + 1 < 2^64) :
    (a + 1).toNat = a.toNat + 1 := by
  have h_pre : a.toNat + (1 : u64).toNat < 2^64 := by
    rw [u64_one_toNat]; exact h
  rw [UInt64.toNat_add_of_lt h_pre, u64_one_toNat]

/-! ## Step lemmas for `count_zeros_at` (mirroring the three branches of the
recursive body). -/

/-- Out-of-bounds step: when `i.toNat ≥ numbers.val.size`, the function
    returns `RustM.ok acc`. -/
private theorem count_zeros_at_oob
    (numbers : RustSlice u64) (i : usize) (acc : u64)
    (hi : numbers.val.size ≤ i.toNat) :
    clever_039_triples_sum_to_zero.count_zeros_at numbers i acc = RustM.ok acc := by
  conv => lhs; unfold clever_039_triples_sum_to_zero.count_zeros_at
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' numbers.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat numbers.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- Match step: when `i.toNat < numbers.val.size`, `numbers[i] = 0`, and
    `acc.toNat + 1 < 2^64`, the function delegates to `count_zeros_at numbers
    (i+1) (acc+1)`. -/
private theorem count_zeros_at_match
    (numbers : RustSlice u64) (i : usize) (acc : u64)
    (hi : i.toNat < numbers.val.size)
    (h : numbers.val[i.toNat]'hi = (0 : u64))
    (h_no_acc : acc.toNat + 1 < 2^64) :
    clever_039_triples_sum_to_zero.count_zeros_at numbers i acc =
      clever_039_triples_sum_to_zero.count_zeros_at numbers (i + 1) (acc + 1) := by
  conv => lhs; unfold clever_039_triples_sum_to_zero.count_zeros_at
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' numbers.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat numbers.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (numbers[i]_? : RustM u64) = RustM.ok (numbers.val[i.toNat]'hi) := by
    show (if h : i.toNat < numbers.val.size then pure (numbers.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (numbers.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
  have h_beq_true : (numbers.val[i.toNat]'hi == (0 : u64)) = true := by
    rw [beq_iff_eq]; exact h
  have h_size : numbers.val.size < 2^64 := numbers.size_lt_usizeSize
  have h_no_overflow_i : i.toNat + 1 < 2^64 := by omega
  have h_no_bv_i : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hi' := (USize64.uaddOverflow_iff i 1).mp hbo
      rw [usize_one_toNat] at hi'
      omega
  have h_no_bv_acc : BitVec.uaddOverflow acc.toBitVec ((1 : u64).toBitVec) = false := by
    generalize hbo : BitVec.uaddOverflow acc.toBitVec ((1 : u64).toBitVec) = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have : UInt64.addOverflow acc 1 := hbo
      rw [UInt64.addOverflow_iff] at this
      rw [u64_one_toNat] at this
      omega
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.cmp.eq, h_beq_true,
             rust_primitives.ops.arith.Add.add, h_no_bv_i, h_no_bv_acc]

/-- Non-match step: when `i.toNat < numbers.val.size` and `numbers[i] ≠ 0`,
    the function delegates to `count_zeros_at numbers (i+1) acc`. -/
private theorem count_zeros_at_norm
    (numbers : RustSlice u64) (i : usize) (acc : u64)
    (hi : i.toNat < numbers.val.size)
    (h : numbers.val[i.toNat]'hi ≠ (0 : u64)) :
    clever_039_triples_sum_to_zero.count_zeros_at numbers i acc =
      clever_039_triples_sum_to_zero.count_zeros_at numbers (i + 1) acc := by
  conv => lhs; unfold clever_039_triples_sum_to_zero.count_zeros_at
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' numbers.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat numbers.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (numbers[i]_? : RustM u64) = RustM.ok (numbers.val[i.toNat]'hi) := by
    show (if h : i.toNat < numbers.val.size then pure (numbers.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (numbers.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
  have h_beq_false : (numbers.val[i.toNat]'hi == (0 : u64)) = false := by
    rw [beq_eq_false_iff_ne]; exact h
  have h_size : numbers.val.size < 2^64 := numbers.size_lt_usizeSize
  have h_no_overflow_i : i.toNat + 1 < 2^64 := by omega
  have h_no_bv_i : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hi' := (USize64.uaddOverflow_iff i 1).mp hbo
      rw [usize_one_toNat] at hi'
      omega
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.cmp.eq, h_beq_false,
             rust_primitives.ops.arith.Add.add, h_no_bv_i]

/-! ## Equational lemmas for the Nat-level spec oracle. -/

private theorem count_zeros_from_oob (numbers : RustSlice u64) (i : Nat)
    (h : ¬ i < numbers.val.size) :
    count_zeros_from numbers i = 0 := by
  unfold count_zeros_from; rw [dif_neg h]

private theorem count_zeros_from_succ (numbers : RustSlice u64) (i : Nat)
    (h : i < numbers.val.size) :
    count_zeros_from numbers i =
      (if numbers.val[i]'h = (0 : u64) then 1 else 0) + count_zeros_from numbers (i + 1) := by
  conv => lhs; unfold count_zeros_from
  rw [dif_pos h]

/-- The count of zeros from index `i` is bounded by the number of remaining indices. -/
private theorem count_zeros_from_le (numbers : RustSlice u64) (i : Nat) :
    count_zeros_from numbers i ≤ numbers.val.size - i := by
  induction hk : (numbers.val.size - i) using Nat.strongRecOn generalizing i with
  | _ k ih =>
    by_cases h : i < numbers.val.size
    · rw [count_zeros_from_succ numbers i h]
      have h_meas : numbers.val.size - (i + 1) < k := by rw [← hk]; omega
      have h_ih := ih (numbers.val.size - (i + 1)) h_meas (i + 1) rfl
      by_cases hz : numbers.val[i]'h = (0 : u64)
      · rw [if_pos hz]; omega
      · rw [if_neg hz]; omega
    · rw [count_zeros_from_oob numbers i h]; omega

/-! ## Workhorse: `count_zeros_at` agrees with the Nat-level oracle.

Strong induction on the measure `numbers.val.size - i.toNat`. The
`h_acc` precondition ensures the running accumulator plus the remaining
zero count fits in a `u64`, discharging both the `acc +? 1` overflow check
and the final ok-equation. -/
private theorem count_zeros_at_correct
    (numbers : RustSlice u64) (i : usize) (acc : u64)
    (h_acc : acc.toNat + (numbers.val.size - i.toNat) < 2^64) :
    ∃ v : u64,
      clever_039_triples_sum_to_zero.count_zeros_at numbers i acc = RustM.ok v
      ∧ v.toNat = acc.toNat + count_zeros_from numbers i.toNat := by
  induction hk : (numbers.val.size - i.toNat) using Nat.strongRecOn generalizing i acc with
  | _ k ih =>
    by_cases h_oob : numbers.val.size ≤ i.toNat
    · have h_eq := count_zeros_at_oob numbers i acc h_oob
      have h_size_eq : count_zeros_from numbers i.toNat = 0 := by
        apply count_zeros_from_oob; omega
      refine ⟨acc, h_eq, ?_⟩
      rw [h_size_eq]
    · have hi : i.toNat < numbers.val.size := Nat.lt_of_not_le h_oob
      have h_size : numbers.val.size < 2^64 := numbers.size_lt_usizeSize
      have h_no_overflow_i : i.toNat + 1 < 2^64 := by omega
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 :=
        usize_add_one_toNat i h_no_overflow_i
      have h_count_le : count_zeros_from numbers (i.toNat + 1) ≤ numbers.val.size - (i.toNat + 1) :=
        count_zeros_from_le numbers (i.toNat + 1)
      have h_measure : numbers.val.size - (i + 1).toNat < k := by rw [h_i1_toNat]; omega
      have h_csz_succ := count_zeros_from_succ numbers i.toNat hi
      by_cases hz : numbers.val[i.toNat]'hi = (0 : u64)
      · -- zero case: recurse with (i+1, acc+1)
        have h_no_acc : acc.toNat + 1 < 2^64 := by omega
        have h_step := count_zeros_at_match numbers i acc hi hz h_no_acc
        have h_acc1_toNat : (acc + 1).toNat = acc.toNat + 1 :=
          u64_add_one_toNat acc h_no_acc
        have h_acc' : (acc + 1).toNat + (numbers.val.size - (i + 1).toNat) < 2^64 := by
          rw [h_acc1_toNat, h_i1_toNat]; omega
        obtain ⟨v, hv_eq, hv_nat⟩ :=
          ih (numbers.val.size - (i + 1).toNat) h_measure (i + 1) (acc + 1) h_acc' rfl
        refine ⟨v, ?_, ?_⟩
        · rw [h_step]; exact hv_eq
        · rw [hv_nat, h_acc1_toNat, h_i1_toNat, h_csz_succ, if_pos hz]; omega
      · -- non-zero case: recurse with (i+1, acc)
        have h_step := count_zeros_at_norm numbers i acc hi hz
        have h_acc' : acc.toNat + (numbers.val.size - (i + 1).toNat) < 2^64 := by
          rw [h_i1_toNat]; omega
        obtain ⟨v, hv_eq, hv_nat⟩ :=
          ih (numbers.val.size - (i + 1).toNat) h_measure (i + 1) acc h_acc' rfl
        refine ⟨v, ?_, ?_⟩
        · rw [h_step]; exact hv_eq
        · rw [hv_nat, h_i1_toNat, h_csz_succ, if_neg hz]; omega

/-! ## Forward bridge: count-threshold ⇒ existence of distinct zero indices.

Three small lemmas in a ladder. Each lemma extracts one zero from the
running count and recurses for the rest. -/

private theorem one_zero_from
    (numbers : RustSlice u64) (start : Nat)
    (h_count : count_zeros_from numbers start ≥ 1) :
    ∃ i : Nat, ∃ (hi : i < numbers.val.size),
      start ≤ i ∧ numbers.val[i]'hi = (0 : u64) := by
  induction hk : numbers.val.size - start using Nat.strongRecOn generalizing start with
  | _ k ih =>
    by_cases h_oob : numbers.val.size ≤ start
    · exfalso
      have : count_zeros_from numbers start = 0 :=
        count_zeros_from_oob numbers start (by omega)
      omega
    · have h_lt : start < numbers.val.size := Nat.lt_of_not_le h_oob
      have h_meas : numbers.val.size - (start + 1) < k := by rw [← hk]; omega
      have h_csz := count_zeros_from_succ numbers start h_lt
      by_cases hz : numbers.val[start]'h_lt = (0 : u64)
      · exact ⟨start, h_lt, Nat.le_refl _, hz⟩
      · rw [h_csz, if_neg hz] at h_count
        have h_count' : count_zeros_from numbers (start + 1) ≥ 1 := by omega
        obtain ⟨i, hi_lt, hi_le, hi_eq⟩ := ih _ h_meas (start + 1) h_count' rfl
        exact ⟨i, hi_lt, by omega, hi_eq⟩

private theorem two_zeros_from
    (numbers : RustSlice u64) (start : Nat)
    (h_count : count_zeros_from numbers start ≥ 2) :
    ∃ i j : Nat, ∃ (hi : i < numbers.val.size) (hj : j < numbers.val.size),
      start ≤ i ∧ i < j ∧
      numbers.val[i]'hi = (0 : u64) ∧ numbers.val[j]'hj = (0 : u64) := by
  induction hk : numbers.val.size - start using Nat.strongRecOn generalizing start with
  | _ k ih =>
    by_cases h_oob : numbers.val.size ≤ start
    · exfalso
      have : count_zeros_from numbers start = 0 :=
        count_zeros_from_oob numbers start (by omega)
      omega
    · have h_lt : start < numbers.val.size := Nat.lt_of_not_le h_oob
      have h_meas : numbers.val.size - (start + 1) < k := by rw [← hk]; omega
      have h_csz := count_zeros_from_succ numbers start h_lt
      by_cases hz : numbers.val[start]'h_lt = (0 : u64)
      · -- start is a zero, need one more in (start, size)
        rw [h_csz, if_pos hz] at h_count
        have h_count' : count_zeros_from numbers (start + 1) ≥ 1 := by omega
        obtain ⟨j, hj_lt, hj_le, hj_eq⟩ := one_zero_from numbers (start + 1) h_count'
        exact ⟨start, j, h_lt, hj_lt, Nat.le_refl _, by omega, hz, hj_eq⟩
      · rw [h_csz, if_neg hz] at h_count
        have h_count' : count_zeros_from numbers (start + 1) ≥ 2 := by omega
        obtain ⟨i, j, hi_lt, hj_lt, hi_le, hij, hi_eq, hj_eq⟩ :=
          ih _ h_meas (start + 1) h_count' rfl
        exact ⟨i, j, hi_lt, hj_lt, by omega, hij, hi_eq, hj_eq⟩

private theorem three_zeros_from
    (numbers : RustSlice u64) (start : Nat)
    (h_count : count_zeros_from numbers start ≥ 3) :
    ∃ i j k : Nat,
      ∃ (hi : i < numbers.val.size)
        (hj : j < numbers.val.size)
        (hk : k < numbers.val.size),
      start ≤ i ∧ i < j ∧ j < k ∧
      numbers.val[i]'hi = (0 : u64) ∧
      numbers.val[j]'hj = (0 : u64) ∧
      numbers.val[k]'hk = (0 : u64) := by
  induction hkk : numbers.val.size - start using Nat.strongRecOn generalizing start with
  | _ kk ih =>
    by_cases h_oob : numbers.val.size ≤ start
    · exfalso
      have : count_zeros_from numbers start = 0 :=
        count_zeros_from_oob numbers start (by omega)
      omega
    · have h_lt : start < numbers.val.size := Nat.lt_of_not_le h_oob
      have h_meas : numbers.val.size - (start + 1) < kk := by rw [← hkk]; omega
      have h_csz := count_zeros_from_succ numbers start h_lt
      by_cases hz : numbers.val[start]'h_lt = (0 : u64)
      · rw [h_csz, if_pos hz] at h_count
        have h_count_2 : count_zeros_from numbers (start + 1) ≥ 2 := by omega
        obtain ⟨j, k, hj_lt, hk_lt, hj_le, hjk, hj_eq, hk_eq⟩ :=
          two_zeros_from numbers (start + 1) h_count_2
        exact ⟨start, j, k, h_lt, hj_lt, hk_lt, Nat.le_refl _, by omega, hjk, hz, hj_eq, hk_eq⟩
      · rw [h_csz, if_neg hz] at h_count
        have h_count' : count_zeros_from numbers (start + 1) ≥ 3 := by omega
        obtain ⟨i, j, k, hi_lt, hj_lt, hk_lt, hi_le, hij, hjk, hi_eq, hj_eq, hk_eq⟩ :=
          ih _ h_meas (start + 1) h_count' rfl
        exact ⟨i, j, k, hi_lt, hj_lt, hk_lt, by omega, hij, hjk, hi_eq, hj_eq, hk_eq⟩

/-! ## Reverse bridge: existence of distinct zero indices ⇒ count ≥ k.

Symmetric ladder. The induction goes on the gap `i - start`, walking
`start` up toward the first witness `i` and bounding the count from
below at each step. -/

private theorem count_ge_one_of_zero
    (numbers : RustSlice u64) (start i : Nat) (hi : i < numbers.val.size)
    (h_le : start ≤ i) (h_eq : numbers.val[i]'hi = (0 : u64)) :
    count_zeros_from numbers start ≥ 1 := by
  induction hk : i - start using Nat.strongRecOn generalizing start with
  | _ k ih =>
    have h_lt : start < numbers.val.size := Nat.lt_of_le_of_lt h_le hi
    have h_csz := count_zeros_from_succ numbers start h_lt
    by_cases hs : start = i
    · have h_eq_s : numbers.val[start]'h_lt = (0 : u64) := by subst hs; exact h_eq
      rw [h_csz, if_pos h_eq_s]; omega
    · have h_start_lt_i : start < i := by omega
      have h_meas : i - (start + 1) < k := by rw [← hk]; omega
      have h_ih : count_zeros_from numbers (start + 1) ≥ 1 :=
        ih _ h_meas (start + 1) (by omega) rfl
      rw [h_csz]
      by_cases hz : numbers.val[start]'h_lt = (0 : u64)
      · rw [if_pos hz]; omega
      · rw [if_neg hz]; omega

private theorem count_ge_two_of_two_zeros
    (numbers : RustSlice u64) (start i j : Nat)
    (hi : i < numbers.val.size) (hj : j < numbers.val.size)
    (h_le : start ≤ i) (h_ij : i < j)
    (h_i_eq : numbers.val[i]'hi = (0 : u64))
    (h_j_eq : numbers.val[j]'hj = (0 : u64)) :
    count_zeros_from numbers start ≥ 2 := by
  induction hk : i - start using Nat.strongRecOn generalizing start with
  | _ k ih =>
    have h_lt : start < numbers.val.size := Nat.lt_of_le_of_lt h_le hi
    have h_csz := count_zeros_from_succ numbers start h_lt
    by_cases hs : start = i
    · have h_eq_s : numbers.val[start]'h_lt = (0 : u64) := by
        subst hs; exact h_i_eq
      have h_one_more : count_zeros_from numbers (start + 1) ≥ 1 := by
        apply count_ge_one_of_zero numbers (start + 1) j hj _ h_j_eq
        omega
      rw [h_csz, if_pos h_eq_s]; omega
    · have h_start_lt_i : start < i := by omega
      have h_meas : i - (start + 1) < k := by rw [← hk]; omega
      have h_ih : count_zeros_from numbers (start + 1) ≥ 2 :=
        ih _ h_meas (start + 1) (by omega) rfl
      rw [h_csz]
      by_cases hz : numbers.val[start]'h_lt = (0 : u64)
      · rw [if_pos hz]; omega
      · rw [if_neg hz]; omega

private theorem count_ge_three_of_three_zeros
    (numbers : RustSlice u64) (start i j k : Nat)
    (hi : i < numbers.val.size) (hj : j < numbers.val.size) (hk : k < numbers.val.size)
    (h_le : start ≤ i) (h_ij : i < j) (h_jk : j < k)
    (h_i_eq : numbers.val[i]'hi = (0 : u64))
    (h_j_eq : numbers.val[j]'hj = (0 : u64))
    (h_k_eq : numbers.val[k]'hk = (0 : u64)) :
    count_zeros_from numbers start ≥ 3 := by
  induction hkk : i - start using Nat.strongRecOn generalizing start with
  | _ kk ih =>
    have h_lt : start < numbers.val.size := Nat.lt_of_le_of_lt h_le hi
    have h_csz := count_zeros_from_succ numbers start h_lt
    by_cases hs : start = i
    · have h_eq_s : numbers.val[start]'h_lt = (0 : u64) := by
        subst hs; exact h_i_eq
      have h_more : count_zeros_from numbers (start + 1) ≥ 2 := by
        apply count_ge_two_of_two_zeros numbers (start + 1) j k hj hk _ h_jk
          h_j_eq h_k_eq
        omega
      rw [h_csz, if_pos h_eq_s]; omega
    · have h_start_lt_i : start < i := by omega
      have h_meas : i - (start + 1) < kk := by rw [← hkk]; omega
      have h_ih : count_zeros_from numbers (start + 1) ≥ 3 :=
        ih _ h_meas (start + 1) (by omega) rfl
      rw [h_csz]
      by_cases hz : numbers.val[start]'h_lt = (0 : u64)
      · rw [if_pos hz]; omega
      · rw [if_neg hz]; omega

/-! ## Top-level theorems. -/

/-- Completeness clause: when three distinct positions of `numbers` hold value
    `0`, `triples_sum_to_zero numbers = RustM.ok true`. -/
theorem triples_sum_to_zero_returns_true (numbers : RustSlice u64)
    (h : ∃ i j k : Nat,
           ∃ (hi : i < numbers.val.size)
             (hj : j < numbers.val.size)
             (hk : k < numbers.val.size),
           i < j ∧ j < k
           ∧ numbers.val[i]'hi = (0 : u64)
           ∧ numbers.val[j]'hj = (0 : u64)
           ∧ numbers.val[k]'hk = (0 : u64)) :
    clever_039_triples_sum_to_zero.triples_sum_to_zero numbers = RustM.ok true := by
  unfold clever_039_triples_sum_to_zero.triples_sum_to_zero
  have h_size : numbers.val.size < 2^64 := numbers.size_lt_usizeSize
  have h_zero_toNat_usize : (0 : usize).toNat = 0 := rfl
  have h_zero_toNat_u64 : (0 : u64).toNat = 0 := rfl
  have h_3_toNat_u64 : (3 : u64).toNat = 3 := rfl
  have h_acc : (0 : u64).toNat + (numbers.val.size - (0 : usize).toNat) < 2^64 := by
    rw [h_zero_toNat_u64, h_zero_toNat_usize]; omega
  obtain ⟨v, hv_eq, hv_nat⟩ := count_zeros_at_correct numbers (0 : usize) (0 : u64) h_acc
  rw [hv_eq]
  simp only [RustM_ok_bind]
  obtain ⟨i, j, k, hi, hj, hk, hij, hjk, hi_eq, hj_eq, hk_eq⟩ := h
  have h_count_ge : count_zeros_from numbers 0 ≥ 3 :=
    count_ge_three_of_three_zeros numbers 0 i j k hi hj hk
      (Nat.zero_le _) hij hjk hi_eq hj_eq hk_eq
  have h_v_ge : v.toNat ≥ 3 := by
    rw [hv_nat, h_zero_toNat_u64, h_zero_toNat_usize]; omega
  show (v >=? (3 : u64) : RustM Bool) = RustM.ok true
  show (pure (decide ((3 : u64) ≤ v)) : RustM Bool) = RustM.ok true
  have h_dec : decide ((3 : u64) ≤ v) = true := by
    rw [decide_eq_true_iff, UInt64.le_iff_toNat_le, h_3_toNat_u64]
    exact h_v_ge
  rw [h_dec]; rfl

/-- Soundness clause: when `numbers` contains no three distinct positions
    holding value `0`, `triples_sum_to_zero numbers = RustM.ok false`. -/
theorem triples_sum_to_zero_returns_false (numbers : RustSlice u64)
    (h : ¬ ∃ i j k : Nat,
           ∃ (hi : i < numbers.val.size)
             (hj : j < numbers.val.size)
             (hk : k < numbers.val.size),
           i < j ∧ j < k
           ∧ numbers.val[i]'hi = (0 : u64)
           ∧ numbers.val[j]'hj = (0 : u64)
           ∧ numbers.val[k]'hk = (0 : u64)) :
    clever_039_triples_sum_to_zero.triples_sum_to_zero numbers = RustM.ok false := by
  unfold clever_039_triples_sum_to_zero.triples_sum_to_zero
  have h_size : numbers.val.size < 2^64 := numbers.size_lt_usizeSize
  have h_zero_toNat_usize : (0 : usize).toNat = 0 := rfl
  have h_zero_toNat_u64 : (0 : u64).toNat = 0 := rfl
  have h_3_toNat_u64 : (3 : u64).toNat = 3 := rfl
  have h_acc : (0 : u64).toNat + (numbers.val.size - (0 : usize).toNat) < 2^64 := by
    rw [h_zero_toNat_u64, h_zero_toNat_usize]; omega
  obtain ⟨v, hv_eq, hv_nat⟩ := count_zeros_at_correct numbers (0 : usize) (0 : u64) h_acc
  rw [hv_eq]
  simp only [RustM_ok_bind]
  have h_count_lt : count_zeros_from numbers 0 < 3 := by
    rcases Nat.lt_or_ge (count_zeros_from numbers 0) 3 with h_lt | h_geq
    · exact h_lt
    · exfalso
      apply h
      obtain ⟨i, j, k, hi, hj, hk, _, hij, hjk, hi_eq, hj_eq, hk_eq⟩ :=
        three_zeros_from numbers 0 h_geq
      exact ⟨i, j, k, hi, hj, hk, hij, hjk, hi_eq, hj_eq, hk_eq⟩
  have h_v_lt : v.toNat < 3 := by
    rw [hv_nat, h_zero_toNat_u64, h_zero_toNat_usize]; omega
  show (v >=? (3 : u64) : RustM Bool) = RustM.ok false
  show (pure (decide ((3 : u64) ≤ v)) : RustM Bool) = RustM.ok false
  have h_dec : decide ((3 : u64) ≤ v) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [UInt64.le_iff_toNat_le, h_3_toNat_u64] at hle
    omega
  rw [h_dec]; rfl

end Clever_039_triples_sum_to_zeroObligations
