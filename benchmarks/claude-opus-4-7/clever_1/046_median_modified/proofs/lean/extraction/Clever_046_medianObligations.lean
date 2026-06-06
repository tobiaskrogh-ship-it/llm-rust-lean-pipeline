-- Companion obligations file for the `clever_046_median` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_046_median

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_046_medianObligations

/-! ## Specification oracles: counts of strictly less / strictly greater
    elements in a slice prefix.

`lt_count l m k` is the number of indices `j < k` for which `l.val[j] < m`,
expressed at the `Nat` level. Each top-level theorem applies it with
`k = l.val.size`, so the bounded indices always exist. The `gt_count`
oracle is the symmetric construction for `l.val[j] > m`. -/

private def lt_count (l : RustSlice i64) (m : i64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      if h : k < l.val.size then
        (if (l.val[k]'h) < m then 1 else 0) + lt_count l m k
      else lt_count l m k

private def gt_count (l : RustSlice i64) (m : i64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      if h : k < l.val.size then
        (if (l.val[k]'h) > m then 1 else 0) + gt_count l m k
      else gt_count l m k

/-! ## Standard scaffolding (transferred from `clever_039` reference). -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl
private theorem u64_zero_toNat : (0 : u64).toNat = 0 := rfl
private theorem u64_one_toNat : (1 : u64).toNat = 1 := rfl
private theorem u64_two_toNat : (2 : u64).toNat = 2 := rfl

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

private theorem u64_add_one_toNat (a : u64) (h : a.toNat + 1 < 2^64) :
    (a + 1).toNat = a.toNat + 1 := by
  have h_pre : a.toNat + (1 : u64).toNat < 2^64 := by
    rw [u64_one_toNat]; exact h
  rw [UInt64.toNat_add_of_lt h_pre, u64_one_toNat]

/-! ## Step lemmas for `count_strictly_less`. -/

/-- Out-of-bounds step: when `i.toNat ≥ l.val.size`, the function returns
    `RustM.ok 0`. -/
private theorem csl_oob (l : RustSlice i64) (m : i64) (i : usize)
    (hi : l.val.size ≤ i.toNat) :
    clever_046_median.count_strictly_less l m i = RustM.ok (0 : u64) := by
  conv => lhs; unfold clever_046_median.count_strictly_less
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

/-- Match step: when `i.toNat < l.val.size` and `l[i] < m`, the function
    delegates to `1 + count_strictly_less l m (i+1)`. -/
private theorem csl_match (l : RustSlice i64) (m : i64) (i : usize)
    (hi : i.toNat < l.val.size)
    (hlt : (l.val[i.toNat]'hi) < m) :
    clever_046_median.count_strictly_less l m i =
      clever_046_median.count_strictly_less l m (i + 1) >>= fun r =>
        ((1 : u64) +? r) := by
  conv => lhs; unfold clever_046_median.count_strictly_less
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
  have h_lt_cond : decide ((l.val[i.toNat]'hi) < m) = true := by
    rw [decide_eq_true_iff]; exact hlt
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
             rust_primitives.cmp.lt, h_lt_cond,
             rust_primitives.ops.arith.Add.add, h_no_bv_i]

/-- Non-match step: when `i.toNat < l.val.size` and `¬ (l[i] < m)`, the
    function delegates to `count_strictly_less l m (i+1)`. -/
private theorem csl_norm (l : RustSlice i64) (m : i64) (i : usize)
    (hi : i.toNat < l.val.size)
    (hnlt : ¬ ((l.val[i.toNat]'hi) < m)) :
    clever_046_median.count_strictly_less l m i =
      clever_046_median.count_strictly_less l m (i + 1) := by
  conv => lhs; unfold clever_046_median.count_strictly_less
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
  have h_lt_cond : decide ((l.val[i.toNat]'hi) < m) = false := by
    rw [decide_eq_false_iff_not]; exact hnlt
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
             rust_primitives.cmp.lt, h_lt_cond,
             rust_primitives.ops.arith.Add.add, h_no_bv_i]

/-! ## Nat-level forward-count oracles for the recursive counters.

`lt_count_from l m i` counts indices `j ∈ [i, l.val.size)` with `l[j] < m`.
This matches the operational behaviour of `count_strictly_less l m i`. The
final theorems will bridge it back to `lt_count l m size = lt_count_from l m 0`. -/

private def lt_count_from (l : RustSlice i64) (m : i64) (i : Nat) : Nat :=
  if h : i < l.val.size then
    (if (l.val[i]'h) < m then 1 else 0) + lt_count_from l m (i + 1)
  else 0
termination_by l.val.size - i

private def gt_count_from (l : RustSlice i64) (m : i64) (i : Nat) : Nat :=
  if h : i < l.val.size then
    (if (l.val[i]'h) > m then 1 else 0) + gt_count_from l m (i + 1)
  else 0
termination_by l.val.size - i

private theorem lt_count_from_oob (l : RustSlice i64) (m : i64) (i : Nat)
    (h : ¬ i < l.val.size) :
    lt_count_from l m i = 0 := by
  unfold lt_count_from; rw [dif_neg h]

private theorem lt_count_from_succ (l : RustSlice i64) (m : i64) (i : Nat)
    (h : i < l.val.size) :
    lt_count_from l m i =
      (if (l.val[i]'h) < m then 1 else 0) + lt_count_from l m (i + 1) := by
  conv => lhs; unfold lt_count_from
  rw [dif_pos h]

private theorem gt_count_from_oob (l : RustSlice i64) (m : i64) (i : Nat)
    (h : ¬ i < l.val.size) :
    gt_count_from l m i = 0 := by
  unfold gt_count_from; rw [dif_neg h]

private theorem gt_count_from_succ (l : RustSlice i64) (m : i64) (i : Nat)
    (h : i < l.val.size) :
    gt_count_from l m i =
      (if (l.val[i]'h) > m then 1 else 0) + gt_count_from l m (i + 1) := by
  conv => lhs; unfold gt_count_from
  rw [dif_pos h]

private theorem lt_count_from_le (l : RustSlice i64) (m : i64) (i : Nat) :
    lt_count_from l m i ≤ l.val.size - i := by
  induction hk : (l.val.size - i) using Nat.strongRecOn generalizing i with
  | _ k ih =>
    by_cases h : i < l.val.size
    · rw [lt_count_from_succ l m i h]
      have h_meas : l.val.size - (i + 1) < k := by rw [← hk]; omega
      have h_ih := ih (l.val.size - (i + 1)) h_meas (i + 1) rfl
      by_cases hz : (l.val[i]'h) < m
      · rw [if_pos hz]; omega
      · rw [if_neg hz]; omega
    · rw [lt_count_from_oob l m i h]; omega

private theorem gt_count_from_le (l : RustSlice i64) (m : i64) (i : Nat) :
    gt_count_from l m i ≤ l.val.size - i := by
  induction hk : (l.val.size - i) using Nat.strongRecOn generalizing i with
  | _ k ih =>
    by_cases h : i < l.val.size
    · rw [gt_count_from_succ l m i h]
      have h_meas : l.val.size - (i + 1) < k := by rw [← hk]; omega
      have h_ih := ih (l.val.size - (i + 1)) h_meas (i + 1) rfl
      by_cases hz : (l.val[i]'h) > m
      · rw [if_pos hz]; omega
      · rw [if_neg hz]; omega
    · rw [gt_count_from_oob l m i h]; omega

/-! ## Bridge from the obligations' `lt_count`/`gt_count` (counts up to k)
    to the forward-count oracles (counts from i forward).

`lt_count l m l.val.size = lt_count_from l m 0`. -/

private theorem lt_count_eq_sub (l : RustSlice i64) (m : i64) (i : Nat)
    (hi : i ≤ l.val.size) :
    lt_count_from l m i = lt_count l m l.val.size - lt_count l m i := by
  -- We prove the stronger version: lt_count l m size = lt_count l m i + lt_count_from l m i
  suffices h : lt_count l m l.val.size = lt_count l m i + lt_count_from l m i by omega
  induction hk : (l.val.size - i) using Nat.strongRecOn generalizing i with
  | _ k ih =>
    by_cases h : i < l.val.size
    · have h_meas : l.val.size - (i + 1) < k := by rw [← hk]; omega
      have h_ih := ih (l.val.size - (i + 1)) h_meas (i + 1) (by omega) rfl
      rw [h_ih]
      rw [lt_count_from_succ l m i h]
      -- lt_count_from l m i = (if l[i]<m then 1 else 0) + lt_count_from l m (i+1)
      -- lt_count l m (i+1) = ... + lt_count l m i
      have h_lt_count_succ : lt_count l m (i + 1) =
          (if (l.val[i]'h) < m then 1 else 0) + lt_count l m i := by
        show (if h' : i < l.val.size then
               (if (l.val[i]'h') < m then 1 else 0) + lt_count l m i
             else lt_count l m i) = _
        rw [dif_pos h]
      omega
    · have hi_eq : i = l.val.size := by omega
      rw [hi_eq]
      rw [lt_count_from_oob l m l.val.size (by omega)]

private theorem gt_count_eq_sub (l : RustSlice i64) (m : i64) (i : Nat)
    (hi : i ≤ l.val.size) :
    gt_count_from l m i = gt_count l m l.val.size - gt_count l m i := by
  suffices h : gt_count l m l.val.size = gt_count l m i + gt_count_from l m i by omega
  induction hk : (l.val.size - i) using Nat.strongRecOn generalizing i with
  | _ k ih =>
    by_cases h : i < l.val.size
    · have h_meas : l.val.size - (i + 1) < k := by rw [← hk]; omega
      have h_ih := ih (l.val.size - (i + 1)) h_meas (i + 1) (by omega) rfl
      rw [h_ih]
      rw [gt_count_from_succ l m i h]
      have h_gt_count_succ : gt_count l m (i + 1) =
          (if (l.val[i]'h) > m then 1 else 0) + gt_count l m i := by
        show (if h' : i < l.val.size then
               (if (l.val[i]'h') > m then 1 else 0) + gt_count l m i
             else gt_count l m i) = _
        rw [dif_pos h]
      omega
    · have hi_eq : i = l.val.size := by omega
      rw [hi_eq]
      rw [gt_count_from_oob l m l.val.size (by omega)]

/-! ## Workhorse: `count_strictly_less` and `count_strictly_greater` agree
    with the Nat-level oracles. -/

private theorem csl_correct (l : RustSlice i64) (m : i64) (i : usize)
    (hi : i.toNat ≤ l.val.size) :
    ∃ v : u64,
      clever_046_median.count_strictly_less l m i = RustM.ok v ∧
      v.toNat = lt_count_from l m i.toNat := by
  induction hk : (l.val.size - i.toNat) using Nat.strongRecOn generalizing i with
  | _ k ih =>
    by_cases h_oob : l.val.size ≤ i.toNat
    · have h_oob_eq : i.toNat = l.val.size := by omega
      have h_eq := csl_oob l m i h_oob
      have h_lcf_zero : lt_count_from l m i.toNat = 0 := by
        rw [h_oob_eq]; exact lt_count_from_oob l m l.val.size (by omega)
      refine ⟨0, h_eq, ?_⟩
      rw [h_lcf_zero]; rfl
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le h_oob
      have h_size : l.val.size < 2^64 := l.size_lt_usizeSize
      have h_no_overflow_i : i.toNat + 1 < 2^64 := by omega
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 :=
        usize_add_one_toNat i h_no_overflow_i
      have h_count_le : lt_count_from l m (i.toNat + 1) ≤ l.val.size - (i.toNat + 1) :=
        lt_count_from_le l m (i.toNat + 1)
      have h_measure : l.val.size - (i + 1).toNat < k := by rw [h_i1_toNat]; omega
      have h_lcf_succ := lt_count_from_succ l m i.toNat hi_lt
      obtain ⟨v', hv'_eq, hv'_nat⟩ :=
        ih (l.val.size - (i + 1).toNat) h_measure (i + 1) (by rw [h_i1_toNat]; omega) rfl
      rw [h_i1_toNat] at hv'_nat
      by_cases hlt : (l.val[i.toNat]'hi_lt) < m
      · -- match branch
        have h_step := csl_match l m i hi_lt hlt
        have h_one_v' : v'.toNat + 1 < 2^64 := by rw [hv'_nat]; omega
        have h_no_bv_acc :
            BitVec.uaddOverflow ((1 : u64).toBitVec) v'.toBitVec = false := by
          generalize hbo : BitVec.uaddOverflow ((1 : u64).toBitVec) v'.toBitVec = bo
          cases bo with
          | false => rfl
          | true =>
            exfalso
            have hov : UInt64.addOverflow 1 v' := hbo
            rw [UInt64.addOverflow_iff] at hov
            rw [u64_one_toNat] at hov
            omega
        have h_add_eq : ((1 : u64) +? v' : RustM u64) = RustM.ok ((1 : u64) + v') := by
          show (if BitVec.uaddOverflow (1 : u64).toBitVec v'.toBitVec then
                  (.fail .integerOverflow : RustM u64)
                else pure ((1 : u64) + v')) = _
          rw [h_no_bv_acc]; rfl
        refine ⟨(1 : u64) + v', ?_, ?_⟩
        · rw [h_step, hv'_eq, RustM_ok_bind, h_add_eq]
        · rw [UInt64.toNat_add_of_lt (by rw [u64_one_toNat]; omega)]
          rw [u64_one_toNat, hv'_nat]
          rw [h_lcf_succ, if_pos hlt]
      · -- non-match branch
        have h_step := csl_norm l m i hi_lt hlt
        refine ⟨v', ?_, ?_⟩
        · rw [h_step, hv'_eq]
        · rw [hv'_nat, h_lcf_succ, if_neg hlt]; omega


private theorem csg_oob (l : RustSlice i64) (m : i64) (i : usize)
    (hi : l.val.size ≤ i.toNat) :
    clever_046_median.count_strictly_greater l m i = RustM.ok (0 : u64) := by
  conv => lhs; unfold clever_046_median.count_strictly_greater
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

private theorem csg_match (l : RustSlice i64) (m : i64) (i : usize)
    (hi : i.toNat < l.val.size)
    (hgt : (l.val[i.toNat]'hi) > m) :
    clever_046_median.count_strictly_greater l m i =
      clever_046_median.count_strictly_greater l m (i + 1) >>= fun r =>
        ((1 : u64) +? r) := by
  conv => lhs; unfold clever_046_median.count_strictly_greater
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
  have h_gt_cond : decide ((l.val[i.toNat]'hi) > m) = true := by
    rw [decide_eq_true_iff]; exact hgt
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
             rust_primitives.cmp.gt, h_gt_cond,
             rust_primitives.ops.arith.Add.add, h_no_bv_i]

private theorem csg_norm (l : RustSlice i64) (m : i64) (i : usize)
    (hi : i.toNat < l.val.size)
    (hngt : ¬ ((l.val[i.toNat]'hi) > m)) :
    clever_046_median.count_strictly_greater l m i =
      clever_046_median.count_strictly_greater l m (i + 1) := by
  conv => lhs; unfold clever_046_median.count_strictly_greater
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
  have h_gt_cond : decide ((l.val[i.toNat]'hi) > m) = false := by
    rw [decide_eq_false_iff_not]; exact hngt
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
             rust_primitives.cmp.gt, h_gt_cond,
             rust_primitives.ops.arith.Add.add, h_no_bv_i]

private theorem csg_correct (l : RustSlice i64) (m : i64) (i : usize)
    (hi : i.toNat ≤ l.val.size) :
    ∃ v : u64,
      clever_046_median.count_strictly_greater l m i = RustM.ok v ∧
      v.toNat = gt_count_from l m i.toNat := by
  induction hk : (l.val.size - i.toNat) using Nat.strongRecOn generalizing i with
  | _ k ih =>
    by_cases h_oob : l.val.size ≤ i.toNat
    · have h_oob_eq : i.toNat = l.val.size := by omega
      have h_eq := csg_oob l m i h_oob
      have h_gcf_zero : gt_count_from l m i.toNat = 0 := by
        rw [h_oob_eq]; exact gt_count_from_oob l m l.val.size (by omega)
      refine ⟨0, h_eq, ?_⟩
      rw [h_gcf_zero]; rfl
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le h_oob
      have h_size : l.val.size < 2^64 := l.size_lt_usizeSize
      have h_no_overflow_i : i.toNat + 1 < 2^64 := by omega
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 :=
        usize_add_one_toNat i h_no_overflow_i
      have h_count_le : gt_count_from l m (i.toNat + 1) ≤ l.val.size - (i.toNat + 1) :=
        gt_count_from_le l m (i.toNat + 1)
      have h_measure : l.val.size - (i + 1).toNat < k := by rw [h_i1_toNat]; omega
      have h_gcf_succ := gt_count_from_succ l m i.toNat hi_lt
      obtain ⟨v', hv'_eq, hv'_nat⟩ :=
        ih (l.val.size - (i + 1).toNat) h_measure (i + 1) (by rw [h_i1_toNat]; omega) rfl
      rw [h_i1_toNat] at hv'_nat
      by_cases hgt : (l.val[i.toNat]'hi_lt) > m
      · have h_step := csg_match l m i hi_lt hgt
        have h_one_v' : v'.toNat + 1 < 2^64 := by rw [hv'_nat]; omega
        have h_no_bv_acc :
            BitVec.uaddOverflow ((1 : u64).toBitVec) v'.toBitVec = false := by
          generalize hbo : BitVec.uaddOverflow ((1 : u64).toBitVec) v'.toBitVec = bo
          cases bo with
          | false => rfl
          | true =>
            exfalso
            have hov : UInt64.addOverflow 1 v' := hbo
            rw [UInt64.addOverflow_iff] at hov
            rw [u64_one_toNat] at hov
            omega
        have h_add_eq : ((1 : u64) +? v' : RustM u64) = RustM.ok ((1 : u64) + v') := by
          show (if BitVec.uaddOverflow (1 : u64).toBitVec v'.toBitVec then
                  (.fail .integerOverflow : RustM u64)
                else pure ((1 : u64) + v')) = _
          rw [h_no_bv_acc]; rfl
        refine ⟨(1 : u64) + v', ?_, ?_⟩
        · rw [h_step, hv'_eq, RustM_ok_bind, h_add_eq]
        · rw [UInt64.toNat_add_of_lt (by rw [u64_one_toNat]; omega)]
          rw [u64_one_toNat, hv'_nat]
          rw [h_gcf_succ, if_pos hgt]
      · have h_step := csg_norm l m i hi_lt hgt
        refine ⟨v', ?_, ?_⟩
        · rw [h_step, hv'_eq]
        · rw [hv'_nat, h_gcf_succ, if_neg hgt]; omega

/-! ## Bridge to List-based counts and sort-based existence of a median.

The recursive Nat-level oracles `lt_count_from`/`gt_count_from` agree with
`List.countP` applied to the slice's underlying list. Combined with
`List.mergeSort`'s permutation + pairwise lemmas, this gives an existence
witness for a value in `l` satisfying the lower-median count predicate. -/

private theorem lt_count_from_eq_drop_countP
    (l : RustSlice i64) (m : i64) (i : Nat) (hi : i ≤ l.val.size) :
    lt_count_from l m i = (l.val.toList.drop i).countP (fun x => decide (x < m)) := by
  induction hk : (l.val.size - i) using Nat.strongRecOn generalizing i with
  | _ k ih =>
    by_cases h : i < l.val.size
    · rw [lt_count_from_succ l m i h]
      have h_meas : l.val.size - (i + 1) < k := by rw [← hk]; omega
      have h_ih := ih (l.val.size - (i + 1)) h_meas (i + 1) (by omega) rfl
      rw [h_ih]
      have h_lt_len : i < l.val.toList.length := by
        rw [Array.length_toList]; exact h
      have h_drop : l.val.toList.drop i =
          (l.val.toList[i]'h_lt_len) :: l.val.toList.drop (i + 1) :=
        List.drop_eq_getElem_cons h_lt_len
      have h_get_eq : l.val.toList[i]'h_lt_len = l.val[i]'h := by
        exact Array.getElem_toList _
      rw [h_drop, h_get_eq]
      rw [List.countP_cons]
      by_cases hz : (l.val[i]'h) < m
      · rw [if_pos hz]
        rw [if_pos (by simp [hz] : decide ((l.val[i]'h) < m) = true)]
        omega
      · rw [if_neg hz]
        rw [if_neg (by simp [hz] : ¬ decide ((l.val[i]'h) < m) = true)]
        omega
    · rw [lt_count_from_oob l m i h]
      have h_eq : i = l.val.size := by omega
      have h_drop_eq : l.val.toList.drop i = [] := by
        rw [h_eq]
        apply List.drop_eq_nil_of_le
        rw [Array.length_toList]; exact Nat.le_refl _
      rw [h_drop_eq]; rfl

private theorem gt_count_from_eq_drop_countP
    (l : RustSlice i64) (m : i64) (i : Nat) (hi : i ≤ l.val.size) :
    gt_count_from l m i = (l.val.toList.drop i).countP (fun x => decide (x > m)) := by
  induction hk : (l.val.size - i) using Nat.strongRecOn generalizing i with
  | _ k ih =>
    by_cases h : i < l.val.size
    · rw [gt_count_from_succ l m i h]
      have h_meas : l.val.size - (i + 1) < k := by rw [← hk]; omega
      have h_ih := ih (l.val.size - (i + 1)) h_meas (i + 1) (by omega) rfl
      rw [h_ih]
      have h_lt_len : i < l.val.toList.length := by
        rw [Array.length_toList]; exact h
      have h_drop : l.val.toList.drop i =
          (l.val.toList[i]'h_lt_len) :: l.val.toList.drop (i + 1) :=
        List.drop_eq_getElem_cons h_lt_len
      have h_get_eq : l.val.toList[i]'h_lt_len = l.val[i]'h := by
        exact Array.getElem_toList _
      rw [h_drop, h_get_eq]
      rw [List.countP_cons]
      by_cases hz : (l.val[i]'h) > m
      · rw [if_pos hz]
        rw [if_pos (by simp [hz] : decide ((l.val[i]'h) > m) = true)]
        omega
      · rw [if_neg hz]
        rw [if_neg (by simp [hz] : ¬ decide ((l.val[i]'h) > m) = true)]
        omega
    · rw [gt_count_from_oob l m i h]
      have h_eq : i = l.val.size := by omega
      have h_drop_eq : l.val.toList.drop i = [] := by
        rw [h_eq]
        apply List.drop_eq_nil_of_le
        rw [Array.length_toList]; exact Nat.le_refl _
      rw [h_drop_eq]; rfl

private theorem lt_count_from_zero_eq_countP (l : RustSlice i64) (m : i64) :
    lt_count_from l m 0 = l.val.toList.countP (fun x => decide (x < m)) := by
  have h := lt_count_from_eq_drop_countP l m 0 (Nat.zero_le _)
  rw [List.drop_zero] at h; exact h

private theorem gt_count_from_zero_eq_countP (l : RustSlice i64) (m : i64) :
    gt_count_from l m 0 = l.val.toList.countP (fun x => decide (x > m)) := by
  have h := gt_count_from_eq_drop_countP l m 0 (Nat.zero_le _)
  rw [List.drop_zero] at h; exact h

/-- Bound on `countP (· < m) sorted` when `m = sorted[half]` for a sorted list.
    The median value is abstracted to a fresh variable `m` to avoid dependent
    rewrite issues with `s[half]'h_half`. -/
private theorem countP_lt_le_half_of_sorted
    (s : List i64) (m : i64) (half : Nat) (h_half : half < s.length)
    (h_sorted : s.Pairwise (· ≤ ·))
    (h_m_eq : s[half]'h_half = m) :
    s.countP (fun x => decide (x < m)) ≤ half := by
  rw [List.countP_eq_length_filter]
  have h_split : s = s.take half ++ s.drop half := by
    rw [List.take_append_drop]
  conv => lhs; rw [h_split]
  rw [List.filter_append, List.length_append]
  have h_take_len : (s.take half).length ≤ half := by
    rw [List.length_take]; omega
  have h_filter_take_len :
      ((s.take half).filter (fun x => decide (x < m))).length ≤ (s.take half).length :=
    List.length_filter_le _ _
  have h_filter_drop_nil : (s.drop half).filter (fun x => decide (x < m)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    rw [List.mem_iff_getElem] at hx
    obtain ⟨j, hj_lt, hj_eq⟩ := hx
    have hj_lt_len : (s.drop half).length = s.length - half := by
      rw [List.length_drop]
    rw [hj_lt_len] at hj_lt
    have h_idx_lt : half + j < s.length := by omega
    have h_eq_get : x = s[half + j]'h_idx_lt := by
      rw [← hj_eq]; rw [List.getElem_drop]
    intro h_dec
    rw [decide_eq_true_iff] at h_dec
    rw [h_eq_get] at h_dec
    rw [← h_m_eq] at h_dec
    by_cases h_j_zero : j = 0
    · -- j = 0 ⇒ x = s[half + 0] = s[half], so h_dec : s[half] < s[half], contradiction.
      subst h_j_zero
      -- Use the pairwise on (half, half + 0 = half) → reflexive comparison
      -- Direct: ¬ s[half + 0]'h_idx_lt < s[half]'h_half.
      -- These two indices are equal as Nat (= half), so the elements are equal
      -- by getElem_congr_idx + proof irrelevance.
      have h_idx_eq : half + 0 = half := Nat.add_zero _
      have h_get_eq : s[half + 0]'h_idx_lt = s[half]'h_half := by
        congr 1
      rw [h_get_eq] at h_dec
      exact Int64.lt_irrefl h_dec
    · have h_half_lt' : half < half + j := by omega
      have h_pw : s[half]'h_half ≤ s[half + j]'h_idx_lt :=
        List.pairwise_iff_getElem.mp h_sorted half (half + j) h_half h_idx_lt h_half_lt'
      exact absurd (Int64.lt_of_lt_of_le h_dec h_pw) Int64.lt_irrefl
  rw [h_filter_drop_nil, List.length_nil, Nat.add_zero]
  exact Nat.le_trans h_filter_take_len h_take_len

/-- Symmetric bound for `countP (· > m)`. -/
private theorem countP_gt_le_of_sorted
    (s : List i64) (m : i64) (half : Nat) (h_half : half < s.length)
    (h_sorted : s.Pairwise (· ≤ ·))
    (h_m_eq : s[half]'h_half = m) :
    s.countP (fun x => decide (x > m)) ≤ s.length - 1 - half := by
  rw [List.countP_eq_length_filter]
  have h_split : s = s.take (half + 1) ++ s.drop (half + 1) := by
    rw [List.take_append_drop]
  conv => lhs; rw [h_split]
  rw [List.filter_append, List.length_append]
  have h_drop_len : (s.drop (half + 1)).length = s.length - (half + 1) := by
    rw [List.length_drop]
  have h_filter_drop_le :
      ((s.drop (half + 1)).filter (fun x => decide (x > m))).length ≤
        (s.drop (half + 1)).length :=
    List.length_filter_le _ _
  have h_filter_take_nil :
      (s.take (half + 1)).filter (fun x => decide (x > m)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    rw [List.mem_iff_getElem] at hx
    obtain ⟨j, hj_lt, hj_eq⟩ := hx
    have hj_take_len : (s.take (half + 1)).length = min (half + 1) s.length := by
      rw [List.length_take]
    rw [hj_take_len] at hj_lt
    have hj_lt' : j ≤ half := by
      have : j < half + 1 := by omega
      omega
    have h_j_lt_s : j < s.length := by omega
    have h_eq_get : x = s[j]'h_j_lt_s := by
      rw [← hj_eq]; rw [List.getElem_take]
    intro h_dec
    rw [decide_eq_true_iff] at h_dec
    rw [h_eq_get] at h_dec
    rw [← h_m_eq] at h_dec
    by_cases h_j_eq : j = half
    · subst h_j_eq
      exact Int64.lt_irrefl h_dec
    · have h_j_lt_half : j < half := by omega
      have h_pw : s[j]'h_j_lt_s ≤ s[half]'h_half :=
        List.pairwise_iff_getElem.mp h_sorted j half h_j_lt_s h_half h_j_lt_half
      exact absurd (Int64.lt_of_lt_of_le h_dec h_pw) Int64.lt_irrefl
  rw [h_filter_take_nil, List.length_nil, Nat.zero_add]
  rw [h_drop_len] at h_filter_drop_le
  have h_eq : s.length - (half + 1) = s.length - 1 - half := by omega
  rw [← h_eq]
  exact h_filter_drop_le

/-- Existence of a witness for the lower-median predicate via `mergeSort`. -/
private theorem exists_median_witness
    (l : RustSlice i64) (h_size : 0 < l.val.size) :
    ∃ m : i64, ∃ k : Nat, ∃ (hk : k < l.val.size),
      l.val[k]'hk = m ∧
      lt_count_from l m 0 ≤ (l.val.size - 1) / 2 ∧
      gt_count_from l m 0 + 1 + (l.val.size - 1) / 2 ≤ l.val.size := by
  -- Bool-valued comparator for mergeSort.
  have h_trans : ∀ a b c : i64, decide (a ≤ b) = true → decide (b ≤ c) = true →
      decide (a ≤ c) = true := by
    intro a b c h1 h2
    rw [decide_eq_true_iff] at h1 h2 ⊢
    exact Int64.le_trans h1 h2
  have h_total : ∀ a b : i64, (decide (a ≤ b) || decide (b ≤ a)) = true := by
    intro a b
    rcases Int64.le_total a b with h | h
    · simp [h]
    · simp [h]
  let s := l.val.toList.mergeSort (fun a b : i64 => decide (a ≤ b))
  have h_perm : List.Perm s l.val.toList := List.mergeSort_perm _ _
  have h_len : s.length = l.val.size := by
    show (l.val.toList.mergeSort (fun a b : i64 => decide (a ≤ b))).length = l.val.size
    rw [List.length_mergeSort, Array.length_toList]
  have h_pw_bool : s.Pairwise (fun a b : i64 => decide (a ≤ b) = true) :=
    List.pairwise_mergeSort h_trans h_total _
  have h_pw : s.Pairwise (· ≤ ·) := by
    apply List.Pairwise.imp _ h_pw_bool
    intro a b h
    rw [decide_eq_true_iff] at h; exact h
  let half := (l.val.size - 1) / 2
  have h_half_lt : half < s.length := by
    show (l.val.size - 1) / 2 < s.length
    rw [h_len]; omega
  let m := s[half]'h_half_lt
  have h_m_mem : m ∈ l.val.toList := by
    have h_m_in_s : m ∈ s := List.getElem_mem _
    exact h_perm.mem_iff.mp h_m_in_s
  rw [List.mem_iff_getElem] at h_m_mem
  obtain ⟨k, hk_lt_len, hk_eq⟩ := h_m_mem
  have hk_lt_size : k < l.val.size := by
    rw [← Array.length_toList]; exact hk_lt_len
  have h_m_eq : s[half]'h_half_lt = m := rfl
  refine ⟨m, k, hk_lt_size, ?_, ?_, ?_⟩
  · have h_get_eq : l.val.toList[k]'hk_lt_len = l.val[k]'hk_lt_size :=
      Array.getElem_toList _
    rw [← h_get_eq]; exact hk_eq
  · rw [lt_count_from_zero_eq_countP]
    have h_perm_countP :
        l.val.toList.countP (fun x => decide (x < m)) =
          s.countP (fun x => decide (x < m)) :=
      (h_perm.countP_eq _).symm
    rw [h_perm_countP]
    exact countP_lt_le_half_of_sorted s m half h_half_lt h_pw h_m_eq
  · rw [gt_count_from_zero_eq_countP]
    have h_perm_countP :
        l.val.toList.countP (fun x => decide (x > m)) =
          s.countP (fun x => decide (x > m)) :=
      (h_perm.countP_eq _).symm
    rw [h_perm_countP]
    have h_bd := countP_gt_le_of_sorted s m half h_half_lt h_pw h_m_eq
    rw [h_len] at h_bd
    omega

/-! ## Step lemmas for `find_median_at`. -/

/-- The median predicate at the Nat level: there are at most half indices
    strictly less than `m`, and the symmetric upper-bound on indices
    strictly greater. -/
private def median_pred (l : RustSlice i64) (m : i64) : Prop :=
  lt_count_from l m 0 ≤ (l.val.size - 1) / 2 ∧
  gt_count_from l m 0 + 1 + (l.val.size - 1) / 2 ≤ l.val.size

/-- When `0 < l.val.size` and `i.toNat ≥ l.val.size`, the function takes
    the `i >= len` branch and returns `RustM.ok 0`. -/
private theorem fma_oob_nonempty
    (l : RustSlice i64) (h_size_pos : 0 < l.val.size) (i : usize)
    (hi : l.val.size ≤ i.toNat) :
    clever_046_median.find_median_at l i = RustM.ok (0 : i64) := by
  conv => lhs; unfold clever_046_median.find_median_at
  have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_n_toNat : ((USize64.ofNat l.val.size).toUInt64).toNat = l.val.size := by
    show ((USize64.ofNat l.val.size).toNat).toUInt64.toNat = l.val.size
    rw [h_ofNat]
    show l.val.size % UInt64.size = l.val.size
    exact Nat.mod_eq_of_lt h_size_lt
  have h_n_eq_0_cond : ((USize64.ofNat l.val.size).toUInt64 == (0 : u64)) = false := by
    rw [beq_eq_false_iff_ne]
    intro h_eq
    have : ((USize64.ofNat l.val.size).toUInt64).toNat = (0 : u64).toNat :=
      congrArg UInt64.toNat h_eq
    rw [h_n_toNat, u64_zero_toNat] at this
    omega
  have h_i_ge_cond : decide (USize64.ofNat l.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.hax.cast_op, Cast.cast,
             rust_primitives.cmp.eq, rust_primitives.cmp.ge,
             pure_bind,
             h_n_eq_0_cond, Bool.false_eq_true, ↓reduceIte,
             h_i_ge_cond]
  rfl

/-- Step lemma: in the in-bounds case, find_median_at either matches at i with
    the predicate holding, or recurses to (i+1) with the predicate failing.
    Derived from `find_median_at l i = RustM.ok m` (so all u64 arithmetic in
    the iteration must have succeeded). -/
private theorem fma_step
    (l : RustSlice i64) (h_size_pos : 0 < l.val.size) (i : usize)
    (hi_lt : i.toNat < l.val.size) (m : i64)
    (hres : clever_046_median.find_median_at l i = RustM.ok m) :
    (m = l.val[i.toNat]'hi_lt ∧ median_pred l (l.val[i.toNat]'hi_lt)) ∨
    (clever_046_median.find_median_at l (i + 1) = RustM.ok m ∧
     ¬ median_pred l (l.val[i.toNat]'hi_lt)) := by
  have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
  -- Bind csl/csg result.
  obtain ⟨lt_v, h_lt_eq, h_lt_nat⟩ :=
    csl_correct l (l.val[i.toNat]'hi_lt) (0 : usize) (Nat.zero_le _)
  obtain ⟨gt_v, h_gt_eq, h_gt_nat⟩ :=
    csg_correct l (l.val[i.toNat]'hi_lt) (0 : usize) (Nat.zero_le _)
  have h_zero_toNat : ((0 : usize).toNat : Nat) = 0 := rfl
  rw [h_zero_toNat] at h_lt_nat h_gt_nat
  -- Compute n.toNat = size and (n-1)/2.toNat = (size-1)/2 at u64
  have h_n_ofNat_toNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_n_toNat : ((USize64.ofNat l.val.size).toUInt64).toNat = l.val.size := by
    show ((USize64.ofNat l.val.size).toNat).toUInt64.toNat = l.val.size
    rw [h_n_ofNat_toNat]
    exact Nat.mod_eq_of_lt h_size_lt
  -- gt_v upper bound: just ≤ size; overflow on gt+1 (if any) is handled
  -- by case-analysis below using hres : ok m.
  have h_gt_bound : gt_v.toNat ≤ l.val.size := by
    rw [h_gt_nat]
    have := gt_count_from_le l (l.val[i.toNat]'hi_lt) 0
    omega
  -- Unfold find_median_at
  conv at hres => lhs; unfold clever_046_median.find_median_at
  -- Step-by-step reductions
  have h_n_eq_0_cond :
      ((USize64.ofNat l.val.size).toUInt64 == (0 : u64)) = false := by
    rw [beq_eq_false_iff_ne]
    intro h_eq
    have : ((USize64.ofNat l.val.size).toUInt64).toNat = (0 : u64).toNat :=
      congrArg UInt64.toNat h_eq
    rw [h_n_toNat, u64_zero_toNat] at this
    omega
  have h_i_ge_cond : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_n_ofNat_toNat] at hle
    omega
  have h_n_minus_1_ok :
      ((USize64.ofNat l.val.size).toUInt64 -? (1 : u64) : RustM u64) =
        RustM.ok ((USize64.ofNat l.val.size).toUInt64 - (1 : u64)) := by
    show (if BitVec.usubOverflow ((USize64.ofNat l.val.size).toUInt64).toBitVec
                                   ((1 : u64).toBitVec) then
            (.fail .integerOverflow : RustM u64)
          else pure ((USize64.ofNat l.val.size).toUInt64 - (1 : u64))) = _
    have h_no_sub_ov :
        BitVec.usubOverflow ((USize64.ofNat l.val.size).toUInt64).toBitVec
                              ((1 : u64).toBitVec) = false := by
      generalize hbo : BitVec.usubOverflow ((USize64.ofNat l.val.size).toUInt64).toBitVec
                                             ((1 : u64).toBitVec) = bo
      cases bo with
      | false => rfl
      | true =>
        exfalso
        have hov : UInt64.subOverflow (USize64.ofNat l.val.size).toUInt64 1 := hbo
        rw [UInt64.subOverflow_iff] at hov
        rw [h_n_toNat, u64_one_toNat] at hov
        omega
    rw [h_no_sub_ov]; rfl
  have h_n_minus_1_toNat :
      ((USize64.ofNat l.val.size).toUInt64 - (1 : u64)).toNat = l.val.size - 1 := by
    rw [UInt64.toNat_sub_of_le']
    · rw [h_n_toNat, u64_one_toNat]
    · rw [u64_one_toNat, h_n_toNat]; omega
  have h_div_2_ok :
      (((USize64.ofNat l.val.size).toUInt64 - (1 : u64)) /? (2 : u64) : RustM u64) =
        RustM.ok (((USize64.ofNat l.val.size).toUInt64 - (1 : u64)) / (2 : u64)) := by
    show (if (2 : u64) = 0 then (.fail .divisionByZero : RustM u64)
          else pure (((USize64.ofNat l.val.size).toUInt64 - 1) / 2)) = _
    rw [if_neg (by decide : (2 : u64) ≠ 0)]; rfl
  have h_half_toNat :
      (((USize64.ofNat l.val.size).toUInt64 - (1 : u64)) / (2 : u64)).toNat =
        (l.val.size - 1) / 2 := by
    rw [UInt64.toNat_div, h_n_minus_1_toNat, u64_two_toNat]
  -- l[i]_? = RustM.ok (l[i.toNat])
  have h_l_i :
      (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi_lt) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i]) else .fail .arrayOutOfBounds) =
          RustM.ok (l.val[i.toNat]'hi_lt)
    rw [dif_pos hi_lt]; rfl
  -- Reduce hres with all these
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.hax.cast_op, Cast.cast,
             rust_primitives.cmp.eq, rust_primitives.cmp.ge,
             pure_bind, RustM_ok_bind,
             h_n_eq_0_cond, Bool.false_eq_true, ↓reduceIte,
             h_i_ge_cond,
             h_n_minus_1_ok, h_div_2_ok,
             h_l_i, h_lt_eq, h_gt_eq] at hres
  -- Abbreviations for clarity
  -- Now hres has the form (after simp):
  --   (do let __ ← lt_v <=? half_v
  --       let _gt1 ← gt_v +? 1
  --       let _gt1h ← _gt1 +? half_v
  --       let __3 ← _gt1h <=? n_v
  --       let __c ← __ &&? __3
  --       if __c then l[i]_? else (do let __ ← i +? 1; fma l __)) = ok m
  -- Reduce <=? and &&? (pure operations).
  -- lt_v <=? half_v = pure (decide (lt_v ≤ half_v))
  -- &&? is pure ∘ ∧
  -- Let me proceed by case-analysis on the boolean predicate
  -- First: compute lt_le_half (Bool)
  have h_lt_le_half :
      (lt_v <=? (((USize64.ofNat l.val.size).toUInt64 - (1 : u64)) / (2 : u64)) : RustM Bool) =
        RustM.ok (decide (lt_v ≤
          ((USize64.ofNat l.val.size).toUInt64 - (1 : u64)) / (2 : u64))) := rfl
  -- Case-analyze on gt_v + 1 overflow. If overflow → algorithm fails → contradiction.
  by_cases h_gt1_ov : BitVec.uaddOverflow gt_v.toBitVec ((1 : u64).toBitVec) = true
  · exfalso
    have h_add_fail : (gt_v +? (1 : u64) : RustM u64) = RustM.fail .integerOverflow := by
      show (if BitVec.uaddOverflow gt_v.toBitVec ((1 : u64).toBitVec) then
              (.fail .integerOverflow : RustM u64)
            else pure (gt_v + 1)) = _
      rw [h_gt1_ov]; rfl
    rw [h_add_fail] at hres
    simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, Option.bind] at hres
    cases hres
  have h_gt1_no_ov :
      BitVec.uaddOverflow gt_v.toBitVec ((1 : u64).toBitVec) = false := by
    cases h_bv : BitVec.uaddOverflow gt_v.toBitVec ((1 : u64).toBitVec) with
    | false => rfl
    | true => exact absurd h_bv h_gt1_ov
  have h_gt_plus_1_ok :
      (gt_v +? (1 : u64) : RustM u64) = RustM.ok (gt_v + 1) := by
    show (if BitVec.uaddOverflow gt_v.toBitVec ((1 : u64).toBitVec) then
            (.fail .integerOverflow : RustM u64)
          else pure (gt_v + 1)) = _
    rw [h_gt1_no_ov]; rfl
  have h_gt1_no_ov_nat : gt_v.toNat + 1 < 2^64 := by
    rcases Nat.lt_or_ge (gt_v.toNat + 1) (2^64) with h | h
    · exact h
    · exfalso
      have hov : UInt64.addOverflow gt_v 1 := by
        rw [UInt64.addOverflow_iff, u64_one_toNat]; exact h
      have hov_bv : BitVec.uaddOverflow gt_v.toBitVec ((1 : u64).toBitVec) = true := hov
      rw [hov_bv] at h_gt1_no_ov
      exact Bool.noConfusion h_gt1_no_ov
  have h_gt_plus_1_toNat : (gt_v + 1).toNat = gt_v.toNat + 1 := by
    rw [UInt64.toNat_add_of_lt (by rw [u64_one_toNat]; omega), u64_one_toNat]
  simp only [h_lt_le_half, RustM_ok_bind, h_gt_plus_1_ok] at hres
  -- Now hres has form:
  --   (do let __2 ← (gt_v + 1) +? half_v
  --       let __3 ← __2 <=? n_v
  --       let __c ← (decide (lt_v ≤ half_v)) &&? __3
  --       if __c then ok l[i] else fma l (i+1)) = ok m
  -- Case-split on whether (gt_v + 1) +? half_v overflows
  by_cases h_ov : BitVec.uaddOverflow (gt_v + 1).toBitVec
        (((USize64.ofNat l.val.size).toUInt64 - (1 : u64)) / (2 : u64)).toBitVec = true
  · -- Overflow → +? = fail → hres = ok m is false
    exfalso
    have h_add_fail :
        ((gt_v + 1) +? (((USize64.ofNat l.val.size).toUInt64 - (1 : u64)) / (2 : u64)) : RustM u64)
          = RustM.fail .integerOverflow := by
      show (if BitVec.uaddOverflow (gt_v + 1).toBitVec
              (((USize64.ofNat l.val.size).toUInt64 - (1 : u64)) / (2 : u64)).toBitVec then
              (.fail .integerOverflow : RustM u64)
            else pure ((gt_v + 1) + ((USize64.ofNat l.val.size).toUInt64 - (1 : u64)) / (2 : u64))) = _
      rw [h_ov]; rfl
    rw [h_add_fail] at hres
    simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, Option.bind] at hres
    cases hres
  · -- No overflow.
    have h_ov_false :
        BitVec.uaddOverflow (gt_v + 1).toBitVec
          (((USize64.ofNat l.val.size).toUInt64 - (1 : u64)) / (2 : u64)).toBitVec = false := by
      cases h_bv : BitVec.uaddOverflow (gt_v + 1).toBitVec
          (((USize64.ofNat l.val.size).toUInt64 - (1 : u64)) / (2 : u64)).toBitVec with
      | false => rfl
      | true => exact absurd h_bv h_ov
    have h_no_ov_nat : (gt_v + 1).toNat +
        (((USize64.ofNat l.val.size).toUInt64 - (1 : u64)) / (2 : u64)).toNat < 2^64 := by
      rcases Nat.lt_or_ge ((gt_v + 1).toNat +
          (((USize64.ofNat l.val.size).toUInt64 - (1 : u64)) / (2 : u64)).toNat) (2^64) with h | h
      · exact h
      · exfalso
        have hov_again : UInt64.addOverflow (gt_v + 1)
              (((USize64.ofNat l.val.size).toUInt64 - (1 : u64)) / (2 : u64)) := by
          rw [UInt64.addOverflow_iff]; exact h
        have hov_bv : BitVec.uaddOverflow (gt_v + 1).toBitVec
              (((USize64.ofNat l.val.size).toUInt64 - (1 : u64)) / (2 : u64)).toBitVec = true :=
          hov_again
        rw [hov_bv] at h_ov_false
        exact Bool.noConfusion h_ov_false
    have h_add2_ok :
        ((gt_v + 1) +? (((USize64.ofNat l.val.size).toUInt64 - (1 : u64)) / (2 : u64)) : RustM u64)
          = RustM.ok ((gt_v + 1) + (((USize64.ofNat l.val.size).toUInt64 - (1 : u64)) / (2 : u64))) := by
      show (if BitVec.uaddOverflow (gt_v + 1).toBitVec _ then
              (.fail .integerOverflow : RustM u64)
            else pure _) = _
      rw [h_ov_false]; rfl
    have h_add2_toNat :
        ((gt_v + 1) + (((USize64.ofNat l.val.size).toUInt64 - (1 : u64)) / (2 : u64))).toNat =
          gt_v.toNat + 1 + (l.val.size - 1) / 2 := by
      rw [UInt64.toNat_add_of_lt h_no_ov_nat, h_gt_plus_1_toNat, h_half_toNat]
    -- Reduce hres further
    have h_le_n :
        (((gt_v + 1) + (((USize64.ofNat l.val.size).toUInt64 - (1 : u64)) / (2 : u64))) <=?
          (USize64.ofNat l.val.size).toUInt64 : RustM Bool) =
          RustM.ok (decide ((gt_v + 1) + (((USize64.ofNat l.val.size).toUInt64 - (1 : u64)) / (2 : u64))
                            ≤ (USize64.ofNat l.val.size).toUInt64)) := rfl
    simp only [h_add2_ok, RustM_ok_bind, h_le_n] at hres
    -- Now hres : (do let _c ← _ &&? _; if _c then ok l[i] else fma l (i+1)) = ok m
    -- &&? : pure ∘ And
    have h_and_pure : ∀ a b : Bool, (a &&? b : RustM Bool) = RustM.ok (a && b) := by
      intros; rfl
    simp only [h_and_pure, RustM_ok_bind] at hres
    -- hres : if decide(lt_v ≤ half_v) && decide((gt+1)+half ≤ n) then ok l[i] else fma l (i+1) = ok m
    -- Note: hres also has the inner l[i]_?, but we've already reduced it via h_l_i.
    -- Wait we need to check the if-branches use l[i]_? still
    -- Let me reduce the case
    by_cases h_pred_u64 :
        (decide (lt_v ≤ ((USize64.ofNat l.val.size).toUInt64 - (1 : u64)) / (2 : u64)) &&
         decide ((gt_v + 1) + ((USize64.ofNat l.val.size).toUInt64 - (1 : u64)) / (2 : u64)
                 ≤ (USize64.ofNat l.val.size).toUInt64)) = true
    · -- Match branch: m = l[i]
      rw [if_pos h_pred_u64] at hres
      have h_m_eq : m = l.val[i.toNat]'hi_lt := by
        have heq : RustM.ok (l.val[i.toNat]'hi_lt) = RustM.ok m := hres
        injection heq with h1
        injection h1 with h2
        exact h2.symm
      -- Derive median_pred from h_pred_u64
      rw [Bool.and_eq_true] at h_pred_u64
      obtain ⟨h_lt_le, h_gt_le⟩ := h_pred_u64
      rw [decide_eq_true_iff] at h_lt_le h_gt_le
      have h_lt_le_nat : lt_v.toNat ≤
          (((USize64.ofNat l.val.size).toUInt64 - (1 : u64)) / (2 : u64)).toNat :=
        UInt64.le_iff_toNat_le.mp h_lt_le
      have h_gt_le_nat : ((gt_v + 1) + ((USize64.ofNat l.val.size).toUInt64 - (1 : u64)) / (2 : u64)).toNat
                        ≤ ((USize64.ofNat l.val.size).toUInt64).toNat :=
        UInt64.le_iff_toNat_le.mp h_gt_le
      rw [h_n_toNat] at h_gt_le_nat
      rw [h_add2_toNat] at h_gt_le_nat
      rw [h_half_toNat] at h_lt_le_nat
      rw [h_lt_nat] at h_lt_le_nat
      rw [h_gt_nat] at h_gt_le_nat
      left
      refine ⟨h_m_eq, ?_, ?_⟩
      · -- lt_count_from l l[i] 0 ≤ (size - 1) / 2
        exact h_lt_le_nat
      · -- gt_count_from l l[i] 0 + 1 + (size-1)/2 ≤ size
        omega
    · -- Recurse branch: hres reduces to fma l (i+1) = ok m
      rw [if_neg h_pred_u64] at hres
      -- The recursion: i +? 1
      have h_no_bv_i :
          BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
        generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
        cases bo with
        | false => rfl
        | true =>
          exfalso
          have hi' := (USize64.uaddOverflow_iff i 1).mp hbo
          rw [usize_one_toNat] at hi'; omega
      have h_i_plus_1 :
          ((i +? (1 : usize)) : RustM usize) = RustM.ok (i + 1) := by
        show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec then
                (.fail .integerOverflow : RustM usize)
              else pure (i + 1)) = _
        rw [h_no_bv_i]; rfl
      simp only [h_i_plus_1, RustM_ok_bind] at hres
      right
      refine ⟨hres, ?_⟩
      -- ¬ median_pred l l[i]
      intro h_med
      apply h_pred_u64
      obtain ⟨h_lt_bd, h_gt_bd⟩ := h_med
      rw [Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · rw [decide_eq_true_iff, UInt64.le_iff_toNat_le, h_half_toNat, h_lt_nat]
        exact h_lt_bd
      · rw [decide_eq_true_iff, UInt64.le_iff_toNat_le, h_n_toNat, h_add2_toNat, h_gt_nat]
        omega

/-- Structural analysis of `find_median_at`: when called on a non-empty slice
    with `i.toNat ≤ l.val.size` and `find_median_at l i = ok m`, then either
    the algorithm scanned past every index without finding a satisfying one
    (m = 0, and the predicate fails at every k ∈ [i, size)) — or it matched
    at some k ∈ [i, size) where `l[k] = m` and `median_pred l m` holds. -/
private theorem fma_analysis
    (l : RustSlice i64) (h_size_pos : 0 < l.val.size) :
    ∀ (i : usize) (m : i64), i.toNat ≤ l.val.size →
      clever_046_median.find_median_at l i = RustM.ok m →
      (m = 0 ∧ ∀ k : Nat, i.toNat ≤ k → ∀ (hk : k < l.val.size),
        ¬ median_pred l (l.val[k]'hk)) ∨
      (∃ k : Nat, i.toNat ≤ k ∧ ∃ (hk : k < l.val.size),
        l.val[k]'hk = m ∧ median_pred l m) := by
  intro i
  induction hk : (l.val.size - i.toNat) using Nat.strongRecOn generalizing i with
  | _ K ih =>
    intro m hi_le hres
    by_cases h_oob : l.val.size ≤ i.toNat
    · have h_eq := fma_oob_nonempty l h_size_pos i h_oob
      rw [h_eq] at hres
      have h_m_zero : m = 0 := by
        have h_eq : RustM.ok m = RustM.ok (0 : i64) := hres.symm
        injection h_eq with h1
        injection h1
      left
      refine ⟨h_m_zero, ?_⟩
      intro k hk_ge hk_lt _
      omega
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le h_oob
      have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
      have h_no_overflow_i : i.toNat + 1 < 2^64 := by omega
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 :=
        usize_add_one_toNat i h_no_overflow_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1_toNat]; omega
      have h_measure : l.val.size - (i + 1).toNat < K := by rw [h_i1_toNat]; omega
      rcases fma_step l h_size_pos i hi_lt m hres with ⟨h_m_eq, h_pred⟩ | ⟨h_rec, h_not_pred⟩
      · -- Matched at i
        right
        refine ⟨i.toNat, Nat.le_refl _, hi_lt, h_m_eq.symm, ?_⟩
        rw [← h_m_eq] at h_pred
        exact h_pred
      · -- Recursed
        have h_ih := ih (l.val.size - (i + 1).toNat) h_measure (i + 1) rfl m h_i1_le h_rec
        rcases h_ih with ⟨h_m_zero, h_no_pred⟩ | ⟨k, hk_ge, hk_lt, hk_eq, hk_pred⟩
        · -- IH gave case 1
          left
          refine ⟨h_m_zero, ?_⟩
          intro k hk_ge_i hk_lt'
          by_cases h_k_eq_i : k = i.toNat
          · subst h_k_eq_i
            -- pred fails at i (h_not_pred)
            exact h_not_pred
          · have hk_ge_i1 : (i + 1).toNat ≤ k := by rw [h_i1_toNat]; omega
            exact h_no_pred k hk_ge_i1 hk_lt'
        · -- IH gave case 2
          right
          refine ⟨k, ?_, hk_lt, hk_eq, hk_pred⟩
          rw [h_i1_toNat] at hk_ge
          omega

/-- Boundary clause: on the empty input the function returns the sentinel `0`.
    Captures the property test `empty_returns_zero`. -/
theorem empty_returns_zero
    (l : RustSlice i64) (hempty : l.val.size = 0) :
    clever_046_median.median l = RustM.ok (0 : i64) := by
  unfold clever_046_median.median
  unfold clever_046_median.find_median_at
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             hempty, rust_primitives.hax.cast_op, Cast.cast, pure_bind,
             rust_primitives.cmp.eq]
  rfl

/-- Helper: run `fma_analysis` starting from `i = 0`, rule out the OOB case
    via `exists_median_witness`, and return the surviving witness with the
    median predicate (in lt_count_from / gt_count_from form). -/
private theorem median_witness_exists
    (l : RustSlice i64) (m : i64)
    (hnonempty : 0 < l.val.size)
    (h : clever_046_median.median l = RustM.ok m) :
    ∃ k : Nat, ∃ (hk : k < l.val.size),
      l.val[k]'hk = m ∧ median_pred l m := by
  unfold clever_046_median.median at h
  have h_zero_le : (0 : usize).toNat ≤ l.val.size := by show 0 ≤ _; omega
  rcases fma_analysis l hnonempty (0 : usize) m h_zero_le h with
    ⟨h_m_zero, h_no_pred⟩ | ⟨k, _, hk_lt, hk_eq, hk_pred⟩
  · -- All indices fail the predicate; contradicts exists_median_witness
    exfalso
    obtain ⟨m', k', hk'_lt, hk'_eq, hk'_lt_bd, hk'_gt_bd⟩ :=
      exists_median_witness l hnonempty
    have h_pred_at_m' : median_pred l m' := ⟨hk'_lt_bd, hk'_gt_bd⟩
    rw [← hk'_eq] at h_pred_at_m'
    have h_zero_toNat : ((0 : usize).toNat : Nat) = 0 := rfl
    rw [h_zero_toNat] at h_no_pred
    exact h_no_pred k' (Nat.zero_le _) hk'_lt h_pred_at_m'
  · exact ⟨k, hk_lt, hk_eq, hk_pred⟩

/-- The returned value is one of the elements of the input slice.
    Captures the property test `returned_value_is_in_list`. -/
theorem returned_value_is_in_list
    (l : RustSlice i64) (m : i64)
    (hnonempty : 0 < l.val.size)
    (h : clever_046_median.median l = RustM.ok m) :
    ∃ i : Nat, ∃ (hi : i < l.val.size), l.val[i]'hi = m := by
  obtain ⟨k, hk_lt, hk_eq, _⟩ := median_witness_exists l m hnonempty h
  exact ⟨k, hk_lt, hk_eq⟩

/-- Bridge between the obligations' `lt_count l m l.val.size` and the
    forward-form `lt_count_from l m 0`. -/
private theorem lt_count_size_eq_from (l : RustSlice i64) (m : i64) :
    lt_count l m l.val.size = lt_count_from l m 0 := by
  have h := lt_count_eq_sub l m 0 (Nat.zero_le _)
  -- lt_count_from l m 0 = lt_count l m size - lt_count l m 0
  -- lt_count l m 0 = 0 (definition).
  have h_zero : lt_count l m 0 = 0 := rfl
  rw [h_zero] at h
  omega

private theorem gt_count_size_eq_from (l : RustSlice i64) (m : i64) :
    gt_count l m l.val.size = gt_count_from l m 0 := by
  have h := gt_count_eq_sub l m 0 (Nat.zero_le _)
  have h_zero : gt_count l m 0 = 0 := rfl
  rw [h_zero] at h
  omega

/-- Lower-median characterisation, part 1: the count of strictly-smaller
    elements is bounded by `(size - 1) / 2`. Together with
    `median_gt_count_bound`, this captures the property test
    `matches_brute_force`. -/
theorem median_lt_count_bound
    (l : RustSlice i64) (m : i64)
    (hnonempty : 0 < l.val.size)
    (h : clever_046_median.median l = RustM.ok m) :
    lt_count l m l.val.size ≤ (l.val.size - 1) / 2 := by
  obtain ⟨_, _, _, h_pred⟩ := median_witness_exists l m hnonempty h
  rw [lt_count_size_eq_from]
  exact h_pred.1

/-- Lower-median characterisation, part 2: the count of strictly-greater
    elements plus `1 + (size - 1) / 2` is at most `size`. Together with
    `median_lt_count_bound`, captures `matches_brute_force`. -/
theorem median_gt_count_bound
    (l : RustSlice i64) (m : i64)
    (hnonempty : 0 < l.val.size)
    (h : clever_046_median.median l = RustM.ok m) :
    gt_count l m l.val.size + 1 + (l.val.size - 1) / 2 ≤ l.val.size := by
  obtain ⟨_, _, _, h_pred⟩ := median_witness_exists l m hnonempty h
  rw [gt_count_size_eq_from]
  exact h_pred.2

end Clever_046_medianObligations
