-- Companion obligations file for the `clever_068_search` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_068_search

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_068_searchObligations

/-! ## Specification oracle: count of occurrences of `v` in a slice tail.

`count_occ_from l v i` is the number of indices `j ∈ [i, l.val.size)` with
`l.val[j] = v`, expressed at the `Nat` level. The top-level theorems apply
it with `i = 0`. This matches the operational behaviour of the extracted
`count_occurrences l v i`, modulo the Nat/u64 conversion. -/

private def count_occ_from (l : RustSlice u64) (v : u64) (i : Nat) : Nat :=
  if h : i < l.val.size then
    (if l.val[i]'h = v then 1 else 0) + count_occ_from l v (i + 1)
  else 0
termination_by l.val.size - i

/-! ## Standard scaffolding. -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl
private theorem u64_zero_toNat : (0 : u64).toNat = 0 := rfl
private theorem u64_one_toNat : (1 : u64).toNat = 1 := rfl

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

/-! ## Equational lemmas for the Nat-level oracle. -/

private theorem count_occ_from_oob (l : RustSlice u64) (v : u64) (i : Nat)
    (h : ¬ i < l.val.size) :
    count_occ_from l v i = 0 := by
  unfold count_occ_from; rw [dif_neg h]

private theorem count_occ_from_succ (l : RustSlice u64) (v : u64) (i : Nat)
    (h : i < l.val.size) :
    count_occ_from l v i =
      (if l.val[i]'h = v then 1 else 0) + count_occ_from l v (i + 1) := by
  conv => lhs; unfold count_occ_from
  rw [dif_pos h]

private theorem count_occ_from_le (l : RustSlice u64) (v : u64) (i : Nat) :
    count_occ_from l v i ≤ l.val.size - i := by
  induction hk : (l.val.size - i) using Nat.strongRecOn generalizing i with
  | _ k ih =>
    by_cases h : i < l.val.size
    · rw [count_occ_from_succ l v i h]
      have h_meas : l.val.size - (i + 1) < k := by rw [← hk]; omega
      have h_ih := ih (l.val.size - (i + 1)) h_meas (i + 1) rfl
      by_cases hz : l.val[i]'h = v
      · rw [if_pos hz]; omega
      · rw [if_neg hz]; omega
    · rw [count_occ_from_oob l v i h]; omega

/-! ## Step lemmas for `count_occurrences`. -/

private theorem co_oob (l : RustSlice u64) (v : u64) (i : usize)
    (hi : l.val.size ≤ i.toNat) :
    clever_068_search.count_occurrences l v i = RustM.ok (0 : u64) := by
  conv => lhs; unfold clever_068_search.count_occurrences
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

private theorem co_match (l : RustSlice u64) (v : u64) (i : usize)
    (hi : i.toNat < l.val.size)
    (heq : (l.val[i.toNat]'hi) = v) :
    clever_068_search.count_occurrences l v i =
      clever_068_search.count_occurrences l v (i + 1) >>= fun r =>
        ((1 : u64) +? r) := by
  conv => lhs; unfold clever_068_search.count_occurrences
  have h_size : l.val.size < 2^64 := l.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (l[i]_? : RustM u64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
  have h_beq_true : ((l.val[i.toNat]'hi) == v) = true := by
    rw [beq_iff_eq]; exact heq
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
             rust_primitives.cmp.eq, h_beq_true,
             rust_primitives.ops.arith.Add.add, h_no_bv_i]

private theorem co_norm (l : RustSlice u64) (v : u64) (i : usize)
    (hi : i.toNat < l.val.size)
    (hne : (l.val[i.toNat]'hi) ≠ v) :
    clever_068_search.count_occurrences l v i =
      clever_068_search.count_occurrences l v (i + 1) := by
  conv => lhs; unfold clever_068_search.count_occurrences
  have h_size : l.val.size < 2^64 := l.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (l[i]_? : RustM u64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
  have h_beq_false : ((l.val[i.toNat]'hi) == v) = false := by
    rw [beq_eq_false_iff_ne]; exact hne
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

/-! ## Workhorse: `count_occurrences l v i` agrees with `count_occ_from l v i.toNat`. -/

private theorem co_correct (l : RustSlice u64) (v : u64) (i : usize)
    (hi : i.toNat ≤ l.val.size) :
    ∃ c : u64,
      clever_068_search.count_occurrences l v i = RustM.ok c ∧
      c.toNat = count_occ_from l v i.toNat := by
  induction hk : (l.val.size - i.toNat) using Nat.strongRecOn generalizing i with
  | _ k ih =>
    by_cases h_oob : l.val.size ≤ i.toNat
    · have h_oob_eq : i.toNat = l.val.size := by omega
      have h_eq := co_oob l v i h_oob
      have h_cof_zero : count_occ_from l v i.toNat = 0 := by
        rw [h_oob_eq]; exact count_occ_from_oob l v l.val.size (by omega)
      refine ⟨0, h_eq, ?_⟩
      rw [h_cof_zero]; rfl
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le h_oob
      have h_size : l.val.size < 2^64 := l.size_lt_usizeSize
      have h_no_overflow_i : i.toNat + 1 < 2^64 := by omega
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 :=
        usize_add_one_toNat i h_no_overflow_i
      have h_count_le : count_occ_from l v (i.toNat + 1) ≤ l.val.size - (i.toNat + 1) :=
        count_occ_from_le l v (i.toNat + 1)
      have h_measure : l.val.size - (i + 1).toNat < k := by rw [h_i1_toNat]; omega
      have h_cof_succ := count_occ_from_succ l v i.toNat hi_lt
      obtain ⟨c', hc'_eq, hc'_nat⟩ :=
        ih (l.val.size - (i + 1).toNat) h_measure (i + 1) (by rw [h_i1_toNat]; omega) rfl
      rw [h_i1_toNat] at hc'_nat
      by_cases heq : (l.val[i.toNat]'hi_lt) = v
      · -- match branch: result = 1 + c'
        have h_step := co_match l v i hi_lt heq
        have h_one_c' : c'.toNat + 1 < 2^64 := by rw [hc'_nat]; omega
        have h_no_bv_acc :
            BitVec.uaddOverflow ((1 : u64).toBitVec) c'.toBitVec = false := by
          generalize hbo : BitVec.uaddOverflow ((1 : u64).toBitVec) c'.toBitVec = bo
          cases bo with
          | false => rfl
          | true =>
            exfalso
            have hov : UInt64.addOverflow 1 c' := hbo
            rw [UInt64.addOverflow_iff] at hov
            rw [u64_one_toNat] at hov
            omega
        have h_add_eq : ((1 : u64) +? c' : RustM u64) = RustM.ok ((1 : u64) + c') := by
          show (if BitVec.uaddOverflow (1 : u64).toBitVec c'.toBitVec then
                  (.fail .integerOverflow : RustM u64)
                else pure ((1 : u64) + c')) = _
          rw [h_no_bv_acc]; rfl
        refine ⟨(1 : u64) + c', ?_, ?_⟩
        · rw [h_step, hc'_eq, RustM_ok_bind, h_add_eq]
        · rw [UInt64.toNat_add_of_lt (by rw [u64_one_toNat]; omega)]
          rw [u64_one_toNat, hc'_nat]
          rw [h_cof_succ, if_pos heq]
      · -- non-match branch: result = c'
        have h_step := co_norm l v i hi_lt heq
        refine ⟨c', ?_, ?_⟩
        · rw [h_step, hc'_eq]
        · rw [hc'_nat, h_cof_succ, if_neg heq]; omega

/-- Specialization at `i = 0`. -/
private theorem co_correct_zero (l : RustSlice u64) (v : u64) :
    ∃ c : u64,
      clever_068_search.count_occurrences l v (0 : usize) = RustM.ok c ∧
      c.toNat = count_occ_from l v 0 := by
  have h_zero : (0 : usize).toNat = 0 := rfl
  obtain ⟨c, h_eq, h_nat⟩ := co_correct l v (0 : usize) (by rw [h_zero]; omega)
  rw [h_zero] at h_nat
  exact ⟨c, h_eq, h_nat⟩

/-! ## Step lemmas for `search_at`.

`search_at` has three branches in its in-bounds case: update best (v>0,
v>best, count≥v), no-update (v>0, v>best, count<v), and skip
(¬(v>0 ∧ v>best)). -/

/-- Out-of-bounds step: returns the running `best`. -/
private theorem sa_oob (l : RustSlice u64) (i : usize) (best : u64)
    (hi : l.val.size ≤ i.toNat) :
    clever_068_search.search_at l i best = RustM.ok best := by
  conv => lhs; unfold clever_068_search.search_at
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

/-- Skip step: in-bounds, but `v ≤ 0` or `v ≤ best`. The recursion is on `(i+1, best)`. -/
private theorem sa_skip (l : RustSlice u64) (i : usize) (best : u64)
    (hi : i.toNat < l.val.size)
    (h_skip : ¬ ((0 : u64) < (l.val[i.toNat]'hi) ∧ best < (l.val[i.toNat]'hi))) :
    clever_068_search.search_at l i best =
      clever_068_search.search_at l (i + 1) best := by
  conv => lhs; unfold clever_068_search.search_at
  have h_size : l.val.size < 2^64 := l.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (l[i]_? : RustM u64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
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
  have h_and_cond :
      (decide ((0 : u64) < (l.val[i.toNat]'hi)) && decide (best < (l.val[i.toNat]'hi))) = false := by
    rw [Bool.and_eq_false_iff]
    by_cases h0 : (0 : u64) < (l.val[i.toNat]'hi)
    · by_cases hb : best < (l.val[i.toNat]'hi)
      · exfalso; exact h_skip ⟨h0, hb⟩
      · right; rw [decide_eq_false_iff_not]; exact hb
    · left; rw [decide_eq_false_iff_not]; exact h0
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.cmp.gt,
             rust_primitives.hax.logical_op.and,
             h_and_cond,
             rust_primitives.ops.arith.Add.add, h_no_bv_i]

/-- Update step: in-bounds, `v > 0 ∧ v > best`, and `count_occurrences l v 0 = ok c`
    with `c ≥ v`. The recursion is on `(i+1, v)`. -/
private theorem sa_update (l : RustSlice u64) (i : usize) (best : u64)
    (hi : i.toNat < l.val.size)
    (h_pos : (0 : u64) < (l.val[i.toNat]'hi))
    (h_gt : best < (l.val[i.toNat]'hi))
    (c : u64)
    (hcount : clever_068_search.count_occurrences l (l.val[i.toNat]'hi) (0 : usize)
                = RustM.ok c)
    (hc_ge : (l.val[i.toNat]'hi) ≤ c) :
    clever_068_search.search_at l i best =
      clever_068_search.search_at l (i + 1) (l.val[i.toNat]'hi) := by
  conv => lhs; unfold clever_068_search.search_at
  have h_size : l.val.size < 2^64 := l.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (l[i]_? : RustM u64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
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
  have h_and_cond :
      (decide ((0 : u64) < (l.val[i.toNat]'hi)) && decide (best < (l.val[i.toNat]'hi))) = true := by
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [decide_eq_true_iff]; exact h_pos
    · rw [decide_eq_true_iff]; exact h_gt
  have h_ge_cond : decide ((l.val[i.toNat]'hi) ≤ c) = true := by
    rw [decide_eq_true_iff]; exact hc_ge
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.cmp.gt,
             rust_primitives.hax.logical_op.and,
             h_and_cond,
             hcount,
             h_ge_cond,
             rust_primitives.ops.arith.Add.add, h_no_bv_i]

/-- No-update step: in-bounds, `v > 0 ∧ v > best`, and `count_occurrences l v 0 = ok c`
    with `c < v`. The recursion is on `(i+1, best)`. -/
private theorem sa_no_update (l : RustSlice u64) (i : usize) (best : u64)
    (hi : i.toNat < l.val.size)
    (h_pos : (0 : u64) < (l.val[i.toNat]'hi))
    (h_gt : best < (l.val[i.toNat]'hi))
    (c : u64)
    (hcount : clever_068_search.count_occurrences l (l.val[i.toNat]'hi) (0 : usize)
                = RustM.ok c)
    (hc_lt : c < (l.val[i.toNat]'hi)) :
    clever_068_search.search_at l i best =
      clever_068_search.search_at l (i + 1) best := by
  conv => lhs; unfold clever_068_search.search_at
  have h_size : l.val.size < 2^64 := l.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (l[i]_? : RustM u64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
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
  have h_and_cond :
      (decide ((0 : u64) < (l.val[i.toNat]'hi)) && decide (best < (l.val[i.toNat]'hi))) = true := by
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [decide_eq_true_iff]; exact h_pos
    · rw [decide_eq_true_iff]; exact h_gt
  have h_ge_cond : decide ((l.val[i.toNat]'hi) ≤ c) = false := by
    rw [decide_eq_false_iff_not]
    intro h_le
    have h1 := UInt64.le_iff_toNat_le.mp h_le
    have h2 := UInt64.lt_iff_toNat_lt.mp hc_lt
    omega
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.cmp.gt,
             rust_primitives.hax.logical_op.and,
             h_and_cond,
             hcount,
             h_ge_cond,
             rust_primitives.ops.arith.Add.add, h_no_bv_i]

/-! ## Structural correctness of `search_at`.

The invariant we thread:

  `best = 0 ∨ count_occ_from l best 0 ≥ best.toNat`

and the conclusions for the returned value `r`:

  1. monotonicity: `best ≤ r`,
  2. invariant on `r`: `r = 0 ∨ count_occ_from l r 0 ≥ r.toNat`,
  3. maximality from `i` onward: for all in-bounds `k ≥ i.toNat`,
     if `l.val[k] > r` then `count_occ_from l l.val[k] 0 < l.val[k].toNat`. -/

private theorem search_at_correct (l : RustSlice u64) :
    ∀ (i : usize) (best : u64) (r : u64),
      (best = 0 ∨ best.toNat ≤ count_occ_from l best 0) →
      i.toNat ≤ l.val.size →
      clever_068_search.search_at l i best = RustM.ok r →
      best ≤ r ∧
      (r = 0 ∨ r.toNat ≤ count_occ_from l r 0) ∧
      (∀ k : Nat, i.toNat ≤ k → ∀ (hk : k < l.val.size),
        r < (l.val[k]'hk) →
        count_occ_from l (l.val[k]'hk) 0 < (l.val[k]'hk).toNat) := by
  intro i
  induction hk : (l.val.size - i.toNat) using Nat.strongRecOn generalizing i with
  | _ K ih =>
    intro best r h_inv hi_le hres
    by_cases h_oob : l.val.size ≤ i.toNat
    · -- OOB: r = best
      have h_eq := sa_oob l i best h_oob
      rw [h_eq] at hres
      have h_r_eq : r = best := by
        injection hres with h1
        injection h1 with h2
        exact h2.symm
      subst h_r_eq
      refine ⟨?_, h_inv, ?_⟩
      · exact UInt64.le_iff_toNat_le.mpr (Nat.le_refl _)
      · intro k hk_ge hk_lt _
        omega
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le h_oob
      have h_size : l.val.size < 2^64 := l.size_lt_usizeSize
      have h_no_overflow_i : i.toNat + 1 < 2^64 := by omega
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 :=
        usize_add_one_toNat i h_no_overflow_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1_toNat]; omega
      have h_measure : l.val.size - (i + 1).toNat < K := by rw [h_i1_toNat]; omega
      -- Define v at this index for brevity in the case analysis.
      have hv_def : (l.val[i.toNat]'hi_lt) = (l.val[i.toNat]'hi_lt) := rfl
      -- Branch on the boolean condition.
      by_cases h_cond : (0 : u64) < (l.val[i.toNat]'hi_lt) ∧ best < (l.val[i.toNat]'hi_lt)
      · -- "Possibly update" branch.
        obtain ⟨h_pos, h_gt⟩ := h_cond
        -- Get the count.
        obtain ⟨c, hc_eq, hc_nat⟩ := co_correct_zero l (l.val[i.toNat]'hi_lt)
        -- Sub-branch on c ≥ v (u64).
        by_cases hc_ge : (l.val[i.toNat]'hi_lt) ≤ c
        · -- Update branch: recurse with (i+1, v).
          have h_step := sa_update l i best hi_lt h_pos h_gt c hc_eq hc_ge
          rw [h_step] at hres
          -- v satisfies invariant (count(v) ≥ v.toNat).
          have h_v_nat_le_count : (l.val[i.toNat]'hi_lt).toNat
              ≤ count_occ_from l (l.val[i.toNat]'hi_lt) 0 := by
            have h_v_le_c_nat : (l.val[i.toNat]'hi_lt).toNat ≤ c.toNat :=
              UInt64.le_iff_toNat_le.mp hc_ge
            rw [← hc_nat]; exact h_v_le_c_nat
          have h_v_inv : (l.val[i.toNat]'hi_lt) = 0
              ∨ (l.val[i.toNat]'hi_lt).toNat ≤ count_occ_from l (l.val[i.toNat]'hi_lt) 0 :=
            Or.inr h_v_nat_le_count
          have h_ih := ih (l.val.size - (i + 1).toNat) h_measure (i + 1) rfl
                          (l.val[i.toNat]'hi_lt) r h_v_inv h_i1_le hres
          obtain ⟨h_v_le_r, h_r_inv, h_max_i1⟩ := h_ih
          refine ⟨?_, h_r_inv, ?_⟩
          · -- best ≤ r via best < v ≤ r.
            have h_best_lt_v_nat : best.toNat < (l.val[i.toNat]'hi_lt).toNat :=
              UInt64.lt_iff_toNat_lt.mp h_gt
            have h_v_le_r_nat : (l.val[i.toNat]'hi_lt).toNat ≤ r.toNat :=
              UInt64.le_iff_toNat_le.mp h_v_le_r
            exact UInt64.le_iff_toNat_le.mpr (by omega)
          · -- maximality at all k ≥ i.toNat
            intro k hk_ge hk_lt h_lt_lk
            by_cases h_eq_i : k = i.toNat
            · -- k = i.toNat ⇒ v = l[k]. From v ≤ r, l[k] ≤ r. Contradicts h_lt_lk : r < l[k].
              subst h_eq_i
              exfalso
              have h_v_le_r_nat : (l.val[i.toNat]'hi_lt).toNat ≤ r.toNat :=
                UInt64.le_iff_toNat_le.mp h_v_le_r
              have h_r_lt_v_nat : r.toNat < (l.val[i.toNat]'hk_lt).toNat :=
                UInt64.lt_iff_toNat_lt.mp h_lt_lk
              omega
            · have hk_ge_i1 : (i + 1).toNat ≤ k := by rw [h_i1_toNat]; omega
              exact h_max_i1 k hk_ge_i1 hk_lt h_lt_lk
        · -- c < v: no_update branch.
          have hc_lt : c < (l.val[i.toNat]'hi_lt) := by
            have h_nat : ¬ (l.val[i.toNat]'hi_lt).toNat ≤ c.toNat :=
              fun h => hc_ge (UInt64.le_iff_toNat_le.mpr h)
            have h_c_lt_v_nat : c.toNat < (l.val[i.toNat]'hi_lt).toNat := by omega
            exact UInt64.lt_iff_toNat_lt.mpr h_c_lt_v_nat
          have h_step := sa_no_update l i best hi_lt h_pos h_gt c hc_eq hc_lt
          rw [h_step] at hres
          have h_ih := ih (l.val.size - (i + 1).toNat) h_measure (i + 1) rfl best r
                          h_inv h_i1_le hres
          obtain ⟨h_best_le_r, h_r_inv, h_max_i1⟩ := h_ih
          refine ⟨h_best_le_r, h_r_inv, ?_⟩
          intro k hk_ge hk_lt h_lt_lk
          by_cases h_eq_i : k = i.toNat
          · -- k = i.toNat: at l[i] = v. We need count(v) < v.toNat. From hc_nat & hc_lt.
            subst h_eq_i
            have h_c_lt_v_nat : c.toNat < (l.val[i.toNat]'hk_lt).toNat :=
              UInt64.lt_iff_toNat_lt.mp hc_lt
            rw [← hc_nat]
            exact h_c_lt_v_nat
          · have hk_ge_i1 : (i + 1).toNat ≤ k := by rw [h_i1_toNat]; omega
            exact h_max_i1 k hk_ge_i1 hk_lt h_lt_lk
      · -- Skip branch.
        have h_step := sa_skip l i best hi_lt h_cond
        rw [h_step] at hres
        have h_ih := ih (l.val.size - (i + 1).toNat) h_measure (i + 1) rfl best r
                        h_inv h_i1_le hres
        obtain ⟨h_best_le_r, h_r_inv, h_max_i1⟩ := h_ih
        refine ⟨h_best_le_r, h_r_inv, ?_⟩
        intro k hk_ge hk_lt h_lt_lk
        by_cases h_eq_i : k = i.toNat
        · -- k = i.toNat: skip says ¬(0 < v ∧ best < v). So v = 0 or v ≤ best. Combined with
          -- best ≤ r and h_lt_lk : r < v: derive contradiction.
          subst h_eq_i
          exfalso
          -- From h_cond : ¬(0 < l[i] ∧ best < l[i]):
          -- case 1: ¬ (0 < l[i]) ⇒ l[i] = 0 (since u64 ≥ 0) ⇒ r < 0 ⇒ contradiction (r ≥ best ≥ 0).
          -- case 2: ¬ (best < l[i]) ⇒ l[i] ≤ best ≤ r ⇒ contradicts r < l[i].
          have h_best_le_r_nat : best.toNat ≤ r.toNat := UInt64.le_iff_toNat_le.mp h_best_le_r
          have h_r_lt_v_nat : r.toNat < (l.val[i.toNat]'hk_lt).toNat :=
            UInt64.lt_iff_toNat_lt.mp h_lt_lk
          by_cases hA : (0 : u64) < (l.val[i.toNat]'hk_lt)
          · -- ¬ (best < l[i])  ⇒  l[i].toNat ≤ best.toNat
            have h_not_gt : ¬ best < (l.val[i.toNat]'hk_lt) :=
              fun hB => h_cond ⟨hA, hB⟩
            have h_nat : ¬ best.toNat < (l.val[i.toNat]'hk_lt).toNat :=
              fun h => h_not_gt (UInt64.lt_iff_toNat_lt.mpr h)
            omega
          · -- ¬ (0 < l[i])  ⇒  l[i].toNat ≤ 0
            have h_nat : ¬ (0 : u64).toNat < (l.val[i.toNat]'hk_lt).toNat :=
              fun h => hA (UInt64.lt_iff_toNat_lt.mpr h)
            rw [u64_zero_toNat] at h_nat
            omega
        · have hk_ge_i1 : (i + 1).toNat ≤ k := by rw [h_i1_toNat]; omega
          exact h_max_i1 k hk_ge_i1 hk_lt h_lt_lk

/-! ## Top-level theorems. -/

/-- Boundary clause: on the empty input the function returns the sentinel `0`. -/
theorem empty_returns_zero
    (numbers : RustSlice u64) (hempty : numbers.val.size = 0) :
    clever_068_search.search numbers = RustM.ok (0 : u64) := by
  unfold clever_068_search.search
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_oob : numbers.val.size ≤ (0 : usize).toNat := by
    rw [h_zero_toNat, hempty]; exact Nat.le_refl _
  exact sa_oob numbers (0 : usize) (0 : u64) h_oob

/-- Frequency invariant: if `search numbers` returns a positive value `r`,
    then `r` occurs at least `r` times in `numbers`. -/
theorem frequency_invariant
    (numbers : RustSlice u64) (r : u64)
    (h : clever_068_search.search numbers = RustM.ok r)
    (hr : (0 : u64) < r) :
    r.toNat ≤ count_occ_from numbers r 0 := by
  unfold clever_068_search.search at h
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_zero_le : (0 : usize).toNat ≤ numbers.val.size := by
    rw [h_zero_toNat]; omega
  have h_inv : (0 : u64) = 0 ∨ (0 : u64).toNat ≤ count_occ_from numbers (0 : u64) 0 := by
    left; rfl
  obtain ⟨_, h_r_inv, _⟩ := search_at_correct numbers (0 : usize) (0 : u64) r h_inv h_zero_le h
  rcases h_r_inv with h_r_zero | h_count
  · exfalso
    rw [h_r_zero] at hr
    have := UInt64.lt_iff_toNat_lt.mp hr
    rw [u64_zero_toNat] at this
    omega
  · exact h_count

/-- Maximality: no value strictly greater than the result, occurring in
    `numbers`, satisfies the "frequency ≥ self" condition. -/
theorem maximality
    (numbers : RustSlice u64) (r : u64)
    (h : clever_068_search.search numbers = RustM.ok r) :
    ∀ i : Nat, ∀ (hi : i < numbers.val.size),
      r < (numbers.val[i]'hi) →
      count_occ_from numbers (numbers.val[i]'hi) 0
        < (numbers.val[i]'hi).toNat := by
  unfold clever_068_search.search at h
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_zero_le : (0 : usize).toNat ≤ numbers.val.size := by
    rw [h_zero_toNat]; omega
  have h_inv : (0 : u64) = 0 ∨ (0 : u64).toNat ≤ count_occ_from numbers (0 : u64) 0 := by
    left; rfl
  obtain ⟨_, _, h_max⟩ := search_at_correct numbers (0 : usize) (0 : u64) r h_inv h_zero_le h
  intro i hi h_lt
  have h_zero_le_i : (0 : usize).toNat ≤ i := by rw [h_zero_toNat]; omega
  exact h_max i h_zero_le_i hi h_lt

end Clever_068_searchObligations
