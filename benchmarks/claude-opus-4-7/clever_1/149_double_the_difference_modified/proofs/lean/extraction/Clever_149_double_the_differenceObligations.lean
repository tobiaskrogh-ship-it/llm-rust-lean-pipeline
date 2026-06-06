-- Companion obligations file for the `clever_149_double_the_difference` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_149_double_the_difference

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_149_double_the_differenceObligations

/-! ## Integer-valued specification

The Rust source `double_the_difference(numbers)` returns the sum of
squares of the positive odd integers in `numbers` (negative values and
even values are ignored).  We mirror this at the `Int` level via a
primitive-recursive prefix-sum oracle so the specification itself
cannot overflow on any input the Lean model permits; overflow shows
up as a precondition on the obligation rather than a hidden
assumption in the spec.
-/

/-- Integer-valued prefix sum of squares of positive-odd elements. -/
private def dtd_int (l : RustSlice i64) : Nat → Int
  | 0     => 0
  | k + 1 =>
      dtd_int l k +
        (if h : k < l.val.size then
           (if 0 < (l.val[k]'h).toInt ∧ (l.val[k]'h).toInt % 2 = 1
            then (l.val[k]'h).toInt * (l.val[k]'h).toInt
            else 0)
         else 0)

/-! ## Standard helpers (mirrored from `clever_084_solve_modified` /
    `sum_squares_132_modified`). -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl
private theorem usize_zero_toNat : (0 : usize).toNat = 0 := rfl
private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide

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
    have hii := (USize64.uaddOverflow_iff i 1).mp hbo
    rw [usize_one_toNat] at hii
    omega

private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide

private theorem slice_index_eq (l : RustSlice i64) (i : usize)
    (hi : i.toNat < l.val.size) :
    (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi) := by
  show (if h : i.toNat < l.val.size then pure (l.val[i])
          else .fail .arrayOutOfBounds)
      = RustM.ok (l.val[i.toNat]'hi)
  rw [dif_pos hi]; rfl

/-! ## `i64`-modulo helpers (mirrored from `clever_084_solve_modified`,
    adapted for `% 2 == 1`). -/

/-- `(x %? 2 : RustM i64) = RustM.ok (x % 2)` (since `2 ≠ -1, 0`). -/
private theorem i64_rem_two_eq (x : i64) :
    (x %? (2 : i64) : RustM i64) = RustM.ok (x % 2) := by
  show (rust_primitives.ops.arith.Rem.rem x 2 : RustM i64) = RustM.ok (x % 2)
  show (if (x = Int64.minValue && (2 : i64) = -1) then
          (.fail .integerOverflow : RustM i64)
        else if (2 : i64) = 0 then .fail .divisionByZero
        else pure (x % 2)) = _
  have h_and : (x = Int64.minValue && decide ((2 : i64) = -1)) = false := by
    rw [show (decide ((2 : i64) = -1)) = false from by decide]
    exact Bool.and_false _
  rw [h_and]
  rw [if_neg (by decide : ¬ ((2 : i64) = 0))]
  rfl

/-- `((x % (2 : i64)) = (1 : i64)) ↔ x.toInt.tmod 2 = 1`. -/
private theorem i64_mod_two_eq_one_iff_tmod (x : i64) :
    ((x % (2 : i64)) = (1 : i64)) ↔ x.toInt.tmod 2 = 1 := by
  constructor
  · intro h
    have h_toInt : (x % 2 : i64).toInt = (1 : i64).toInt := by rw [h]
    rw [Int64.toInt_mod] at h_toInt
    rw [show ((2 : i64).toInt) = (2 : Int) from rfl] at h_toInt
    rw [show ((1 : i64).toInt) = (1 : Int) from by decide] at h_toInt
    exact h_toInt
  · intro h
    apply Int64.toInt_inj.mp
    rw [Int64.toInt_mod]
    rw [show ((2 : i64).toInt) = (2 : Int) from rfl]
    rw [show ((1 : i64).toInt) = (1 : Int) from by decide]
    exact h

/-! ## Spec helpers. -/

/-- `0 ≤ x * x` for `x : Int`.  No `Mathlib.sq_nonneg` here. -/
private theorem mul_self_nonneg_int (x : Int) : 0 ≤ x * x := by
  by_cases h : x < 0
  · have h1 : 0 ≤ -x := by omega
    have h2 : 0 ≤ (-x) * (-x) := Int.mul_nonneg h1 h1
    rw [Int.neg_mul_neg] at h2
    exact h2
  · have h' : 0 ≤ x := by omega
    exact Int.mul_nonneg h' h'

/-- Step of `dtd_int`: when `k < l.val.size`, the outer `dite` reduces. -/
private theorem dtd_int_succ
    (l : RustSlice i64) (k : Nat) (hk : k < l.val.size) :
    dtd_int l (k + 1) =
      dtd_int l k +
        (if 0 < (l.val[k]'hk).toInt ∧ (l.val[k]'hk).toInt % 2 = 1
         then (l.val[k]'hk).toInt * (l.val[k]'hk).toInt
         else 0) := by
  show dtd_int l k
        + (if h : k < l.val.size then
             (if 0 < (l.val[k]'h).toInt ∧ (l.val[k]'h).toInt % 2 = 1
              then (l.val[k]'h).toInt * (l.val[k]'h).toInt
              else 0)
           else 0)
       = _
  rw [dif_pos hk]

/-- `dtd_int l k ≥ 0`: each addend is non-negative (square of an Int or 0). -/
private theorem dtd_int_nonneg (l : RustSlice i64) (k : Nat) :
    0 ≤ dtd_int l k := by
  induction k with
  | zero => show (0 : Int) ≤ 0; omega
  | succ k ih =>
    show 0 ≤ dtd_int l k
              + (if h : k < l.val.size then
                  (if 0 < (l.val[k]'h).toInt ∧ (l.val[k]'h).toInt % 2 = 1
                   then (l.val[k]'h).toInt * (l.val[k]'h).toInt
                   else 0)
                 else 0)
    by_cases h : k < l.val.size
    · rw [dif_pos h]
      by_cases h_pred :
          0 < (l.val[k]'h).toInt ∧ (l.val[k]'h).toInt % 2 = 1
      · rw [if_pos h_pred]
        have h_sq : 0 ≤ (l.val[k]'h).toInt * (l.val[k]'h).toInt :=
          mul_self_nonneg_int _
        omega
      · rw [if_neg h_pred]; omega
    · rw [dif_neg h]; omega

/-! ## Step lemmas for `sum_at`. -/

/-- Out-of-bounds step. -/
private theorem sum_at_oob (l : RustSlice i64) (i : usize) (acc : i64)
    (hi : l.val.size ≤ i.toNat) :
    clever_149_double_the_difference.sum_at l i acc = RustM.ok acc := by
  conv => lhs; unfold clever_149_double_the_difference.sum_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = true := by
    rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, h_cond, ↓reduceIte]
  rfl

/-- Take step: when the predicate `0 < l[i].toInt ∧ l[i].toInt % 2 = 1`
    holds, neither the per-element square nor the accumulator addition
    overflow, and `i+1` fits in `usize`, the function delegates to
    `sum_at l (i+1) (acc + l[i] * l[i])`. -/
private theorem sum_at_take
    (l : RustSlice i64) (i : usize) (acc : i64)
    (hi : i.toNat < l.val.size)
    (h_pos : 0 < (l.val[i.toNat]'hi).toInt)
    (h_odd : (l.val[i.toNat]'hi).toInt % 2 = 1)
    (hno_mul : ¬ Int64.mulOverflow (l.val[i.toNat]'hi) (l.val[i.toNat]'hi))
    (hno_add : ¬ Int64.addOverflow acc
                  ((l.val[i.toNat]'hi) * (l.val[i.toNat]'hi))) :
    clever_149_double_the_difference.sum_at l i acc =
      clever_149_double_the_difference.sum_at l (i + 1)
        (acc + (l.val[i.toNat]'hi) * (l.val[i.toNat]'hi)) := by
  conv => lhs; unfold clever_149_double_the_difference.sum_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]
    omega
  have h_idx := slice_index_eq l i hi
  have h_irem := i64_rem_two_eq (l.val[i.toNat]'hi)
  -- Bridge `l[i] > 0` (Bool) to `0 < l[i].toInt`.
  have h_gt : decide ((l.val[i.toNat]'hi) > (0 : i64)) = true := by
    rw [decide_eq_true_iff]
    show (0 : i64) < (l.val[i.toNat]'hi)
    rw [Int64.lt_iff_toInt_lt, i64_zero_toInt]
    exact h_pos
  -- Bridge `l[i] % 2 = 1` from spec hypotheses.
  have h_tmod : (l.val[i.toNat]'hi).toInt.tmod 2 = 1 := by
    rw [Int.tmod_eq_emod_of_nonneg (Int.le_of_lt h_pos)]
    exact h_odd
  have h_mod_eq : ((l.val[i.toNat]'hi) % 2 : i64) = (1 : i64) :=
    (i64_mod_two_eq_one_iff_tmod _).mpr h_tmod
  have h_beq : ((l.val[i.toNat]'hi) % 2 == (1 : i64)) = true := by
    rw [beq_iff_eq]; exact h_mod_eq
  have h_and_true :
      (decide ((l.val[i.toNat]'hi) > (0 : i64))
        && ((l.val[i.toNat]'hi) % 2 == (1 : i64))) = true := by
    rw [h_gt, h_beq]; rfl
  -- Mul no-overflow as a Bool fact.
  have h_no_mul_bv :
      BitVec.smulOverflow (l.val[i.toNat]'hi).toBitVec
                          (l.val[i.toNat]'hi).toBitVec = false := by
    have hno' : ¬ (BitVec.smulOverflow (l.val[i.toNat]'hi).toBitVec
                                       (l.val[i.toNat]'hi).toBitVec = true) := hno_mul
    cases hb : BitVec.smulOverflow (l.val[i.toNat]'hi).toBitVec
                                    (l.val[i.toNat]'hi).toBitVec with
    | false => rfl
    | true => exact absurd hb hno'
  -- Add no-overflow as a Bool fact.
  have h_no_add_bv :
      BitVec.saddOverflow acc.toBitVec
        ((l.val[i.toNat]'hi) * (l.val[i.toNat]'hi)).toBitVec = false := by
    have hno' : ¬ (BitVec.saddOverflow acc.toBitVec
                    ((l.val[i.toNat]'hi) * (l.val[i.toNat]'hi)).toBitVec = true) := hno_add
    cases hb : BitVec.saddOverflow acc.toBitVec
                ((l.val[i.toNat]'hi) * (l.val[i.toNat]'hi)).toBitVec with
    | false => rfl
    | true => exact absurd hb hno'
  have h_no_bv_i :
      BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false :=
    usize_add_one_no_bv i h_no_ov_i
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_irem,
             rust_primitives.cmp.gt, rust_primitives.cmp.eq,
             rust_primitives.hax.logical_op.and,
             h_and_true,
             rust_primitives.ops.arith.Mul.mul, h_no_mul_bv,
             rust_primitives.ops.arith.Add.add, h_no_add_bv, h_no_bv_i]

/-- Skip step: when the predicate fails, the function delegates to
    `sum_at l (i+1) acc` without touching `acc`. -/
private theorem sum_at_skip
    (l : RustSlice i64) (i : usize) (acc : i64)
    (hi : i.toNat < l.val.size)
    (h_cond : ¬ (0 < (l.val[i.toNat]'hi).toInt ∧ (l.val[i.toNat]'hi).toInt % 2 = 1)) :
    clever_149_double_the_difference.sum_at l i acc =
      clever_149_double_the_difference.sum_at l (i + 1) acc := by
  conv => lhs; unfold clever_149_double_the_difference.sum_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]
    omega
  have h_idx := slice_index_eq l i hi
  have h_irem := i64_rem_two_eq (l.val[i.toNat]'hi)
  have h_no_bv_i :
      BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false :=
    usize_add_one_no_bv i h_no_ov_i
  -- The combined Bool predicate is false.
  have h_and_false :
      (decide ((l.val[i.toNat]'hi) > (0 : i64))
        && ((l.val[i.toNat]'hi) % 2 == (1 : i64))) = false := by
    by_cases h_pos : 0 < (l.val[i.toNat]'hi).toInt
    · -- Positive ⇒ must violate odd condition.
      have h_odd_no : (l.val[i.toNat]'hi).toInt % 2 ≠ 1 := by
        intro h_eq
        exact h_cond ⟨h_pos, h_eq⟩
      have h_tmod_no : (l.val[i.toNat]'hi).toInt.tmod 2 ≠ 1 := by
        rw [Int.tmod_eq_emod_of_nonneg (Int.le_of_lt h_pos)]
        exact h_odd_no
      have h_mod_ne : ((l.val[i.toNat]'hi) % 2 : i64) ≠ (1 : i64) := by
        intro h_eq
        exact h_tmod_no ((i64_mod_two_eq_one_iff_tmod _).mp h_eq)
      have h_beq_false : ((l.val[i.toNat]'hi) % 2 == (1 : i64)) = false := by
        rw [beq_eq_false_iff_ne]; exact h_mod_ne
      rw [h_beq_false]; exact Bool.and_false _
    · -- Non-positive ⇒ violate `> 0`.
      have h_gt_false : decide ((l.val[i.toNat]'hi) > (0 : i64)) = false := by
        rw [decide_eq_false_iff_not]
        show ¬ ((0 : i64) < (l.val[i.toNat]'hi))
        rw [Int64.lt_iff_toInt_lt, i64_zero_toInt]
        omega
      rw [h_gt_false]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_irem,
             rust_primitives.cmp.gt, rust_primitives.cmp.eq,
             rust_primitives.hax.logical_op.and,
             h_and_false,
             rust_primitives.ops.arith.Add.add, h_no_bv_i]

/-! ## Strong-induction master lemma. -/

private theorem sum_at_correct (l : RustSlice i64)
    (hfit : ∀ k : Nat, k ≤ l.val.size →
              -(2^63 : Int) ≤ dtd_int l k ∧ dtd_int l k < 2^63) :
    ∀ (m : Nat) (i : usize) (acc : i64),
      l.val.size - i.toNat ≤ m →
      i.toNat ≤ l.val.size →
      acc.toInt = dtd_int l i.toNat →
      ∃ r : i64,
        clever_149_double_the_difference.sum_at l i acc = RustM.ok r ∧
        r.toInt = dtd_int l l.val.size := by
  intro m
  induction m with
  | zero =>
    intro i acc hm hi_le hinv
    have hi_eq : i.toNat = l.val.size := by omega
    have hi_ge : l.val.size ≤ i.toNat := by omega
    refine ⟨acc, sum_at_oob l i acc hi_ge, ?_⟩
    rw [hinv, hi_eq]
  | succ m ih =>
    intro i acc hm hi_le hinv
    by_cases hi_ge : l.val.size ≤ i.toNat
    · have hi_eq : i.toNat = l.val.size := by omega
      refine ⟨acc, sum_at_oob l i acc hi_ge, ?_⟩
      rw [hinv, hi_eq]
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_m_le : l.val.size - (i + 1).toNat ≤ m := by rw [h_i1]; omega
      have h_succ_eq := dtd_int_succ l i.toNat hi_lt
      by_cases h_take :
          0 < (l.val[i.toNat]'hi_lt).toInt ∧
          (l.val[i.toNat]'hi_lt).toInt % 2 = 1
      · obtain ⟨h_pos, h_odd⟩ := h_take
        have h_psum_succ :
            dtd_int l (i.toNat + 1) =
              dtd_int l i.toNat
                + (l.val[i.toNat]'hi_lt).toInt * (l.val[i.toNat]'hi_lt).toInt := by
          rw [h_succ_eq]
          rw [if_pos ⟨h_pos, h_odd⟩]
        have h_fit_succ := hfit (i.toNat + 1) (by omega)
        -- Per-element multiplication overflow is dominated by the prefix
        -- bound at k+1, using non-negativity of `dtd_int l i.toNat`.
        have h_sq_nonneg :
            0 ≤ (l.val[i.toNat]'hi_lt).toInt * (l.val[i.toNat]'hi_lt).toInt :=
          mul_self_nonneg_int _
        have h_psum_i_nonneg : 0 ≤ dtd_int l i.toNat := dtd_int_nonneg l i.toNat
        have h_sq_lt :
            (l.val[i.toNat]'hi_lt).toInt * (l.val[i.toNat]'hi_lt).toInt < 2^63 := by
          have hbnd := h_fit_succ.2
          rw [h_psum_succ] at hbnd
          omega
        have h_sq_ge :
            -(2^63 : Int) ≤
              (l.val[i.toNat]'hi_lt).toInt * (l.val[i.toNat]'hi_lt).toInt := by
          omega
        have hno_mul :
            ¬ Int64.mulOverflow (l.val[i.toNat]'hi_lt) (l.val[i.toNat]'hi_lt) := by
          intro hov
          rw [Int64.mulOverflow_iff] at hov
          rcases hov with hov_pos | hov_neg
          · omega
          · omega
        -- Accumulator addition overflow dominated by prefix bound at k+1.
        have h_acc_plus_sq_toInt_eq :
            acc.toInt + (l.val[i.toNat]'hi_lt).toInt * (l.val[i.toNat]'hi_lt).toInt
              = dtd_int l (i.toNat + 1) := by
          rw [h_psum_succ, hinv]
        have hno_add :
            ¬ Int64.addOverflow acc
                ((l.val[i.toNat]'hi_lt) * (l.val[i.toNat]'hi_lt)) := by
          intro hov
          rw [Int64.addOverflow_iff] at hov
          rw [Int64.toInt_mul_of_not_mulOverflow hno_mul] at hov
          rw [h_acc_plus_sq_toInt_eq] at hov
          rcases hov with hov_pos | hov_neg
          · have := h_fit_succ.2; omega
          · have := h_fit_succ.1; omega
        have h_step := sum_at_take l i acc hi_lt h_pos h_odd hno_mul hno_add
        have h_new_inv :
            (acc + (l.val[i.toNat]'hi_lt) * (l.val[i.toNat]'hi_lt)).toInt
              = dtd_int l (i + 1).toNat := by
          rw [h_i1]
          rw [Int64.toInt_add_of_not_addOverflow hno_add]
          rw [Int64.toInt_mul_of_not_mulOverflow hno_mul]
          exact h_acc_plus_sq_toInt_eq
        obtain ⟨r, h_rec_eq, h_r_int⟩ :=
          ih (i + 1)
            (acc + (l.val[i.toNat]'hi_lt) * (l.val[i.toNat]'hi_lt))
            h_m_le h_i1_le h_new_inv
        refine ⟨r, ?_, h_r_int⟩
        rw [h_step]; exact h_rec_eq
      · -- Skip branch.
        have h_psum_succ_skip :
            dtd_int l (i.toNat + 1) = dtd_int l i.toNat := by
          rw [h_succ_eq]
          rw [if_neg]
          · omega
          · exact h_take
        have h_step := sum_at_skip l i acc hi_lt h_take
        have h_new_inv : acc.toInt = dtd_int l (i + 1).toNat := by
          rw [hinv, h_i1, h_psum_succ_skip]
        obtain ⟨r, h_rec_eq, h_r_int⟩ :=
          ih (i + 1) acc h_m_le h_i1_le h_new_inv
        refine ⟨r, ?_, h_r_int⟩
        rw [h_step]; exact h_rec_eq

/-! ## Top-level theorems. -/

/-- Empty-slice boundary contract. -/
theorem empty_returns_zero
    (numbers : RustSlice i64) (hempty : numbers.val.size = 0) :
    clever_149_double_the_difference.double_the_difference numbers
      = RustM.ok (0 : i64) := by
  unfold clever_149_double_the_difference.double_the_difference
  have hi_ge : numbers.val.size ≤ (0 : usize).toNat := by
    rw [usize_zero_toNat, hempty]; omega
  exact sum_at_oob numbers (0 : usize) (0 : i64) hi_ge

/-- Singleton positivity-fail: a singleton whose element is non-positive
    returns `0`. -/
theorem singleton_non_positive_returns_zero
    (numbers : RustSlice i64) (n : i64)
    (h_size : numbers.val.size = 1)
    (h_first : ∀ (h : 0 < numbers.val.size), numbers.val[0]'h = n)
    (h_nonpos : n.toInt ≤ 0) :
    clever_149_double_the_difference.double_the_difference numbers
      = RustM.ok (0 : i64) := by
  unfold clever_149_double_the_difference.double_the_difference
  have h0_lt : (0 : usize).toNat < numbers.val.size := by
    rw [usize_zero_toNat, h_size]; omega
  have h_pos_size : 0 < numbers.val.size := by rw [h_size]; omega
  -- (0 : usize).toNat = 0 by `rfl`, so the dependent index matches by defeq.
  have h_first_eq : (numbers.val[(0 : usize).toNat]'h0_lt) = n :=
    h_first h_pos_size
  -- Skip branch: predicate fails because n.toInt ≤ 0.
  have h_cond_false :
      ¬ (0 < (numbers.val[(0 : usize).toNat]'h0_lt).toInt ∧
         (numbers.val[(0 : usize).toNat]'h0_lt).toInt % 2 = 1) := by
    rintro ⟨h_pos, _⟩
    rw [h_first_eq] at h_pos
    omega
  have h_step := sum_at_skip numbers (0 : usize) (0 : i64) h0_lt h_cond_false
  rw [h_step]
  -- After step, we're at (i+1) = 1, which equals val.size, so OOB.
  have h_no_ov : (0 : usize).toNat + 1 < 2 ^ 64 := by
    rw [usize_zero_toNat]; decide
  have h_i1_toNat : ((0 : usize) + 1).toNat = 1 := by
    rw [usize_add_one_toNat (0 : usize) h_no_ov, usize_zero_toNat]
  have h_i1_ge : numbers.val.size ≤ ((0 : usize) + 1).toNat := by
    rw [h_i1_toNat, h_size]; omega
  exact sum_at_oob numbers ((0 : usize) + 1) (0 : i64) h_i1_ge

/-- Singleton parity-fail: a singleton with an even element returns `0`. -/
theorem singleton_even_returns_zero
    (numbers : RustSlice i64) (n : i64)
    (h_size : numbers.val.size = 1)
    (h_first : ∀ (h : 0 < numbers.val.size), numbers.val[0]'h = n)
    (h_even : n.toInt % 2 = 0) :
    clever_149_double_the_difference.double_the_difference numbers
      = RustM.ok (0 : i64) := by
  unfold clever_149_double_the_difference.double_the_difference
  have h0_lt : (0 : usize).toNat < numbers.val.size := by
    rw [usize_zero_toNat, h_size]; omega
  have h_pos_size : 0 < numbers.val.size := by rw [h_size]; omega
  have h_first_eq : (numbers.val[(0 : usize).toNat]'h0_lt) = n :=
    h_first h_pos_size
  -- Skip branch: predicate fails because % 2 = 0 ≠ 1.
  have h_cond_false :
      ¬ (0 < (numbers.val[(0 : usize).toNat]'h0_lt).toInt ∧
         (numbers.val[(0 : usize).toNat]'h0_lt).toInt % 2 = 1) := by
    rintro ⟨_, h_odd⟩
    rw [h_first_eq] at h_odd
    omega
  have h_step := sum_at_skip numbers (0 : usize) (0 : i64) h0_lt h_cond_false
  rw [h_step]
  have h_no_ov : (0 : usize).toNat + 1 < 2 ^ 64 := by
    rw [usize_zero_toNat]; decide
  have h_i1_toNat : ((0 : usize) + 1).toNat = 1 := by
    rw [usize_add_one_toNat (0 : usize) h_no_ov, usize_zero_toNat]
  have h_i1_ge : numbers.val.size ≤ ((0 : usize) + 1).toNat := by
    rw [h_i1_toNat, h_size]; omega
  exact sum_at_oob numbers ((0 : usize) + 1) (0 : i64) h_i1_ge

/-- Singleton positive-odd take: a positive odd singleton returns `n^2`. -/
theorem singleton_positive_odd_returns_square
    (numbers : RustSlice i64) (n : i64)
    (h_size : numbers.val.size = 1)
    (h_first : ∀ (h : 0 < numbers.val.size), numbers.val[0]'h = n)
    (h_pos : 0 < n.toInt) (h_odd : n.toInt % 2 = 1)
    (h_fit : n.toInt * n.toInt < 2 ^ 63) :
    ∃ r : i64,
      clever_149_double_the_difference.double_the_difference numbers
        = RustM.ok r ∧
      r.toInt = n.toInt * n.toInt := by
  unfold clever_149_double_the_difference.double_the_difference
  have h0_lt : (0 : usize).toNat < numbers.val.size := by
    rw [usize_zero_toNat, h_size]; omega
  have h_pos_size : 0 < numbers.val.size := by rw [h_size]; omega
  have h_first_eq : (numbers.val[(0 : usize).toNat]'h0_lt) = n :=
    h_first h_pos_size
  -- Take branch: predicate holds.
  have h_pos' : 0 < (numbers.val[(0 : usize).toNat]'h0_lt).toInt := by
    rw [h_first_eq]; exact h_pos
  have h_odd' : (numbers.val[(0 : usize).toNat]'h0_lt).toInt % 2 = 1 := by
    rw [h_first_eq]; exact h_odd
  -- No mul overflow.
  have h_sq_nonneg : 0 ≤ n.toInt * n.toInt := mul_self_nonneg_int _
  have h_sq_ge : -(2 ^ 63 : Int) ≤ n.toInt * n.toInt := by omega
  have hno_mul :
      ¬ Int64.mulOverflow (numbers.val[(0 : usize).toNat]'h0_lt)
                          (numbers.val[(0 : usize).toNat]'h0_lt) := by
    intro hov
    rw [Int64.mulOverflow_iff] at hov
    rw [h_first_eq] at hov
    rcases hov with hov_pos | hov_neg
    · omega
    · omega
  -- No add overflow on `0 + n*n = n*n`.
  have h_zero_toInt : (0 : i64).toInt = 0 := i64_zero_toInt
  have hno_add :
      ¬ Int64.addOverflow (0 : i64)
          ((numbers.val[(0 : usize).toNat]'h0_lt)
            * (numbers.val[(0 : usize).toNat]'h0_lt)) := by
    intro hov
    rw [Int64.addOverflow_iff] at hov
    rw [Int64.toInt_mul_of_not_mulOverflow hno_mul] at hov
    rw [h_zero_toInt, h_first_eq] at hov
    rcases hov with hov_pos | hov_neg
    · -- 0 + n*n ≥ 2^63, contradicts h_fit
      have : (0 : Int) + n.toInt * n.toInt = n.toInt * n.toInt := by omega
      rw [this] at hov_pos
      omega
    · -- 0 + n*n < -2^63, contradicts h_sq_ge
      have : (0 : Int) + n.toInt * n.toInt = n.toInt * n.toInt := by omega
      rw [this] at hov_neg
      omega
  have h_step :=
    sum_at_take numbers (0 : usize) (0 : i64) h0_lt h_pos' h_odd' hno_mul hno_add
  rw [h_step]
  -- After step we are at (0+1, 0 + n*n). Show OOB returns `0 + n*n`.
  have h_no_ov : (0 : usize).toNat + 1 < 2 ^ 64 := by
    rw [usize_zero_toNat]; decide
  have h_i1_toNat : ((0 : usize) + 1).toNat = 1 := by
    rw [usize_add_one_toNat (0 : usize) h_no_ov, usize_zero_toNat]
  have h_i1_ge : numbers.val.size ≤ ((0 : usize) + 1).toNat := by
    rw [h_i1_toNat, h_size]; omega
  have h_oob :=
    sum_at_oob numbers ((0 : usize) + 1)
      ((0 : i64) + (numbers.val[(0 : usize).toNat]'h0_lt)
        * (numbers.val[(0 : usize).toNat]'h0_lt)) h_i1_ge
  refine ⟨(0 : i64)
            + (numbers.val[(0 : usize).toNat]'h0_lt)
              * (numbers.val[(0 : usize).toNat]'h0_lt), h_oob, ?_⟩
  -- toInt of `0 + n*n` equals `n.toInt * n.toInt`.
  rw [Int64.toInt_add_of_not_addOverflow hno_add]
  rw [Int64.toInt_mul_of_not_mulOverflow hno_mul]
  rw [h_zero_toInt, h_first_eq]
  omega

/-- Main functional-correctness postcondition. -/
theorem matches_spec
    (numbers : RustSlice i64)
    (hfit : ∀ k : Nat, k ≤ numbers.val.size →
              -(2 ^ 63 : Int) ≤ dtd_int numbers k
              ∧ dtd_int numbers k < 2 ^ 63) :
    ∃ r : i64,
      clever_149_double_the_difference.double_the_difference numbers
        = RustM.ok r ∧
      r.toInt = dtd_int numbers numbers.val.size := by
  unfold clever_149_double_the_difference.double_the_difference
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_inv : (0 : i64).toInt = dtd_int numbers (0 : usize).toNat := by
    rw [h_zero_toNat, i64_zero_toInt]; rfl
  have h_m_le : numbers.val.size - (0 : usize).toNat ≤ numbers.val.size := by
    rw [h_zero_toNat]; omega
  have h_i_le : (0 : usize).toNat ≤ numbers.val.size := by
    rw [h_zero_toNat]; omega
  exact sum_at_correct numbers hfit numbers.val.size (0 : usize) (0 : i64)
    h_m_le h_i_le h_inv

end Clever_149_double_the_differenceObligations
