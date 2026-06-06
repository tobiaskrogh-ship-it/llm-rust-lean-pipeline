-- Companion obligations file for the `clever_003_below_zero` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_003_below_zero

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_003_below_zeroObligations

/-! ## Specification of the prefix-sum oracle

`below_zero ops` should return `true` iff some non-empty prefix of `ops`
has a strictly negative integer sum. We compute the sum in `Int` (matching
the `i128` running accumulator used by `spec_below_zero` in the Rust
source's `tests` module) so the spec itself cannot overflow on any input
the function under verification can legally accept. -/

/-- Integer-valued prefix sum:
    `prefix_sum_int ops k = Σ_{i<k} (ops.val[i]).toInt`.

    The `dite` on `k < ops.val.size` makes the definition total — in actual
    use, every theorem below quantifies `k` so that `k ≤ ops.val.size`,
    keeping the index in range. -/
private def prefix_sum_int (ops : RustSlice i64) : Nat → Int
  | 0       => 0
  | k + 1   =>
      prefix_sum_int ops k +
        (if h : k < ops.val.size then (ops.val[k]'h).toInt else 0)

/-! ## Helpers (transferred from `contains_u64` reference) -/

/-- `RustM.ok x >>= f = f x`. The library's `pure_bind` simp lemma only
    matches literal `Pure.pure`; this rewrite handles the `RustM.ok` form
    produced after reducing definitions. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

/-- `(0 : i64).toInt = 0`. Used to bridge the Rust `<? 0` comparison to
    the integer `< 0` predicate on prefix sums. -/
private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide

/-- Step of `prefix_sum_int`: when `k < ops.val.size`, the `dite` reduces
    to the `Int`-valued addition. -/
private theorem prefix_sum_int_succ
    (ops : RustSlice i64) (k : Nat) (hk : k < ops.val.size) :
    prefix_sum_int ops (k + 1) =
      prefix_sum_int ops k + (ops.val[k]'hk).toInt := by
  show prefix_sum_int ops k
        + (if h : k < ops.val.size then (ops.val[k]'h).toInt else 0)
       = prefix_sum_int ops k + (ops.val[k]'hk).toInt
  rw [dif_pos hk]

/-! ## Step lemmas for `below_zero_at`

The three branches of the recursive body, packaged so the strong-induction
work in `sound_aux` / `complete_aux` can rewrite the goal directly without
re-expanding the `do`-block at every site.  All three lemmas follow the
same `unfold + simp only` recipe as the `contains_u64` reference.
-/

/-- Out-of-bounds step: when `i.toNat ≥ ops.val.size`, the function
    returns `RustM.ok false`. -/
private theorem below_zero_at_oob (ops : RustSlice i64) (i : usize) (balance : i64)
    (hi : ops.val.size ≤ i.toNat) :
    clever_003_below_zero.below_zero_at ops i balance = RustM.ok false := by
  conv => lhs; unfold clever_003_below_zero.below_zero_at
  have h_ofNat : (USize64.ofNat ops.val.size).toNat = ops.val.size :=
    USize64.toNat_ofNat_of_lt' ops.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat ops.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- Found step (returns `true`): when `i.toNat < ops.val.size`, the
    signed addition `balance + ops[i]` does not overflow, and the
    resulting `new_balance` is strictly negative, the function returns
    `RustM.ok true`. -/
private theorem below_zero_at_found (ops : RustSlice i64) (i : usize) (balance : i64)
    (hi : i.toNat < ops.val.size)
    (hno : ¬ Int64.addOverflow balance (ops.val[i.toNat]'hi))
    (hneg : (balance + ops.val[i.toNat]'hi).toInt < 0) :
    clever_003_below_zero.below_zero_at ops i balance = RustM.ok true := by
  conv => lhs; unfold clever_003_below_zero.below_zero_at
  have h_ofNat : (USize64.ofNat ops.val.size).toNat = ops.val.size :=
    USize64.toNat_ofNat_of_lt' ops.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat ops.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (ops[i]_? : RustM i64) = RustM.ok (ops.val[i.toNat]'hi) := by
    show (if h : i.toNat < ops.val.size then pure (ops.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (ops.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
  have h_no_bv :
      BitVec.saddOverflow balance.toBitVec (ops.val[i.toNat]'hi).toBitVec = false := by
    have hno' : ¬ (BitVec.saddOverflow balance.toBitVec
                                       (ops.val[i.toNat]'hi).toBitVec = true) := hno
    cases hb : BitVec.saddOverflow balance.toBitVec (ops.val[i.toNat]'hi).toBitVec with
    | false => rfl
    | true => exact absurd hb hno'
  have h_add :
      (balance +? (ops.val[i.toNat]'hi) : RustM i64) =
        RustM.ok (balance + ops.val[i.toNat]'hi) := by
    show (rust_primitives.ops.arith.Add.add balance (ops.val[i.toNat]'hi) : RustM i64) = _
    show (if BitVec.saddOverflow balance.toBitVec (ops.val[i.toNat]'hi).toBitVec then
            (.fail .integerOverflow : RustM i64)
          else pure (balance + ops.val[i.toNat]'hi)) = _
    rw [h_no_bv]; rfl
  have h_neg_cond :
      decide ((balance + ops.val[i.toNat]'hi) < (0 : i64)) = true := by
    rw [decide_eq_true_iff]
    rw [Int64.lt_iff_toInt_lt, i64_zero_toInt]
    exact hneg
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_add,
             rust_primitives.cmp.lt, h_neg_cond]
  rfl

/-- Recursion step: when `i.toNat < ops.val.size`, the signed addition
    doesn't overflow, and the resulting `new_balance` is non-negative,
    the function delegates to `below_zero_at ops (i+1) new_balance`. -/
private theorem below_zero_at_recurse
    (ops : RustSlice i64) (i : usize) (balance : i64)
    (hi : i.toNat < ops.val.size)
    (hno : ¬ Int64.addOverflow balance (ops.val[i.toNat]'hi))
    (hnneg : 0 ≤ (balance + ops.val[i.toNat]'hi).toInt) :
    clever_003_below_zero.below_zero_at ops i balance =
      clever_003_below_zero.below_zero_at ops (i + 1)
        (balance + ops.val[i.toNat]'hi) := by
  conv => lhs; unfold clever_003_below_zero.below_zero_at
  have h_ofNat : (USize64.ofNat ops.val.size).toNat = ops.val.size :=
    USize64.toNat_ofNat_of_lt' ops.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat ops.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (ops[i]_? : RustM i64) = RustM.ok (ops.val[i.toNat]'hi) := by
    show (if h : i.toNat < ops.val.size then pure (ops.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (ops.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
  have h_no_bv :
      BitVec.saddOverflow balance.toBitVec (ops.val[i.toNat]'hi).toBitVec = false := by
    have hno' : ¬ (BitVec.saddOverflow balance.toBitVec
                                       (ops.val[i.toNat]'hi).toBitVec = true) := hno
    cases hb : BitVec.saddOverflow balance.toBitVec (ops.val[i.toNat]'hi).toBitVec with
    | false => rfl
    | true => exact absurd hb hno'
  have h_add :
      (balance +? (ops.val[i.toNat]'hi) : RustM i64) =
        RustM.ok (balance + ops.val[i.toNat]'hi) := by
    show (rust_primitives.ops.arith.Add.add balance (ops.val[i.toNat]'hi) : RustM i64) = _
    show (if BitVec.saddOverflow balance.toBitVec (ops.val[i.toNat]'hi).toBitVec then
            (.fail .integerOverflow : RustM i64)
          else pure (balance + ops.val[i.toNat]'hi)) = _
    rw [h_no_bv]; rfl
  have h_nneg_cond :
      decide ((balance + ops.val[i.toNat]'hi) < (0 : i64)) = false := by
    rw [decide_eq_false_iff_not]
    rw [Int64.lt_iff_toInt_lt, i64_zero_toInt]
    omega
  have h_size_lt : ops.val.size < 2^64 := ops.size_lt_usizeSize
  have h_no_overflow_i : i.toNat + 1 < 2^64 := by omega
  have h_no_bv_i :
      BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
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
             rust_primitives.ops.arith.Add.add, h_no_bv, h_no_bv_i,
             rust_primitives.cmp.lt, h_nneg_cond]

/-! ## Soundness strong-induction lemma

If `below_zero_at ops i balance` evaluates to `RustM.ok true` and the
balance is the prefix sum up to `i`, then some prefix of `ops` strictly
past `i` has negative integer sum.  Induction on the measure
`ops.val.size - i.toNat`. -/

private theorem sound_aux (ops : RustSlice i64) :
    ∀ (m : Nat) (i : usize) (balance : i64),
      ops.val.size - i.toNat ≤ m →
      balance.toInt = prefix_sum_int ops i.toNat →
      clever_003_below_zero.below_zero_at ops i balance = RustM.ok true →
      ∃ k : Nat, i.toNat < k ∧ k ≤ ops.val.size ∧ prefix_sum_int ops k < 0 := by
  intro m
  induction m with
  | zero =>
    intro i balance hm hinv hat
    -- `ops.val.size - i.toNat = 0` ⇒ `i.toNat ≥ size`, so `below_zero_at = ok false`.
    have hi_ge : ops.val.size ≤ i.toNat := by omega
    have h_false := below_zero_at_oob ops i balance hi_ge
    rw [h_false] at hat
    exact absurd hat (by decide)
  | succ m ih =>
    intro i balance hm hinv hat
    by_cases hi_ge : ops.val.size ≤ i.toNat
    · -- OOB: returns false, contradicting `ok true`.
      have h_false := below_zero_at_oob ops i balance hi_ge
      rw [h_false] at hat
      exact absurd hat (by decide)
    · have hi_lt : i.toNat < ops.val.size := Nat.lt_of_not_le hi_ge
      -- Extract the no-overflow witness from the fact that the function returned `ok true`.
      -- We argue by contradiction: if the add overflows, the function fails.
      by_cases hov : Int64.addOverflow balance (ops.val[i.toNat]'hi_lt)
      · -- Add overflows ⇒ function returns `fail`. But hypothesis says `ok true`.
        exfalso
        have h_size_lt : ops.val.size < 2^64 := ops.size_lt_usizeSize
        have h_ofNat : (USize64.ofNat ops.val.size).toNat = ops.val.size :=
          USize64.toNat_ofNat_of_lt' h_size_lt
        have h_cond : decide (USize64.ofNat ops.val.size ≤ i) = false := by
          rw [decide_eq_false_iff_not]
          intro hle
          rw [USize64.le_iff_toNat_le, h_ofNat] at hle
          omega
        have h_idx : (ops[i]_? : RustM i64) = RustM.ok (ops.val[i.toNat]'hi_lt) := by
          show (if h : i.toNat < ops.val.size then pure (ops.val[i]) else .fail .arrayOutOfBounds)
              = RustM.ok (ops.val[i.toNat]'hi_lt)
          rw [dif_pos hi_lt]; rfl
        have h_bv_true :
            BitVec.saddOverflow balance.toBitVec (ops.val[i.toNat]'hi_lt).toBitVec = true := hov
        have h_add_fail :
            (balance +? (ops.val[i.toNat]'hi_lt) : RustM i64) =
              RustM.fail Error.integerOverflow := by
          show (rust_primitives.ops.arith.Add.add balance (ops.val[i.toNat]'hi_lt)
                : RustM i64) = _
          show (if BitVec.saddOverflow balance.toBitVec (ops.val[i.toNat]'hi_lt).toBitVec
                then (.fail .integerOverflow : RustM i64)
                else pure (balance + ops.val[i.toNat]'hi_lt)) = _
          rw [h_bv_true]; rfl
        conv at hat => lhs; unfold clever_003_below_zero.below_zero_at
        simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
                   rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
                   h_cond, Bool.false_eq_true, ↓reduceIte,
                   h_idx, h_add_fail] at hat
        -- `hat` now says `RustM.fail … >>= … = RustM.ok true`.  Reduce the bind
        -- explicitly and finish by injection-into-`none`.
        simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, Option.bind] at hat
        cases hat
      · -- Add does not overflow. The toInt equation propagates the invariant.
        have h_new_toInt :
            (balance + ops.val[i.toNat]'hi_lt).toInt =
              balance.toInt + (ops.val[i.toNat]'hi_lt).toInt :=
          Int64.toInt_add_of_not_addOverflow hov
        have h_new_eq_psum :
            (balance + ops.val[i.toNat]'hi_lt).toInt =
              prefix_sum_int ops (i.toNat + 1) := by
          rw [h_new_toInt, hinv]
          rw [prefix_sum_int_succ ops i.toNat hi_lt]
        by_cases hneg : (balance + ops.val[i.toNat]'hi_lt).toInt < 0
        · -- The witness is `k = i.toNat + 1`.
          refine ⟨i.toNat + 1, ?_, ?_, ?_⟩
          · omega
          · omega
          · rw [← h_new_eq_psum]; exact hneg
        · -- Non-negative ⇒ function recurses; apply IH.
          have hnneg : 0 ≤ (balance + ops.val[i.toNat]'hi_lt).toInt := by omega
          have h_rec := below_zero_at_recurse ops i balance hi_lt hov hnneg
          rw [h_rec] at hat
          -- Compute (i+1).toNat = i.toNat + 1.
          have h_size_lt : ops.val.size < 2^64 := ops.size_lt_usizeSize
          have h_no_ov_i : i.toNat + 1 < 2^64 := by omega
          have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
          -- Apply IH with reduced measure and the same prefix-sum invariant.
          have h_inv' :
              (balance + ops.val[i.toNat]'hi_lt).toInt =
                prefix_sum_int ops (i + 1).toNat := by
            rw [h_i1]; exact h_new_eq_psum
          have h_m_le : ops.val.size - (i + 1).toNat ≤ m := by
            rw [h_i1]; omega
          obtain ⟨k, hk_lo, hk_hi, hk_neg⟩ :=
            ih (i + 1) (balance + ops.val[i.toNat]'hi_lt) h_m_le h_inv' hat
          refine ⟨k, ?_, hk_hi, hk_neg⟩
          rw [h_i1] at hk_lo
          omega

/-! ## Completeness strong-induction lemma

Given a non-empty prefix whose integer sum is strictly negative, the
running balance must overflow or reach below zero. Under the no-overflow
precondition, the latter holds and the function returns `RustM.ok true`. -/

private theorem complete_aux (ops : RustSlice i64) :
    ∀ (m : Nat) (i : usize) (balance : i64),
      ops.val.size - i.toNat ≤ m →
      balance.toInt = prefix_sum_int ops i.toNat →
      (∀ k : Nat, i.toNat ≤ k → k ≤ ops.val.size →
          -(2^63 : Int) ≤ prefix_sum_int ops k
          ∧ prefix_sum_int ops k < 2^63) →
      (∃ k : Nat, i.toNat < k ∧ k ≤ ops.val.size ∧ prefix_sum_int ops k < 0) →
      clever_003_below_zero.below_zero_at ops i balance = RustM.ok true := by
  intro m
  induction m with
  | zero =>
    -- ops.val.size - i.toNat = 0 ⇒ no witness k > i.toNat with k ≤ size exists.
    intro i balance hm hinv hfit ⟨k, hk_lo, hk_hi, _⟩
    omega
  | succ m ih =>
    intro i balance hm hinv hfit ⟨k, hk_lo, hk_hi, hk_neg⟩
    -- Witness `k` forces `i.toNat < size`.
    have hi_lt : i.toNat < ops.val.size := by omega
    -- Use `hfit` on `i.toNat + 1` (which is ≤ size since `k > i.toNat` and `k ≤ size`).
    have h_i1_le_size : i.toNat + 1 ≤ ops.val.size := by omega
    have h_fit_succ := hfit (i.toNat + 1) (by omega) h_i1_le_size
    -- Bound the toInt of the prospective new_balance via the prefix-sum invariant.
    have h_psum_succ :
        prefix_sum_int ops (i.toNat + 1) =
          balance.toInt + (ops.val[i.toNat]'hi_lt).toInt := by
      rw [prefix_sum_int_succ ops i.toNat hi_lt, hinv]
    -- No overflow on `balance + ops[i]`.
    have hno_ov : ¬ Int64.addOverflow balance (ops.val[i.toNat]'hi_lt) := by
      intro hov
      rw [Int64.addOverflow_iff] at hov
      rw [← h_psum_succ] at hov
      rcases hov with hov_pos | hov_neg
      · have := h_fit_succ.2; omega
      · have := h_fit_succ.1; omega
    -- toInt of new_balance equals prefix_sum_int ops (i.toNat + 1).
    have h_new_toInt :
        (balance + ops.val[i.toNat]'hi_lt).toInt =
          balance.toInt + (ops.val[i.toNat]'hi_lt).toInt :=
      Int64.toInt_add_of_not_addOverflow hno_ov
    have h_new_eq_psum :
        (balance + ops.val[i.toNat]'hi_lt).toInt =
          prefix_sum_int ops (i.toNat + 1) := by
      rw [h_new_toInt]; exact h_psum_succ.symm
    by_cases hneg : (balance + ops.val[i.toNat]'hi_lt).toInt < 0
    · -- new_balance < 0 ⇒ `below_zero_at` returns `ok true` directly.
      exact below_zero_at_found ops i balance hi_lt hno_ov hneg
    · -- new_balance ≥ 0 ⇒ recurse. The witness must lie strictly past `i+1`.
      have hnneg : 0 ≤ (balance + ops.val[i.toNat]'hi_lt).toInt := by omega
      -- prefix_sum_int ops (i.toNat + 1) ≥ 0, so witness k ≠ i.toNat + 1.
      have h_k_gt : k > i.toNat + 1 := by
        rcases Nat.lt_or_ge (i.toNat + 1) k with hgt | hle
        · exact hgt
        · -- hle : k ≤ i.toNat + 1. With hk_lo : i.toNat < k, k = i.toNat + 1.
          exfalso
          have hk_eq : k = i.toNat + 1 := by omega
          rw [hk_eq] at hk_neg
          rw [← h_new_eq_psum] at hk_neg
          omega
      have h_rec := below_zero_at_recurse ops i balance hi_lt hno_ov hnneg
      rw [h_rec]
      -- Apply IH with (i+1, new_balance).
      have h_size_lt : ops.val.size < 2^64 := ops.size_lt_usizeSize
      have h_no_ov_i : i.toNat + 1 < 2^64 := by omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_inv' :
          (balance + ops.val[i.toNat]'hi_lt).toInt =
            prefix_sum_int ops (i + 1).toNat := by
        rw [h_i1]; exact h_new_eq_psum
      have h_m_le : ops.val.size - (i + 1).toNat ≤ m := by
        rw [h_i1]; omega
      have h_fit' :
          ∀ k' : Nat, (i + 1).toNat ≤ k' → k' ≤ ops.val.size →
            -(2^63 : Int) ≤ prefix_sum_int ops k' ∧ prefix_sum_int ops k' < 2^63 := by
        intro k' hk'_lo hk'_hi
        apply hfit k' _ hk'_hi
        rw [h_i1] at hk'_lo
        omega
      have h_exists' :
          ∃ k' : Nat, (i + 1).toNat < k' ∧ k' ≤ ops.val.size ∧ prefix_sum_int ops k' < 0 := by
        refine ⟨k, ?_, hk_hi, hk_neg⟩
        rw [h_i1]; exact h_k_gt
      exact ih (i + 1) (balance + ops.val[i.toNat]'hi_lt) h_m_le h_inv' h_fit' h_exists'

/-! ## Top-level theorems

Each of the three obligations specialises an aux lemma above at
`i := (0 : usize), balance := (0 : i64)`, where the prefix-sum invariant
`(0 : i64).toInt = 0 = prefix_sum_int ops 0` holds by definition. -/

/-- Empty-slice boundary contract. -/
theorem empty_returns_false (ops : RustSlice i64) (hempty : ops.val.size = 0) :
    clever_003_below_zero.below_zero ops = RustM.ok false := by
  unfold clever_003_below_zero.below_zero
  have hi_ge : ops.val.size ≤ (0 : usize).toNat := by
    show ops.val.size ≤ 0
    omega
  exact below_zero_at_oob ops (0 : usize) (0 : i64) hi_ge

/-- Soundness (no-false-positive). -/
theorem sound_no_false_positive (ops : RustSlice i64)
    (h : clever_003_below_zero.below_zero ops = RustM.ok true) :
    ∃ k : Nat, 1 ≤ k ∧ k ≤ ops.val.size ∧ prefix_sum_int ops k < 0 := by
  unfold clever_003_below_zero.below_zero at h
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_inv : (0 : i64).toInt = prefix_sum_int ops (0 : usize).toNat := by
    rw [h_zero_toNat, i64_zero_toInt]; rfl
  obtain ⟨k, hk_lo, hk_hi, hk_neg⟩ :=
    sound_aux ops ops.val.size (0 : usize) (0 : i64)
      (by rw [h_zero_toNat]; omega) h_inv h
  refine ⟨k, ?_, hk_hi, hk_neg⟩
  rw [h_zero_toNat] at hk_lo
  omega

/-- Completeness (no-false-negative). -/
theorem complete_no_false_negative (ops : RustSlice i64)
    (hfit : ∀ k : Nat, k ≤ ops.val.size →
              -(2^63 : Int) ≤ prefix_sum_int ops k
              ∧ prefix_sum_int ops k < 2^63)
    (h : ∃ k : Nat, 1 ≤ k ∧ k ≤ ops.val.size ∧ prefix_sum_int ops k < 0) :
    clever_003_below_zero.below_zero ops = RustM.ok true := by
  unfold clever_003_below_zero.below_zero
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_inv : (0 : i64).toInt = prefix_sum_int ops (0 : usize).toNat := by
    rw [h_zero_toNat, i64_zero_toInt]; rfl
  have h_fit' :
      ∀ k : Nat, (0 : usize).toNat ≤ k → k ≤ ops.val.size →
        -(2^63 : Int) ≤ prefix_sum_int ops k ∧ prefix_sum_int ops k < 2^63 := by
    intro k _ hk_hi
    exact hfit k hk_hi
  obtain ⟨k, hk_lo, hk_hi, hk_neg⟩ := h
  have h_exists :
      ∃ k : Nat, (0 : usize).toNat < k ∧ k ≤ ops.val.size ∧ prefix_sum_int ops k < 0 := by
    refine ⟨k, ?_, hk_hi, hk_neg⟩
    rw [h_zero_toNat]; omega
  exact complete_aux ops ops.val.size (0 : usize) (0 : i64)
    (by rw [h_zero_toNat]; omega) h_inv h_fit' h_exists

end Clever_003_below_zeroObligations
