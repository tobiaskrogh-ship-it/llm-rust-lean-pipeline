-- Companion obligations file for the `clever_070_triangle_area` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_070_triangle_area

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_070_triangle_areaObligations

/-! ## i64 ⇄ Int bridge helpers -/

private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide
private theorem i64_one_toInt : (1 : i64).toInt = 1 := by decide
private theorem i64_two_toInt : (2 : i64).toInt = 2 := by decide
private theorem i64_neg_one_toInt : (-1 : i64).toInt = -1 := by decide

private theorem i64_toInt_lt (x : i64) : x.toInt < 2 ^ 63 := by
  have h := Int64.toInt_lt x; simpa using h

private theorem i64_toInt_ge (x : i64) : -(2 ^ 63 : Int) ≤ x.toInt := by
  have h := Int64.le_toInt x; simpa using h

private theorem h63_eq : (2 : Int) ^ (64 - 1) = 2 ^ 63 := by decide

private theorem int64_min_toInt : Int64.minValue.toInt = -9223372036854775808 := by decide

/-! ## Generic Int identities for the Heron chain -/

private theorem int_le_self_mul {a b : Int} (ha : 0 ≤ a) (hb : 1 ≤ b) : a ≤ a * b :=
  calc a = a * 1 := (Int.mul_one a).symm
    _ ≤ a * b := Int.mul_le_mul_of_nonneg_left hb ha

/-- `(4 * u) * (4 * u) = 16 * (u * u)`. -/
private theorem int_four_mul_sq (u : Int) : (4 * u) * (4 * u) = 16 * (u * u) := by
  -- (4 * u) * (4 * u) = 4 * (u * (4 * u))
  rw [Int.mul_assoc 4 u (4 * u)]
  -- = 4 * ((4 * u) * u)
  rw [Int.mul_comm u (4 * u)]
  -- = 4 * (4 * (u * u))
  rw [Int.mul_assoc 4 u u]
  -- = (4 * 4) * (u * u) = 16 * (u * u)
  rw [← Int.mul_assoc 4 4 (u * u)]
  show (16 : Int) * (u * u) = 16 * (u * u)
  rfl

/-- `(4 * u + 4) * (4 * u + 4) = 16 * ((u + 1) * (u + 1))`. -/
private theorem int_four_succ_sq (u : Int) :
    (4 * u + 4) * (4 * u + 4) = 16 * ((u + 1) * (u + 1)) := by
  have h_factor : 4 * u + 4 = 4 * (u + 1) := by
    rw [Int.mul_add, Int.mul_one]
  rw [h_factor]
  exact int_four_mul_sq (u + 1)

/-- `s * 10000 = 16 * (s * 625)`. -/
private theorem int_10000_eq (s : Int) : s * 10000 = 16 * (s * 625) := by
  show s * 10000 = 16 * (s * 625)
  rw [show (10000 : Int) = 625 * 16 from rfl]
  rw [← Int.mul_assoc s 625 16, Int.mul_comm (s * 625) 16]

/-! ## Operation reductions

For each of the partial Rust operations used in the source, we provide a
reduction lemma that rewrites it to a pure value under explicit overflow
hypotheses. The reductions follow the patterns established by the
reference proof files. -/

private theorem i64_add_pure (a b : i64) (h : ¬ Int64.addOverflow a b) :
    (a +? b : RustM i64) = pure (a + b) := by
  show (rust_primitives.ops.arith.Add.add a b : RustM i64) = pure (a + b)
  show (if BitVec.saddOverflow a.toBitVec b.toBitVec then
          (.fail .integerOverflow : RustM i64)
        else pure (a + b)) = pure (a + b)
  have h_bv : BitVec.saddOverflow a.toBitVec b.toBitVec = false := by
    cases hb : BitVec.saddOverflow a.toBitVec b.toBitVec with
    | false => rfl
    | true => exact absurd hb h
  rw [h_bv]; rfl

private theorem i64_sub_pure (a b : i64) (h : ¬ Int64.subOverflow a b) :
    (a -? b : RustM i64) = pure (a - b) := by
  show (rust_primitives.ops.arith.Sub.sub a b : RustM i64) = pure (a - b)
  show (if BitVec.ssubOverflow a.toBitVec b.toBitVec then
          (.fail .integerOverflow : RustM i64)
        else pure (a - b)) = pure (a - b)
  have h_bv : BitVec.ssubOverflow a.toBitVec b.toBitVec = false := by
    cases hb : BitVec.ssubOverflow a.toBitVec b.toBitVec with
    | false => rfl
    | true => exact absurd hb h
  rw [h_bv]; rfl

private theorem i64_mul_pure (a b : i64) (h : ¬ Int64.mulOverflow a b) :
    (a *? b : RustM i64) = pure (a * b) := by
  show (rust_primitives.ops.arith.Mul.mul a b : RustM i64) = pure (a * b)
  show (if BitVec.smulOverflow a.toBitVec b.toBitVec then
          (.fail .integerOverflow : RustM i64)
        else pure (a * b)) = pure (a * b)
  have h_bv : BitVec.smulOverflow a.toBitVec b.toBitVec = false := by
    cases hb : BitVec.smulOverflow a.toBitVec b.toBitVec with
    | false => rfl
    | true => exact absurd hb h
  rw [h_bv]; rfl

/-- Division reduction: when `a` is not `minValue` (rules out the `a = MIN, b = -1`
    overflow corner) and `b ≠ 0`, signed division reduces to `pure (a / b)`. -/
private theorem i64_div_pure_of_ne_min (a b : i64)
    (h_ne_min : a ≠ Int64.minValue) (h_ne_zero : b ≠ 0) :
    (a /? b : RustM i64) = pure (a / b) := by
  show (rust_primitives.ops.arith.Div.div a b : RustM i64) = pure (a / b)
  show (if a = Int64.minValue && b = -1 then
          (.fail .integerOverflow : RustM i64)
        else if b = 0 then .fail .divisionByZero
             else pure (a / b)) = pure (a / b)
  have h_and : (a = Int64.minValue && b = -1) = false := by
    rcases Decidable.em (a = Int64.minValue) with h | h
    · exact absurd h h_ne_min
    · simp [h]
  rw [h_and, if_neg h_ne_zero]; rfl

private theorem i64_le_pure (a b : i64) :
    (a <=? b : RustM Bool) = pure (decide (a ≤ b)) := rfl

private theorem i64_lt_pure (a b : i64) :
    (a <? b : RustM Bool) = pure (decide (a < b)) := rfl

private theorem i64_gt_pure (a b : i64) :
    (a >? b : RustM Bool) = pure (decide (a > b)) := rfl

private theorem i64_eq_pure (a b : i64) :
    (a ==? b : RustM Bool) = pure (decide (a = b)) := rfl

/-- Disjunctive `or` reduction. -/
private theorem rustM_or_pure (a b : Bool) :
    (a ||? b : RustM Bool) = pure (a || b) := rfl

/-! ## `isqrt` characterization

The recursive helper `isqrt_bin n lo hi` performs binary search for
`floor(sqrt n)` within `[lo, hi]`. Wrapped by `isqrt`, which short-circuits
non-positive inputs to `0` and otherwise calls `isqrt_bin n 0 3037000500`.

The upper bound `3037000500 > floor(sqrt(i64::MAX)) = 3037000499` is large
enough that for every `n : i64` with `0 ≤ n`, the invariant `n < hi*hi`
holds, so the binary search returns the true integer square root. Also,
the largest `mid` ever computed is `≤ 3037000499`, so `mid * mid ≤
(3037000499)^2 < 2^63` and the inner multiplication never overflows. -/

/-- Boundary clause: `isqrt n = 0` for any `n ≤ 0`.

    Pins the early-return arm `if n <=? 0 then pure 0` in `isqrt`. -/
theorem isqrt_nonpos (n : i64) (hn : n.toInt ≤ 0) :
    clever_070_triangle_area.isqrt n = RustM.ok (0 : i64) := by
  unfold clever_070_triangle_area.isqrt
  have h_le : n ≤ (0 : i64) := by
    apply Int64.le_iff_toInt_le.mpr
    rw [i64_zero_toInt]; exact hn
  have h_dec : decide (n ≤ (0 : i64)) = true := decide_eq_true h_le
  simp only [show (n <=? (0 : i64) : RustM Bool) =
               (pure (decide (n ≤ (0 : i64))) : RustM Bool) from rfl,
             h_dec, pure_bind, ↓reduceIte]
  rfl

/-- Postcondition for the binary-search helper.

    Invariant: `0 ≤ lo ≤ hi ≤ 3037000500`, `lo² ≤ n`, `n < hi²`.
    Result: `r` with `lo ≤ r`, `r * r ≤ n`, `n < (r+1)²`. -/
private theorem isqrt_bin_postcondition
    (n : i64) (hn : 0 ≤ n.toInt) :
    ∀ (lo hi : i64),
      0 ≤ lo.toInt →
      lo.toInt ≤ hi.toInt →
      hi.toInt ≤ 3037000500 →
      lo.toInt * lo.toInt ≤ n.toInt →
      n.toInt < hi.toInt * hi.toInt →
      ∃ r : i64, clever_070_triangle_area.isqrt_bin n lo hi = RustM.ok r ∧
        lo.toInt ≤ r.toInt ∧
        r.toInt ≤ hi.toInt ∧
        r.toInt * r.toInt ≤ n.toInt ∧
        n.toInt < (r.toInt + 1) * (r.toInt + 1) := by
  intro lo hi
  induction hk : (hi.toInt - lo.toInt).toNat using Nat.strongRecOn
    generalizing lo hi with
  | _ k ih =>
    intro hlo_nn hlo_le_hi hhi_bound hlo_sq_le hn_lt_hi_sq
    -- Standard i64 bounds
    have hlo_lt_2_63 := i64_toInt_lt lo
    have hhi_lt_2_63 := i64_toInt_lt hi
    have hlo_ge_neg := i64_toInt_ge lo
    have hhi_ge_neg := i64_toInt_ge hi
    -- hi - lo ≥ 0, ≤ 3037000500.
    have hdiff_nn : 0 ≤ hi.toInt - lo.toInt := by omega
    have hdiff_le : hi.toInt - lo.toInt ≤ 3037000500 := by omega
    -- Subtraction hi -? lo doesn't overflow.
    have h_no_sub : ¬ Int64.subOverflow hi lo := by
      intro hov
      rw [Int64.subOverflow_iff, h63_eq] at hov
      rcases hov with hov | hov
      · omega
      · omega
    -- (hi - lo).toInt = hi.toInt - lo.toInt
    have h_sub_toInt : (hi - lo).toInt = hi.toInt - lo.toInt :=
      Int64.toInt_sub_of_not_subOverflow h_no_sub
    unfold clever_070_triangle_area.isqrt_bin
    rw [i64_sub_pure hi lo h_no_sub]
    simp only [pure_bind]
    rw [i64_le_pure]
    simp only [pure_bind]
    by_cases hexit : (hi - lo) ≤ (1 : i64)
    · -- Base case: hi - lo ≤ 1.
      simp only [decide_eq_true hexit, ↓reduceIte]
      have h_diff_le_one : (hi - lo).toInt ≤ (1 : i64).toInt :=
        Int64.le_iff_toInt_le.mp hexit
      rw [i64_one_toInt] at h_diff_le_one
      rw [h_sub_toInt] at h_diff_le_one
      -- We have lo² ≤ n < hi² and hi ≤ lo + 1.
      -- If lo = hi, then n < lo² ≤ n contradicts. So hi = lo + 1.
      have hlo_lt_hi : lo.toInt < hi.toInt := by
        by_cases h_eq : lo.toInt = hi.toInt
        · exfalso; rw [h_eq] at hlo_sq_le; omega
        · omega
      have h_hi_eq : hi.toInt = lo.toInt + 1 := by omega
      refine ⟨lo, rfl, ?_, ?_, hlo_sq_le, ?_⟩
      · omega
      · omega
      · rw [← h_hi_eq]; exact hn_lt_hi_sq
    · -- Recursive case: hi - lo > 1.
      simp only [decide_eq_false hexit, Bool.false_eq_true, ↓reduceIte]
      have h_not_le_one : ¬ (hi - lo).toInt ≤ (1 : i64).toInt := by
        intro h
        apply hexit
        apply Int64.le_iff_toInt_le.mpr h
      rw [i64_one_toInt] at h_not_le_one
      rw [h_sub_toInt] at h_not_le_one
      have h_gap : hi.toInt - lo.toInt ≥ 2 := by omega
      -- Add: lo +? hi. 0 ≤ lo + hi ≤ 2 * 3037000500 < 2^63.
      have h_no_add : ¬ Int64.addOverflow lo hi := by
        intro hov
        rw [Int64.addOverflow_iff, h63_eq] at hov
        rcases hov with hov | hov
        · omega
        · omega
      have h_add_toInt : (lo + hi).toInt = lo.toInt + hi.toInt :=
        Int64.toInt_add_of_not_addOverflow h_no_add
      rw [i64_add_pure lo hi h_no_add]
      simp only [pure_bind]
      -- Div: (lo+hi) /? 2. We need lo+hi ≠ minValue and 2 ≠ 0.
      have h_lh_nn : 0 ≤ (lo + hi).toInt := by rw [h_add_toInt]; omega
      have h_lh_ne_min : lo + hi ≠ Int64.minValue := by
        intro h
        have : (lo + hi).toInt = Int64.minValue.toInt := by rw [h]
        rw [int64_min_toInt] at this
        omega
      have h_two_ne_zero : (2 : i64) ≠ 0 := by decide
      rw [i64_div_pure_of_ne_min (lo + hi) 2 h_lh_ne_min h_two_ne_zero]
      simp only [pure_bind]
      -- mid = (lo + hi) / 2. mid.toInt = (lo + hi).toInt / 2.
      let mid := (lo + hi) / 2
      have h_mid_def : mid = (lo + hi) / 2 := rfl
      have h_mid_toInt : mid.toInt = (lo.toInt + hi.toInt) / 2 := by
        show ((lo + hi) / 2).toInt = _
        have h_div_tdiv : ((lo + hi) / 2).toInt = (lo + hi).toInt.tdiv (2 : i64).toInt := by
          have := @Int64.toInt_div_of_ne_left (lo + hi) 2 h_lh_ne_min
          exact this
        rw [h_div_tdiv, h_add_toInt, i64_two_toInt]
        -- Int.tdiv = Int.ediv when dividend ≥ 0.
        have h_dividend_nn : 0 ≤ lo.toInt + hi.toInt := by omega
        rw [Int.tdiv_eq_ediv]
        rw [if_pos (Or.inl h_dividend_nn)]
        omega
      -- mid satisfies lo < mid < hi.
      have h_mid_lo : lo.toInt < mid.toInt := by
        rw [h_mid_toInt]
        -- (lo + hi) / 2 ≥ (lo + lo + 2) / 2 = lo + 1.
        have h_sum_ge : lo.toInt + hi.toInt ≥ 2 * lo.toInt + 2 := by omega
        have h_div_ge : (2 * lo.toInt + 2) / 2 ≤ (lo.toInt + hi.toInt) / 2 :=
          Int.ediv_le_ediv (by decide) h_sum_ge
        have h_simp : (2 * lo.toInt + 2) / 2 = lo.toInt + 1 := by
          have h_eq : 2 * lo.toInt + 2 = (lo.toInt + 1) * 2 := by omega
          rw [h_eq]
          exact Int.mul_ediv_cancel _ (by decide)
        omega
      have h_mid_hi : mid.toInt < hi.toInt := by
        rw [h_mid_toInt]
        -- (lo + hi) / 2 ≤ (hi + hi - 2) / 2 = hi - 1 (when gap ≥ 2).
        have h_sum_le : lo.toInt + hi.toInt ≤ 2 * hi.toInt - 2 := by omega
        have h_div_le : (lo.toInt + hi.toInt) / 2 ≤ (2 * hi.toInt - 2) / 2 :=
          Int.ediv_le_ediv (by decide) h_sum_le
        have h_simp : (2 * hi.toInt - 2) / 2 = hi.toInt - 1 := by
          have h_eq : 2 * hi.toInt - 2 = (hi.toInt - 1) * 2 := by omega
          rw [h_eq]
          exact Int.mul_ediv_cancel _ (by decide)
        omega
      have h_mid_nn : 0 ≤ mid.toInt := by omega
      have h_mid_bound : mid.toInt ≤ 3037000500 := by omega
      have h_mid_lt_2_63 := i64_toInt_lt mid
      -- mid * mid: no overflow since mid ≤ 3037000499 (mid < hi ≤ 3037000500).
      have h_mid_lt : mid.toInt < 3037000500 := by omega
      have h_no_mul : ¬ Int64.mulOverflow mid mid := by
        intro hov
        rw [Int64.mulOverflow_iff, h63_eq] at hov
        have h_sq_bound : mid.toInt * mid.toInt < 2 ^ 63 := by
          -- mid ≤ 3037000499 < sqrt(2^63)
          have h_mid_ub : mid.toInt ≤ 3037000499 := by omega
          have h_sq_le : mid.toInt * mid.toInt ≤ 3037000499 * 3037000499 := by
            have h := Int.mul_le_mul h_mid_ub h_mid_ub h_mid_nn (by omega)
            exact h
          have h_val : (3037000499 : Int) * 3037000499 < 2 ^ 63 := by decide
          omega
        have h_sq_nn : 0 ≤ mid.toInt * mid.toInt := Int.mul_nonneg h_mid_nn h_mid_nn
        rcases hov with hov | hov
        · omega
        · omega
      have h_mul_toInt : (mid * mid).toInt = mid.toInt * mid.toInt :=
        Int64.toInt_mul_of_not_mulOverflow h_no_mul
      rw [i64_mul_pure mid mid h_no_mul]
      simp only [pure_bind]
      rw [i64_le_pure]
      simp only [pure_bind]
      by_cases h_sq_le_n : (mid * mid) ≤ n
      · -- Recurse with (mid, hi).
        simp only [decide_eq_true h_sq_le_n, ↓reduceIte]
        have h_sq_le_int : (mid * mid).toInt ≤ n.toInt := Int64.le_iff_toInt_le.mp h_sq_le_n
        rw [h_mul_toInt] at h_sq_le_int
        -- Measure decreases: hi - mid < hi - lo.
        have h_new_measure : (hi.toInt - mid.toInt).toNat < k := by
          rw [← hk]
          have h_diff_pos_old : 0 ≤ hi.toInt - lo.toInt := by omega
          have h_diff_pos_new : 0 ≤ hi.toInt - mid.toInt := by omega
          have h_lt : hi.toInt - mid.toInt < hi.toInt - lo.toInt := by omega
          omega
        obtain ⟨r, hr_eq, hr_lo, hr_hi, hr_sq, hr_succ⟩ :=
          ih (hi.toInt - mid.toInt).toNat h_new_measure mid hi
              rfl h_mid_nn (by omega : mid.toInt ≤ hi.toInt) hhi_bound h_sq_le_int hn_lt_hi_sq
        refine ⟨r, hr_eq, ?_, hr_hi, hr_sq, hr_succ⟩
        omega
      · -- Recurse with (lo, mid).
        simp only [decide_eq_false h_sq_le_n, Bool.false_eq_true, ↓reduceIte]
        have h_sq_gt_n : ¬ (mid * mid).toInt ≤ n.toInt := by
          intro h
          exact h_sq_le_n (Int64.le_iff_toInt_le.mpr h)
        rw [h_mul_toInt] at h_sq_gt_n
        have h_n_lt_sq : n.toInt < mid.toInt * mid.toInt := by omega
        -- Measure decreases: mid - lo < hi - lo.
        have h_new_measure : (mid.toInt - lo.toInt).toNat < k := by
          rw [← hk]
          have h_lt : mid.toInt - lo.toInt < hi.toInt - lo.toInt := by omega
          omega
        obtain ⟨r, hr_eq, hr_lo, hr_hi, hr_sq, hr_succ⟩ :=
          ih (mid.toInt - lo.toInt).toNat h_new_measure lo mid
              rfl hlo_nn (by omega : lo.toInt ≤ mid.toInt) h_mid_bound hlo_sq_le h_n_lt_sq
        refine ⟨r, hr_eq, hr_lo, ?_, hr_sq, hr_succ⟩
        omega

/-- Full postcondition for `isqrt`: returns the integer square root. -/
theorem isqrt_postcondition (n : i64) (hn : 0 ≤ n.toInt) :
    ∃ r : i64, clever_070_triangle_area.isqrt n = RustM.ok r ∧
      0 ≤ r.toInt ∧
      r.toInt * r.toInt ≤ n.toInt ∧
      n.toInt < (r.toInt + 1) * (r.toInt + 1) := by
  unfold clever_070_triangle_area.isqrt
  by_cases hn_zero : n.toInt = 0
  · -- n = 0: returns isqrt_bin n 0 3037000500.
    -- But the if guard is `n <=? 0`, so we exit via the zero branch.
    have h_le : n ≤ (0 : i64) := by
      apply Int64.le_iff_toInt_le.mpr
      rw [i64_zero_toInt]; omega
    have h_dec : decide (n ≤ (0 : i64)) = true := decide_eq_true h_le
    simp only [show (n <=? (0 : i64) : RustM Bool) =
                 (pure (decide (n ≤ (0 : i64))) : RustM Bool) from rfl,
               h_dec, pure_bind, ↓reduceIte]
    refine ⟨0, rfl, ?_, ?_, ?_⟩
    · rw [i64_zero_toInt]; omega
    · rw [i64_zero_toInt, hn_zero]; omega
    · rw [i64_zero_toInt, hn_zero]; decide
  · -- n > 0: call isqrt_bin n 0 3037000500.
    have hn_pos : 0 < n.toInt := by omega
    have h_not_le : ¬ n ≤ (0 : i64) := by
      intro h
      have := Int64.le_iff_toInt_le.mp h
      rw [i64_zero_toInt] at this
      omega
    have h_dec : decide (n ≤ (0 : i64)) = false := decide_eq_false h_not_le
    simp only [show (n <=? (0 : i64) : RustM Bool) =
                 (pure (decide (n ≤ (0 : i64))) : RustM Bool) from rfl,
               h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
    -- Invariants:
    -- lo = 0: 0 ≤ 0, 0 ≤ 3037000500, 0² = 0 ≤ n.
    -- hi = 3037000500: n < 3037000500². n ≤ 2^63 - 1 < 3037000500².
    have h_0_toInt : (0 : i64).toInt = 0 := i64_zero_toInt
    have h_hi_toInt : (3037000500 : i64).toInt = 3037000500 := by decide
    have h_lo_nn : 0 ≤ (0 : i64).toInt := by rw [h_0_toInt]; omega
    have h_lo_le_hi : (0 : i64).toInt ≤ (3037000500 : i64).toInt := by
      rw [h_0_toInt, h_hi_toInt]; decide
    have h_hi_bound : (3037000500 : i64).toInt ≤ 3037000500 := by rw [h_hi_toInt]; omega
    have h_lo_sq_le : (0 : i64).toInt * (0 : i64).toInt ≤ n.toInt := by
      rw [h_0_toInt]; omega
    have h_n_lt_hi_sq : n.toInt < (3037000500 : i64).toInt * (3037000500 : i64).toInt := by
      rw [h_hi_toInt]
      have h_n_lt := i64_toInt_lt n
      have h_hi_sq : (3037000500 : Int) * 3037000500 = 9223372037000250000 := by decide
      have h_2_63 : (2 : Int) ^ 63 = 9223372036854775808 := by decide
      omega
    obtain ⟨r, hr_eq, hr_lo, hr_hi, hr_sq, hr_succ⟩ :=
      isqrt_bin_postcondition n hn (0 : i64) (3037000500 : i64)
        h_lo_nn h_lo_le_hi h_hi_bound h_lo_sq_le h_n_lt_hi_sq
    refine ⟨r, hr_eq, ?_, hr_sq, hr_succ⟩
    rw [h_0_toInt] at hr_lo
    exact hr_lo

/-! ## `triangle_area` contract

The three property tests in the Rust source decompose as follows:

  * `invalid_iff_minus_one` ⇒ two directions:
       - invalid → returns `-1` (`triangle_area_invalid_returns_minus_one`)
       - valid   → returns `r ≥ 0` (`triangle_area_valid_returns_nonneg`)
  * `matches_oracle`        ⇒ valid → closed-form match
       (`triangle_area_valid_formula`)
  * `known_cases`           ⇒ four concrete pinned values.

All non-boundary theorems carry the three "no-overflow on the
validity-check sums" preconditions for `a +? b`, `a +? c`, `b +? c`,
because the Hax extraction evaluates all three additions before any
boolean is consumed. The valid-branch theorems also carry positivity and
a Heron-product bound that suffices for every intermediate `+?`, `-?`,
`*?` in the chain to stay in i64 range. -/

/-- Invalid-triangle case: when the validity-check sums do not overflow
    and at least one of the triangle inequalities flips (one side is at
    least the sum of the other two), the function returns the sentinel
    `-1`.

    Corresponds to the `else` branch of `invalid_iff_minus_one`:
    `prop_assert_eq!(triangle_area(a,b,c), -1)`. -/
theorem triangle_area_invalid_returns_minus_one (a b c : i64)
    (h_ab : ¬ Int64.addOverflow a b)
    (h_ac : ¬ Int64.addOverflow a c)
    (h_bc : ¬ Int64.addOverflow b c)
    (h_invalid :
      (a + b).toInt ≤ c.toInt ∨
      (a + c).toInt ≤ b.toInt ∨
      (b + c).toInt ≤ a.toInt) :
    clever_070_triangle_area.triangle_area a b c = RustM.ok (-1 : i64) := by
  unfold clever_070_triangle_area.triangle_area
  rw [i64_add_pure a b h_ab]; simp only [pure_bind]
  rw [i64_le_pure]; simp only [pure_bind]
  rw [i64_add_pure a c h_ac]; simp only [pure_bind]
  rw [i64_le_pure]; simp only [pure_bind]
  rw [rustM_or_pure]; simp only [pure_bind]
  rw [i64_add_pure b c h_bc]; simp only [pure_bind]
  rw [i64_le_pure]; simp only [pure_bind]
  rw [rustM_or_pure]; simp only [pure_bind]
  -- Now the guard reduces to `decide ((a+b ≤ c) || (a+c ≤ b)) || (b+c ≤ a)`.
  have h_ab_le : (a + b ≤ c) ↔ (a + b).toInt ≤ c.toInt := Int64.le_iff_toInt_le
  have h_ac_le : (a + c ≤ b) ↔ (a + c).toInt ≤ b.toInt := Int64.le_iff_toInt_le
  have h_bc_le : (b + c ≤ a) ↔ (b + c).toInt ≤ a.toInt := Int64.le_iff_toInt_le
  have h_guard :
      ((decide (a + b ≤ c) || decide (a + c ≤ b)) || decide (b + c ≤ a)) = true := by
    rcases h_invalid with h | h | h
    · rw [decide_eq_true (h_ab_le.mpr h)]; rfl
    · rw [decide_eq_true (h_ac_le.mpr h)]; simp
    · rw [decide_eq_true (h_bc_le.mpr h)]; simp
  rw [h_guard]; rfl

/-- Master helper for the valid branch. Returns the full postcondition:
    the result `r` is the integer floor of `√(s2·10000) / 4`, encoded as
    `r² ≤ s2·625 < (r+1)²`, with `r ≥ 0` and the result equation. -/
private theorem triangle_area_valid_helper (a b c : i64)
    (h_ab : ¬ Int64.addOverflow a b)
    (h_ac : ¬ Int64.addOverflow a c)
    (h_bc : ¬ Int64.addOverflow b c)
    (ha_pos : 0 ≤ a.toInt) (hb_pos : 0 ≤ b.toInt) (hc_pos : 0 ≤ c.toInt)
    (h_valid_ab : c.toInt < a.toInt + b.toInt)
    (h_valid_ac : b.toInt < a.toInt + c.toInt)
    (h_valid_bc : a.toInt < b.toInt + c.toInt)
    (h_heron_bound :
      (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
        (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt) * 10000
      < 2 ^ 63) :
    ∃ r : i64, clever_070_triangle_area.triangle_area a b c = RustM.ok r ∧
      0 ≤ r.toInt ∧
      r.toInt * r.toInt ≤
        ((a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
          (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt)) * 625 ∧
      ((a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
        (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt)) * 625
        < (r.toInt + 1) * (r.toInt + 1) := by
  -- Int-level Heron factors and positivity.
  -- A = a+b+c, B = b+c-a, C = a-b+c, D = a+b-c.
  -- Validity: A > 0, B > 0, C > 0, D > 0. Each is ≥ 1.
  have hA_pos : 0 < a.toInt + b.toInt + c.toInt := by omega
  have hB_pos : 0 < b.toInt + c.toInt - a.toInt := by omega
  have hC_pos : 0 < a.toInt - b.toInt + c.toInt := by omega
  have hD_pos : 0 < a.toInt + b.toInt - c.toInt := by omega
  have hA_ge : 1 ≤ a.toInt + b.toInt + c.toInt := by omega
  have hB_ge : 1 ≤ b.toInt + c.toInt - a.toInt := by omega
  have hC_ge : 1 ≤ a.toInt - b.toInt + c.toInt := by omega
  have hD_ge : 1 ≤ a.toInt + b.toInt - c.toInt := by omega
  -- Standard i64 bounds.
  have h_a_lt := i64_toInt_lt a
  have h_b_lt := i64_toInt_lt b
  have h_c_lt := i64_toInt_lt c
  have h_a_ge := i64_toInt_ge a
  have h_b_ge := i64_toInt_ge b
  have h_c_ge := i64_toInt_ge c
  -- Positive product chain.
  have hAB_pos : 0 < (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) :=
    Int.mul_pos hA_pos hB_pos
  have hABC_pos : 0 < (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
      (a.toInt - b.toInt + c.toInt) :=
    Int.mul_pos hAB_pos hC_pos
  have hABCD_pos : 0 < (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
      (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt) :=
    Int.mul_pos hABC_pos hD_pos
  -- Bound chains: partial products ≤ ABCD ≤ ABCD * 10000 < 2^63.
  have h_ABCD_le_full :
      (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
        (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt)
      ≤ (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
        (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt) * 10000 :=
    int_le_self_mul (Int.le_of_lt hABCD_pos) (by decide : (1:Int) ≤ 10000)
  have h_ABC_le_ABCD :
      (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
        (a.toInt - b.toInt + c.toInt)
      ≤ (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
        (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt) :=
    int_le_self_mul (Int.le_of_lt hABC_pos) hD_ge
  have h_AB_le_ABC :
      (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt)
      ≤ (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
        (a.toInt - b.toInt + c.toInt) :=
    int_le_self_mul (Int.le_of_lt hAB_pos) hC_ge
  have h_A_le_AB :
      a.toInt + b.toInt + c.toInt
      ≤ (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) :=
    int_le_self_mul (Int.le_of_lt hA_pos) hB_ge
  -- All partial products and individual factors are < 2^63.
  have h_A_lt : a.toInt + b.toInt + c.toInt < 2 ^ 63 := by omega
  have h_AB_lt : (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) < 2 ^ 63 := by
    omega
  have h_ABC_lt : (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
      (a.toInt - b.toInt + c.toInt) < 2 ^ 63 := by omega
  have h_ABCD_lt : (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
      (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt) < 2 ^ 63 := by omega
  -- a+b, b+c are also < A < 2^63. a+c too.
  have h_ab_lt : a.toInt + b.toInt < 2 ^ 63 := by omega
  have h_ac_lt : a.toInt + c.toInt < 2 ^ 63 := by omega
  have h_bc_lt : b.toInt + c.toInt < 2 ^ 63 := by omega
  have h_amb_in : -(2 ^ 63 : Int) ≤ a.toInt - b.toInt ∧ a.toInt - b.toInt < 2 ^ 63 := by
    constructor <;> omega
  have h_bma_in : -(2 ^ 63 : Int) ≤ b.toInt - a.toInt ∧ b.toInt - a.toInt < 2 ^ 63 := by
    constructor <;> omega
  -- Reductions: a+b, a+c, b+c (already have h_ab, h_ac, h_bc).
  have h_ab_toInt : (a + b).toInt = a.toInt + b.toInt :=
    Int64.toInt_add_of_not_addOverflow h_ab
  have h_ac_toInt : (a + c).toInt = a.toInt + c.toInt :=
    Int64.toInt_add_of_not_addOverflow h_ac
  have h_bc_toInt : (b + c).toInt = b.toInt + c.toInt :=
    Int64.toInt_add_of_not_addOverflow h_bc
  -- (a+b)+c: a.toInt + b.toInt + c.toInt < 2^63 and ≥ 0.
  have h_no_ab_c : ¬ Int64.addOverflow (a + b) c := by
    intro hov
    rw [Int64.addOverflow_iff, h63_eq, h_ab_toInt] at hov
    rcases hov with hov | hov
    · omega
    · omega
  have h_ab_c_toInt : ((a + b) + c).toInt = a.toInt + b.toInt + c.toInt := by
    rw [Int64.toInt_add_of_not_addOverflow h_no_ab_c, h_ab_toInt]
  -- (b+c) - a.
  have h_no_bc_sub_a : ¬ Int64.subOverflow (b + c) a := by
    intro hov
    rw [Int64.subOverflow_iff, h63_eq, h_bc_toInt] at hov
    rcases hov with hov | hov
    · omega
    · omega
  have h_bc_a_toInt : ((b + c) - a).toInt = b.toInt + c.toInt - a.toInt := by
    rw [Int64.toInt_sub_of_not_subOverflow h_no_bc_sub_a, h_bc_toInt]
  -- ((a+b)+c) * ((b+c)-a) = A * B.
  have h_no_AB_mul : ¬ Int64.mulOverflow ((a + b) + c) ((b + c) - a) := by
    intro hov
    rw [Int64.mulOverflow_iff, h63_eq, h_ab_c_toInt, h_bc_a_toInt] at hov
    rcases hov with hov | hov
    · omega
    · have : 0 ≤ (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) :=
        Int.le_of_lt hAB_pos
      omega
  have h_AB_toInt : (((a + b) + c) * ((b + c) - a)).toInt =
      (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) := by
    rw [Int64.toInt_mul_of_not_mulOverflow h_no_AB_mul, h_ab_c_toInt, h_bc_a_toInt]
  -- a - b.
  have h_no_a_sub_b : ¬ Int64.subOverflow a b := by
    intro hov
    rw [Int64.subOverflow_iff, h63_eq] at hov
    rcases hov with hov | hov
    · omega
    · omega
  have h_a_sub_b_toInt : (a - b).toInt = a.toInt - b.toInt :=
    Int64.toInt_sub_of_not_subOverflow h_no_a_sub_b
  -- (a-b) + c.
  have h_no_amb_c : ¬ Int64.addOverflow (a - b) c := by
    intro hov
    rw [Int64.addOverflow_iff, h63_eq, h_a_sub_b_toInt] at hov
    rcases hov with hov | hov
    · omega
    · omega
  have h_amb_c_toInt : ((a - b) + c).toInt = a.toInt - b.toInt + c.toInt := by
    rw [Int64.toInt_add_of_not_addOverflow h_no_amb_c, h_a_sub_b_toInt]
  -- (A*B) * C.
  have h_no_ABC_mul :
      ¬ Int64.mulOverflow (((a + b) + c) * ((b + c) - a)) ((a - b) + c) := by
    intro hov
    rw [Int64.mulOverflow_iff, h63_eq, h_AB_toInt, h_amb_c_toInt] at hov
    rcases hov with hov | hov
    · omega
    · have : 0 ≤ (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
        (a.toInt - b.toInt + c.toInt) := Int.le_of_lt hABC_pos
      omega
  have h_ABC_toInt :
      ((((a + b) + c) * ((b + c) - a)) * ((a - b) + c)).toInt =
      (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
        (a.toInt - b.toInt + c.toInt) := by
    rw [Int64.toInt_mul_of_not_mulOverflow h_no_ABC_mul, h_AB_toInt, h_amb_c_toInt]
  -- (a+b) - c.
  have h_no_ab_sub_c : ¬ Int64.subOverflow (a + b) c := by
    intro hov
    rw [Int64.subOverflow_iff, h63_eq, h_ab_toInt] at hov
    rcases hov with hov | hov
    · omega
    · omega
  have h_ab_sub_c_toInt : ((a + b) - c).toInt = a.toInt + b.toInt - c.toInt := by
    rw [Int64.toInt_sub_of_not_subOverflow h_no_ab_sub_c, h_ab_toInt]
  -- (A*B*C) * D.
  have h_no_ABCD_mul :
      ¬ Int64.mulOverflow ((((a + b) + c) * ((b + c) - a)) * ((a - b) + c))
        ((a + b) - c) := by
    intro hov
    rw [Int64.mulOverflow_iff, h63_eq, h_ABC_toInt, h_ab_sub_c_toInt] at hov
    rcases hov with hov | hov
    · omega
    · have : 0 ≤ (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
        (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt) :=
        Int.le_of_lt hABCD_pos
      omega
  have h_ABCD_toInt :
      (((((a + b) + c) * ((b + c) - a)) * ((a - b) + c)) * ((a + b) - c)).toInt =
      (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
        (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt) := by
    rw [Int64.toInt_mul_of_not_mulOverflow h_no_ABCD_mul, h_ABC_toInt, h_ab_sub_c_toInt]
  -- Set s2 = (((a+b)+c) * ((b+c)-a)) * ((a-b)+c)) * ((a+b)-c).
  let s2 := (((((a + b) + c) * ((b + c) - a)) * ((a - b) + c)) * ((a + b) - c))
  have h_s2_toInt : s2.toInt =
      (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
        (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt) :=
    h_ABCD_toInt
  -- s2 * 10000.
  have h_10000_toInt : (10000 : i64).toInt = 10000 := by decide
  have h_no_s2_mul : ¬ Int64.mulOverflow s2 (10000 : i64) := by
    intro hov
    rw [Int64.mulOverflow_iff, h63_eq, h_s2_toInt, h_10000_toInt] at hov
    rcases hov with hov | hov
    · omega
    · have h_ABCD_nn : 0 ≤ (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
          (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt) :=
        Int.le_of_lt hABCD_pos
      have h_10000_nn : (0 : Int) ≤ 10000 := by decide
      have : 0 ≤ (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
          (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt) * 10000 :=
        Int.mul_nonneg h_ABCD_nn h_10000_nn
      omega
  have h_s2_10000_toInt : (s2 * 10000).toInt =
      (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
        (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt) * 10000 := by
    rw [Int64.toInt_mul_of_not_mulOverflow h_no_s2_mul, h_s2_toInt, h_10000_toInt]
  have h_s2_10000_nn : 0 ≤ (s2 * 10000).toInt := by
    rw [h_s2_10000_toInt]
    have h_ABCD_nn : 0 ≤ (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
        (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt) :=
      Int.le_of_lt hABCD_pos
    exact Int.mul_nonneg h_ABCD_nn (by decide : (0:Int) ≤ 10000)
  -- Apply isqrt_postcondition.
  obtain ⟨R, hR_eq, hR_nn, hR_sq_le, h_lt_R_sq⟩ :=
    isqrt_postcondition (s2 * 10000) h_s2_10000_nn
  -- R / 4. R ≠ minValue since R ≥ 0.
  have h_R_ne_min : R ≠ Int64.minValue := by
    intro h
    have : R.toInt = Int64.minValue.toInt := by rw [h]
    rw [int64_min_toInt] at this
    omega
  have h_four_ne_zero : (4 : i64) ≠ 0 := by decide
  -- r := R / 4. r.toInt = R.toInt / 4 (since R ≥ 0).
  have h_four_toInt : (4 : i64).toInt = 4 := by decide
  have h_r_toInt : (R / 4).toInt = R.toInt / 4 := by
    have h_div_tdiv : (R / 4).toInt = R.toInt.tdiv (4 : i64).toInt :=
      @Int64.toInt_div_of_ne_left R 4 h_R_ne_min
    rw [h_div_tdiv, h_four_toInt]
    rw [Int.tdiv_eq_ediv]
    rw [if_pos (Or.inl hR_nn)]
    omega
  -- Show triangle_area a b c = isqrt(s2 * 10000) /? 4 = pure (R / 4).
  -- We need to reduce the whole computation.
  refine ⟨R / 4, ?_, ?_, ?_, ?_⟩
  · -- The function equation.
    unfold clever_070_triangle_area.triangle_area
    -- Reduce the guard to false.
    rw [i64_add_pure a b h_ab]; simp only [pure_bind]
    rw [i64_le_pure]; simp only [pure_bind]
    rw [i64_add_pure a c h_ac]; simp only [pure_bind]
    rw [i64_le_pure]; simp only [pure_bind]
    rw [rustM_or_pure]; simp only [pure_bind]
    rw [i64_add_pure b c h_bc]; simp only [pure_bind]
    rw [i64_le_pure]; simp only [pure_bind]
    rw [rustM_or_pure]; simp only [pure_bind]
    -- Guard is false: each disjunct's decide is false.
    have h_ab_le_false : decide (a + b ≤ c) = false := by
      apply decide_eq_false
      intro h
      have := Int64.le_iff_toInt_le.mp h
      rw [h_ab_toInt] at this; omega
    have h_ac_le_false : decide (a + c ≤ b) = false := by
      apply decide_eq_false
      intro h
      have := Int64.le_iff_toInt_le.mp h
      rw [h_ac_toInt] at this; omega
    have h_bc_le_false : decide (b + c ≤ a) = false := by
      apply decide_eq_false
      intro h
      have := Int64.le_iff_toInt_le.mp h
      rw [h_bc_toInt] at this; omega
    have h_guard_false :
        ((decide (a + b ≤ c) || decide (a + c ≤ b)) || decide (b + c ≤ a)) = false := by
      rw [h_ab_le_false, h_ac_le_false, h_bc_le_false]; rfl
    rw [h_guard_false]
    simp only [Bool.false_eq_true, ↓reduceIte]
    -- Now reduce the else branch step by step. Note: a +? b, b +? c are
    -- already evaluated to a + b, b + c because they appeared in the guard.
    rw [i64_add_pure (a + b) c h_no_ab_c]; simp only [pure_bind]
    rw [i64_sub_pure (b + c) a h_no_bc_sub_a]; simp only [pure_bind]
    rw [i64_mul_pure ((a + b) + c) ((b + c) - a) h_no_AB_mul]; simp only [pure_bind]
    rw [i64_sub_pure a b h_no_a_sub_b]; simp only [pure_bind]
    rw [i64_add_pure (a - b) c h_no_amb_c]; simp only [pure_bind]
    rw [i64_mul_pure (((a + b) + c) * ((b + c) - a)) ((a - b) + c) h_no_ABC_mul]
    simp only [pure_bind]
    rw [i64_sub_pure (a + b) c h_no_ab_sub_c]; simp only [pure_bind]
    rw [i64_mul_pure ((((a + b) + c) * ((b + c) - a)) * ((a - b) + c)) ((a + b) - c)
        h_no_ABCD_mul]
    simp only [pure_bind]
    rw [i64_mul_pure s2 10000 h_no_s2_mul]; simp only [pure_bind]
    rw [hR_eq]
    show (RustM.ok R >>= fun x => x /? 4) = RustM.ok (R / 4)
    rw [show (RustM.ok R >>= fun x => x /? 4 : RustM i64) = (R /? 4 : RustM i64) from rfl]
    rw [i64_div_pure_of_ne_min R 4 h_R_ne_min h_four_ne_zero]
    rfl
  · -- 0 ≤ r.toInt.
    rw [h_r_toInt]
    apply Int.ediv_nonneg hR_nn
    omega
  · -- r * r ≤ ABCD * 625.
    -- 16 * (r * r) ≤ R * R ≤ ABCD * 10000 = ABCD * 16 * 625
    -- so r * r ≤ ABCD * 625.
    rw [h_r_toInt]
    have h_4r_le_R : 4 * (R.toInt / 4) ≤ R.toInt := by
      have := Int.ediv_add_emod R.toInt 4
      have h_mod_nn : 0 ≤ R.toInt % 4 := Int.emod_nonneg R.toInt (by decide)
      omega
    have h_4r_nn : 0 ≤ 4 * (R.toInt / 4) := by
      apply Int.mul_nonneg (by decide)
      exact Int.ediv_nonneg hR_nn (by decide)
    have h_16r_sq : (4 * (R.toInt / 4)) * (4 * (R.toInt / 4)) ≤ R.toInt * R.toInt :=
      Int.mul_le_mul h_4r_le_R h_4r_le_R h_4r_nn hR_nn
    rw [h_s2_10000_toInt] at hR_sq_le
    have h_R_sq_le_16ABCD :
        R.toInt * R.toInt ≤
          (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
            (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt) * 10000 := hR_sq_le
    -- (4r)*(4r) = 16 r², and 16 * (ABCD * 625) = ABCD * 10000.
    have h_chain : 16 * ((R.toInt / 4) * (R.toInt / 4)) ≤
        16 * (((a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
          (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt)) * 625) := by
      have h1 : (4 * (R.toInt / 4)) * (4 * (R.toInt / 4)) = 16 * ((R.toInt / 4) * (R.toInt / 4)) :=
        int_four_mul_sq (R.toInt / 4)
      have h2 : (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
        (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt) * 10000
        = 16 * (((a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
          (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt)) * 625) :=
        int_10000_eq _
      omega
    omega
  · -- s2 * 625 < (r+1)^2.
    -- (4r+4)^2 > (R+1)^2 > s2 * 10000 = 16 * s2 * 625, so (r+1)^2 > s2*625.
    rw [h_r_toInt]
    have h_R_lt : R.toInt + 1 ≤ 4 * (R.toInt / 4) + 4 := by
      have h := Int.ediv_add_emod R.toInt 4
      have h_mod_lt : R.toInt % 4 < 4 := Int.emod_lt_of_pos R.toInt (by decide)
      omega
    have h_R1_nn : 0 ≤ R.toInt + 1 := by omega
    have h_4r4_nn : 0 ≤ 4 * (R.toInt / 4) + 4 := by
      apply Int.add_nonneg
      · apply Int.mul_nonneg (by decide); exact Int.ediv_nonneg hR_nn (by decide)
      · decide
    have h_R1_sq_le : (R.toInt + 1) * (R.toInt + 1) ≤
        (4 * (R.toInt / 4) + 4) * (4 * (R.toInt / 4) + 4) :=
      Int.mul_le_mul h_R_lt h_R_lt h_R1_nn h_4r4_nn
    rw [h_s2_10000_toInt] at h_lt_R_sq
    have h_step : (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
        (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt) * 10000
        < (4 * (R.toInt / 4) + 4) * (4 * (R.toInt / 4) + 4) :=
      Int.lt_of_lt_of_le h_lt_R_sq h_R1_sq_le
    -- (4r+4)*(4r+4) = 16*(r+1)*(r+1), and ABCD*10000 = 16*(ABCD*625).
    have h_lhs : (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
        (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt) * 10000
        = 16 * (((a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
          (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt)) * 625) :=
      int_10000_eq _
    have h_rhs : (4 * (R.toInt / 4) + 4) * (4 * (R.toInt / 4) + 4)
        = 16 * ((R.toInt / 4 + 1) * (R.toInt / 4 + 1)) :=
      int_four_succ_sq (R.toInt / 4)
    rw [h_lhs, h_rhs] at h_step
    omega

theorem triangle_area_valid_returns_nonneg (a b c : i64)
    (h_ab : ¬ Int64.addOverflow a b)
    (h_ac : ¬ Int64.addOverflow a c)
    (h_bc : ¬ Int64.addOverflow b c)
    (ha_pos : 0 ≤ a.toInt) (hb_pos : 0 ≤ b.toInt) (hc_pos : 0 ≤ c.toInt)
    (h_valid_ab : c.toInt < a.toInt + b.toInt)
    (h_valid_ac : b.toInt < a.toInt + c.toInt)
    (h_valid_bc : a.toInt < b.toInt + c.toInt)
    (h_heron_bound :
      (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
        (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt) * 10000
      < 2 ^ 63) :
    ∃ r : i64, clever_070_triangle_area.triangle_area a b c = RustM.ok r ∧
      0 ≤ r.toInt := by
  obtain ⟨r, hr_eq, hr_nn, _, _⟩ := triangle_area_valid_helper a b c
    h_ab h_ac h_bc ha_pos hb_pos hc_pos h_valid_ab h_valid_ac h_valid_bc h_heron_bound
  exact ⟨r, hr_eq, hr_nn⟩

/-- Closed-form postcondition (valid branch).

    Let `s2 = (a+b+c)(b+c-a)(a-b+c)(a+b-c)`. In the valid branch the
    function returns `r = floor(sqrt(s2 * 10000)) / 4`, which equals
    `floor(sqrt(s2 * 625))` because `10000 = 16 * 625` and the integer
    square root commutes with division by a perfect square at the
    Int-floor level. This is captured here as the pair of bounds
    `r * r ≤ s2 * 625` and `s2 * 625 < (r + 1) * (r + 1)`, plus `0 ≤ r`.

    Corresponds to `matches_oracle`. The `±1` slack in the proptest is
    f64 rounding error on the *oracle*; the Rust function computes the
    exact integer floor. -/
theorem triangle_area_valid_formula (a b c : i64)
    (h_ab : ¬ Int64.addOverflow a b)
    (h_ac : ¬ Int64.addOverflow a c)
    (h_bc : ¬ Int64.addOverflow b c)
    (ha_pos : 0 ≤ a.toInt) (hb_pos : 0 ≤ b.toInt) (hc_pos : 0 ≤ c.toInt)
    (h_valid_ab : c.toInt < a.toInt + b.toInt)
    (h_valid_ac : b.toInt < a.toInt + c.toInt)
    (h_valid_bc : a.toInt < b.toInt + c.toInt)
    (h_heron_bound :
      (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
        (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt) * 10000
      < 2 ^ 63) :
    ∃ r : i64, clever_070_triangle_area.triangle_area a b c = RustM.ok r ∧
      0 ≤ r.toInt ∧
      r.toInt * r.toInt ≤
        ((a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
          (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt)) * 625 ∧
      ((a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
        (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt)) * 625
        < (r.toInt + 1) * (r.toInt + 1) :=
  triangle_area_valid_helper a b c h_ab h_ac h_bc ha_pos hb_pos hc_pos
    h_valid_ab h_valid_ac h_valid_bc h_heron_bound

/-! ## Known cases (from `known_cases` test)

Four concrete value checks that pin specific input/output pairs. They
are corollaries of the general theorems above but exercise the explicit
code paths the proptests sample at. -/

/-- `triangle_area 1 2 10 = -1`. Invalid triangle (1 + 2 < 10): far from
    the boundary. Discharged directly via the invalid-branch theorem;
    `1 + 2 = 3 ≤ 10` selects the validity-failure arm. -/
theorem triangle_area_1_2_10 :
    clever_070_triangle_area.triangle_area 1 2 10 = RustM.ok (-1 : i64) := by
  apply triangle_area_invalid_returns_minus_one (1 : i64) (2 : i64) (10 : i64)
  · intro hov
    rw [Int64.addOverflow_iff] at hov
    rcases hov with hov | hov <;> (exfalso; revert hov; decide)
  · intro hov
    rw [Int64.addOverflow_iff] at hov
    rcases hov with hov | hov <;> (exfalso; revert hov; decide)
  · intro hov
    rw [Int64.addOverflow_iff] at hov
    rcases hov with hov | hov <;> (exfalso; revert hov; decide)
  · left
    show ((1 : i64) + (2 : i64)).toInt ≤ ((10 : i64)).toInt
    decide

/-- `triangle_area 1 2 3 = -1`. Degenerate triangle (1 + 2 = 3): the
    triangle inequality is non-strict, so the function correctly rejects
    it as invalid. Exercises the `a + b ≤ c` boundary of the validity
    check. -/
theorem triangle_area_1_2_3 :
    clever_070_triangle_area.triangle_area 1 2 3 = RustM.ok (-1 : i64) := by
  apply triangle_area_invalid_returns_minus_one (1 : i64) (2 : i64) (3 : i64)
  · intro hov
    rw [Int64.addOverflow_iff] at hov
    rcases hov with hov | hov <;> (exfalso; revert hov; decide)
  · intro hov
    rw [Int64.addOverflow_iff] at hov
    rcases hov with hov | hov <;> (exfalso; revert hov; decide)
  · intro hov
    rw [Int64.addOverflow_iff] at hov
    rcases hov with hov | hov <;> (exfalso; revert hov; decide)
  · left
    show ((1 : i64) + (2 : i64)).toInt ≤ ((3 : i64)).toInt
    decide

/-- `triangle_area 3 4 5 = 600`. The 3-4-5 right triangle has true area
    `6.00`, encoded as `600`. Discharged via the valid-branch helper:
    instantiates the closed-form bound at a=3, b=4, c=5 (where
    `s2 = 12·6·4·2 = 576`, `s2·625 = 360000`, `r² ≤ 360000 < (r+1)²`
    forces `r = 600`). -/
theorem triangle_area_3_4_5 :
    clever_070_triangle_area.triangle_area 3 4 5 = RustM.ok (600 : i64) := by
  obtain ⟨r, hr_eq, hr_nn, hr_sq, hr_succ⟩ :=
    triangle_area_valid_helper (3 : i64) (4 : i64) (5 : i64)
      (by intro hov; rw [Int64.addOverflow_iff] at hov
          rcases hov with h | h <;> revert h <;> decide)
      (by intro hov; rw [Int64.addOverflow_iff] at hov
          rcases hov with h | h <;> revert h <;> decide)
      (by intro hov; rw [Int64.addOverflow_iff] at hov
          rcases hov with h | h <;> revert h <;> decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide)
  -- s2 = 576, so r² ≤ 360000 < (r+1)². Hence r = 600.
  have h1 : r.toInt * r.toInt ≤ 360000 := by
    have : ((3 : i64).toInt + (4 : i64).toInt + (5 : i64).toInt) *
        ((4 : i64).toInt + (5 : i64).toInt - (3 : i64).toInt) *
        ((3 : i64).toInt - (4 : i64).toInt + (5 : i64).toInt) *
        ((3 : i64).toInt + (4 : i64).toInt - (5 : i64).toInt) * 625 = 360000 := by decide
    omega
  have h2 : 360000 < (r.toInt + 1) * (r.toInt + 1) := by
    have : ((3 : i64).toInt + (4 : i64).toInt + (5 : i64).toInt) *
        ((4 : i64).toInt + (5 : i64).toInt - (3 : i64).toInt) *
        ((3 : i64).toInt - (4 : i64).toInt + (5 : i64).toInt) *
        ((3 : i64).toInt + (4 : i64).toInt - (5 : i64).toInt) * 625 = 360000 := by decide
    omega
  -- r² ≤ 360000 < (r+1)² with r ≥ 0 forces r = 600.
  have h_r_eq : r.toInt = 600 := by
    by_cases h : r.toInt < 600
    · exfalso
      -- r ≤ 599, so (r+1)² ≤ 600² = 360000, contradicting h2.
      have h_r1_le : r.toInt + 1 ≤ 600 := by omega
      have h_r1_nn : 0 ≤ r.toInt + 1 := by omega
      have h_600_nn : (0 : Int) ≤ 600 := by decide
      have h_sq_le : (r.toInt + 1) * (r.toInt + 1) ≤ 600 * 600 :=
        Int.mul_le_mul h_r1_le h_r1_le h_r1_nn h_600_nn
      have h_360000 : (600 : Int) * 600 = 360000 := by decide
      omega
    · by_cases h' : 600 < r.toInt
      · exfalso
        -- r ≥ 601, so r² ≥ 601² > 360000, contradicting h1.
        have h_601_le : 601 ≤ r.toInt := by omega
        have h_601_nn : (0 : Int) ≤ 601 := by decide
        have h_sq_ge : 601 * 601 ≤ r.toInt * r.toInt :=
          Int.mul_le_mul h_601_le h_601_le h_601_nn (by omega)
        have h_361201 : (601 : Int) * 601 = 361201 := by decide
        omega
      · omega
  -- Now r is the i64 with toInt = 600, hence r = 600.
  have : r = (600 : i64) := by
    apply Int64.toInt_inj.mp
    rw [h_r_eq]; decide
  rw [this] at hr_eq
  exact hr_eq

/-- `triangle_area 6 8 10 = 2400`. The 6-8-10 right triangle (scaled
    3-4-5) has true area `24.00`, encoded as `2400`. Discharged via the
    valid-branch helper. -/
theorem triangle_area_6_8_10 :
    clever_070_triangle_area.triangle_area 6 8 10 = RustM.ok (2400 : i64) := by
  obtain ⟨r, hr_eq, hr_nn, hr_sq, hr_succ⟩ :=
    triangle_area_valid_helper (6 : i64) (8 : i64) (10 : i64)
      (by intro hov; rw [Int64.addOverflow_iff] at hov
          rcases hov with h | h <;> revert h <;> decide)
      (by intro hov; rw [Int64.addOverflow_iff] at hov
          rcases hov with h | h <;> revert h <;> decide)
      (by intro hov; rw [Int64.addOverflow_iff] at hov
          rcases hov with h | h <;> revert h <;> decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide)
  -- s2 = 24·12·8·4 = 9216; s2·625 = 5760000; r² ≤ 5760000 < (r+1)² ⇒ r = 2400.
  have h1 : r.toInt * r.toInt ≤ 5760000 := by
    have : ((6 : i64).toInt + (8 : i64).toInt + (10 : i64).toInt) *
        ((8 : i64).toInt + (10 : i64).toInt - (6 : i64).toInt) *
        ((6 : i64).toInt - (8 : i64).toInt + (10 : i64).toInt) *
        ((6 : i64).toInt + (8 : i64).toInt - (10 : i64).toInt) * 625 = 5760000 := by decide
    omega
  have h2 : 5760000 < (r.toInt + 1) * (r.toInt + 1) := by
    have : ((6 : i64).toInt + (8 : i64).toInt + (10 : i64).toInt) *
        ((8 : i64).toInt + (10 : i64).toInt - (6 : i64).toInt) *
        ((6 : i64).toInt - (8 : i64).toInt + (10 : i64).toInt) *
        ((6 : i64).toInt + (8 : i64).toInt - (10 : i64).toInt) * 625 = 5760000 := by decide
    omega
  have h_r_eq : r.toInt = 2400 := by
    by_cases h : r.toInt < 2400
    · exfalso
      have h_r1_le : r.toInt + 1 ≤ 2400 := by omega
      have h_r1_nn : 0 ≤ r.toInt + 1 := by omega
      have h_2400_nn : (0 : Int) ≤ 2400 := by decide
      have h_sq_le : (r.toInt + 1) * (r.toInt + 1) ≤ 2400 * 2400 :=
        Int.mul_le_mul h_r1_le h_r1_le h_r1_nn h_2400_nn
      have h_val : (2400 : Int) * 2400 = 5760000 := by decide
      omega
    · by_cases h' : 2400 < r.toInt
      · exfalso
        have h_2401_le : 2401 ≤ r.toInt := by omega
        have h_2401_nn : (0 : Int) ≤ 2401 := by decide
        have h_sq_ge : 2401 * 2401 ≤ r.toInt * r.toInt :=
          Int.mul_le_mul h_2401_le h_2401_le h_2401_nn (by omega)
        have h_val : (2401 : Int) * 2401 = 5764801 := by decide
        omega
      · omega
  have : r = (2400 : i64) := by
    apply Int64.toInt_inj.mp
    rw [h_r_eq]; decide
  rw [this] at hr_eq
  exact hr_eq

end Clever_070_triangle_areaObligations
