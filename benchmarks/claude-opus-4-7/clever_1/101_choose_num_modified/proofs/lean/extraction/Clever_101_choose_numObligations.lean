-- Companion obligations file for the `clever_101_choose_num` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_101_choose_num

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_101_choose_numObligations

open clever_101_choose_num

/-- An `i64` value is even, interpreted at the `Int` level (sign-agnostic). -/
private abbrev isEven (z : i64) : Prop := z.toInt % 2 = 0

/-! ## Standard helpers (mirrored from `pluck_modified` / `clever_084_solve_modified`). -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

/-- `(y %? 2 : RustM i64) = RustM.ok (y % 2)` since `2 ≠ -1, 0`. -/
private theorem i64_rem_two_eq (y : i64) :
    (y %? (2 : i64) : RustM i64) = RustM.ok (y % 2) := by
  show (rust_primitives.ops.arith.Rem.rem y 2 : RustM i64) = RustM.ok (y % 2)
  show (if (y = Int64.minValue && (2 : i64) = -1) then
          (.fail .integerOverflow : RustM i64)
        else if (2 : i64) = 0 then .fail .divisionByZero
        else pure (y % 2)) = _
  have h_and : (y = Int64.minValue && decide ((2 : i64) = -1)) = false := by
    rw [show (decide ((2 : i64) = -1)) = false from by decide]
    exact Bool.and_false _
  rw [h_and]
  rw [if_neg (by decide : ¬ ((2 : i64) = 0))]
  rfl

/-- `y % 2 = 0 ↔ y.toInt % 2 = 0` for `i64`. -/
private theorem i64_mod_two_eq_zero_iff (y : i64) :
    ((y % (2 : i64)) = (0 : i64)) ↔ y.toInt % 2 = 0 := by
  constructor
  · intro h
    have h_toInt : (y % 2 : i64).toInt = (0 : i64).toInt := by rw [h]
    have h_via128 : (y % 2 : i64).toInt128.toInt
                     = (y.toInt128 % (2 : i64).toInt128).toInt := by
      rw [Int64.toInt128_mod]
    rw [Int64.toInt_toInt128] at h_via128
    rw [h_via128] at h_toInt
    rw [Int128.toInt_mod] at h_toInt
    rw [Int64.toInt_toInt128] at h_toInt
    rw [show (((2 : i64).toInt128).toInt) = (2 : Int) from rfl] at h_toInt
    rw [show ((0 : i64).toInt) = (0 : Int) from by decide] at h_toInt
    have h_dvd : (2 : Int) ∣ y.toInt := Int.dvd_of_tmod_eq_zero h_toInt
    exact Int.emod_eq_zero_of_dvd h_dvd
  · intro h
    apply Int64.toInt_inj.mp
    have h_via128 : (y % 2 : i64).toInt128.toInt
                     = (y.toInt128 % (2 : i64).toInt128).toInt := by
      rw [Int64.toInt128_mod]
    rw [Int64.toInt_toInt128] at h_via128
    rw [h_via128]
    rw [Int128.toInt_mod]
    rw [Int64.toInt_toInt128]
    rw [show (((2 : i64).toInt128).toInt) = (2 : Int) from rfl]
    rw [show ((0 : i64).toInt) = (0 : Int) from by decide]
    have h_dvd : (2 : Int) ∣ y.toInt := Int.dvd_of_emod_eq_zero h
    exact Int.tmod_eq_zero_of_dvd h_dvd

/-- `Int64.minValue` is even at the `Int` level. -/
private theorem isEven_minValue : isEven Int64.minValue := by decide

/-- If `y` is odd, then `y ≠ Int64.minValue` (because `minValue` is even). -/
private theorem ne_minValue_of_not_isEven {y : i64} (hodd : ¬ isEven y) :
    y ≠ Int64.minValue := by
  intro heq
  apply hodd
  rw [heq]
  exact isEven_minValue

/-- For an odd `y`, the signed subtraction `y - 1` does not overflow. -/
private theorem subOverflow_one_eq_false_of_not_isEven {y : i64} (hodd : ¬ isEven y) :
    BitVec.ssubOverflow y.toBitVec (1 : i64).toBitVec = false := by
  generalize hb : BitVec.ssubOverflow y.toBitVec (1 : i64).toBitVec = b
  cases b with
  | false => rfl
  | true =>
    exfalso
    have hov : Int64.subOverflow y (1 : i64) = true := hb
    have hov' := Int64.subOverflow_iff.mp hov
    have h_one_toInt : (1 : i64).toInt = (1 : Int) := by decide
    rw [h_one_toInt] at hov'
    have h_y_lb : -(2^63 : Int) ≤ y.toInt := by
      have := Int64.le_toInt y
      simpa using this
    have h_y_ub : y.toInt < 2^63 := by
      have := Int64.toInt_lt y
      simpa using this
    rcases hov' with hov_pos | hov_neg
    · omega
    · have h_y_min : y.toInt = -(2^63 : Int) := by omega
      have h_min_toInt : (Int64.minValue : i64).toInt = -(2^63 : Int) := by decide
      have h_eq : y.toInt = (Int64.minValue : i64).toInt := by
        rw [h_y_min, h_min_toInt]
      have h_y_eq : y = Int64.minValue := Int64.toInt_inj.mp h_eq
      exact (ne_minValue_of_not_isEven hodd) h_y_eq

/-- For an odd `y`, `(y -? 1 : RustM i64) = RustM.ok (y - 1)`. -/
private theorem i64_sub_one_eq_of_odd {y : i64} (hodd : ¬ isEven y) :
    (y -? (1 : i64) : RustM i64) = RustM.ok (y - 1) := by
  show (rust_primitives.ops.arith.Sub.sub y (1 : i64) : RustM i64) = RustM.ok (y - 1)
  show (if BitVec.ssubOverflow y.toBitVec (1 : i64).toBitVec
        then (.fail .integerOverflow : RustM i64)
        else pure (y - 1)) = _
  rw [subOverflow_one_eq_false_of_not_isEven hodd]
  rfl

/-- For an odd `y`, `(y - 1).toInt = y.toInt - 1`. -/
private theorem i64_sub_one_toInt_of_odd {y : i64} (hodd : ¬ isEven y) :
    (y - 1).toInt = y.toInt - 1 := by
  have h_no : ¬ Int64.subOverflow y (1 : i64) := by
    intro hov
    have hb : BitVec.ssubOverflow y.toBitVec (1 : i64).toBitVec = true := hov
    rw [subOverflow_one_eq_false_of_not_isEven hodd] at hb
    exact Bool.noConfusion hb
  have h := Int64.toInt_sub_of_not_subOverflow h_no
  have h_one_toInt : (1 : i64).toInt = (1 : Int) := by decide
  rw [h_one_toInt] at h
  exact h

/-! ## Master evaluation lemma.

`choose_num x y` always succeeds, and the result is determined by a small
case analysis. The four cases correspond to the four branches of the
function. -/

/-- Case 1: `x > y` returns the sentinel `-1`. -/
private theorem choose_num_eq_neg1_of_gt
    (x y : i64) (hgt : x > y) :
    choose_num x y = RustM.ok (-1 : i64) := by
  unfold choose_num
  show (do
        if (← (x >? y)) then pure (-1 : i64)
        else (do
          if (← ((← (y %? (2 : i64))) ==? (0 : i64))) then pure y
          else (do
            if (← ((← (y -? (1 : i64))) >=? x)) then (y -? (1 : i64))
            else (pure (-1 : i64))))) = _
  have h_gt : (x >? y : RustM Bool) = RustM.ok true := by
    show (rust_primitives.cmp.gt x y : RustM Bool) = _
    show (pure (decide (x > y)) : RustM Bool) = _
    rw [decide_eq_true hgt]
    rfl
  rw [h_gt]
  rfl

/-- Case 2: `x ≤ y ∧ y` is even returns `y`. -/
private theorem choose_num_eq_y_of_le_even
    (x y : i64) (hle : ¬ x > y) (heven : isEven y) :
    choose_num x y = RustM.ok y := by
  unfold choose_num
  show (do
        if (← (x >? y)) then pure (-1 : i64)
        else (do
          if (← ((← (y %? (2 : i64))) ==? (0 : i64))) then pure y
          else (do
            if (← ((← (y -? (1 : i64))) >=? x)) then (y -? (1 : i64))
            else (pure (-1 : i64))))) = _
  have h_gt : (x >? y : RustM Bool) = RustM.ok false := by
    show (rust_primitives.cmp.gt x y : RustM Bool) = _
    show (pure (decide (x > y)) : RustM Bool) = _
    rw [decide_eq_false hle]
    rfl
  rw [h_gt]
  have h_rem := i64_rem_two_eq y
  have h_mod_zero : (y % (2 : i64)) = (0 : i64) :=
    (i64_mod_two_eq_zero_iff y).mpr heven
  have h_eq_zero : ((y % (2 : i64)) ==? (0 : i64) : RustM Bool) = RustM.ok true := by
    show (rust_primitives.cmp.eq (y % (2 : i64)) (0 : i64) : RustM Bool) = _
    show (pure ((y % (2 : i64)) == (0 : i64)) : RustM Bool) = _
    rw [h_mod_zero]
    rfl
  simp only [RustM_ok_bind, Bool.false_eq_true, ↓reduceIte, h_rem, h_eq_zero]
  rfl

/-- Case 3: `x ≤ y ∧ y` is odd and `y - 1 ≥ x` returns `y - 1`. -/
private theorem choose_num_eq_ymin1
    (x y : i64) (hle : ¬ x > y) (hodd : ¬ isEven y) (hge : y - 1 ≥ x) :
    choose_num x y = RustM.ok (y - 1) := by
  unfold choose_num
  show (do
        if (← (x >? y)) then pure (-1 : i64)
        else (do
          if (← ((← (y %? (2 : i64))) ==? (0 : i64))) then pure y
          else (do
            if (← ((← (y -? (1 : i64))) >=? x)) then (y -? (1 : i64))
            else (pure (-1 : i64))))) = _
  have h_gt : (x >? y : RustM Bool) = RustM.ok false := by
    show (rust_primitives.cmp.gt x y : RustM Bool) = _
    show (pure (decide (x > y)) : RustM Bool) = _
    rw [decide_eq_false hle]; rfl
  rw [h_gt]
  have h_rem := i64_rem_two_eq y
  have h_mod_nz : (y % (2 : i64)) ≠ (0 : i64) := by
    intro h
    exact hodd ((i64_mod_two_eq_zero_iff y).mp h)
  have h_eq_zero : ((y % (2 : i64)) ==? (0 : i64) : RustM Bool) = RustM.ok false := by
    show (rust_primitives.cmp.eq (y % (2 : i64)) (0 : i64) : RustM Bool) = _
    show (pure ((y % (2 : i64)) == (0 : i64)) : RustM Bool) = _
    have : ((y % (2 : i64)) == (0 : i64)) = false := by
      rw [beq_eq_false_iff_ne]; exact h_mod_nz
    rw [this]; rfl
  have h_sub := i64_sub_one_eq_of_odd hodd
  have h_ge : ((y - 1) >=? x : RustM Bool) = RustM.ok true := by
    show (rust_primitives.cmp.ge (y - 1) x : RustM Bool) = _
    show (pure (decide ((y - 1) ≥ x)) : RustM Bool) = _
    rw [decide_eq_true hge]; rfl
  simp only [RustM_ok_bind, Bool.false_eq_true, ↓reduceIte,
             h_rem, h_eq_zero, h_sub, h_ge]

/-- Case 4: `x ≤ y ∧ y` is odd and `y - 1 < x` returns `-1`. -/
private theorem choose_num_eq_neg1_of_le_odd_lt
    (x y : i64) (hle : ¬ x > y) (hodd : ¬ isEven y) (hlt : ¬ y - 1 ≥ x) :
    choose_num x y = RustM.ok (-1 : i64) := by
  unfold choose_num
  show (do
        if (← (x >? y)) then pure (-1 : i64)
        else (do
          if (← ((← (y %? (2 : i64))) ==? (0 : i64))) then pure y
          else (do
            if (← ((← (y -? (1 : i64))) >=? x)) then (y -? (1 : i64))
            else (pure (-1 : i64))))) = _
  have h_gt : (x >? y : RustM Bool) = RustM.ok false := by
    show (rust_primitives.cmp.gt x y : RustM Bool) = _
    show (pure (decide (x > y)) : RustM Bool) = _
    rw [decide_eq_false hle]; rfl
  rw [h_gt]
  have h_rem := i64_rem_two_eq y
  have h_mod_nz : (y % (2 : i64)) ≠ (0 : i64) := by
    intro h
    exact hodd ((i64_mod_two_eq_zero_iff y).mp h)
  have h_eq_zero : ((y % (2 : i64)) ==? (0 : i64) : RustM Bool) = RustM.ok false := by
    show (rust_primitives.cmp.eq (y % (2 : i64)) (0 : i64) : RustM Bool) = _
    show (pure ((y % (2 : i64)) == (0 : i64)) : RustM Bool) = _
    have : ((y % (2 : i64)) == (0 : i64)) = false := by
      rw [beq_eq_false_iff_ne]; exact h_mod_nz
    rw [this]; rfl
  have h_sub := i64_sub_one_eq_of_odd hodd
  have h_ge : ((y - 1) >=? x : RustM Bool) = RustM.ok false := by
    show (rust_primitives.cmp.ge (y - 1) x : RustM Bool) = _
    show (pure (decide ((y - 1) ≥ x)) : RustM Bool) = _
    rw [decide_eq_false hlt]; rfl
  simp only [RustM_ok_bind, Bool.false_eq_true, ↓reduceIte,
             h_rem, h_eq_zero, h_sub, h_ge]
  rfl

/-! ## Master result: a closed-form characterisation of `choose_num x y`. -/

/-- Closed form of `choose_num` at the `Int` level. -/
private theorem choose_num_master (x y : i64) :
    ∃ r : i64, choose_num x y = RustM.ok r ∧
      ((y.toInt < x.toInt ∨ (x = y ∧ ¬ isEven y)) → r = (-1 : i64)) ∧
      ((¬ y.toInt < x.toInt ∧ isEven y) → r = y) ∧
      ((¬ y.toInt < x.toInt ∧ ¬ isEven y ∧ x.toInt < y.toInt) → r = y - 1) ∧
      ((¬ y.toInt < x.toInt ∧ ¬ isEven y ∧ ¬ x.toInt < y.toInt) → r = (-1 : i64))
       := by
  by_cases hgt : x > y
  · refine ⟨(-1 : i64), choose_num_eq_neg1_of_gt x y hgt, ?_, ?_, ?_, ?_⟩
    · intro _; rfl
    · intro ⟨h_le_int, _⟩
      have : y.toInt < x.toInt := Int64.lt_iff_toInt_lt.mp hgt
      exact absurd this h_le_int
    · intro ⟨h_le_int, _, _⟩
      have : y.toInt < x.toInt := Int64.lt_iff_toInt_lt.mp hgt
      exact absurd this h_le_int
    · intro ⟨h_le_int, _, _⟩
      have : y.toInt < x.toInt := Int64.lt_iff_toInt_lt.mp hgt
      exact absurd this h_le_int
  · by_cases heven : isEven y
    · refine ⟨y, choose_num_eq_y_of_le_even x y hgt heven, ?_, ?_, ?_, ?_⟩
      · rintro (h_lt | ⟨hxy, hodd⟩)
        · have : x > y := Int64.lt_iff_toInt_lt.mpr h_lt
          exact absurd this hgt
        · exact absurd (hxy ▸ heven) hodd
      · intro _; rfl
      · intro ⟨_, hodd, _⟩
        exact absurd heven hodd
      · intro ⟨_, hodd, _⟩
        exact absurd heven hodd
    · by_cases hge_i : y - 1 ≥ x
      · refine ⟨y - 1, choose_num_eq_ymin1 x y hgt heven hge_i, ?_, ?_, ?_, ?_⟩
        · rintro (h_lt | ⟨hxy, _⟩)
          · have : x > y := Int64.lt_iff_toInt_lt.mpr h_lt
            exact absurd this hgt
          · subst hxy
            have h_le : x.toInt ≤ (x - 1).toInt := Int64.le_iff_toInt_le.mp hge_i
            rw [i64_sub_one_toInt_of_odd heven] at h_le
            omega
        · intro ⟨_, hodd_iff⟩
          exact absurd hodd_iff heven
        · intro _; rfl
        · intro ⟨_, _, h_not_lt⟩
          have h_le_int : x.toInt ≤ (y - 1).toInt := Int64.le_iff_toInt_le.mp hge_i
          rw [i64_sub_one_toInt_of_odd heven] at h_le_int
          omega
      · refine ⟨(-1 : i64), choose_num_eq_neg1_of_le_odd_lt x y hgt heven hge_i, ?_, ?_, ?_, ?_⟩
        · intro _; rfl
        · intro ⟨_, hodd_iff⟩
          exact absurd hodd_iff heven
        · intro ⟨_, _, h_x_lt⟩
          have h_not_le : ¬ x.toInt ≤ (y - 1).toInt := by
            intro h_le
            exact hge_i (Int64.le_iff_toInt_le.mpr h_le)
          rw [i64_sub_one_toInt_of_odd heven] at h_not_le
          omega
        · intro _; rfl

/-! ## Contract clauses

`choose_num` is total in the Lean model: the only partial operations on
the path are `y %? 2` (safe because `2 ≠ 0, -1`) and `y -? 1` (only
reached when `y` is odd, and `Int64.minValue` is even, so `y ≠ minValue`
and the signed subtraction does not underflow). No precondition is
required for any of the postcondition theorems below. -/

/-- Failure characterization (sentinel iff). -/
theorem choose_num_returns_neg1_iff (x y : i64) :
    ∃ r : i64, choose_num x y = RustM.ok r ∧
      (r = (-1 : i64) ↔ y < x ∨ (x = y ∧ ¬ isEven x)) := by
  obtain ⟨r, hr_eq, h1, h2, h3, h4⟩ := choose_num_master x y
  refine ⟨r, hr_eq, ?_⟩
  constructor
  · intro hr_neg1
    by_cases hgt : x > y
    · -- x > y, i.e., y < x as i64.
      left; exact hgt
    · have h_le_int : ¬ y.toInt < x.toInt := by
        intro h
        exact hgt (Int64.lt_iff_toInt_lt.mpr h)
      by_cases heven : isEven y
      · have h_r_y : r = y := h2 ⟨h_le_int, heven⟩
        rw [h_r_y] at hr_neg1
        have h_minus_one_not_even : ¬ isEven ((-1) : i64) := by decide
        rw [hr_neg1] at heven
        exact absurd heven h_minus_one_not_even
      · by_cases hxlt : x.toInt < y.toInt
        · have h_r : r = y - 1 := h3 ⟨h_le_int, heven, hxlt⟩
          rw [h_r] at hr_neg1
          have h_toInt_eq : (y - 1).toInt = ((-1) : i64).toInt := by rw [hr_neg1]
          rw [i64_sub_one_toInt_of_odd heven] at h_toInt_eq
          have h_minus_one_toInt : ((-1) : i64).toInt = -1 := by decide
          rw [h_minus_one_toInt] at h_toInt_eq
          have h_y_toInt : y.toInt = 0 := by omega
          have h_zero_toInt : (0 : i64).toInt = 0 := by decide
          have h_y_eq_zero : y = 0 := by
            apply Int64.toInt_inj.mp
            rw [h_y_toInt, h_zero_toInt]
          have h_zero_even : isEven (0 : i64) := by decide
          rw [h_y_eq_zero] at heven
          exact absurd h_zero_even heven
        · -- ¬ y.toInt < x.toInt and ¬ x.toInt < y.toInt → x.toInt = y.toInt → x = y.
          have h_xy_int : x.toInt = y.toInt := by omega
          have h_xy : x = y := Int64.toInt_inj.mp h_xy_int
          right
          refine ⟨h_xy, ?_⟩
          rw [h_xy]; exact heven
  · rintro (hlt | ⟨hxy, hxodd⟩)
    · have h_lt_int : y.toInt < x.toInt := Int64.lt_iff_toInt_lt.mp hlt
      exact h1 (Or.inl h_lt_int)
    · have h_y_odd : ¬ isEven y := by rw [← hxy]; exact hxodd
      apply h1
      right
      exact ⟨hxy, h_y_odd⟩

/-- Postcondition (evenness): a non-sentinel result is an even integer. -/
theorem choose_num_result_is_even (x y : i64) :
    ∃ r : i64, choose_num x y = RustM.ok r ∧
      (r ≠ (-1 : i64) → isEven r) := by
  obtain ⟨r, hr_eq, h1, h2, h3, h4⟩ := choose_num_master x y
  refine ⟨r, hr_eq, ?_⟩
  intro hr_ne
  by_cases hgt : x > y
  · have : r = (-1 : i64) := h1 (Or.inl (Int64.lt_iff_toInt_lt.mp hgt))
    exact absurd this hr_ne
  · have h_le_int : ¬ y.toInt < x.toInt := by
      intro h; exact hgt (Int64.lt_iff_toInt_lt.mpr h)
    by_cases heven : isEven y
    · have h_r_y : r = y := h2 ⟨h_le_int, heven⟩
      rw [h_r_y]; exact heven
    · by_cases hxlt : x.toInt < y.toInt
      · have h_r : r = y - 1 := h3 ⟨h_le_int, heven, hxlt⟩
        rw [h_r]
        unfold isEven
        rw [i64_sub_one_toInt_of_odd heven]
        have h_odd_int : y.toInt % 2 ≠ 0 := heven
        have h0 : 0 ≤ y.toInt % 2 := Int.emod_nonneg _ (by decide : (2 : Int) ≠ 0)
        have h1' : y.toInt % 2 < 2 := Int.emod_lt_of_pos _ (by decide : (0 : Int) < 2)
        have h_y_odd : y.toInt % 2 = 1 := by omega
        omega
      · have : r = (-1 : i64) := h4 ⟨h_le_int, heven, hxlt⟩
        exact absurd this hr_ne

/-- Postcondition (range, lower bound): a non-sentinel result is at least `x`. -/
theorem choose_num_result_ge_x (x y : i64) :
    ∃ r : i64, choose_num x y = RustM.ok r ∧
      (r ≠ (-1 : i64) → x ≤ r) := by
  obtain ⟨r, hr_eq, h1, h2, h3, h4⟩ := choose_num_master x y
  refine ⟨r, hr_eq, ?_⟩
  intro hr_ne
  by_cases hgt : x > y
  · have : r = (-1 : i64) := h1 (Or.inl (Int64.lt_iff_toInt_lt.mp hgt))
    exact absurd this hr_ne
  · have h_le_int : ¬ y.toInt < x.toInt := by
      intro h; exact hgt (Int64.lt_iff_toInt_lt.mpr h)
    by_cases heven : isEven y
    · have h_r_y : r = y := h2 ⟨h_le_int, heven⟩
      rw [h_r_y]
      apply Int64.le_iff_toInt_le.mpr
      omega
    · by_cases hxlt : x.toInt < y.toInt
      · have h_r : r = y - 1 := h3 ⟨h_le_int, heven, hxlt⟩
        rw [h_r]
        apply Int64.le_iff_toInt_le.mpr
        rw [i64_sub_one_toInt_of_odd heven]
        omega
      · have : r = (-1 : i64) := h4 ⟨h_le_int, heven, hxlt⟩
        exact absurd this hr_ne

/-- Postcondition (range, upper bound): a non-sentinel result is at most `y`. -/
theorem choose_num_result_le_y (x y : i64) :
    ∃ r : i64, choose_num x y = RustM.ok r ∧
      (r ≠ (-1 : i64) → r ≤ y) := by
  obtain ⟨r, hr_eq, h1, h2, h3, h4⟩ := choose_num_master x y
  refine ⟨r, hr_eq, ?_⟩
  intro hr_ne
  by_cases hgt : x > y
  · have : r = (-1 : i64) := h1 (Or.inl (Int64.lt_iff_toInt_lt.mp hgt))
    exact absurd this hr_ne
  · have h_le_int : ¬ y.toInt < x.toInt := by
      intro h; exact hgt (Int64.lt_iff_toInt_lt.mpr h)
    by_cases heven : isEven y
    · have h_r_y : r = y := h2 ⟨h_le_int, heven⟩
      rw [h_r_y]
      apply Int64.le_iff_toInt_le.mpr
      omega
    · by_cases hxlt : x.toInt < y.toInt
      · have h_r : r = y - 1 := h3 ⟨h_le_int, heven, hxlt⟩
        rw [h_r]
        apply Int64.le_iff_toInt_le.mpr
        rw [i64_sub_one_toInt_of_odd heven]
        omega
      · have : r = (-1 : i64) := h4 ⟨h_le_int, heven, hxlt⟩
        exact absurd this hr_ne

/-- Postcondition (maximality): for a non-sentinel result, `r + 2 > y`
    at the `Int` level. -/
theorem choose_num_result_is_maximal (x y : i64) :
    ∃ r : i64, choose_num x y = RustM.ok r ∧
      (r ≠ (-1 : i64) → r.toInt + 2 > y.toInt) := by
  obtain ⟨r, hr_eq, h1, h2, h3, h4⟩ := choose_num_master x y
  refine ⟨r, hr_eq, ?_⟩
  intro hr_ne
  by_cases hgt : x > y
  · have : r = (-1 : i64) := h1 (Or.inl (Int64.lt_iff_toInt_lt.mp hgt))
    exact absurd this hr_ne
  · have h_le_int : ¬ y.toInt < x.toInt := by
      intro h; exact hgt (Int64.lt_iff_toInt_lt.mpr h)
    by_cases heven : isEven y
    · have h_r_y : r = y := h2 ⟨h_le_int, heven⟩
      rw [h_r_y]; omega
    · by_cases hxlt : x.toInt < y.toInt
      · have h_r : r = y - 1 := h3 ⟨h_le_int, heven, hxlt⟩
        rw [h_r]
        rw [i64_sub_one_toInt_of_odd heven]
        omega
      · have : r = (-1 : i64) := h4 ⟨h_le_int, heven, hxlt⟩
        exact absurd this hr_ne

end Clever_101_choose_numObligations
