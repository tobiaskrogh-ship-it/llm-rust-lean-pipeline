-- Companion obligations file for the `clever_107_count_nums` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_107_count_nums

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_107_count_numsObligations

/-! ## Common helpers and `i64` toInt facts. -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide
private theorem i64_one_toInt  : (1 : i64).toInt = 1 := by decide
private theorem i64_two_toInt  : (2 : i64).toInt = 2 := by decide
private theorem i64_ten_toInt  : (10 : i64).toInt = 10 := by decide
private theorem int64_min_toInt : Int64.minValue.toInt = -(2^63 : Int) := by decide

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl
private theorem usize_zero_toNat : (0 : usize).toNat = 0 := rfl

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

private theorem i64_lt_max (n : i64) : n.toInt < 2^63 := by
  have h := Int64.toInt_lt n
  have h63 : (Int64.size : Int) / 2 = 2^63 := by decide
  omega

private theorem i64_min_le (n : i64) : -(2^63 : Int) ≤ n.toInt := by
  have h := Int64.minValue_le n
  have h_min : Int64.minValue.toInt = -(2^63 : Int) := int64_min_toInt
  have h_iff : Int64.minValue.toInt ≤ n.toInt := Int64.le_iff_toInt_le.mp h
  rw [h_min] at h_iff
  exact h_iff

/-! ## Reductions for primitive ops on `i64` with constant divisors / negation. -/

/-- `n /? 10` always succeeds (10 ≠ 0, 10 ≠ -1). -/
private theorem i64_div_10 (n : i64) :
    (n /? (10 : i64) : RustM i64) = pure (n / 10) := by
  show (rust_primitives.ops.arith.Div.div n (10 : i64) : RustM i64) = pure (n / 10)
  show (if n = Int64.minValue && (10 : i64) = -1 then
          (.fail .integerOverflow : RustM i64)
        else if (10 : i64) = 0 then .fail .divisionByZero
        else pure (n / 10)) = pure (n / 10)
  have h_and : (n = Int64.minValue && ((10 : i64) = -1)) = false := by
    show (decide (n = Int64.minValue) && decide ((10 : i64) = -1)) = false
    rw [show decide ((10 : i64) = -1) = false from by decide, Bool.and_false]
  rw [h_and, if_neg (by decide : (10 : i64) ≠ 0)]; rfl

/-- `n %? 10` always succeeds (10 ≠ 0, 10 ≠ -1). -/
private theorem i64_mod_10 (n : i64) :
    (n %? (10 : i64) : RustM i64) = pure (n % 10) := by
  show (rust_primitives.ops.arith.Rem.rem n (10 : i64) : RustM i64) = pure (n % 10)
  show (if n = Int64.minValue && (10 : i64) = -1 then
          (.fail .integerOverflow : RustM i64)
        else if (10 : i64) = 0 then .fail .divisionByZero
        else pure (n % 10)) = pure (n % 10)
  have h_and : (n = Int64.minValue && ((10 : i64) = -1)) = false := by
    show (decide (n = Int64.minValue) && decide ((10 : i64) = -1)) = false
    rw [show decide ((10 : i64) = -1) = false from by decide, Bool.and_false]
  rw [h_and, if_neg (by decide : (10 : i64) ≠ 0)]; rfl

/-- `-? n` succeeds when `n ≠ Int64.minValue`. -/
private theorem i64_neg (n : i64) (h : n ≠ Int64.minValue) :
    (-? n : RustM i64) = pure (- n) := by
  show (rust_primitives.ops.arith.Neg.neg n : RustM i64) = pure (- n)
  show (if n = Int64.minValue then (.fail .integerOverflow : RustM i64)
        else pure (- n)) = _
  rw [if_neg h]

/-- `a +? b` succeeds when the addition doesn't overflow. -/
private theorem i64_add_pure (a b : i64) (h : ¬ Int64.addOverflow a b) :
    (a +? b : RustM i64) = pure (a + b) := by
  show (rust_primitives.ops.arith.Add.add a b : RustM i64) = _
  show (if BitVec.saddOverflow a.toBitVec b.toBitVec then
          (.fail .integerOverflow : RustM i64)
        else pure (a + b)) = _
  have h_no_bv : BitVec.saddOverflow a.toBitVec b.toBitVec = false := by
    cases hb : BitVec.saddOverflow a.toBitVec b.toBitVec with
    | false => rfl
    | true => exact absurd hb h
  rw [h_no_bv]; rfl

/-- `a -? b` succeeds when the subtraction doesn't overflow. -/
private theorem i64_sub_pure (a b : i64) (h : ¬ Int64.subOverflow a b) :
    (a -? b : RustM i64) = pure (a - b) := by
  show (rust_primitives.ops.arith.Sub.sub a b : RustM i64) = _
  show (if BitVec.ssubOverflow a.toBitVec b.toBitVec then
          (.fail .integerOverflow : RustM i64)
        else pure (a - b)) = _
  have h_no_bv : BitVec.ssubOverflow a.toBitVec b.toBitVec = false := by
    cases hb : BitVec.ssubOverflow a.toBitVec b.toBitVec with
    | false => rfl
    | true => exact absurd hb h
  rw [h_no_bv]; rfl

/-- `a *? b` (with `a = 2`) when the multiplication doesn't overflow. -/
private theorem i64_mul_pure (a b : i64) (h : ¬ Int64.mulOverflow a b) :
    (a *? b : RustM i64) = pure (a * b) := by
  show (rust_primitives.ops.arith.Mul.mul a b : RustM i64) = _
  show (if BitVec.smulOverflow a.toBitVec b.toBitVec then
          (.fail .integerOverflow : RustM i64)
        else pure (a * b)) = _
  have h_no_bv : BitVec.smulOverflow a.toBitVec b.toBitVec = false := by
    cases hb : BitVec.smulOverflow a.toBitVec b.toBitVec with
    | false => rfl
    | true => exact absurd hb h
  rw [h_no_bv]; rfl

/-! ## Nat-level oracles for digit decomposition. -/

/-- Leading decimal digit of `n` (for `n = 0`, returns 0). -/
private def first_digit_nat (n : Nat) : Nat :=
  if n < 10 then n else first_digit_nat (n / 10)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

/-- Sum of the decimal digits of `n`, added to `acc`. -/
private def digit_sum_nat (n acc : Nat) : Nat :=
  if h : 0 < n then digit_sum_nat (n / 10) (acc + n % 10)
  else acc
termination_by n
decreasing_by exact Nat.div_lt_self h (by decide)

/-! ### Equations -/

private theorem first_digit_nat_small (n : Nat) (h : n < 10) :
    first_digit_nat n = n := by
  unfold first_digit_nat; rw [if_pos h]

private theorem first_digit_nat_large (n : Nat) (h : ¬ n < 10) :
    first_digit_nat n = first_digit_nat (n / 10) := by
  conv => lhs; unfold first_digit_nat
  rw [if_neg h]

private theorem digit_sum_nat_zero (acc : Nat) : digit_sum_nat 0 acc = acc := by
  unfold digit_sum_nat; rw [dif_neg (by decide : ¬ 0 < 0)]

private theorem digit_sum_nat_succ (n acc : Nat) (h : 0 < n) :
    digit_sum_nat n acc = digit_sum_nat (n / 10) (acc + n % 10) := by
  conv => lhs; unfold digit_sum_nat
  rw [dif_pos h]

/-! ### Properties of `first_digit_nat` -/

private theorem first_digit_nat_lt_10 (n : Nat) : first_digit_nat n < 10 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n < 10
    · rw [first_digit_nat_small n h]; exact h
    · rw [first_digit_nat_large n h]
      apply ih
      have hn_pos : 0 < n := by omega
      exact Nat.div_lt_self hn_pos (by decide)

private theorem first_digit_nat_le_n (n : Nat) : first_digit_nat n ≤ n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n < 10
    · rw [first_digit_nat_small n h]; exact Nat.le_refl n
    · rw [first_digit_nat_large n h]
      have hn_pos : 0 < n := by omega
      have h_div_lt : n / 10 < n := Nat.div_lt_self hn_pos (by decide)
      have ih' : first_digit_nat (n / 10) ≤ n / 10 := ih (n / 10) h_div_lt
      have : n / 10 ≤ n := Nat.div_le_self n 10
      omega

private theorem first_digit_nat_pos (n : Nat) (h : 0 < n) : 0 < first_digit_nat n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hlt : n < 10
    · rw [first_digit_nat_small n hlt]; exact h
    · rw [first_digit_nat_large n hlt]
      have h_div_pos : 0 < n / 10 := by
        have h_ge : 10 ≤ n := by omega
        have : 10 / 10 ≤ n / 10 := Nat.div_le_div_right h_ge
        omega
      have h_div_lt : n / 10 < n := Nat.div_lt_self h (by decide)
      exact ih (n / 10) h_div_lt h_div_pos

/-! ### Properties of `digit_sum_nat` -/

private theorem digit_sum_nat_mono (n acc1 acc2 : Nat) (h : acc1 ≤ acc2) :
    digit_sum_nat n acc1 ≤ digit_sum_nat n acc2 := by
  induction n using Nat.strongRecOn generalizing acc1 acc2 with
  | _ n ih =>
    by_cases hn : 0 < n
    · rw [digit_sum_nat_succ n acc1 hn, digit_sum_nat_succ n acc2 hn]
      apply ih (n / 10) (Nat.div_lt_self hn (by decide))
      omega
    · have hz : n = 0 := by omega
      rw [hz, digit_sum_nat_zero, digit_sum_nat_zero]; exact h

private theorem digit_sum_nat_le_acc_add (n acc : Nat) :
    acc ≤ digit_sum_nat n acc := by
  induction n using Nat.strongRecOn generalizing acc with
  | _ n ih =>
    by_cases hn : 0 < n
    · rw [digit_sum_nat_succ n acc hn]
      have h_le : acc ≤ acc + n % 10 := by omega
      have ih' := ih (n / 10) (Nat.div_lt_self hn (by decide)) (acc + n % 10)
      omega
    · have hz : n = 0 := by omega
      rw [hz, digit_sum_nat_zero]; exact Nat.le_refl acc

/-- Linear bound: each step adds at most 9, recursion depth is ≤ number of digits. -/
private theorem digit_sum_nat_le_pow :
    ∀ (k : Nat) (n acc : Nat), n < 10 ^ k →
      digit_sum_nat n acc ≤ acc + 9 * k := by
  intro k
  induction k with
  | zero =>
    intro n acc h
    have hn : n = 0 := by simp at h; omega
    rw [hn, digit_sum_nat_zero]; omega
  | succ k ih =>
    intro n acc h
    by_cases hn : 0 < n
    · rw [digit_sum_nat_succ n acc hn]
      have h_div_lt : n / 10 < 10 ^ k := by
        have h_split : (10 : Nat) ^ (k + 1) = 10 * 10 ^ k := by
          rw [Nat.pow_succ, Nat.mul_comm]
        rw [h_split] at h
        exact Nat.div_lt_of_lt_mul h
      have h_mod : n % 10 ≤ 9 := by
        have := Nat.mod_lt n (by decide : 0 < 10); omega
      have ih' := ih (n / 10) (acc + n % 10) h_div_lt
      omega
    · have hz : n = 0 := by omega
      rw [hz, digit_sum_nat_zero]; omega

/-- `digit_sum_nat n acc ≤ acc + 9*19` for any `i64`-bounded value. -/
private theorem digit_sum_nat_bound_i64 (n acc : Nat) (h : n < 2^63) :
    digit_sum_nat n acc ≤ acc + 9 * 19 := by
  apply digit_sum_nat_le_pow 19
  have h_le : (2 : Nat) ^ 63 ≤ 10 ^ 19 := by decide
  omega

/-! ## Bridging Int and Nat for n / 10 and n % 10 (non-negative) -/

private theorem int_toNat_ediv {x y : Int} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x / y).toNat = x.toNat / y.toNat :=
  match x, y, Int.eq_ofNat_of_zero_le hx, Int.eq_ofNat_of_zero_le hy with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => rfl

private theorem digit_sum_nat_acc_eq (n acc : Nat) :
    digit_sum_nat n acc = acc + digit_sum_nat n 0 := by
  induction n using Nat.strongRecOn generalizing acc with
  | _ n ih =>
    by_cases hn : 0 < n
    · rw [digit_sum_nat_succ n acc hn, digit_sum_nat_succ n 0 hn]
      rw [ih (n / 10) (Nat.div_lt_self hn (by decide)) (acc + n % 10)]
      rw [ih (n / 10) (Nat.div_lt_self hn (by decide)) (0 + n % 10)]
      omega
    · have hz : n = 0 := by omega
      subst hz
      rw [digit_sum_nat_zero acc, digit_sum_nat_zero 0]

/-- Bridge: convert i64 division by 10 (positive case) to Int. -/
private theorem i64_div_10_toInt (n : i64) (hn : 0 ≤ n.toInt) :
    (n / (10 : i64)).toInt = n.toInt / 10 := by
  have h_ne : (10 : i64) ≠ (-1 : i64) := by decide
  have h_tdiv : (n / (10 : i64)).toInt = n.toInt.tdiv 10 :=
    Int64.toInt_div_of_ne_right n 10 h_ne
  rw [h_tdiv, Int.tdiv_eq_ediv_of_nonneg hn]

private theorem i64_mod_10_toInt (n : i64) (hn : 0 ≤ n.toInt) :
    (n % (10 : i64)).toInt = n.toInt % 10 := by
  have h_tmod : (n % (10 : i64)).toInt = n.toInt.tmod 10 :=
    Int64.toInt_mod n 10
  rw [h_tmod, Int.tmod_eq_emod_of_nonneg hn]

private theorem i64_div_10_nonneg (n : i64) (hn : 0 ≤ n.toInt) :
    0 ≤ (n / (10 : i64)).toInt := by
  rw [i64_div_10_toInt n hn]
  exact Int.ediv_nonneg hn (by decide)

private theorem i64_mod_10_nonneg (n : i64) (hn : 0 ≤ n.toInt) :
    0 ≤ (n % (10 : i64)).toInt := by
  rw [i64_mod_10_toInt n hn]
  exact Int.emod_nonneg n.toInt (by decide)

private theorem i64_mod_10_le_9 (n : i64) (hn : 0 ≤ n.toInt) :
    (n % (10 : i64)).toInt ≤ 9 := by
  rw [i64_mod_10_toInt n hn]
  have h := Int.emod_lt_of_pos n.toInt (by decide : (0 : Int) < 10)
  omega

/-! ## Pointwise correctness of `first_digit_at`. -/

private theorem first_digit_at_correct (n : i64) (hn : 0 ≤ n.toInt) :
    ∃ r : i64,
      clever_107_count_nums.first_digit_at n = RustM.ok r ∧
      r.toInt = (first_digit_nat n.toInt.toNat : Int) ∧
      0 ≤ r.toInt ∧
      r.toInt ≤ 9 := by
  induction hk : n.toInt.toNat using Nat.strongRecOn generalizing n with
  | _ k ih =>
    unfold clever_107_count_nums.first_digit_at
    by_cases h_lt : n < (10 : i64)
    · -- Base case: n < 10. Returns ok n. n.toInt.toNat < 10 so first_digit_nat = identity.
      have h_n_lt_10 : n.toInt < 10 := by
        have := Int64.lt_iff_toInt_lt.mp h_lt
        simpa [i64_ten_toInt] using this
      have h_dec : decide (n < (10 : i64)) = true := decide_eq_true h_lt
      simp only [show (n <? (10 : i64) : RustM Bool) =
                   (pure (decide (n < (10 : i64))) : RustM Bool) from rfl,
                 h_dec, pure_bind, ↓reduceIte]
      have h_n_nat_lt_10 : n.toInt.toNat < 10 := by
        have h_cast : (n.toInt.toNat : Int) = n.toInt := Int.toNat_of_nonneg hn
        have hh : (n.toInt.toNat : Int) < 10 := by rw [h_cast]; exact h_n_lt_10
        exact_mod_cast hh
      have h_fd_eq : first_digit_nat n.toInt.toNat = n.toInt.toNat :=
        first_digit_nat_small n.toInt.toNat h_n_nat_lt_10
      refine ⟨n, rfl, ?_, hn, ?_⟩
      · rw [← hk, h_fd_eq]; exact (Int.toNat_of_nonneg hn).symm
      · have h_cast : (n.toInt.toNat : Int) = n.toInt := Int.toNat_of_nonneg hn
        omega
    · -- Step case: n ≥ 10. Recurses on n / 10.
      have h_n_ge_10 : (10 : Int) ≤ n.toInt := by
        have h_not_lt : ¬ n.toInt < 10 := fun h => h_lt (by
          rw [Int64.lt_iff_toInt_lt, i64_ten_toInt]; exact h)
        omega
      have h_dec : decide (n < (10 : i64)) = false := decide_eq_false h_lt
      simp only [show (n <? (10 : i64) : RustM Bool) =
                   (pure (decide (n < (10 : i64))) : RustM Bool) from rfl,
                 h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
      rw [i64_div_10 n, pure_bind]
      have h_div_nn : 0 ≤ (n / 10).toInt := i64_div_10_nonneg n hn
      have h_div_lt : (n / 10).toInt < n.toInt := by
        rw [i64_div_10_toInt n hn]
        exact Int.ediv_lt_self_of_pos_of_ne_one (by omega) (by decide)
      have h_n_pos : 0 < n.toInt := by omega
      have h_div_nat : (n / 10).toInt.toNat = n.toInt.toNat / 10 := by
        rw [i64_div_10_toInt n hn]
        exact int_toNat_ediv hn (by decide)
      have h_measure : (n / 10).toInt.toNat < k := by
        rw [← hk]
        exact (Int.toNat_lt_toNat (by omega)).mpr h_div_lt
      obtain ⟨r, h_eq, h_int, h_nn, h_le_9⟩ :=
        ih (n / 10).toInt.toNat h_measure (n / 10) h_div_nn rfl
      refine ⟨r, h_eq, ?_, h_nn, h_le_9⟩
      rw [h_int]
      have h_n_nat_ge_10 : ¬ n.toInt.toNat < 10 := by
        have h_cast : (n.toInt.toNat : Int) = n.toInt := Int.toNat_of_nonneg hn
        intro hh
        have hh' : (n.toInt.toNat : Int) < 10 := by exact_mod_cast hh
        rw [h_cast] at hh'
        omega
      rw [← hk, first_digit_nat_large n.toInt.toNat h_n_nat_ge_10, ← h_div_nat]

/-! ## Pointwise correctness of `digit_sum_at`. -/

private theorem digit_sum_at_correct (n acc : i64)
    (hn : 0 ≤ n.toInt) (hacc : 0 ≤ acc.toInt)
    (h_bound : acc.toInt + (digit_sum_nat n.toInt.toNat 0 : Int) < 2^63) :
    ∃ r : i64,
      clever_107_count_nums.digit_sum_at n acc = RustM.ok r ∧
      r.toInt = acc.toInt + (digit_sum_nat n.toInt.toNat 0 : Int) ∧
      0 ≤ r.toInt := by
  induction hk : n.toInt.toNat using Nat.strongRecOn generalizing n acc with
  | _ k ih =>
    unfold clever_107_count_nums.digit_sum_at
    by_cases h_eq_zero : n = (0 : i64)
    · -- Base case: n = 0. Returns ok acc.
      subst h_eq_zero
      have h_beq : ((0 : i64) == (0 : i64)) = true := by decide
      simp only [show ((0 : i64) ==? (0 : i64) : RustM Bool) =
                   (pure ((0 : i64) == (0 : i64))) from rfl,
                 h_beq, pure_bind, ↓reduceIte]
      refine ⟨acc, rfl, ?_, hacc⟩
      have h_n_nat_zero : (0 : i64).toInt.toNat = 0 := by rw [i64_zero_toInt]; rfl
      rw [← hk, h_n_nat_zero, digit_sum_nat_zero]
      simp
    · -- Step case: n ≠ 0.
      have h_n_ne_zero_toInt : n.toInt ≠ 0 := by
        intro h
        apply h_eq_zero
        apply Int64.toInt_inj.mp
        rw [i64_zero_toInt]; exact h
      have h_n_pos : 0 < n.toInt := by omega
      have h_beq : (n == (0 : i64)) = false := by
        show decide (n = (0 : i64)) = false; exact decide_eq_false h_eq_zero
      simp only [show (n ==? (0 : i64) : RustM Bool) =
                   (pure (n == (0 : i64))) from rfl,
                 h_beq, pure_bind, Bool.false_eq_true, ↓reduceIte]
      -- Process binds in evaluation order: n /? 10 first, then n %? 10, then acc +? ...
      rw [i64_div_10 n, pure_bind]
      rw [i64_mod_10 n, pure_bind]
      have h_mod_nn : 0 ≤ (n % 10).toInt := i64_mod_10_nonneg n hn
      have h_mod_le_9 : (n % 10).toInt ≤ 9 := i64_mod_10_le_9 n hn
      have h_n_lt : n.toInt < 2^63 := i64_lt_max n
      have h_acc_lt : acc.toInt < 2^63 := i64_lt_max acc
      -- new_acc = acc + n%10. Need ¬ addOverflow.
      have h_acc_plus_mod_bound : acc.toInt + (n % 10).toInt < 2^63 := by
        have h_ds_pos : (0 : Int) ≤ (digit_sum_nat n.toInt.toNat 0 : Int) :=
          Int.natCast_nonneg _
        -- From h_bound: acc.toInt + digit_sum_nat ... < 2^63. Need: acc + (n%10) < 2^63.
        -- We use (n%10) ≤ 9 ≤ digit_sum_nat (for n > 0). Actually, we need a sharper bound.
        -- For n > 0, n % 10 is one of n's digits, so n % 10 ≤ digit_sum_nat n 0.
        -- This is true because digit_sum_nat unfolds to ... + n%10.
        have h_n_nat_pos : 0 < n.toInt.toNat := by
          have h_cast : (n.toInt.toNat : Int) = n.toInt := Int.toNat_of_nonneg hn
          have : 0 < (n.toInt.toNat : Int) := by rw [h_cast]; exact h_n_pos
          exact_mod_cast this
        have h_dsn_unfold : digit_sum_nat n.toInt.toNat 0 =
            digit_sum_nat (n.toInt.toNat / 10) (n.toInt.toNat % 10) := by
          rw [digit_sum_nat_succ n.toInt.toNat 0 h_n_nat_pos]
          congr 1; omega
        have h_ge_mod : (n.toInt.toNat % 10 : Nat) ≤ digit_sum_nat n.toInt.toNat 0 := by
          rw [h_dsn_unfold]
          exact digit_sum_nat_le_acc_add (n.toInt.toNat / 10) (n.toInt.toNat % 10)
        have h_mod_nat_eq : (n % 10).toInt = (n.toInt.toNat % 10 : Int) := by
          rw [i64_mod_10_toInt n hn]
          have h_cast : (n.toInt.toNat : Int) = n.toInt := Int.toNat_of_nonneg hn
          have : (n.toInt.toNat % 10 : Int) = ((n.toInt.toNat : Int) % 10) := by push_cast; rfl
          rw [this, h_cast]
        rw [h_mod_nat_eq]
        have h_cast_ge : ((n.toInt.toNat % 10 : Nat) : Int) ≤ (digit_sum_nat n.toInt.toNat 0 : Int) := by
          exact_mod_cast h_ge_mod
        omega
      have h_no_overflow : ¬ Int64.addOverflow acc (n % 10) := by
        intro hov
        rw [Int64.addOverflow_iff] at hov
        have h_acc_min : -(2^63 : Int) ≤ acc.toInt := i64_min_le acc
        have h63 : (2 : Int) ^ (64 - 1) = 2^63 := by decide
        rw [h63] at hov
        rcases hov with hov | hov
        · omega
        · omega
      rw [i64_add_pure acc (n % 10) h_no_overflow, pure_bind]
      -- Recurse with (n / 10, acc + n%10)
      have h_div_nn : 0 ≤ (n / 10).toInt := i64_div_10_nonneg n hn
      have h_div_lt : (n / 10).toInt < n.toInt := by
        rw [i64_div_10_toInt n hn]
        exact Int.ediv_lt_self_of_pos_of_ne_one h_n_pos (by decide)
      have h_div_nat : (n / 10).toInt.toNat = n.toInt.toNat / 10 := by
        rw [i64_div_10_toInt n hn]
        exact int_toNat_ediv hn (by decide)
      have h_measure : (n / 10).toInt.toNat < k := by
        rw [← hk]
        exact (Int.toNat_lt_toNat (by omega)).mpr h_div_lt
      have h_new_acc_toInt : (acc + (n % 10)).toInt = acc.toInt + (n % 10).toInt :=
        Int64.toInt_add_of_not_addOverflow h_no_overflow
      have h_new_acc_nn : 0 ≤ (acc + (n % 10)).toInt := by
        rw [h_new_acc_toInt]; omega
      -- Bridge: digit_sum_nat n 0 = (n%10) + digit_sum_nat (n/10) 0
      have h_n_nat_pos : 0 < n.toInt.toNat := by
        have h_cast : (n.toInt.toNat : Int) = n.toInt := Int.toNat_of_nonneg hn
        have : 0 < (n.toInt.toNat : Int) := by rw [h_cast]; exact h_n_pos
        exact_mod_cast this
      have h_dsn_succ_int :
          (digit_sum_nat n.toInt.toNat 0 : Int) =
            (n.toInt.toNat % 10 : Int) + (digit_sum_nat (n.toInt.toNat / 10) 0 : Int) := by
        rw [digit_sum_nat_succ n.toInt.toNat 0 h_n_nat_pos]
        rw [digit_sum_nat_acc_eq (n.toInt.toNat / 10) (0 + n.toInt.toNat % 10)]
        push_cast; omega
      have h_mod_nat : (n.toInt.toNat % 10 : Int) = (n % 10).toInt := by
        rw [i64_mod_10_toInt n hn]
        have h_cast : (n.toInt.toNat : Int) = n.toInt := Int.toNat_of_nonneg hn
        have h_cast_mod : (n.toInt.toNat % 10 : Int) = ((n.toInt.toNat : Int) % 10) := by
          push_cast; rfl
        rw [h_cast_mod, h_cast]
      have h_new_acc_bound :
          (acc + (n % 10)).toInt + (digit_sum_nat (n / 10).toInt.toNat 0 : Int) < 2^63 := by
        rw [h_new_acc_toInt, h_div_nat]
        have h0 : acc.toInt + (digit_sum_nat n.toInt.toNat 0 : Int) < 2^63 := h_bound
        rw [h_dsn_succ_int, h_mod_nat] at h0
        omega
      obtain ⟨r, h_eq, h_int, h_r_nn⟩ :=
        ih (n / 10).toInt.toNat h_measure (n / 10) (acc + (n % 10)) h_div_nn h_new_acc_nn
          h_new_acc_bound rfl
      refine ⟨r, h_eq, ?_, h_r_nn⟩
      rw [h_int, h_new_acc_toInt, ← hk, h_dsn_succ_int, ← h_mod_nat, ← h_div_nat]
      omega

/-! ## Int-level oracle for `signed_digit_sum`. -/

private def signed_digit_sum_int (n : Int) : Int :=
  if n = 0 then 0
  else if 0 < n then (digit_sum_nat n.toNat 0 : Int)
  else (digit_sum_nat (-n).toNat 0 : Int) - 2 * (first_digit_nat (-n).toNat : Int)

private theorem signed_digit_sum_int_zero : signed_digit_sum_int 0 = 0 := by
  unfold signed_digit_sum_int; rfl

private theorem signed_digit_sum_int_pos (n : Int) (h : 0 < n) :
    signed_digit_sum_int n = (digit_sum_nat n.toNat 0 : Int) := by
  unfold signed_digit_sum_int
  rw [if_neg (by omega : n ≠ 0), if_pos h]

private theorem signed_digit_sum_int_neg (n : Int) (h : n < 0) :
    signed_digit_sum_int n =
      (digit_sum_nat (-n).toNat 0 : Int) - 2 * (first_digit_nat (-n).toNat : Int) := by
  unfold signed_digit_sum_int
  rw [if_neg (by omega : n ≠ 0), if_neg (by omega : ¬ 0 < n)]

/-! ## Bound on `digit_sum_nat` of small positive values. -/

private theorem digit_sum_nat_small (n : Nat) (h : n < 10) :
    digit_sum_nat n 0 = n := by
  by_cases hn : 0 < n
  · rw [digit_sum_nat_succ n 0 hn]
    have h_div : n / 10 = 0 := Nat.div_eq_of_lt h
    have h_mod : n % 10 = n := Nat.mod_eq_of_lt h
    rw [h_div, h_mod, digit_sum_nat_zero]
    omega
  · have hz : n = 0 := by omega
    rw [hz, digit_sum_nat_zero]

private theorem first_digit_nat_small_pos (n : Nat) (h : n < 10) :
    first_digit_nat n = n := first_digit_nat_small n h

/-! ## Pointwise correctness of `signed_digit_sum`. -/

private theorem signed_digit_sum_zero :
    clever_107_count_nums.signed_digit_sum (0 : i64) = RustM.ok (0 : i64) := by
  unfold clever_107_count_nums.signed_digit_sum
  have h_beq : ((0 : i64) == (0 : i64)) = true := by decide
  simp only [show ((0 : i64) ==? (0 : i64) : RustM Bool) =
               (pure ((0 : i64) == (0 : i64))) from rfl,
             h_beq, pure_bind, ↓reduceIte]
  rfl

private theorem signed_digit_sum_correct
    (n : i64) (h_no_min : n ≠ Int64.minValue) :
    ∃ r : i64,
      clever_107_count_nums.signed_digit_sum n = RustM.ok r ∧
      r.toInt = signed_digit_sum_int n.toInt := by
  unfold clever_107_count_nums.signed_digit_sum
  by_cases h_zero : n = (0 : i64)
  · -- n = 0
    subst h_zero
    have h_beq : ((0 : i64) == (0 : i64)) = true := by decide
    simp only [show ((0 : i64) ==? (0 : i64) : RustM Bool) =
                 (pure ((0 : i64) == (0 : i64))) from rfl,
               h_beq, pure_bind, ↓reduceIte]
    refine ⟨0, ?_, ?_⟩
    · rfl
    · rw [i64_zero_toInt, signed_digit_sum_int_zero]
  · have h_n_ne_zero_toInt : n.toInt ≠ 0 := by
      intro h; apply h_zero; apply Int64.toInt_inj.mp
      rw [i64_zero_toInt]; exact h
    have h_beq : (n == (0 : i64)) = false := by
      show decide (n = (0 : i64)) = false; exact decide_eq_false h_zero
    simp only [show (n ==? (0 : i64) : RustM Bool) =
                 (pure (n == (0 : i64))) from rfl,
               h_beq, pure_bind, Bool.false_eq_true, ↓reduceIte]
    by_cases h_pos : (0 : i64) < n
    · -- n > 0 branch
      have h_n_pos_int : 0 < n.toInt := by
        have := Int64.lt_iff_toInt_lt.mp h_pos
        simpa [i64_zero_toInt] using this
      have h_n_nn : 0 ≤ n.toInt := by omega
      have h_dec_gt : decide ((0 : i64) < n) = true := decide_eq_true h_pos
      simp only [show (n >? (0 : i64) : RustM Bool) =
                   (pure (decide ((0 : i64) < n)) : RustM Bool) from rfl,
                 h_dec_gt, pure_bind, ↓reduceIte]
      -- digit_sum bound is automatically satisfied: at most 9*19 < 2^63
      have h_bound : (0 : i64).toInt + (digit_sum_nat n.toInt.toNat 0 : Int) < 2^63 := by
        have h_n_nat_lt : n.toInt.toNat < 2^63 := by
          have h_cast : (n.toInt.toNat : Int) = n.toInt := Int.toNat_of_nonneg h_n_nn
          have hL : n.toInt < 2^63 := i64_lt_max n
          have : (n.toInt.toNat : Int) < 2^63 := by rw [h_cast]; exact hL
          exact_mod_cast this
        have hd := digit_sum_nat_bound_i64 n.toInt.toNat 0 h_n_nat_lt
        have : (digit_sum_nat n.toInt.toNat 0 : Int) ≤ 9 * 19 := by exact_mod_cast hd
        rw [i64_zero_toInt]
        have h_bnd : (9 * 19 : Int) < 2^63 := by decide
        omega
      obtain ⟨r, h_eq, h_int, _⟩ :=
        digit_sum_at_correct n 0 h_n_nn (by rw [i64_zero_toInt]; exact Int.le_refl 0) h_bound
      refine ⟨r, h_eq, ?_⟩
      rw [h_int, signed_digit_sum_int_pos n.toInt h_n_pos_int, i64_zero_toInt]
      omega
    · -- n < 0 branch
      have h_n_neg_int : n.toInt < 0 := by
        have h_not_pos : ¬ (0 : i64) < n := h_pos
        have h_not_int : ¬ (0 : Int) < n.toInt := by
          intro hh; apply h_not_pos
          rw [Int64.lt_iff_toInt_lt, i64_zero_toInt]; exact hh
        omega
      have h_dec_gt : decide ((0 : i64) < n) = false := decide_eq_false h_pos
      simp only [show (n >? (0 : i64) : RustM Bool) =
                   (pure (decide ((0 : i64) < n)) : RustM Bool) from rfl,
                 h_dec_gt, pure_bind, Bool.false_eq_true, ↓reduceIte]
      -- m := -n. Need n ≠ minValue ⇒ m doesn't overflow.
      rw [i64_neg n h_no_min, pure_bind]
      have h_m_toInt : (-n).toInt = -n.toInt := Int64.toInt_neg_of_ne_intMin h_no_min
      have h_m_pos : 0 < (-n).toInt := by rw [h_m_toInt]; omega
      have h_m_nn : 0 ≤ (-n).toInt := by omega
      -- digit_sum_at (-n) 0 = ok ds
      have h_bound_ds : (0 : i64).toInt + (digit_sum_nat (-n).toInt.toNat 0 : Int) < 2^63 := by
        have h_m_nat_lt : (-n).toInt.toNat < 2^63 := by
          have h_cast : ((-n).toInt.toNat : Int) = (-n).toInt := Int.toNat_of_nonneg h_m_nn
          have hL : (-n).toInt < 2^63 := i64_lt_max (-n)
          have : ((-n).toInt.toNat : Int) < 2^63 := by rw [h_cast]; exact hL
          exact_mod_cast this
        have hd := digit_sum_nat_bound_i64 (-n).toInt.toNat 0 h_m_nat_lt
        have : (digit_sum_nat (-n).toInt.toNat 0 : Int) ≤ 9 * 19 := by exact_mod_cast hd
        rw [i64_zero_toInt]
        have h_bnd : (9 * 19 : Int) < 2^63 := by decide
        omega
      obtain ⟨ds, h_ds_eq, h_ds_int, h_ds_nn⟩ :=
        digit_sum_at_correct (-n) 0 h_m_nn (by rw [i64_zero_toInt]; exact Int.le_refl 0) h_bound_ds
      have h_ds_bound : ds.toInt ≤ 9 * 19 := by
        have h_m_nat_lt : (-n).toInt.toNat < 2^63 := by
          have h_cast : ((-n).toInt.toNat : Int) = (-n).toInt := Int.toNat_of_nonneg h_m_nn
          have hL : (-n).toInt < 2^63 := i64_lt_max (-n)
          have : ((-n).toInt.toNat : Int) < 2^63 := by rw [h_cast]; exact hL
          exact_mod_cast this
        have hd := digit_sum_nat_bound_i64 (-n).toInt.toNat 0 h_m_nat_lt
        have : (digit_sum_nat (-n).toInt.toNat 0 : Int) ≤ 9 * 19 := by exact_mod_cast hd
        rw [h_ds_int, i64_zero_toInt]; omega
      rw [h_ds_eq]
      simp only [RustM_ok_bind]
      -- first_digit_at (-n) = ok fd
      obtain ⟨fd, h_fd_eq, h_fd_int, h_fd_nn, h_fd_le_9⟩ :=
        first_digit_at_correct (-n) h_m_nn
      rw [h_fd_eq]
      simp only [RustM_ok_bind]
      -- 2 *? fd = ok (2 * fd) — fd ≤ 9, so 2*fd ≤ 18, no overflow
      have h_no_mul_ov : ¬ Int64.mulOverflow (2 : i64) fd := by
        intro hov
        rw [Int64.mulOverflow_iff] at hov
        rw [i64_two_toInt] at hov
        have h63 : (2 : Int) ^ (64 - 1) = 2^63 := by decide
        rw [h63] at hov
        rcases hov with hov | hov
        · omega
        · omega
      rw [i64_mul_pure (2 : i64) fd h_no_mul_ov, pure_bind]
      have h_2fd_toInt : ((2 : i64) * fd).toInt = 2 * fd.toInt := by
        have h := Int64.toInt_mul_of_not_mulOverflow h_no_mul_ov
        rw [h, i64_two_toInt]
      -- ds -? (2 * fd) — both bounded, result is digit_sum - 2*first_digit which is bounded
      have h_no_sub_ov : ¬ Int64.subOverflow ds ((2 : i64) * fd) := by
        intro hov
        rw [Int64.subOverflow_iff] at hov
        rw [h_2fd_toInt] at hov
        have h63 : (2 : Int) ^ (64 - 1) = 2^63 := by decide
        rw [h63] at hov
        -- ds ∈ [0, 9*19=171], 2*fd ∈ [0, 18], so ds - 2*fd ∈ [-18, 171]
        rcases hov with hov | hov
        · omega
        · omega
      rw [i64_sub_pure ds ((2 : i64) * fd) h_no_sub_ov]
      refine ⟨ds - (2 : i64) * fd, rfl, ?_⟩
      rw [Int64.toInt_sub_of_not_subOverflow h_no_sub_ov, h_2fd_toInt]
      rw [signed_digit_sum_int_neg n.toInt h_n_neg_int]
      rw [h_ds_int, h_fd_int]
      rw [i64_zero_toInt, h_m_toInt]; omega

/-! ## Specialised: signed_digit_sum n = 0 ⇔ ... (boundary helpers) -/

/-- `signed_digit_sum n > 0` whenever `n > 0`. -/
private theorem signed_digit_sum_pos_pos (n : i64) (h_pos : 0 < n.toInt) :
    ∃ r : i64,
      clever_107_count_nums.signed_digit_sum n = RustM.ok r ∧ 0 < r.toInt := by
  have h_no_min : n ≠ Int64.minValue := by
    intro h; rw [h, int64_min_toInt] at h_pos
    have h63 : (0 : Int) < 2^63 := by decide
    omega
  obtain ⟨r, h_eq, h_int⟩ := signed_digit_sum_correct n h_no_min
  refine ⟨r, h_eq, ?_⟩
  rw [h_int, signed_digit_sum_int_pos n.toInt h_pos]
  -- digit_sum_nat n.toNat 0 > 0 because n > 0 implies at least one nonzero digit
  have h_n_nat_pos : 0 < n.toInt.toNat := by
    have h_cast : (n.toInt.toNat : Int) = n.toInt := Int.toNat_of_nonneg (by omega)
    have : 0 < (n.toInt.toNat : Int) := by rw [h_cast]; exact h_pos
    exact_mod_cast this
  -- Use first_digit_nat ≤ digit_sum_nat and first_digit_nat > 0 for n > 0.
  have h_fd_pos : 0 < first_digit_nat n.toInt.toNat := first_digit_nat_pos n.toInt.toNat h_n_nat_pos
  -- Bound: first_digit_nat n ≤ digit_sum_nat n 0
  -- Proof sketch: induct on n. When n < 10, first_digit n = n, digit_sum n 0 = n, ≤.
  -- When n ≥ 10, first_digit n = first_digit (n/10), digit_sum n 0 = (n%10) + digit_sum (n/10) 0
  --   By IH, first_digit (n/10) ≤ digit_sum (n/10) 0 ≤ digit_sum n 0.
  have h_fd_le_dsn : first_digit_nat n.toInt.toNat ≤ digit_sum_nat n.toInt.toNat 0 := by
    have h_aux : ∀ m, first_digit_nat m ≤ digit_sum_nat m 0 := by
      intro m
      induction m using Nat.strongRecOn with
      | _ m ih =>
        by_cases hm : m < 10
        · rw [first_digit_nat_small m hm, digit_sum_nat_small m hm]; exact Nat.le_refl m
        · have hm_pos : 0 < m := by omega
          rw [first_digit_nat_large m hm]
          rw [digit_sum_nat_succ m 0 hm_pos]
          rw [digit_sum_nat_acc_eq (m / 10) (0 + m % 10)]
          have ih' : first_digit_nat (m / 10) ≤ digit_sum_nat (m / 10) 0 :=
            ih (m / 10) (Nat.div_lt_self hm_pos (by decide))
          omega
    exact h_aux n.toInt.toNat
  have h_cast : (1 : Int) ≤ (digit_sum_nat n.toInt.toNat 0 : Int) := by
    have h_one_le : 1 ≤ digit_sum_nat n.toInt.toNat 0 := by omega
    exact_mod_cast h_one_le
  omega

/-- For `n ∈ [-9, -1]`, `signed_digit_sum n = n`. -/
private theorem signed_digit_sum_small_neg (n : i64)
    (h_lb : (-9 : Int) ≤ n.toInt) (h_ub : n.toInt ≤ -1) :
    clever_107_count_nums.signed_digit_sum n = RustM.ok n := by
  have h_no_min : n ≠ Int64.minValue := by
    intro h
    rw [h, int64_min_toInt] at h_lb
    have : (2 : Int)^63 = 9223372036854775808 := by decide
    omega
  obtain ⟨r, h_eq, h_int⟩ := signed_digit_sum_correct n h_no_min
  have h_n_neg : n.toInt < 0 := by omega
  have h_m_pos : (0 : Int) < -n.toInt := by omega
  have h_m_le_9 : -n.toInt ≤ 9 := by omega
  have h_m_nat_lt_10 : (-n.toInt).toNat < 10 := by
    have h_cast : ((-n.toInt).toNat : Int) = -n.toInt := Int.toNat_of_nonneg (by omega)
    have : ((-n.toInt).toNat : Int) < 10 := by rw [h_cast]; omega
    exact_mod_cast this
  have h_m_nat_pos : 0 < (-n.toInt).toNat := by
    have h_cast : ((-n.toInt).toNat : Int) = -n.toInt := Int.toNat_of_nonneg (by omega)
    have : 0 < ((-n.toInt).toNat : Int) := by rw [h_cast]; omega
    exact_mod_cast this
  have h_dsn : digit_sum_nat (-n.toInt).toNat 0 = (-n.toInt).toNat :=
    digit_sum_nat_small (-n.toInt).toNat h_m_nat_lt_10
  have h_fd : first_digit_nat (-n.toInt).toNat = (-n.toInt).toNat :=
    first_digit_nat_small (-n.toInt).toNat h_m_nat_lt_10
  -- signed_digit_sum_int n = digit_sum (-n) - 2 * first_digit (-n) = (-n) - 2*(-n) = n
  have h_sgs : signed_digit_sum_int n.toInt = n.toInt := by
    rw [signed_digit_sum_int_neg n.toInt h_n_neg]
    rw [h_dsn, h_fd]
    have h_cast : ((-n.toInt).toNat : Int) = -n.toInt := Int.toNat_of_nonneg (by omega)
    rw [h_cast]; omega
  have h_r_eq_n : r.toInt = n.toInt := by rw [h_int, h_sgs]
  have h_r_eq : r = n := Int64.toInt_inj.mp h_r_eq_n
  rw [h_r_eq] at h_eq
  exact h_eq

/-! ## Nat-level prefix count oracle. -/

private def pos_count_pref (arr : Array i64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      pos_count_pref arr k +
        (if h : k < arr.size then
           (if 0 < signed_digit_sum_int (arr[k]'h).toInt then 1 else 0)
         else 0)

private theorem pos_count_pref_succ_in (arr : Array i64) (k : Nat) (h : k < arr.size) :
    pos_count_pref arr (k + 1) =
      pos_count_pref arr k +
        (if 0 < signed_digit_sum_int (arr[k]'h).toInt then 1 else 0) := by
  show pos_count_pref arr k +
      (if h : k < arr.size then
         (if 0 < signed_digit_sum_int (arr[k]'h).toInt then 1 else 0)
       else 0)
    = pos_count_pref arr k +
      (if 0 < signed_digit_sum_int (arr[k]'h).toInt then 1 else 0)
  rw [dif_pos h]

private theorem pos_count_pref_le (arr : Array i64) :
    ∀ k, pos_count_pref arr k ≤ k := by
  intro k
  induction k with
  | zero => simp [pos_count_pref]
  | succ k ih =>
    show pos_count_pref arr k +
        (if h : k < arr.size then
           (if 0 < signed_digit_sum_int (arr[k]'h).toInt then 1 else 0)
         else 0) ≤ k + 1
    by_cases hk : k < arr.size
    · rw [dif_pos hk]
      by_cases hpos : 0 < signed_digit_sum_int (arr[k]'hk).toInt
      · rw [if_pos hpos]; omega
      · rw [if_neg hpos]; omega
    · rw [dif_neg hk]; omega

/-! ## Helper lemmas for `Array.append` indexing. -/

private theorem aux_concat_left_eq {α : Type} {c a b : Array α}
    (h_concat : c = a ++ b) {j : Nat} (h_left : j < a.size)
    (h_c : j < c.size) :
    c[j]'h_c = a[j]'h_left := by
  subst h_concat
  exact Array.getElem_append_left h_left

private theorem aux_concat_right_eq {α : Type} {c a b : Array α}
    (h_concat : c = a ++ b) {j : Nat} (h_c : j < c.size)
    (h_not_left : ¬ j < a.size) (h_right : j - a.size < b.size) :
    c[j]'h_c = b[j - a.size]'h_right := by
  subst h_concat
  exact Array.getElem_append_right (Nat.le_of_not_lt h_not_left)

private theorem aux_concat_size {α : Type} {c a b : Array α}
    (h_concat : c = a ++ b) : c.size = a.size + b.size := by
  subst h_concat
  exact Array.size_append

/-! ## Step lemma: count_at when i ≥ arr.size returns acc. -/

private theorem count_at_oob (arr : RustSlice i64) (i : usize) (acc : i64)
    (hi : arr.val.size ≤ i.toNat) :
    clever_107_count_nums.count_at arr i acc = RustM.ok acc := by
  conv => lhs; unfold clever_107_count_nums.count_at
  have h_ofNat : (USize64.ofNat arr.val.size).toNat = arr.val.size :=
    USize64.toNat_ofNat_of_lt' arr.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat arr.val.size ≤ i) = true := by
    rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, h_cond, ↓reduceIte]
  rfl

/-! ## Strong-induction correctness of `count_at`. -/

private theorem count_at_correct
    (arr : RustSlice i64)
    (h_size : (arr.val.size : Int) < 2^63)
    (h_no_min : ∀ (j : Nat) (h : j < arr.val.size),
                  arr.val[j]'h ≠ Int64.minValue) :
    ∀ (m : Nat) (i : usize) (acc : i64),
      arr.val.size - i.toNat ≤ m →
      i.toNat ≤ arr.val.size →
      0 ≤ acc.toInt →
      acc.toInt + ((arr.val.size : Int) - (i.toNat : Int)) < 2^63 →
      ∃ r : i64,
        clever_107_count_nums.count_at arr i acc = RustM.ok r ∧
        r.toInt = acc.toInt
          + ((pos_count_pref arr.val arr.val.size : Int)
              - (pos_count_pref arr.val i.toNat : Int)) := by
  intro m
  induction m with
  | zero =>
    intro i acc h_meas h_i_le h_acc_nn h_bound
    have h_i_ge : arr.val.size ≤ i.toNat := by omega
    have h_i_eq : i.toNat = arr.val.size := by omega
    refine ⟨acc, count_at_oob arr i acc h_i_ge, ?_⟩
    rw [h_i_eq]; omega
  | succ m ih =>
    intro i acc h_meas h_i_le h_acc_nn h_bound
    by_cases h_i_ge : arr.val.size ≤ i.toNat
    · -- OOB: returns ok acc
      have h_i_eq : i.toNat = arr.val.size := by omega
      refine ⟨acc, count_at_oob arr i acc h_i_ge, ?_⟩
      rw [h_i_eq]; omega
    · -- Step case
      have h_i_lt : i.toNat < arr.val.size := by omega
      have h_size_lt : arr.val.size < 2^64 := arr.size_lt_usizeSize
      have h_ofNat : (USize64.ofNat arr.val.size).toNat = arr.val.size :=
        USize64.toNat_ofNat_of_lt' h_size_lt
      -- Element under inspection
      let a : i64 := arr.val[i.toNat]'h_i_lt
      have h_a_def : a = arr.val[i.toNat]'h_i_lt := rfl
      have ha_no_min : a ≠ Int64.minValue := h_no_min i.toNat h_i_lt
      -- Unfold count_at and reduce OOB check
      unfold clever_107_count_nums.count_at
      have h_cond : decide (USize64.ofNat arr.val.size ≤ i) = false := by
        rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]
        omega
      simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
                 rust_primitives.cmp.ge, pure_bind, h_cond, Bool.false_eq_true,
                 ↓reduceIte]
      -- Reduce arr[i]_? = ok a
      have h_idx : (arr[i]_? : RustM i64) = RustM.ok a := by
        show (if h : i.toNat < arr.val.size then pure (arr.val[i])
              else .fail .arrayOutOfBounds)
            = RustM.ok a
        rw [dif_pos h_i_lt]; rfl
      rw [h_idx]
      simp only [RustM_ok_bind]
      -- Apply signed_digit_sum_correct
      obtain ⟨s, h_s_eq, h_s_int⟩ := signed_digit_sum_correct a ha_no_min
      rw [h_s_eq]
      simp only [RustM_ok_bind]
      -- Reduce s >? 0
      have h_cmp_pos : (s >? (0 : i64) : RustM Bool) = pure (decide ((0 : i64) < s)) := rfl
      rw [h_cmp_pos]
      simp only [pure_bind]
      -- Reduce i +? 1 — always succeeds since i.toNat < size < 2^64
      have h_no_i_ov : i.toNat + 1 < 2^64 := by omega
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
      have h_i1_pure : (i +? (1 : usize) : RustM usize) = pure (i + 1) := by
        show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = pure (i + 1)
        show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec then
                (.fail .integerOverflow : RustM usize)
              else pure (i + 1)) = _
        rw [h_no_bv_i]; rfl
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 :=
        usize_add_one_toNat i h_no_i_ov
      have h_i1_le_size : (i + 1).toNat ≤ arr.val.size := by
        rw [h_i1_toNat]; omega
      have h_meas_step : arr.val.size - (i + 1).toNat ≤ m := by
        rw [h_i1_toNat]; omega
      -- The Int-level predicate value: signed_digit_sum_int a.toInt
      have h_sdsi_val : signed_digit_sum_int a.toInt = s.toInt := h_s_int.symm
      -- Bridge the count_pref step
      have h_pos_count_step :
          (pos_count_pref arr.val (i.toNat + 1) : Int) =
            (pos_count_pref arr.val i.toNat : Int) +
              (if 0 < signed_digit_sum_int a.toInt then 1 else 0) := by
        rw [pos_count_pref_succ_in arr.val i.toNat h_i_lt, h_a_def]
        push_cast
        split <;> simp
      by_cases h_s_pos : (0 : i64) < s
      · -- Predicate fires: recurse with (i+1, acc+1)
        have h_s_pos_int : 0 < s.toInt := by
          have := Int64.lt_iff_toInt_lt.mp h_s_pos
          simpa [i64_zero_toInt] using this
        have h_dec_pos : decide ((0 : i64) < s) = true := decide_eq_true h_s_pos
        rw [h_dec_pos]
        simp only [↓reduceIte]
        rw [h_i1_pure]
        simp only [pure_bind]
        -- acc +? 1 doesn't overflow since acc + (size - i) < 2^63
        have h_acc1_bound : acc.toInt + 1 < 2^63 := by
          have h_si_int_pos : (0 : Int) < signed_digit_sum_int a.toInt := by
            rw [h_sdsi_val]; exact h_s_pos_int
          omega
        have h_no_acc_ov : ¬ Int64.addOverflow acc (1 : i64) := by
          intro hov
          rw [Int64.addOverflow_iff] at hov
          rw [i64_one_toInt] at hov
          have h63 : (2 : Int) ^ (64 - 1) = 2^63 := by decide
          rw [h63] at hov
          have h_acc_min : -(2^63 : Int) ≤ acc.toInt := i64_min_le acc
          rcases hov with hov | hov
          · omega
          · omega
        rw [i64_add_pure acc (1 : i64) h_no_acc_ov]
        simp only [pure_bind]
        have h_acc1_toInt : (acc + (1 : i64)).toInt = acc.toInt + 1 := by
          rw [Int64.toInt_add_of_not_addOverflow h_no_acc_ov, i64_one_toInt]
        have h_acc1_nn : 0 ≤ (acc + (1 : i64)).toInt := by rw [h_acc1_toInt]; omega
        have h_acc1_bound_step :
            (acc + (1 : i64)).toInt + ((arr.val.size : Int) - ((i + 1).toNat : Int)) < 2^63 := by
          rw [h_acc1_toInt, h_i1_toNat]; push_cast; omega
        obtain ⟨r, h_r_eq, h_r_int⟩ :=
          ih (i + 1) (acc + (1 : i64)) h_meas_step h_i1_le_size h_acc1_nn h_acc1_bound_step
        refine ⟨r, h_r_eq, ?_⟩
        rw [h_r_int, h_acc1_toInt, h_i1_toNat]
        have h_pc_step :
            (pos_count_pref arr.val (i.toNat + 1) : Int) =
              (pos_count_pref arr.val i.toNat : Int) + 1 := by
          rw [h_pos_count_step]
          have h_si_int_pos : (0 : Int) < signed_digit_sum_int a.toInt := by
            rw [h_sdsi_val]; exact h_s_pos_int
          rw [if_pos h_si_int_pos]
        rw [h_pc_step]; omega
      · -- Predicate doesn't fire: recurse with (i+1, acc)
        have h_s_nn : ¬ (0 : Int) < s.toInt := by
          intro hh; apply h_s_pos
          rw [Int64.lt_iff_toInt_lt, i64_zero_toInt]; exact hh
        have h_dec_pos : decide ((0 : i64) < s) = false := decide_eq_false h_s_pos
        rw [h_dec_pos]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [h_i1_pure]
        simp only [pure_bind]
        have h_acc_bound_step :
            acc.toInt + ((arr.val.size : Int) - ((i + 1).toNat : Int)) < 2^63 := by
          rw [h_i1_toNat]; push_cast; omega
        obtain ⟨r, h_r_eq, h_r_int⟩ :=
          ih (i + 1) acc h_meas_step h_i1_le_size h_acc_nn h_acc_bound_step
        refine ⟨r, h_r_eq, ?_⟩
        rw [h_r_int, h_i1_toNat]
        have h_pc_step :
            (pos_count_pref arr.val (i.toNat + 1) : Int) =
              (pos_count_pref arr.val i.toNat : Int) := by
          rw [h_pos_count_step]
          have h_si_int_nneg : ¬ (0 : Int) < signed_digit_sum_int a.toInt := by
            rw [h_sdsi_val]; exact h_s_nn
          rw [if_neg h_si_int_nneg]; omega
        rw [h_pc_step]

/-! ## Obligation theorems. -/

/-- Empty-slice boundary: `count_nums []` returns 0. -/
theorem count_nums_empty
    (arr : RustSlice i64) (h_empty : arr.val.size = 0) :
    clever_107_count_nums.count_nums arr = RustM.ok (0 : i64) := by
  unfold clever_107_count_nums.count_nums
  have hi_ge : arr.val.size ≤ (0 : usize).toNat := by
    rw [usize_zero_toNat, h_empty]; exact Nat.le_refl 0
  exact count_at_oob arr (0 : usize) (0 : i64) hi_ge

/-- All-zero boundary: if every element is `0` then result is `0`. -/
theorem count_nums_all_zero
    (arr : RustSlice i64)
    (h_all_zero : ∀ (i : Nat) (h : i < arr.val.size), arr.val[i]'h = (0 : i64)) :
    clever_107_count_nums.count_nums arr = RustM.ok (0 : i64) := by
  -- Use count_at_correct with the observation that pos_count_pref = 0 everywhere.
  have h_no_min : ∀ (j : Nat) (h : j < arr.val.size),
      arr.val[j]'h ≠ Int64.minValue := by
    intro j h_lt; rw [h_all_zero j h_lt]; decide
  have h_size_lt : arr.val.size < 2^64 := arr.size_lt_usizeSize
  -- Slice size < 2^63 from concrete check: arr.val.size could be up to 2^64-1 in general,
  -- but for the all-zero result we don't need bounds — pos_count is identically 0,
  -- so the counter never increments.
  -- We need h_size : (arr.val.size : Int) < 2^63 to invoke count_at_correct.
  -- Strategy: prove a direct version that doesn't require this hypothesis.
  -- Actually, since the predicate never fires for zero, count_at always returns the accumulator.
  -- Let's prove this directly by strong induction without count_at_correct.
  have h_aux : ∀ (m : Nat) (i : usize) (acc : i64),
      arr.val.size - i.toNat ≤ m →
      i.toNat ≤ arr.val.size →
      clever_107_count_nums.count_at arr i acc = RustM.ok acc := by
    intro m
    induction m with
    | zero =>
      intro i acc h_meas h_i_le
      have hi_ge : arr.val.size ≤ i.toNat := by omega
      exact count_at_oob arr i acc hi_ge
    | succ m ih =>
      intro i acc h_meas h_i_le
      by_cases h_i_ge : arr.val.size ≤ i.toNat
      · exact count_at_oob arr i acc h_i_ge
      · have h_i_lt : i.toNat < arr.val.size := by omega
        let a : i64 := arr.val[i.toNat]'h_i_lt
        have ha_eq : a = 0 := h_all_zero i.toNat h_i_lt
        have h_ofNat : (USize64.ofNat arr.val.size).toNat = arr.val.size :=
          USize64.toNat_ofNat_of_lt' h_size_lt
        conv => lhs; unfold clever_107_count_nums.count_at
        have h_cond : decide (USize64.ofNat arr.val.size ≤ i) = false := by
          rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]; omega
        simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
                   rust_primitives.cmp.ge, pure_bind, h_cond, Bool.false_eq_true,
                   ↓reduceIte]
        have h_idx : (arr[i]_? : RustM i64) = RustM.ok a := by
          show (if h : i.toNat < arr.val.size then pure (arr.val[i])
                else .fail .arrayOutOfBounds) = RustM.ok a
          rw [dif_pos h_i_lt]; rfl
        rw [h_idx]
        simp only [RustM_ok_bind]
        -- a = 0, so signed_digit_sum returns 0
        rw [ha_eq, signed_digit_sum_zero]
        simp only [RustM_ok_bind]
        -- 0 >? 0 = false
        have h_cmp : ((0 : i64) >? (0 : i64) : RustM Bool) = pure false := by
          show (pure (decide ((0 : i64) < (0 : i64))) : RustM Bool) = pure false
          rfl
        rw [h_cmp]
        simp only [pure_bind, Bool.false_eq_true, ↓reduceIte]
        -- recurse with (i+1, acc)
        have h_no_i_ov : i.toNat + 1 < 2^64 := by omega
        have h_no_bv_i :
            BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
          generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
          cases bo with
          | false => rfl
          | true =>
            exfalso
            have hii := (USize64.uaddOverflow_iff i 1).mp hbo
            rw [usize_one_toNat] at hii; omega
        have h_i1_pure : (i +? (1 : usize) : RustM usize) = pure (i + 1) := by
          show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = pure (i + 1)
          show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec then
                  (.fail .integerOverflow : RustM usize)
                else pure (i + 1)) = _
          rw [h_no_bv_i]; rfl
        have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_i_ov
        rw [h_i1_pure]
        simp only [pure_bind]
        have h_meas_step : arr.val.size - (i + 1).toNat ≤ m := by rw [h_i1_toNat]; omega
        have h_i1_le : (i + 1).toNat ≤ arr.val.size := by rw [h_i1_toNat]; omega
        exact ih (i + 1) acc h_meas_step h_i1_le
  unfold clever_107_count_nums.count_nums
  exact h_aux arr.val.size (0 : usize) (0 : i64) (by rw [usize_zero_toNat]; omega)
    (by rw [usize_zero_toNat]; omega)

/-- Small-negatives boundary: for every element in `[-9, -1]`, result is `0`. -/
theorem count_nums_small_negatives
    (arr : RustSlice i64)
    (h_small_neg : ∀ (i : Nat) (h : i < arr.val.size),
                     (-9 : Int) ≤ (arr.val[i]'h).toInt
                     ∧ (arr.val[i]'h).toInt ≤ -1) :
    clever_107_count_nums.count_nums arr = RustM.ok (0 : i64) := by
  have h_size_lt : arr.val.size < 2^64 := arr.size_lt_usizeSize
  -- Strong induction: counter stays at acc because predicate never fires for small_neg
  have h_aux : ∀ (m : Nat) (i : usize) (acc : i64),
      arr.val.size - i.toNat ≤ m →
      i.toNat ≤ arr.val.size →
      clever_107_count_nums.count_at arr i acc = RustM.ok acc := by
    intro m
    induction m with
    | zero =>
      intro i acc h_meas h_i_le
      have hi_ge : arr.val.size ≤ i.toNat := by omega
      exact count_at_oob arr i acc hi_ge
    | succ m ih =>
      intro i acc h_meas h_i_le
      by_cases h_i_ge : arr.val.size ≤ i.toNat
      · exact count_at_oob arr i acc h_i_ge
      · have h_i_lt : i.toNat < arr.val.size := by omega
        let a : i64 := arr.val[i.toNat]'h_i_lt
        have h_a_bnd := h_small_neg i.toNat h_i_lt
        have h_a_lb : (-9 : Int) ≤ a.toInt := h_a_bnd.1
        have h_a_ub : a.toInt ≤ -1 := h_a_bnd.2
        -- signed_digit_sum a = ok a (signed_digit_sum_small_neg)
        have h_sds : clever_107_count_nums.signed_digit_sum a = RustM.ok a :=
          signed_digit_sum_small_neg a h_a_lb h_a_ub
        have h_ofNat : (USize64.ofNat arr.val.size).toNat = arr.val.size :=
          USize64.toNat_ofNat_of_lt' h_size_lt
        conv => lhs; unfold clever_107_count_nums.count_at
        have h_cond : decide (USize64.ofNat arr.val.size ≤ i) = false := by
          rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]; omega
        simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
                   rust_primitives.cmp.ge, pure_bind, h_cond, Bool.false_eq_true,
                   ↓reduceIte]
        have h_idx : (arr[i]_? : RustM i64) = RustM.ok a := by
          show (if h : i.toNat < arr.val.size then pure (arr.val[i])
                else .fail .arrayOutOfBounds) = RustM.ok a
          rw [dif_pos h_i_lt]; rfl
        rw [h_idx]
        simp only [RustM_ok_bind]
        rw [h_sds]
        simp only [RustM_ok_bind]
        -- a >? 0 = false since a ≤ -1 < 0
        have h_a_not_pos : ¬ (0 : i64) < a := by
          intro hh
          have : 0 < a.toInt := by
            have := Int64.lt_iff_toInt_lt.mp hh
            simpa [i64_zero_toInt] using this
          omega
        have h_cmp_false : decide ((0 : i64) < a) = false := decide_eq_false h_a_not_pos
        rw [show ((a >? (0 : i64)) : RustM Bool) = pure (decide ((0 : i64) < a)) from rfl,
            h_cmp_false, pure_bind]
        simp only [Bool.false_eq_true, ↓reduceIte]
        have h_no_i_ov : i.toNat + 1 < 2^64 := by omega
        have h_no_bv_i :
            BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
          generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
          cases bo with
          | false => rfl
          | true =>
            exfalso
            have hii := (USize64.uaddOverflow_iff i 1).mp hbo
            rw [usize_one_toNat] at hii; omega
        have h_i1_pure : (i +? (1 : usize) : RustM usize) = pure (i + 1) := by
          show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = pure (i + 1)
          show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec then
                  (.fail .integerOverflow : RustM usize)
                else pure (i + 1)) = _
          rw [h_no_bv_i]; rfl
        have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_i_ov
        rw [h_i1_pure]
        simp only [pure_bind]
        have h_meas_step : arr.val.size - (i + 1).toNat ≤ m := by rw [h_i1_toNat]; omega
        have h_i1_le : (i + 1).toNat ≤ arr.val.size := by rw [h_i1_toNat]; omega
        exact ih (i + 1) acc h_meas_step h_i1_le
  unfold clever_107_count_nums.count_nums
  exact h_aux arr.val.size (0 : usize) (0 : i64) (by rw [usize_zero_toNat]; omega)
    (by rw [usize_zero_toNat]; omega)

/-- Lower bound: `count_nums arr ≥ 0`. -/
theorem count_nums_nonneg
    (arr : RustSlice i64)
    (h_size : (arr.val.size : Int) < 2^63)
    (h_no_min : ∀ (i : Nat) (h : i < arr.val.size),
                  arr.val[i]'h ≠ Int64.minValue) :
    ∃ r : i64,
      clever_107_count_nums.count_nums arr = RustM.ok r
      ∧ 0 ≤ r.toInt := by
  unfold clever_107_count_nums.count_nums
  have h_init_bound : (0 : i64).toInt + ((arr.val.size : Int) - ((0 : usize).toNat : Int)) < 2^63 := by
    rw [i64_zero_toInt, usize_zero_toNat]; push_cast; omega
  obtain ⟨r, h_eq, h_int⟩ :=
    count_at_correct arr h_size h_no_min arr.val.size (0 : usize) (0 : i64)
      (by rw [usize_zero_toNat]; omega)
      (by rw [usize_zero_toNat]; omega)
      (by rw [i64_zero_toInt]; exact Int.le_refl 0)
      h_init_bound
  refine ⟨r, h_eq, ?_⟩
  rw [h_int, i64_zero_toInt, usize_zero_toNat]
  -- r.toInt = 0 + (pos_count_pref arr arr.size - pos_count_pref arr 0)
  -- = pos_count_pref arr arr.size (since pos_count_pref arr 0 = 0)
  have h_pc_zero : pos_count_pref arr.val 0 = 0 := by simp [pos_count_pref]
  rw [h_pc_zero]
  have h_pc_nn : (0 : Int) ≤ (pos_count_pref arr.val arr.val.size : Int) := Int.natCast_nonneg _
  omega

/-- Upper bound: `count_nums arr ≤ arr.val.size`. -/
theorem count_nums_le_size
    (arr : RustSlice i64)
    (h_size : (arr.val.size : Int) < 2^63)
    (h_no_min : ∀ (i : Nat) (h : i < arr.val.size),
                  arr.val[i]'h ≠ Int64.minValue) :
    ∃ r : i64,
      clever_107_count_nums.count_nums arr = RustM.ok r
      ∧ r.toInt ≤ (arr.val.size : Int) := by
  unfold clever_107_count_nums.count_nums
  have h_init_bound : (0 : i64).toInt + ((arr.val.size : Int) - ((0 : usize).toNat : Int)) < 2^63 := by
    rw [i64_zero_toInt, usize_zero_toNat]; push_cast; omega
  obtain ⟨r, h_eq, h_int⟩ :=
    count_at_correct arr h_size h_no_min arr.val.size (0 : usize) (0 : i64)
      (by rw [usize_zero_toNat]; omega)
      (by rw [usize_zero_toNat]; omega)
      (by rw [i64_zero_toInt]; exact Int.le_refl 0)
      h_init_bound
  refine ⟨r, h_eq, ?_⟩
  rw [h_int, i64_zero_toInt, usize_zero_toNat]
  have h_pc_zero : pos_count_pref arr.val 0 = 0 := by simp [pos_count_pref]
  rw [h_pc_zero]
  have h_pc_le : (pos_count_pref arr.val arr.val.size : Int) ≤ (arr.val.size : Int) := by
    have : pos_count_pref arr.val arr.val.size ≤ arr.val.size := pos_count_pref_le arr.val arr.val.size
    exact_mod_cast this
  omega

/-- All-positives postcondition. -/
theorem count_nums_all_positives
    (arr : RustSlice i64)
    (h_size : (arr.val.size : Int) < 2^63)
    (h_all_pos : ∀ (i : Nat) (h : i < arr.val.size),
                   0 < (arr.val[i]'h).toInt) :
    ∃ r : i64,
      clever_107_count_nums.count_nums arr = RustM.ok r
      ∧ r.toInt = (arr.val.size : Int) := by
  have h_no_min : ∀ (i : Nat) (h : i < arr.val.size),
      arr.val[i]'h ≠ Int64.minValue := by
    intro j h_lt
    intro h_eq
    have h_t : (arr.val[j]'h_lt).toInt = Int64.minValue.toInt := by rw [h_eq]
    rw [int64_min_toInt] at h_t
    have := h_all_pos j h_lt
    have h63 : (0 : Int) < 2^63 := by decide
    omega
  unfold clever_107_count_nums.count_nums
  have h_init_bound : (0 : i64).toInt + ((arr.val.size : Int) - ((0 : usize).toNat : Int)) < 2^63 := by
    rw [i64_zero_toInt, usize_zero_toNat]; push_cast; omega
  obtain ⟨r, h_eq, h_int⟩ :=
    count_at_correct arr h_size h_no_min arr.val.size (0 : usize) (0 : i64)
      (by rw [usize_zero_toNat]; omega)
      (by rw [usize_zero_toNat]; omega)
      (by rw [i64_zero_toInt]; exact Int.le_refl 0)
      h_init_bound
  refine ⟨r, h_eq, ?_⟩
  rw [h_int, i64_zero_toInt, usize_zero_toNat]
  -- All elements positive ⇒ pos_count_pref arr arr.size = arr.size
  have h_pc_all : pos_count_pref arr.val arr.val.size = arr.val.size := by
    have h_aux : ∀ k, k ≤ arr.val.size → pos_count_pref arr.val k = k := by
      intro k h_le
      induction k with
      | zero => simp [pos_count_pref]
      | succ k ih =>
        have h_k_lt : k < arr.val.size := by omega
        rw [pos_count_pref_succ_in arr.val k h_k_lt]
        have ih_k : pos_count_pref arr.val k = k := ih (by omega)
        rw [ih_k]
        -- Need: signed_digit_sum_int (arr.val[k]).toInt > 0
        have h_pos := h_all_pos k h_k_lt
        rw [signed_digit_sum_int_pos (arr.val[k]'h_k_lt).toInt h_pos]
        -- digit_sum_nat n.toNat 0 > 0 when n > 0
        have h_n_nat_pos : 0 < (arr.val[k]'h_k_lt).toInt.toNat := by
          have h_cast : ((arr.val[k]'h_k_lt).toInt.toNat : Int) = (arr.val[k]'h_k_lt).toInt :=
            Int.toNat_of_nonneg (by omega)
          have : 0 < ((arr.val[k]'h_k_lt).toInt.toNat : Int) := by rw [h_cast]; exact h_pos
          exact_mod_cast this
        have h_fd_pos : 0 < first_digit_nat (arr.val[k]'h_k_lt).toInt.toNat :=
          first_digit_nat_pos _ h_n_nat_pos
        have h_fd_le_ds : first_digit_nat (arr.val[k]'h_k_lt).toInt.toNat
            ≤ digit_sum_nat (arr.val[k]'h_k_lt).toInt.toNat 0 := by
          have h_aux2 : ∀ m, first_digit_nat m ≤ digit_sum_nat m 0 := by
            intro m
            induction m using Nat.strongRecOn with
            | _ m ih =>
              by_cases hm : m < 10
              · rw [first_digit_nat_small m hm, digit_sum_nat_small m hm]
                exact Nat.le_refl m
              · have hm_pos : 0 < m := by omega
                rw [first_digit_nat_large m hm]
                rw [digit_sum_nat_succ m 0 hm_pos]
                rw [digit_sum_nat_acc_eq (m / 10) (0 + m % 10)]
                have ih' : first_digit_nat (m / 10) ≤ digit_sum_nat (m / 10) 0 :=
                  ih (m / 10) (Nat.div_lt_self hm_pos (by decide))
                omega
          exact h_aux2 _
        have h_ds_pos : 0 < digit_sum_nat (arr.val[k]'h_k_lt).toInt.toNat 0 := by omega
        have h_ds_pos_int : (0 : Int) < (digit_sum_nat (arr.val[k]'h_k_lt).toInt.toNat 0 : Int) := by
          exact_mod_cast h_ds_pos
        rw [if_pos h_ds_pos_int]
    exact h_aux arr.val.size (Nat.le_refl _)
  have h_pc_zero : pos_count_pref arr.val 0 = 0 := by simp [pos_count_pref]
  rw [h_pc_all, h_pc_zero]; push_cast; omega

/-- Additivity: `count_nums (a ++ b) = count_nums a + count_nums b`. -/
theorem count_nums_additive
    (a b c : RustSlice i64)
    (h_concat : c.val = a.val ++ b.val)
    (h_c_size : (c.val.size : Int) < 2^63)
    (h_no_min_a : ∀ (i : Nat) (h : i < a.val.size),
                    a.val[i]'h ≠ Int64.minValue)
    (h_no_min_b : ∀ (i : Nat) (h : i < b.val.size),
                    b.val[i]'h ≠ Int64.minValue) :
    ∃ ra rb rc : i64,
      clever_107_count_nums.count_nums a = RustM.ok ra
      ∧ clever_107_count_nums.count_nums b = RustM.ok rb
      ∧ clever_107_count_nums.count_nums c = RustM.ok rc
      ∧ rc.toInt = ra.toInt + rb.toInt := by
  -- First, derive size relations
  have h_size_eq : c.val.size = a.val.size + b.val.size := aux_concat_size h_concat
  have h_a_size : (a.val.size : Int) < 2^63 := by
    have : a.val.size ≤ c.val.size := by omega
    have h : (a.val.size : Int) ≤ (c.val.size : Int) := by exact_mod_cast this
    omega
  have h_b_size : (b.val.size : Int) < 2^63 := by
    have : b.val.size ≤ c.val.size := by omega
    have h : (b.val.size : Int) ≤ (c.val.size : Int) := by exact_mod_cast this
    omega
  -- Derive h_no_min for c via the concat structure
  have h_no_min_c : ∀ (j : Nat) (h : j < c.val.size),
      c.val[j]'h ≠ Int64.minValue := by
    intro j h_lt
    by_cases h_left : j < a.val.size
    · rw [aux_concat_left_eq h_concat h_left h_lt]; exact h_no_min_a j h_left
    · have h_right : j - a.val.size < b.val.size := by omega
      rw [aux_concat_right_eq h_concat h_lt h_left h_right]
      exact h_no_min_b (j - a.val.size) h_right
  -- Compute count_at_correct for a, b, c
  have h_init_bound_a : (0 : i64).toInt + ((a.val.size : Int) - ((0 : usize).toNat : Int)) < 2^63 := by
    rw [i64_zero_toInt, usize_zero_toNat]; push_cast; omega
  have h_init_bound_b : (0 : i64).toInt + ((b.val.size : Int) - ((0 : usize).toNat : Int)) < 2^63 := by
    rw [i64_zero_toInt, usize_zero_toNat]; push_cast; omega
  have h_init_bound_c : (0 : i64).toInt + ((c.val.size : Int) - ((0 : usize).toNat : Int)) < 2^63 := by
    rw [i64_zero_toInt, usize_zero_toNat]; push_cast; omega
  obtain ⟨ra, h_a_eq, h_a_int⟩ :=
    count_at_correct a h_a_size h_no_min_a a.val.size (0 : usize) (0 : i64)
      (by rw [usize_zero_toNat]; omega)
      (by rw [usize_zero_toNat]; omega)
      (by rw [i64_zero_toInt]; exact Int.le_refl 0)
      h_init_bound_a
  obtain ⟨rb, h_b_eq, h_b_int⟩ :=
    count_at_correct b h_b_size h_no_min_b b.val.size (0 : usize) (0 : i64)
      (by rw [usize_zero_toNat]; omega)
      (by rw [usize_zero_toNat]; omega)
      (by rw [i64_zero_toInt]; exact Int.le_refl 0)
      h_init_bound_b
  obtain ⟨rc, h_c_eq, h_c_int⟩ :=
    count_at_correct c h_c_size h_no_min_c c.val.size (0 : usize) (0 : i64)
      (by rw [usize_zero_toNat]; omega)
      (by rw [usize_zero_toNat]; omega)
      (by rw [i64_zero_toInt]; exact Int.le_refl 0)
      h_init_bound_c
  refine ⟨ra, rb, rc, ?_, ?_, ?_, ?_⟩
  · unfold clever_107_count_nums.count_nums; exact h_a_eq
  · unfold clever_107_count_nums.count_nums; exact h_b_eq
  · unfold clever_107_count_nums.count_nums; exact h_c_eq
  · -- Additivity of pos_count_pref over concat
    have h_pc_zero : ∀ arr : Array i64, pos_count_pref arr 0 = 0 := by intro; simp [pos_count_pref]
    -- Need: pos_count_pref c.val c.val.size = pos_count_pref a.val a.val.size + pos_count_pref b.val b.val.size
    have h_pc_additive :
        pos_count_pref c.val c.val.size =
          pos_count_pref a.val a.val.size + pos_count_pref b.val b.val.size := by
      -- First: for k ≤ a.val.size, pos_count_pref c.val k = pos_count_pref a.val k
      have h_left : ∀ k, k ≤ a.val.size →
          pos_count_pref c.val k = pos_count_pref a.val k := by
        intro k h_le
        induction k with
        | zero => simp [pos_count_pref]
        | succ k ih =>
          have h_k_lt_a : k < a.val.size := by omega
          have h_k_lt_c : k < c.val.size := by omega
          rw [pos_count_pref_succ_in c.val k h_k_lt_c]
          rw [pos_count_pref_succ_in a.val k h_k_lt_a]
          rw [ih (by omega)]
          rw [aux_concat_left_eq h_concat h_k_lt_a h_k_lt_c]
      -- Then: for j (offset from a.size) and k = a.size + j ≤ c.size, 
      --   pos_count_pref c.val (a.size + j) = pos_count_pref a.val a.size + pos_count_pref b.val j
      have h_right : ∀ j, j ≤ b.val.size →
          pos_count_pref c.val (a.val.size + j) =
            pos_count_pref a.val a.val.size + pos_count_pref b.val j := by
        intro j h_le
        induction j with
        | zero => 
          rw [Nat.add_zero, h_left a.val.size (Nat.le_refl _)]
          simp [pos_count_pref]
        | succ j ih =>
          have h_j_lt_b : j < b.val.size := by omega
          have h_jak_lt_c : a.val.size + j < c.val.size := by omega
          have h_step : a.val.size + (j + 1) = (a.val.size + j) + 1 := by omega
          rw [h_step]
          rw [pos_count_pref_succ_in c.val (a.val.size + j) h_jak_lt_c]
          rw [pos_count_pref_succ_in b.val j h_j_lt_b]
          rw [ih (by omega)]
          have h_not_left : ¬ a.val.size + j < a.val.size := by omega
          have h_right_idx_lt : (a.val.size + j) - a.val.size < b.val.size := by
            have : (a.val.size + j) - a.val.size = j := by omega
            rw [this]; exact h_j_lt_b
          rw [aux_concat_right_eq h_concat h_jak_lt_c h_not_left h_right_idx_lt]
          have h_idx_eq : (a.val.size + j) - a.val.size = j := by omega
          have h_b_eq : b.val[(a.val.size + j) - a.val.size]'h_right_idx_lt =
                          b.val[j]'h_j_lt_b := by
            congr 1
          rw [h_b_eq]
          omega
      have h_full : pos_count_pref c.val c.val.size =
          pos_count_pref a.val a.val.size + pos_count_pref b.val b.val.size := by
        rw [h_size_eq]
        exact h_right b.val.size (Nat.le_refl _)
      exact h_full
    rw [h_a_int, h_b_int, h_c_int]
    rw [i64_zero_toInt, usize_zero_toNat]
    have h_pc_zero_a : pos_count_pref a.val 0 = 0 := h_pc_zero a.val
    have h_pc_zero_b : pos_count_pref b.val 0 = 0 := h_pc_zero b.val
    have h_pc_zero_c : pos_count_pref c.val 0 = 0 := h_pc_zero c.val
    rw [h_pc_zero_a, h_pc_zero_b, h_pc_zero_c]
    rw [h_pc_additive]
    push_cast; omega

/-- Unit pin: count_nums [-1, 11, -11] = 1. -/
theorem count_nums_at_neg_mix :
    clever_107_count_nums.count_nums
        { val := #[(-1 : i64), 11, -11], size_lt_usizeSize := by decide }
      = RustM.ok (1 : i64) := by
  native_decide

end Clever_107_count_numsObligations
