-- Companion obligations file for the `clever_143_order_by_points` extraction.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_143_order_by_points

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Clever_143_order_by_pointsObligations

/-! ## Specification oracles. -/

/-- Count occurrences of `target` among the first `k` entries of `s`. -/
private def vec_count (s : Array i64) (target : i64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      if h : k < s.size then
        (if (s[k]'h) = target then 1 else 0) + vec_count s target k
      else
        vec_count s target k

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

/-- Integer-level oracle for the sort key. -/
private def signed_digit_sum_int (n : Int) : Int :=
  if n = 0 then 0
  else if 0 < n then (digit_sum_nat n.toNat 0 : Int)
  else
    let m := (-n).toNat
    (digit_sum_nat m 0 : Int) - 2 * (first_digit_nat m : Int)

/-- Subsequence of the first `n` entries of `s` whose key equals `k`. -/
private def filter_by_key (s : Array i64) (k : Int) : Nat → Array i64
  | 0     => #[]
  | n + 1 =>
      if h : n < s.size then
        let rest := filter_by_key s k n
        if signed_digit_sum_int (s[n]'h).toInt = k then rest.push (s[n]'h)
        else rest
      else
        filter_by_key s k n

/-! ## Scaffolding lemmas. -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl
private theorem usize_zero_toNat : (0 : usize).toNat = 0 := rfl
private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide
private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide

private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide
private theorem i64_one_toInt  : (1 : i64).toInt = 1 := by decide
private theorem i64_two_toInt  : (2 : i64).toInt = 2 := by decide
private theorem i64_ten_toInt  : (10 : i64).toInt = 10 := by decide
private theorem int64_min_toInt : Int64.minValue.toInt = -(2^63 : Int) := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

private theorem usize_add_one_ok (i : usize) (h : i.toNat + 1 < 2^64) :
    (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
  show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
  show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure (i + 1)) = _
  have h_no_bv :
      BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hii := (USize64.uaddOverflow_iff i 1).mp hbo
      rw [usize_one_toNat] at hii
      omega
  rw [h_no_bv]; rfl

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

/-! ## Push helpers for the Vec accumulator. -/

private def push_one (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec i64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

private theorem push_one_size (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h : acc.val.size + 1 < USize64.size) :
    (push_one acc x h).val.size = acc.val.size + 1 := by
  show (acc.val ++ #[x]).size = acc.val.size + 1
  rw [Array.size_append]; rfl

/-! ## Reductions for primitive ops on `i64`. -/

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

private theorem i64_neg (n : i64) (h : n ≠ Int64.minValue) :
    (-? n : RustM i64) = pure (- n) := by
  show (rust_primitives.ops.arith.Neg.neg n : RustM i64) = pure (- n)
  show (if n = Int64.minValue then (.fail .integerOverflow : RustM i64)
        else pure (- n)) = _
  rw [if_neg h]

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

/-! ## Nat-level digit oracle equations and properties. -/

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

private theorem digit_sum_nat_bound_i64 (n acc : Nat) (h : n < 2^63) :
    digit_sum_nat n acc ≤ acc + 9 * 19 := by
  apply digit_sum_nat_le_pow 19
  have h_le : (2 : Nat) ^ 63 ≤ 10 ^ 19 := by decide
  omega

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

/-! ## Bridging i64/Int and Nat for n/10, n%10 (non-negative). -/

private theorem int_toNat_ediv {x y : Int} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x / y).toNat = x.toNat / y.toNat :=
  match x, y, Int.eq_ofNat_of_zero_le hx, Int.eq_ofNat_of_zero_le hy with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => rfl

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
      clever_143_order_by_points.first_digit_at n = RustM.ok r ∧
      r.toInt = (first_digit_nat n.toInt.toNat : Int) ∧
      0 ≤ r.toInt ∧
      r.toInt ≤ 9 := by
  induction hk : n.toInt.toNat using Nat.strongRecOn generalizing n with
  | _ k ih =>
    unfold clever_143_order_by_points.first_digit_at
    by_cases h_lt : n < (10 : i64)
    · have h_n_lt_10 : n.toInt < 10 := by
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
    · have h_n_ge_10 : (10 : Int) ≤ n.toInt := by
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
      clever_143_order_by_points.digit_sum_at n acc = RustM.ok r ∧
      r.toInt = acc.toInt + (digit_sum_nat n.toInt.toNat 0 : Int) ∧
      0 ≤ r.toInt := by
  induction hk : n.toInt.toNat using Nat.strongRecOn generalizing n acc with
  | _ k ih =>
    unfold clever_143_order_by_points.digit_sum_at
    by_cases h_eq_zero : n = (0 : i64)
    · subst h_eq_zero
      have h_beq : ((0 : i64) == (0 : i64)) = true := by decide
      simp only [show ((0 : i64) ==? (0 : i64) : RustM Bool) =
                   (pure ((0 : i64) == (0 : i64))) from rfl,
                 h_beq, pure_bind, ↓reduceIte]
      refine ⟨acc, rfl, ?_, hacc⟩
      have h_n_nat_zero : (0 : i64).toInt.toNat = 0 := by rw [i64_zero_toInt]; rfl
      rw [← hk, h_n_nat_zero, digit_sum_nat_zero]
      simp
    · have h_n_ne_zero_toInt : n.toInt ≠ 0 := by
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
      rw [i64_div_10 n, pure_bind]
      rw [i64_mod_10 n, pure_bind]
      have h_mod_nn : 0 ≤ (n % 10).toInt := i64_mod_10_nonneg n hn
      have h_mod_le_9 : (n % 10).toInt ≤ 9 := i64_mod_10_le_9 n hn
      have h_n_lt : n.toInt < 2^63 := i64_lt_max n
      have h_acc_lt : acc.toInt < 2^63 := i64_lt_max acc
      have h_acc_plus_mod_bound : acc.toInt + (n % 10).toInt < 2^63 := by
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

/-! ## `signed_digit_sum_int` equations. -/

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

/-! ## Pointwise correctness of `signed_digit_sum`. -/

private theorem signed_digit_sum_zero :
    clever_143_order_by_points.signed_digit_sum (0 : i64) = RustM.ok (0 : i64) := by
  unfold clever_143_order_by_points.signed_digit_sum
  have h_beq : ((0 : i64) == (0 : i64)) = true := by decide
  simp only [show ((0 : i64) ==? (0 : i64) : RustM Bool) =
               (pure ((0 : i64) == (0 : i64))) from rfl,
             h_beq, pure_bind, ↓reduceIte]
  rfl

private theorem signed_digit_sum_correct
    (n : i64) (h_no_min : n ≠ Int64.minValue) :
    ∃ r : i64,
      clever_143_order_by_points.signed_digit_sum n = RustM.ok r ∧
      r.toInt = signed_digit_sum_int n.toInt := by
  unfold clever_143_order_by_points.signed_digit_sum
  by_cases h_zero : n = (0 : i64)
  · subst h_zero
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
    · have h_n_pos_int : 0 < n.toInt := by
        have := Int64.lt_iff_toInt_lt.mp h_pos
        simpa [i64_zero_toInt] using this
      have h_n_nn : 0 ≤ n.toInt := by omega
      have h_dec_gt : decide ((0 : i64) < n) = true := decide_eq_true h_pos
      simp only [show (n >? (0 : i64) : RustM Bool) =
                   (pure (decide ((0 : i64) < n)) : RustM Bool) from rfl,
                 h_dec_gt, pure_bind, ↓reduceIte]
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
    · have h_n_neg_int : n.toInt < 0 := by
        have h_not_pos : ¬ (0 : i64) < n := h_pos
        have h_not_int : ¬ (0 : Int) < n.toInt := by
          intro hh; apply h_not_pos
          rw [Int64.lt_iff_toInt_lt, i64_zero_toInt]; exact hh
        omega
      have h_dec_gt : decide ((0 : i64) < n) = false := decide_eq_false h_pos
      simp only [show (n >? (0 : i64) : RustM Bool) =
                   (pure (decide ((0 : i64) < n)) : RustM Bool) from rfl,
                 h_dec_gt, pure_bind, Bool.false_eq_true, ↓reduceIte]
      rw [i64_neg n h_no_min, pure_bind]
      have h_m_toInt : (-n).toInt = -n.toInt := Int64.toInt_neg_of_ne_intMin h_no_min
      have h_m_pos : 0 < (-n).toInt := by rw [h_m_toInt]; omega
      have h_m_nn : 0 ≤ (-n).toInt := by omega
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
      obtain ⟨fd, h_fd_eq, h_fd_int, h_fd_nn, h_fd_le_9⟩ :=
        first_digit_at_correct (-n) h_m_nn
      rw [h_fd_eq]
      simp only [RustM_ok_bind]
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
      have h_no_sub_ov : ¬ Int64.subOverflow ds ((2 : i64) * fd) := by
        intro hov
        rw [Int64.subOverflow_iff] at hov
        rw [h_2fd_toInt] at hov
        have h63 : (2 : Int) ^ (64 - 1) = 2^63 := by decide
        rw [h63] at hov
        rcases hov with hov | hov
        · omega
        · omega
      rw [i64_sub_pure ds ((2 : i64) * fd) h_no_sub_ov]
      refine ⟨ds - (2 : i64) * fd, rfl, ?_⟩
      rw [Int64.toInt_sub_of_not_subOverflow h_no_sub_ov, h_2fd_toInt]
      rw [signed_digit_sum_int_neg n.toInt h_n_neg_int]
      rw [h_ds_int, h_fd_int]
      rw [i64_zero_toInt, h_m_toInt]; omega

/-! ## `vec_count` lemmas. -/

private theorem vec_count_succ (s : Array i64) (target : i64) (k : Nat) (hk : k < s.size) :
    vec_count s target (k + 1) =
      (if (s[k]'hk) = target then 1 else 0) + vec_count s target k := by
  show (if h : k < s.size then
          (if (s[k]'h) = target then 1 else 0) + vec_count s target k
        else vec_count s target k) = _
  rw [dif_pos hk]

private theorem vec_count_prefix (acc : Array i64) (y target : i64) :
    ∀ k, k ≤ acc.size →
      vec_count (acc ++ #[y]) target k = vec_count acc target k := by
  have h_size_app : (acc ++ #[y]).size = acc.size + 1 := by rw [Array.size_append]; rfl
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk_lt : k < acc.size := by omega
    have hk_lt_app : k < (acc ++ #[y]).size := by rw [h_size_app]; omega
    have h_app : (acc ++ #[y])[k]'hk_lt_app = acc[k]'hk_lt :=
      Array.getElem_append_left hk_lt
    show (if h : k < (acc ++ #[y]).size then
            (if ((acc ++ #[y])[k]'h) = target then 1 else 0)
              + vec_count (acc ++ #[y]) target k
          else vec_count (acc ++ #[y]) target k) = _
    rw [dif_pos hk_lt_app, h_app, ih (Nat.le_of_lt hk)]
    show _ = (if h : k < acc.size then
                (if (acc[k]'h) = target then 1 else 0) + vec_count acc target k
              else vec_count acc target k)
    rw [dif_pos hk_lt]

private theorem vec_count_append_singleton (acc : Array i64) (y target : i64) :
    vec_count (acc ++ #[y]) target (acc.size + 1) =
      vec_count acc target acc.size + (if y = target then 1 else 0) := by
  have h_size_app : (acc ++ #[y]).size = acc.size + 1 := by rw [Array.size_append]; rfl
  have h_lt : acc.size < (acc ++ #[y]).size := by rw [h_size_app]; omega
  have h_get : (acc ++ #[y])[acc.size]'h_lt = y := by
    rw [Array.getElem_append_right (Nat.le_refl _)]
    simp
  have h_step := vec_count_succ (acc ++ #[y]) target acc.size h_lt
  rw [h_step, h_get, vec_count_prefix acc y target acc.size (Nat.le_refl _)]
  omega

/-! ## Sortedness predicate. -/

/-- Sort key on `i64` (Int-level oracle on the underlying integer). -/
private abbrev key (x : i64) : Int := signed_digit_sum_int x.toInt

/-- An array is sorted by `key` when all index pairs k₁ ≤ k₂ have key(arr[k₁]) ≤ key(arr[k₂]). -/
private def sorted_by_key (arr : Array i64) : Prop :=
  ∀ (k₁ k₂ : Nat) (h₁ : k₁ < arr.size) (h₂ : k₂ < arr.size),
    k₁ ≤ k₂ → key (arr[k₁]'h₁) ≤ key (arr[k₂]'h₂)

private theorem sorted_by_key_empty : sorted_by_key #[] := by
  intro k₁ k₂ h₁ _ _
  have : (#[] : Array i64).size = 0 := rfl
  omega

private theorem sorted_by_key_append_singleton (acc : Array i64) (y : i64)
    (h_acc : sorted_by_key acc)
    (h_le : ∀ (k : Nat) (hk : k < acc.size), key (acc[k]'hk) ≤ key y) :
    sorted_by_key (acc ++ #[y]) := by
  intro k₁ k₂ h₁ h₂ hle12
  rw [Array.size_append] at h₁ h₂
  have h_one : (#[y] : Array i64).size = 1 := rfl
  by_cases h_k1_lt : k₁ < acc.size
  · by_cases h_k2_lt : k₂ < acc.size
    · rw [Array.getElem_append_left h_k1_lt, Array.getElem_append_left h_k2_lt]
      exact h_acc k₁ k₂ h_k1_lt h_k2_lt hle12
    · have h_k2_ge : acc.size ≤ k₂ := by omega
      rw [Array.getElem_append_left h_k1_lt]
      rw [Array.getElem_append_right h_k2_ge]
      have h_idx : k₂ - acc.size = 0 := by omega
      have h_zero : (0 : Nat) < (#[y] : Array i64).size := by rw [h_one]; omega
      rw [show ((#[y] : Array i64)[k₂ - acc.size]'(by rw [h_idx]; exact h_zero))
              = (#[y] : Array i64)[0]'h_zero from by simp [h_idx]]
      show key (acc[k₁]'h_k1_lt) ≤ key y
      exact h_le k₁ h_k1_lt
  · have h_k1_ge : acc.size ≤ k₁ := by omega
    have h_k2_ge : acc.size ≤ k₂ := by omega
    rw [Array.getElem_append_right h_k1_ge, Array.getElem_append_right h_k2_ge]
    have h_k1_idx : k₁ - acc.size = 0 := by omega
    have h_k2_idx : k₂ - acc.size = 0 := by omega
    have h_zero : (0 : Nat) < (#[y] : Array i64).size := by rw [h_one]; omega
    rw [show ((#[y] : Array i64)[k₁ - acc.size]'(by rw [h_k1_idx]; exact h_zero))
            = (#[y] : Array i64)[0]'h_zero from by simp [h_k1_idx]]
    rw [show ((#[y] : Array i64)[k₂ - acc.size]'(by rw [h_k2_idx]; exact h_zero))
            = (#[y] : Array i64)[0]'h_zero from by simp [h_k2_idx]]
    exact Int.le_refl _

/-- Push two elements onto a Vec. -/
private def push_two (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x y : i64)
    (h : acc.val.size + 2 < USize64.size) :
    alloc.vec.Vec i64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x, y], by
    have h_size : (acc.val ++ #[x, y]).size = acc.val.size + 2 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

private theorem push_two_size (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x y : i64)
    (h : acc.val.size + 2 < USize64.size) :
    (push_two acc x y h).val.size = acc.val.size + 2 := by
  show (acc.val ++ #[x, y]).size = acc.val.size + 2
  rw [Array.size_append]; rfl

private theorem two_lt_usize_size : (2 : Nat) < USize64.size := by decide

/-! ## Bool reductions for i64 comparisons. -/

private theorem i64_gt_test (a b : i64) :
    (a >? b : RustM Bool) = pure (decide (b < a)) := rfl

private theorem i64_lt_test (a b : i64) :
    (a <? b : RustM Bool) = pure (decide (a < b)) := rfl

private theorem i64_eq_test (a b : i64) :
    (a ==? b : RustM Bool) = pure (a == b) := rfl

/-! ## `insert_stable_at` OOB / step / fail lemmas. -/

private theorem insert_stable_at_oob_done
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (x kx : i64) (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat) :
    clever_143_order_by_points.insert_stable_at v x kx i true acc = RustM.ok acc := by
  unfold clever_143_order_by_points.insert_stable_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat v.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]; rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  simp only [alloc.vec.Impl_1.len,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, ↓reduceIte]
  rfl

private theorem insert_stable_at_oob_not_done
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (x kx : i64) (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_143_order_by_points.insert_stable_at v x kx i false acc =
      RustM.ok (push_one acc x h_acc) := by
  unfold clever_143_order_by_points.insert_stable_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat v.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]; rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  have h_app_size : acc.val.size + (#[x] : Array i64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  have h_extend :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[x], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.ok (push_one acc x h_acc) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]; rfl
  simp only [alloc.vec.Impl_1.len,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, ↓reduceIte]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[x] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[x], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend]
  rfl

private theorem insert_stable_at_oob_not_done_fail
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (x kx : i64) (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_143_order_by_points.insert_stable_at v x kx i false acc
      = RustM.fail .maximumSizeExceeded := by
  unfold clever_143_order_by_points.insert_stable_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat v.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]; rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  have h_app_size_neg :
      ¬ acc.val.size + (#[x] : Array i64).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[x], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [alloc.vec.Impl_1.len,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, ↓reduceIte]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[x] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[x], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

/-- Step-insert branch: i in bounds, vi ≠ minValue, done=false,
    kx.toInt < key(vi). Extends acc with `[x, vi]`, recurses with done=true. -/
private theorem insert_stable_at_step_insert
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (x kx : i64) (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_vi_no_min : (v.val[i.toNat]'hi) ≠ Int64.minValue)
    (h_lt : kx.toInt < key (v.val[i.toNat]'hi))
    (h_acc : acc.val.size + 2 < USize64.size) :
    clever_143_order_by_points.insert_stable_at v x kx i false acc =
      clever_143_order_by_points.insert_stable_at v x kx (i + 1) true
        (push_two acc x (v.val[i.toNat]'hi) h_acc) := by
  conv => lhs; unfold clever_143_order_by_points.insert_stable_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM i64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  obtain ⟨s, h_s_eq, h_s_int⟩ := signed_digit_sum_correct _ h_vi_no_min
  have h_kx_lt_s : kx < s := by
    rw [Int64.lt_iff_toInt_lt, h_s_int]; exact h_lt
  have h_dec_lt : decide (kx < s) = true := decide_eq_true h_kx_lt_s
  have h_add : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := usize_add_one_ok i h_no_ov_i
  have h_app_size : acc.val.size + (#[x, v.val[i.toNat]'hi] : Array i64).size < USize64.size := by
    show acc.val.size + 2 < USize64.size; exact h_acc
  have h_extend :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[x, v.val[i.toNat]'hi], two_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.ok (push_two acc x (v.val[i.toNat]'hi) h_acc) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]; rfl
  simp only [alloc.vec.Impl_1.len,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx]
  rw [h_s_eq]
  simp only [RustM_ok_bind]
  rw [i64_gt_test]
  simp only [pure_bind]
  rw [h_dec_lt]
  simp only [rust_primitives.hax.logical_op.not,
             rust_primitives.hax.logical_op.and,
             pure_bind, Bool.not_false, Bool.true_and, ↓reduceIte]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[x, v.val[i.toNat]'hi] : RustArray i64 2)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[x, v.val[i.toNat]'hi], two_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend]
  simp only [RustM_ok_bind]
  rw [h_add]
  simp only [RustM_ok_bind]

/-- Step-insert failure: extend overflows. -/
private theorem insert_stable_at_step_insert_fail
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (x kx : i64) (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_vi_no_min : (v.val[i.toNat]'hi) ≠ Int64.minValue)
    (h_lt : kx.toInt < key (v.val[i.toNat]'hi))
    (h_big : USize64.size ≤ acc.val.size + 2) :
    clever_143_order_by_points.insert_stable_at v x kx i false acc
      = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_143_order_by_points.insert_stable_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM i64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  obtain ⟨s, h_s_eq, h_s_int⟩ := signed_digit_sum_correct _ h_vi_no_min
  have h_kx_lt_s : kx < s := by
    rw [Int64.lt_iff_toInt_lt, h_s_int]; exact h_lt
  have h_dec_lt : decide (kx < s) = true := decide_eq_true h_kx_lt_s
  have h_app_size_neg :
      ¬ acc.val.size + (#[x, v.val[i.toNat]'hi] : Array i64).size < USize64.size := by
    show ¬ acc.val.size + 2 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[x, v.val[i.toNat]'hi], two_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [alloc.vec.Impl_1.len,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx]
  rw [h_s_eq]
  simp only [RustM_ok_bind]
  rw [i64_gt_test]
  simp only [pure_bind]
  rw [h_dec_lt]
  simp only [rust_primitives.hax.logical_op.not,
             rust_primitives.hax.logical_op.and,
             pure_bind, Bool.not_false, Bool.true_and, ↓reduceIte]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[x, v.val[i.toNat]'hi] : RustArray i64 2)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[x, v.val[i.toNat]'hi], two_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

/-- Pass step: i in bounds, vi ≠ minValue, and either done=true or
    key(vi) ≤ kx.toInt. Extends acc with `[vi]` and recurses with same done. -/
private theorem insert_stable_at_step_pass
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (x kx : i64) (i : usize) (done : Bool) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_vi_no_min : (v.val[i.toNat]'hi) ≠ Int64.minValue)
    (h_skip : done = true ∨ key (v.val[i.toNat]'hi) ≤ kx.toInt)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_143_order_by_points.insert_stable_at v x kx i done acc =
      clever_143_order_by_points.insert_stable_at v x kx (i + 1) done
        (push_one acc (v.val[i.toNat]'hi) h_acc) := by
  conv => lhs; unfold clever_143_order_by_points.insert_stable_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM i64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  obtain ⟨s, h_s_eq, h_s_int⟩ := signed_digit_sum_correct _ h_vi_no_min
  -- Either done=true (so !done && _ = false), or key(vi) ≤ kx.toInt (so kx < s is false).
  have h_cond_false : ((!done) && (decide (kx < s))) = false := by
    cases h_skip with
    | inl h_done_true => subst h_done_true; rfl
    | inr h_le =>
      have h_le' : signed_digit_sum_int (v.val[i.toNat]'hi).toInt ≤ kx.toInt := h_le
      have h_not_lt : ¬ (kx < s) := by
        intro h
        have h_int : kx.toInt < s.toInt := Int64.lt_iff_toInt_lt.mp h
        rw [h_s_int] at h_int
        omega
      have hh : decide (kx < s) = false := decide_eq_false h_not_lt
      rw [hh]
      cases done <;> rfl
  have h_add : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := usize_add_one_ok i h_no_ov_i
  have h_app_size :
      acc.val.size + (#[v.val[i.toNat]'hi] : Array i64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  have h_extend :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[v.val[i.toNat]'hi], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.ok (push_one acc (v.val[i.toNat]'hi) h_acc) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]; rfl
  simp only [alloc.vec.Impl_1.len,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx]
  rw [h_s_eq]
  simp only [RustM_ok_bind]
  rw [i64_gt_test]
  simp only [pure_bind]
  simp only [rust_primitives.hax.logical_op.not,
             rust_primitives.hax.logical_op.and,
             pure_bind]
  rw [h_cond_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[v.val[i.toNat]'hi] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[v.val[i.toNat]'hi], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend]
  simp only [RustM_ok_bind]
  rw [h_add]
  simp only [RustM_ok_bind]

/-- Pass step failure: extend overflows. -/
private theorem insert_stable_at_step_pass_fail
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (x kx : i64) (i : usize) (done : Bool) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_vi_no_min : (v.val[i.toNat]'hi) ≠ Int64.minValue)
    (h_skip : done = true ∨ key (v.val[i.toNat]'hi) ≤ kx.toInt)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_143_order_by_points.insert_stable_at v x kx i done acc
      = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_143_order_by_points.insert_stable_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM i64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  obtain ⟨s, h_s_eq, h_s_int⟩ := signed_digit_sum_correct _ h_vi_no_min
  have h_cond_false : ((!done) && (decide (kx < s))) = false := by
    cases h_skip with
    | inl h_done_true => subst h_done_true; rfl
    | inr h_le =>
      have h_le' : signed_digit_sum_int (v.val[i.toNat]'hi).toInt ≤ kx.toInt := h_le
      have h_not_lt : ¬ (kx < s) := by
        intro h
        have h_int : kx.toInt < s.toInt := Int64.lt_iff_toInt_lt.mp h
        rw [h_s_int] at h_int
        omega
      have hh : decide (kx < s) = false := decide_eq_false h_not_lt
      rw [hh]
      cases done <;> rfl
  have h_app_size_neg :
      ¬ acc.val.size + (#[v.val[i.toNat]'hi] : Array i64).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[v.val[i.toNat]'hi], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [alloc.vec.Impl_1.len,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx]
  rw [h_s_eq]
  simp only [RustM_ok_bind]
  rw [i64_gt_test]
  simp only [pure_bind]
  simp only [rust_primitives.hax.logical_op.not,
             rust_primitives.hax.logical_op.and,
             pure_bind]
  rw [h_cond_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[v.val[i.toNat]'hi] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[v.val[i.toNat]'hi], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

/-! ## `insert_stable_at` invariant (size + vec_count). -/

private theorem insert_stable_at_inv :
    ∀ (n : Nat) (v : alloc.vec.Vec i64 alloc.alloc.Global) (x kx : i64)
      (i : usize) (done : Bool)
      (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global) (target : i64),
      v.val.size - i.toNat ≤ n →
      i.toNat ≤ v.val.size →
      (∀ (k : Nat) (h : k < v.val.size), i.toNat ≤ k → v.val[k]'h ≠ Int64.minValue) →
      clever_143_order_by_points.insert_stable_at v x kx i done acc = RustM.ok r →
      r.val.size = acc.val.size + (v.val.size - i.toNat) + (if done then 0 else 1) ∧
      vec_count r.val target r.val.size + vec_count v.val target i.toNat =
        vec_count acc.val target acc.val.size + vec_count v.val target v.val.size
          + (if done then 0 else (if x = target then 1 else 0)) := by
  intro n
  induction n with
  | zero =>
    intro v x kx i done acc r target hm hi_le h_nomin hres
    have hi_ge : v.val.size ≤ i.toNat := by omega
    have hi_eq : i.toNat = v.val.size := by omega
    cases done with
    | true =>
      rw [insert_stable_at_oob_done v x kx i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      refine ⟨?_, ?_⟩
      · simp [hi_eq]
      · rw [hi_eq]; simp
    | false =>
      by_cases h_acc : acc.val.size + 1 < USize64.size
      · rw [insert_stable_at_oob_not_done v x kx i acc hi_ge h_acc] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        refine ⟨?_, ?_⟩
        · show (acc.val ++ #[x]).size = acc.val.size + (v.val.size - i.toNat) + 1
          rw [Array.size_append]; simp; omega
        · show vec_count (acc.val ++ #[x]) target (acc.val ++ #[x]).size + vec_count v.val target i.toNat
              = vec_count acc.val target acc.val.size + vec_count v.val target v.val.size
                + (if x = target then 1 else 0)
          have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
            rw [Array.size_append]; rfl
          rw [h_size, vec_count_append_singleton, hi_eq]
          omega
      · exfalso
        have h_big : USize64.size ≤ acc.val.size + 1 := by omega
        rw [insert_stable_at_oob_not_done_fail v x kx i acc hi_ge h_big] at hres
        cases hres
  | succ n ih =>
    intro v x kx i done acc r target hm hi_le h_nomin hres
    by_cases hi_ge : v.val.size ≤ i.toNat
    · have hi_eq : i.toNat = v.val.size := by omega
      cases done with
      | true =>
        rw [insert_stable_at_oob_done v x kx i acc hi_ge] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        refine ⟨?_, ?_⟩
        · simp [hi_eq]
        · rw [hi_eq]; simp
      | false =>
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [insert_stable_at_oob_not_done v x kx i acc hi_ge h_acc] at hres
          injection hres with h_eq
          injection h_eq with h_eq'
          subst h_eq'
          refine ⟨?_, ?_⟩
          · show (acc.val ++ #[x]).size = acc.val.size + (v.val.size - i.toNat) + 1
            rw [Array.size_append]; simp; omega
          · show vec_count (acc.val ++ #[x]) target (acc.val ++ #[x]).size + vec_count v.val target i.toNat
                = vec_count acc.val target acc.val.size + vec_count v.val target v.val.size
                  + (if x = target then 1 else 0)
            have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
              rw [Array.size_append]; rfl
            rw [h_size, vec_count_append_singleton, hi_eq]
            omega
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_stable_at_oob_not_done_fail v x kx i acc hi_ge h_big] at hres
          cases hres
    · have hi_lt : i.toNat < v.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ v.val.size := by rw [h_i1]; omega
      have h_meas : v.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      have h_vi_no_min : v.val[i.toNat]'hi_lt ≠ Int64.minValue :=
        h_nomin i.toNat hi_lt (Nat.le_refl _)
      have h_nomin_next : ∀ (k : Nat) (h : k < v.val.size),
          (i + 1).toNat ≤ k → v.val[k]'h ≠ Int64.minValue := by
        intro k h_lt h_ge
        apply h_nomin k h_lt
        rw [h_i1] at h_ge; omega
      have h_vec_succ_v :
          vec_count v.val target (i.toNat + 1) =
            (if v.val[i.toNat]'hi_lt = target then 1 else 0) + vec_count v.val target i.toNat :=
        vec_count_succ v.val target i.toNat hi_lt
      -- Case split on the if condition inside.
      cases done with
      | true =>
        -- done = true, so we always pass.
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · -- Need step_pass with done=true.
          rw [insert_stable_at_step_pass v x kx i true acc hi_lt h_vi_no_min (Or.inl rfl) h_acc] at hres
          have h_push_size :
              (push_one acc (v.val[i.toNat]'hi_lt) h_acc).val.size = acc.val.size + 1 :=
            push_one_size acc _ h_acc
          have h_count_pushed :
              vec_count (push_one acc (v.val[i.toNat]'hi_lt) h_acc).val target
                (acc.val.size + 1) =
              vec_count acc.val target acc.val.size +
                (if v.val[i.toNat]'hi_lt = target then 1 else 0) := by
            show vec_count (acc.val ++ #[v.val[i.toNat]'hi_lt]) target (acc.val.size + 1) = _
            exact vec_count_append_singleton acc.val (v.val[i.toNat]'hi_lt) target
          have ih_app := ih v x kx (i + 1) true (push_one acc (v.val[i.toNat]'hi_lt) h_acc) r target
            h_meas h_i1_le h_nomin_next hres
          rw [h_i1] at ih_app
          obtain ⟨h_size_eq, h_count_eq⟩ := ih_app
          rw [h_push_size] at h_size_eq h_count_eq
          simp only [if_true, if_pos rfl] at h_size_eq h_count_eq
          refine ⟨?_, ?_⟩
          · simp only [if_true, if_pos rfl]; rw [h_size_eq]
            have : 0 < v.val.size - i.toNat := by omega
            omega
          · simp only [if_true, if_pos rfl]
            rw [h_count_pushed] at h_count_eq
            rw [h_vec_succ_v] at h_count_eq
            omega
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_stable_at_step_pass_fail v x kx i true acc hi_lt h_vi_no_min (Or.inl rfl) h_big] at hres
          cases hres
      | false =>
        -- done = false. Split on whether kx < key(v[i]) (insert) or not (pass).
        by_cases h_lt : kx.toInt < key (v.val[i.toNat]'hi_lt)
        · -- Insert branch
          by_cases h_acc : acc.val.size + 2 < USize64.size
          · rw [insert_stable_at_step_insert v x kx i acc hi_lt h_vi_no_min h_lt h_acc] at hres
            have h_push2_size :
                (push_two acc x (v.val[i.toNat]'hi_lt) h_acc).val.size = acc.val.size + 2 :=
              push_two_size acc x _ h_acc
            -- vec_count of push_two = acc + (x = target ? 1 : 0) + (vi = target ? 1 : 0)
            have h_count_pushed_2 :
                vec_count (push_two acc x (v.val[i.toNat]'hi_lt) h_acc).val target
                  (acc.val.size + 2) =
                vec_count acc.val target acc.val.size +
                  (if x = target then 1 else 0) +
                  (if v.val[i.toNat]'hi_lt = target then 1 else 0) := by
              show vec_count (acc.val ++ #[x, v.val[i.toNat]'hi_lt]) target (acc.val.size + 2) = _
              -- Show: vec_count at size acc+2 = vec_count at size acc+1 + (vi = target?)
              -- by directly using the recurrence.
              have h_app_size : (acc.val ++ #[x, v.val[i.toNat]'hi_lt]).size = acc.val.size + 2 := by
                rw [Array.size_append]; rfl
              have h_lt2 : acc.val.size + 1 < (acc.val ++ #[x, v.val[i.toNat]'hi_lt]).size := by
                rw [h_app_size]; omega
              have h_get_2 :
                  (acc.val ++ #[x, v.val[i.toNat]'hi_lt])[acc.val.size + 1]'h_lt2
                    = v.val[i.toNat]'hi_lt := by
                rw [Array.getElem_append_right (by omega : acc.val.size ≤ acc.val.size + 1)]
                have h_idx : acc.val.size + 1 - acc.val.size = 1 := by omega
                simp [h_idx]
              have h_step2 := vec_count_succ (acc.val ++ #[x, v.val[i.toNat]'hi_lt])
                target (acc.val.size + 1) h_lt2
              rw [h_step2, h_get_2]
              -- Now vec_count (acc++[x,vi]) target (acc.size + 1)
              -- equals vec_count acc target acc.size + (x = target ? 1 : 0)
              -- because the (acc.size)-th element is x.
              have h_lt1 : acc.val.size < (acc.val ++ #[x, v.val[i.toNat]'hi_lt]).size := by
                rw [h_app_size]; omega
              have h_get_1 :
                  (acc.val ++ #[x, v.val[i.toNat]'hi_lt])[acc.val.size]'h_lt1 = x := by
                rw [Array.getElem_append_right (Nat.le_refl _)]
                simp
              have h_step1 := vec_count_succ (acc.val ++ #[x, v.val[i.toNat]'hi_lt])
                target acc.val.size h_lt1
              rw [h_step1, h_get_1]
              -- vec_count (acc++[x,vi]) target acc.size = vec_count acc target acc.size
              have h_pref :
                  vec_count (acc.val ++ #[x, v.val[i.toNat]'hi_lt]) target acc.val.size
                    = vec_count acc.val target acc.val.size := by
                -- generalize the singleton-prefix lemma
                have h_gen : ∀ k, k ≤ acc.val.size →
                    vec_count (acc.val ++ #[x, v.val[i.toNat]'hi_lt]) target k
                      = vec_count acc.val target k := by
                  intro k hk
                  induction k with
                  | zero => rfl
                  | succ k ih =>
                    have hk_lt_acc : k < acc.val.size := by omega
                    have hk_lt_app : k < (acc.val ++ #[x, v.val[i.toNat]'hi_lt]).size := by
                      rw [h_app_size]; omega
                    have h_get_k :
                        (acc.val ++ #[x, v.val[i.toNat]'hi_lt])[k]'hk_lt_app
                          = acc.val[k]'hk_lt_acc :=
                      Array.getElem_append_left hk_lt_acc
                    rw [vec_count_succ _ _ k hk_lt_app, vec_count_succ _ _ k hk_lt_acc]
                    rw [h_get_k, ih (Nat.le_of_lt hk)]
                exact h_gen acc.val.size (Nat.le_refl _)
              rw [h_pref]
              omega
            have ih_app := ih v x kx (i + 1) true
              (push_two acc x (v.val[i.toNat]'hi_lt) h_acc) r target h_meas h_i1_le h_nomin_next hres
            rw [h_i1] at ih_app
            obtain ⟨h_size_eq, h_count_eq⟩ := ih_app
            rw [h_push2_size] at h_size_eq h_count_eq
            rw [if_pos (rfl : true = true)] at h_size_eq h_count_eq
            rw [if_neg (Bool.false_ne_true), if_neg (Bool.false_ne_true)]
            rw [h_count_pushed_2] at h_count_eq
            rw [h_vec_succ_v] at h_count_eq
            refine ⟨?_, ?_⟩
            · rw [h_size_eq]
              have : 0 < v.val.size - i.toNat := by omega
              omega
            · omega
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 2 := by omega
            rw [insert_stable_at_step_insert_fail v x kx i acc hi_lt h_vi_no_min h_lt h_big] at hres
            cases hres
        · -- Pass branch (done=false, key(vi) ≤ kx.toInt)
          have h_le : key (v.val[i.toNat]'hi_lt) ≤ kx.toInt := by
            simp only [key] at h_lt ⊢
            omega
          by_cases h_acc : acc.val.size + 1 < USize64.size
          · rw [insert_stable_at_step_pass v x kx i false acc hi_lt h_vi_no_min (Or.inr h_le) h_acc] at hres
            have h_push_size :
                (push_one acc (v.val[i.toNat]'hi_lt) h_acc).val.size = acc.val.size + 1 :=
              push_one_size acc _ h_acc
            have h_count_pushed :
                vec_count (push_one acc (v.val[i.toNat]'hi_lt) h_acc).val target
                  (acc.val.size + 1) =
                vec_count acc.val target acc.val.size +
                  (if v.val[i.toNat]'hi_lt = target then 1 else 0) := by
              show vec_count (acc.val ++ #[v.val[i.toNat]'hi_lt]) target (acc.val.size + 1) = _
              exact vec_count_append_singleton acc.val (v.val[i.toNat]'hi_lt) target
            have ih_app := ih v x kx (i + 1) false
              (push_one acc (v.val[i.toNat]'hi_lt) h_acc) r target h_meas h_i1_le h_nomin_next hres
            rw [h_i1] at ih_app
            obtain ⟨h_size_eq, h_count_eq⟩ := ih_app
            rw [h_push_size] at h_size_eq h_count_eq
            rw [if_neg (Bool.false_ne_true)] at h_size_eq h_count_eq
            rw [if_neg (Bool.false_ne_true), if_neg (Bool.false_ne_true)]
            rw [h_count_pushed] at h_count_eq
            rw [h_vec_succ_v] at h_count_eq
            refine ⟨?_, ?_⟩
            · rw [h_size_eq]
              have : 0 < v.val.size - i.toNat := by omega
              omega
            · omega
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 1 := by omega
            rw [insert_stable_at_step_pass_fail v x kx i false acc hi_lt h_vi_no_min (Or.inr h_le) h_big] at hres
            cases hres

/-! ## `insert_stable_at` sortedness invariant. -/

private theorem insert_stable_at_sorted
    (v : alloc.vec.Vec i64 alloc.alloc.Global) (x kx : i64)
    (h_v_sorted : sorted_by_key v.val)
    (h_kx : kx.toInt = key x) :
    ∀ (n : Nat) (i : usize) (done : Bool)
      (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      v.val.size - i.toNat ≤ n →
      i.toNat ≤ v.val.size →
      (∀ (k : Nat) (h : k < v.val.size), i.toNat ≤ k → v.val[k]'h ≠ Int64.minValue) →
      clever_143_order_by_points.insert_stable_at v x kx i done acc = RustM.ok r →
      sorted_by_key acc.val →
      (∀ (k : Nat) (hk : k < acc.val.size) (hi_lt : i.toNat < v.val.size),
          key (acc.val[k]'hk) ≤ key (v.val[i.toNat]'hi_lt)) →
      (done = false →
          ∀ (k : Nat) (hk : k < acc.val.size), key (acc.val[k]'hk) ≤ kx.toInt) →
      sorted_by_key r.val := by
  intro n
  induction n with
  | zero =>
    intro i done acc r hm hi_le h_nomin hres h_acc_sorted h_acc_le_vi h_acc_le_kx
    have hi_ge : v.val.size ≤ i.toNat := by omega
    cases done with
    | true =>
      rw [insert_stable_at_oob_done v x kx i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      exact h_acc_sorted
    | false =>
      by_cases h_acc : acc.val.size + 1 < USize64.size
      · rw [insert_stable_at_oob_not_done v x kx i acc hi_ge h_acc] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        show sorted_by_key (acc.val ++ #[x])
        apply sorted_by_key_append_singleton acc.val x h_acc_sorted
        intro k hk
        have : key (acc.val[k]'hk) ≤ kx.toInt := h_acc_le_kx rfl k hk
        rw [h_kx] at this; exact this
      · exfalso
        have h_big : USize64.size ≤ acc.val.size + 1 := by omega
        rw [insert_stable_at_oob_not_done_fail v x kx i acc hi_ge h_big] at hres
        cases hres
  | succ n ih =>
    intro i done acc r hm hi_le h_nomin hres h_acc_sorted h_acc_le_vi h_acc_le_kx
    by_cases hi_ge : v.val.size ≤ i.toNat
    · cases done with
      | true =>
        rw [insert_stable_at_oob_done v x kx i acc hi_ge] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        exact h_acc_sorted
      | false =>
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [insert_stable_at_oob_not_done v x kx i acc hi_ge h_acc] at hres
          injection hres with h_eq
          injection h_eq with h_eq'
          subst h_eq'
          show sorted_by_key (acc.val ++ #[x])
          apply sorted_by_key_append_singleton acc.val x h_acc_sorted
          intro k hk
          have : key (acc.val[k]'hk) ≤ kx.toInt := h_acc_le_kx rfl k hk
          rw [h_kx] at this; exact this
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_stable_at_oob_not_done_fail v x kx i acc hi_ge h_big] at hres
          cases hres
    · have hi_lt : i.toNat < v.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ v.val.size := by rw [h_i1]; omega
      have h_meas : v.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      have h_vi_no_min : v.val[i.toNat]'hi_lt ≠ Int64.minValue :=
        h_nomin i.toNat hi_lt (Nat.le_refl _)
      have h_nomin_next : ∀ (k : Nat) (h : k < v.val.size),
          (i + 1).toNat ≤ k → v.val[k]'h ≠ Int64.minValue := by
        intro k h_lt h_ge
        apply h_nomin k h_lt
        rw [h_i1] at h_ge; omega
      -- Sortedness of v: key(v[i]) ≤ key(v[i+1])
      have h_v_step (hi_i1 : (i + 1).toNat < v.val.size) :
          key (v.val[i.toNat]'hi_lt) ≤ key (v.val[(i + 1).toNat]'hi_i1) := by
        have h_le_idx : i.toNat ≤ (i + 1).toNat := by rw [h_i1]; omega
        have h_int_le := h_v_sorted i.toNat (i + 1).toNat hi_lt hi_i1 h_le_idx
        exact h_int_le
      cases done with
      | true =>
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [insert_stable_at_step_pass v x kx i true acc hi_lt h_vi_no_min (Or.inl rfl) h_acc] at hres
          have h_new_sorted : sorted_by_key (acc.val ++ #[v.val[i.toNat]'hi_lt]) := by
            apply sorted_by_key_append_singleton acc.val (v.val[i.toNat]'hi_lt) h_acc_sorted
            intro k hk
            exact h_acc_le_vi k hk hi_lt
          have h_new_le_vi :
              ∀ (k : Nat) (hk : k < (acc.val ++ #[v.val[i.toNat]'hi_lt]).size)
                (hi_i1 : (i + 1).toNat < v.val.size),
                key ((acc.val ++ #[v.val[i.toNat]'hi_lt])[k]'hk) ≤
                  key (v.val[(i + 1).toNat]'hi_i1) := by
            intro k hk hi_i1
            rw [Array.size_append] at hk
            have h_one : (#[v.val[i.toNat]'hi_lt] : Array i64).size = 1 := rfl
            by_cases h_k_lt : k < acc.val.size
            · rw [Array.getElem_append_left h_k_lt]
              have h1 := h_acc_le_vi k h_k_lt hi_lt
              have h2 := h_v_step hi_i1
              exact Int.le_trans h1 h2
            · have h_k_ge : acc.val.size ≤ k := by omega
              rw [Array.getElem_append_right h_k_ge]
              have h_idx : k - acc.val.size = 0 := by omega
              have h_zero_lt : (0 : Nat) < (#[v.val[i.toNat]'hi_lt] : Array i64).size := by
                rw [h_one]; omega
              rw [show ((#[v.val[i.toNat]'hi_lt] : Array i64)[k - acc.val.size]'(by rw [h_idx]; exact h_zero_lt))
                      = (#[v.val[i.toNat]'hi_lt] : Array i64)[0]'h_zero_lt from by simp [h_idx]]
              exact h_v_step hi_i1
          exact ih (i + 1) true _ r h_meas h_i1_le h_nomin_next hres h_new_sorted h_new_le_vi
            (fun h => by cases h)
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_stable_at_step_pass_fail v x kx i true acc hi_lt h_vi_no_min (Or.inl rfl) h_big] at hres
          cases hres
      | false =>
        by_cases h_lt : kx.toInt < key (v.val[i.toNat]'hi_lt)
        · -- Insert branch
          by_cases h_acc : acc.val.size + 2 < USize64.size
          · rw [insert_stable_at_step_insert v x kx i acc hi_lt h_vi_no_min h_lt h_acc] at hres
            -- New acc = acc ++ [x, vi]
            have h_x_le_vi : key x ≤ key (v.val[i.toNat]'hi_lt) := by
              rw [← h_kx]; omega
            have h_p1 : sorted_by_key (acc.val ++ #[x]) := by
              apply sorted_by_key_append_singleton acc.val x h_acc_sorted
              intro k hk
              have : key (acc.val[k]'hk) ≤ kx.toInt := h_acc_le_kx rfl k hk
              rw [h_kx] at this; exact this
            have h_p1_le_vi :
                ∀ (k : Nat) (hk : k < (acc.val ++ #[x]).size),
                  key ((acc.val ++ #[x])[k]'hk) ≤ key (v.val[i.toNat]'hi_lt) := by
              intro k hk
              rw [Array.size_append] at hk
              have h_one : (#[x] : Array i64).size = 1 := rfl
              by_cases h_k_lt : k < acc.val.size
              · rw [Array.getElem_append_left h_k_lt]
                exact h_acc_le_vi k h_k_lt hi_lt
              · have h_k_ge : acc.val.size ≤ k := by omega
                rw [Array.getElem_append_right h_k_ge]
                have h_idx : k - acc.val.size = 0 := by omega
                have h_zero_lt : (0 : Nat) < (#[x] : Array i64).size := by rw [h_one]; omega
                rw [show ((#[x] : Array i64)[k - acc.val.size]'(by rw [h_idx]; exact h_zero_lt))
                        = (#[x] : Array i64)[0]'h_zero_lt from by simp [h_idx]]
                exact h_x_le_vi
            have h_p2_sorted : sorted_by_key ((acc.val ++ #[x]) ++ #[v.val[i.toNat]'hi_lt]) :=
              sorted_by_key_append_singleton _ _ h_p1 h_p1_le_vi
            -- push_two acc x vi = ⟨acc.val ++ #[x, vi], _⟩. And acc++#[x,vi] = (acc++#[x])++#[vi]
            -- They're not definitionally equal; rewrite via array_helper.
            have h_assoc : acc.val ++ #[x, v.val[i.toNat]'hi_lt]
                        = (acc.val ++ #[x]) ++ #[v.val[i.toNat]'hi_lt] := by
              apply Array.ext
              · rw [Array.size_append, Array.size_append, Array.size_append]; rfl
              · intro k h1 h2
                have h_size_eq : (acc.val ++ #[x, v.val[i.toNat]'hi_lt]).size
                              = ((acc.val ++ #[x]) ++ #[v.val[i.toNat]'hi_lt]).size := by
                  rw [Array.size_append, Array.size_append, Array.size_append]; rfl
                have h_acc1_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
                  rw [Array.size_append]; rfl
                have h_xvi_size : (#[x, v.val[i.toNat]'hi_lt] : Array i64).size = 2 := rfl
                by_cases h_k_lt : k < acc.val.size
                · rw [Array.getElem_append_left h_k_lt]
                  have h_k_lt' : k < (acc.val ++ #[x]).size := by rw [h_acc1_size]; omega
                  rw [Array.getElem_append_left h_k_lt']
                  rw [Array.getElem_append_left h_k_lt]
                · have h_k_ge : acc.val.size ≤ k := by omega
                  rw [Array.getElem_append_right h_k_ge]
                  by_cases h_k_eq : k = acc.val.size
                  · subst h_k_eq
                    have h_idx : acc.val.size - acc.val.size = 0 := Nat.sub_self _
                    have h_zero_lt : (0 : Nat) < (#[x, v.val[i.toNat]'hi_lt] : Array i64).size := by
                      rw [h_xvi_size]; omega
                    rw [show ((#[x, v.val[i.toNat]'hi_lt] : Array i64)[acc.val.size - acc.val.size]'(by rw [h_idx]; exact h_zero_lt))
                            = (#[x, v.val[i.toNat]'hi_lt] : Array i64)[0]'h_zero_lt from by simp [h_idx]]
                    have h_k_lt' : acc.val.size < (acc.val ++ #[x]).size := by rw [h_acc1_size]; omega
                    rw [Array.getElem_append_left h_k_lt']
                    rw [Array.getElem_append_right (Nat.le_refl _)]
                    simp
                  · have h_k_gt : acc.val.size + 1 ≤ k := by omega
                    have h_k_eq_1 : k - acc.val.size = 1 := by
                      have h_lt_xvi : k - acc.val.size < (#[x, v.val[i.toNat]'hi_lt] : Array i64).size := by
                        rw [h_xvi_size]; rw [Array.size_append, h_xvi_size] at h1; omega
                      have h_lt_2 : k - acc.val.size < 2 := by rw [← h_xvi_size]; exact h_lt_xvi
                      omega
                    have h_zero_lt_xvi : (1 : Nat) < (#[x, v.val[i.toNat]'hi_lt] : Array i64).size := by
                      rw [h_xvi_size]; omega
                    rw [show ((#[x, v.val[i.toNat]'hi_lt] : Array i64)[k - acc.val.size]'(by rw [h_k_eq_1]; exact h_zero_lt_xvi))
                            = (#[x, v.val[i.toNat]'hi_lt] : Array i64)[1]'h_zero_lt_xvi from by simp [h_k_eq_1]]
                    have h_k_ge_acc1 : (acc.val ++ #[x]).size ≤ k := by rw [h_acc1_size]; omega
                    rw [Array.getElem_append_right h_k_ge_acc1]
                    have h_k_minus : k - (acc.val ++ #[x]).size = 0 := by
                      rw [h_acc1_size]; omega
                    have h_zero_lt_vi : (0 : Nat) < (#[v.val[i.toNat]'hi_lt] : Array i64).size := by
                      show 0 < 1; omega
                    rw [show ((#[v.val[i.toNat]'hi_lt] : Array i64)[k - (acc.val ++ #[x]).size]'(by rw [h_k_minus]; exact h_zero_lt_vi))
                            = (#[v.val[i.toNat]'hi_lt] : Array i64)[0]'h_zero_lt_vi from by simp [h_k_minus]]
                    simp
            have h_new_sorted : sorted_by_key (push_two acc x (v.val[i.toNat]'hi_lt) h_acc).val := by
              show sorted_by_key (acc.val ++ #[x, v.val[i.toNat]'hi_lt])
              rw [h_assoc]; exact h_p2_sorted
            have h_new_le_vi :
                ∀ (k : Nat)
                  (hk : k < (push_two acc x (v.val[i.toNat]'hi_lt) h_acc).val.size)
                  (hi_i1 : (i + 1).toNat < v.val.size),
                  key ((push_two acc x (v.val[i.toNat]'hi_lt) h_acc).val[k]'hk) ≤
                    key (v.val[(i + 1).toNat]'hi_i1) := by
              intro k hk hi_i1
              have h_vi_step := h_v_step hi_i1
              have h_pp_size :
                  (push_two acc x (v.val[i.toNat]'hi_lt) h_acc).val.size = acc.val.size + 2 :=
                push_two_size acc x _ h_acc
              have h_p1_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
                rw [Array.size_append]; rfl
              have h_a2_size : ((acc.val ++ #[x]) ++ #[v.val[i.toNat]'hi_lt]).size = acc.val.size + 2 := by
                rw [Array.size_append, Array.size_append]; rfl
              have h_one : (#[v.val[i.toNat]'hi_lt] : Array i64).size = 1 := rfl
              have h_k_lt' : k < ((acc.val ++ #[x]) ++ #[v.val[i.toNat]'hi_lt]).size := by
                rw [h_a2_size]; rw [h_pp_size] at hk; exact hk
              -- Use the array equality to transport the element access.
              have h_get_eq :
                  (push_two acc x (v.val[i.toNat]'hi_lt) h_acc).val[k]'hk
                    = ((acc.val ++ #[x]) ++ #[v.val[i.toNat]'hi_lt])[k]'h_k_lt' := by
                show (acc.val ++ #[x, v.val[i.toNat]'hi_lt])[k]'hk = _
                congr 1
              rw [h_get_eq]
              by_cases h_k_lt : k < (acc.val ++ #[x]).size
              · rw [Array.getElem_append_left h_k_lt]
                exact Int.le_trans (h_p1_le_vi k h_k_lt) h_vi_step
              · have h_k_ge : (acc.val ++ #[x]).size ≤ k := by omega
                rw [Array.getElem_append_right h_k_ge]
                have h_idx : k - (acc.val ++ #[x]).size = 0 := by
                  rw [h_p1_size]
                  rw [h_pp_size] at hk; omega
                have h_zero_lt : (0 : Nat) < (#[v.val[i.toNat]'hi_lt] : Array i64).size := by
                  rw [h_one]; omega
                rw [show ((#[v.val[i.toNat]'hi_lt] : Array i64)[k - (acc.val ++ #[x]).size]'(by rw [h_idx]; exact h_zero_lt))
                        = (#[v.val[i.toNat]'hi_lt] : Array i64)[0]'h_zero_lt from by simp [h_idx]]
                exact h_vi_step
            exact ih (i + 1) true _ r h_meas h_i1_le h_nomin_next hres h_new_sorted h_new_le_vi
              (fun h => by cases h)
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 2 := by omega
            rw [insert_stable_at_step_insert_fail v x kx i acc hi_lt h_vi_no_min h_lt h_big] at hres
            cases hres
        · -- Pass branch (done=false, key(vi) ≤ kx.toInt)
          have h_le : key (v.val[i.toNat]'hi_lt) ≤ kx.toInt := by
            simp only [key] at h_lt ⊢
            omega
          by_cases h_acc : acc.val.size + 1 < USize64.size
          · rw [insert_stable_at_step_pass v x kx i false acc hi_lt h_vi_no_min (Or.inr h_le) h_acc] at hres
            have h_new_sorted : sorted_by_key (acc.val ++ #[v.val[i.toNat]'hi_lt]) := by
              apply sorted_by_key_append_singleton acc.val (v.val[i.toNat]'hi_lt) h_acc_sorted
              intro k hk
              exact h_acc_le_vi k hk hi_lt
            have h_new_le_vi :
                ∀ (k : Nat) (hk : k < (acc.val ++ #[v.val[i.toNat]'hi_lt]).size)
                  (hi_i1 : (i + 1).toNat < v.val.size),
                  key ((acc.val ++ #[v.val[i.toNat]'hi_lt])[k]'hk) ≤
                    key (v.val[(i + 1).toNat]'hi_i1) := by
              intro k hk hi_i1
              rw [Array.size_append] at hk
              have h_one : (#[v.val[i.toNat]'hi_lt] : Array i64).size = 1 := rfl
              have h_vi_step := h_v_step hi_i1
              by_cases h_k_lt : k < acc.val.size
              · rw [Array.getElem_append_left h_k_lt]
                exact Int.le_trans (h_acc_le_vi k h_k_lt hi_lt) h_vi_step
              · have h_k_ge : acc.val.size ≤ k := by omega
                rw [Array.getElem_append_right h_k_ge]
                have h_idx : k - acc.val.size = 0 := by omega
                have h_zero_lt : (0 : Nat) < (#[v.val[i.toNat]'hi_lt] : Array i64).size := by
                  rw [h_one]; omega
                rw [show ((#[v.val[i.toNat]'hi_lt] : Array i64)[k - acc.val.size]'(by rw [h_idx]; exact h_zero_lt))
                        = (#[v.val[i.toNat]'hi_lt] : Array i64)[0]'h_zero_lt from by simp [h_idx]]
                exact h_vi_step
            have h_new_le_kx : false = false →
                ∀ (k : Nat) (hk : k < (acc.val ++ #[v.val[i.toNat]'hi_lt]).size),
                  key ((acc.val ++ #[v.val[i.toNat]'hi_lt])[k]'hk) ≤ kx.toInt := by
              intro _ k hk
              rw [Array.size_append] at hk
              have h_one : (#[v.val[i.toNat]'hi_lt] : Array i64).size = 1 := rfl
              by_cases h_k_lt : k < acc.val.size
              · rw [Array.getElem_append_left h_k_lt]
                exact h_acc_le_kx rfl k h_k_lt
              · have h_k_ge : acc.val.size ≤ k := by omega
                rw [Array.getElem_append_right h_k_ge]
                have h_idx : k - acc.val.size = 0 := by omega
                have h_zero_lt : (0 : Nat) < (#[v.val[i.toNat]'hi_lt] : Array i64).size := by
                  rw [h_one]; omega
                rw [show ((#[v.val[i.toNat]'hi_lt] : Array i64)[k - acc.val.size]'(by rw [h_idx]; exact h_zero_lt))
                        = (#[v.val[i.toNat]'hi_lt] : Array i64)[0]'h_zero_lt from by simp [h_idx]]
                exact h_le
            exact ih (i + 1) false _ r h_meas h_i1_le h_nomin_next hres h_new_sorted h_new_le_vi h_new_le_kx
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 1 := by omega
            rw [insert_stable_at_step_pass_fail v x kx i false acc hi_lt h_vi_no_min (Or.inr h_le) h_big] at hres
            cases hres

/-! ## `insert_stable` wrappers. -/

private theorem insert_stable_inv
    (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h_x_no_min : x ≠ Int64.minValue)
    (h_v_no_min : ∀ (k : Nat) (h : k < v.val.size), v.val[k]'h ≠ Int64.minValue)
    (r : alloc.vec.Vec i64 alloc.alloc.Global) (target : i64)
    (hres : clever_143_order_by_points.insert_stable v x = RustM.ok r) :
    r.val.size = v.val.size + 1 ∧
    vec_count r.val target r.val.size =
      vec_count v.val target v.val.size + (if x = target then 1 else 0) := by
  unfold clever_143_order_by_points.insert_stable at hres
  obtain ⟨kx, h_kx_eq, h_kx_int⟩ := signed_digit_sum_correct x h_x_no_min
  rw [h_kx_eq] at hres
  simp only [RustM_ok_bind] at hres
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_meas : v.val.size - (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  have h_le : (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  have h_nomin_zero : ∀ (k : Nat) (h : k < v.val.size), (0 : usize).toNat ≤ k → v.val[k]'h ≠ Int64.minValue := by
    intro k h _; exact h_v_no_min k h
  have inv := insert_stable_at_inv v.val.size v x kx (0 : usize) false
    ⟨(List.nil).toArray, by grind⟩ r target h_meas h_le h_nomin_zero hres
  obtain ⟨h_size_eq, h_count_eq⟩ := inv
  have h_empty_size : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
  rw [h_empty_size, h_zero_toNat] at h_size_eq
  rw [h_empty_size, h_zero_toNat] at h_count_eq
  have h_empty_count : vec_count ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val target 0 = 0 := rfl
  refine ⟨?_, ?_⟩
  · rw [h_size_eq]; simp
  · rw [h_empty_count] at h_count_eq
    have h_total_zero : vec_count v.val target 0 = 0 := rfl
    rw [h_total_zero] at h_count_eq
    simp at h_count_eq
    omega

private theorem insert_stable_sorted
    (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h_x_no_min : x ≠ Int64.minValue)
    (h_v_no_min : ∀ (k : Nat) (h : k < v.val.size), v.val[k]'h ≠ Int64.minValue)
    (r : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_143_order_by_points.insert_stable v x = RustM.ok r)
    (h_v_sorted : sorted_by_key v.val) :
    sorted_by_key r.val := by
  unfold clever_143_order_by_points.insert_stable at hres
  obtain ⟨kx, h_kx_eq, h_kx_int⟩ := signed_digit_sum_correct x h_x_no_min
  rw [h_kx_eq] at hres
  simp only [RustM_ok_bind] at hres
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_meas : v.val.size - (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  have h_le : (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  have h_nomin_zero : ∀ (k : Nat) (h : k < v.val.size), (0 : usize).toNat ≤ k → v.val[k]'h ≠ Int64.minValue := by
    intro k h _; exact h_v_no_min k h
  have h_empty_sorted : sorted_by_key ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val := by
    intro k₁ k₂ h₁ _ _
    have : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  have h_empty_le_vi :
      ∀ (k : Nat) (hk : k < ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size)
        (_ : (0 : usize).toNat < v.val.size),
      key (((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val[k]'hk)
        ≤ key (v.val[(0 : usize).toNat]'(by assumption)) := by
    intro k hk _
    have h_empty : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  have h_empty_le_kx : false = false →
      ∀ (k : Nat) (hk : k < ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size),
      key (((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val[k]'hk) ≤ kx.toInt := by
    intro _ k hk
    have h_empty : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  exact insert_stable_at_sorted v x kx h_v_sorted h_kx_int v.val.size (0 : usize) false
    ⟨(List.nil).toArray, by grind⟩ r h_meas h_le h_nomin_zero hres h_empty_sorted h_empty_le_vi h_empty_le_kx

/-! ## Lemma: insert_stable preserves the "no-minValue" predicate on entries. -/

private theorem insert_stable_no_min
    (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h_x_no_min : x ≠ Int64.minValue)
    (h_v_no_min : ∀ (k : Nat) (h : k < v.val.size), v.val[k]'h ≠ Int64.minValue)
    (r : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_143_order_by_points.insert_stable v x = RustM.ok r) :
    ∀ (k : Nat) (h : k < r.val.size), r.val[k]'h ≠ Int64.minValue := by
  -- vec_count r minValue r.size = vec_count v minValue v.size + (x = minValue ? 1 : 0)
  -- Since x ≠ minValue, no contribution from x. Since all v[k] ≠ minValue, count = 0.
  -- Then no r[k] = minValue.
  have h_inv := insert_stable_inv v x h_x_no_min h_v_no_min r Int64.minValue hres
  have h_x_dec : (if x = Int64.minValue then 1 else 0) = 0 := by
    rw [if_neg h_x_no_min]
  have h_v_count : vec_count v.val Int64.minValue v.val.size = 0 := by
    -- prove by induction over k that vec_count v minValue k = 0
    have : ∀ k, k ≤ v.val.size → vec_count v.val Int64.minValue k = 0 := by
      intro k hk
      induction k with
      | zero => rfl
      | succ k ih =>
        have hk_lt : k < v.val.size := by omega
        rw [vec_count_succ v.val Int64.minValue k hk_lt]
        rw [if_neg (h_v_no_min k hk_lt)]
        simp [ih (Nat.le_of_lt hk)]
    exact this v.val.size (Nat.le_refl _)
  have h_r_count : vec_count r.val Int64.minValue r.val.size = 0 := by
    have h_eq := h_inv.2
    rw [h_v_count, h_x_dec] at h_eq
    omega
  -- Now derive r.val[k] ≠ minValue from r_count = 0
  intro k h
  intro h_eq
  -- Build a contradiction: vec_count r minValue (k+1) ≥ 1, but vec_count r minValue r.size = 0
  -- needs monotonicity of vec_count.
  have h_count_succ := vec_count_succ r.val Int64.minValue k h
  rw [if_pos h_eq] at h_count_succ
  have h_mono : ∀ k₁ k₂, k₁ ≤ k₂ → k₂ ≤ r.val.size →
      vec_count r.val Int64.minValue k₁ ≤ vec_count r.val Int64.minValue k₂ := by
    intro k₁ k₂ hle hk₂
    induction k₂ with
    | zero => have : k₁ = 0 := by omega
              rw [this]; exact Nat.le_refl _
    | succ k₂ ih =>
      by_cases hk₂_eq : k₁ ≤ k₂
      · have h_step : vec_count r.val Int64.minValue (k₂ + 1) ≥ vec_count r.val Int64.minValue k₂ := by
          by_cases hk : k₂ < r.val.size
          · rw [vec_count_succ r.val Int64.minValue k₂ hk]
            split <;> omega
          · show (if h : k₂ < r.val.size then
                    (if (r.val[k₂]'h) = Int64.minValue then 1 else 0) + vec_count r.val Int64.minValue k₂
                  else vec_count r.val Int64.minValue k₂) ≥ _
            rw [dif_neg hk]; exact Nat.le_refl _
        have ih' := ih hk₂_eq (Nat.le_of_lt hk₂)
        omega
      · have : k₁ = k₂ + 1 := by omega
        rw [this]; exact Nat.le_refl _
  have h_le_total := h_mono (k + 1) r.val.size (by omega) (Nat.le_refl _)
  omega

/-! ## `sort_at` OOB / step lemmas. -/

private theorem sort_at_oob (l : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : l.val.size ≤ i.toNat) :
    clever_143_order_by_points.sort_at l i acc = RustM.ok acc := by
  unfold clever_143_order_by_points.sort_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

private theorem sort_at_step (l : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < l.val.size) :
    clever_143_order_by_points.sort_at l i acc =
      (do
        let acc' ← clever_143_order_by_points.insert_stable acc (l.val[i.toNat]'hi)
        clever_143_order_by_points.sort_at l (i + 1) acc') := by
  conv => lhs; unfold clever_143_order_by_points.sort_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_add : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := usize_add_one_ok i h_no_ov_i
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx]
  rw [h_add]
  simp only [RustM_ok_bind]

/-! ## `sort_at` invariants (size, vec_count, sortedness). -/

private theorem sort_at_inv :
    ∀ (n : Nat) (l : RustSlice i64) (i : usize)
      (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global) (target : i64),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      (∀ (k : Nat) (h : k < l.val.size), l.val[k]'h ≠ Int64.minValue) →
      (∀ (k : Nat) (h : k < acc.val.size), acc.val[k]'h ≠ Int64.minValue) →
      clever_143_order_by_points.sort_at l i acc = RustM.ok r →
      r.val.size = acc.val.size + (l.val.size - i.toNat) ∧
      vec_count r.val target r.val.size + vec_count l.val target i.toNat =
        vec_count acc.val target acc.val.size + vec_count l.val target l.val.size := by
  intro n
  induction n with
  | zero =>
    intro l i acc r target hm hi_le h_l_nomin h_acc_nomin hres
    have hi_ge : l.val.size ≤ i.toNat := by omega
    have hi_eq : i.toNat = l.val.size := by omega
    rw [sort_at_oob l i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    refine ⟨?_, ?_⟩
    · rw [hi_eq]; omega
    · rw [hi_eq]
  | succ n ih =>
    intro l i acc r target hm hi_le h_l_nomin h_acc_nomin hres
    by_cases hi_ge : l.val.size ≤ i.toNat
    · have hi_eq : i.toNat = l.val.size := by omega
      rw [sort_at_oob l i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      refine ⟨?_, ?_⟩
      · rw [hi_eq]; omega
      · rw [hi_eq]
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_meas : l.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      have h_vec_succ_l :
          vec_count l.val target (i.toNat + 1) =
            (if l.val[i.toNat]'hi_lt = target then 1 else 0) + vec_count l.val target i.toNat :=
        vec_count_succ l.val target i.toNat hi_lt
      rw [sort_at_step l i acc hi_lt] at hres
      generalize h_ins : clever_143_order_by_points.insert_stable acc (l.val[i.toNat]'hi_lt) = ins_res at hres
      cases ins_res with
      | none =>
        exfalso
        have hh : (do let acc' ← (none : RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                       clever_143_order_by_points.sort_at l (i + 1) acc')
                  = RustM.ok r := hres
        cases hh
      | some res' =>
        cases res' with
        | error e =>
          exfalso
          have hh : (do let acc' ← (some (Except.error e) :
                                      RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                         clever_143_order_by_points.sort_at l (i + 1) acc')
                    = RustM.ok r := hres
          cases hh
        | ok acc' =>
          have h_ins_ok : clever_143_order_by_points.insert_stable acc (l.val[i.toNat]'hi_lt) = RustM.ok acc' := h_ins
          simp only [RustM_ok_bind] at hres
          have h_l_no_min : l.val[i.toNat]'hi_lt ≠ Int64.minValue := h_l_nomin i.toNat hi_lt
          have h_acc'_nomin : ∀ (k : Nat) (h : k < acc'.val.size), acc'.val[k]'h ≠ Int64.minValue :=
            insert_stable_no_min acc (l.val[i.toNat]'hi_lt) h_l_no_min h_acc_nomin acc' h_ins_ok
          have h_ins_inv := insert_stable_inv acc (l.val[i.toNat]'hi_lt) h_l_no_min h_acc_nomin acc' target h_ins_ok
          obtain ⟨h_acc'_size, h_acc'_count⟩ := h_ins_inv
          have ih_app := ih l (i + 1) acc' r target h_meas h_i1_le h_l_nomin h_acc'_nomin hres
          rw [h_i1] at ih_app
          obtain ⟨h_size_eq, h_count_eq⟩ := ih_app
          rw [h_acc'_size] at h_size_eq
          rw [h_acc'_count] at h_count_eq
          rw [h_vec_succ_l] at h_count_eq
          refine ⟨?_, ?_⟩
          · rw [h_size_eq]; omega
          · omega

private theorem sort_at_sorted :
    ∀ (n : Nat) (l : RustSlice i64)
      (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      (∀ (k : Nat) (h : k < l.val.size), l.val[k]'h ≠ Int64.minValue) →
      (∀ (k : Nat) (h : k < acc.val.size), acc.val[k]'h ≠ Int64.minValue) →
      clever_143_order_by_points.sort_at l i acc = RustM.ok r →
      sorted_by_key acc.val →
      sorted_by_key r.val := by
  intro n
  induction n with
  | zero =>
    intro l i acc r hm hi_le h_l_nomin h_acc_nomin hres h_acc_sorted
    have hi_ge : l.val.size ≤ i.toNat := by omega
    rw [sort_at_oob l i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    exact h_acc_sorted
  | succ n ih =>
    intro l i acc r hm hi_le h_l_nomin h_acc_nomin hres h_acc_sorted
    by_cases hi_ge : l.val.size ≤ i.toNat
    · rw [sort_at_oob l i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      exact h_acc_sorted
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_meas : l.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      rw [sort_at_step l i acc hi_lt] at hres
      generalize h_ins : clever_143_order_by_points.insert_stable acc (l.val[i.toNat]'hi_lt) = ins_res at hres
      cases ins_res with
      | none =>
        exfalso
        have hh : (do let acc' ← (none : RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                       clever_143_order_by_points.sort_at l (i + 1) acc')
                  = RustM.ok r := hres
        cases hh
      | some res' =>
        cases res' with
        | error e =>
          exfalso
          have hh : (do let acc' ← (some (Except.error e) :
                                      RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                         clever_143_order_by_points.sort_at l (i + 1) acc')
                    = RustM.ok r := hres
          cases hh
        | ok acc' =>
          have h_ins_ok : clever_143_order_by_points.insert_stable acc (l.val[i.toNat]'hi_lt) = RustM.ok acc' := h_ins
          simp only [RustM_ok_bind] at hres
          have h_l_no_min : l.val[i.toNat]'hi_lt ≠ Int64.minValue := h_l_nomin i.toNat hi_lt
          have h_acc'_nomin : ∀ (k : Nat) (h : k < acc'.val.size), acc'.val[k]'h ≠ Int64.minValue :=
            insert_stable_no_min acc (l.val[i.toNat]'hi_lt) h_l_no_min h_acc_nomin acc' h_ins_ok
          have h_acc'_sorted : sorted_by_key acc'.val :=
            insert_stable_sorted acc (l.val[i.toNat]'hi_lt) h_l_no_min h_acc_nomin acc' h_ins_ok h_acc_sorted
          exact ih l (i + 1) acc' r h_meas h_i1_le h_l_nomin h_acc'_nomin hres h_acc'_sorted

/-! ## Deriving the no-minValue precondition from `order_by_points` success. -/

private theorem sort_at_no_min_input :
    ∀ (n : Nat) (l : RustSlice i64) (i : usize)
      (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      (∀ (k : Nat) (h : k < acc.val.size), acc.val[k]'h ≠ Int64.minValue) →
      clever_143_order_by_points.sort_at l i acc = RustM.ok r →
      ∀ (k : Nat) (h : k < l.val.size), i.toNat ≤ k → l.val[k]'h ≠ Int64.minValue := by
  intro n
  induction n with
  | zero =>
    intro l i acc r hm hi_le h_acc_nomin hres
    intro k hk hi_k
    have hi_ge : l.val.size ≤ i.toNat := by omega
    omega
  | succ n ih =>
    intro l i acc r hm hi_le h_acc_nomin hres
    intro k hk hi_k
    by_cases hi_ge : l.val.size ≤ i.toNat
    · omega
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_meas : l.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      rw [sort_at_step l i acc hi_lt] at hres
      generalize h_ins : clever_143_order_by_points.insert_stable acc (l.val[i.toNat]'hi_lt) = ins_res at hres
      cases ins_res with
      | none =>
        exfalso
        have hh : (do let acc' ← (none : RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                       clever_143_order_by_points.sort_at l (i + 1) acc')
                  = RustM.ok r := hres
        cases hh
      | some res' =>
        cases res' with
        | error e =>
          exfalso
          have hh : (do let acc' ← (some (Except.error e) :
                                      RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                         clever_143_order_by_points.sort_at l (i + 1) acc')
                    = RustM.ok r := hres
          cases hh
        | ok acc' =>
          have h_ins_ok : clever_143_order_by_points.insert_stable acc (l.val[i.toNat]'hi_lt) = RustM.ok acc' := h_ins
          -- From insert_stable success we get l[i.toNat] ≠ minValue (else signed_digit_sum fails)
          have h_l_i_no_min : l.val[i.toNat]'hi_lt ≠ Int64.minValue := by
            intro h_eq
            -- insert_stable unfolds to: signed_digit_sum vi >>= ...
            -- If vi = minValue, signed_digit_sum fails. Contradiction.
            unfold clever_143_order_by_points.insert_stable at h_ins_ok
            rw [h_eq] at h_ins_ok
            -- signed_digit_sum minValue = ?
            unfold clever_143_order_by_points.signed_digit_sum at h_ins_ok
            have h_min_ne_zero : (Int64.minValue : i64) ≠ (0 : i64) := by decide
            have h_beq : ((Int64.minValue : i64) == (0 : i64)) = false := by
              show decide ((Int64.minValue : i64) = (0 : i64)) = false
              exact decide_eq_false h_min_ne_zero
            simp only [show ((Int64.minValue : i64) ==? (0 : i64) : RustM Bool) =
                         (pure ((Int64.minValue : i64) == (0 : i64))) from rfl,
                       h_beq, pure_bind, Bool.false_eq_true, ↓reduceIte] at h_ins_ok
            have h_gt : (Int64.minValue > (0 : i64)) = false := by decide
            have h_gt_dec : decide ((0 : i64) < Int64.minValue) = false := by
              show decide ((0 : i64) < Int64.minValue) = false
              exact decide_eq_false (by decide)
            simp only [show ((Int64.minValue : i64) >? (0 : i64) : RustM Bool) =
                         (pure (decide ((0 : i64) < Int64.minValue)) : RustM Bool) from rfl,
                       h_gt_dec, pure_bind, Bool.false_eq_true, ↓reduceIte] at h_ins_ok
            -- Now negation step:  -? minValue fails
            have h_neg_fail : ((-? (Int64.minValue : i64)) : RustM i64) = RustM.fail .integerOverflow := by
              show (rust_primitives.ops.arith.Neg.neg (Int64.minValue : i64) : RustM i64) = _
              show (if (Int64.minValue : i64) = Int64.minValue then (.fail .integerOverflow : RustM i64)
                    else pure (- (Int64.minValue : i64))) = _
              rw [if_pos rfl]
            rw [h_neg_fail] at h_ins_ok
            cases h_ins_ok
          -- Now: if k = i.toNat, we have the result. Else k > i.toNat, use IH.
          have h_acc'_nomin : ∀ (k : Nat) (h : k < acc'.val.size), acc'.val[k]'h ≠ Int64.minValue :=
            insert_stable_no_min acc (l.val[i.toNat]'hi_lt) h_l_i_no_min h_acc_nomin acc' h_ins_ok
          simp only [RustM_ok_bind] at hres
          by_cases h_k_eq : k = i.toNat
          · subst h_k_eq; exact h_l_i_no_min
          · have h_k_ge : (i + 1).toNat ≤ k := by rw [h_i1]; omega
            exact ih l (i + 1) acc' r h_meas h_i1_le h_acc'_nomin hres k hk h_k_ge

/-! ## Stability machinery. -/

/-- Subsequence of `s[lo..lo+n)` with key `k`, in forward order.
    Head-first definition: peels off the first element. -/
private def filter_seg (s : Array i64) (k : Int) (lo : Nat) : Nat → Array i64
  | 0 => #[]
  | n + 1 =>
      if h : lo < s.size then
        if signed_digit_sum_int (s[lo]'h).toInt = k then
          #[s[lo]'h] ++ filter_seg s k (lo + 1) n
        else
          filter_seg s k (lo + 1) n
      else #[]

private theorem filter_seg_oob (s : Array i64) (k : Int) (lo : Nat) :
    ∀ n, s.size ≤ lo → filter_seg s k lo n = #[] := by
  intro n h_oob
  induction n generalizing lo with
  | zero => rfl
  | succ n ih =>
    show (if h : lo < s.size then _ else #[]) = #[]
    rw [dif_neg (by omega : ¬ lo < s.size)]

/-- Helper: at any specific n, filter_seg unfolds as head-first. -/
private theorem filter_seg_succ_lo_lt (s : Array i64) (k : Int) (lo n : Nat)
    (h_lo : lo < s.size) :
    filter_seg s k lo (n + 1) =
      (if signed_digit_sum_int (s[lo]'h_lo).toInt = k then #[s[lo]'h_lo] else #[])
        ++ filter_seg s k (lo + 1) n := by
  show (if h : lo < s.size then
          if signed_digit_sum_int (s[lo]'h).toInt = k then
            #[s[lo]'h] ++ filter_seg s k (lo + 1) n
          else filter_seg s k (lo + 1) n
        else #[]) = _
  rw [dif_pos h_lo]
  by_cases h_key : signed_digit_sum_int (s[lo]'h_lo).toInt = k
  · rw [if_pos h_key, if_pos h_key]
  · rw [if_neg h_key, if_neg h_key]; simp

private theorem filter_seg_succ_lo_ge (s : Array i64) (k : Int) (lo n : Nat)
    (h_lo : ¬ lo < s.size) :
    filter_seg s k lo (n + 1) = #[] := by
  show (if h : lo < s.size then _ else #[]) = #[]
  rw [dif_neg h_lo]

/-- Splitting off the last element (tail-first equation) from a forward filter. -/
private theorem filter_seg_snoc (s : Array i64) (k : Int) :
    ∀ (lo n : Nat),
      filter_seg s k lo (n + 1) =
        filter_seg s k lo n ++
          (if h : lo + n < s.size then
             (if signed_digit_sum_int (s[lo + n]'h).toInt = k then #[s[lo + n]'h] else #[])
           else #[]) := by
  intro lo n
  induction n generalizing lo with
  | zero =>
    by_cases h_lo : lo < s.size
    · rw [filter_seg_succ_lo_lt s k lo 0 h_lo]
      have h_lo' : lo + 0 < s.size := by rw [Nat.add_zero]; exact h_lo
      have h_idx : s[lo + 0]'h_lo' = s[lo]'h_lo := by congr 1
      show (if signed_digit_sum_int (s[lo]'h_lo).toInt = k then #[s[lo]'h_lo] else #[]) ++ #[] =
            #[] ++ (if h : lo + 0 < s.size then
                       (if signed_digit_sum_int (s[lo + 0]'h).toInt = k then #[s[lo + 0]'h] else #[])
                    else #[])
      rw [dif_pos h_lo', h_idx]
      simp
    · rw [filter_seg_succ_lo_ge s k lo 0 h_lo]
      have h_lo' : ¬ lo + 0 < s.size := by rw [Nat.add_zero]; exact h_lo
      show #[] = #[] ++ (if h : lo + 0 < s.size then
                          (if signed_digit_sum_int (s[lo + 0]'h).toInt = k then #[s[lo + 0]'h] else #[])
                        else #[])
      rw [dif_neg h_lo']; simp
  | succ n ih =>
    by_cases h_lo : lo < s.size
    · rw [filter_seg_succ_lo_lt s k lo (n + 1) h_lo]
      rw [filter_seg_succ_lo_lt s k lo n h_lo]
      rw [ih (lo + 1)]
      rw [Array.append_assoc]
      congr 1
      by_cases h_idx : lo + 1 + n < s.size
      · have h_idx' : lo + (n + 1) < s.size := by omega
        rw [dif_pos h_idx, dif_pos h_idx']
        have h_idx_get : s[lo + 1 + n]'h_idx = s[lo + (n + 1)]'h_idx' := by congr 1; omega
        rw [h_idx_get]
      · have h_idx' : ¬ lo + (n + 1) < s.size := by omega
        rw [dif_neg h_idx, dif_neg h_idx']
    · rw [filter_seg_succ_lo_ge s k lo (n + 1) h_lo]
      rw [filter_seg_succ_lo_ge s k lo n h_lo]
      have h_idx' : ¬ lo + (n + 1) < s.size := by omega
      show #[] = #[] ++ _
      rw [dif_neg h_idx']; simp

/-- Connection of `filter_seg` to `filter_by_key`. -/
private theorem filter_seg_zero_eq_filter_by_key (s : Array i64) (k : Int) :
    ∀ n, filter_seg s k 0 n = filter_by_key s k n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [filter_seg_snoc s k 0 n, ih]
    show filter_by_key s k n ++ (if h : 0 + n < s.size then
                                   (if signed_digit_sum_int (s[0 + n]'h).toInt = k then #[s[0 + n]'h] else #[])
                                 else #[]) =
         filter_by_key s k (n + 1)
    show _ = (if h : n < s.size then
                let rest := filter_by_key s k n
                if signed_digit_sum_int (s[n]'h).toInt = k then rest.push (s[n]'h)
                else rest
              else filter_by_key s k n)
    by_cases h_lt : n < s.size
    · have h_lt' : 0 + n < s.size := by rw [Nat.zero_add]; exact h_lt
      rw [dif_pos h_lt', dif_pos h_lt]
      have h_idx : s[0 + n]'h_lt' = s[n]'h_lt := by congr 1; omega
      rw [h_idx]
      by_cases h_key : signed_digit_sum_int (s[n]'h_lt).toInt = k
      · rw [if_pos h_key, if_pos h_key]
        show filter_by_key s k n ++ #[s[n]'h_lt] = (filter_by_key s k n).push (s[n]'h_lt)
        simp
      · rw [if_neg h_key, if_neg h_key]; simp
    · have h_lt' : ¬ 0 + n < s.size := by rw [Nat.zero_add]; exact h_lt
      rw [dif_neg h_lt', dif_neg h_lt]
      simp

/-! ## filter_by_key for append (singleton/pair) and prefix. -/

private theorem filter_by_key_prefix (acc : Array i64) (ys : Array i64) (k : Int) :
    ∀ n, n ≤ acc.size →
      filter_by_key (acc ++ ys) k n = filter_by_key acc k n := by
  have h_size_app : (acc ++ ys).size = acc.size + ys.size := by
    rw [Array.size_append]
  intro n h_le
  induction n with
  | zero => rfl
  | succ n ih =>
    have h_n_lt : n < acc.size := by omega
    have h_n_lt_app : n < (acc ++ ys).size := by rw [h_size_app]; omega
    have h_get : (acc ++ ys)[n]'h_n_lt_app = acc[n]'h_n_lt :=
      Array.getElem_append_left h_n_lt
    show (if h : n < (acc ++ ys).size then
            let rest := filter_by_key (acc ++ ys) k n
            if signed_digit_sum_int ((acc ++ ys)[n]'h).toInt = k then rest.push ((acc ++ ys)[n]'h)
            else rest
          else filter_by_key (acc ++ ys) k n) =
         (if h : n < acc.size then
            let rest := filter_by_key acc k n
            if signed_digit_sum_int (acc[n]'h).toInt = k then rest.push (acc[n]'h)
            else rest
          else filter_by_key acc k n)
    rw [dif_pos h_n_lt_app, dif_pos h_n_lt, h_get, ih (Nat.le_of_lt h_le)]

private theorem filter_by_key_append_singleton (acc : Array i64) (y : i64) (k : Int) :
    filter_by_key (acc ++ #[y]) k (acc.size + 1) =
      filter_by_key acc k acc.size ++
        (if signed_digit_sum_int y.toInt = k then #[y] else #[]) := by
  have h_size_app : (acc ++ #[y]).size = acc.size + 1 := by
    rw [Array.size_append]; rfl
  have h_lt : acc.size < (acc ++ #[y]).size := by rw [h_size_app]; omega
  have h_get : (acc ++ #[y])[acc.size]'h_lt = y := by
    rw [Array.getElem_append_right (Nat.le_refl _)]
    simp
  show (if h : acc.size < (acc ++ #[y]).size then
          let rest := filter_by_key (acc ++ #[y]) k acc.size
          if signed_digit_sum_int ((acc ++ #[y])[acc.size]'h).toInt = k then rest.push ((acc ++ #[y])[acc.size]'h)
          else rest
        else filter_by_key (acc ++ #[y]) k acc.size) = _
  rw [dif_pos h_lt, h_get]
  rw [filter_by_key_prefix acc #[y] k acc.size (Nat.le_refl _)]
  by_cases h_key : signed_digit_sum_int y.toInt = k
  · rw [if_pos h_key, if_pos h_key]; simp
  · rw [if_neg h_key, if_neg h_key]; simp

private theorem filter_by_key_append_pair (acc : Array i64) (x y : i64) (k : Int) :
    filter_by_key (acc ++ #[x, y]) k (acc.size + 2) =
      filter_by_key acc k acc.size ++
        (if signed_digit_sum_int x.toInt = k then #[x] else #[]) ++
        (if signed_digit_sum_int y.toInt = k then #[y] else #[]) := by
  have h_size_app : (acc ++ #[x, y]).size = acc.size + 2 := by
    rw [Array.size_append]; rfl
  have h_lt_y : acc.size + 1 < (acc ++ #[x, y]).size := by rw [h_size_app]; omega
  have h_lt_x : acc.size < (acc ++ #[x, y]).size := by rw [h_size_app]; omega
  have h_get_y : (acc ++ #[x, y])[acc.size + 1]'h_lt_y = y := by
    rw [Array.getElem_append_right (by omega : acc.size ≤ acc.size + 1)]
    have h_idx : acc.size + 1 - acc.size = 1 := by omega
    simp [h_idx]
  have h_get_x : (acc ++ #[x, y])[acc.size]'h_lt_x = x := by
    rw [Array.getElem_append_right (Nat.le_refl _)]
    simp
  show (if h : acc.size + 1 < (acc ++ #[x, y]).size then
          let rest := filter_by_key (acc ++ #[x, y]) k (acc.size + 1)
          if signed_digit_sum_int ((acc ++ #[x, y])[acc.size + 1]'h).toInt = k then rest.push ((acc ++ #[x, y])[acc.size + 1]'h)
          else rest
        else filter_by_key (acc ++ #[x, y]) k (acc.size + 1)) = _
  rw [dif_pos h_lt_y, h_get_y]
  show (let rest := if h : acc.size < (acc ++ #[x, y]).size then
                       let rest' := filter_by_key (acc ++ #[x, y]) k acc.size
                       if signed_digit_sum_int ((acc ++ #[x, y])[acc.size]'h).toInt = k then rest'.push ((acc ++ #[x, y])[acc.size]'h)
                       else rest'
                     else filter_by_key (acc ++ #[x, y]) k acc.size
        if signed_digit_sum_int y.toInt = k then rest.push y else rest) = _
  rw [dif_pos h_lt_x, h_get_x]
  rw [filter_by_key_prefix acc #[x, y] k acc.size (Nat.le_refl _)]
  by_cases h_x : signed_digit_sum_int x.toInt = k
  · by_cases h_y : signed_digit_sum_int y.toInt = k
    · rw [if_pos h_x, if_pos h_y, if_pos h_x, if_pos h_y]
      simp
    · rw [if_pos h_x, if_neg h_y, if_pos h_x, if_neg h_y]
      simp
  · by_cases h_y : signed_digit_sum_int y.toInt = k
    · rw [if_neg h_x, if_pos h_y, if_neg h_x, if_pos h_y]
      simp
    · rw [if_neg h_x, if_neg h_y, if_neg h_x, if_neg h_y]
      simp

/-! ## Sortedness consequences for the segment. -/

/-- If `v` is sorted by key, `v[i].key > kx`, and all `v[j]` are within the
    sorted range, then no `v[j]` with `j ∈ [i, v.size)` has key = kx — so
    `filter_seg v kx i (v.size - i) = #[]`. -/
private theorem filter_seg_empty_when_gt
    (v : Array i64) (kx : Int) (i : Nat)
    (h_i_lt : i < v.size)
    (h_v_sorted : sorted_by_key v)
    (h_v_i_gt : kx < key (v[i]'h_i_lt)) :
    ∀ n, filter_seg v kx i n = #[] := by
  intro n
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    show (if h : i < v.size then
            if signed_digit_sum_int (v[i]'h).toInt = kx then
              #[v[i]'h] ++ filter_seg v kx (i + 1) n
            else filter_seg v kx (i + 1) n
          else #[]) = #[]
    rw [dif_pos h_i_lt]
    have h_key_ne : signed_digit_sum_int (v[i]'h_i_lt).toInt ≠ kx := by
      have : key (v[i]'h_i_lt) > kx := h_v_i_gt
      simp only [key] at this
      omega
    rw [if_neg h_key_ne]
    by_cases h_i1_lt : i + 1 < v.size
    · have h_step : key (v[i]'h_i_lt) ≤ key (v[i + 1]'h_i1_lt) :=
        h_v_sorted i (i + 1) h_i_lt h_i1_lt (by omega)
      have h_v_i1_gt : kx < key (v[i + 1]'h_i1_lt) := by
        have : kx < key (v[i]'h_i_lt) := h_v_i_gt
        omega
      exact ih (i + 1) h_i1_lt h_v_i1_gt
    · exact filter_seg_oob v kx (i + 1) n (by omega)

/-! ## Big invariant: insert_stable_at preserves filter_by_key.

We split into two lemmas by the `done` flag — they have different shapes:
`done = true` adds nothing, `done = false` adds `[x]` when `k = key x`. -/

/-- Filter invariant for the `done = true` branch of `insert_stable_at`. -/
private theorem insert_stable_at_filter_true
    (v : alloc.vec.Vec i64 alloc.alloc.Global) (x kx : i64) (k : Int) :
    ∀ (n : Nat) (i : usize)
      (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      v.val.size - i.toNat ≤ n →
      i.toNat ≤ v.val.size →
      (∀ (k' : Nat) (h : k' < v.val.size), i.toNat ≤ k' → v.val[k']'h ≠ Int64.minValue) →
      clever_143_order_by_points.insert_stable_at v x kx i true acc = RustM.ok r →
      filter_by_key r.val k r.val.size =
        filter_by_key acc.val k acc.val.size ++
          filter_seg v.val k i.toNat (v.val.size - i.toNat) := by
  intro n
  induction n with
  | zero =>
    intro i acc r hm hi_le h_nomin hres
    have hi_ge : v.val.size ≤ i.toNat := by omega
    have h_seg_empty : filter_seg v.val k i.toNat (v.val.size - i.toNat) = #[] :=
      filter_seg_oob v.val k i.toNat (v.val.size - i.toNat) hi_ge
    rw [insert_stable_at_oob_done v x kx i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    rw [h_seg_empty]; simp
  | succ n ih =>
    intro i acc r hm hi_le h_nomin hres
    by_cases hi_ge : v.val.size ≤ i.toNat
    · have h_seg_empty : filter_seg v.val k i.toNat (v.val.size - i.toNat) = #[] :=
        filter_seg_oob v.val k i.toNat (v.val.size - i.toNat) hi_ge
      rw [insert_stable_at_oob_done v x kx i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      rw [h_seg_empty]; simp
    · have hi_lt : i.toNat < v.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [usize_size_eq] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ v.val.size := by rw [h_i1]; omega
      have h_meas : v.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      have h_vi_no_min : v.val[i.toNat]'hi_lt ≠ Int64.minValue :=
        h_nomin i.toNat hi_lt (Nat.le_refl _)
      have h_nomin_next : ∀ (k' : Nat) (h : k' < v.val.size),
          (i + 1).toNat ≤ k' → v.val[k']'h ≠ Int64.minValue := by
        intro k' h_lt h_ge
        apply h_nomin k' h_lt
        rw [h_i1] at h_ge; omega
      -- pass step (done=true)
      by_cases h_acc : acc.val.size + 1 < USize64.size
      · rw [insert_stable_at_step_pass v x kx i true acc hi_lt h_vi_no_min (Or.inl rfl) h_acc] at hres
        have ih_app := ih (i + 1) (push_one acc (v.val[i.toNat]'hi_lt) h_acc) r
          h_meas h_i1_le h_nomin_next hres
        rw [h_i1] at ih_app
        rw [ih_app]
        -- LHS: filter_by_key (push_one acc v[i]).val k _ ++ filter_seg v.val k (i.toNat + 1) (v.size - (i+1).toNat)
        -- RHS: filter_by_key acc.val k acc.val.size ++ filter_seg v.val k i.toNat (v.val.size - i.toNat)
        have h_push_filter :
            filter_by_key (push_one acc (v.val[i.toNat]'hi_lt) h_acc).val k
              (push_one acc (v.val[i.toNat]'hi_lt) h_acc).val.size =
            filter_by_key acc.val k acc.val.size ++
              (if signed_digit_sum_int (v.val[i.toNat]'hi_lt).toInt = k then
                 #[v.val[i.toNat]'hi_lt] else #[]) := by
          show filter_by_key (acc.val ++ #[v.val[i.toNat]'hi_lt]) k
                (acc.val ++ #[v.val[i.toNat]'hi_lt]).size = _
          have h_size_app : (acc.val ++ #[v.val[i.toNat]'hi_lt]).size = acc.val.size + 1 := by
            rw [Array.size_append]; rfl
          rw [h_size_app, filter_by_key_append_singleton]
        rw [h_push_filter]
        -- Now relate filter_seg v.val k i.toNat (v.val.size - i.toNat) to the unfolded version
        have h_n_eq : v.val.size - i.toNat = (v.val.size - (i.toNat + 1)) + 1 := by omega
        rw [h_n_eq, filter_seg_succ_lo_lt v.val k i.toNat (v.val.size - (i.toNat + 1)) hi_lt]
        rw [Array.append_assoc]
      · exfalso
        have h_big : USize64.size ≤ acc.val.size + 1 := by omega
        rw [insert_stable_at_step_pass_fail v x kx i true acc hi_lt h_vi_no_min (Or.inl rfl) h_big] at hres
        cases hres

/-- Filter invariant for the `done = false` branch of `insert_stable_at`. -/
private theorem insert_stable_at_filter_false
    (v : alloc.vec.Vec i64 alloc.alloc.Global) (x kx : i64) (k : Int)
    (h_v_sorted : sorted_by_key v.val)
    (h_kx : kx.toInt = key x) :
    ∀ (n : Nat) (i : usize)
      (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      v.val.size - i.toNat ≤ n →
      i.toNat ≤ v.val.size →
      (∀ (k' : Nat) (h : k' < v.val.size), i.toNat ≤ k' → v.val[k']'h ≠ Int64.minValue) →
      clever_143_order_by_points.insert_stable_at v x kx i false acc = RustM.ok r →
      filter_by_key r.val k r.val.size =
        filter_by_key acc.val k acc.val.size ++
          filter_seg v.val k i.toNat (v.val.size - i.toNat) ++
          (if k = key x then #[x] else #[]) := by
  intro n
  induction n with
  | zero =>
    intro i acc r hm hi_le h_nomin hres
    have hi_ge : v.val.size ≤ i.toNat := by omega
    have h_seg_empty : filter_seg v.val k i.toNat (v.val.size - i.toNat) = #[] :=
      filter_seg_oob v.val k i.toNat (v.val.size - i.toNat) hi_ge
    by_cases h_acc : acc.val.size + 1 < USize64.size
    · rw [insert_stable_at_oob_not_done v x kx i acc hi_ge h_acc] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      show filter_by_key (acc.val ++ #[x]) k (acc.val ++ #[x]).size = _
      have h_size_app : (acc.val ++ #[x]).size = acc.val.size + 1 := by
        rw [Array.size_append]; rfl
      rw [h_size_app, filter_by_key_append_singleton]
      rw [h_seg_empty]
      -- LHS: filter_by_key acc.val k acc.val.size ++ (if key x = k then [x] else [])
      -- RHS: filter_by_key acc.val k acc.val.size ++ #[] ++ (if k = key x then [x] else [])
      by_cases h_eq : k = key x
      · have h_eq' : signed_digit_sum_int x.toInt = k := by
          simp only [key] at h_eq; exact h_eq.symm
        rw [if_pos h_eq', if_pos h_eq]; simp
      · have h_eq' : ¬ signed_digit_sum_int x.toInt = k := by
          simp only [key] at h_eq; intro h; exact h_eq h.symm
        rw [if_neg h_eq', if_neg h_eq]; simp
    · exfalso
      have h_big : USize64.size ≤ acc.val.size + 1 := by omega
      rw [insert_stable_at_oob_not_done_fail v x kx i acc hi_ge h_big] at hres
      cases hres
  | succ n ih =>
    intro i acc r hm hi_le h_nomin hres
    by_cases hi_ge : v.val.size ≤ i.toNat
    · -- Same as base case.
      have h_seg_empty : filter_seg v.val k i.toNat (v.val.size - i.toNat) = #[] :=
        filter_seg_oob v.val k i.toNat (v.val.size - i.toNat) hi_ge
      by_cases h_acc : acc.val.size + 1 < USize64.size
      · rw [insert_stable_at_oob_not_done v x kx i acc hi_ge h_acc] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        show filter_by_key (acc.val ++ #[x]) k (acc.val ++ #[x]).size = _
        have h_size_app : (acc.val ++ #[x]).size = acc.val.size + 1 := by
          rw [Array.size_append]; rfl
        rw [h_size_app, filter_by_key_append_singleton]
        rw [h_seg_empty]
        by_cases h_eq : k = key x
        · have h_eq' : signed_digit_sum_int x.toInt = k := by
            simp only [key] at h_eq; exact h_eq.symm
          rw [if_pos h_eq', if_pos h_eq]; simp
        · have h_eq' : ¬ signed_digit_sum_int x.toInt = k := by
            simp only [key] at h_eq; intro h; exact h_eq h.symm
          rw [if_neg h_eq', if_neg h_eq]; simp
      · exfalso
        have h_big : USize64.size ≤ acc.val.size + 1 := by omega
        rw [insert_stable_at_oob_not_done_fail v x kx i acc hi_ge h_big] at hres
        cases hres
    · have hi_lt : i.toNat < v.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [usize_size_eq] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ v.val.size := by rw [h_i1]; omega
      have h_meas : v.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      have h_vi_no_min : v.val[i.toNat]'hi_lt ≠ Int64.minValue :=
        h_nomin i.toNat hi_lt (Nat.le_refl _)
      have h_nomin_next : ∀ (k' : Nat) (h : k' < v.val.size),
          (i + 1).toNat ≤ k' → v.val[k']'h ≠ Int64.minValue := by
        intro k' h_lt h_ge
        apply h_nomin k' h_lt
        rw [h_i1] at h_ge; omega
      -- Head-first unfold of filter_seg at i.toNat
      have h_n_eq : v.val.size - i.toNat = (v.val.size - (i.toNat + 1)) + 1 := by omega
      have h_unfold_seg :
          filter_seg v.val k i.toNat (v.val.size - i.toNat) =
            (if signed_digit_sum_int (v.val[i.toNat]'hi_lt).toInt = k then
                #[v.val[i.toNat]'hi_lt] else #[]) ++
              filter_seg v.val k (i.toNat + 1) (v.val.size - (i.toNat + 1)) := by
        rw [h_n_eq]
        exact filter_seg_succ_lo_lt v.val k i.toNat (v.val.size - (i.toNat + 1)) hi_lt
      by_cases h_lt : kx.toInt < key (v.val[i.toNat]'hi_lt)
      · -- Insert branch.
        by_cases h_acc : acc.val.size + 2 < USize64.size
        · rw [insert_stable_at_step_insert v x kx i acc hi_lt h_vi_no_min h_lt h_acc] at hres
          have ih_app := insert_stable_at_filter_true v x kx k
            (n + 1) (i + 1) (push_two acc x (v.val[i.toNat]'hi_lt) h_acc) r
            (by rw [h_i1]; omega) h_i1_le h_nomin_next hres
          rw [h_i1] at ih_app
          rw [ih_app]
          have h_push_filter :
              filter_by_key (push_two acc x (v.val[i.toNat]'hi_lt) h_acc).val k
                (push_two acc x (v.val[i.toNat]'hi_lt) h_acc).val.size =
              filter_by_key acc.val k acc.val.size ++
                (if signed_digit_sum_int x.toInt = k then #[x] else #[]) ++
                (if signed_digit_sum_int (v.val[i.toNat]'hi_lt).toInt = k then
                   #[v.val[i.toNat]'hi_lt] else #[]) := by
            show filter_by_key (acc.val ++ #[x, v.val[i.toNat]'hi_lt]) k
                  (acc.val ++ #[x, v.val[i.toNat]'hi_lt]).size = _
            have h_size_app : (acc.val ++ #[x, v.val[i.toNat]'hi_lt]).size = acc.val.size + 2 := by
              rw [Array.size_append]; rfl
            rw [h_size_app, filter_by_key_append_pair]
          rw [h_push_filter]
          -- Now: LHS = filter_by_key acc.val k acc.val.size ++
          --              (if key x = k then [x] else []) ++
          --              (if key v[i] = k then [v[i]] else []) ++
          --              filter_seg v.val k (i.toNat + 1) (v.val.size - (i.toNat + 1))
          --     RHS = filter_by_key acc.val k acc.val.size ++
          --             filter_seg v.val k i.toNat (v.val.size - i.toNat) ++
          --             (if k = key x then [x] else [])
          --     Note: filter_seg v.val k i.toNat (...) = head v[i] ++ tail
          -- For k = key x: key v[i] > kx = key x = k, so key v[i] ≠ k. Tail filter is empty (sorted invariant).
          rw [h_unfold_seg]
          by_cases h_eq : k = key x
          · -- k = key x, so signed_digit_sum_int x.toInt = k.
            have h_xk : signed_digit_sum_int x.toInt = k := by
              simp only [key] at h_eq; exact h_eq.symm
            have h_v_i_ne_k : ¬ signed_digit_sum_int (v.val[i.toNat]'hi_lt).toInt = k := by
              have h_gt : kx.toInt < key (v.val[i.toNat]'hi_lt) := h_lt
              rw [h_kx] at h_gt
              simp only [key] at h_gt
              rw [h_eq]
              simp only [key]
              intro h_keq; omega
            have h_seg_empty :
                filter_seg v.val k (i.toNat + 1) (v.val.size - (i.toNat + 1)) = #[] := by
              by_cases h_i1_lt' : i.toNat + 1 < v.val.size
              · have h_step : key (v.val[i.toNat]'hi_lt) ≤ key (v.val[i.toNat + 1]'h_i1_lt') :=
                  h_v_sorted i.toNat (i.toNat + 1) hi_lt h_i1_lt' (by omega)
                have h_v_i1_gt : k < key (v.val[i.toNat + 1]'h_i1_lt') := by
                  have h_k_lt_vi : k < key (v.val[i.toNat]'hi_lt) := by
                    rw [h_eq]; rw [← h_kx]; exact h_lt
                  omega
                exact filter_seg_empty_when_gt v.val k (i.toNat + 1) h_i1_lt' h_v_sorted h_v_i1_gt _
              · exact filter_seg_oob v.val k (i.toNat + 1) _ (by omega)
            rw [if_pos h_xk, if_neg h_v_i_ne_k, if_pos h_eq, h_seg_empty]
            simp
          · -- k ≠ key x, so signed_digit_sum_int x.toInt ≠ k.
            have h_xk : ¬ signed_digit_sum_int x.toInt = k := by
              simp only [key] at h_eq; intro h; exact h_eq h.symm
            rw [if_neg h_xk, if_neg h_eq]
            simp [Array.append_assoc]
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 2 := by omega
          rw [insert_stable_at_step_insert_fail v x kx i acc hi_lt h_vi_no_min h_lt h_big] at hres
          cases hres
      · -- Pass branch (done=false stays false).
        have h_le : key (v.val[i.toNat]'hi_lt) ≤ kx.toInt := by
          simp only [key] at h_lt ⊢; omega
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [insert_stable_at_step_pass v x kx i false acc hi_lt h_vi_no_min (Or.inr h_le) h_acc] at hres
          have ih_app := ih (i + 1) (push_one acc (v.val[i.toNat]'hi_lt) h_acc) r
            h_meas h_i1_le h_nomin_next hres
          rw [h_i1] at ih_app
          rw [ih_app]
          have h_push_filter :
              filter_by_key (push_one acc (v.val[i.toNat]'hi_lt) h_acc).val k
                (push_one acc (v.val[i.toNat]'hi_lt) h_acc).val.size =
              filter_by_key acc.val k acc.val.size ++
                (if signed_digit_sum_int (v.val[i.toNat]'hi_lt).toInt = k then
                   #[v.val[i.toNat]'hi_lt] else #[]) := by
            show filter_by_key (acc.val ++ #[v.val[i.toNat]'hi_lt]) k
                  (acc.val ++ #[v.val[i.toNat]'hi_lt]).size = _
            have h_size_app : (acc.val ++ #[v.val[i.toNat]'hi_lt]).size = acc.val.size + 1 := by
              rw [Array.size_append]; rfl
            rw [h_size_app, filter_by_key_append_singleton]
          rw [h_push_filter, h_unfold_seg]
          simp [Array.append_assoc]
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_stable_at_step_pass_fail v x kx i false acc hi_lt h_vi_no_min (Or.inr h_le) h_big] at hres
          cases hres

/-! ## `insert_stable` wrapper for filter. -/

private theorem insert_stable_filter
    (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64) (k : Int)
    (h_x_no_min : x ≠ Int64.minValue)
    (h_v_no_min : ∀ (k' : Nat) (h : k' < v.val.size), v.val[k']'h ≠ Int64.minValue)
    (h_v_sorted : sorted_by_key v.val)
    (r : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_143_order_by_points.insert_stable v x = RustM.ok r) :
    filter_by_key r.val k r.val.size =
      filter_by_key v.val k v.val.size ++
        (if k = key x then #[x] else #[]) := by
  unfold clever_143_order_by_points.insert_stable at hres
  obtain ⟨kx, h_kx_eq, h_kx_int⟩ := signed_digit_sum_correct x h_x_no_min
  rw [h_kx_eq] at hres
  simp only [RustM_ok_bind] at hres
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_meas : v.val.size - (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  have h_le : (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  have h_nomin_zero : ∀ (k' : Nat) (h : k' < v.val.size), (0 : usize).toNat ≤ k' → v.val[k']'h ≠ Int64.minValue := by
    intro k' h _; exact h_v_no_min k' h
  have inv := insert_stable_at_filter_false v x kx k h_v_sorted h_kx_int v.val.size (0 : usize)
    ⟨(List.nil).toArray, by grind⟩ r h_meas h_le h_nomin_zero hres
  rw [h_zero_toNat] at inv
  -- Simplify the right-hand side.
  have h_empty_filter :
      filter_by_key ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val k
        ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = #[] := rfl
  rw [h_empty_filter] at inv
  -- filter_seg v.val k 0 v.val.size = filter_by_key v.val k v.val.size
  rw [filter_seg_zero_eq_filter_by_key] at inv
  rw [inv]
  simp

/-! ## sort_at filter invariant. -/

private theorem sort_at_filter
    (l : RustSlice i64) (k : Int)
    (h_l_no_min : ∀ (k' : Nat) (h : k' < l.val.size), l.val[k']'h ≠ Int64.minValue) :
    ∀ (n : Nat) (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      (∀ (k' : Nat) (h : k' < acc.val.size), acc.val[k']'h ≠ Int64.minValue) →
      sorted_by_key acc.val →
      filter_by_key acc.val k acc.val.size = filter_by_key l.val k i.toNat →
      clever_143_order_by_points.sort_at l i acc = RustM.ok r →
      filter_by_key r.val k r.val.size = filter_by_key l.val k l.val.size := by
  intro n
  induction n with
  | zero =>
    intro i acc r hm hi_le h_acc_nomin h_acc_sorted h_inv hres
    have hi_ge : l.val.size ≤ i.toNat := by omega
    have hi_eq : i.toNat = l.val.size := by omega
    rw [sort_at_oob l i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    rw [h_inv, hi_eq]
  | succ n ih =>
    intro i acc r hm hi_le h_acc_nomin h_acc_sorted h_inv hres
    by_cases hi_ge : l.val.size ≤ i.toNat
    · have hi_eq : i.toNat = l.val.size := by omega
      rw [sort_at_oob l i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      rw [h_inv, hi_eq]
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_meas : l.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      rw [sort_at_step l i acc hi_lt] at hres
      generalize h_ins : clever_143_order_by_points.insert_stable acc (l.val[i.toNat]'hi_lt) = ins_res at hres
      cases ins_res with
      | none =>
        exfalso
        have hh : (do let acc' ← (none : RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                       clever_143_order_by_points.sort_at l (i + 1) acc')
                  = RustM.ok r := hres
        cases hh
      | some res' =>
        cases res' with
        | error e =>
          exfalso
          have hh : (do let acc' ← (some (Except.error e) :
                                      RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                         clever_143_order_by_points.sort_at l (i + 1) acc')
                    = RustM.ok r := hres
          cases hh
        | ok acc' =>
          have h_ins_ok : clever_143_order_by_points.insert_stable acc (l.val[i.toNat]'hi_lt) = RustM.ok acc' := h_ins
          simp only [RustM_ok_bind] at hres
          have h_l_i_no_min : l.val[i.toNat]'hi_lt ≠ Int64.minValue := h_l_no_min i.toNat hi_lt
          have h_acc'_nomin : ∀ (k' : Nat) (h : k' < acc'.val.size), acc'.val[k']'h ≠ Int64.minValue :=
            insert_stable_no_min acc (l.val[i.toNat]'hi_lt) h_l_i_no_min h_acc_nomin acc' h_ins_ok
          have h_acc'_sorted : sorted_by_key acc'.val :=
            insert_stable_sorted acc (l.val[i.toNat]'hi_lt) h_l_i_no_min h_acc_nomin acc' h_ins_ok h_acc_sorted
          have h_acc'_filter : filter_by_key acc'.val k acc'.val.size =
              filter_by_key acc.val k acc.val.size ++
                (if k = key (l.val[i.toNat]'hi_lt) then #[l.val[i.toNat]'hi_lt] else #[]) :=
            insert_stable_filter acc (l.val[i.toNat]'hi_lt) k h_l_i_no_min h_acc_nomin h_acc_sorted acc' h_ins_ok
          have h_filter_l_succ :
              filter_by_key l.val k (i.toNat + 1) =
                filter_by_key l.val k i.toNat ++
                  (if k = key (l.val[i.toNat]'hi_lt) then #[l.val[i.toNat]'hi_lt] else #[]) := by
            show (if h : i.toNat < l.val.size then
                    let rest := filter_by_key l.val k i.toNat
                    if signed_digit_sum_int (l.val[i.toNat]'h).toInt = k then rest.push (l.val[i.toNat]'h)
                    else rest
                  else filter_by_key l.val k i.toNat) = _
            rw [dif_pos hi_lt]
            by_cases h_eq : signed_digit_sum_int (l.val[i.toNat]'hi_lt).toInt = k
            · have h_eq' : k = key (l.val[i.toNat]'hi_lt) := by
                simp only [key]; exact h_eq.symm
              rw [if_pos h_eq, if_pos h_eq']; simp
            · have h_eq' : k ≠ key (l.val[i.toNat]'hi_lt) := by
                simp only [key]; intro h; exact h_eq h.symm
              rw [if_neg h_eq, if_neg h_eq']; simp
          have h_acc'_inv : filter_by_key acc'.val k acc'.val.size = filter_by_key l.val k (i + 1).toNat := by
            rw [h_acc'_filter, h_inv, h_i1, ← h_filter_l_succ]
          exact ih (i + 1) acc' r h_meas h_i1_le h_acc'_nomin h_acc'_sorted h_acc'_inv hres

/-! ## Obligation theorems. -/

/-- Anchor: an empty input slice yields a successful empty output. -/
theorem empty_input_yields_empty_output
    (l : RustSlice i64) (hempty : l.val.size = 0) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_143_order_by_points.order_by_points l = RustM.ok v ∧
      v.val.size = 0 := by
  refine ⟨⟨(List.nil).toArray, by grind⟩, ?_, ?_⟩
  · unfold clever_143_order_by_points.order_by_points
    have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                    RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                  RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
    rw [h_new]
    simp only [RustM_ok_bind]
    -- sort_at l 0 acc with l.val.size = 0
    unfold clever_143_order_by_points.sort_at
    have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
    have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
      USize64.toNat_ofNat_of_lt' h_size_lt
    have h_cond : decide (USize64.ofNat l.val.size ≤ (0 : usize)) = true := by
      rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat, hempty]
      exact Nat.zero_le _
    simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
               rust_primitives.cmp.ge, pure_bind, h_cond, ↓reduceIte]
    rfl
  · rfl

/-- Postcondition 1 — Permutation: the multiset of output entries equals
    the multiset of input entries (witnessed by `vec_count`). -/
theorem output_is_permutation_of_input
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_143_order_by_points.order_by_points l = RustM.ok v)
    (target : i64) :
    vec_count v.val target v.val.size
      = vec_count l.val target l.val.size := by
  unfold clever_143_order_by_points.order_by_points at hres
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  have h_zero_le : (0 : usize).toNat = 0 := rfl
  have h_meas : l.val.size - (0 : usize).toNat ≤ l.val.size := by rw [h_zero_le]; omega
  have h_le : (0 : usize).toNat ≤ l.val.size := by rw [h_zero_le]; omega
  have h_empty_nomin : ∀ (k : Nat) (h : k < ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size),
      ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val[k]'h ≠ Int64.minValue := by
    intro k h
    have h_empty : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  -- Derive that all l elements are non-minValue from sort_at success.
  have h_l_nomin : ∀ (k : Nat) (h : k < l.val.size), l.val[k]'h ≠ Int64.minValue := by
    intro k h_lt
    have h_ge : (0 : usize).toNat ≤ k := by rw [h_zero_le]; omega
    exact sort_at_no_min_input l.val.size l (0 : usize)
            ⟨(List.nil).toArray, by grind⟩ v h_meas h_le h_empty_nomin hres k h_lt h_ge
  have inv := sort_at_inv l.val.size l (0 : usize)
                ⟨(List.nil).toArray, by grind⟩ v target h_meas h_le h_l_nomin h_empty_nomin hres
  obtain ⟨h_size_eq, h_count_eq⟩ := inv
  rw [h_zero_le] at h_count_eq
  have h_l_zero : vec_count l.val target 0 = 0 := rfl
  have h_empty_size :
      ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
  rw [h_empty_size] at h_count_eq
  have h_empty_count_at_zero :
      vec_count ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val target 0 = 0 :=
    rfl
  rw [h_empty_count_at_zero, h_l_zero] at h_count_eq
  omega

/-- Postcondition 2 — Sorted by key. -/
theorem output_is_sorted_by_signed_digit_sum
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_143_order_by_points.order_by_points l = RustM.ok v)
    (k : Nat) (hk : k + 1 < v.val.size) :
    signed_digit_sum_int (v.val[k]'(Nat.lt_of_succ_lt hk)).toInt
      ≤ signed_digit_sum_int (v.val[k + 1]'hk).toInt := by
  unfold clever_143_order_by_points.order_by_points at hres
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  have h_zero_le : (0 : usize).toNat = 0 := rfl
  have h_meas : l.val.size - (0 : usize).toNat ≤ l.val.size := by rw [h_zero_le]; omega
  have h_le : (0 : usize).toNat ≤ l.val.size := by rw [h_zero_le]; omega
  have h_empty_nomin : ∀ (k : Nat) (h : k < ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size),
      ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val[k]'h ≠ Int64.minValue := by
    intro k h
    have h_empty : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  have h_l_nomin : ∀ (k : Nat) (h : k < l.val.size), l.val[k]'h ≠ Int64.minValue := by
    intro k h_lt
    have h_ge : (0 : usize).toNat ≤ k := by rw [h_zero_le]; omega
    exact sort_at_no_min_input l.val.size l (0 : usize)
            ⟨(List.nil).toArray, by grind⟩ v h_meas h_le h_empty_nomin hres k h_lt h_ge
  have h_empty_sorted : sorted_by_key ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val := by
    intro k₁ k₂ h₁ _ _
    have : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  have h_v_sorted : sorted_by_key v.val :=
    sort_at_sorted l.val.size l (0 : usize) ⟨(List.nil).toArray, by grind⟩ v
      h_meas h_le h_l_nomin h_empty_nomin hres h_empty_sorted
  exact h_v_sorted k (k + 1) (Nat.lt_of_succ_lt hk) hk (Nat.le_succ _)

/--
Postcondition 3 — Stability: for every key value `k`, the subsequence
of input elements whose key equals `k` is preserved verbatim in the
output. -/
theorem output_is_stable
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_143_order_by_points.order_by_points l = RustM.ok v)
    (k : Int) :
    filter_by_key l.val k l.val.size
      = filter_by_key v.val k v.val.size := by
  unfold clever_143_order_by_points.order_by_points at hres
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  have h_zero_le : (0 : usize).toNat = 0 := rfl
  have h_meas : l.val.size - (0 : usize).toNat ≤ l.val.size := by rw [h_zero_le]; omega
  have h_le : (0 : usize).toNat ≤ l.val.size := by rw [h_zero_le]; omega
  have h_empty_nomin : ∀ (k : Nat) (h : k < ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size),
      ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val[k]'h ≠ Int64.minValue := by
    intro k h
    have h_empty : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  have h_l_nomin : ∀ (k : Nat) (h : k < l.val.size), l.val[k]'h ≠ Int64.minValue := by
    intro k h_lt
    have h_ge : (0 : usize).toNat ≤ k := by rw [h_zero_le]; omega
    exact sort_at_no_min_input l.val.size l (0 : usize)
            ⟨(List.nil).toArray, by grind⟩ v h_meas h_le h_empty_nomin hres k h_lt h_ge
  have h_empty_sorted : sorted_by_key ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val := by
    intro k₁ k₂ h₁ _ _
    have : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  have h_empty_filter :
      filter_by_key ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val k
        ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = #[] := rfl
  have h_inv_start :
      filter_by_key ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val k
        ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size =
      filter_by_key l.val k (0 : usize).toNat := by
    rw [h_empty_filter]; rw [h_zero_le]; rfl
  have h_final :=
    sort_at_filter l k h_l_nomin l.val.size (0 : usize)
      ⟨(List.nil).toArray, by grind⟩ v h_meas h_le h_empty_nomin h_empty_sorted h_inv_start hres
  exact h_final.symm

/-- Concrete signed_digit_sum: for non-minValue inputs, if the integer-level
    oracle agrees with `m.toInt`, then `signed_digit_sum n = RustM.ok m`. -/
private theorem signed_digit_sum_val (n m : i64)
    (h_no_min : n ≠ Int64.minValue)
    (h_eq : signed_digit_sum_int n.toInt = m.toInt) :
    clever_143_order_by_points.signed_digit_sum n = RustM.ok m := by
  obtain ⟨r, h_r_eq, h_r_int⟩ := signed_digit_sum_correct n h_no_min
  have h_r_m : r = m := Int64.toInt_inj.mp (by rw [h_r_int, h_eq])
  rw [h_r_eq, h_r_m]

/-- digit_sum_nat 1 0 = 1. -/
private theorem digit_sum_nat_1 : digit_sum_nat 1 0 = 1 :=
  digit_sum_nat_small 1 (by decide)

/-- digit_sum_nat 11 0 = 2. -/
private theorem digit_sum_nat_11 : digit_sum_nat 11 0 = 2 := by
  rw [digit_sum_nat_succ 11 0 (by decide)]
  -- digit_sum_nat (11/10) (0 + 11%10) = digit_sum_nat 1 1
  show digit_sum_nat 1 1 = 2
  rw [digit_sum_nat_succ 1 1 (by decide)]
  show digit_sum_nat 0 2 = 2
  rw [digit_sum_nat_zero 2]

/-- first_digit_nat 1 = 1. -/
private theorem first_digit_nat_1 : first_digit_nat 1 = 1 :=
  first_digit_nat_small 1 (by decide)

/-- first_digit_nat 11 = 1. -/
private theorem first_digit_nat_11 : first_digit_nat 11 = 1 := by
  rw [first_digit_nat_large 11 (by decide)]
  show first_digit_nat 1 = 1
  exact first_digit_nat_small 1 (by decide)

private theorem sds_1 : clever_143_order_by_points.signed_digit_sum (1 : i64) = RustM.ok 1 := by
  apply signed_digit_sum_val 1 1 (by decide)
  have h1 : (1 : i64).toInt = 1 := i64_one_toInt
  rw [h1, signed_digit_sum_int_pos 1 (by decide)]
  show ((digit_sum_nat (1 : Int).toNat 0 : Nat) : Int) = (1 : i64).toInt
  rw [show ((1 : Int).toNat = 1) from rfl, digit_sum_nat_1, h1]
  rfl

private theorem sds_11 : clever_143_order_by_points.signed_digit_sum (11 : i64) = RustM.ok 2 := by
  apply signed_digit_sum_val 11 2 (by decide)
  have h11 : (11 : i64).toInt = 11 := by decide
  have h2 : (2 : i64).toInt = 2 := i64_two_toInt
  rw [h11, signed_digit_sum_int_pos 11 (by decide)]
  show ((digit_sum_nat (11 : Int).toNat 0 : Nat) : Int) = (2 : i64).toInt
  rw [show ((11 : Int).toNat = 11) from rfl, digit_sum_nat_11, h2]
  rfl

private theorem sds_neg1 : clever_143_order_by_points.signed_digit_sum (-1 : i64) = RustM.ok (-1) := by
  apply signed_digit_sum_val (-1) (-1) (by decide)
  have h_neg1 : (-1 : i64).toInt = -1 := by decide
  rw [h_neg1, signed_digit_sum_int_neg (-1) (by decide)]
  show (digit_sum_nat (- (-1 : Int)).toNat 0 : Int)
        - 2 * (first_digit_nat (- (-1 : Int)).toNat : Int) = (-1 : i64).toInt
  rw [show ((- (-1 : Int)).toNat = 1) from rfl, digit_sum_nat_1, first_digit_nat_1, h_neg1]
  decide

private theorem sds_neg11 : clever_143_order_by_points.signed_digit_sum (-11 : i64) = RustM.ok 0 := by
  apply signed_digit_sum_val (-11) 0 (by decide)
  have h_neg11 : (-11 : i64).toInt = -11 := by decide
  have h0 : (0 : i64).toInt = 0 := i64_zero_toInt
  rw [h_neg11, signed_digit_sum_int_neg (-11) (by decide)]
  show (digit_sum_nat (- (-11 : Int)).toNat 0 : Int)
        - 2 * (first_digit_nat (- (-11 : Int)).toNat : Int) = (0 : i64).toInt
  rw [show ((- (-11 : Int)).toNat = 11) from rfl, digit_sum_nat_11, first_digit_nat_11, h0]
  decide

private theorem sds_0 : clever_143_order_by_points.signed_digit_sum (0 : i64) = RustM.ok 0 :=
  signed_digit_sum_zero

/-- Concrete `key` values. -/
private theorem key_1 : key (1 : i64) = 1 := by
  show signed_digit_sum_int (1 : i64).toInt = 1
  rw [i64_one_toInt, signed_digit_sum_int_pos 1 (by decide)]
  show ((digit_sum_nat (1 : Int).toNat 0 : Nat) : Int) = 1
  rw [show ((1 : Int).toNat = 1) from rfl, digit_sum_nat_1]; rfl

private theorem key_11 : key (11 : i64) = 2 := by
  show signed_digit_sum_int (11 : i64).toInt = 2
  rw [show ((11 : i64).toInt = 11) from by decide, signed_digit_sum_int_pos 11 (by decide)]
  show ((digit_sum_nat (11 : Int).toNat 0 : Nat) : Int) = 2
  rw [show ((11 : Int).toNat = 11) from rfl, digit_sum_nat_11]; rfl

private theorem key_neg1 : key (-1 : i64) = -1 := by
  show signed_digit_sum_int (-1 : i64).toInt = -1
  rw [show ((-1 : i64).toInt = -1) from by decide, signed_digit_sum_int_neg (-1) (by decide)]
  show (digit_sum_nat (- (-1 : Int)).toNat 0 : Int) - 2 * (first_digit_nat (- (-1 : Int)).toNat : Int) = -1
  rw [show ((- (-1 : Int)).toNat = 1) from rfl, digit_sum_nat_1, first_digit_nat_1]; decide

private theorem key_neg11 : key (-11 : i64) = 0 := by
  show signed_digit_sum_int (-11 : i64).toInt = 0
  rw [show ((-11 : i64).toInt = -11) from by decide, signed_digit_sum_int_neg (-11) (by decide)]
  show (digit_sum_nat (- (-11 : Int)).toNat 0 : Int) - 2 * (first_digit_nat (- (-11 : Int)).toNat : Int) = 0
  rw [show ((- (-11 : Int)).toNat = 11) from rfl, digit_sum_nat_11, first_digit_nat_11]; decide

private theorem key_0 : key (0 : i64) = 0 := by
  show signed_digit_sum_int (0 : i64).toInt = 0
  rw [i64_zero_toInt, signed_digit_sum_int_zero]

/-- Step 1: insert 1 into empty Vec. -/
private theorem ins_1 :
    clever_143_order_by_points.insert_stable
      (⟨#[], by decide⟩ : alloc.vec.Vec i64 alloc.alloc.Global) 1
      = RustM.ok ⟨#[(1 : i64)], by decide⟩ := by
  unfold clever_143_order_by_points.insert_stable
  rw [sds_1]
  simp only [RustM_ok_bind]
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok (⟨#[], by decide⟩ : alloc.vec.Vec i64 alloc.alloc.Global) := rfl
  rw [h_new]
  simp only [RustM_ok_bind]
  have h_acc_bound : (⟨#[], by decide⟩ : alloc.vec.Vec i64 alloc.alloc.Global).val.size + 1 < USize64.size := by decide
  rw [insert_stable_at_oob_not_done _ 1 1 0
      (⟨#[], by decide⟩ : alloc.vec.Vec i64 alloc.alloc.Global)
      (by show 0 ≤ 0; exact Nat.le_refl 0) h_acc_bound]
  rfl

/-- Step 2: insert 11 into ⟨#[1], _⟩. -/
private theorem ins_11 :
    clever_143_order_by_points.insert_stable
      (⟨#[1], by decide⟩ : alloc.vec.Vec i64 alloc.alloc.Global) 11
      = RustM.ok ⟨#[(1 : i64), 11], by decide⟩ := by
  unfold clever_143_order_by_points.insert_stable
  rw [sds_11]
  simp only [RustM_ok_bind]
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok (⟨#[], by decide⟩ : alloc.vec.Vec i64 alloc.alloc.Global) := rfl
  rw [h_new]
  simp only [RustM_ok_bind]
  let v : alloc.vec.Vec i64 alloc.alloc.Global := ⟨#[1], by decide⟩
  let acc0 : alloc.vec.Vec i64 alloc.alloc.Global := ⟨#[], by decide⟩
  have h_v_0 : v.val[(0:usize).toNat]'(by show 0 < 1; decide) = 1 := rfl
  have h_no_min_0 : (v.val[(0:usize).toNat]'(by show 0 < 1; decide)) ≠ Int64.minValue := by
    rw [h_v_0]; decide
  have h_skip_0 : key (v.val[(0:usize).toNat]'(by show 0 < 1; decide)) ≤ (2 : i64).toInt := by
    rw [h_v_0, key_1, i64_two_toInt]; decide
  have h_acc_bound_0 : acc0.val.size + 1 < USize64.size := by decide
  rw [insert_stable_at_step_pass v 11 2 0 false acc0
      (by show 0 < 1; decide) h_no_min_0 (Or.inr h_skip_0) h_acc_bound_0]
  have h_acc1_bound : (push_one acc0 (v.val[(0:usize).toNat]'(by show 0 < 1; decide)) h_acc_bound_0).val.size + 1 < USize64.size := by
    rw [push_one_size]; decide
  rw [insert_stable_at_oob_not_done v 11 2 ((0:usize) + 1)
      (push_one acc0 (v.val[(0:usize).toNat]'(by show 0 < 1; decide)) h_acc_bound_0)
      (by show 1 ≤ 1; exact Nat.le_refl 1) h_acc1_bound]
  rfl

/-- Step 3: insert -1 into ⟨#[1, 11], _⟩. -/
private theorem ins_neg1 :
    clever_143_order_by_points.insert_stable
      (⟨#[1, 11], by decide⟩ : alloc.vec.Vec i64 alloc.alloc.Global) (-1)
      = RustM.ok ⟨#[(-1 : i64), 1, 11], by decide⟩ := by
  unfold clever_143_order_by_points.insert_stable
  rw [sds_neg1]
  simp only [RustM_ok_bind]
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok (⟨#[], by decide⟩ : alloc.vec.Vec i64 alloc.alloc.Global) := rfl
  rw [h_new]
  simp only [RustM_ok_bind]
  let v : alloc.vec.Vec i64 alloc.alloc.Global := ⟨#[1, 11], by decide⟩
  let acc0 : alloc.vec.Vec i64 alloc.alloc.Global := ⟨#[], by decide⟩
  -- i=0: vi=1, key(1)=1. kx=-1 < 1. Insert.
  have h_v_0 : v.val[(0:usize).toNat]'(by show 0 < 2; decide) = 1 := rfl
  have h_no_min_0 : (v.val[(0:usize).toNat]'(by show 0 < 2; decide)) ≠ Int64.minValue := by
    rw [h_v_0]; decide
  have h_lt_0 : (-1 : i64).toInt < key (v.val[(0:usize).toNat]'(by show 0 < 2; decide)) := by
    rw [h_v_0, key_1]; decide
  have h_acc_bound_0 : acc0.val.size + 2 < USize64.size := by decide
  rw [insert_stable_at_step_insert v (-1) (-1) 0 acc0
      (by show 0 < 2; decide) h_no_min_0 h_lt_0 h_acc_bound_0]
  -- Now insert_stable_at v (-1) (-1) 1 true (push_two acc0 (-1) v[0] _)
  -- new acc = ⟨#[-1, 1], _⟩
  -- i=1: vi=11, done=true → pass.
  let acc1 := push_two acc0 (-1 : i64) (v.val[(0:usize).toNat]'(by show 0 < 2; decide)) h_acc_bound_0
  have h_v_1 : v.val[((0:usize) + 1).toNat]'(by
      have : ((0:usize) + 1).toNat = 1 := by decide
      rw [this]; decide) = 11 := by
    have h_idx : ((0:usize) + 1).toNat = 1 := by decide
    show v.val[((0:usize) + 1).toNat] = 11
    have : ((0:usize) + 1).toNat = 1 := h_idx
    congr 1
  have h_no_min_1 : (v.val[((0:usize) + 1).toNat]'(by
      have : ((0:usize) + 1).toNat = 1 := by decide
      rw [this]; decide)) ≠ Int64.minValue := by
    rw [h_v_1]; decide
  have h_acc_bound_1 : acc1.val.size + 1 < USize64.size := by
    show (acc0.val ++ #[(-1 : i64), v.val[(0:usize).toNat]'(by show 0 < 2; decide)]).size + 1 < USize64.size
    rw [Array.size_append]; decide
  have h_idx_1' : ((0:usize) + 1).toNat = 1 := by decide
  have h_pos_1 : ((0:usize) + 1).toNat < v.val.size := by rw [h_idx_1']; show 1 < 2; decide
  rw [insert_stable_at_step_pass v (-1) (-1) ((0:usize) + 1) true acc1
      h_pos_1
      h_no_min_1 (Or.inl rfl) h_acc_bound_1]
  -- Now insert_stable_at v (-1) (-1) 2 true (push_one acc1 v[1] _)
  -- new acc = ⟨#[-1, 1, 11], _⟩
  -- i=2: i ≥ v.size, done=true → oob_done.
  rw [insert_stable_at_oob_done v (-1) (-1) ((0:usize) + 1 + 1) _
      (by
        have : ((0:usize) + 1 + 1).toNat = 2 := by decide
        rw [this]; decide)]
  rfl

/-- Step 4: insert -11 into ⟨#[-1, 1, 11], _⟩. -/
private theorem ins_neg11 :
    clever_143_order_by_points.insert_stable
      (⟨#[-1, 1, 11], by decide⟩ : alloc.vec.Vec i64 alloc.alloc.Global) (-11)
      = RustM.ok ⟨#[(-1 : i64), -11, 1, 11], by decide⟩ := by
  unfold clever_143_order_by_points.insert_stable
  rw [sds_neg11]
  simp only [RustM_ok_bind]
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok (⟨#[], by decide⟩ : alloc.vec.Vec i64 alloc.alloc.Global) := rfl
  rw [h_new]
  simp only [RustM_ok_bind]
  let v : alloc.vec.Vec i64 alloc.alloc.Global := ⟨#[-1, 1, 11], by decide⟩
  let acc0 : alloc.vec.Vec i64 alloc.alloc.Global := ⟨#[], by decide⟩
  -- i=0: vi=-1, key(-1)=-1. kx=0. -1 > 0 is false. Pass (done=false).
  have h_v_0 : v.val[(0:usize).toNat]'(by show 0 < 3; decide) = -1 := rfl
  have h_no_min_0 : (v.val[(0:usize).toNat]'(by show 0 < 3; decide)) ≠ Int64.minValue := by
    rw [h_v_0]; decide
  have h_skip_0 : key (v.val[(0:usize).toNat]'(by show 0 < 3; decide)) ≤ (0 : i64).toInt := by
    rw [h_v_0, key_neg1, i64_zero_toInt]; decide
  have h_acc_bound_0 : acc0.val.size + 1 < USize64.size := by decide
  rw [insert_stable_at_step_pass v (-11) 0 0 false acc0
      (by show 0 < 3; decide) h_no_min_0 (Or.inr h_skip_0) h_acc_bound_0]
  -- new acc = ⟨#[-1], _⟩
  let acc1 := push_one acc0 (v.val[(0:usize).toNat]'(by show 0 < 3; decide)) h_acc_bound_0
  -- i=1: vi=1, key(1)=1. kx=0 < 1. Insert.
  have h_idx_1 : ((0:usize) + 1).toNat = 1 := by decide
  have h_v_1 : v.val[((0:usize) + 1).toNat]'(by rw [h_idx_1]; decide) = 1 := by
    show v.val[((0:usize) + 1).toNat] = 1
    congr 1
  have h_no_min_1 : (v.val[((0:usize) + 1).toNat]'(by rw [h_idx_1]; decide)) ≠ Int64.minValue := by
    rw [h_v_1]; decide
  have h_lt_1 : (0 : i64).toInt < key (v.val[((0:usize) + 1).toNat]'(by rw [h_idx_1]; decide)) := by
    rw [h_v_1, key_1, i64_zero_toInt]; decide
  have h_acc_bound_1 : acc1.val.size + 2 < USize64.size := by
    show (acc0.val ++ #[v.val[(0:usize).toNat]'(by show 0 < 3; decide)]).size + 2 < USize64.size
    rw [Array.size_append]; decide
  rw [insert_stable_at_step_insert v (-11) 0 ((0:usize) + 1) acc1
      (by rw [h_idx_1]; decide) h_no_min_1 h_lt_1 h_acc_bound_1]
  -- new acc = ⟨#[-1, -11, 1], _⟩
  let acc2 := push_two acc1 (-11 : i64) (v.val[((0:usize) + 1).toNat]'(by rw [h_idx_1]; decide)) h_acc_bound_1
  -- i=2: done=true. Pass.
  have h_idx_2 : ((0:usize) + 1 + 1).toNat = 2 := by decide
  have h_v_2 : v.val[((0:usize) + 1 + 1).toNat]'(by rw [h_idx_2]; decide) = 11 := by
    show v.val[((0:usize) + 1 + 1).toNat] = 11
    congr 1
  have h_no_min_2 : (v.val[((0:usize) + 1 + 1).toNat]'(by rw [h_idx_2]; decide)) ≠ Int64.minValue := by
    rw [h_v_2]; decide
  have h_acc_bound_2 : acc2.val.size + 1 < USize64.size := by
    show (acc1.val ++ #[(-11 : i64), v.val[((0:usize) + 1).toNat]'(by rw [h_idx_1]; decide)]).size + 1 < USize64.size
    rw [Array.size_append]
    show acc1.val.size + 2 + 1 < USize64.size
    show (acc0.val ++ #[v.val[(0:usize).toNat]'(by show 0 < 3; decide)]).size + 2 + 1 < USize64.size
    rw [Array.size_append]; decide
  rw [insert_stable_at_step_pass v (-11) 0 ((0:usize) + 1 + 1) true acc2
      (by rw [h_idx_2]; decide) h_no_min_2 (Or.inl rfl) h_acc_bound_2]
  -- i=3: oob_done
  rw [insert_stable_at_oob_done v (-11) 0 ((0:usize) + 1 + 1 + 1) _
      (by
        have : ((0:usize) + 1 + 1 + 1).toNat = 3 := by decide
        rw [this]; decide)]
  rfl

/-- Step 5: insert 0 into ⟨#[-1, -11, 1, 11], _⟩. -/
private theorem ins_0 :
    clever_143_order_by_points.insert_stable
      (⟨#[-1, -11, 1, 11], by decide⟩ : alloc.vec.Vec i64 alloc.alloc.Global) 0
      = RustM.ok ⟨#[(-1 : i64), -11, 0, 1, 11], by decide⟩ := by
  unfold clever_143_order_by_points.insert_stable
  rw [sds_0]
  simp only [RustM_ok_bind]
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok (⟨#[], by decide⟩ : alloc.vec.Vec i64 alloc.alloc.Global) := rfl
  rw [h_new]
  simp only [RustM_ok_bind]
  let v : alloc.vec.Vec i64 alloc.alloc.Global := ⟨#[-1, -11, 1, 11], by decide⟩
  let acc0 : alloc.vec.Vec i64 alloc.alloc.Global := ⟨#[], by decide⟩
  -- i=0: vi=-1, key(-1)=-1. 0 > -1 true, but skip is "key(vi) ≤ kx", i.e. -1 ≤ 0. Pass.
  have h_v_0 : v.val[(0:usize).toNat]'(by show 0 < 4; decide) = -1 := rfl
  have h_no_min_0 : (v.val[(0:usize).toNat]'(by show 0 < 4; decide)) ≠ Int64.minValue := by
    rw [h_v_0]; decide
  have h_skip_0 : key (v.val[(0:usize).toNat]'(by show 0 < 4; decide)) ≤ (0 : i64).toInt := by
    rw [h_v_0, key_neg1, i64_zero_toInt]; decide
  have h_acc_bound_0 : acc0.val.size + 1 < USize64.size := by decide
  rw [insert_stable_at_step_pass v 0 0 0 false acc0
      (by show 0 < 4; decide) h_no_min_0 (Or.inr h_skip_0) h_acc_bound_0]
  let acc1 := push_one acc0 (v.val[(0:usize).toNat]'(by show 0 < 4; decide)) h_acc_bound_0
  -- i=1: vi=-11, key(-11)=0. 0 ≤ 0. Pass.
  have h_idx_1 : ((0:usize) + 1).toNat = 1 := by decide
  have h_v_1 : v.val[((0:usize) + 1).toNat]'(by rw [h_idx_1]; decide) = -11 := by
    show v.val[((0:usize) + 1).toNat] = -11
    congr 1
  have h_no_min_1 : (v.val[((0:usize) + 1).toNat]'(by rw [h_idx_1]; decide)) ≠ Int64.minValue := by
    rw [h_v_1]; decide
  have h_skip_1 : key (v.val[((0:usize) + 1).toNat]'(by rw [h_idx_1]; decide)) ≤ (0 : i64).toInt := by
    rw [h_v_1, key_neg11, i64_zero_toInt]
    decide
  have h_acc_bound_1 : acc1.val.size + 1 < USize64.size := by
    show (acc0.val ++ #[v.val[(0:usize).toNat]'(by show 0 < 4; decide)]).size + 1 < USize64.size
    rw [Array.size_append]; decide
  rw [insert_stable_at_step_pass v 0 0 ((0:usize) + 1) false acc1
      (by rw [h_idx_1]; decide) h_no_min_1 (Or.inr h_skip_1) h_acc_bound_1]
  let acc2 := push_one acc1 (v.val[((0:usize) + 1).toNat]'(by rw [h_idx_1]; decide)) h_acc_bound_1
  -- i=2: vi=1, key(1)=1. 0 < 1. Insert.
  have h_idx_2 : ((0:usize) + 1 + 1).toNat = 2 := by decide
  have h_v_2 : v.val[((0:usize) + 1 + 1).toNat]'(by rw [h_idx_2]; decide) = 1 := by
    show v.val[((0:usize) + 1 + 1).toNat] = 1
    congr 1
  have h_no_min_2 : (v.val[((0:usize) + 1 + 1).toNat]'(by rw [h_idx_2]; decide)) ≠ Int64.minValue := by
    rw [h_v_2]; decide
  have h_lt_2 : (0 : i64).toInt < key (v.val[((0:usize) + 1 + 1).toNat]'(by rw [h_idx_2]; decide)) := by
    rw [h_v_2, key_1, i64_zero_toInt]; decide
  have h_acc_bound_2 : acc2.val.size + 2 < USize64.size := by
    show (acc1.val ++ #[v.val[((0:usize) + 1).toNat]'(by rw [h_idx_1]; decide)]).size + 2 < USize64.size
    rw [Array.size_append]
    show acc1.val.size + 1 + 2 < USize64.size
    show (acc0.val ++ #[v.val[(0:usize).toNat]'(by show 0 < 4; decide)]).size + 1 + 2 < USize64.size
    rw [Array.size_append]; decide
  rw [insert_stable_at_step_insert v 0 0 ((0:usize) + 1 + 1) acc2
      (by rw [h_idx_2]; decide) h_no_min_2 h_lt_2 h_acc_bound_2]
  let acc3 := push_two acc2 (0 : i64) (v.val[((0:usize) + 1 + 1).toNat]'(by rw [h_idx_2]; decide)) h_acc_bound_2
  -- i=3: done=true. Pass.
  have h_idx_3 : ((0:usize) + 1 + 1 + 1).toNat = 3 := by decide
  have h_v_3 : v.val[((0:usize) + 1 + 1 + 1).toNat]'(by rw [h_idx_3]; decide) = 11 := by
    show v.val[((0:usize) + 1 + 1 + 1).toNat] = 11
    congr 1
  have h_no_min_3 : (v.val[((0:usize) + 1 + 1 + 1).toNat]'(by rw [h_idx_3]; decide)) ≠ Int64.minValue := by
    rw [h_v_3]; decide
  have h_acc_bound_3 : acc3.val.size + 1 < USize64.size := by
    show (acc2.val ++ #[(0 : i64), v.val[((0:usize) + 1 + 1).toNat]'(by rw [h_idx_2]; decide)]).size + 1 < USize64.size
    rw [Array.size_append]
    show acc2.val.size + 2 + 1 < USize64.size
    show (acc1.val ++ #[v.val[((0:usize) + 1).toNat]'(by rw [h_idx_1]; decide)]).size + 2 + 1 < USize64.size
    rw [Array.size_append]
    show acc1.val.size + 1 + 2 + 1 < USize64.size
    show (acc0.val ++ #[v.val[(0:usize).toNat]'(by show 0 < 4; decide)]).size + 1 + 2 + 1 < USize64.size
    rw [Array.size_append]; decide
  rw [insert_stable_at_step_pass v 0 0 ((0:usize) + 1 + 1 + 1) true acc3
      (by rw [h_idx_3]; decide) h_no_min_3 (Or.inl rfl) h_acc_bound_3]
  -- i=4: oob_done.
  rw [insert_stable_at_oob_done v 0 0 ((0:usize) + 1 + 1 + 1 + 1) _
      (by
        have : ((0:usize) + 1 + 1 + 1 + 1).toNat = 4 := by decide
        rw [this]; decide)]
  rfl

theorem order_by_points_known :
    clever_143_order_by_points.order_by_points
        { val := #[(1 : i64), 11, -1, -11, 0], size_lt_usizeSize := by decide }
      = RustM.ok ⟨#[(-1 : i64), -11, 0, 1, 11], by decide⟩ := by
  unfold clever_143_order_by_points.order_by_points
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok (⟨#[], by decide⟩ : alloc.vec.Vec i64 alloc.alloc.Global) := rfl
  rw [h_new]
  simp only [RustM_ok_bind]
  -- The input list.
  let l : RustSlice i64 := { val := #[(1 : i64), 11, -1, -11, 0], size_lt_usizeSize := by decide }
  show clever_143_order_by_points.sort_at l 0 ⟨#[], by decide⟩
        = RustM.ok ⟨#[(-1 : i64), -11, 0, 1, 11], by decide⟩
  -- Step 1: sort_at l 0 acc = insert_stable acc l[0]=1 >>= sort_at l 1
  rw [sort_at_step l 0 _ (by show 0 < 5; decide)]
  show (do let acc' ← clever_143_order_by_points.insert_stable
              (⟨#[], by decide⟩ : alloc.vec.Vec i64 alloc.alloc.Global) (l.val[(0:usize).toNat]'(by show 0 < 5; decide))
           clever_143_order_by_points.sort_at l ((0:usize) + 1) acc') =
        RustM.ok ⟨#[(-1 : i64), -11, 0, 1, 11], by decide⟩
  have h_l_0 : l.val[(0:usize).toNat]'(by show 0 < 5; decide) = 1 := rfl
  rw [h_l_0, ins_1]
  simp only [RustM_ok_bind]
  -- Step 2: sort_at l 1 ⟨#[1], _⟩ = insert_stable ⟨#[1], _⟩ l[1]=11 >>= sort_at l 2
  have h_idx_1 : ((0:usize) + 1).toNat = 1 := by decide
  have h_l_1_pos : ((0:usize) + 1).toNat < l.val.size := by rw [h_idx_1]; show 1 < 5; decide
  rw [sort_at_step l ((0:usize) + 1) _ h_l_1_pos]
  have h_l_1 : l.val[((0:usize) + 1).toNat]'h_l_1_pos = 11 := by
    show l.val[((0:usize) + 1).toNat] = 11
    congr 1
  rw [h_l_1, ins_11]
  simp only [RustM_ok_bind]
  -- Step 3: sort_at l 2 ⟨#[1, 11], _⟩ = insert_stable ... l[2]=-1 >>= sort_at l 3
  have h_idx_2 : ((0:usize) + 1 + 1).toNat = 2 := by decide
  have h_l_2_pos : ((0:usize) + 1 + 1).toNat < l.val.size := by rw [h_idx_2]; show 2 < 5; decide
  rw [sort_at_step l ((0:usize) + 1 + 1) _ h_l_2_pos]
  have h_l_2 : l.val[((0:usize) + 1 + 1).toNat]'h_l_2_pos = -1 := by
    show l.val[((0:usize) + 1 + 1).toNat] = -1
    congr 1
  rw [h_l_2, ins_neg1]
  simp only [RustM_ok_bind]
  -- Step 4: sort_at l 3 ⟨#[-1, 1, 11], _⟩ = insert_stable ... l[3]=-11 >>= sort_at l 4
  have h_idx_3 : ((0:usize) + 1 + 1 + 1).toNat = 3 := by decide
  have h_l_3_pos : ((0:usize) + 1 + 1 + 1).toNat < l.val.size := by rw [h_idx_3]; show 3 < 5; decide
  rw [sort_at_step l ((0:usize) + 1 + 1 + 1) _ h_l_3_pos]
  have h_l_3 : l.val[((0:usize) + 1 + 1 + 1).toNat]'h_l_3_pos = -11 := by
    show l.val[((0:usize) + 1 + 1 + 1).toNat] = -11
    congr 1
  rw [h_l_3, ins_neg11]
  simp only [RustM_ok_bind]
  -- Step 5: sort_at l 4 ⟨#[-1, -11, 1, 11], _⟩ = insert_stable ... l[4]=0 >>= sort_at l 5
  have h_idx_4 : ((0:usize) + 1 + 1 + 1 + 1).toNat = 4 := by decide
  have h_l_4_pos : ((0:usize) + 1 + 1 + 1 + 1).toNat < l.val.size := by rw [h_idx_4]; show 4 < 5; decide
  rw [sort_at_step l ((0:usize) + 1 + 1 + 1 + 1) _ h_l_4_pos]
  have h_l_4 : l.val[((0:usize) + 1 + 1 + 1 + 1).toNat]'h_l_4_pos = 0 := by
    show l.val[((0:usize) + 1 + 1 + 1 + 1).toNat] = 0
    congr 1
  rw [h_l_4, ins_0]
  simp only [RustM_ok_bind]
  -- Step 6: sort_at l 5 = OOB
  have h_idx_5 : ((0:usize) + 1 + 1 + 1 + 1 + 1).toNat = 5 := by decide
  rw [sort_at_oob l ((0:usize) + 1 + 1 + 1 + 1 + 1) _
      (by rw [h_idx_5]; show 5 ≤ 5; exact Nat.le_refl 5)]

end Clever_143_order_by_pointsObligations
