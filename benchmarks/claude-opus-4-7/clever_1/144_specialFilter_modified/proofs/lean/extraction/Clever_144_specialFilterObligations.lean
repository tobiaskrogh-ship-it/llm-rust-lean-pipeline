-- Companion obligations file for the `clever_144_specialFilter` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_144_specialFilter

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_144_specialFilterObligations

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
private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide

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

/-! ## Reductions for primitive ops on `i64` with constant divisors. -/

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

private theorem i64_mod_2 (n : i64) :
    (n %? (2 : i64) : RustM i64) = pure (n % 2) := by
  show (rust_primitives.ops.arith.Rem.rem n (2 : i64) : RustM i64) = pure (n % 2)
  show (if n = Int64.minValue && (2 : i64) = -1 then
          (.fail .integerOverflow : RustM i64)
        else if (2 : i64) = 0 then .fail .divisionByZero
        else pure (n % 2)) = pure (n % 2)
  have h_and : (n = Int64.minValue && ((2 : i64) = -1)) = false := by
    show (decide (n = Int64.minValue) && decide ((2 : i64) = -1)) = false
    rw [show decide ((2 : i64) = -1) = false from by decide, Bool.and_false]
  rw [h_and, if_neg (by decide : (2 : i64) ≠ 0)]; rfl

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

/-! ## Bridging Int and Nat for n / 10 and n % 10 (non-negative). -/

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

private theorem i64_mod_2_toInt (n : i64) (hn : 0 ≤ n.toInt) :
    (n % (2 : i64)).toInt = n.toInt % 2 := by
  have h_tmod : (n % (2 : i64)).toInt = n.toInt.tmod 2 :=
    Int64.toInt_mod n 2
  rw [h_tmod, Int.tmod_eq_emod_of_nonneg hn]

private theorem i64_div_10_nonneg (n : i64) (hn : 0 ≤ n.toInt) :
    0 ≤ (n / (10 : i64)).toInt := by
  rw [i64_div_10_toInt n hn]
  exact Int.ediv_nonneg hn (by decide)

private theorem i64_mod_10_nonneg (n : i64) (hn : 0 ≤ n.toInt) :
    0 ≤ (n % (10 : i64)).toInt := by
  rw [i64_mod_10_toInt n hn]
  exact Int.emod_nonneg n.toInt (by decide)

/-! ## Nat-level oracle for the leading decimal digit. -/

private def first_digit_nat (n : Nat) : Nat :=
  if n < 10 then n else first_digit_nat (n / 10)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

private theorem first_digit_nat_small (n : Nat) (h : n < 10) :
    first_digit_nat n = n := by
  unfold first_digit_nat; rw [if_pos h]

private theorem first_digit_nat_large (n : Nat) (h : ¬ n < 10) :
    first_digit_nat n = first_digit_nat (n / 10) := by
  conv => lhs; unfold first_digit_nat
  rw [if_neg h]

private theorem first_digit_nat_lt_10 (n : Nat) : first_digit_nat n < 10 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n < 10
    · rw [first_digit_nat_small n h]; exact h
    · rw [first_digit_nat_large n h]
      apply ih
      have hn_pos : 0 < n := by omega
      exact Nat.div_lt_self hn_pos (by decide)

/-! ## Reference predicate. -/

private abbrev qualifies_int (n : Int) : Prop :=
  10 < n ∧ (first_digit_nat n.toNat) % 2 = 1 ∧ n % 10 % 2 = 1

/-! ## Pointwise correctness of `first_digit_at` on non-negative inputs. -/

private theorem first_digit_at_correct (n : i64) (hn : 0 ≤ n.toInt) :
    ∃ r : i64,
      clever_144_specialFilter.first_digit_at n = RustM.ok r ∧
      r.toInt = (first_digit_nat n.toInt.toNat : Int) ∧
      0 ≤ r.toInt ∧
      r.toInt ≤ 9 := by
  induction hk : n.toInt.toNat using Nat.strongRecOn generalizing n with
  | _ k ih =>
    unfold clever_144_specialFilter.first_digit_at
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

/-! ## Bridging the i64-level boolean predicate to `qualifies_int`. -/

/-- When `0 ≤ a.toInt`, the compound i64 boolean
    `(fd % 2 == 1) && ((a % 10) % 2 == 1)` is `true` iff both `Int.emod`-level
    parities are `1`. -/
private theorem bool_compound_iff
    (a fd : i64) (h_v_nn : 0 ≤ a.toInt) (h_fd_nn : 0 ≤ fd.toInt) :
    (((fd % 2) == (1 : i64)) && (((a % 10) % 2) == (1 : i64))) = true ↔
    (fd.toInt % 2 = 1 ∧ a.toInt % 10 % 2 = 1) := by
  have h_a_mod_10_toInt' : (a % 10).toInt = a.toInt % 10 := i64_mod_10_toInt a h_v_nn
  have h_a_mod_10_nn : 0 ≤ (a % 10).toInt := i64_mod_10_nonneg a h_v_nn
  have h_fd_mod_2_toInt' : (fd % 2).toInt = fd.toInt % 2 := i64_mod_2_toInt fd h_fd_nn
  have h_a_mod_10_mod_2_toInt :
      ((a % 10) % 2).toInt = (a % 10).toInt % 2 := i64_mod_2_toInt (a % 10) h_a_mod_10_nn
  have h_fd_eq_iff : (fd % 2) = (1 : i64) ↔ fd.toInt % 2 = 1 := by
    constructor
    · intro h
      have : (fd % 2).toInt = (1 : i64).toInt := by rw [h]
      rw [h_fd_mod_2_toInt', i64_one_toInt] at this; exact this
    · intro h
      apply Int64.toInt_inj.mp
      rw [h_fd_mod_2_toInt', i64_one_toInt]; exact h
  have h_last_eq_iff : ((a % 10) % 2) = (1 : i64) ↔ a.toInt % 10 % 2 = 1 := by
    constructor
    · intro h
      have : ((a % 10) % 2).toInt = (1 : i64).toInt := by rw [h]
      rw [h_a_mod_10_mod_2_toInt, h_a_mod_10_toInt', i64_one_toInt] at this; exact this
    · intro h
      apply Int64.toInt_inj.mp
      rw [h_a_mod_10_mod_2_toInt, h_a_mod_10_toInt', i64_one_toInt]; exact h
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq, h_fd_eq_iff, h_last_eq_iff]

/-- Given `10 < a.toInt` and `fd.toInt = first_digit_nat a.toInt.toNat`,
    the Int-level conjunction matches `qualifies_int a.toInt`. -/
private theorem qualifies_iff_pair
    (a fd : i64)
    (h_v_pos_int : (10 : Int) < a.toInt)
    (h_fd_int : fd.toInt = (first_digit_nat a.toInt.toNat : Int)) :
    (fd.toInt % 2 = 1 ∧ a.toInt % 10 % 2 = 1) ↔ qualifies_int a.toInt := by
  constructor
  · intro ⟨h1, h2⟩
    refine ⟨h_v_pos_int, ?_, h2⟩
    have h_int_eq : (first_digit_nat a.toInt.toNat : Int) % 2 = 1 := by
      rw [← h_fd_int]; exact h1
    have h_cast : ((first_digit_nat a.toInt.toNat : Int) % 2)
        = ((first_digit_nat a.toInt.toNat % 2 : Nat) : Int) := by push_cast; rfl
    rw [h_cast] at h_int_eq
    exact Int.ofNat.inj h_int_eq
  · intro ⟨_, h_fd_odd, h_last_odd⟩
    refine ⟨?_, h_last_odd⟩
    rw [h_fd_int]
    have h_cast : ((first_digit_nat a.toInt.toNat : Int) % 2)
        = ((first_digit_nat a.toInt.toNat % 2 : Nat) : Int) := by push_cast; rfl
    rw [h_cast, h_fd_odd]; rfl

/-! ## Nat-level prefix count oracle. -/

private def pos_count_pref (arr : Array i64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      pos_count_pref arr k +
        (if h : k < arr.size then
           (if qualifies_int (arr[k]'h).toInt then 1 else 0)
         else 0)

private theorem pos_count_pref_succ_in (arr : Array i64) (k : Nat) (h : k < arr.size) :
    pos_count_pref arr (k + 1) =
      pos_count_pref arr k +
        (if qualifies_int (arr[k]'h).toInt then 1 else 0) := by
  show pos_count_pref arr k +
      (if h : k < arr.size then
         (if qualifies_int (arr[k]'h).toInt then 1 else 0)
       else 0)
    = pos_count_pref arr k +
      (if qualifies_int (arr[k]'h).toInt then 1 else 0)
  rw [dif_pos h]

private theorem pos_count_pref_le (arr : Array i64) :
    ∀ k, pos_count_pref arr k ≤ k := by
  intro k
  induction k with
  | zero => simp [pos_count_pref]
  | succ k ih =>
    show pos_count_pref arr k +
        (if h : k < arr.size then
           (if qualifies_int (arr[k]'h).toInt then 1 else 0)
         else 0) ≤ k + 1
    by_cases hk : k < arr.size
    · rw [dif_pos hk]
      by_cases hpos : qualifies_int (arr[k]'hk).toInt
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
    clever_144_specialFilter.count_at arr i acc = RustM.ok acc := by
  conv => lhs; unfold clever_144_specialFilter.count_at
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
    (h_size : (arr.val.size : Int) < 2^63) :
    ∀ (m : Nat) (i : usize) (acc : i64),
      arr.val.size - i.toNat ≤ m →
      i.toNat ≤ arr.val.size →
      0 ≤ acc.toInt →
      acc.toInt + ((arr.val.size : Int) - (i.toNat : Int)) < 2^63 →
      ∃ r : i64,
        clever_144_specialFilter.count_at arr i acc = RustM.ok r ∧
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
    · have h_i_eq : i.toNat = arr.val.size := by omega
      refine ⟨acc, count_at_oob arr i acc h_i_ge, ?_⟩
      rw [h_i_eq]; omega
    · have h_i_lt : i.toNat < arr.val.size := by omega
      have h_size_lt : arr.val.size < 2^64 := arr.size_lt_usizeSize
      have h_ofNat : (USize64.ofNat arr.val.size).toNat = arr.val.size :=
        USize64.toNat_ofNat_of_lt' h_size_lt
      let a : i64 := arr.val[i.toNat]'h_i_lt
      have h_a_def : a = arr.val[i.toNat]'h_i_lt := rfl
      -- Unfold count_at
      unfold clever_144_specialFilter.count_at
      have h_cond : decide (USize64.ofNat arr.val.size ≤ i) = false := by
        rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]
        omega
      simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
                 rust_primitives.cmp.ge, pure_bind, h_cond, Bool.false_eq_true,
                 ↓reduceIte]
      -- arr[i]_? = ok a
      have h_idx : (arr[i]_? : RustM i64) = RustM.ok a := by
        show (if h : i.toNat < arr.val.size then pure (arr.val[i])
              else .fail .arrayOutOfBounds)
            = RustM.ok a
        rw [dif_pos h_i_lt]; rfl
      rw [h_idx]
      simp only [RustM_ok_bind]
      -- i +? 1 — no overflow
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
      -- Pos count step bridge
      have h_pos_count_step :
          (pos_count_pref arr.val (i.toNat + 1) : Int) =
            (pos_count_pref arr.val i.toNat : Int) +
              (if qualifies_int a.toInt then 1 else 0) := by
        rw [pos_count_pref_succ_in arr.val i.toNat h_i_lt, h_a_def]
        push_cast
        split <;> simp
      by_cases h_v_gt : (10 : i64) < a
      · -- v > 10 branch
        have h_v_pos_int : (10 : Int) < a.toInt := by
          have := Int64.lt_iff_toInt_lt.mp h_v_gt
          simpa [i64_ten_toInt] using this
        have h_v_nn : 0 ≤ a.toInt := by omega
        have h_dec_gt : decide ((10 : i64) < a) = true := decide_eq_true h_v_gt
        simp only [show (a >? (10 : i64) : RustM Bool) =
                     (pure (decide ((10 : i64) < a)) : RustM Bool) from rfl,
                   h_dec_gt, pure_bind, ↓reduceIte]
        obtain ⟨fd, h_fd_eq, h_fd_int, h_fd_nn, h_fd_le_9⟩ :=
          first_digit_at_correct a h_v_nn
        rw [h_fd_eq]
        simp only [RustM_ok_bind]
        rw [i64_mod_10 a, pure_bind]
        rw [i64_mod_2 fd, pure_bind]
        have h_eq_first : ((fd % 2) ==? (1 : i64) : RustM Bool) =
            pure ((fd % 2) == (1 : i64)) := rfl
        rw [h_eq_first, pure_bind]
        rw [i64_mod_2 (a % 10), pure_bind]
        have h_eq_last : (((a % 10) % 2) ==? (1 : i64) : RustM Bool) =
            pure (((a % 10) % 2) == (1 : i64)) := rfl
        rw [h_eq_last, pure_bind]
        simp only [rust_primitives.hax.logical_op.and, pure_bind]
        -- Bridge the boolean conjunction to qualifies_int.
        have h_bool_iff := bool_compound_iff a fd h_v_nn h_fd_nn
        have h_pair_iff := qualifies_iff_pair a fd h_v_pos_int h_fd_int
        by_cases h_q : qualifies_int a.toInt
        · -- Predicate fires
          have h_pair := h_pair_iff.mpr h_q
          have h_bool_true :
              (((fd % 2) == (1 : i64)) && (((a % 10) % 2) == (1 : i64))) = true :=
            h_bool_iff.mpr h_pair
          rw [h_bool_true]
          simp only [↓reduceIte]
          rw [h_i1_pure]
          simp only [pure_bind]
          have h_acc1_bound : acc.toInt + 1 < 2^63 := by
            have h_pos_count_le : pos_count_pref arr.val (i.toNat + 1) ≤ i.toNat + 1 :=
              pos_count_pref_le arr.val (i.toNat + 1)
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
            rw [h_pos_count_step, if_pos h_q]
          rw [h_pc_step]; omega
        · -- Predicate doesn't fire
          have h_pair_false : ¬ (fd.toInt % 2 = 1 ∧ a.toInt % 10 % 2 = 1) :=
            fun hp => h_q (h_pair_iff.mp hp)
          have h_bool_false :
              (((fd % 2) == (1 : i64)) && (((a % 10) % 2) == (1 : i64))) = false := by
            cases hb : (((fd % 2) == (1 : i64)) && (((a % 10) % 2) == (1 : i64))) with
            | false => rfl
            | true => exfalso; exact h_pair_false (h_bool_iff.mp hb)
          rw [h_bool_false]
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
            rw [h_pos_count_step, if_neg h_q]; omega
          rw [h_pc_step]
      · -- v ≤ 10 branch
        have h_a_le_10 : a.toInt ≤ 10 := by
          have h_not : ¬ (10 : Int) < a.toInt := by
            intro hh; apply h_v_gt
            rw [Int64.lt_iff_toInt_lt, i64_ten_toInt]; exact hh
          omega
        have h_dec_gt : decide ((10 : i64) < a) = false := decide_eq_false h_v_gt
        simp only [show (a >? (10 : i64) : RustM Bool) =
                     (pure (decide ((10 : i64) < a)) : RustM Bool) from rfl,
                   h_dec_gt, pure_bind, Bool.false_eq_true, ↓reduceIte]
        rw [h_i1_pure]
        simp only [pure_bind]
        have h_not_q : ¬ qualifies_int a.toInt := by
          intro ⟨h_gt, _, _⟩; omega
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
          rw [h_pos_count_step, if_neg h_not_q]; omega
        rw [h_pc_step]

/-! ## Obligation theorems. -/

theorem specialFilter_empty
    (nums : RustSlice i64) (h_empty : nums.val.size = 0) :
    clever_144_specialFilter.specialFilter nums = RustM.ok (0 : i64) := by
  unfold clever_144_specialFilter.specialFilter
  have hi_ge : nums.val.size ≤ (0 : usize).toNat := by
    rw [usize_zero_toNat, h_empty]; exact Nat.le_refl 0
  exact count_at_oob nums (0 : usize) (0 : i64) hi_ge

theorem specialFilter_nonneg
    (nums : RustSlice i64) (h_size : (nums.val.size : Int) < 2^63) :
    ∃ r : i64,
      clever_144_specialFilter.specialFilter nums = RustM.ok r ∧ 0 ≤ r.toInt := by
  unfold clever_144_specialFilter.specialFilter
  have h_init_bound : (0 : i64).toInt + ((nums.val.size : Int) - ((0 : usize).toNat : Int)) < 2^63 := by
    rw [i64_zero_toInt, usize_zero_toNat]; push_cast; omega
  obtain ⟨r, h_eq, h_int⟩ :=
    count_at_correct nums h_size nums.val.size (0 : usize) (0 : i64)
      (by rw [usize_zero_toNat]; omega)
      (by rw [usize_zero_toNat]; omega)
      (by rw [i64_zero_toInt]; exact Int.le_refl 0)
      h_init_bound
  refine ⟨r, h_eq, ?_⟩
  rw [h_int, i64_zero_toInt, usize_zero_toNat]
  have h_pc_zero : pos_count_pref nums.val 0 = 0 := by simp [pos_count_pref]
  rw [h_pc_zero]
  have h_pc_nn : (0 : Int) ≤ (pos_count_pref nums.val nums.val.size : Int) := Int.natCast_nonneg _
  omega

theorem specialFilter_le_size
    (nums : RustSlice i64) (h_size : (nums.val.size : Int) < 2^63) :
    ∃ r : i64,
      clever_144_specialFilter.specialFilter nums = RustM.ok r
      ∧ r.toInt ≤ (nums.val.size : Int) := by
  unfold clever_144_specialFilter.specialFilter
  have h_init_bound : (0 : i64).toInt + ((nums.val.size : Int) - ((0 : usize).toNat : Int)) < 2^63 := by
    rw [i64_zero_toInt, usize_zero_toNat]; push_cast; omega
  obtain ⟨r, h_eq, h_int⟩ :=
    count_at_correct nums h_size nums.val.size (0 : usize) (0 : i64)
      (by rw [usize_zero_toNat]; omega)
      (by rw [usize_zero_toNat]; omega)
      (by rw [i64_zero_toInt]; exact Int.le_refl 0)
      h_init_bound
  refine ⟨r, h_eq, ?_⟩
  rw [h_int, i64_zero_toInt, usize_zero_toNat]
  have h_pc_zero : pos_count_pref nums.val 0 = 0 := by simp [pos_count_pref]
  rw [h_pc_zero]
  have h_pc_le : (pos_count_pref nums.val nums.val.size : Int) ≤ (nums.val.size : Int) := by
    have : pos_count_pref nums.val nums.val.size ≤ nums.val.size :=
      pos_count_pref_le nums.val nums.val.size
    exact_mod_cast this
  omega

theorem specialFilter_additive
    (a b c : RustSlice i64)
    (h_concat : c.val = a.val ++ b.val)
    (h_c_size : (c.val.size : Int) < 2^63) :
    ∃ ra rb rc : i64,
      clever_144_specialFilter.specialFilter a = RustM.ok ra
      ∧ clever_144_specialFilter.specialFilter b = RustM.ok rb
      ∧ clever_144_specialFilter.specialFilter c = RustM.ok rc
      ∧ rc.toInt = ra.toInt + rb.toInt := by
  have h_size_eq : c.val.size = a.val.size + b.val.size := aux_concat_size h_concat
  have h_a_size : (a.val.size : Int) < 2^63 := by
    have : a.val.size ≤ c.val.size := by omega
    have h : (a.val.size : Int) ≤ (c.val.size : Int) := by exact_mod_cast this
    omega
  have h_b_size : (b.val.size : Int) < 2^63 := by
    have : b.val.size ≤ c.val.size := by omega
    have h : (b.val.size : Int) ≤ (c.val.size : Int) := by exact_mod_cast this
    omega
  have h_init_bound_a : (0 : i64).toInt + ((a.val.size : Int) - ((0 : usize).toNat : Int)) < 2^63 := by
    rw [i64_zero_toInt, usize_zero_toNat]; push_cast; omega
  have h_init_bound_b : (0 : i64).toInt + ((b.val.size : Int) - ((0 : usize).toNat : Int)) < 2^63 := by
    rw [i64_zero_toInt, usize_zero_toNat]; push_cast; omega
  have h_init_bound_c : (0 : i64).toInt + ((c.val.size : Int) - ((0 : usize).toNat : Int)) < 2^63 := by
    rw [i64_zero_toInt, usize_zero_toNat]; push_cast; omega
  obtain ⟨ra, h_a_eq, h_a_int⟩ :=
    count_at_correct a h_a_size a.val.size (0 : usize) (0 : i64)
      (by rw [usize_zero_toNat]; omega)
      (by rw [usize_zero_toNat]; omega)
      (by rw [i64_zero_toInt]; exact Int.le_refl 0)
      h_init_bound_a
  obtain ⟨rb, h_b_eq, h_b_int⟩ :=
    count_at_correct b h_b_size b.val.size (0 : usize) (0 : i64)
      (by rw [usize_zero_toNat]; omega)
      (by rw [usize_zero_toNat]; omega)
      (by rw [i64_zero_toInt]; exact Int.le_refl 0)
      h_init_bound_b
  obtain ⟨rc, h_c_eq, h_c_int⟩ :=
    count_at_correct c h_c_size c.val.size (0 : usize) (0 : i64)
      (by rw [usize_zero_toNat]; omega)
      (by rw [usize_zero_toNat]; omega)
      (by rw [i64_zero_toInt]; exact Int.le_refl 0)
      h_init_bound_c
  refine ⟨ra, rb, rc, ?_, ?_, ?_, ?_⟩
  · unfold clever_144_specialFilter.specialFilter; exact h_a_eq
  · unfold clever_144_specialFilter.specialFilter; exact h_b_eq
  · unfold clever_144_specialFilter.specialFilter; exact h_c_eq
  · have h_pc_zero : ∀ arr : Array i64, pos_count_pref arr 0 = 0 := by intro; simp [pos_count_pref]
    have h_pc_additive :
        pos_count_pref c.val c.val.size =
          pos_count_pref a.val a.val.size + pos_count_pref b.val b.val.size := by
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
      rw [h_size_eq]
      exact h_right b.val.size (Nat.le_refl _)
    rw [h_a_int, h_b_int, h_c_int]
    rw [i64_zero_toInt, usize_zero_toNat]
    have h_pc_zero_a : pos_count_pref a.val 0 = 0 := h_pc_zero a.val
    have h_pc_zero_b : pos_count_pref b.val 0 = 0 := h_pc_zero b.val
    have h_pc_zero_c : pos_count_pref c.val 0 = 0 := h_pc_zero c.val
    rw [h_pc_zero_a, h_pc_zero_b, h_pc_zero_c]
    rw [h_pc_additive]
    push_cast; omega

theorem specialFilter_singleton_matches_predicate (v : i64) :
    clever_144_specialFilter.specialFilter
        { val := #[v],
          size_lt_usizeSize := by show (1 : Nat) < USize64.size; decide }
      = RustM.ok (if qualifies_int v.toInt then (1 : i64) else (0 : i64)) := by
  let s : RustSlice i64 := { val := #[v],
                              size_lt_usizeSize := by show (1 : Nat) < USize64.size; decide }
  have h_size : s.val.size = 1 := by show (#[v] : Array i64).size = 1; rfl
  have h_size_int : (s.val.size : Int) < 2^63 := by rw [h_size]; decide
  have h_init_bound : (0 : i64).toInt + ((s.val.size : Int) - ((0 : usize).toNat : Int)) < 2^63 := by
    rw [i64_zero_toInt, usize_zero_toNat, h_size]; decide
  obtain ⟨r, h_eq, h_int⟩ :=
    count_at_correct s h_size_int s.val.size (0 : usize) (0 : i64)
      (by rw [usize_zero_toNat]; omega)
      (by rw [usize_zero_toNat]; omega)
      (by rw [i64_zero_toInt]; exact Int.le_refl 0)
      h_init_bound
  show clever_144_specialFilter.specialFilter s = _
  unfold clever_144_specialFilter.specialFilter
  have h0_lt : 0 < s.val.size := by
    show 0 < s.val.size; rw [h_size]; exact Nat.zero_lt_one
  have h_v_idx : s.val[0]'h0_lt = v := by
    show (#[v] : Array i64)[0]'(Nat.zero_lt_one) = v; rfl
  have h_pc_0 : pos_count_pref s.val 0 = 0 := by simp [pos_count_pref]
  have h_pc_1 : pos_count_pref s.val 1 =
      (if qualifies_int v.toInt then 1 else 0) := by
    rw [pos_count_pref_succ_in s.val 0 h0_lt, h_pc_0, h_v_idx, Nat.zero_add]
  have h_r_eq : r = if qualifies_int v.toInt then (1 : i64) else (0 : i64) := by
    apply Int64.toInt_inj.mp
    rw [h_int, i64_zero_toInt, usize_zero_toNat, h_pc_0, h_size, h_pc_1]
    by_cases h : qualifies_int v.toInt
    · rw [if_pos h, if_pos h, i64_one_toInt]
      omega
    · rw [if_neg h, if_neg h, i64_zero_toInt]
      omega
  rw [← h_r_eq]; exact h_eq

end Clever_144_specialFilterObligations
