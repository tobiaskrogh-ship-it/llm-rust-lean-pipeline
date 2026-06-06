-- Companion obligations file for the `clever_004_mean_absolute_deviation` extraction.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_004_mean_absolute_deviation

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_004_mean_absolute_deviationObligations

/-! ## Integer-valued oracles -/

private def prefix_sum_int (numbers : RustSlice i64) : Nat → Int
  | 0     => 0
  | k + 1 =>
      prefix_sum_int numbers k +
        (if h : k < numbers.val.size then (numbers.val[k]'h).toInt else 0)

/-- `mean_int` uses `Int.tdiv` (truncation toward zero), exactly matching Rust's
    `i64 /` semantics. Lean 4 core's `(·/·) : Int → Int → Int` is `Int.ediv`
    (Euclidean), which differs from Rust's tdiv on negative numerators — so we
    cannot use `/` here, only for the final result equation where the numerator
    is a non-negative sum of `natAbs`s. -/
private def mean_int (numbers : RustSlice i64) : Int :=
  Int.tdiv (prefix_sum_int numbers numbers.val.size) (numbers.val.size : Int)

private def prefix_abs_dev_sum_int (numbers : RustSlice i64) (mean : Int) : Nat → Int
  | 0     => 0
  | k + 1 =>
      prefix_abs_dev_sum_int numbers mean k +
        (if h : k < numbers.val.size then
           (((numbers.val[k]'h).toInt - mean).natAbs : Int)
         else 0)

/-! ## Helpers -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide

private theorem i64_neg_one_toInt : (-1 : i64).toInt = -1 := by decide

/-- `Nat.toInt64` of a Nat below `2^63` interprets back to the same Int. -/
private theorem Nat_toInt64_toInt (n : Nat) (h : n < 2^63) :
    (n.toInt64).toInt = (n : Int) := by
  have h_n_lt_2_64 : n < 2^64 := Nat.lt_trans h (by decide)
  have h_bv_toNat : n.toInt64.toBitVec.toNat = n := by
    show (BitVec.ofNat 64 n).toNat = n
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt h_n_lt_2_64
  rw [Int64.toInt, BitVec.toInt_eq_toNat_bmod, h_bv_toNat]
  -- Goal: (↑n).bmod (2^64) = ↑n
  -- Unfold bmod: it's `let r := x % m; if r < (m+1)/2 then r else r - m`.
  unfold Int.bmod
  have h_mod : ((n : Int) % ((2^64 : Nat) : Int)) = (n : Int) := by
    rw [show (((2^64 : Nat)) : Int) = (2^64 : Int) from by norm_cast]
    exact Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le _)
                            (by exact_mod_cast (Nat.lt_trans h (by decide : (2^63 : Nat) < 2^64)))
  rw [h_mod]
  -- The `have r := ↑n` is just a `let`. Use `show` to expand it.
  show (if (n : Int) < (((2^64 : Nat) : Int) + 1) / 2 then (n : Int) else (n : Int) - ((2^64 : Nat) : Int)) = (n : Int)
  have h_half_eq : (((2^64 : Nat) : Int) + 1) / 2 = 2^63 := by decide
  rw [h_half_eq]
  have h_cond : (n : Int) < (2^63 : Int) := by exact_mod_cast h
  rw [if_pos h_cond]

/-- The cast `(USize64.ofNat n).toInt64.toInt = n` when `n < 2^63`. -/
private theorem usize_ofNat_toInt64_toInt (n : Nat) (h : n < 2^63) :
    ((USize64.ofNat n).toInt64).toInt = (n : Int) := by
  have h_n_lt_2_64 : n < 2^64 := Nat.lt_trans h (by decide)
  show ((USize64.ofNat n).toNat.toInt64).toInt = (n : Int)
  rw [USize64.toNat_ofNat_of_lt' h_n_lt_2_64]
  exact Nat_toInt64_toInt n h

/-- Division `n /? p` is `pure (n / p)` when `0 < p.toInt`. -/
private theorem i64_div_pure (n p : i64) (hp_pos : 0 < p.toInt) :
    (n /? p : RustM i64) = pure (n / p) := by
  show (rust_primitives.ops.arith.Div.div n p : RustM i64) = pure (n / p)
  show (if n = Int64.minValue && p = -1 then
          (.fail .integerOverflow : RustM i64)
        else if p = 0 then .fail .divisionByZero
        else pure (n / p)) = pure (n / p)
  have hp_ne_neg_one : p ≠ (-1 : i64) := by
    intro h_eq
    have : p.toInt = -1 := by rw [h_eq, i64_neg_one_toInt]
    omega
  have hp_ne_zero : p ≠ (0 : i64) := by
    intro h_eq
    have : p.toInt = 0 := by rw [h_eq, i64_zero_toInt]
    omega
  have h_and : (n = Int64.minValue && p = -1) = false := by
    rcases Decidable.em (n = Int64.minValue) with hn | hn
    · simp [hn, hp_ne_neg_one]
    · simp [hn]
  rw [h_and, if_neg hp_ne_zero]
  rfl

/-- `(n / p).toInt = n.toInt.tdiv p.toInt` when `0 < p.toInt`. -/
private theorem i64_toInt_div_tdiv (n p : i64) (hp_pos : 0 < p.toInt) :
    (n / p).toInt = n.toInt.tdiv p.toInt := by
  have hp_ne_neg_one : p ≠ (-1 : i64) := by
    intro h_eq
    have : p.toInt = -1 := by rw [h_eq, i64_neg_one_toInt]
    omega
  exact Int64.toInt_div_of_ne_right n p hp_ne_neg_one

/-- Step of `prefix_sum_int`. -/
private theorem prefix_sum_int_succ
    (numbers : RustSlice i64) (k : Nat) (hk : k < numbers.val.size) :
    prefix_sum_int numbers (k + 1) =
      prefix_sum_int numbers k + (numbers.val[k]'hk).toInt := by
  show prefix_sum_int numbers k
        + (if h : k < numbers.val.size then (numbers.val[k]'h).toInt else 0)
       = prefix_sum_int numbers k + (numbers.val[k]'hk).toInt
  rw [dif_pos hk]

/-- Step of `prefix_abs_dev_sum_int`. -/
private theorem prefix_abs_dev_sum_int_succ
    (numbers : RustSlice i64) (mean : Int)
    (k : Nat) (hk : k < numbers.val.size) :
    prefix_abs_dev_sum_int numbers mean (k + 1) =
      prefix_abs_dev_sum_int numbers mean k +
        (((numbers.val[k]'hk).toInt - mean).natAbs : Int) := by
  show prefix_abs_dev_sum_int numbers mean k
        + (if h : k < numbers.val.size then
             (((numbers.val[k]'h).toInt - mean).natAbs : Int)
           else 0)
       = prefix_abs_dev_sum_int numbers mean k +
           (((numbers.val[k]'hk).toInt - mean).natAbs : Int)
  rw [dif_pos hk]

/-! ## Step lemmas for `sum_from` -/

private theorem sum_from_oob (numbers : RustSlice i64) (i : usize)
    (hi : numbers.val.size ≤ i.toNat) :
    clever_004_mean_absolute_deviation.sum_from numbers i = RustM.ok (0 : i64) := by
  conv => lhs; unfold clever_004_mean_absolute_deviation.sum_from
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' numbers.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat numbers.val.size ≤ i) = true := by
    rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

private theorem sum_from_recurse (numbers : RustSlice i64) (i : usize)
    (hi : i.toNat < numbers.val.size) :
    clever_004_mean_absolute_deviation.sum_from numbers i =
      (clever_004_mean_absolute_deviation.sum_from numbers (i + 1)) >>=
        fun r => (numbers.val[i.toNat]'hi) +? r := by
  conv => lhs; unfold clever_004_mean_absolute_deviation.sum_from
  have h_size_lt : numbers.val.size < USize64.size := numbers.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat numbers.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]
    omega
  have h_idx : (numbers[i]_? : RustM i64) = RustM.ok (numbers.val[i.toNat]'hi) := by
    show (if h : i.toNat < numbers.val.size then pure (numbers.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (numbers.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_no_ov_i : i.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_size_lt; omega
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
  have h_add_eq : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
    show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
    show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
          then (.fail .integerOverflow : RustM usize)
          else pure (i + 1)) = _
    rw [h_no_bv_i]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_add_eq]

/-! ## Strong induction for `sum_from`. -/

private theorem sum_from_correct (numbers : RustSlice i64)
    (hfit : ∀ i, i ≤ numbers.val.size →
        -(2^63 : Int) ≤
            prefix_sum_int numbers numbers.val.size - prefix_sum_int numbers i ∧
        prefix_sum_int numbers numbers.val.size - prefix_sum_int numbers i
          < 2^63) :
    ∀ (m : Nat) (i : usize),
      numbers.val.size - i.toNat ≤ m →
      i.toNat ≤ numbers.val.size →
      ∃ r : i64,
        clever_004_mean_absolute_deviation.sum_from numbers i = RustM.ok r ∧
        r.toInt =
          prefix_sum_int numbers numbers.val.size -
            prefix_sum_int numbers i.toNat := by
  intro m
  induction m with
  | zero =>
    intro i hm hi_le
    have hi_eq : i.toNat = numbers.val.size := by omega
    have hi_ge : numbers.val.size ≤ i.toNat := by omega
    refine ⟨(0 : i64), sum_from_oob numbers i hi_ge, ?_⟩
    rw [i64_zero_toInt, hi_eq]; omega
  | succ m ih =>
    intro i hm hi_le
    by_cases hi_ge : numbers.val.size ≤ i.toNat
    · have hi_eq : i.toNat = numbers.val.size := by omega
      refine ⟨(0 : i64), sum_from_oob numbers i hi_ge, ?_⟩
      rw [i64_zero_toInt, hi_eq]; omega
    · have hi_lt : i.toNat < numbers.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : numbers.val.size < USize64.size := numbers.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ numbers.val.size := by rw [h_i1]; omega
      have h_m_le : numbers.val.size - (i + 1).toNat ≤ m := by rw [h_i1]; omega
      obtain ⟨r', h_rec_eq, h_r_toInt⟩ := ih (i + 1) h_m_le h_i1_le
      have h_psum_succ :
          prefix_sum_int numbers (i.toNat + 1) =
            prefix_sum_int numbers i.toNat + (numbers.val[i.toNat]'hi_lt).toInt :=
        prefix_sum_int_succ numbers i.toNat hi_lt
      have h_r_eq_suffix_i1 :
          r'.toInt =
            prefix_sum_int numbers numbers.val.size -
              prefix_sum_int numbers (i.toNat + 1) := by
        rw [h_r_toInt, h_i1]
      have h_target_suffix :
          prefix_sum_int numbers numbers.val.size -
              prefix_sum_int numbers i.toNat =
            (numbers.val[i.toNat]'hi_lt).toInt + r'.toInt := by
        rw [h_r_eq_suffix_i1, h_psum_succ]; omega
      have h_fit_i := hfit i.toNat (Nat.le_of_lt hi_lt)
      have h_target_bound :
          -(2^63 : Int) ≤ (numbers.val[i.toNat]'hi_lt).toInt + r'.toInt ∧
          (numbers.val[i.toNat]'hi_lt).toInt + r'.toInt < 2^63 := by
        rw [← h_target_suffix]; exact h_fit_i
      have hno : ¬ Int64.addOverflow (numbers.val[i.toNat]'hi_lt) r' := by
        intro hov
        rw [Int64.addOverflow_iff] at hov
        rcases hov with hov_pos | hov_neg
        · have := h_target_bound.2; omega
        · have := h_target_bound.1; omega
      have h_no_bv :
          BitVec.saddOverflow (numbers.val[i.toNat]'hi_lt).toBitVec r'.toBitVec = false := by
        have hno' : ¬ (BitVec.saddOverflow (numbers.val[i.toNat]'hi_lt).toBitVec
                                           r'.toBitVec = true) := hno
        cases hb : BitVec.saddOverflow (numbers.val[i.toNat]'hi_lt).toBitVec r'.toBitVec with
        | false => rfl
        | true => exact absurd hb hno'
      have h_add :
          ((numbers.val[i.toNat]'hi_lt) +? r' : RustM i64) =
            RustM.ok ((numbers.val[i.toNat]'hi_lt) + r') := by
        show (rust_primitives.ops.arith.Add.add (numbers.val[i.toNat]'hi_lt) r'
              : RustM i64) = _
        show (if BitVec.saddOverflow (numbers.val[i.toNat]'hi_lt).toBitVec r'.toBitVec
              then (.fail .integerOverflow : RustM i64)
              else pure ((numbers.val[i.toNat]'hi_lt) + r')) = _
        rw [h_no_bv]; rfl
      have h_toInt_add :
          ((numbers.val[i.toNat]'hi_lt) + r').toInt =
            (numbers.val[i.toNat]'hi_lt).toInt + r'.toInt :=
        Int64.toInt_add_of_not_addOverflow hno
      refine ⟨(numbers.val[i.toNat]'hi_lt) + r', ?_, ?_⟩
      · rw [sum_from_recurse numbers i hi_lt, h_rec_eq, RustM_ok_bind, h_add]
      · rw [h_toInt_add, h_target_suffix]

/-! ## Step lemmas for `abs_dev_sum_from`. -/

private theorem abs_dev_sum_from_oob (numbers : RustSlice i64) (mean : i64) (i : usize)
    (hi : numbers.val.size ≤ i.toNat) :
    clever_004_mean_absolute_deviation.abs_dev_sum_from numbers mean i =
      RustM.ok (0 : i64) := by
  conv => lhs; unfold clever_004_mean_absolute_deviation.abs_dev_sum_from
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' numbers.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat numbers.val.size ≤ i) = true := by
    rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- d ≥ 0 branch: abs_d = d, the recursion becomes  `(rec)>>= λ r => d +? r`. -/
private theorem abs_dev_sum_from_recurse_pos
    (numbers : RustSlice i64) (mean : i64) (i : usize)
    (hi : i.toNat < numbers.val.size)
    (hno_sub : ¬ Int64.subOverflow (numbers.val[i.toNat]'hi) mean)
    (h_d_nneg : 0 ≤ ((numbers.val[i.toNat]'hi) - mean).toInt) :
    clever_004_mean_absolute_deviation.abs_dev_sum_from numbers mean i =
      (clever_004_mean_absolute_deviation.abs_dev_sum_from numbers mean (i + 1)) >>=
        fun r => ((numbers.val[i.toNat]'hi) - mean) +? r := by
  conv => lhs; unfold clever_004_mean_absolute_deviation.abs_dev_sum_from
  have h_size_lt : numbers.val.size < USize64.size := numbers.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat numbers.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]
    omega
  have h_idx : (numbers[i]_? : RustM i64) = RustM.ok (numbers.val[i.toNat]'hi) := by
    show (if h : i.toNat < numbers.val.size then pure (numbers.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (numbers.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_no_bv_sub :
      BitVec.ssubOverflow (numbers.val[i.toNat]'hi).toBitVec mean.toBitVec = false := by
    have hno' : ¬ (BitVec.ssubOverflow (numbers.val[i.toNat]'hi).toBitVec
                                       mean.toBitVec = true) := hno_sub
    cases hb : BitVec.ssubOverflow (numbers.val[i.toNat]'hi).toBitVec mean.toBitVec with
    | false => rfl
    | true => exact absurd hb hno'
  have h_sub_eq :
      ((numbers.val[i.toNat]'hi) -? mean : RustM i64) =
        RustM.ok ((numbers.val[i.toNat]'hi) - mean) := by
    show (rust_primitives.ops.arith.Sub.sub (numbers.val[i.toNat]'hi) mean
          : RustM i64) = _
    show (if BitVec.ssubOverflow (numbers.val[i.toNat]'hi).toBitVec mean.toBitVec
          then (.fail .integerOverflow : RustM i64)
          else pure ((numbers.val[i.toNat]'hi) - mean)) = _
    rw [h_no_bv_sub]; rfl
  have h_d_ge_dec :
      decide ((0 : i64) ≤ (numbers.val[i.toNat]'hi) - mean) = true := by
    rw [decide_eq_true_iff, Int64.le_iff_toInt_le, i64_zero_toInt]
    exact h_d_nneg
  have h_no_ov_i : i.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_size_lt; omega
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
  have h_add_eq : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
    show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
    show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
          then (.fail .integerOverflow : RustM usize)
          else pure (i + 1)) = _
    rw [h_no_bv_i]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_sub_eq, h_add_eq, h_d_ge_dec]

/-- d < 0 branch: abs_d = -d, the recursion becomes  `(rec)>>= λ r => (-d) +? r`.

We need d ≠ Int64.minValue (i.e., d.toInt > -2^63) so that the unary `-? d`
doesn't overflow. -/
private theorem abs_dev_sum_from_recurse_neg
    (numbers : RustSlice i64) (mean : i64) (i : usize)
    (hi : i.toNat < numbers.val.size)
    (hno_sub : ¬ Int64.subOverflow (numbers.val[i.toNat]'hi) mean)
    (h_d_neg : ((numbers.val[i.toNat]'hi) - mean).toInt < 0)
    (h_d_not_min :
      -(2^63 : Int) < ((numbers.val[i.toNat]'hi) - mean).toInt) :
    clever_004_mean_absolute_deviation.abs_dev_sum_from numbers mean i =
      (clever_004_mean_absolute_deviation.abs_dev_sum_from numbers mean (i + 1)) >>=
        fun r => (-((numbers.val[i.toNat]'hi) - mean)) +? r := by
  conv => lhs; unfold clever_004_mean_absolute_deviation.abs_dev_sum_from
  have h_size_lt : numbers.val.size < USize64.size := numbers.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat numbers.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]
    omega
  have h_idx : (numbers[i]_? : RustM i64) = RustM.ok (numbers.val[i.toNat]'hi) := by
    show (if h : i.toNat < numbers.val.size then pure (numbers.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (numbers.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_no_bv_sub :
      BitVec.ssubOverflow (numbers.val[i.toNat]'hi).toBitVec mean.toBitVec = false := by
    have hno' : ¬ (BitVec.ssubOverflow (numbers.val[i.toNat]'hi).toBitVec
                                       mean.toBitVec = true) := hno_sub
    cases hb : BitVec.ssubOverflow (numbers.val[i.toNat]'hi).toBitVec mean.toBitVec with
    | false => rfl
    | true => exact absurd hb hno'
  have h_sub_eq :
      ((numbers.val[i.toNat]'hi) -? mean : RustM i64) =
        RustM.ok ((numbers.val[i.toNat]'hi) - mean) := by
    show (rust_primitives.ops.arith.Sub.sub (numbers.val[i.toNat]'hi) mean
          : RustM i64) = _
    show (if BitVec.ssubOverflow (numbers.val[i.toNat]'hi).toBitVec mean.toBitVec
          then (.fail .integerOverflow : RustM i64)
          else pure ((numbers.val[i.toNat]'hi) - mean)) = _
    rw [h_no_bv_sub]; rfl
  have h_d_ge_dec :
      decide ((0 : i64) ≤ (numbers.val[i.toNat]'hi) - mean) = false := by
    rw [decide_eq_false_iff_not, Int64.le_iff_toInt_le, i64_zero_toInt]
    omega
  have h_d_ne_min :
      ((numbers.val[i.toNat]'hi) - mean) ≠ Int64.minValue := by
    intro h_eq
    have h_toInt : ((numbers.val[i.toNat]'hi) - mean).toInt = Int64.minValue.toInt := by
      rw [h_eq]
    have h_min : Int64.minValue.toInt = -(2^63 : Int) := by decide
    rw [h_min] at h_toInt
    omega
  have h_neg_eq :
      (-? ((numbers.val[i.toNat]'hi) - mean) : RustM i64) =
        RustM.ok (-((numbers.val[i.toNat]'hi) - mean)) := by
    show (rust_primitives.ops.arith.Neg.neg ((numbers.val[i.toNat]'hi) - mean)
          : RustM i64) = _
    show (if ((numbers.val[i.toNat]'hi) - mean) = Int64.minValue
          then (.fail .integerOverflow : RustM i64)
          else pure (-((numbers.val[i.toNat]'hi) - mean))) = _
    rw [if_neg h_d_ne_min]; rfl
  have h_no_ov_i : i.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_size_lt; omega
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
  have h_add_eq : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
    show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
    show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
          then (.fail .integerOverflow : RustM usize)
          else pure (i + 1)) = _
    rw [h_no_bv_i]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_sub_eq, h_add_eq, h_d_ge_dec, h_neg_eq]

/-! ## Strong induction for `abs_dev_sum_from`. -/

private theorem abs_dev_sum_from_correct (numbers : RustSlice i64) (mean : i64)
    (h_mean_eq : mean.toInt = mean_int numbers)
    (hdev_bounded : ∀ (k : Nat) (h : k < numbers.val.size),
        (((numbers.val[k]'h).toInt - mean_int numbers).natAbs : Int) < 2^63)
    (hfit : ∀ i, i ≤ numbers.val.size →
        -(2^63 : Int) ≤
            prefix_abs_dev_sum_int numbers (mean_int numbers) numbers.val.size
              - prefix_abs_dev_sum_int numbers (mean_int numbers) i ∧
        prefix_abs_dev_sum_int numbers (mean_int numbers) numbers.val.size
              - prefix_abs_dev_sum_int numbers (mean_int numbers) i
            < 2^63) :
    ∀ (m : Nat) (i : usize),
      numbers.val.size - i.toNat ≤ m →
      i.toNat ≤ numbers.val.size →
      ∃ r : i64,
        clever_004_mean_absolute_deviation.abs_dev_sum_from numbers mean i =
          RustM.ok r ∧
        r.toInt =
          prefix_abs_dev_sum_int numbers (mean_int numbers) numbers.val.size -
            prefix_abs_dev_sum_int numbers (mean_int numbers) i.toNat := by
  intro m
  induction m with
  | zero =>
    intro i hm hi_le
    have hi_eq : i.toNat = numbers.val.size := by omega
    have hi_ge : numbers.val.size ≤ i.toNat := by omega
    refine ⟨(0 : i64), abs_dev_sum_from_oob numbers mean i hi_ge, ?_⟩
    rw [i64_zero_toInt, hi_eq]; omega
  | succ m ih =>
    intro i hm hi_le
    by_cases hi_ge : numbers.val.size ≤ i.toNat
    · have hi_eq : i.toNat = numbers.val.size := by omega
      refine ⟨(0 : i64), abs_dev_sum_from_oob numbers mean i hi_ge, ?_⟩
      rw [i64_zero_toInt, hi_eq]; omega
    · have hi_lt : i.toNat < numbers.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : numbers.val.size < USize64.size := numbers.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ numbers.val.size := by rw [h_i1]; omega
      have h_m_le : numbers.val.size - (i + 1).toNat ≤ m := by rw [h_i1]; omega
      obtain ⟨r', h_rec_eq, h_r_toInt⟩ := ih (i + 1) h_m_le h_i1_le
      -- Useful intermediate values
      have h_devi : (((numbers.val[i.toNat]'hi_lt).toInt - mean.toInt).natAbs : Int) =
                      (((numbers.val[i.toNat]'hi_lt).toInt - mean_int numbers).natAbs : Int) := by
        rw [h_mean_eq]
      -- Prefix step
      have h_padsum_succ :
          prefix_abs_dev_sum_int numbers (mean_int numbers) (i.toNat + 1) =
            prefix_abs_dev_sum_int numbers (mean_int numbers) i.toNat +
              (((numbers.val[i.toNat]'hi_lt).toInt - mean_int numbers).natAbs : Int) :=
        prefix_abs_dev_sum_int_succ numbers (mean_int numbers) i.toNat hi_lt
      -- r' = suffix from (i+1) of the abs-dev oracle
      have h_r_eq_suffix_i1 :
          r'.toInt =
            prefix_abs_dev_sum_int numbers (mean_int numbers) numbers.val.size -
              prefix_abs_dev_sum_int numbers (mean_int numbers) (i.toNat + 1) := by
        rw [h_r_toInt, h_i1]
      -- Target = absdev(i) + r'
      have h_target_suffix :
          prefix_abs_dev_sum_int numbers (mean_int numbers) numbers.val.size -
              prefix_abs_dev_sum_int numbers (mean_int numbers) i.toNat =
            (((numbers.val[i.toNat]'hi_lt).toInt - mean_int numbers).natAbs : Int) +
              r'.toInt := by
        rw [h_r_eq_suffix_i1, h_padsum_succ]; omega
      -- Bound from hfit at i.toNat: suffix from i.toNat fits in i64.
      have h_fit_i := hfit i.toNat (Nat.le_of_lt hi_lt)
      have h_target_bound :
          -(2^63 : Int) ≤
            (((numbers.val[i.toNat]'hi_lt).toInt - mean_int numbers).natAbs : Int) +
              r'.toInt ∧
          (((numbers.val[i.toNat]'hi_lt).toInt - mean_int numbers).natAbs : Int) +
              r'.toInt < 2^63 := by
        rw [← h_target_suffix]; exact h_fit_i
      -- The per-element absdev is non-negative.
      have h_natAbs_nneg :
          0 ≤ (((numbers.val[i.toNat]'hi_lt).toInt - mean_int numbers).natAbs : Int) :=
        Int.natCast_nonneg _
      -- Bound the element's deviation: |d| < 2^63 (from hdev_bounded).
      have h_d_bounded :
          (((numbers.val[i.toNat]'hi_lt).toInt - mean_int numbers).natAbs : Int) < 2^63 :=
        hdev_bounded i.toNat hi_lt
      -- Bridge to mean: d_real = numbers[i].toInt - mean.toInt = numbers[i].toInt - mean_int numbers.
      have h_d_real_eq :
          (numbers.val[i.toNat]'hi_lt).toInt - mean.toInt =
            (numbers.val[i.toNat]'hi_lt).toInt - mean_int numbers := by
        rw [h_mean_eq]
      -- No-overflow for the i64 subtraction numbers[i] -? mean.
      -- |numbers[i].toInt - mean.toInt| < 2^63 ⇒ both bounds.
      have h_d_natAbs_lt : (((numbers.val[i.toNat]'hi_lt).toInt - mean.toInt).natAbs : Int) < 2^63 := by
        rw [h_d_real_eq]; exact h_d_bounded
      have h_d_real_bounds :
          -(2^63 : Int) < (numbers.val[i.toNat]'hi_lt).toInt - mean.toInt ∧
          (numbers.val[i.toNat]'hi_lt).toInt - mean.toInt < 2^63 := by
        omega
      have hno_sub :
          ¬ Int64.subOverflow (numbers.val[i.toNat]'hi_lt) mean := by
        intro hov
        rw [Int64.subOverflow_iff] at hov
        rcases hov with hov_pos | hov_neg
        · have := h_d_real_bounds.2; omega
        · have := h_d_real_bounds.1; omega
      have h_sub_toInt :
          ((numbers.val[i.toNat]'hi_lt) - mean).toInt =
            (numbers.val[i.toNat]'hi_lt).toInt - mean.toInt :=
        Int64.toInt_sub_of_not_subOverflow hno_sub
      -- Case split on d ≥ 0 vs d < 0.
      by_cases h_d_real_ge : 0 ≤ ((numbers.val[i.toNat]'hi_lt) - mean).toInt
      · -- POS branch: abs_d = d.
        have h_d_real_ge' :
            0 ≤ (numbers.val[i.toNat]'hi_lt).toInt - mean.toInt := by
          rw [← h_sub_toInt]; exact h_d_real_ge
        have h_d_mean_nneg :
            0 ≤ (numbers.val[i.toNat]'hi_lt).toInt - mean_int numbers := by
          rw [← h_d_real_eq]; exact h_d_real_ge'
        have h_step :=
          abs_dev_sum_from_recurse_pos numbers mean i hi_lt hno_sub h_d_real_ge
        -- The +? at the end: abs_d = d, must show no overflow with r'.
        have h_natAbs_eq_d :
            (((numbers.val[i.toNat]'hi_lt).toInt - mean_int numbers).natAbs : Int) =
              (numbers.val[i.toNat]'hi_lt).toInt - mean.toInt := by
          rw [Int.natAbs_of_nonneg h_d_mean_nneg]
          rw [h_mean_eq]
        have h_no_add_ov :
            ¬ Int64.addOverflow ((numbers.val[i.toNat]'hi_lt) - mean) r' := by
          intro hov
          rw [Int64.addOverflow_iff] at hov
          rw [h_sub_toInt] at hov
          rcases hov with hov_pos | hov_neg
          · have := h_target_bound.2
            rw [h_natAbs_eq_d] at this
            omega
          · have := h_target_bound.1
            rw [h_natAbs_eq_d] at this
            omega
        have h_no_bv_add :
            BitVec.saddOverflow ((numbers.val[i.toNat]'hi_lt) - mean).toBitVec
                                 r'.toBitVec = false := by
          have hno' : ¬ (BitVec.saddOverflow ((numbers.val[i.toNat]'hi_lt) - mean).toBitVec
                                             r'.toBitVec = true) := h_no_add_ov
          cases hb : BitVec.saddOverflow ((numbers.val[i.toNat]'hi_lt) - mean).toBitVec
                                          r'.toBitVec with
          | false => rfl
          | true => exact absurd hb hno'
        have h_add_eq2 :
            (((numbers.val[i.toNat]'hi_lt) - mean) +? r' : RustM i64) =
              RustM.ok (((numbers.val[i.toNat]'hi_lt) - mean) + r') := by
          show (rust_primitives.ops.arith.Add.add ((numbers.val[i.toNat]'hi_lt) - mean) r'
                : RustM i64) = _
          show (if BitVec.saddOverflow ((numbers.val[i.toNat]'hi_lt) - mean).toBitVec
                                        r'.toBitVec
                then (.fail .integerOverflow : RustM i64)
                else pure (((numbers.val[i.toNat]'hi_lt) - mean) + r')) = _
          rw [h_no_bv_add]; rfl
        have h_toInt_add :
            (((numbers.val[i.toNat]'hi_lt) - mean) + r').toInt =
              ((numbers.val[i.toNat]'hi_lt) - mean).toInt + r'.toInt :=
          Int64.toInt_add_of_not_addOverflow h_no_add_ov
        refine ⟨((numbers.val[i.toNat]'hi_lt) - mean) + r', ?_, ?_⟩
        · rw [h_step, h_rec_eq, RustM_ok_bind, h_add_eq2]
        · rw [h_toInt_add, h_sub_toInt, h_target_suffix, h_natAbs_eq_d]
      · -- NEG branch: abs_d = -d.
        have h_d_real_lt : ((numbers.val[i.toNat]'hi_lt) - mean).toInt < 0 := by
          omega
        have h_d_real_lt' :
            (numbers.val[i.toNat]'hi_lt).toInt - mean.toInt < 0 := by
          rw [← h_sub_toInt]; exact h_d_real_lt
        have h_d_mean_neg :
            (numbers.val[i.toNat]'hi_lt).toInt - mean_int numbers < 0 := by
          rw [← h_d_real_eq]; exact h_d_real_lt'
        have h_d_not_min :
            -(2^63 : Int) < ((numbers.val[i.toNat]'hi_lt) - mean).toInt := by
          rw [h_sub_toInt]; exact h_d_real_bounds.1
        have h_step :=
          abs_dev_sum_from_recurse_neg numbers mean i hi_lt hno_sub h_d_real_lt h_d_not_min
        -- abs_d = -d. Use Int.natAbs_of_nonneg on -d.
        have h_natAbs_eq_neg_d :
            (((numbers.val[i.toNat]'hi_lt).toInt - mean_int numbers).natAbs : Int) =
              -((numbers.val[i.toNat]'hi_lt).toInt - mean.toInt) := by
          have h_neg_nneg :
              0 ≤ -((numbers.val[i.toNat]'hi_lt).toInt - mean_int numbers) := by omega
          have h_natAbs_neg :
              ((-((numbers.val[i.toNat]'hi_lt).toInt - mean_int numbers)).natAbs : Int) =
                -((numbers.val[i.toNat]'hi_lt).toInt - mean_int numbers) :=
            Int.natAbs_of_nonneg h_neg_nneg
          rw [Int.natAbs_neg] at h_natAbs_neg
          rw [h_natAbs_neg]
          rw [h_mean_eq]
        -- Use Int64.toInt_neg with the not-min condition.
        have h_neg_toInt :
            (-((numbers.val[i.toNat]'hi_lt) - mean)).toInt =
              -((numbers.val[i.toNat]'hi_lt) - mean).toInt := by
          have h_dne : ((numbers.val[i.toNat]'hi_lt) - mean) ≠ Int64.minValue := by
            intro h_eq
            have h_t : ((numbers.val[i.toNat]'hi_lt) - mean).toInt = Int64.minValue.toInt := by
              rw [h_eq]
            have h_min_eq : Int64.minValue.toInt = -(2^63 : Int) := by decide
            rw [h_min_eq] at h_t
            omega
          exact Int64.toInt_neg_of_ne_intMin h_dne
        have h_no_add_ov :
            ¬ Int64.addOverflow (-((numbers.val[i.toNat]'hi_lt) - mean)) r' := by
          intro hov
          rw [Int64.addOverflow_iff] at hov
          rw [h_neg_toInt, h_sub_toInt] at hov
          rcases hov with hov_pos | hov_neg
          · have := h_target_bound.2
            rw [h_natAbs_eq_neg_d] at this
            omega
          · have := h_target_bound.1
            rw [h_natAbs_eq_neg_d] at this
            omega
        have h_no_bv_add :
            BitVec.saddOverflow (-((numbers.val[i.toNat]'hi_lt) - mean)).toBitVec
                                 r'.toBitVec = false := by
          have hno' : ¬ (BitVec.saddOverflow (-((numbers.val[i.toNat]'hi_lt) - mean)).toBitVec
                                             r'.toBitVec = true) := h_no_add_ov
          cases hb : BitVec.saddOverflow (-((numbers.val[i.toNat]'hi_lt) - mean)).toBitVec
                                          r'.toBitVec with
          | false => rfl
          | true => exact absurd hb hno'
        have h_add_eq2 :
            ((-((numbers.val[i.toNat]'hi_lt) - mean)) +? r' : RustM i64) =
              RustM.ok ((-((numbers.val[i.toNat]'hi_lt) - mean)) + r') := by
          show (rust_primitives.ops.arith.Add.add (-((numbers.val[i.toNat]'hi_lt) - mean)) r'
                : RustM i64) = _
          show (if BitVec.saddOverflow (-((numbers.val[i.toNat]'hi_lt) - mean)).toBitVec
                                        r'.toBitVec
                then (.fail .integerOverflow : RustM i64)
                else pure ((-((numbers.val[i.toNat]'hi_lt) - mean)) + r')) = _
          rw [h_no_bv_add]; rfl
        have h_toInt_add :
            ((-((numbers.val[i.toNat]'hi_lt) - mean)) + r').toInt =
              (-((numbers.val[i.toNat]'hi_lt) - mean)).toInt + r'.toInt :=
          Int64.toInt_add_of_not_addOverflow h_no_add_ov
        refine ⟨(-((numbers.val[i.toNat]'hi_lt) - mean)) + r', ?_, ?_⟩
        · rw [h_step, h_rec_eq, RustM_ok_bind, h_add_eq2]
        · rw [h_toInt_add, h_neg_toInt, h_sub_toInt, h_target_suffix, h_natAbs_eq_neg_d]

/-! ## Top-level theorems -/

/-- Empty-slice boundary contract. -/
theorem empty_returns_zero
    (numbers : RustSlice i64) (hempty : numbers.val.size = 0) :
    clever_004_mean_absolute_deviation.mean_absolute_deviation numbers
      = RustM.ok (0 : i64) := by
  unfold clever_004_mean_absolute_deviation.mean_absolute_deviation
  have h_size_lt : numbers.val.size < USize64.size := numbers.size_lt_usizeSize
  have h_n_toNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  -- The cast usize → i64. cast_op x : RustM i64 = pure (USize64.toInt64 x) = pure (x.toNat.toInt64).
  have h_cast_eq :
      (rust_primitives.hax.cast_op (USize64.ofNat numbers.val.size) : RustM i64) =
        pure ((USize64.ofNat numbers.val.size).toInt64) := rfl
  have h_n_eq : (USize64.ofNat numbers.val.size).toInt64 = (0 : i64) := by
    show (USize64.ofNat numbers.val.size).toNat.toInt64 = (0 : i64)
    rw [h_n_toNat, hempty]; rfl
  have h_eq_dec : decide ((USize64.ofNat numbers.val.size).toInt64 = (0 : i64)) = true := by
    rw [decide_eq_true_iff]; exact h_n_eq
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             pure_bind, h_cast_eq]
  show (do
        let __do_lift ← ((USize64.ofNat numbers.val.size).toInt64 ==? (0 : i64) : RustM Bool)
        if __do_lift = true then pure 0
        else _) = RustM.ok (0 : i64)
  show (do
        let __do_lift ← (pure (decide ((USize64.ofNat numbers.val.size).toInt64 = (0 : i64))) : RustM Bool)
        if __do_lift = true then pure 0
        else _) = RustM.ok (0 : i64)
  rw [h_eq_dec]
  simp only [pure_bind, ↓reduceIte]
  rfl

/-- Non-negativity of the integer-valued abs-dev oracle. -/
private theorem prefix_abs_dev_sum_int_nonneg (numbers : RustSlice i64) (mean : Int) :
    ∀ (k : Nat), 0 ≤ prefix_abs_dev_sum_int numbers mean k
  | 0 => Int.le_refl 0
  | k + 1 => by
    show 0 ≤ prefix_abs_dev_sum_int numbers mean k +
          (if h : k < numbers.val.size then
             (((numbers.val[k]'h).toInt - mean).natAbs : Int)
           else 0)
    have ih := prefix_abs_dev_sum_int_nonneg numbers mean k
    by_cases hk : k < numbers.val.size
    · rw [dif_pos hk]
      have h_pos : 0 ≤ (((numbers.val[k]'hk).toInt - mean).natAbs : Int) :=
        Int.natCast_nonneg _
      omega
    · rw [dif_neg hk]
      omega

/-- Aux: combines formula equation and non-negativity in one lemma. -/
private theorem mad_aux
    (numbers : RustSlice i64)
    (hsize_fits : (numbers.val.size : Int) < 2^63)
    (hsum_fit : ∀ i, i ≤ numbers.val.size →
        -(2^63 : Int) ≤
            prefix_sum_int numbers numbers.val.size - prefix_sum_int numbers i ∧
        prefix_sum_int numbers numbers.val.size - prefix_sum_int numbers i
          < 2^63)
    (hdev_bounded : ∀ (k : Nat) (h : k < numbers.val.size),
        (((numbers.val[k]'h).toInt - mean_int numbers).natAbs : Int) < 2^63)
    (habs_sum_fit : ∀ i, i ≤ numbers.val.size →
        -(2^63 : Int) ≤
            prefix_abs_dev_sum_int numbers (mean_int numbers) numbers.val.size
              - prefix_abs_dev_sum_int numbers (mean_int numbers) i ∧
        prefix_abs_dev_sum_int numbers (mean_int numbers) numbers.val.size
              - prefix_abs_dev_sum_int numbers (mean_int numbers) i
            < 2^63) :
    ∃ r : i64,
      clever_004_mean_absolute_deviation.mean_absolute_deviation numbers
        = RustM.ok r ∧
      r.toInt =
        (prefix_abs_dev_sum_int numbers (mean_int numbers) numbers.val.size)
          / (numbers.val.size : Int) ∧
      0 ≤ r.toInt := by
  by_cases hempty : numbers.val.size = 0
  · -- Empty case: function returns 0, formula = 0/0 = 0 in Lean.
    refine ⟨(0 : i64), empty_returns_zero numbers hempty, ?_, ?_⟩
    · rw [i64_zero_toInt, hempty]
      show (0 : Int) = prefix_abs_dev_sum_int numbers (mean_int numbers) 0 / ((0 : Nat) : Int)
      show (0 : Int) = (0 : Int) / ((0 : Nat) : Int)
      decide
    · rw [i64_zero_toInt]; omega
  · -- Non-empty case.
    have h_size_pos : 0 < numbers.val.size := Nat.pos_of_ne_zero hempty
    have h_size_lt_64 : numbers.val.size < USize64.size := numbers.size_lt_usizeSize
    have h_size_lt_63 : numbers.val.size < 2^63 := by
      have h1 : (numbers.val.size : Int) < 2^63 := hsize_fits
      exact_mod_cast h1
    have h_n_toInt :
        ((USize64.ofNat numbers.val.size).toInt64).toInt = (numbers.val.size : Int) :=
      usize_ofNat_toInt64_toInt numbers.val.size h_size_lt_63
    have h_n_pos : 0 < ((USize64.ofNat numbers.val.size).toInt64).toInt := by
      rw [h_n_toInt]; exact_mod_cast h_size_pos
    have h_n_ne_zero : (USize64.ofNat numbers.val.size).toInt64 ≠ (0 : i64) := by
      intro h_eq
      have h_t : ((USize64.ofNat numbers.val.size).toInt64).toInt = (0 : i64).toInt := by
        rw [h_eq]
      rw [h_n_toInt, i64_zero_toInt] at h_t
      have : (numbers.val.size : Int) = 0 := h_t
      have : numbers.val.size = 0 := by exact_mod_cast this
      exact hempty this
    -- Apply sum_from_correct at i=0.
    have h_zero_toNat : (0 : usize).toNat = 0 := rfl
    have h_m_le : numbers.val.size - (0 : usize).toNat ≤ numbers.val.size := by
      rw [h_zero_toNat]; omega
    have h_i_le : (0 : usize).toNat ≤ numbers.val.size := by
      rw [h_zero_toNat]; omega
    obtain ⟨s, h_sum_eq, h_s_toInt⟩ :=
      sum_from_correct numbers hsum_fit numbers.val.size (0 : usize) h_m_le h_i_le
    have h_s_toInt' : s.toInt = prefix_sum_int numbers numbers.val.size := by
      rw [h_s_toInt, h_zero_toNat]
      show prefix_sum_int numbers numbers.val.size - prefix_sum_int numbers 0 =
            prefix_sum_int numbers numbers.val.size
      show prefix_sum_int numbers numbers.val.size - 0 =
            prefix_sum_int numbers numbers.val.size
      omega
    -- mean = s / n. Its toInt = mean_int numbers.
    have h_div_pure_mean :
        (s /? ((USize64.ofNat numbers.val.size).toInt64) : RustM i64) =
          pure (s / ((USize64.ofNat numbers.val.size).toInt64)) :=
      i64_div_pure s _ h_n_pos
    have h_mean_toInt :
        (s / ((USize64.ofNat numbers.val.size).toInt64)).toInt = mean_int numbers := by
      rw [i64_toInt_div_tdiv s _ h_n_pos]
      rw [h_s_toInt', h_n_toInt]
      rfl
    -- Apply abs_dev_sum_from_correct.
    obtain ⟨a, h_a_eq, h_a_toInt⟩ :=
      abs_dev_sum_from_correct numbers (s / ((USize64.ofNat numbers.val.size).toInt64))
        h_mean_toInt hdev_bounded habs_sum_fit
        numbers.val.size (0 : usize) h_m_le h_i_le
    have h_a_toInt' :
        a.toInt = prefix_abs_dev_sum_int numbers (mean_int numbers) numbers.val.size := by
      rw [h_a_toInt, h_zero_toNat]
      show prefix_abs_dev_sum_int numbers (mean_int numbers) numbers.val.size -
            prefix_abs_dev_sum_int numbers (mean_int numbers) 0 =
              prefix_abs_dev_sum_int numbers (mean_int numbers) numbers.val.size
      show prefix_abs_dev_sum_int numbers (mean_int numbers) numbers.val.size - 0 =
              prefix_abs_dev_sum_int numbers (mean_int numbers) numbers.val.size
      omega
    -- Final: r = a / n.
    have h_a_nneg : 0 ≤ a.toInt := by
      rw [h_a_toInt']
      exact prefix_abs_dev_sum_int_nonneg numbers (mean_int numbers) numbers.val.size
    have h_div_pure_r :
        (a /? ((USize64.ofNat numbers.val.size).toInt64) : RustM i64) =
          pure (a / ((USize64.ofNat numbers.val.size).toInt64)) :=
      i64_div_pure a _ h_n_pos
    have h_r_toInt :
        (a / ((USize64.ofNat numbers.val.size).toInt64)).toInt =
          a.toInt / ((USize64.ofNat numbers.val.size).toInt64).toInt := by
      rw [i64_toInt_div_tdiv a _ h_n_pos]
      exact Int.tdiv_eq_ediv_of_nonneg h_a_nneg
    have h_size_nneg : (0 : Int) ≤ (numbers.val.size : Int) := by
      exact_mod_cast Nat.zero_le _
    have h_r_nneg : 0 ≤ (a / ((USize64.ofNat numbers.val.size).toInt64)).toInt := by
      rw [h_r_toInt, h_n_toInt]
      exact Int.ediv_nonneg h_a_nneg h_size_nneg
    refine ⟨a / ((USize64.ofNat numbers.val.size).toInt64), ?_, ?_, h_r_nneg⟩
    · -- The function evaluates to RustM.ok (a / n).
      unfold clever_004_mean_absolute_deviation.mean_absolute_deviation
      have h_cast_eq :
          (rust_primitives.hax.cast_op (USize64.ofNat numbers.val.size) : RustM i64) =
            pure ((USize64.ofNat numbers.val.size).toInt64) := rfl
      have h_eq_dec :
          decide ((USize64.ofNat numbers.val.size).toInt64 = (0 : i64)) = false := by
        rw [decide_eq_false_iff_not]; exact h_n_ne_zero
      simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
                 pure_bind, h_cast_eq,
                 show ((USize64.ofNat numbers.val.size).toInt64 ==? (0 : i64) : RustM Bool) =
                   pure (decide ((USize64.ofNat numbers.val.size).toInt64 = (0 : i64))) from rfl,
                 h_eq_dec, Bool.false_eq_true, ↓reduceIte]
      rw [h_sum_eq, RustM_ok_bind, h_div_pure_mean, pure_bind, h_a_eq, RustM_ok_bind, h_div_pure_r]
      rfl
    · rw [h_r_toInt, h_n_toInt, h_a_toInt']

/-- Main correctness postcondition. -/
theorem mad_matches_formula
    (numbers : RustSlice i64)
    (hsize_fits : (numbers.val.size : Int) < 2^63)
    (hsum_fit : ∀ i, i ≤ numbers.val.size →
        -(2^63 : Int) ≤
            prefix_sum_int numbers numbers.val.size - prefix_sum_int numbers i ∧
        prefix_sum_int numbers numbers.val.size - prefix_sum_int numbers i
          < 2^63)
    (hdev_bounded : ∀ (k : Nat) (h : k < numbers.val.size),
        (((numbers.val[k]'h).toInt - mean_int numbers).natAbs : Int) < 2^63)
    (habs_sum_fit : ∀ i, i ≤ numbers.val.size →
        -(2^63 : Int) ≤
            prefix_abs_dev_sum_int numbers (mean_int numbers) numbers.val.size
              - prefix_abs_dev_sum_int numbers (mean_int numbers) i ∧
        prefix_abs_dev_sum_int numbers (mean_int numbers) numbers.val.size
              - prefix_abs_dev_sum_int numbers (mean_int numbers) i
            < 2^63) :
    ∃ r : i64,
      clever_004_mean_absolute_deviation.mean_absolute_deviation numbers
        = RustM.ok r ∧
      r.toInt =
        (prefix_abs_dev_sum_int numbers (mean_int numbers) numbers.val.size)
          / (numbers.val.size : Int) := by
  obtain ⟨r, hres, heq, _⟩ := mad_aux numbers hsize_fits hsum_fit hdev_bounded habs_sum_fit
  exact ⟨r, hres, heq⟩

/-- Non-negativity of the result. -/
theorem mad_non_negative
    (numbers : RustSlice i64)
    (hsize_fits : (numbers.val.size : Int) < 2^63)
    (hsum_fit : ∀ i, i ≤ numbers.val.size →
        -(2^63 : Int) ≤
            prefix_sum_int numbers numbers.val.size - prefix_sum_int numbers i ∧
        prefix_sum_int numbers numbers.val.size - prefix_sum_int numbers i
          < 2^63)
    (hdev_bounded : ∀ (k : Nat) (h : k < numbers.val.size),
        (((numbers.val[k]'h).toInt - mean_int numbers).natAbs : Int) < 2^63)
    (habs_sum_fit : ∀ i, i ≤ numbers.val.size →
        -(2^63 : Int) ≤
            prefix_abs_dev_sum_int numbers (mean_int numbers) numbers.val.size
              - prefix_abs_dev_sum_int numbers (mean_int numbers) i ∧
        prefix_abs_dev_sum_int numbers (mean_int numbers) numbers.val.size
              - prefix_abs_dev_sum_int numbers (mean_int numbers) i
            < 2^63) :
    ∃ r : i64,
      clever_004_mean_absolute_deviation.mean_absolute_deviation numbers
        = RustM.ok r ∧
      0 ≤ r.toInt := by
  obtain ⟨r, hres, _, hnn⟩ :=
    mad_aux numbers hsize_fits hsum_fit hdev_bounded habs_sum_fit
  exact ⟨r, hres, hnn⟩

end Clever_004_mean_absolute_deviationObligations
