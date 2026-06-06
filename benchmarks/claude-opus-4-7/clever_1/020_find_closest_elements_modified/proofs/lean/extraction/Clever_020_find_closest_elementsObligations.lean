-- Companion obligations file for the `clever_020_find_closest_elements` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_020_find_closest_elements

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_020_find_closest_elementsObligations

/-! ## Pairwise-difference fit hypothesis -/

private abbrev pairwise_diff_fits (numbers : RustSlice i64) : Prop :=
  ∀ (i j : Nat) (hi : i < numbers.val.size) (hj : j < numbers.val.size),
    -(2^63 : Int) ≤ (numbers.val[i]'hi).toInt - (numbers.val[j]'hj).toInt
    ∧ (numbers.val[i]'hi).toInt - (numbers.val[j]'hj).toInt < 2^63

/-! ## Helpers -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl
private theorem usize_two_toNat : (2 : usize).toNat = 2 := rfl
private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

private theorem usize_add_two_toNat (i : usize) (h : i.toNat + 2 < 2^64) :
    (i + 2).toNat = i.toNat + 2 := by
  have h_pre : i.toNat + (2 : usize).toNat < 2^64 := by
    rw [usize_two_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_two_toNat]

/-! ## `abs_diff` evaluation. -/

/-- `abs_diff` returns the larger-minus-smaller, given no overflow in either
    direction. -/
private theorem abs_diff_eval (a b : i64)
    (h_ab : ¬ Int64.subOverflow a b)
    (h_ba : ¬ Int64.subOverflow b a) :
    clever_020_find_closest_elements.abs_diff a b =
      pure (if a > b then a - b else b - a) := by
  simp only [clever_020_find_closest_elements.abs_diff,
             rust_primitives.cmp.gt, rust_primitives.ops.arith.Sub.sub]
  have h_no_ab : ¬ (BitVec.ssubOverflow a.toBitVec b.toBitVec = true) := h_ab
  have h_no_ba : ¬ (BitVec.ssubOverflow b.toBitVec a.toBitVec = true) := h_ba
  by_cases h_gt : a > b
  · simp [h_gt, h_no_ab]
  · simp [h_gt, h_no_ba]

/-- `abs_diff`'s result, transferred to `Int`, is exactly the symmetric
    natural-absolute-difference. -/
private theorem abs_diff_toInt (a b : i64)
    (h_ab : ¬ Int64.subOverflow a b)
    (h_ba : ¬ Int64.subOverflow b a) :
    ∃ d : i64,
      clever_020_find_closest_elements.abs_diff a b = RustM.ok d
      ∧ d.toInt = ((a.toInt - b.toInt).natAbs : Int) := by
  refine ⟨if a > b then a - b else b - a, ?_, ?_⟩
  · rw [abs_diff_eval a b h_ab h_ba]; rfl
  · by_cases h_gt : a > b
    · rw [if_pos h_gt]
      rw [Int64.toInt_sub_of_not_subOverflow h_ab]
      have h_gt_int : b.toInt < a.toInt := Int64.lt_iff_toInt_lt.mp h_gt
      have h_pos : 0 ≤ a.toInt - b.toInt := by omega
      rw [Int.natAbs_of_nonneg h_pos]
    · rw [if_neg h_gt]
      rw [Int64.toInt_sub_of_not_subOverflow h_ba]
      have h_le : a.toInt ≤ b.toInt := by
        rcases Int.lt_or_le b.toInt a.toInt with h_lt | h_ge
        · exact absurd (Int64.lt_iff_toInt_lt.mpr h_lt) h_gt
        · exact h_ge
      have h_neg_pos : 0 ≤ b.toInt - a.toInt := by omega
      have h_eq : a.toInt - b.toInt = -(b.toInt - a.toInt) := by omega
      rw [h_eq, Int.natAbs_neg, Int.natAbs_of_nonneg h_neg_pos]

/-- Pairwise-diff fits ⇒ both directions of the signed subtraction don't
    overflow. -/
private theorem no_sub_overflow_of_fit
    (numbers : RustSlice i64) (hfit : pairwise_diff_fits numbers)
    (i j : Nat) (hi : i < numbers.val.size) (hj : j < numbers.val.size) :
    ¬ Int64.subOverflow (numbers.val[i]'hi) (numbers.val[j]'hj) := by
  rw [Int64.subOverflow_iff]
  intro hov
  obtain ⟨hlo, hhi⟩ := hfit i j hi hj
  rcases hov with h_high | h_low
  · omega
  · omega

/-! ## `usize +? 1` and `usize +? 2` reductions. -/

private theorem usize_add_one_eq (i : usize) (h : i.toNat + 1 < 2^64) :
    (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
  show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
  show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure (i + 1)) = _
  have h_no_bv : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hi' := (USize64.uaddOverflow_iff i 1).mp hbo
      rw [usize_one_toNat] at hi'
      omega
  rw [h_no_bv]; rfl

private theorem usize_add_two_eq (i : usize) (h : i.toNat + 2 < 2^64) :
    (i +? (2 : usize) : RustM usize) = RustM.ok (i + 2) := by
  show (rust_primitives.ops.arith.Add.add i 2 : RustM usize) = RustM.ok (i + 2)
  show (if BitVec.uaddOverflow i.toBitVec (2 : usize).toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure (i + 2)) = _
  have h_no_bv : BitVec.uaddOverflow i.toBitVec (2 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (2 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hi' := (USize64.uaddOverflow_iff i 2).mp hbo
      rw [usize_two_toNat] at hi'
      omega
  rw [h_no_bv]; rfl

/-! ## Step lemmas for `scan_at`. -/

/-- Stop case: when `i + 1 ≥ n`, the function returns `(best_i, best_j)`. -/
private theorem scan_at_stop
    (numbers : RustSlice i64) (i j best_i best_j : usize)
    (h_iov : i.toNat + 1 < 2^64)
    (h_stop : numbers.val.size ≤ i.toNat + 1) :
    clever_020_find_closest_elements.scan_at numbers i j best_i best_j
      = RustM.ok ⟨best_i, best_j⟩ := by
  conv => lhs; unfold clever_020_find_closest_elements.scan_at
  have h_size_lt : numbers.val.size < USize64.size := numbers.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_add_eq : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
    usize_add_one_eq i h_iov
  have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_iov
  have h_cond_ge :
      ((i + 1) >=? USize64.ofNat numbers.val.size : RustM Bool) = RustM.ok true := by
    show (rust_primitives.cmp.ge (i + 1) _ : RustM Bool) = RustM.ok true
    show (pure (decide _) : RustM Bool) = RustM.ok true
    have h_dec : decide (USize64.ofNat numbers.val.size ≤ i + 1) = true := by
      rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat, h_i1_toNat]
      exact h_stop
    rw [h_dec]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             pure_bind, RustM_ok_bind, h_add_eq, h_cond_ge, ↓reduceIte]
  rfl

/-- Jump case: `i + 1 < n` and `j ≥ n`. -/
private theorem scan_at_jump
    (numbers : RustSlice i64) (i j best_i best_j : usize)
    (h_iov1 : i.toNat + 1 < 2^64)
    (h_iov2 : i.toNat + 2 < 2^64)
    (h_no_stop : i.toNat + 1 < numbers.val.size)
    (h_jump : numbers.val.size ≤ j.toNat) :
    clever_020_find_closest_elements.scan_at numbers i j best_i best_j
      = clever_020_find_closest_elements.scan_at numbers (i + 1) (i + 2) best_i best_j := by
  conv => lhs; unfold clever_020_find_closest_elements.scan_at
  have h_size_lt : numbers.val.size < USize64.size := numbers.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_add1_eq : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
    usize_add_one_eq i h_iov1
  have h_add2_eq : (i +? (2 : usize) : RustM usize) = RustM.ok (i + 2) :=
    usize_add_two_eq i h_iov2
  have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_iov1
  have h_cond_stop :
      ((i + 1) >=? USize64.ofNat numbers.val.size : RustM Bool) = RustM.ok false := by
    show (rust_primitives.cmp.ge (i + 1) _ : RustM Bool) = RustM.ok false
    show (pure (decide _) : RustM Bool) = RustM.ok false
    have h_dec : decide (USize64.ofNat numbers.val.size ≤ i + 1) = false := by
      rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat, h_i1_toNat]
      omega
    rw [h_dec]; rfl
  have h_cond_jump :
      (j >=? USize64.ofNat numbers.val.size : RustM Bool) = RustM.ok true := by
    show (rust_primitives.cmp.ge j _ : RustM Bool) = RustM.ok true
    show (pure (decide _) : RustM Bool) = RustM.ok true
    have h_dec : decide (USize64.ofNat numbers.val.size ≤ j) = true := by
      rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat]
      exact h_jump
    rw [h_dec]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             pure_bind, RustM_ok_bind, h_add1_eq, h_add2_eq,
             h_cond_stop, h_cond_jump, Bool.false_eq_true, ↓reduceIte]

/-- Step case: both `i + 1 < n` and `j < n`. Computes `cur` and `best`
    absolute differences, compares, and recurses on the smaller. -/
private theorem scan_at_step
    (numbers : RustSlice i64) (i j best_i best_j : usize)
    (h_iov1 : i.toNat + 1 < 2^64)
    (h_jov : j.toNat + 1 < 2^64)
    (h_no_stop : i.toNat + 1 < numbers.val.size)
    (h_no_jump : j.toNat < numbers.val.size)
    (hbest_i : best_i.toNat < numbers.val.size)
    (hbest_j : best_j.toNat < numbers.val.size)
    (hi : i.toNat < numbers.val.size)
    (h_sub_ij : ¬ Int64.subOverflow (numbers.val[i.toNat]'hi) (numbers.val[j.toNat]'h_no_jump))
    (h_sub_ji : ¬ Int64.subOverflow (numbers.val[j.toNat]'h_no_jump) (numbers.val[i.toNat]'hi))
    (h_sub_bibj : ¬ Int64.subOverflow (numbers.val[best_i.toNat]'hbest_i) (numbers.val[best_j.toNat]'hbest_j))
    (h_sub_bjbi : ¬ Int64.subOverflow (numbers.val[best_j.toNat]'hbest_j) (numbers.val[best_i.toNat]'hbest_i)) :
    clever_020_find_closest_elements.scan_at numbers i j best_i best_j =
      (let cur : i64 :=
        if (numbers.val[i.toNat]'hi) > (numbers.val[j.toNat]'h_no_jump) then
          (numbers.val[i.toNat]'hi) - (numbers.val[j.toNat]'h_no_jump)
        else (numbers.val[j.toNat]'h_no_jump) - (numbers.val[i.toNat]'hi)
       let best : i64 :=
        if (numbers.val[best_i.toNat]'hbest_i) > (numbers.val[best_j.toNat]'hbest_j) then
          (numbers.val[best_i.toNat]'hbest_i) - (numbers.val[best_j.toNat]'hbest_j)
        else (numbers.val[best_j.toNat]'hbest_j) - (numbers.val[best_i.toNat]'hbest_i)
       if cur < best then
         clever_020_find_closest_elements.scan_at numbers i (j + 1) i j
       else
         clever_020_find_closest_elements.scan_at numbers i (j + 1) best_i best_j) := by
  conv => lhs; unfold clever_020_find_closest_elements.scan_at
  have h_size_lt : numbers.val.size < USize64.size := numbers.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_add1_eq : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
    usize_add_one_eq i h_iov1
  have h_addj1_eq : (j +? (1 : usize) : RustM usize) = RustM.ok (j + 1) :=
    usize_add_one_eq j h_jov
  have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_iov1
  have h_cond_stop :
      ((i + 1) >=? USize64.ofNat numbers.val.size : RustM Bool) = RustM.ok false := by
    show (rust_primitives.cmp.ge (i + 1) _ : RustM Bool) = RustM.ok false
    show (pure (decide _) : RustM Bool) = RustM.ok false
    have h_dec : decide (USize64.ofNat numbers.val.size ≤ i + 1) = false := by
      rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat, h_i1_toNat]
      omega
    rw [h_dec]; rfl
  have h_cond_jump :
      (j >=? USize64.ofNat numbers.val.size : RustM Bool) = RustM.ok false := by
    show (rust_primitives.cmp.ge j _ : RustM Bool) = RustM.ok false
    show (pure (decide _) : RustM Bool) = RustM.ok false
    have h_dec : decide (USize64.ofNat numbers.val.size ≤ j) = false := by
      rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]
      omega
    rw [h_dec]; rfl
  have h_idx_i : (numbers[i]_? : RustM i64) = RustM.ok (numbers.val[i.toNat]'hi) := by
    show (if h : i.toNat < numbers.val.size then pure (numbers.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (numbers.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_idx_j : (numbers[j]_? : RustM i64) = RustM.ok (numbers.val[j.toNat]'h_no_jump) := by
    show (if h : j.toNat < numbers.val.size then pure (numbers.val[j])
            else .fail .arrayOutOfBounds)
        = RustM.ok (numbers.val[j.toNat]'h_no_jump)
    rw [dif_pos h_no_jump]; rfl
  have h_idx_bi : (numbers[best_i]_? : RustM i64)
      = RustM.ok (numbers.val[best_i.toNat]'hbest_i) := by
    show (if h : best_i.toNat < numbers.val.size then pure (numbers.val[best_i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (numbers.val[best_i.toNat]'hbest_i)
    rw [dif_pos hbest_i]; rfl
  have h_idx_bj : (numbers[best_j]_? : RustM i64)
      = RustM.ok (numbers.val[best_j.toNat]'hbest_j) := by
    show (if h : best_j.toNat < numbers.val.size then pure (numbers.val[best_j])
            else .fail .arrayOutOfBounds)
        = RustM.ok (numbers.val[best_j.toNat]'hbest_j)
    rw [dif_pos hbest_j]; rfl
  have h_abs_cur := abs_diff_eval (numbers.val[i.toNat]'hi)
                                   (numbers.val[j.toNat]'h_no_jump) h_sub_ij h_sub_ji
  have h_abs_best := abs_diff_eval (numbers.val[best_i.toNat]'hbest_i)
                                    (numbers.val[best_j.toNat]'hbest_j) h_sub_bibj h_sub_bjbi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             pure_bind, RustM_ok_bind, h_add1_eq, h_addj1_eq,
             h_cond_stop, h_cond_jump, Bool.false_eq_true, ↓reduceIte,
             h_idx_i, h_idx_j, h_idx_bi, h_idx_bj,
             h_abs_cur, h_abs_best, rust_primitives.cmp.lt,
             decide_eq_true_eq]

/-- Bridge: `cur := if a > b then a - b else b - a` has `toInt = natAbs(a-b)`. -/
private theorem abs_diff_val_toInt (a b : i64)
    (h_ab : ¬ Int64.subOverflow a b)
    (h_ba : ¬ Int64.subOverflow b a) :
    ((if a > b then a - b else b - a) : i64).toInt
      = ((a.toInt - b.toInt).natAbs : Int) := by
  by_cases h_gt : a > b
  · rw [if_pos h_gt, Int64.toInt_sub_of_not_subOverflow h_ab]
    have h_gt_int : b.toInt < a.toInt := Int64.lt_iff_toInt_lt.mp h_gt
    have h_pos : 0 ≤ a.toInt - b.toInt := by omega
    rw [Int.natAbs_of_nonneg h_pos]
  · rw [if_neg h_gt, Int64.toInt_sub_of_not_subOverflow h_ba]
    have h_le : a.toInt ≤ b.toInt := by
      rcases Int.lt_or_le b.toInt a.toInt with h_lt | h_ge
      · exact absurd (Int64.lt_iff_toInt_lt.mpr h_lt) h_gt
      · exact h_ge
    have h_neg_pos : 0 ≤ b.toInt - a.toInt := by omega
    have h_eq : a.toInt - b.toInt = -(b.toInt - a.toInt) := by omega
    rw [h_eq, Int.natAbs_neg, Int.natAbs_of_nonneg h_neg_pos]

/-! ## The workhorse correctness lemma for `scan_at`.

Strong induction on the measure
  `(numbers.val.size - i.toNat) * (numbers.val.size + 2) - j.toNat`,
which decreases on both `scan_at` recursion edges (jump: `i → i+1`,
`j → i+2`; step: `j → j+1`). -/

private theorem scan_at_correct
    (numbers : RustSlice i64) (hfit : pairwise_diff_fits numbers) :
    ∀ (μ : Nat) (i j best_i best_j : usize)
      (h_i_le : i.toNat + 1 ≤ numbers.val.size)
      (h_j_le : j.toNat ≤ numbers.val.size)
      (h_ij : i.toNat + 1 ≤ j.toNat)
      (hbest_i : best_i.toNat < numbers.val.size)
      (hbest_j : best_j.toNat < numbers.val.size)
      (hbest_neq : best_i.toNat ≠ best_j.toNat),
      (numbers.val.size - i.toNat) * (numbers.val.size + 2) - j.toNat ≤ μ →
      ∃ (r_i r_j : usize) (h_ri : r_i.toNat < numbers.val.size)
        (h_rj : r_j.toNat < numbers.val.size),
        clever_020_find_closest_elements.scan_at numbers i j best_i best_j
          = RustM.ok ⟨r_i, r_j⟩ ∧
        r_i.toNat ≠ r_j.toNat ∧
        (((numbers.val[r_i.toNat]'h_ri).toInt
            - (numbers.val[r_j.toNat]'h_rj).toInt).natAbs : Int)
          ≤ (((numbers.val[best_i.toNat]'hbest_i).toInt
              - (numbers.val[best_j.toNat]'hbest_j).toInt).natAbs : Int) ∧
        (∀ (p q : Nat) (hp : p < numbers.val.size) (hq : q < numbers.val.size),
            p < q →
            ((p = i.toNat ∧ j.toNat ≤ q) ∨ i.toNat < p) →
            (((numbers.val[r_i.toNat]'h_ri).toInt
                - (numbers.val[r_j.toNat]'h_rj).toInt).natAbs : Int)
              ≤ (((numbers.val[p]'hp).toInt
                  - (numbers.val[q]'hq).toInt).natAbs : Int)) := by
  have h_size_lt : numbers.val.size < USize64.size := numbers.size_lt_usizeSize
  have h_usize_size : (USize64.size : Nat) = 2 ^ 64 := usize_size_eq
  have h_n_lt : numbers.val.size < 2^64 := by rw [← h_usize_size]; exact h_size_lt
  intro μ
  induction μ with
  | zero =>
    -- Measure zero forces i.toNat = numbers.val.size, contradiction with i + 1 ≤ n.
    intro i j best_i best_j h_i_le h_j_le h_ij hbest_i hbest_j hbest_neq hμ
    exfalso
    -- (n - i) * (n + 2) - j ≤ 0
    -- With j ≤ n, (n - i) * (n + 2) ≤ j ≤ n.
    -- (n - i) ≥ 1 (since i + 1 ≤ n means i < n means n - i ≥ 1).
    -- So (n + 2) ≤ (n - i) * (n + 2) ≤ n. Contradiction (since 2 > 0).
    have h_n_minus_i : 1 ≤ numbers.val.size - i.toNat := by omega
    have h1 : numbers.val.size + 2 ≤ (numbers.val.size - i.toNat) * (numbers.val.size + 2) := by
      have := Nat.mul_le_mul_right (numbers.val.size + 2) h_n_minus_i
      simpa using this
    have h2 : (numbers.val.size - i.toNat) * (numbers.val.size + 2) ≤ j.toNat := by
      omega
    omega
  | succ μ ih =>
    intro i j best_i best_j h_i_le h_j_le h_ij hbest_i hbest_j hbest_neq hμ
    have h_iov1 : i.toNat + 1 < 2^64 := by omega
    -- Decide which branch of `scan_at` applies.
    by_cases h_stop : numbers.val.size ≤ i.toNat + 1
    · -- Stop case: i + 1 = n.
      have h_stop_eq : numbers.val.size = i.toNat + 1 := by omega
      refine ⟨best_i, best_j, hbest_i, hbest_j, ?_, hbest_neq, ?_, ?_⟩
      · exact scan_at_stop numbers i j best_i best_j h_iov1 h_stop
      · exact Int.le_refl _
      · intro p q hp hq hpq hcase
        exfalso
        rcases hcase with ⟨hp_eq, hjq⟩ | hpi
        · -- p = i, j ≤ q, but j ≥ i + 1 = n and q < n: contradiction.
          omega
        · -- i < p, but i + 1 = n and p < n: contradiction.
          omega
    · -- Recursive case: i + 1 < n.
      have h_no_stop : i.toNat + 1 < numbers.val.size := Nat.lt_of_not_le h_stop
      have h_i_lt : i.toNat < numbers.val.size := by omega
      have h_i_plus_two_le : i.toNat + 2 ≤ numbers.val.size := by omega
      by_cases h_jump : numbers.val.size ≤ j.toNat
      · -- Jump case: j ≥ n.
        have h_j_eq : j.toNat = numbers.val.size := by omega
        -- Derive overflow guards.
        have h_iov2 : i.toNat + 2 < 2^64 := by omega
        have h_step := scan_at_jump numbers i j best_i best_j h_iov1 h_iov2 h_no_stop h_jump
        -- Apply IH with state (i+1, i+2, best_i, best_j).
        have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_iov1
        have h_i2_toNat : (i + 2).toNat = i.toNat + 2 := usize_add_two_toNat i h_iov2
        have h_i_le' : (i + 1).toNat + 1 ≤ numbers.val.size := by rw [h_i1_toNat]; omega
        have h_j_le' : (i + 2).toNat ≤ numbers.val.size := by rw [h_i2_toNat]; omega
        have h_ij' : (i + 1).toNat + 1 ≤ (i + 2).toNat := by
          rw [h_i1_toNat, h_i2_toNat]; omega
        -- measure decrease.
        have h_mul_split :
            (numbers.val.size - i.toNat) * (numbers.val.size + 2)
              = (numbers.val.size - (i.toNat + 1)) * (numbers.val.size + 2)
                  + (numbers.val.size + 2) := by
          have h_succ : numbers.val.size - i.toNat
                          = (numbers.val.size - (i.toNat + 1)) + 1 := by omega
          calc (numbers.val.size - i.toNat) * (numbers.val.size + 2)
              = ((numbers.val.size - (i.toNat + 1)) + 1) * (numbers.val.size + 2) := by
                  rw [h_succ]
            _ = (numbers.val.size - (i.toNat + 1)) * (numbers.val.size + 2)
                + 1 * (numbers.val.size + 2) := Nat.add_mul _ _ _
            _ = (numbers.val.size - (i.toNat + 1)) * (numbers.val.size + 2)
                + (numbers.val.size + 2) := by rw [Nat.one_mul]
        have h_old_lower :
            (numbers.val.size - i.toNat) * (numbers.val.size + 2) - numbers.val.size ≤ μ + 1 := by
          have h_tmp := hμ
          rw [h_j_eq] at h_tmp
          exact h_tmp
        have h_μ' : (numbers.val.size - (i + 1).toNat) * (numbers.val.size + 2)
                      - (i + 2).toNat ≤ μ := by
          rw [h_i1_toNat, h_i2_toNat, h_mul_split] at *
          omega
        obtain ⟨r_i, r_j, h_ri, h_rj, h_eq, h_neq, h_best, h_future⟩ :=
          ih (i + 1) (i + 2) best_i best_j h_i_le' h_j_le' h_ij'
             hbest_i hbest_j hbest_neq h_μ'
        refine ⟨r_i, r_j, h_ri, h_rj, ?_, h_neq, h_best, ?_⟩
        · rw [h_step]; exact h_eq
        · intro p q hp hq hpq hcase
          apply h_future p q hp hq hpq
          rcases hcase with ⟨hp_eq, hjq⟩ | hpi
          · -- p = i.toNat, j.toNat ≤ q. In the new state (i+1, i+2), we have:
            --   either p = (i+1).toNat ∧ (i+2).toNat ≤ q, or (i+1).toNat < p.
            -- p = i, so p < i + 1 means we need the second disjunct.
            -- But i + 1 ≤ p means i + 1 ≤ i, false. So this branch is impossible.
            -- Actually p = i. We have i + 1 ≤ j ≤ q < n, so q ≥ j ≥ i + 1.
            -- The relevant disjunct from new state: in new state (i+1, i+2):
            --   (p = i + 1 ∧ i + 2 ≤ q) or i + 1 < p.
            -- Since p = i (here), neither holds.
            -- Wait, we need to derive future from old future. The OLD pair (p, q) maps to a NEW future pair iff...
            -- Hmm actually the old pair (p = i, q ≥ j) is included in the new future set
            -- iff it matches one of: (p = i+1 ∧ q ≥ i+2) or p > i+1.
            -- p = i ≠ i + 1, so first disjunct fails. p = i ≤ i+1 fails second.
            -- So this pair is NOT in the new future set. But we still need to bound it!
            -- The bound comes from: the pair (i, q) with q ≥ j = n is impossible since q < n.
            -- Wait, j = n and j ≤ q ≤ n - 1 = j - 1, contradiction. So no such pair exists.
            exfalso
            omega
          · -- i < p in old state; for new state we need (i+1 < p) or (p = i+1 ∧ i+2 ≤ q).
            -- Case: p = i + 1. Then (p = i + 1) and we need i + 2 ≤ q.
            --   Since p < q and p = i + 1, q ≥ i + 2. ✓
            -- Case: p > i + 1. Then i + 1 < p. ✓
            rcases Nat.lt_or_ge (i.toNat + 1) p with hp_gt | hp_le
            · right; rw [h_i1_toNat]; exact hp_gt
            · -- p = i + 1 (since i < p and p ≤ i + 1)
              have hp_eq : p = i.toNat + 1 := by omega
              left
              constructor
              · rw [h_i1_toNat]; exact hp_eq
              · rw [h_i2_toNat]
                -- p < q and p = i + 1, so q ≥ i + 2.
                omega
      · -- Step case: j < n.
        have h_j_lt : j.toNat < numbers.val.size := Nat.lt_of_not_le h_jump
        -- Derive overflow guards.
        have h_jov : j.toNat + 1 < 2^64 := by omega
        -- Derive no-overflow conditions for abs_diff calls.
        have h_sub_ij := no_sub_overflow_of_fit numbers hfit i.toNat j.toNat h_i_lt h_j_lt
        have h_sub_ji := no_sub_overflow_of_fit numbers hfit j.toNat i.toNat h_j_lt h_i_lt
        have h_sub_bibj := no_sub_overflow_of_fit numbers hfit
                              best_i.toNat best_j.toNat hbest_i hbest_j
        have h_sub_bjbi := no_sub_overflow_of_fit numbers hfit
                              best_j.toNat best_i.toNat hbest_j hbest_i
        have h_step_eq := scan_at_step numbers i j best_i best_j h_iov1 h_jov
                            h_no_stop h_j_lt hbest_i hbest_j h_i_lt
                            h_sub_ij h_sub_ji h_sub_bibj h_sub_bjbi
        -- Define cur and best i64-values via local abbreviations.
        let ni : i64 := numbers.val[i.toNat]'h_i_lt
        let nj : i64 := numbers.val[j.toNat]'h_j_lt
        let nbi : i64 := numbers.val[best_i.toNat]'hbest_i
        let nbj : i64 := numbers.val[best_j.toNat]'hbest_j
        let cur : i64 := if ni > nj then ni - nj else nj - ni
        let best : i64 := if nbi > nbj then nbi - nbj else nbj - nbi
        -- The diffs in Int.
        have h_cur_int :
            cur.toInt = ((ni.toInt - nj.toInt).natAbs : Int) :=
          abs_diff_val_toInt ni nj h_sub_ij h_sub_ji
        have h_best_int :
            best.toInt = ((nbi.toInt - nbj.toInt).natAbs : Int) :=
          abs_diff_val_toInt nbi nbj h_sub_bibj h_sub_bjbi
        -- Bound for j + 1.
        have h_j1_toNat : (j + 1).toNat = j.toNat + 1 := usize_add_one_toNat j h_jov
        have h_j1_le : (j + 1).toNat ≤ numbers.val.size := by rw [h_j1_toNat]; omega
        have h_ij_new : i.toNat + 1 ≤ (j + 1).toNat := by rw [h_j1_toNat]; omega
        -- Measure decrease.
        have h_μ_new :
            (numbers.val.size - i.toNat) * (numbers.val.size + 2) - (j + 1).toNat ≤ μ := by
          rw [h_j1_toNat]
          omega
        by_cases h_cmp : cur < best
        · -- Take (i, j) as new best.
          have h_i_neq_j : i.toNat ≠ j.toNat := by omega
          obtain ⟨r_i, r_j, h_ri, h_rj, h_eq, h_neq, h_best_ij, h_future⟩ :=
            ih i (j + 1) i j h_i_le h_j1_le h_ij_new
               h_i_lt h_j_lt h_i_neq_j h_μ_new
          refine ⟨r_i, r_j, h_ri, h_rj, ?_, h_neq, ?_, ?_⟩
          · rw [h_step_eq]
            -- LHS after step_eq: `let cur' := …; let best' := …; if cur' < best' then … else …`
            -- which is the same as cur and best with `set`.
            show (if cur < best then
                    clever_020_find_closest_elements.scan_at numbers i (j + 1) i j
                  else
                    clever_020_find_closest_elements.scan_at numbers i (j + 1) best_i best_j)
                = RustM.ok ⟨r_i, r_j⟩
            rw [if_pos h_cmp]
            exact h_eq
          · -- bound r_diff ≤ best_old_diff.
            -- h_best_ij : r_diff ≤ |ni - nj|.natAbs (the new best is (i, j))
            -- h_cmp : cur < best, equiv to |ni - nj|.natAbs < |nbi - nbj|.natAbs
            have h_cur_lt_best : cur.toInt < best.toInt := Int64.lt_iff_toInt_lt.mp h_cmp
            rw [h_cur_int, h_best_int] at h_cur_lt_best
            calc (((numbers.val[r_i.toNat]'h_ri).toInt
                    - (numbers.val[r_j.toNat]'h_rj).toInt).natAbs : Int)
                ≤ ((ni.toInt - nj.toInt).natAbs : Int) := h_best_ij
              _ ≤ ((nbi.toInt - nbj.toInt).natAbs : Int) := by omega
          · -- future bound
            intro p q hp hq hpq hcase
            -- We have h_future for the new state (i, j+1, i, j).
            -- For pair (p, q): if (p = i ∧ q ≥ j+1) ∨ p > i, use h_future directly.
            -- If p = i ∧ q = j, use the bound from h_best_ij directly.
            rcases hcase with ⟨hp_eq, hjq⟩ | hpi
            · subst hp_eq
              rcases Nat.lt_or_ge q (j.toNat + 1) with hq_lt | hq_ge
              · -- q = j (since j ≤ q < j + 1)
                have hq_eq : q = j.toNat := by omega
                subst hq_eq
                exact h_best_ij
              · -- q ≥ j + 1; use h_future at (i, q)
                apply h_future i.toNat q hp hq hpq
                left
                refine ⟨rfl, ?_⟩
                rw [h_j1_toNat]; exact hq_ge
            · apply h_future p q hp hq hpq
              right; exact hpi
        · -- Keep (best_i, best_j).
          obtain ⟨r_i, r_j, h_ri, h_rj, h_eq, h_neq, h_best_keep, h_future⟩ :=
            ih i (j + 1) best_i best_j h_i_le h_j1_le h_ij_new
               hbest_i hbest_j hbest_neq h_μ_new
          refine ⟨r_i, r_j, h_ri, h_rj, ?_, h_neq, h_best_keep, ?_⟩
          · rw [h_step_eq]
            show (if cur < best then
                    clever_020_find_closest_elements.scan_at numbers i (j + 1) i j
                  else
                    clever_020_find_closest_elements.scan_at numbers i (j + 1) best_i best_j)
                = RustM.ok ⟨r_i, r_j⟩
            rw [if_neg h_cmp]
            exact h_eq
          · intro p q hp hq hpq hcase
            rcases hcase with ⟨hp_eq, hjq⟩ | hpi
            · subst hp_eq
              rcases Nat.lt_or_ge q (j.toNat + 1) with hq_lt | hq_ge
              · have hq_eq : q = j.toNat := by omega
                subst hq_eq
                -- r_diff ≤ best.toInt and best.toInt ≤ cur.toInt = |ni - nj|.natAbs
                have h_best_le_cur : best.toInt ≤ cur.toInt := by
                  rcases Int.lt_or_le cur.toInt best.toInt with h_lt | h_ge
                  · exact absurd (Int64.lt_iff_toInt_lt.mpr h_lt) h_cmp
                  · exact h_ge
                rw [h_best_int, h_cur_int] at h_best_le_cur
                calc (((numbers.val[r_i.toNat]'h_ri).toInt
                        - (numbers.val[r_j.toNat]'h_rj).toInt).natAbs : Int)
                    ≤ ((nbi.toInt - nbj.toInt).natAbs : Int) := h_best_keep
                  _ ≤ ((ni.toInt - nj.toInt).natAbs : Int) := by omega
              · apply h_future i.toNat q hp hq hpq
                left
                refine ⟨rfl, ?_⟩
                rw [h_j1_toNat]; exact hq_ge
            · apply h_future p q hp hq hpq
              right; exact hpi

/-! ## Top-level theorems. -/

/-- Failure / defensive boundary: when the documented precondition
    `numbers.size ≥ 2` is violated, the function returns `(0, 0)`
    successfully. -/
theorem short_input_returns_zero_zero
    (numbers : RustSlice i64)
    (hshort : numbers.val.size < 2) :
    clever_020_find_closest_elements.find_closest_elements numbers
      = RustM.ok (rust_primitives.hax.Tuple2.mk (0 : i64) (0 : i64)) := by
  unfold clever_020_find_closest_elements.find_closest_elements
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' numbers.size_lt_usizeSize
  have h_two_toNat : (2 : usize).toNat = 2 := usize_two_toNat
  have h_cond : decide ((USize64.ofNat numbers.val.size) < (2 : usize)) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.lt_iff_toNat_lt, h_ofNat, h_two_toNat]
    exact hshort
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.lt, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-! ## Find_closest_elements composition

Combine `scan_at_correct` with the outer `find_closest_elements` body
(short-input branch already handled; here we're in the `n ≥ 2` branch). -/

private theorem find_closest_elements_eval
    (numbers : RustSlice i64)
    (hlen : 2 ≤ numbers.val.size)
    (hfit : pairwise_diff_fits numbers) :
    ∃ (r_i r_j : usize) (h_ri : r_i.toNat < numbers.val.size)
       (h_rj : r_j.toNat < numbers.val.size),
      r_i.toNat ≠ r_j.toNat ∧
      clever_020_find_closest_elements.find_closest_elements numbers
        = (if (numbers.val[r_i.toNat]'h_ri) ≤ (numbers.val[r_j.toNat]'h_rj)
           then RustM.ok (rust_primitives.hax.Tuple2.mk
                  (numbers.val[r_i.toNat]'h_ri) (numbers.val[r_j.toNat]'h_rj))
           else RustM.ok (rust_primitives.hax.Tuple2.mk
                  (numbers.val[r_j.toNat]'h_rj) (numbers.val[r_i.toNat]'h_ri))) ∧
      (∀ (p q : Nat) (hp : p < numbers.val.size) (hq : q < numbers.val.size),
         p < q →
         (((numbers.val[r_i.toNat]'h_ri).toInt
              - (numbers.val[r_j.toNat]'h_rj).toInt).natAbs : Int)
           ≤ (((numbers.val[p]'hp).toInt
               - (numbers.val[q]'hq).toInt).natAbs : Int)) := by
  -- Apply scan_at_correct with the initial state (0, 1, 0, 1).
  have h_0lt : (0 : Nat) < numbers.val.size := by omega
  have h_1lt : (1 : Nat) < numbers.val.size := by omega
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_one_toNat : (1 : usize).toNat = 1 := usize_one_toNat
  have h_i_le : (0 : usize).toNat + 1 ≤ numbers.val.size := by
    rw [h_zero_toNat]; omega
  have h_j_le : (1 : usize).toNat ≤ numbers.val.size := by
    rw [h_one_toNat]; omega
  have h_ij : (0 : usize).toNat + 1 ≤ (1 : usize).toNat := by
    rw [h_zero_toNat, h_one_toNat]; omega
  have h_zero_lt_size : (0 : usize).toNat < numbers.val.size := by
    rw [h_zero_toNat]; omega
  have h_one_lt_size : (1 : usize).toNat < numbers.val.size := by
    rw [h_one_toNat]; omega
  have h_zero_neq_one : (0 : usize).toNat ≠ (1 : usize).toNat := by
    rw [h_zero_toNat, h_one_toNat]; decide
  obtain ⟨r_i, r_j, h_ri, h_rj, h_scan_eq, h_neq, _, h_future⟩ :=
    scan_at_correct numbers hfit
      ((numbers.val.size - 0) * (numbers.val.size + 2) - 1)
      (0 : usize) (1 : usize) (0 : usize) (1 : usize)
      h_i_le h_j_le h_ij h_zero_lt_size h_one_lt_size h_zero_neq_one
      (Nat.le_refl _)
  -- Reduce find_closest_elements using h_scan_eq.
  refine ⟨r_i, r_j, h_ri, h_rj, h_neq, ?_, ?_⟩
  · unfold clever_020_find_closest_elements.find_closest_elements
    have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
      USize64.toNat_ofNat_of_lt' numbers.size_lt_usizeSize
    have h_two_toNat : (2 : usize).toNat = 2 := usize_two_toNat
    have h_cond_short :
        ((USize64.ofNat numbers.val.size) <? (2 : usize) : RustM Bool) = RustM.ok false := by
      show (rust_primitives.cmp.lt _ _ : RustM Bool) = RustM.ok false
      show (pure (decide _) : RustM Bool) = RustM.ok false
      have h_dec : decide ((USize64.ofNat numbers.val.size) < (2 : usize)) = false := by
        rw [decide_eq_false_iff_not, USize64.lt_iff_toNat_lt, h_ofNat, h_two_toNat]
        omega
      rw [h_dec]; rfl
    have h_idx_ri : (numbers[r_i]_? : RustM i64) = RustM.ok (numbers.val[r_i.toNat]'h_ri) := by
      show (if h : r_i.toNat < numbers.val.size then pure (numbers.val[r_i])
              else .fail .arrayOutOfBounds)
          = RustM.ok (numbers.val[r_i.toNat]'h_ri)
      rw [dif_pos h_ri]; rfl
    have h_idx_rj : (numbers[r_j]_? : RustM i64) = RustM.ok (numbers.val[r_j.toNat]'h_rj) := by
      show (if h : r_j.toNat < numbers.val.size then pure (numbers.val[r_j])
              else .fail .arrayOutOfBounds)
          = RustM.ok (numbers.val[r_j.toNat]'h_rj)
      rw [dif_pos h_rj]; rfl
    simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
               pure_bind, RustM_ok_bind, h_cond_short, Bool.false_eq_true, ↓reduceIte,
               h_scan_eq, h_idx_ri, h_idx_rj, rust_primitives.cmp.le, decide_eq_true_eq]
    by_cases h_le : (numbers.val[r_i.toNat]'h_ri) ≤ (numbers.val[r_j.toNat]'h_rj)
    · rw [if_pos h_le, if_pos h_le]; rfl
    · rw [if_neg h_le, if_neg h_le]; rfl
  · intro p q hp hq hpq
    apply h_future p q hp hq hpq
    -- Either p = 0 ∧ 1 ≤ q, or 0 < p.
    rcases Nat.eq_zero_or_pos p with hp_zero | hp_pos
    · left
      refine ⟨?_, ?_⟩
      · rw [h_zero_toNat]; exact hp_zero
      · rw [h_one_toNat]; omega
    · right
      rw [h_zero_toNat]; exact hp_pos

/-- Postcondition 1 (ordered output). -/
theorem result_is_ordered
    (numbers : RustSlice i64)
    (hlen : 2 ≤ numbers.val.size)
    (hfit : pairwise_diff_fits numbers) :
    ∃ a b : i64,
      clever_020_find_closest_elements.find_closest_elements numbers
        = RustM.ok (rust_primitives.hax.Tuple2.mk a b)
      ∧ a.toInt ≤ b.toInt := by
  obtain ⟨r_i, r_j, h_ri, h_rj, _, h_eq, _⟩ := find_closest_elements_eval numbers hlen hfit
  by_cases h_le : (numbers.val[r_i.toNat]'h_ri) ≤ (numbers.val[r_j.toNat]'h_rj)
  · refine ⟨numbers.val[r_i.toNat]'h_ri, numbers.val[r_j.toNat]'h_rj, ?_, ?_⟩
    · rw [h_eq, if_pos h_le]
    · exact Int64.le_iff_toInt_le.mp h_le
  · refine ⟨numbers.val[r_j.toNat]'h_rj, numbers.val[r_i.toNat]'h_ri, ?_, ?_⟩
    · rw [h_eq, if_neg h_le]
    · -- ¬ a ≤ b means b ≤ a... wait actually ¬ (numbers[r_i] ≤ numbers[r_j])
      -- means numbers[r_j] < numbers[r_i], so we have numbers[r_j].toInt ≤ numbers[r_i].toInt.
      rcases Int.lt_or_le (numbers.val[r_i.toNat]'h_ri).toInt
                          (numbers.val[r_j.toNat]'h_rj).toInt with h_lt | h_ge
      · exact absurd (Int64.le_iff_toInt_le.mpr (Int.le_of_lt h_lt)) h_le
      · exact h_ge

/-- Postcondition 2 (values drawn from input). -/
theorem result_elements_drawn_from_input
    (numbers : RustSlice i64)
    (hlen : 2 ≤ numbers.val.size)
    (hfit : pairwise_diff_fits numbers) :
    ∃ a b : i64,
      clever_020_find_closest_elements.find_closest_elements numbers
        = RustM.ok (rust_primitives.hax.Tuple2.mk a b)
      ∧ ∃ (i j : Nat) (hi : i < numbers.val.size) (hj : j < numbers.val.size),
          i ≠ j ∧ (numbers.val[i]'hi) = a ∧ (numbers.val[j]'hj) = b := by
  obtain ⟨r_i, r_j, h_ri, h_rj, h_neq, h_eq, _⟩ := find_closest_elements_eval numbers hlen hfit
  by_cases h_le : (numbers.val[r_i.toNat]'h_ri) ≤ (numbers.val[r_j.toNat]'h_rj)
  · refine ⟨numbers.val[r_i.toNat]'h_ri, numbers.val[r_j.toNat]'h_rj, ?_,
            r_i.toNat, r_j.toNat, h_ri, h_rj, h_neq, rfl, rfl⟩
    rw [h_eq, if_pos h_le]
  · refine ⟨numbers.val[r_j.toNat]'h_rj, numbers.val[r_i.toNat]'h_ri, ?_,
            r_j.toNat, r_i.toNat, h_rj, h_ri, ?_, rfl, rfl⟩
    · rw [h_eq, if_neg h_le]
    · exact fun h => h_neq h.symm

/-- Postcondition 3 (minimum difference). -/
theorem result_difference_is_minimum
    (numbers : RustSlice i64)
    (hlen : 2 ≤ numbers.val.size)
    (hfit : pairwise_diff_fits numbers) :
    ∃ a b : i64,
      clever_020_find_closest_elements.find_closest_elements numbers
        = RustM.ok (rust_primitives.hax.Tuple2.mk a b)
      ∧ a.toInt ≤ b.toInt
      ∧ ∀ (i j : Nat) (hi : i < numbers.val.size) (hj : j < numbers.val.size),
          i ≠ j →
          b.toInt - a.toInt
            ≤ (((numbers.val[i]'hi).toInt - (numbers.val[j]'hj).toInt).natAbs : Int) := by
  obtain ⟨r_i, r_j, h_ri, h_rj, h_neq, h_eq, h_future⟩ :=
    find_closest_elements_eval numbers hlen hfit
  -- Helper: natAbs is symmetric.
  have h_natAbs_sym :
      ∀ (a b : Int), (a - b).natAbs = (b - a).natAbs := by
    intro a b
    rw [show a - b = -(b - a) by omega, Int.natAbs_neg]
  -- Pair-comparison bound: the bound holds for any unordered pair (p, q).
  have h_bound_any :
      ∀ (p q : Nat) (hp : p < numbers.val.size) (hq : q < numbers.val.size),
        p ≠ q →
        (((numbers.val[r_i.toNat]'h_ri).toInt
            - (numbers.val[r_j.toNat]'h_rj).toInt).natAbs : Int)
          ≤ (((numbers.val[p]'hp).toInt - (numbers.val[q]'hq).toInt).natAbs : Int) := by
    intro p q hp hq hpq_ne
    rcases Nat.lt_or_ge p q with hpq_lt | hpq_ge
    · exact h_future p q hp hq hpq_lt
    · have hpq_gt : q < p := Nat.lt_of_le_of_ne hpq_ge (fun h => hpq_ne h.symm)
      have h_bound := h_future q p hq hp hpq_gt
      have h_sym_pq :
          ((numbers.val[p]'hp).toInt - (numbers.val[q]'hq).toInt).natAbs
            = ((numbers.val[q]'hq).toInt - (numbers.val[p]'hp).toInt).natAbs :=
        h_natAbs_sym _ _
      rw [h_sym_pq]; exact h_bound
  by_cases h_le : (numbers.val[r_i.toNat]'h_ri) ≤ (numbers.val[r_j.toNat]'h_rj)
  · refine ⟨numbers.val[r_i.toNat]'h_ri, numbers.val[r_j.toNat]'h_rj, ?_,
            Int64.le_iff_toInt_le.mp h_le, ?_⟩
    · rw [h_eq, if_pos h_le]
    · intro i j hi hj hij_ne
      -- b.toInt - a.toInt = numbers[r_j].toInt - numbers[r_i].toInt
      --                   = (numbers[r_j].toInt - numbers[r_i].toInt).natAbs (since non-neg)
      --                   = (numbers[r_i].toInt - numbers[r_j].toInt).natAbs (by symmetry)
      have h_le_int : (numbers.val[r_i.toNat]'h_ri).toInt
                        ≤ (numbers.val[r_j.toNat]'h_rj).toInt := Int64.le_iff_toInt_le.mp h_le
      have h_bma_eq :
          (numbers.val[r_j.toNat]'h_rj).toInt - (numbers.val[r_i.toNat]'h_ri).toInt
            = (((numbers.val[r_i.toNat]'h_ri).toInt
                  - (numbers.val[r_j.toNat]'h_rj).toInt).natAbs : Int) := by
        rw [h_natAbs_sym]
        have h_nonneg : 0 ≤ (numbers.val[r_j.toNat]'h_rj).toInt
                            - (numbers.val[r_i.toNat]'h_ri).toInt := by omega
        rw [Int.natAbs_of_nonneg h_nonneg]
      rw [h_bma_eq]
      exact h_bound_any i j hi hj hij_ne
  · refine ⟨numbers.val[r_j.toNat]'h_rj, numbers.val[r_i.toNat]'h_ri, ?_, ?_, ?_⟩
    · rw [h_eq, if_neg h_le]
    · rcases Int.lt_or_le (numbers.val[r_i.toNat]'h_ri).toInt
                          (numbers.val[r_j.toNat]'h_rj).toInt with h_lt | h_ge
      · exact absurd (Int64.le_iff_toInt_le.mpr (Int.le_of_lt h_lt)) h_le
      · exact h_ge
    · intro i j hi hj hij_ne
      -- b.toInt - a.toInt = numbers[r_i].toInt - numbers[r_j].toInt
      --                   = (numbers[r_i].toInt - numbers[r_j].toInt).natAbs (since non-neg)
      have h_ge_int : (numbers.val[r_j.toNat]'h_rj).toInt
                       ≤ (numbers.val[r_i.toNat]'h_ri).toInt := by
        rcases Int.lt_or_le (numbers.val[r_i.toNat]'h_ri).toInt
                            (numbers.val[r_j.toNat]'h_rj).toInt with h_lt | h_ge
        · exact absurd (Int64.le_iff_toInt_le.mpr (Int.le_of_lt h_lt)) h_le
        · exact h_ge
      have h_bma_eq :
          (numbers.val[r_i.toNat]'h_ri).toInt - (numbers.val[r_j.toNat]'h_rj).toInt
            = (((numbers.val[r_i.toNat]'h_ri).toInt
                  - (numbers.val[r_j.toNat]'h_rj).toInt).natAbs : Int) := by
        have h_nonneg : 0 ≤ (numbers.val[r_i.toNat]'h_ri).toInt
                            - (numbers.val[r_j.toNat]'h_rj).toInt := by omega
        rw [Int.natAbs_of_nonneg h_nonneg]
      rw [h_bma_eq]
      exact h_bound_any i j hi hj hij_ne

end Clever_020_find_closest_elementsObligations
