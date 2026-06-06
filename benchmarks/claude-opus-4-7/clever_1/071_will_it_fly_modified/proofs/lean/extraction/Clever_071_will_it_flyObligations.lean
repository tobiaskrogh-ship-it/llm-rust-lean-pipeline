-- Companion obligations file for the `clever_071_will_it_fly` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_071_will_it_fly

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_071_will_it_flyObligations

/-! ## Specifications: integer-valued prefix sum and palindrome predicate -/

/-- Integer-valued prefix sum of `q`. -/
private def prefix_sum_int (q : RustSlice i64) : Nat → Int
  | 0     => 0
  | k + 1 =>
      prefix_sum_int q k +
        (if h : k < q.val.size then (q.val[k]'h).toInt else 0)

/-- `q` is a palindrome: every pair of indices summing to `size - 1`
    holds equal values. -/
private def is_palindrome (q : RustSlice i64) : Prop :=
  ∀ i j : Nat, i + j + 1 = q.val.size →
    ∀ (hi : i < q.val.size) (hj : j < q.val.size),
      q.val[i]'hi = q.val[j]'hj

/-! ## Generic helpers (numeric, bind, etc.) -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl
private theorem usize_zero_toNat : (0 : usize).toNat = 0 := rfl

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

private theorem usize_sub_one_toNat (j : usize) (hj : 1 ≤ j.toNat) :
    (j - 1).toNat = j.toNat - 1 := by
  have h_pre : (1 : usize).toNat ≤ j.toNat := by rw [usize_one_toNat]; exact hj
  rw [USize64.toNat_sub_of_le' h_pre, usize_one_toNat]

private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide

/-- Two indices give equal values if the index naturals are equal. -/
private theorem getElem_idx_congr (q : RustSlice i64) (a b : Nat)
    (ha : a < q.val.size) (hb : b < q.val.size) (h : a = b) :
    q.val[a]'ha = q.val[b]'hb := by
  subst h; rfl

/-- Step of `prefix_sum_int`. -/
private theorem prefix_sum_int_succ
    (q : RustSlice i64) (k : Nat) (hk : k < q.val.size) :
    prefix_sum_int q (k + 1) =
      prefix_sum_int q k + (q.val[k]'hk).toInt := by
  show prefix_sum_int q k
        + (if h : k < q.val.size then (q.val[k]'h).toInt else 0)
       = prefix_sum_int q k + (q.val[k]'hk).toInt
  rw [dif_pos hk]

/-! ## Step lemmas for `sum_at` -/

/-- OOB step: when `i.toNat ≥ q.val.size`, the function returns `RustM.ok acc`. -/
private theorem sum_at_oob (q : RustSlice i64) (i : usize) (acc : i64)
    (hi : q.val.size ≤ i.toNat) :
    clever_071_will_it_fly.sum_at q i acc = RustM.ok acc := by
  conv => lhs; unfold clever_071_will_it_fly.sum_at
  have h_ofNat : (USize64.ofNat q.val.size).toNat = q.val.size :=
    USize64.toNat_ofNat_of_lt' q.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat q.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- Recursion step: when `i.toNat < q.val.size` and the signed addition
    `acc + q[i]` does not overflow, `sum_at` delegates to
    `sum_at q (i+1) (acc + q[i])`. -/
private theorem sum_at_recurse (q : RustSlice i64) (i : usize) (acc : i64)
    (hi : i.toNat < q.val.size)
    (hno : ¬ Int64.addOverflow acc (q.val[i.toNat]'hi)) :
    clever_071_will_it_fly.sum_at q i acc =
      clever_071_will_it_fly.sum_at q (i + 1) (acc + q.val[i.toNat]'hi) := by
  conv => lhs; unfold clever_071_will_it_fly.sum_at
  have h_size_lt : q.val.size < 2^64 := q.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat q.val.size).toNat = q.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat q.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (q[i]_? : RustM i64) = RustM.ok (q.val[i.toNat]'hi) := by
    show (if h : i.toNat < q.val.size then pure (q.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (q.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
  have h_no_bv :
      BitVec.saddOverflow acc.toBitVec (q.val[i.toNat]'hi).toBitVec = false := by
    have hno' : ¬ (BitVec.saddOverflow acc.toBitVec
                                        (q.val[i.toNat]'hi).toBitVec = true) := hno
    cases hb : BitVec.saddOverflow acc.toBitVec (q.val[i.toNat]'hi).toBitVec with
    | false => rfl
    | true => exact absurd hb hno'
  have h_add :
      (acc +? (q.val[i.toNat]'hi) : RustM i64) =
        RustM.ok (acc + q.val[i.toNat]'hi) := by
    show (rust_primitives.ops.arith.Add.add acc (q.val[i.toNat]'hi) : RustM i64) = _
    show (if BitVec.saddOverflow acc.toBitVec (q.val[i.toNat]'hi).toBitVec then
            (.fail .integerOverflow : RustM i64)
          else pure (acc + q.val[i.toNat]'hi)) = _
    rw [h_no_bv]; rfl
  have h_no_ov_i : i.toNat + 1 < 2^64 := by omega
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
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.ops.arith.Add.add, h_no_bv, h_no_bv_i]

/-! ## Strong induction for `sum_at` -/

private theorem sum_at_correct (q : RustSlice i64)
    (hfit : ∀ k : Nat, k ≤ q.val.size →
              -(2^63 : Int) ≤ prefix_sum_int q k ∧ prefix_sum_int q k < 2^63) :
    ∀ (m : Nat) (i : usize) (acc : i64),
      q.val.size - i.toNat ≤ m →
      i.toNat ≤ q.val.size →
      acc.toInt = prefix_sum_int q i.toNat →
      ∃ s : i64,
        clever_071_will_it_fly.sum_at q i acc = RustM.ok s ∧
        s.toInt = prefix_sum_int q q.val.size := by
  intro m
  induction m with
  | zero =>
    intro i acc hm hi_le hinv
    have hi_ge : q.val.size ≤ i.toNat := by omega
    have hi_eq : i.toNat = q.val.size := by omega
    refine ⟨acc, sum_at_oob q i acc hi_ge, ?_⟩
    rw [hinv, hi_eq]
  | succ m ih =>
    intro i acc hm hi_le hinv
    by_cases hi_ge : q.val.size ≤ i.toNat
    · have hi_eq : i.toNat = q.val.size := by omega
      refine ⟨acc, sum_at_oob q i acc hi_ge, ?_⟩
      rw [hinv, hi_eq]
    · have hi_lt : i.toNat < q.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : q.val.size < 2^64 := q.size_lt_usizeSize
      have h_psum_succ :
          prefix_sum_int q (i.toNat + 1) =
            prefix_sum_int q i.toNat + (q.val[i.toNat]'hi_lt).toInt :=
        prefix_sum_int_succ q i.toNat hi_lt
      have h_fit_succ := hfit (i.toNat + 1) (by omega)
      have h_new_bounds :
          -(2^63 : Int) ≤ prefix_sum_int q i.toNat + (q.val[i.toNat]'hi_lt).toInt ∧
          prefix_sum_int q i.toNat + (q.val[i.toNat]'hi_lt).toInt < 2^63 := by
        rw [← h_psum_succ]; exact h_fit_succ
      have hno : ¬ Int64.addOverflow acc (q.val[i.toNat]'hi_lt) := by
        intro hov
        rw [Int64.addOverflow_iff] at hov
        rw [hinv] at hov
        rcases hov with hov_pos | hov_neg
        · have := h_new_bounds.2; omega
        · have := h_new_bounds.1; omega
      have h_new_toInt :
          (acc + q.val[i.toNat]'hi_lt).toInt =
            acc.toInt + (q.val[i.toNat]'hi_lt).toInt :=
        Int64.toInt_add_of_not_addOverflow hno
      have h_new_inv :
          (acc + q.val[i.toNat]'hi_lt).toInt = prefix_sum_int q (i.toNat + 1) := by
        rw [h_new_toInt, hinv, h_psum_succ]
      have h_rec := sum_at_recurse q i acc hi_lt hno
      have h_no_ov_i : i.toNat + 1 < 2^64 := by omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_inv' :
          (acc + q.val[i.toNat]'hi_lt).toInt = prefix_sum_int q (i + 1).toNat := by
        rw [h_i1]; exact h_new_inv
      have h_i1_le : (i + 1).toNat ≤ q.val.size := by rw [h_i1]; omega
      have h_m_le : q.val.size - (i + 1).toNat ≤ m := by
        rw [h_i1]; omega
      obtain ⟨s, h_s_eq, h_s_toInt⟩ :=
        ih (i + 1) (acc + q.val[i.toNat]'hi_lt) h_m_le h_i1_le h_inv'
      refine ⟨s, ?_, h_s_toInt⟩
      rw [h_rec]; exact h_s_eq

/-! ## Step lemmas for `is_palindrome_at` -/

/-- OOB step: when `j ≤ i`, the function returns `RustM.ok true`. -/
private theorem is_palindrome_at_oob (q : RustSlice i64) (i j : usize)
    (hij : j.toNat ≤ i.toNat) :
    clever_071_will_it_fly.is_palindrome_at q i j = RustM.ok true := by
  conv => lhs; unfold clever_071_will_it_fly.is_palindrome_at
  have h_cond : decide (j ≤ i) = true := by
    rw [decide_eq_true_iff, USize64.le_iff_toNat_le]; exact hij
  simp only [rust_primitives.cmp.ge, pure_bind, h_cond, ↓reduceIte]
  rfl

/-- Mismatch step. -/
private theorem is_palindrome_at_mismatch (q : RustSlice i64) (i j : usize)
    (hi : i.toNat < q.val.size) (hj : j.toNat < q.val.size)
    (hij : i.toNat < j.toNat)
    (hne : q.val[i.toNat]'hi ≠ q.val[j.toNat]'hj) :
    clever_071_will_it_fly.is_palindrome_at q i j = RustM.ok false := by
  conv => lhs; unfold clever_071_will_it_fly.is_palindrome_at
  have h_cond_ge : decide (j ≤ i) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le]
    omega
  have h_idx_i : (q[i]_? : RustM i64) = RustM.ok (q.val[i.toNat]'hi) := by
    show (if h : i.toNat < q.val.size then pure (q.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (q.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_idx_j : (q[j]_? : RustM i64) = RustM.ok (q.val[j.toNat]'hj) := by
    show (if h : j.toNat < q.val.size then pure (q.val[j]) else .fail .arrayOutOfBounds)
        = RustM.ok (q.val[j.toNat]'hj)
    rw [dif_pos hj]; rfl
  have h_bne_true : (q.val[i.toNat]'hi != q.val[j.toNat]'hj) = true := by
    rw [bne_iff_ne]; exact hne
  simp only [rust_primitives.cmp.ge, pure_bind, h_cond_ge, Bool.false_eq_true, ↓reduceIte,
             RustM_ok_bind, h_idx_i, h_idx_j,
             rust_primitives.cmp.ne, h_bne_true]
  rfl

/-- Recurse step. -/
private theorem is_palindrome_at_recurse (q : RustSlice i64) (i j : usize)
    (hi : i.toNat < q.val.size) (hj : j.toNat < q.val.size)
    (hij : i.toNat < j.toNat)
    (heq : q.val[i.toNat]'hi = q.val[j.toNat]'hj) :
    clever_071_will_it_fly.is_palindrome_at q i j =
      clever_071_will_it_fly.is_palindrome_at q (i + 1) (j - 1) := by
  conv => lhs; unfold clever_071_will_it_fly.is_palindrome_at
  have h_size_lt : q.val.size < 2^64 := q.size_lt_usizeSize
  have h_cond_ge : decide (j ≤ i) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le]
    omega
  have h_idx_i : (q[i]_? : RustM i64) = RustM.ok (q.val[i.toNat]'hi) := by
    show (if h : i.toNat < q.val.size then pure (q.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (q.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_idx_j : (q[j]_? : RustM i64) = RustM.ok (q.val[j.toNat]'hj) := by
    show (if h : j.toNat < q.val.size then pure (q.val[j]) else .fail .arrayOutOfBounds)
        = RustM.ok (q.val[j.toNat]'hj)
    rw [dif_pos hj]; rfl
  have h_bne_false : (q.val[i.toNat]'hi != q.val[j.toNat]'hj) = false := by
    rw [bne_eq_false_iff_eq]; exact heq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by omega
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
  have h_j_pos : 1 ≤ j.toNat := by omega
  have h_no_bv_j :
      BitVec.usubOverflow j.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.usubOverflow j.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have h_sov : USize64.subOverflow j (1 : usize) = true := hbo
      have hh := USize64.subOverflow_iff.mp h_sov
      rw [usize_one_toNat] at hh
      omega
  simp only [rust_primitives.cmp.ge, pure_bind, h_cond_ge, Bool.false_eq_true, ↓reduceIte,
             RustM_ok_bind, h_idx_i, h_idx_j,
             rust_primitives.cmp.ne, h_bne_false,
             rust_primitives.ops.arith.Add.add, h_no_bv_i,
             rust_primitives.ops.arith.Sub.sub, h_no_bv_j]

/-! ## Iff and totality lemmas for `is_palindrome_at` -/

/-- Iff between `is_palindrome_at q i j = ok true` and "every pair `(k, i+j-k)`
    with `i ≤ k ≤ j` is equal".  Established under the invariant
    `i + j + 1 = size` (so `i + j < size`). -/
private theorem is_palindrome_at_iff_aux (q : RustSlice i64) :
    ∀ (m : Nat) (i j : usize),
      j.toNat - i.toNat ≤ m →
      i.toNat + j.toNat + 1 = q.val.size →
      (clever_071_will_it_fly.is_palindrome_at q i j = RustM.ok true ↔
       ∀ k : Nat, i.toNat ≤ k → k ≤ j.toNat →
         ∀ (hk : k < q.val.size) (hjk : i.toNat + j.toNat - k < q.val.size),
           q.val[k]'hk = q.val[i.toNat + j.toNat - k]'hjk) := by
  intro m
  induction m with
  | zero =>
    intro i j hm hinv
    have hij : j.toNat ≤ i.toNat := by omega
    refine ⟨fun _ k hki hkj hk hjk => ?_, fun _ => is_palindrome_at_oob q i j hij⟩
    -- i ≤ k ≤ j ≤ i so k = i = j; i + j - k = i
    exact getElem_idx_congr q k (i.toNat + j.toNat - k) hk hjk (by omega)
  | succ m ih =>
    intro i j hm hinv
    by_cases hij : j.toNat ≤ i.toNat
    · refine ⟨fun _ k hki hkj hk hjk => ?_, fun _ => is_palindrome_at_oob q i j hij⟩
      exact getElem_idx_congr q k (i.toNat + j.toNat - k) hk hjk (by omega)
    · have hij_lt : i.toNat < j.toNat := Nat.lt_of_not_le hij
      have hi_lt : i.toNat < q.val.size := by omega
      have hj_lt : j.toNat < q.val.size := by omega
      by_cases hcheck : q.val[i.toNat]'hi_lt = q.val[j.toNat]'hj_lt
      · -- Recurse to (i+1, j-1)
        have h_rec := is_palindrome_at_recurse q i j hi_lt hj_lt hij_lt hcheck
        have h_size_lt : q.val.size < 2^64 := q.size_lt_usizeSize
        have h_no_ov_i : i.toNat + 1 < 2^64 := by omega
        have h_j_pos : 1 ≤ j.toNat := by omega
        have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
        have h_j1 : (j - 1).toNat = j.toNat - 1 := usize_sub_one_toNat j h_j_pos
        have h_next_m : (j - 1).toNat - (i + 1).toNat ≤ m := by
          rw [h_i1, h_j1]; omega
        have h_next_inv : (i + 1).toNat + (j - 1).toNat + 1 = q.val.size := by
          rw [h_i1, h_j1]; omega
        have ih' := ih (i + 1) (j - 1) h_next_m h_next_inv
        rw [h_rec, ih']
        have h_next_ij : (i + 1).toNat + (j - 1).toNat = i.toNat + j.toNat := by
          rw [h_i1, h_j1]; omega
        constructor
        · intro hall k hki hkj hk hjk
          by_cases hk_at_i : k = i.toNat
          · apply (getElem_idx_congr q k i.toNat hk hi_lt hk_at_i).trans
            apply (Eq.trans hcheck)
            exact getElem_idx_congr q j.toNat (i.toNat + j.toNat - k) hj_lt hjk (by omega)
          · by_cases hk_at_j : k = j.toNat
            · apply (getElem_idx_congr q k j.toNat hk hj_lt hk_at_j).trans
              apply (Eq.trans hcheck.symm)
              exact getElem_idx_congr q i.toNat (i.toNat + j.toNat - k) hi_lt hjk (by omega)
            · have hki' : (i + 1).toNat ≤ k := by rw [h_i1]; omega
              have hkj' : k ≤ (j - 1).toNat := by rw [h_j1]; omega
              have hjk' : (i + 1).toNat + (j - 1).toNat - k < q.val.size := by
                rw [h_next_ij]; exact hjk
              have htarget := hall k hki' hkj' hk hjk'
              apply htarget.trans
              exact getElem_idx_congr q ((i + 1).toNat + (j - 1).toNat - k)
                                       (i.toNat + j.toNat - k) hjk' hjk (by omega)
        · intro hall k hki hkj hk hjk
          have hki' : i.toNat ≤ k := by rw [h_i1] at hki; omega
          have hkj' : k ≤ j.toNat := by rw [h_j1] at hkj; omega
          have hjk' : i.toNat + j.toNat - k < q.val.size := by
            rw [← h_next_ij]; exact hjk
          have htarget := hall k hki' hkj' hk hjk'
          apply htarget.trans
          exact getElem_idx_congr q (i.toNat + j.toNat - k)
                                   ((i + 1).toNat + (j - 1).toNat - k) hjk' hjk (by omega)
      · have h_false := is_palindrome_at_mismatch q i j hi_lt hj_lt hij_lt hcheck
        refine ⟨fun hT => ?_, fun hall => ?_⟩
        · rw [h_false] at hT
          exact absurd hT (by decide)
        · exfalso
          apply hcheck
          have hjk_lt : i.toNat + j.toNat - i.toNat < q.val.size := by
            have h_eq_sub : i.toNat + j.toNat - i.toNat = j.toNat := by omega
            rw [h_eq_sub]; exact hj_lt
          have hh := hall i.toNat (Nat.le_refl _) (Nat.le_of_lt hij_lt) hi_lt hjk_lt
          apply hh.trans
          exact getElem_idx_congr q (i.toNat + j.toNat - i.toNat) j.toNat hjk_lt hj_lt (by omega)

/-- Totality: `is_palindrome_at q i j` returns either `ok true` or `ok false`
    under the invariant `i + j + 1 = size`. -/
private theorem is_palindrome_at_total (q : RustSlice i64) :
    ∀ (m : Nat) (i j : usize),
      j.toNat - i.toNat ≤ m →
      i.toNat + j.toNat + 1 = q.val.size →
      clever_071_will_it_fly.is_palindrome_at q i j = RustM.ok true ∨
      clever_071_will_it_fly.is_palindrome_at q i j = RustM.ok false := by
  intro m
  induction m with
  | zero =>
    intro i j hm hinv
    have hij : j.toNat ≤ i.toNat := by omega
    left; exact is_palindrome_at_oob q i j hij
  | succ m ih =>
    intro i j hm hinv
    by_cases hij : j.toNat ≤ i.toNat
    · left; exact is_palindrome_at_oob q i j hij
    · have hij_lt : i.toNat < j.toNat := Nat.lt_of_not_le hij
      have hi_lt : i.toNat < q.val.size := by omega
      have hj_lt : j.toNat < q.val.size := by omega
      by_cases hcheck : q.val[i.toNat]'hi_lt = q.val[j.toNat]'hj_lt
      · have h_rec := is_palindrome_at_recurse q i j hi_lt hj_lt hij_lt hcheck
        have h_size_lt : q.val.size < 2^64 := q.size_lt_usizeSize
        have h_no_ov_i : i.toNat + 1 < 2^64 := by omega
        have h_j_pos : 1 ≤ j.toNat := by omega
        have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
        have h_j1 : (j - 1).toNat = j.toNat - 1 := usize_sub_one_toNat j h_j_pos
        have h_next_m : (j - 1).toNat - (i + 1).toNat ≤ m := by
          rw [h_i1, h_j1]; omega
        have h_next_inv : (i + 1).toNat + (j - 1).toNat + 1 = q.val.size := by
          rw [h_i1, h_j1]; omega
        rcases ih (i + 1) (j - 1) h_next_m h_next_inv with h_t | h_f
        · left; rw [h_rec]; exact h_t
        · right; rw [h_rec]; exact h_f
      · right
        exact is_palindrome_at_mismatch q i j hi_lt hj_lt hij_lt hcheck

/-! ## Top-level evaluators -/

/-- Helper to evaluate the `sum_at q 0 0` call. -/
private theorem sum_at_zero_zero (q : RustSlice i64)
    (hfit : ∀ k : Nat, k ≤ q.val.size →
              -(2^63 : Int) ≤ prefix_sum_int q k ∧ prefix_sum_int q k < 2^63) :
    ∃ s : i64,
      clever_071_will_it_fly.sum_at q (0 : usize) (0 : i64) = RustM.ok s ∧
      s.toInt = prefix_sum_int q q.val.size := by
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_inv : (0 : i64).toInt = prefix_sum_int q (0 : usize).toNat := by
    rw [h_zero_toNat, i64_zero_toInt]; rfl
  have h_m_le : q.val.size - (0 : usize).toNat ≤ q.val.size := by
    rw [h_zero_toNat]; omega
  have h_i_le : (0 : usize).toNat ≤ q.val.size := by
    rw [h_zero_toNat]; omega
  exact sum_at_correct q hfit q.val.size (0 : usize) (0 : i64) h_m_le h_i_le h_inv

/-- `is_empty q` evaluates to `ok true` when `q.val.size = 0`. -/
private theorem is_empty_eval_zero (q : RustSlice i64) (h : q.val.size = 0) :
    core_models.slice.Impl.is_empty i64 q = RustM.ok true := by
  unfold core_models.slice.Impl.is_empty core_models.slice.Impl.len
         rust_primitives.slice.slice_length
  show (pure (USize64.ofNat q.val.size) >>= fun n => (n ==? (0 : usize) : RustM Bool)) = _
  rw [pure_bind]
  show ((pure ((USize64.ofNat q.val.size) == (0 : usize))) : RustM Bool) = _
  have h_eq : (USize64.ofNat q.val.size : usize) = (0 : usize) := by
    apply USize64.toNat_inj.mp
    rw [USize64.toNat_ofNat_of_lt' q.size_lt_usizeSize, h]; rfl
  rw [h_eq]; rfl

/-- `is_empty q` evaluates to `ok false` when `q.val.size ≠ 0`. -/
private theorem is_empty_eval_nonzero (q : RustSlice i64) (h : q.val.size ≠ 0) :
    core_models.slice.Impl.is_empty i64 q = RustM.ok false := by
  unfold core_models.slice.Impl.is_empty core_models.slice.Impl.len
         rust_primitives.slice.slice_length
  show (pure (USize64.ofNat q.val.size) >>= fun n => (n ==? (0 : usize) : RustM Bool)) = _
  rw [pure_bind]
  show ((pure ((USize64.ofNat q.val.size) == (0 : usize))) : RustM Bool) = _
  have h_ne : (USize64.ofNat q.val.size : usize) ≠ (0 : usize) := by
    intro h_eq
    apply h
    have h_tn : (USize64.ofNat q.val.size).toNat = (0 : usize).toNat := by rw [h_eq]
    rw [USize64.toNat_ofNat_of_lt' q.size_lt_usizeSize] at h_tn
    show q.val.size = 0
    rw [h_tn]; rfl
  have h_beq : ((USize64.ofNat q.val.size) == (0 : usize)) = false := by
    rw [beq_eq_false_iff_ne]; exact h_ne
  rw [h_beq]; rfl

/-- `core_models.slice.Impl.len i64 q = RustM.ok (USize64.ofNat q.val.size)`. -/
private theorem len_pure_eval (q : RustSlice i64) :
    core_models.slice.Impl.len i64 q = RustM.ok (USize64.ofNat q.val.size) := by
  unfold core_models.slice.Impl.len rust_primitives.slice.slice_length; rfl

/-- Evaluate `(USize64.ofNat size) -? 1` to `ok (USize64.ofNat (size - 1))` when `size ≠ 0`. -/
private theorem ofNat_size_sub_one_eval (q : RustSlice i64) (hne : q.val.size ≠ 0) :
    ((USize64.ofNat q.val.size) -? (1 : usize) : RustM usize) =
      RustM.ok (USize64.ofNat (q.val.size - 1)) := by
  have h_size_pos : 1 ≤ q.val.size := Nat.one_le_iff_ne_zero.mpr hne
  have h_size_lt : q.val.size < 2^64 := q.size_lt_usizeSize
  have h_ofNat_toNat : (USize64.ofNat q.val.size).toNat = q.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_size_ge_one : 1 ≤ (USize64.ofNat q.val.size).toNat := by
    rw [h_ofNat_toNat]; exact h_size_pos
  have h_no_bv :
      BitVec.usubOverflow (USize64.ofNat q.val.size).toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.usubOverflow (USize64.ofNat q.val.size).toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have h_sov : USize64.subOverflow (USize64.ofNat q.val.size) (1 : usize) = true := hbo
      have hh := USize64.subOverflow_iff.mp h_sov
      rw [usize_one_toNat] at hh
      omega
  have h_sub :
      ((USize64.ofNat q.val.size) -? (1 : usize) : RustM usize) =
        RustM.ok ((USize64.ofNat q.val.size) - 1) := by
    show (rust_primitives.ops.arith.Sub.sub (USize64.ofNat q.val.size) (1 : usize)
          : RustM usize) = _
    show (if BitVec.usubOverflow (USize64.ofNat q.val.size).toBitVec (1 : usize).toBitVec
          then (.fail .integerOverflow : RustM usize)
          else pure ((USize64.ofNat q.val.size) - 1)) = _
    rw [h_no_bv]; rfl
  rw [h_sub]
  have h_sub_eq : (USize64.ofNat q.val.size) - 1 = USize64.ofNat (q.val.size - 1) := by
    apply USize64.toNat_inj.mp
    have h_one_le : (1 : usize).toNat ≤ (USize64.ofNat q.val.size).toNat := by
      rw [usize_one_toNat]; exact h_size_ge_one
    rw [USize64.toNat_sub_of_le' h_one_le, h_ofNat_toNat, usize_one_toNat,
        USize64.toNat_ofNat_of_lt' (by omega : q.val.size - 1 < 2^64)]
  rw [h_sub_eq]

/-- `is_palindrome q` implies the iff predicate at `(0, size-1)` for `size ≥ 1`. -/
private theorem is_palindrome_to_iff_pred (q : RustSlice i64) (hne : q.val.size ≠ 0)
    (hpal : is_palindrome q) :
    ∀ k : Nat, (0 : usize).toNat ≤ k →
      k ≤ (USize64.ofNat (q.val.size - 1)).toNat →
      ∀ (hk : k < q.val.size)
        (hjk : (0 : usize).toNat + (USize64.ofNat (q.val.size - 1)).toNat - k < q.val.size),
        q.val[k]'hk = q.val[(0 : usize).toNat + (USize64.ofNat (q.val.size - 1)).toNat - k]'hjk := by
  intro k _ hkj hk hjk
  have h_size_lt : q.val.size < 2^64 := q.size_lt_usizeSize
  have h_sml_lt : q.val.size - 1 < 2^64 := by omega
  have h_jt : (USize64.ofNat (q.val.size - 1)).toNat = q.val.size - 1 :=
    USize64.toNat_ofNat_of_lt' h_sml_lt
  have h_size_pos : 1 ≤ q.val.size := Nat.one_le_iff_ne_zero.mpr hne
  have h_zt : (0 : usize).toNat = 0 := usize_zero_toNat
  -- Pair: k + (size - 1 - k) + 1 = size
  rw [h_jt] at hkj
  have hpair : k + (q.val.size - 1 - k) + 1 = q.val.size := by omega
  have hjk' : q.val.size - 1 - k < q.val.size := by omega
  have h_idx_eq : (0 : usize).toNat + (USize64.ofNat (q.val.size - 1)).toNat - k =
                  q.val.size - 1 - k := by
    rw [h_zt, h_jt]; omega
  have hpalk := hpal k (q.val.size - 1 - k) hpair hk hjk'
  apply hpalk.trans
  exact getElem_idx_congr q (q.val.size - 1 - k)
                           ((0 : usize).toNat + (USize64.ofNat (q.val.size - 1)).toNat - k)
                           hjk' hjk h_idx_eq.symm

/-- Conversely, the iff predicate at `(0, size-1)` implies `is_palindrome q`. -/
private theorem iff_pred_to_is_palindrome (q : RustSlice i64) (hne : q.val.size ≠ 0)
    (hpred : ∀ k : Nat, (0 : usize).toNat ≤ k →
      k ≤ (USize64.ofNat (q.val.size - 1)).toNat →
      ∀ (hk : k < q.val.size)
        (hjk : (0 : usize).toNat + (USize64.ofNat (q.val.size - 1)).toNat - k < q.val.size),
        q.val[k]'hk = q.val[(0 : usize).toNat + (USize64.ofNat (q.val.size - 1)).toNat - k]'hjk) :
    is_palindrome q := by
  intro i j hsum hi hj
  have h_size_lt : q.val.size < 2^64 := q.size_lt_usizeSize
  have h_sml_lt : q.val.size - 1 < 2^64 := by omega
  have h_jt : (USize64.ofNat (q.val.size - 1)).toNat = q.val.size - 1 :=
    USize64.toNat_ofNat_of_lt' h_sml_lt
  have h_zt : (0 : usize).toNat = 0 := usize_zero_toNat
  have h_size_pos : 1 ≤ q.val.size := Nat.one_le_iff_ne_zero.mpr hne
  have hkj_bound : i ≤ (USize64.ofNat (q.val.size - 1)).toNat := by
    rw [h_jt]; omega
  have h_idx_eq : (0 : usize).toNat + (USize64.ofNat (q.val.size - 1)).toNat - i = j := by
    rw [h_zt, h_jt]; omega
  have hjk_lt : (0 : usize).toNat + (USize64.ofNat (q.val.size - 1)).toNat - i < q.val.size := by
    rw [h_idx_eq]; exact hj
  have hh := hpred i (Nat.zero_le _) hkj_bound hi hjk_lt
  apply hh.trans
  exact getElem_idx_congr q ((0 : usize).toNat + (USize64.ofNat (q.val.size - 1)).toNat - i)
                            j hjk_lt hj h_idx_eq

/-! ## Top-level contract clauses -/

theorem sum_exceeds_w_returns_false (q : RustSlice i64) (w : i64)
    (hfit : ∀ k : Nat, k ≤ q.val.size →
              -(2^63 : Int) ≤ prefix_sum_int q k ∧ prefix_sum_int q k < 2^63)
    (hexceeds : w.toInt < prefix_sum_int q q.val.size) :
    clever_071_will_it_fly.will_it_fly q w = RustM.ok false := by
  unfold clever_071_will_it_fly.will_it_fly
  obtain ⟨s, h_sum_eq, h_s_toInt⟩ := sum_at_zero_zero q hfit
  rw [h_sum_eq, RustM_ok_bind]
  have h_gt : s.toInt > w.toInt := by rw [h_s_toInt]; exact hexceeds
  have h_cond : decide (s > w) = true := by
    rw [decide_eq_true_iff]
    exact Int64.lt_iff_toInt_lt.mpr h_gt
  show (rust_primitives.cmp.gt s w >>= _ : RustM Bool) = _
  show (pure (decide (s > w)) >>= _ : RustM Bool) = _
  rw [h_cond]
  rfl

theorem nonpalindrome_returns_false (q : RustSlice i64) (w : i64)
    (hfit : ∀ k : Nat, k ≤ q.val.size →
              -(2^63 : Int) ≤ prefix_sum_int q k ∧ prefix_sum_int q k < 2^63)
    (hnp : ¬ is_palindrome q) :
    clever_071_will_it_fly.will_it_fly q w = RustM.ok false := by
  -- Size must be ≥ 2 (size 0 and 1 are palindromic).
  have hne : q.val.size ≠ 0 := by
    intro hzero
    apply hnp
    intro i j hsum _ _
    rw [hzero] at hsum
    omega
  have hsize_ne_one : q.val.size ≠ 1 := by
    intro hone
    apply hnp
    intro i j hsum hi hj
    rw [hone] at hsum hi hj
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0; subst hj0; rfl
  have hsize_ge_two : 2 ≤ q.val.size := by omega
  unfold clever_071_will_it_fly.will_it_fly
  obtain ⟨s, h_sum_eq, h_s_toInt⟩ := sum_at_zero_zero q hfit
  rw [h_sum_eq, RustM_ok_bind]
  by_cases h_gt : s.toInt > w.toInt
  · have h_cond : decide (s > w) = true := by
      rw [decide_eq_true_iff]
      exact Int64.lt_iff_toInt_lt.mpr h_gt
    show (rust_primitives.cmp.gt s w >>= _ : RustM Bool) = _
    show (pure (decide (s > w)) >>= _ : RustM Bool) = _
    rw [h_cond]; rfl
  · have h_cond : decide (s > w) = false := by
      rw [decide_eq_false_iff_not]
      intro h_gt'
      apply h_gt
      exact Int64.lt_iff_toInt_lt.mp h_gt'
    show (rust_primitives.cmp.gt s w >>= _ : RustM Bool) = _
    show (pure (decide (s > w)) >>= _ : RustM Bool) = _
    rw [h_cond]
    simp only [pure_bind, Bool.false_eq_true, ↓reduceIte]
    rw [is_empty_eval_nonzero q hne, RustM_ok_bind]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [len_pure_eval q, RustM_ok_bind, ofNat_size_sub_one_eval q hne, RustM_ok_bind]
    have h_size_lt : q.val.size < 2^64 := q.size_lt_usizeSize
    have h_sml_lt : q.val.size - 1 < 2^64 := by omega
    have h_jt : (USize64.ofNat (q.val.size - 1)).toNat = q.val.size - 1 :=
      USize64.toNat_ofNat_of_lt' h_sml_lt
    have h_zt : (0 : usize).toNat = 0 := usize_zero_toNat
    have h_inv : (0 : usize).toNat + (USize64.ofNat (q.val.size - 1)).toNat + 1 = q.val.size := by
      rw [h_zt, h_jt]; omega
    have h_m_le : (USize64.ofNat (q.val.size - 1)).toNat - (0 : usize).toNat ≤
                    (USize64.ofNat (q.val.size - 1)).toNat := by omega
    have h_iff := is_palindrome_at_iff_aux q (USize64.ofNat (q.val.size - 1)).toNat
                    (0 : usize) (USize64.ofNat (q.val.size - 1)) h_m_le h_inv
    have h_pred_false :
        ¬ ∀ k : Nat, (0 : usize).toNat ≤ k →
            k ≤ (USize64.ofNat (q.val.size - 1)).toNat →
            ∀ (hk : k < q.val.size)
              (hjk : (0 : usize).toNat + (USize64.ofNat (q.val.size - 1)).toNat - k < q.val.size),
              q.val[k]'hk = q.val[(0 : usize).toNat + (USize64.ofNat (q.val.size - 1)).toNat - k]'hjk := by
      intro hpred
      apply hnp
      exact iff_pred_to_is_palindrome q hne hpred
    have h_total := is_palindrome_at_total q (USize64.ofNat (q.val.size - 1)).toNat
                    (0 : usize) (USize64.ofNat (q.val.size - 1)) h_m_le h_inv
    rcases h_total with h_t | h_f
    · exfalso; apply h_pred_false; exact h_iff.mp h_t
    · exact h_f

theorem palindrome_with_room_returns_true (q : RustSlice i64) (w : i64)
    (hfit : ∀ k : Nat, k ≤ q.val.size →
              -(2^63 : Int) ≤ prefix_sum_int q k ∧ prefix_sum_int q k < 2^63)
    (hpal : is_palindrome q)
    (hsum_le : prefix_sum_int q q.val.size ≤ w.toInt) :
    clever_071_will_it_fly.will_it_fly q w = RustM.ok true := by
  unfold clever_071_will_it_fly.will_it_fly
  obtain ⟨s, h_sum_eq, h_s_toInt⟩ := sum_at_zero_zero q hfit
  rw [h_sum_eq, RustM_ok_bind]
  have h_le_int : s.toInt ≤ w.toInt := by rw [h_s_toInt]; exact hsum_le
  have h_cond : decide (s > w) = false := by
    rw [decide_eq_false_iff_not]
    intro h_gt
    have h_gt_int : s.toInt > w.toInt := Int64.lt_iff_toInt_lt.mp h_gt
    omega
  show (rust_primitives.cmp.gt s w >>= _ : RustM Bool) = _
  show (pure (decide (s > w)) >>= _ : RustM Bool) = _
  rw [h_cond]
  simp only [pure_bind, Bool.false_eq_true, ↓reduceIte]
  -- Now the is_empty branch
  by_cases hempty : q.val.size = 0
  · rw [is_empty_eval_zero q hempty, RustM_ok_bind]
    simp only [↓reduceIte]
    rfl
  · rw [is_empty_eval_nonzero q hempty, RustM_ok_bind]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [len_pure_eval q, RustM_ok_bind, ofNat_size_sub_one_eval q hempty, RustM_ok_bind]
    have h_size_lt : q.val.size < 2^64 := q.size_lt_usizeSize
    have h_sml_lt : q.val.size - 1 < 2^64 := by omega
    have h_jt : (USize64.ofNat (q.val.size - 1)).toNat = q.val.size - 1 :=
      USize64.toNat_ofNat_of_lt' h_sml_lt
    have h_zt : (0 : usize).toNat = 0 := usize_zero_toNat
    have h_inv : (0 : usize).toNat + (USize64.ofNat (q.val.size - 1)).toNat + 1 = q.val.size := by
      rw [h_zt, h_jt]; omega
    have h_m_le : (USize64.ofNat (q.val.size - 1)).toNat - (0 : usize).toNat ≤
                    (USize64.ofNat (q.val.size - 1)).toNat := by omega
    have h_iff := is_palindrome_at_iff_aux q (USize64.ofNat (q.val.size - 1)).toNat
                    (0 : usize) (USize64.ofNat (q.val.size - 1)) h_m_le h_inv
    exact h_iff.mpr (is_palindrome_to_iff_pred q hempty hpal)

end Clever_071_will_it_flyObligations
