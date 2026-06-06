-- Companion obligations file for the `clever_135_largest_smallest_integers` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_135_largest_smallest_integers

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000

namespace Clever_135_largest_smallest_integersObligations

/-! ## Standard helper lemmas (ported from clever_089_next_smallest_modified). -/

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

private theorem usize_add_one_eq (i : usize) (h : i.toNat + 1 < 2^64) :
    (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
  show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
  show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure (i + 1)) = _
  rw [usize_add_one_no_bv i h]; rfl

private theorem slice_index_eq (l : RustSlice i64) (i : usize)
    (hi : i.toNat < l.val.size) :
    (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi) := by
  show (if h : i.toNat < l.val.size then pure (l.val[i])
          else .fail .arrayOutOfBounds)
      = RustM.ok (l.val[i.toNat]'hi)
  rw [dif_pos hi]; rfl

private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide

/-! ## Step lemmas for `lneg_at`.

`lneg_at` tracks the largest negative integer.  Update happens when
`l[i] < 0` AND (`¬found ∨ l[i] > best`). -/

private theorem lneg_at_oob
    (l : RustSlice i64) (i : usize) (best : i64) (found : Bool)
    (hi : l.val.size ≤ i.toNat) :
    clever_135_largest_smallest_integers.lneg_at l i best found
      = RustM.ok (rust_primitives.hax.Tuple2.mk best found) := by
  conv => lhs; unfold clever_135_largest_smallest_integers.lneg_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = true := by
    rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, h_cond, ↓reduceIte]
  rfl

private theorem lneg_at_take
    (l : RustSlice i64) (i : usize) (best : i64) (found : Bool)
    (hi : i.toNat < l.val.size)
    (h_neg : (l.val[i.toNat]'hi).toInt < 0)
    (h_cond : ¬ found ∨ best.toInt < (l.val[i.toNat]'hi).toInt) :
    clever_135_largest_smallest_integers.lneg_at l i best found
      = clever_135_largest_smallest_integers.lneg_at l (i + 1) (l.val[i.toNat]'hi) true := by
  conv => lhs; unfold clever_135_largest_smallest_integers.lneg_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov : i.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]
    omega
  have h_idx := slice_index_eq l i hi
  have h_neg_dec : decide ((l.val[i.toNat]'hi) < (0 : i64)) = true := by
    rw [decide_eq_true_iff]
    apply Int64.lt_iff_toInt_lt.mpr
    rw [i64_zero_toInt]; exact h_neg
  have h_or_true : ((!found) || decide ((l.val[i.toNat]'hi) > best)) = true := by
    rcases h_cond with hnf | hlt
    · have h_false : found = false := by
        cases found
        · rfl
        · exact absurd rfl hnf
      rw [h_false]; rfl
    · have h_dec : decide ((l.val[i.toNat]'hi) > best) = true := by
        rw [decide_eq_true_iff]
        show best < (l.val[i.toNat]'hi)
        exact Int64.lt_iff_toInt_lt.mpr hlt
      rw [h_dec]; rw [Bool.or_true]
  have h_and_true :
      (decide ((l.val[i.toNat]'hi) < (0 : i64)) &&
        ((!found) || decide ((l.val[i.toNat]'hi) > best))) = true := by
    rw [h_neg_dec, h_or_true]; rfl
  have h_add_eq : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
    usize_add_one_eq i h_no_ov
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, rust_primitives.cmp.lt, rust_primitives.cmp.gt,
             rust_primitives.hax.logical_op.not, rust_primitives.hax.logical_op.or,
             rust_primitives.hax.logical_op.and,
             h_and_true, h_add_eq]

private theorem lneg_at_skip
    (l : RustSlice i64) (i : usize) (best : i64) (found : Bool)
    (hi : i.toNat < l.val.size)
    (h_cond : 0 ≤ (l.val[i.toNat]'hi).toInt ∨
              (found = true ∧ (l.val[i.toNat]'hi).toInt ≤ best.toInt)) :
    clever_135_largest_smallest_integers.lneg_at l i best found
      = clever_135_largest_smallest_integers.lneg_at l (i + 1) best found := by
  conv => lhs; unfold clever_135_largest_smallest_integers.lneg_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov : i.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]
    omega
  have h_idx := slice_index_eq l i hi
  have h_and_false :
      (decide ((l.val[i.toNat]'hi) < (0 : i64)) &&
        ((!found) || decide ((l.val[i.toNat]'hi) > best))) = false := by
    rcases h_cond with h_nonneg | ⟨hf_true, hle⟩
    · have h_neg_false : decide ((l.val[i.toNat]'hi) < (0 : i64)) = false := by
        rw [decide_eq_false_iff_not]
        intro h_lt
        have h_lt_int : (l.val[i.toNat]'hi).toInt < (0 : i64).toInt :=
          Int64.lt_iff_toInt_lt.mp h_lt
        rw [i64_zero_toInt] at h_lt_int; omega
      rw [h_neg_false]; rfl
    · have h_not_found : (!found) = false := by rw [hf_true]; rfl
      have h_not_gt : decide ((l.val[i.toNat]'hi) > best) = false := by
        rw [decide_eq_false_iff_not]
        intro h_gt
        have : best.toInt < (l.val[i.toNat]'hi).toInt := Int64.lt_iff_toInt_lt.mp h_gt
        omega
      have h_or_false :
          ((!found) || decide ((l.val[i.toNat]'hi) > best)) = false := by
        rw [h_not_found, h_not_gt]; rfl
      rw [h_or_false]; simp
  have h_add_eq : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
    usize_add_one_eq i h_no_ov
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, rust_primitives.cmp.lt, rust_primitives.cmp.gt,
             rust_primitives.hax.logical_op.not, rust_primitives.hax.logical_op.or,
             rust_primitives.hax.logical_op.and,
             h_and_false, h_add_eq]

/-! ## Step lemmas for `spos_at`.

`spos_at` tracks the smallest positive integer.  Update happens when
`l[i] > 0` AND (`¬found ∨ l[i] < best`). -/

private theorem spos_at_oob
    (l : RustSlice i64) (i : usize) (best : i64) (found : Bool)
    (hi : l.val.size ≤ i.toNat) :
    clever_135_largest_smallest_integers.spos_at l i best found
      = RustM.ok (rust_primitives.hax.Tuple2.mk best found) := by
  conv => lhs; unfold clever_135_largest_smallest_integers.spos_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = true := by
    rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, h_cond, ↓reduceIte]
  rfl

private theorem spos_at_take
    (l : RustSlice i64) (i : usize) (best : i64) (found : Bool)
    (hi : i.toNat < l.val.size)
    (h_pos : 0 < (l.val[i.toNat]'hi).toInt)
    (h_cond : ¬ found ∨ (l.val[i.toNat]'hi).toInt < best.toInt) :
    clever_135_largest_smallest_integers.spos_at l i best found
      = clever_135_largest_smallest_integers.spos_at l (i + 1) (l.val[i.toNat]'hi) true := by
  conv => lhs; unfold clever_135_largest_smallest_integers.spos_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov : i.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]
    omega
  have h_idx := slice_index_eq l i hi
  have h_pos_dec : decide ((l.val[i.toNat]'hi) > (0 : i64)) = true := by
    rw [decide_eq_true_iff]
    show (0 : i64) < (l.val[i.toNat]'hi)
    apply Int64.lt_iff_toInt_lt.mpr
    rw [i64_zero_toInt]; exact h_pos
  have h_or_true : ((!found) || decide ((l.val[i.toNat]'hi) < best)) = true := by
    rcases h_cond with hnf | hlt
    · have h_false : found = false := by
        cases found
        · rfl
        · exact absurd rfl hnf
      rw [h_false]; rfl
    · have h_dec : decide ((l.val[i.toNat]'hi) < best) = true := by
        rw [decide_eq_true_iff]
        exact Int64.lt_iff_toInt_lt.mpr hlt
      rw [h_dec]; rw [Bool.or_true]
  have h_and_true :
      (decide ((l.val[i.toNat]'hi) > (0 : i64)) &&
        ((!found) || decide ((l.val[i.toNat]'hi) < best))) = true := by
    rw [h_pos_dec, h_or_true]; rfl
  have h_add_eq : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
    usize_add_one_eq i h_no_ov
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, rust_primitives.cmp.lt, rust_primitives.cmp.gt,
             rust_primitives.hax.logical_op.not, rust_primitives.hax.logical_op.or,
             rust_primitives.hax.logical_op.and,
             h_and_true, h_add_eq]

private theorem spos_at_skip
    (l : RustSlice i64) (i : usize) (best : i64) (found : Bool)
    (hi : i.toNat < l.val.size)
    (h_cond : (l.val[i.toNat]'hi).toInt ≤ 0 ∨
              (found = true ∧ best.toInt ≤ (l.val[i.toNat]'hi).toInt)) :
    clever_135_largest_smallest_integers.spos_at l i best found
      = clever_135_largest_smallest_integers.spos_at l (i + 1) best found := by
  conv => lhs; unfold clever_135_largest_smallest_integers.spos_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov : i.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]
    omega
  have h_idx := slice_index_eq l i hi
  have h_and_false :
      (decide ((l.val[i.toNat]'hi) > (0 : i64)) &&
        ((!found) || decide ((l.val[i.toNat]'hi) < best))) = false := by
    rcases h_cond with h_nonpos | ⟨hf_true, hge⟩
    · have h_pos_false : decide ((l.val[i.toNat]'hi) > (0 : i64)) = false := by
        rw [decide_eq_false_iff_not]
        intro h_gt
        have h_gt_int : (0 : i64).toInt < (l.val[i.toNat]'hi).toInt :=
          Int64.lt_iff_toInt_lt.mp h_gt
        rw [i64_zero_toInt] at h_gt_int; omega
      rw [h_pos_false]; rfl
    · have h_not_found : (!found) = false := by rw [hf_true]; rfl
      have h_not_lt : decide ((l.val[i.toNat]'hi) < best) = false := by
        rw [decide_eq_false_iff_not]
        intro h_lt
        have : (l.val[i.toNat]'hi).toInt < best.toInt := Int64.lt_iff_toInt_lt.mp h_lt
        omega
      have h_or_false :
          ((!found) || decide ((l.val[i.toNat]'hi) < best)) = false := by
        rw [h_not_found, h_not_lt]; rfl
      rw [h_or_false]; simp
  have h_add_eq : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
    usize_add_one_eq i h_no_ov
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, rust_primitives.cmp.lt, rust_primitives.cmp.gt,
             rust_primitives.hax.logical_op.not, rust_primitives.hax.logical_op.or,
             rust_primitives.hax.logical_op.and,
             h_and_false, h_add_eq]

/-! ## Master correctness lemma for `lneg_at`. -/

private theorem lneg_at_correct (l : RustSlice i64) :
    ∀ (m : Nat) (i : usize) (best : i64) (found : Bool),
      l.val.size - i.toNat ≤ m →
      i.toNat ≤ l.val.size →
      ∃ (rv : i64) (rf : Bool),
        clever_135_largest_smallest_integers.lneg_at l i best found
          = RustM.ok (rust_primitives.hax.Tuple2.mk rv rf) ∧
        (rf = true ↔ found = true ∨ ∃ (j : Nat) (hj : j < l.val.size),
                                       i.toNat ≤ j ∧ (l.val[j]'hj).toInt < 0) ∧
        (rf = true →
          (found = true ∧ rv = best) ∨
          ∃ (j : Nat) (hj : j < l.val.size),
            i.toNat ≤ j ∧ rv = (l.val[j]'hj) ∧ (l.val[j]'hj).toInt < 0) ∧
        (rf = true →
          (found = true → best.toInt ≤ rv.toInt) ∧
          ∀ (j : Nat) (hj : j < l.val.size),
            i.toNat ≤ j → (l.val[j]'hj).toInt < 0 →
            (l.val[j]'hj).toInt ≤ rv.toInt) := by
  intro m
  induction m with
  | zero =>
    intro i best found hm hi_le
    have hi_eq : i.toNat = l.val.size := by omega
    have hi_ge : l.val.size ≤ i.toNat := by omega
    refine ⟨best, found, lneg_at_oob l i best found hi_ge, ?_, ?_, ?_⟩
    · constructor
      · intro hf; left; exact hf
      · rintro (hf | ⟨j, hj, h_jge, _⟩)
        · exact hf
        · rw [hi_eq] at h_jge; omega
    · intro hrf; left; exact ⟨hrf, rfl⟩
    · intro hrf
      refine ⟨fun _ => Int.le_refl _, ?_⟩
      intro j hj h_jge _
      rw [hi_eq] at h_jge; omega
  | succ m ih =>
    intro i best found hm hi_le
    by_cases hi_ge : l.val.size ≤ i.toNat
    · have hi_eq : i.toNat = l.val.size := by omega
      refine ⟨best, found, lneg_at_oob l i best found hi_ge, ?_, ?_, ?_⟩
      · constructor
        · intro hf; left; exact hf
        · rintro (hf | ⟨j, hj, h_jge, _⟩)
          · exact hf
          · rw [hi_eq] at h_jge; omega
      · intro hrf; left; exact ⟨hrf, rfl⟩
      · intro hrf
        refine ⟨fun _ => Int.le_refl _, ?_⟩
        intro j hj h_jge _
        rw [hi_eq] at h_jge; omega
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov : i.toNat + 1 < 2 ^ 64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_m_le : l.val.size - (i + 1).toNat ≤ m := by rw [h_i1]; omega
      by_cases h_take :
          (l.val[i.toNat]'hi_lt).toInt < 0 ∧
          (¬ found = true ∨ best.toInt < (l.val[i.toNat]'hi_lt).toInt)
      · -- TAKE branch
        obtain ⟨h_neg_i, h_cond_raw⟩ := h_take
        have h_cond_simpl : ¬ found ∨ best.toInt < (l.val[i.toNat]'hi_lt).toInt := by
          rcases h_cond_raw with hnf | hlt
          · left; intro hf; apply hnf; cases found
            · cases hf
            · rfl
          · right; exact hlt
        have h_step := lneg_at_take l i best found hi_lt h_neg_i h_cond_simpl
        obtain ⟨rv, rf, hres, h_live, h_mem, h_min⟩ :=
          ih (i + 1) (l.val[i.toNat]'hi_lt) true h_m_le h_i1_le
        refine ⟨rv, rf, ?_, ?_, ?_, ?_⟩
        · rw [h_step]; exact hres
        · -- liveness
          constructor
          · intro hrf
            right
            exact ⟨i.toNat, hi_lt, Nat.le_refl _, h_neg_i⟩
          · intro _
            apply h_live.mpr; left; rfl
        · -- membership
          intro hrf
          rcases h_mem hrf with ⟨hf_true, hrv_eq⟩ | ⟨j, hj, h_jge, h_rv_eq, h_jneg⟩
          · right
            refine ⟨i.toNat, hi_lt, Nat.le_refl _, ?_, h_neg_i⟩
            exact hrv_eq
          · right
            refine ⟨j, hj, ?_, h_rv_eq, h_jneg⟩
            rw [h_i1] at h_jge; omega
        · -- maximality
          intro hrf
          obtain ⟨h_max_best, h_max_suffix⟩ := h_min hrf
          have h_li_le_rv : (l.val[i.toNat]'hi_lt).toInt ≤ rv.toInt := h_max_best rfl
          refine ⟨?_, ?_⟩
          · intro hf
            rcases h_cond_raw with hnf | hlt
            · exact absurd hf hnf
            · omega
          · intro j hj h_jge h_jneg
            by_cases h_jeq : j = i.toNat
            · subst h_jeq; exact h_li_le_rv
            · have h_jge1 : (i + 1).toNat ≤ j := by rw [h_i1]; omega
              exact h_max_suffix j hj h_jge1 h_jneg
      · -- SKIP branch
        have h_skip_cond :
            0 ≤ (l.val[i.toNat]'hi_lt).toInt ∨
            (found = true ∧ (l.val[i.toNat]'hi_lt).toInt ≤ best.toInt) := by
          by_cases h_neg_i : (l.val[i.toNat]'hi_lt).toInt < 0
          · right
            have h_neg : ¬ (¬ found = true ∨ best.toInt < (l.val[i.toNat]'hi_lt).toInt) := by
              intro h; exact h_take ⟨h_neg_i, h⟩
            have h_nf : ¬ ¬ found = true := fun hnf => h_neg (Or.inl hnf)
            have h_nlt : ¬ best.toInt < (l.val[i.toNat]'hi_lt).toInt :=
              fun hlt => h_neg (Or.inr hlt)
            have hf : found = true := by
              cases found with
              | false => exact absurd (fun h => Bool.noConfusion h) h_nf
              | true => rfl
            exact ⟨hf, by omega⟩
          · left; omega
        have h_step := lneg_at_skip l i best found hi_lt h_skip_cond
        obtain ⟨rv, rf, hres, h_live, h_mem, h_min⟩ :=
          ih (i + 1) best found h_m_le h_i1_le
        refine ⟨rv, rf, ?_, ?_, ?_, ?_⟩
        · rw [h_step]; exact hres
        · -- liveness
          constructor
          · intro hrf
            rcases h_live.mp hrf with hf | ⟨j, hj, h_jge, h_jneg⟩
            · left; exact hf
            · right; refine ⟨j, hj, ?_, h_jneg⟩
              rw [h_i1] at h_jge; omega
          · rintro (hf | ⟨j, hj, h_jge, h_jneg⟩)
            · apply h_live.mpr; left; exact hf
            · apply h_live.mpr
              by_cases h_jeq : j = i.toNat
              · subst h_jeq
                rcases h_skip_cond with h_nonneg | ⟨hf, _⟩
                · exfalso; omega
                · left; exact hf
              · right
                refine ⟨j, hj, ?_, h_jneg⟩
                rw [h_i1]; omega
        · -- membership
          intro hrf
          rcases h_mem hrf with ⟨hf, hrv_eq⟩ | ⟨j, hj, h_jge, h_rv_eq, h_jneg⟩
          · left; exact ⟨hf, hrv_eq⟩
          · right
            refine ⟨j, hj, ?_, h_rv_eq, h_jneg⟩
            rw [h_i1] at h_jge; omega
        · -- maximality
          intro hrf
          obtain ⟨h_max_best, h_max_suffix⟩ := h_min hrf
          refine ⟨h_max_best, ?_⟩
          intro j hj h_jge h_jneg
          by_cases h_jeq : j = i.toNat
          · subst h_jeq
            rcases h_skip_cond with h_nonneg | ⟨hf, h_le⟩
            · exfalso; omega
            · have h_best_le_rv : best.toInt ≤ rv.toInt := h_max_best hf
              omega
          · have h_jge1 : (i + 1).toNat ≤ j := by rw [h_i1]; omega
            exact h_max_suffix j hj h_jge1 h_jneg

/-! ## Master correctness lemma for `spos_at`. -/

private theorem spos_at_correct (l : RustSlice i64) :
    ∀ (m : Nat) (i : usize) (best : i64) (found : Bool),
      l.val.size - i.toNat ≤ m →
      i.toNat ≤ l.val.size →
      ∃ (rv : i64) (rf : Bool),
        clever_135_largest_smallest_integers.spos_at l i best found
          = RustM.ok (rust_primitives.hax.Tuple2.mk rv rf) ∧
        (rf = true ↔ found = true ∨ ∃ (j : Nat) (hj : j < l.val.size),
                                       i.toNat ≤ j ∧ 0 < (l.val[j]'hj).toInt) ∧
        (rf = true →
          (found = true ∧ rv = best) ∨
          ∃ (j : Nat) (hj : j < l.val.size),
            i.toNat ≤ j ∧ rv = (l.val[j]'hj) ∧ 0 < (l.val[j]'hj).toInt) ∧
        (rf = true →
          (found = true → rv.toInt ≤ best.toInt) ∧
          ∀ (j : Nat) (hj : j < l.val.size),
            i.toNat ≤ j → 0 < (l.val[j]'hj).toInt →
            rv.toInt ≤ (l.val[j]'hj).toInt) := by
  intro m
  induction m with
  | zero =>
    intro i best found hm hi_le
    have hi_eq : i.toNat = l.val.size := by omega
    have hi_ge : l.val.size ≤ i.toNat := by omega
    refine ⟨best, found, spos_at_oob l i best found hi_ge, ?_, ?_, ?_⟩
    · constructor
      · intro hf; left; exact hf
      · rintro (hf | ⟨j, hj, h_jge, _⟩)
        · exact hf
        · rw [hi_eq] at h_jge; omega
    · intro hrf; left; exact ⟨hrf, rfl⟩
    · intro hrf
      refine ⟨fun _ => Int.le_refl _, ?_⟩
      intro j hj h_jge _
      rw [hi_eq] at h_jge; omega
  | succ m ih =>
    intro i best found hm hi_le
    by_cases hi_ge : l.val.size ≤ i.toNat
    · have hi_eq : i.toNat = l.val.size := by omega
      refine ⟨best, found, spos_at_oob l i best found hi_ge, ?_, ?_, ?_⟩
      · constructor
        · intro hf; left; exact hf
        · rintro (hf | ⟨j, hj, h_jge, _⟩)
          · exact hf
          · rw [hi_eq] at h_jge; omega
      · intro hrf; left; exact ⟨hrf, rfl⟩
      · intro hrf
        refine ⟨fun _ => Int.le_refl _, ?_⟩
        intro j hj h_jge _
        rw [hi_eq] at h_jge; omega
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov : i.toNat + 1 < 2 ^ 64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_m_le : l.val.size - (i + 1).toNat ≤ m := by rw [h_i1]; omega
      by_cases h_take :
          0 < (l.val[i.toNat]'hi_lt).toInt ∧
          (¬ found = true ∨ (l.val[i.toNat]'hi_lt).toInt < best.toInt)
      · -- TAKE branch
        obtain ⟨h_pos_i, h_cond_raw⟩ := h_take
        have h_cond_simpl : ¬ found ∨ (l.val[i.toNat]'hi_lt).toInt < best.toInt := by
          rcases h_cond_raw with hnf | hlt
          · left; intro hf; apply hnf; cases found
            · cases hf
            · rfl
          · right; exact hlt
        have h_step := spos_at_take l i best found hi_lt h_pos_i h_cond_simpl
        obtain ⟨rv, rf, hres, h_live, h_mem, h_min⟩ :=
          ih (i + 1) (l.val[i.toNat]'hi_lt) true h_m_le h_i1_le
        refine ⟨rv, rf, ?_, ?_, ?_, ?_⟩
        · rw [h_step]; exact hres
        · constructor
          · intro hrf
            right
            exact ⟨i.toNat, hi_lt, Nat.le_refl _, h_pos_i⟩
          · intro _
            apply h_live.mpr; left; rfl
        · intro hrf
          rcases h_mem hrf with ⟨hf_true, hrv_eq⟩ | ⟨j, hj, h_jge, h_rv_eq, h_jpos⟩
          · right
            refine ⟨i.toNat, hi_lt, Nat.le_refl _, ?_, h_pos_i⟩
            exact hrv_eq
          · right
            refine ⟨j, hj, ?_, h_rv_eq, h_jpos⟩
            rw [h_i1] at h_jge; omega
        · intro hrf
          obtain ⟨h_min_best, h_min_suffix⟩ := h_min hrf
          have h_rv_le_li : rv.toInt ≤ (l.val[i.toNat]'hi_lt).toInt := h_min_best rfl
          refine ⟨?_, ?_⟩
          · intro hf
            rcases h_cond_raw with hnf | hlt
            · exact absurd hf hnf
            · omega
          · intro j hj h_jge h_jpos
            by_cases h_jeq : j = i.toNat
            · subst h_jeq; exact h_rv_le_li
            · have h_jge1 : (i + 1).toNat ≤ j := by rw [h_i1]; omega
              exact h_min_suffix j hj h_jge1 h_jpos
      · -- SKIP branch
        have h_skip_cond :
            (l.val[i.toNat]'hi_lt).toInt ≤ 0 ∨
            (found = true ∧ best.toInt ≤ (l.val[i.toNat]'hi_lt).toInt) := by
          by_cases h_pos_i : 0 < (l.val[i.toNat]'hi_lt).toInt
          · right
            have h_neg : ¬ (¬ found = true ∨ (l.val[i.toNat]'hi_lt).toInt < best.toInt) := by
              intro h; exact h_take ⟨h_pos_i, h⟩
            have h_nf : ¬ ¬ found = true := fun hnf => h_neg (Or.inl hnf)
            have h_nlt : ¬ (l.val[i.toNat]'hi_lt).toInt < best.toInt :=
              fun hlt => h_neg (Or.inr hlt)
            have hf : found = true := by
              cases found with
              | false => exact absurd (fun h => Bool.noConfusion h) h_nf
              | true => rfl
            exact ⟨hf, by omega⟩
          · left; omega
        have h_step := spos_at_skip l i best found hi_lt h_skip_cond
        obtain ⟨rv, rf, hres, h_live, h_mem, h_min⟩ :=
          ih (i + 1) best found h_m_le h_i1_le
        refine ⟨rv, rf, ?_, ?_, ?_, ?_⟩
        · rw [h_step]; exact hres
        · constructor
          · intro hrf
            rcases h_live.mp hrf with hf | ⟨j, hj, h_jge, h_jpos⟩
            · left; exact hf
            · right; refine ⟨j, hj, ?_, h_jpos⟩
              rw [h_i1] at h_jge; omega
          · rintro (hf | ⟨j, hj, h_jge, h_jpos⟩)
            · apply h_live.mpr; left; exact hf
            · apply h_live.mpr
              by_cases h_jeq : j = i.toNat
              · subst h_jeq
                rcases h_skip_cond with h_nonpos | ⟨hf, _⟩
                · exfalso; omega
                · left; exact hf
              · right
                refine ⟨j, hj, ?_, h_jpos⟩
                rw [h_i1]; omega
        · intro hrf
          rcases h_mem hrf with ⟨hf, hrv_eq⟩ | ⟨j, hj, h_jge, h_rv_eq, h_jpos⟩
          · left; exact ⟨hf, hrv_eq⟩
          · right
            refine ⟨j, hj, ?_, h_rv_eq, h_jpos⟩
            rw [h_i1] at h_jge; omega
        · intro hrf
          obtain ⟨h_min_best, h_min_suffix⟩ := h_min hrf
          refine ⟨h_min_best, ?_⟩
          intro j hj h_jge h_jpos
          by_cases h_jeq : j = i.toNat
          · subst h_jeq
            rcases h_skip_cond with h_nonpos | ⟨hf, h_le⟩
            · exfalso; omega
            · have h_rv_le_best : rv.toInt ≤ best.toInt := h_min_best hf
              omega
          · have h_jge1 : (i + 1).toNat ≤ j := by rw [h_i1]; omega
            exact h_min_suffix j hj h_jge1 h_jpos

/-! ## RustM.ok-of-Tuple2 injection helper. -/

/-- RustM.ok is `some ∘ Except.ok`, so injection through both layers gives
    component-wise equality of the inner Tuple2. -/
private theorem rustM_ok_tuple2_inj {α β : Type}
    (a₁ a₂ : α) (b₁ b₂ : β)
    (h : (RustM.ok (rust_primitives.hax.Tuple2.mk a₁ b₁) : RustM (rust_primitives.hax.Tuple2 α β))
       = RustM.ok (rust_primitives.hax.Tuple2.mk a₂ b₂)) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have h_opt : (some (Except.ok (rust_primitives.hax.Tuple2.mk a₁ b₁))
                    : Option (Except Error (rust_primitives.hax.Tuple2 α β)))
              = some (Except.ok (rust_primitives.hax.Tuple2.mk a₂ b₂)) := h
  have h_exc : (Except.ok (rust_primitives.hax.Tuple2.mk a₁ b₁) : Except Error _)
             = Except.ok (rust_primitives.hax.Tuple2.mk a₂ b₂) :=
    Option.some.inj h_opt
  have h_tup : rust_primitives.hax.Tuple2.mk a₁ b₁ = rust_primitives.hax.Tuple2.mk a₂ b₂ := by
    injection h_exc
  exact ⟨congrArg rust_primitives.hax.Tuple2._0 h_tup,
         congrArg rust_primitives.hax.Tuple2._1 h_tup⟩

/-! ## Wrapper master.

Gathers the form of `largest_smallest_integers lst` together with the
liveness / membership / extremum clauses of both helpers, so each
obligation can be discharged by projecting from this lemma. -/

private theorem wrapper_master (lst : RustSlice i64) :
    ∃ (av : i64) (af : Bool) (bv : i64) (bf : Bool),
      clever_135_largest_smallest_integers.largest_smallest_integers lst
        = RustM.ok (rust_primitives.hax.Tuple2.mk
                      (if af then core_models.option.Option.Some av
                       else core_models.option.Option.None)
                      (if bf then core_models.option.Option.Some bv
                       else core_models.option.Option.None)) ∧
      -- lneg clauses (relative to initial state best=0, found=false; suffix = [0, size))
      (af = true ↔ ∃ (j : Nat) (hj : j < lst.val.size), (lst.val[j]'hj).toInt < 0) ∧
      (af = true →
         ∃ (j : Nat) (hj : j < lst.val.size),
           av = (lst.val[j]'hj) ∧ (lst.val[j]'hj).toInt < 0) ∧
      (af = true →
         ∀ (j : Nat) (hj : j < lst.val.size),
           (lst.val[j]'hj).toInt < 0 → (lst.val[j]'hj).toInt ≤ av.toInt) ∧
      -- spos clauses
      (bf = true ↔ ∃ (j : Nat) (hj : j < lst.val.size), 0 < (lst.val[j]'hj).toInt) ∧
      (bf = true →
         ∃ (j : Nat) (hj : j < lst.val.size),
           bv = (lst.val[j]'hj) ∧ 0 < (lst.val[j]'hj).toInt) ∧
      (bf = true →
         ∀ (j : Nat) (hj : j < lst.val.size),
           0 < (lst.val[j]'hj).toInt → bv.toInt ≤ (lst.val[j]'hj).toInt) := by
  obtain ⟨av, af, h_lneg, h_lneg_live, h_lneg_mem, h_lneg_max⟩ :=
    lneg_at_correct lst lst.val.size (0 : usize) (0 : i64) false
      (by show lst.val.size - (0 : usize).toNat ≤ lst.val.size
          rw [usize_zero_toNat]; omega)
      (by show (0 : usize).toNat ≤ lst.val.size; rw [usize_zero_toNat]; omega)
  obtain ⟨bv, bf, h_spos, h_spos_live, h_spos_mem, h_spos_min⟩ :=
    spos_at_correct lst lst.val.size (0 : usize) (0 : i64) false
      (by show lst.val.size - (0 : usize).toNat ≤ lst.val.size
          rw [usize_zero_toNat]; omega)
      (by show (0 : usize).toNat ≤ lst.val.size; rw [usize_zero_toNat]; omega)
  refine ⟨av, af, bv, bf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The wrapper equation.
    unfold clever_135_largest_smallest_integers.largest_smallest_integers
    rw [h_lneg]
    simp only [RustM_ok_bind]
    rw [h_spos]
    simp only [RustM_ok_bind]
    -- Now split on af and bf to reduce the two ifs.
    cases af <;> cases bf <;> simp <;> rfl
  · -- af liveness
    rw [h_lneg_live]
    constructor
    · rintro (hf | ⟨j, hj, _, h_jneg⟩)
      · cases hf
      · exact ⟨j, hj, h_jneg⟩
    · rintro ⟨j, hj, h_jneg⟩
      right; refine ⟨j, hj, ?_, h_jneg⟩
      rw [usize_zero_toNat]; omega
  · -- af membership
    intro haf
    rcases h_lneg_mem haf with ⟨hf, _⟩ | ⟨j, hj, _, h_av_eq, h_jneg⟩
    · cases hf
    · exact ⟨j, hj, h_av_eq, h_jneg⟩
  · -- af maximality
    intro haf j hj h_jneg
    have := (h_lneg_max haf).2 j hj (by rw [usize_zero_toNat]; omega) h_jneg
    exact this
  · -- bf liveness
    rw [h_spos_live]
    constructor
    · rintro (hf | ⟨j, hj, _, h_jpos⟩)
      · cases hf
      · exact ⟨j, hj, h_jpos⟩
    · rintro ⟨j, hj, h_jpos⟩
      right; refine ⟨j, hj, ?_, h_jpos⟩
      rw [usize_zero_toNat]; omega
  · -- bf membership
    intro hbf
    rcases h_spos_mem hbf with ⟨hf, _⟩ | ⟨j, hj, _, h_bv_eq, h_jpos⟩
    · cases hf
    · exact ⟨j, hj, h_bv_eq, h_jpos⟩
  · -- bf minimality
    intro hbf j hj h_jpos
    have := (h_spos_min hbf).2 j hj (by rw [usize_zero_toNat]; omega) h_jpos
    exact this

/-! ## Theorem placeholders (filled in below). -/

/-- Liveness: the first component is `Some` exactly when `lst` contains a
    negative element. -/
theorem first_some_iff_has_negative
    (lst : RustSlice i64)
    (a b : core_models.option.Option i64)
    (hres : clever_135_largest_smallest_integers.largest_smallest_integers lst
              = RustM.ok (rust_primitives.hax.Tuple2.mk a b)) :
    (∃ x : i64, a = core_models.option.Option.Some x) ↔
    (∃ (i : Nat) (hi : i < lst.val.size), (lst.val[i]'hi).toInt < 0) := by
  obtain ⟨av, af, bv, bf, h_wrap, h_af_iff, _, _, _, _, _⟩ := wrapper_master lst
  rw [h_wrap] at hres
  obtain ⟨h_a, h_b⟩ := rustM_ok_tuple2_inj _ _ _ _ hres
  -- h_a : (if af then Some av else None) = a
  rw [← h_a, ← h_af_iff]
  constructor
  · rintro ⟨x, hx⟩
    cases af with
    | true => rfl
    | false => simp at hx
  · intro h_af
    rw [h_af]; exact ⟨av, rfl⟩

theorem first_some_value_is_negative
    (lst : RustSlice i64) (x : i64) (b : core_models.option.Option i64)
    (hres : clever_135_largest_smallest_integers.largest_smallest_integers lst
              = RustM.ok (rust_primitives.hax.Tuple2.mk
                            (core_models.option.Option.Some x) b)) :
    x.toInt < 0 := by
  obtain ⟨av, af, bv, bf, h_wrap, _, h_af_mem, _, _, _, _⟩ := wrapper_master lst
  rw [h_wrap] at hres
  obtain ⟨h_a, h_b⟩ := rustM_ok_tuple2_inj _ _ _ _ hres
  -- h_a : (if af then Some av else None) = Some x
  have h_af_true : af = true := by
    cases af with
    | true => rfl
    | false => simp at h_a
  have h_av_eq_x : av = x := by
    rw [h_af_true] at h_a
    simp at h_a
    exact h_a
  obtain ⟨j, hj, h_av_jeq, h_jneg⟩ := h_af_mem h_af_true
  rw [← h_av_eq_x, h_av_jeq]
  exact h_jneg

theorem first_some_value_in_list
    (lst : RustSlice i64) (x : i64) (b : core_models.option.Option i64)
    (hres : clever_135_largest_smallest_integers.largest_smallest_integers lst
              = RustM.ok (rust_primitives.hax.Tuple2.mk
                            (core_models.option.Option.Some x) b)) :
    ∃ (i : Nat) (hi : i < lst.val.size), (lst.val[i]'hi) = x := by
  obtain ⟨av, af, bv, bf, h_wrap, _, h_af_mem, _, _, _, _⟩ := wrapper_master lst
  rw [h_wrap] at hres
  obtain ⟨h_a, h_b⟩ := rustM_ok_tuple2_inj _ _ _ _ hres
  have h_af_true : af = true := by
    cases af with
    | true => rfl
    | false => simp at h_a
  have h_av_eq_x : av = x := by
    rw [h_af_true] at h_a
    simp at h_a
    exact h_a
  obtain ⟨j, hj, h_av_jeq, _⟩ := h_af_mem h_af_true
  refine ⟨j, hj, ?_⟩
  rw [← h_av_eq_x, h_av_jeq]

theorem first_some_value_is_largest_negative
    (lst : RustSlice i64) (x : i64) (b : core_models.option.Option i64)
    (hres : clever_135_largest_smallest_integers.largest_smallest_integers lst
              = RustM.ok (rust_primitives.hax.Tuple2.mk
                            (core_models.option.Option.Some x) b)) :
    ∀ (i : Nat) (hi : i < lst.val.size),
      (lst.val[i]'hi).toInt < 0 → (lst.val[i]'hi).toInt ≤ x.toInt := by
  obtain ⟨av, af, bv, bf, h_wrap, _, _, h_af_max, _, _, _⟩ := wrapper_master lst
  rw [h_wrap] at hres
  obtain ⟨h_a, h_b⟩ := rustM_ok_tuple2_inj _ _ _ _ hres
  have h_af_true : af = true := by
    cases af with
    | true => rfl
    | false => simp at h_a
  have h_av_eq_x : av = x := by
    rw [h_af_true] at h_a
    simp at h_a
    exact h_a
  intro i hi h_ineg
  have := h_af_max h_af_true i hi h_ineg
  rw [← h_av_eq_x]; exact this

theorem second_some_iff_has_positive
    (lst : RustSlice i64)
    (a b : core_models.option.Option i64)
    (hres : clever_135_largest_smallest_integers.largest_smallest_integers lst
              = RustM.ok (rust_primitives.hax.Tuple2.mk a b)) :
    (∃ y : i64, b = core_models.option.Option.Some y) ↔
    (∃ (i : Nat) (hi : i < lst.val.size), 0 < (lst.val[i]'hi).toInt) := by
  obtain ⟨av, af, bv, bf, h_wrap, _, _, _, h_bf_iff, _, _⟩ := wrapper_master lst
  rw [h_wrap] at hres
  obtain ⟨h_a, h_b⟩ := rustM_ok_tuple2_inj _ _ _ _ hres
  rw [← h_b, ← h_bf_iff]
  constructor
  · rintro ⟨y, hy⟩
    cases bf with
    | true => rfl
    | false => simp at hy
  · intro h_bf
    rw [h_bf]; exact ⟨bv, rfl⟩

theorem second_some_value_is_positive
    (lst : RustSlice i64) (a : core_models.option.Option i64) (y : i64)
    (hres : clever_135_largest_smallest_integers.largest_smallest_integers lst
              = RustM.ok (rust_primitives.hax.Tuple2.mk a
                            (core_models.option.Option.Some y))) :
    0 < y.toInt := by
  obtain ⟨av, af, bv, bf, h_wrap, _, _, _, _, h_bf_mem, _⟩ := wrapper_master lst
  rw [h_wrap] at hres
  obtain ⟨h_a, h_b⟩ := rustM_ok_tuple2_inj _ _ _ _ hres
  have h_bf_true : bf = true := by
    cases bf with
    | true => rfl
    | false => simp at h_b
  have h_bv_eq_y : bv = y := by
    rw [h_bf_true] at h_b
    simp at h_b
    exact h_b
  obtain ⟨j, hj, h_bv_jeq, h_jpos⟩ := h_bf_mem h_bf_true
  rw [← h_bv_eq_y, h_bv_jeq]
  exact h_jpos

theorem second_some_value_in_list
    (lst : RustSlice i64) (a : core_models.option.Option i64) (y : i64)
    (hres : clever_135_largest_smallest_integers.largest_smallest_integers lst
              = RustM.ok (rust_primitives.hax.Tuple2.mk a
                            (core_models.option.Option.Some y))) :
    ∃ (i : Nat) (hi : i < lst.val.size), (lst.val[i]'hi) = y := by
  obtain ⟨av, af, bv, bf, h_wrap, _, _, _, _, h_bf_mem, _⟩ := wrapper_master lst
  rw [h_wrap] at hres
  obtain ⟨h_a, h_b⟩ := rustM_ok_tuple2_inj _ _ _ _ hres
  have h_bf_true : bf = true := by
    cases bf with
    | true => rfl
    | false => simp at h_b
  have h_bv_eq_y : bv = y := by
    rw [h_bf_true] at h_b
    simp at h_b
    exact h_b
  obtain ⟨j, hj, h_bv_jeq, _⟩ := h_bf_mem h_bf_true
  refine ⟨j, hj, ?_⟩
  rw [← h_bv_eq_y, h_bv_jeq]

theorem second_some_value_is_smallest_positive
    (lst : RustSlice i64) (a : core_models.option.Option i64) (y : i64)
    (hres : clever_135_largest_smallest_integers.largest_smallest_integers lst
              = RustM.ok (rust_primitives.hax.Tuple2.mk a
                            (core_models.option.Option.Some y))) :
    ∀ (i : Nat) (hi : i < lst.val.size),
      0 < (lst.val[i]'hi).toInt → y.toInt ≤ (lst.val[i]'hi).toInt := by
  obtain ⟨av, af, bv, bf, h_wrap, _, _, _, _, _, h_bf_min⟩ := wrapper_master lst
  rw [h_wrap] at hres
  obtain ⟨h_a, h_b⟩ := rustM_ok_tuple2_inj _ _ _ _ hres
  have h_bf_true : bf = true := by
    cases bf with
    | true => rfl
    | false => simp at h_b
  have h_bv_eq_y : bv = y := by
    rw [h_bf_true] at h_b
    simp at h_b
    exact h_b
  intro i hi h_ipos
  have := h_bf_min h_bf_true i hi h_ipos
  rw [← h_bv_eq_y]; exact this

end Clever_135_largest_smallest_integersObligations
