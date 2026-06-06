-- Companion obligations file for the `clever_089_next_smallest` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_089_next_smallest

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_089_next_smallestObligations

/-! ## Standard helper lemmas (ported from pluck_modified / rescale_to_unit_modified). -/

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

/-! ## Step lemmas for `min_at`. -/

private theorem min_at_oob
    (l : RustSlice i64) (i : usize) (best : i64) (found : Bool)
    (hi : l.val.size ≤ i.toNat) :
    clever_089_next_smallest.min_at l i best found
      = RustM.ok (rust_primitives.hax.Tuple2.mk best found) := by
  conv => lhs; unfold clever_089_next_smallest.min_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = true := by
    rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, h_cond, ↓reduceIte]
  rfl

private theorem min_at_take
    (l : RustSlice i64) (i : usize) (best : i64) (found : Bool)
    (hi : i.toNat < l.val.size)
    (h_cond : ¬ found ∨ (l.val[i.toNat]'hi).toInt < best.toInt) :
    clever_089_next_smallest.min_at l i best found
      = clever_089_next_smallest.min_at l (i + 1) (l.val[i.toNat]'hi) true := by
  conv => lhs; unfold clever_089_next_smallest.min_at
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
  have h_add_eq : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
    usize_add_one_eq i h_no_ov
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, rust_primitives.cmp.lt,
             rust_primitives.hax.logical_op.not, rust_primitives.hax.logical_op.or,
             h_or_true, h_add_eq]

private theorem min_at_skip
    (l : RustSlice i64) (i : usize) (best : i64) (found : Bool)
    (hi : i.toNat < l.val.size)
    (h_cond : found = true ∧ best.toInt ≤ (l.val[i.toNat]'hi).toInt) :
    clever_089_next_smallest.min_at l i best found
      = clever_089_next_smallest.min_at l (i + 1) best found := by
  conv => lhs; unfold clever_089_next_smallest.min_at
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
  obtain ⟨hf_true, hge⟩ := h_cond
  have h_not_found : (!found) = false := by rw [hf_true]; rfl
  have h_not_lt : decide ((l.val[i.toNat]'hi) < best) = false := by
    rw [decide_eq_false_iff_not]
    intro h_lt
    have h_lt_int : (l.val[i.toNat]'hi).toInt < best.toInt :=
      Int64.lt_iff_toInt_lt.mp h_lt
    omega
  have h_or_false : ((!found) || decide ((l.val[i.toNat]'hi) < best)) = false := by
    rw [h_not_found, h_not_lt]; rfl
  have h_add_eq : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
    usize_add_one_eq i h_no_ov
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, rust_primitives.cmp.lt,
             rust_primitives.hax.logical_op.not, rust_primitives.hax.logical_op.or,
             h_or_false, h_add_eq]

/-! ## Step lemmas for `min_above_at`. -/

private theorem min_above_at_oob
    (l : RustSlice i64) (floor : i64) (i : usize) (best : i64) (found : Bool)
    (hi : l.val.size ≤ i.toNat) :
    clever_089_next_smallest.min_above_at l floor i best found
      = RustM.ok (rust_primitives.hax.Tuple2.mk best found) := by
  conv => lhs; unfold clever_089_next_smallest.min_above_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = true := by
    rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, h_cond, ↓reduceIte]
  rfl

private theorem min_above_at_take
    (l : RustSlice i64) (floor : i64) (i : usize) (best : i64) (found : Bool)
    (hi : i.toNat < l.val.size)
    (h_above : floor.toInt < (l.val[i.toNat]'hi).toInt)
    (h_cond : ¬ found ∨ (l.val[i.toNat]'hi).toInt < best.toInt) :
    clever_089_next_smallest.min_above_at l floor i best found
      = clever_089_next_smallest.min_above_at l floor (i + 1)
          (l.val[i.toNat]'hi) true := by
  conv => lhs; unfold clever_089_next_smallest.min_above_at
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
  have h_above_dec : decide ((l.val[i.toNat]'hi) > floor) = true := by
    rw [decide_eq_true_iff]
    show floor < (l.val[i.toNat]'hi)
    exact Int64.lt_iff_toInt_lt.mpr h_above
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
      (decide ((l.val[i.toNat]'hi) > floor) &&
        ((!found) || decide ((l.val[i.toNat]'hi) < best))) = true := by
    rw [h_above_dec, h_or_true]; rfl
  have h_add_eq : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
    usize_add_one_eq i h_no_ov
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, rust_primitives.cmp.lt, rust_primitives.cmp.gt,
             rust_primitives.hax.logical_op.not, rust_primitives.hax.logical_op.or,
             rust_primitives.hax.logical_op.and,
             h_and_true, h_add_eq]

private theorem min_above_at_skip
    (l : RustSlice i64) (floor : i64) (i : usize) (best : i64) (found : Bool)
    (hi : i.toNat < l.val.size)
    (h_cond : (l.val[i.toNat]'hi).toInt ≤ floor.toInt ∨
              (found = true ∧ best.toInt ≤ (l.val[i.toNat]'hi).toInt)) :
    clever_089_next_smallest.min_above_at l floor i best found
      = clever_089_next_smallest.min_above_at l floor (i + 1) best found := by
  conv => lhs; unfold clever_089_next_smallest.min_above_at
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
      (decide ((l.val[i.toNat]'hi) > floor) &&
        ((!found) || decide ((l.val[i.toNat]'hi) < best))) = false := by
    rcases h_cond with h_le | ⟨hf_true, hge⟩
    · -- l[i] ≤ floor: above-check is false
      have h_above_false : decide ((l.val[i.toNat]'hi) > floor) = false := by
        rw [decide_eq_false_iff_not]
        intro h_gt
        have h_gt_int : floor.toInt < (l.val[i.toNat]'hi).toInt :=
          Int64.lt_iff_toInt_lt.mp h_gt
        omega
      rw [h_above_false]; rfl
    · -- found ∧ best ≤ l[i]: take-check false
      have h_not_found : (!found) = false := by rw [hf_true]; rfl
      have h_not_lt : decide ((l.val[i.toNat]'hi) < best) = false := by
        rw [decide_eq_false_iff_not]
        intro h_lt
        have h_lt_int : (l.val[i.toNat]'hi).toInt < best.toInt :=
          Int64.lt_iff_toInt_lt.mp h_lt
        omega
      have h_or_false : ((!found) || decide ((l.val[i.toNat]'hi) < best)) = false := by
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

/-! ## Master correctness lemma for `min_at`. -/

private theorem min_at_correct (l : RustSlice i64) :
    ∀ (m : Nat) (i : usize) (best : i64) (found : Bool),
      l.val.size - i.toNat ≤ m →
      i.toNat ≤ l.val.size →
      ∃ (rv : i64) (rf : Bool),
        clever_089_next_smallest.min_at l i best found
          = RustM.ok (rust_primitives.hax.Tuple2.mk rv rf) ∧
        (rf = true ↔ found = true ∨ i.toNat < l.val.size) ∧
        (rf = true →
          (found = true ∧ rv = best) ∨
          ∃ (j : Nat) (hj : j < l.val.size), i.toNat ≤ j ∧ rv = (l.val[j]'hj)) ∧
        (rf = true →
          (found = true → rv.toInt ≤ best.toInt) ∧
          ∀ (j : Nat) (hj : j < l.val.size), i.toNat ≤ j →
            rv.toInt ≤ (l.val[j]'hj).toInt) := by
  intro m
  induction m with
  | zero =>
    intro i best found hm hi_le
    have hi_eq : i.toNat = l.val.size := by omega
    have hi_ge : l.val.size ≤ i.toNat := by omega
    refine ⟨best, found, min_at_oob l i best found hi_ge, ?_, ?_, ?_⟩
    · -- liveness
      constructor
      · intro hf; left; exact hf
      · rintro (hf | hlt)
        · exact hf
        · rw [hi_eq] at hlt; omega
    · -- membership
      intro hrf; left
      exact ⟨hrf, rfl⟩
    · -- minimality
      intro hrf
      refine ⟨fun _ => Int.le_refl _, ?_⟩
      intro j hj h_jge
      rw [hi_eq] at h_jge; omega
  | succ m ih =>
    intro i best found hm hi_le
    by_cases hi_ge : l.val.size ≤ i.toNat
    · -- OOB case
      have hi_eq : i.toNat = l.val.size := by omega
      refine ⟨best, found, min_at_oob l i best found hi_ge, ?_, ?_, ?_⟩
      · constructor
        · intro hf; left; exact hf
        · rintro (hf | hlt)
          · exact hf
          · rw [hi_eq] at hlt; omega
      · intro hrf; left; exact ⟨hrf, rfl⟩
      · intro hrf
        refine ⟨fun _ => Int.le_refl _, ?_⟩
        intro j hj h_jge
        rw [hi_eq] at h_jge; omega
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov : i.toNat + 1 < 2 ^ 64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_m_le : l.val.size - (i + 1).toNat ≤ m := by rw [h_i1]; omega
      by_cases h_take : ¬ found = true ∨ (l.val[i.toNat]'hi_lt).toInt < best.toInt
      · -- TAKE branch
        have h_cond_simpl : ¬ found ∨ (l.val[i.toNat]'hi_lt).toInt < best.toInt := by
          rcases h_take with hnf | hlt
          · left; intro hf; apply hnf; cases found
            · cases hf
            · rfl
          · right; exact hlt
        have h_step := min_at_take l i best found hi_lt h_cond_simpl
        obtain ⟨rv, rf, hres, h_live, h_mem, h_min⟩ :=
          ih (i + 1) (l.val[i.toNat]'hi_lt) true h_m_le h_i1_le
        refine ⟨rv, rf, ?_, ?_, ?_, ?_⟩
        · rw [h_step]; exact hres
        · -- liveness
          constructor
          · intro _; right; exact hi_lt
          · intro _
            apply h_live.mpr; left; rfl
        · -- membership
          intro hrf
          rcases h_mem hrf with ⟨hf_true, hrv_eq⟩ | ⟨j, hj, h_jge, h_rv_eq⟩
          · right
            refine ⟨i.toNat, hi_lt, Nat.le_refl _, ?_⟩
            exact hrv_eq
          · right
            refine ⟨j, hj, ?_, h_rv_eq⟩
            rw [h_i1] at h_jge; omega
        · -- minimality
          intro hrf
          obtain ⟨h_min_best, h_min_suffix⟩ := h_min hrf
          have h_min_li : rv.toInt ≤ (l.val[i.toNat]'hi_lt).toInt := h_min_best rfl
          refine ⟨?_, ?_⟩
          · intro hf
            rcases h_take with hnf | hlt
            · exact absurd hf hnf
            · omega
          · intro j hj h_jge
            by_cases h_jeq : j = i.toNat
            · subst h_jeq; exact h_min_li
            · have h_jge1 : (i + 1).toNat ≤ j := by rw [h_i1]; omega
              exact h_min_suffix j hj h_jge1
      · -- SKIP branch
        have h_skip_cond : found = true ∧ best.toInt ≤ (l.val[i.toNat]'hi_lt).toInt := by
          have h_nf : ¬ (¬ found = true) := fun hnf => h_take (Or.inl hnf)
          have h_nlt : ¬ (l.val[i.toNat]'hi_lt).toInt < best.toInt :=
            fun hlt => h_take (Or.inr hlt)
          have hf : found = true := by
            cases found with
            | false => exact absurd (fun h => Bool.noConfusion h) h_nf
            | true => rfl
          exact ⟨hf, by omega⟩
        have h_step := min_at_skip l i best found hi_lt h_skip_cond
        obtain ⟨rv, rf, hres, h_live, h_mem, h_min⟩ :=
          ih (i + 1) best found h_m_le h_i1_le
        refine ⟨rv, rf, ?_, ?_, ?_, ?_⟩
        · rw [h_step]; exact hres
        · -- liveness
          constructor
          · intro hrf
            rcases h_live.mp hrf with hf | hlt
            · left; exact hf
            · right
              -- (i+1).toNat < size ↔ i.toNat + 1 < size, so certainly i.toNat < size
              omega
          · rintro (hf | _)
            · apply h_live.mpr; left; exact hf
            · -- i.toNat < size; show rf = true.
              -- We have found = true (from h_skip_cond), so apply h_live with left.
              apply h_live.mpr; left; exact h_skip_cond.1
        · -- membership
          intro hrf
          rcases h_mem hrf with ⟨hf, hrv_eq⟩ | ⟨j, hj, h_jge, h_rv_eq⟩
          · left; exact ⟨hf, hrv_eq⟩
          · right
            refine ⟨j, hj, ?_, h_rv_eq⟩
            rw [h_i1] at h_jge; omega
        · -- minimality
          intro hrf
          obtain ⟨h_min_best, h_min_suffix⟩ := h_min hrf
          refine ⟨h_min_best, ?_⟩
          intro j hj h_jge
          by_cases h_jeq : j = i.toNat
          · -- rv ≤ best ≤ l[i]
            subst h_jeq
            have h_rv_best : rv.toInt ≤ best.toInt := h_min_best h_skip_cond.1
            have h_best_li : best.toInt ≤ (l.val[i.toNat]'hi_lt).toInt := h_skip_cond.2
            omega
          · have h_jge1 : (i + 1).toNat ≤ j := by rw [h_i1]; omega
            exact h_min_suffix j hj h_jge1

/-! ## Master correctness lemma for `min_above_at`. -/

private theorem min_above_at_correct (l : RustSlice i64) (floor : i64) :
    ∀ (m : Nat) (i : usize) (best : i64) (found : Bool),
      l.val.size - i.toNat ≤ m →
      i.toNat ≤ l.val.size →
      ∃ (rv : i64) (rf : Bool),
        clever_089_next_smallest.min_above_at l floor i best found
          = RustM.ok (rust_primitives.hax.Tuple2.mk rv rf) ∧
        (rf = true ↔ found = true ∨ ∃ (j : Nat) (hj : j < l.val.size),
                                      i.toNat ≤ j ∧ floor.toInt < (l.val[j]'hj).toInt) ∧
        (rf = true →
          (found = true ∧ rv = best) ∨
          ∃ (j : Nat) (hj : j < l.val.size),
            i.toNat ≤ j ∧ rv = (l.val[j]'hj) ∧ floor.toInt < (l.val[j]'hj).toInt) ∧
        (rf = true →
          (found = true → rv.toInt ≤ best.toInt) ∧
          ∀ (j : Nat) (hj : j < l.val.size),
            i.toNat ≤ j → floor.toInt < (l.val[j]'hj).toInt →
              rv.toInt ≤ (l.val[j]'hj).toInt) := by
  intro m
  induction m with
  | zero =>
    intro i best found hm hi_le
    have hi_eq : i.toNat = l.val.size := by omega
    have hi_ge : l.val.size ≤ i.toNat := by omega
    refine ⟨best, found, min_above_at_oob l floor i best found hi_ge, ?_, ?_, ?_⟩
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
      refine ⟨best, found, min_above_at_oob l floor i best found hi_ge, ?_, ?_, ?_⟩
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
          floor.toInt < (l.val[i.toNat]'hi_lt).toInt ∧
          (¬ found = true ∨ (l.val[i.toNat]'hi_lt).toInt < best.toInt)
      · -- TAKE branch
        obtain ⟨h_above, h_cond_raw⟩ := h_take
        have h_cond_simpl : ¬ found ∨ (l.val[i.toNat]'hi_lt).toInt < best.toInt := by
          rcases h_cond_raw with hnf | hlt
          · left; intro hf; apply hnf; cases found
            · cases hf
            · rfl
          · right; exact hlt
        have h_step := min_above_at_take l floor i best found hi_lt h_above h_cond_simpl
        obtain ⟨rv, rf, hres, h_live, h_mem, h_min⟩ :=
          ih (i + 1) (l.val[i.toNat]'hi_lt) true h_m_le h_i1_le
        refine ⟨rv, rf, ?_, ?_, ?_, ?_⟩
        · rw [h_step]; exact hres
        · -- liveness
          constructor
          · intro _; right
            exact ⟨i.toNat, hi_lt, Nat.le_refl _, h_above⟩
          · intro _
            apply h_live.mpr; left; rfl
        · -- membership
          intro hrf
          rcases h_mem hrf with ⟨hf_true, hrv_eq⟩ | ⟨j, hj, h_jge, h_rv_eq, h_jabove⟩
          · right
            refine ⟨i.toNat, hi_lt, Nat.le_refl _, hrv_eq, h_above⟩
          · right
            refine ⟨j, hj, ?_, h_rv_eq, h_jabove⟩
            rw [h_i1] at h_jge; omega
        · -- minimality
          intro hrf
          obtain ⟨h_min_best, h_min_suffix⟩ := h_min hrf
          have h_min_li : rv.toInt ≤ (l.val[i.toNat]'hi_lt).toInt := h_min_best rfl
          refine ⟨?_, ?_⟩
          · intro hf
            rcases h_cond_raw with hnf | hlt
            · exact absurd hf hnf
            · omega
          · intro j hj h_jge h_jabove
            by_cases h_jeq : j = i.toNat
            · subst h_jeq; exact h_min_li
            · have h_jge1 : (i + 1).toNat ≤ j := by rw [h_i1]; omega
              exact h_min_suffix j hj h_jge1 h_jabove
      · -- SKIP branch
        have h_skip_cond :
            (l.val[i.toNat]'hi_lt).toInt ≤ floor.toInt ∨
            (found = true ∧ best.toInt ≤ (l.val[i.toNat]'hi_lt).toInt) := by
          by_cases h_above : floor.toInt < (l.val[i.toNat]'hi_lt).toInt
          · right
            have h_neg : ¬ (¬ found = true ∨ (l.val[i.toNat]'hi_lt).toInt < best.toInt) := by
              intro h; exact h_take ⟨h_above, h⟩
            have h_nf : ¬ ¬ found = true := fun hnf => h_neg (Or.inl hnf)
            have h_nlt : ¬ (l.val[i.toNat]'hi_lt).toInt < best.toInt :=
              fun hlt => h_neg (Or.inr hlt)
            have hf : found = true := by
              cases found with
              | false => exact absurd (fun h => Bool.noConfusion h) h_nf
              | true => rfl
            exact ⟨hf, by omega⟩
          · left; omega
        have h_step := min_above_at_skip l floor i best found hi_lt h_skip_cond
        obtain ⟨rv, rf, hres, h_live, h_mem, h_min⟩ :=
          ih (i + 1) best found h_m_le h_i1_le
        refine ⟨rv, rf, ?_, ?_, ?_, ?_⟩
        · rw [h_step]; exact hres
        · -- liveness
          constructor
          · intro hrf
            rcases h_live.mp hrf with hf | ⟨j, hj, h_jge, h_jabove⟩
            · left; exact hf
            · right; refine ⟨j, hj, ?_, h_jabove⟩
              rw [h_i1] at h_jge; omega
          · rintro (hf | ⟨j, hj, h_jge, h_jabove⟩)
            · apply h_live.mpr; left; exact hf
            · apply h_live.mpr
              by_cases h_jeq : j = i.toNat
              · -- Need to show (i+1) case: but j = i.toNat, so we use h_skip_cond
                subst h_jeq
                rcases h_skip_cond with h_le | ⟨hf, _⟩
                · -- l[i] ≤ floor contradicts h_jabove
                  exfalso; omega
                · left; exact hf
              · right
                refine ⟨j, hj, ?_, h_jabove⟩
                rw [h_i1]; omega
        · -- membership
          intro hrf
          rcases h_mem hrf with ⟨hf, hrv_eq⟩ | ⟨j, hj, h_jge, h_rv_eq, h_jabove⟩
          · left; exact ⟨hf, hrv_eq⟩
          · right
            refine ⟨j, hj, ?_, h_rv_eq, h_jabove⟩
            rw [h_i1] at h_jge; omega
        · -- minimality
          intro hrf
          obtain ⟨h_min_best, h_min_suffix⟩ := h_min hrf
          refine ⟨h_min_best, ?_⟩
          intro j hj h_jge h_jabove
          by_cases h_jeq : j = i.toNat
          · subst h_jeq
            rcases h_skip_cond with h_le | ⟨hf, h_le⟩
            · exfalso; omega
            · have h_rv_best : rv.toInt ≤ best.toInt := h_min_best hf
              omega
          · have h_jge1 : (i + 1).toNat ≤ j := by rw [h_i1]; omega
            exact h_min_suffix j hj h_jge1 h_jabove

/-! ## Master reduction for `next_smallest`. -/

/-- Reduce `next_smallest l` to a case-analysis on whether `f1 = true` and the
    eventual result of `min_above_at`. We do not need full structural reductions
    of the `let ⟨m1, f1⟩ ←` because once we know the result of `min_at`, the
    bind unfolds via `pure_bind`. -/
private theorem next_smallest_master (l : RustSlice i64) :
    -- Empty case: returns None.
    (l.val.size = 0 →
        clever_089_next_smallest.next_smallest l
          = RustM.ok core_models.option.Option.None) ∧
    -- Non-empty case: there is a min `m1` (witnessed at some `j1`) and the
    -- result depends on whether anything is strictly above it.
    (0 < l.val.size →
        ∃ (m1 : i64) (j1 : Nat) (hj1 : j1 < l.val.size),
          m1 = (l.val[j1]'hj1) ∧
          (∀ (k : Nat) (hk : k < l.val.size), m1.toInt ≤ (l.val[k]'hk).toInt) ∧
          -- 2a. No element above m1: None.
          ((¬ ∃ (k : Nat) (hk : k < l.val.size), m1.toInt < (l.val[k]'hk).toInt) →
              clever_089_next_smallest.next_smallest l
                = RustM.ok core_models.option.Option.None) ∧
          -- 2b. Some element above m1: Some m2.
          ((∃ (k : Nat) (hk : k < l.val.size), m1.toInt < (l.val[k]'hk).toInt) →
              ∃ (m2 : i64) (j2 : Nat) (hj2 : j2 < l.val.size),
                clever_089_next_smallest.next_smallest l
                  = RustM.ok (core_models.option.Option.Some m2) ∧
                m2 = (l.val[j2]'hj2) ∧
                m1.toInt < (l.val[j2]'hj2).toInt ∧
                (∀ (k : Nat) (hk : k < l.val.size),
                    m1.toInt < (l.val[k]'hk).toInt → m2.toInt ≤ (l.val[k]'hk).toInt))) := by
  -- Invoke min_at_correct.
  obtain ⟨rv1, rf1, h_min_at, h_live1, h_mem1, h_min1⟩ :=
    min_at_correct l l.val.size (0 : usize) (0 : i64) false
      (by show l.val.size - (0 : usize).toNat ≤ l.val.size
          rw [usize_zero_toNat]; omega)
      (by show (0 : usize).toNat ≤ l.val.size; rw [usize_zero_toNat]; omega)
  refine ⟨?_, ?_⟩
  · -- Empty case.
    intro hempty
    -- f1 = false because: not found = true ∧ ¬ (0 < size)
    have h_rf1_false : rf1 = false := by
      cases hrf : rf1
      · rfl
      · exfalso
        rcases h_live1.mp hrf with hf | hlt
        · cases hf
        · rw [usize_zero_toNat] at hlt; omega
    unfold clever_089_next_smallest.next_smallest
    rw [h_min_at]
    rw [h_rf1_false]
    -- After rewrites, the body is: let ⟨m1, f1⟩ := ⟨rv1, false⟩; if ... then None else ...
    -- The bind reduces because we have a pure result.
    simp only [pure_bind, RustM_ok_bind, rust_primitives.hax.logical_op.not,
               Bool.not_false, ↓reduceIte]
    rfl
  · -- Non-empty case.
    intro hpos
    -- f1 = true because i = 0 < size.
    have h_rf1_true : rf1 = true := by
      apply h_live1.mpr
      right; rw [usize_zero_toNat]; exact hpos
    rw [h_rf1_true] at h_min_at
    -- Membership: rv1 = some l[j], since the (found = true) branch of h_mem1 has hf = false.
    obtain h_mem_inst := h_mem1 h_rf1_true
    rcases h_mem_inst with ⟨hf, _⟩ | ⟨j1, hj1, h_j1ge, h_rv1_eq⟩
    · cases hf
    · -- Minimality across all suffix indices (suffix is [0, size) = all of l).
      obtain ⟨_, h_min_suffix⟩ := h_min1 h_rf1_true
      have h_rv1_min : ∀ (k : Nat) (hk : k < l.val.size), rv1.toInt ≤ (l.val[k]'hk).toInt := by
        intro k hk
        apply h_min_suffix k hk
        rw [usize_zero_toNat]; omega
      refine ⟨rv1, j1, hj1, h_rv1_eq, h_rv1_min, ?_, ?_⟩
      · -- 2a. No element above m1: result is None.
        intro h_no_above
        -- Apply min_above_at_correct: f2 = false (no above-floor element, no initial found).
        obtain ⟨rv2, rf2, h_above, h_live2, h_mem2, h_min2⟩ :=
          min_above_at_correct l rv1 l.val.size (0 : usize) (0 : i64) false
            (by show l.val.size - (0 : usize).toNat ≤ l.val.size
                rw [usize_zero_toNat]; omega)
            (by show (0 : usize).toNat ≤ l.val.size; rw [usize_zero_toNat]; omega)
        have h_rf2_false : rf2 = false := by
          cases hrf : rf2
          · rfl
          · exfalso
            rcases h_live2.mp hrf with hf | ⟨k, hk, _, h_above_k⟩
            · cases hf
            · exact h_no_above ⟨k, hk, h_above_k⟩
        unfold clever_089_next_smallest.next_smallest
        rw [h_min_at]
        simp only [pure_bind, RustM_ok_bind, rust_primitives.hax.logical_op.not,
                   Bool.not_true, ↓reduceIte, Bool.false_eq_true]
        rw [h_above, h_rf2_false]
        simp only [pure_bind, RustM_ok_bind, ↓reduceIte, Bool.false_eq_true]
        rfl
      · -- 2b. Some element above m1: result is Some m2.
        rintro ⟨k0, hk0, h_above_k0⟩
        obtain ⟨rv2, rf2, h_above, h_live2, h_mem2, h_min2⟩ :=
          min_above_at_correct l rv1 l.val.size (0 : usize) (0 : i64) false
            (by show l.val.size - (0 : usize).toNat ≤ l.val.size
                rw [usize_zero_toNat]; omega)
            (by show (0 : usize).toNat ≤ l.val.size; rw [usize_zero_toNat]; omega)
        have h_rf2_true : rf2 = true := by
          apply h_live2.mpr
          right
          refine ⟨k0, hk0, ?_, h_above_k0⟩
          rw [usize_zero_toNat]; omega
        rw [h_rf2_true] at h_above
        -- Membership.
        obtain h_mem_inst := h_mem2 h_rf2_true
        rcases h_mem_inst with ⟨hf, _⟩ | ⟨j2, hj2, _, h_rv2_eq, h_rv2_above⟩
        · cases hf
        · obtain ⟨_, h_min2_suffix⟩ := h_min2 h_rf2_true
          have h_rv2_min :
              ∀ (k : Nat) (hk : k < l.val.size),
                  rv1.toInt < (l.val[k]'hk).toInt → rv2.toInt ≤ (l.val[k]'hk).toInt := by
            intro k hk h_above_k
            apply h_min2_suffix k hk _ h_above_k
            rw [usize_zero_toNat]; omega
          refine ⟨rv2, j2, hj2, ?_, h_rv2_eq, h_rv2_above, h_rv2_min⟩
          unfold clever_089_next_smallest.next_smallest
          rw [h_min_at]
          simp only [pure_bind, RustM_ok_bind, rust_primitives.hax.logical_op.not,
                     Bool.not_true, ↓reduceIte, Bool.false_eq_true]
          rw [h_above]
          simp only [pure_bind, RustM_ok_bind, h_rf2_true, ↓reduceIte]
          rfl

/-! ## Theorem obligations. -/

/-- Failure / None clause (test `empty_is_none`):
    when the input slice is empty, the result is `None`. -/
theorem empty_returns_none
    (l : RustSlice i64)
    (hempty : l.val.size = 0) :
    clever_089_next_smallest.next_smallest l
      = RustM.ok core_models.option.Option.None := by
  obtain ⟨h_empty, _⟩ := next_smallest_master l
  exact h_empty hempty

/-- Failure / None clause (proptest `all_equal_is_none`):
    when every element of `l` is the same value, the result is `None`. -/
theorem all_equal_returns_none
    (l : RustSlice i64) (x : i64)
    (h_size_pos : 0 < l.val.size)
    (h_all : ∀ (i : Nat) (hi : i < l.val.size), (l.val[i]'hi) = x) :
    clever_089_next_smallest.next_smallest l
      = RustM.ok core_models.option.Option.None := by
  obtain ⟨_, h_nonempty⟩ := next_smallest_master l
  obtain ⟨m1, j1, hj1, h_m1_eq, h_m1_min, h_none, _⟩ := h_nonempty h_size_pos
  apply h_none
  -- No element strictly above m1: every element is x = m1.
  rintro ⟨k, hk, h_above⟩
  have h_lk_eq : (l.val[k]'hk) = x := h_all k hk
  have h_m1_eq_x : m1 = x := by rw [h_m1_eq]; exact h_all j1 hj1
  rw [h_lk_eq, h_m1_eq_x] at h_above
  omega

/-- Converse / None-implies clause. -/
theorem none_implies_fewer_than_two_unique
    (l : RustSlice i64)
    (h_res : clever_089_next_smallest.next_smallest l
              = RustM.ok core_models.option.Option.None) :
    ∀ (i j : Nat) (hi : i < l.val.size) (hj : j < l.val.size),
      (l.val[i]'hi) = (l.val[j]'hj) := by
  intro i j hi hj
  -- We exclude size = 0 since hi makes that impossible. For size > 0:
  have h_size_pos : 0 < l.val.size := Nat.lt_of_le_of_lt (Nat.zero_le _) hi
  obtain ⟨_, h_nonempty⟩ := next_smallest_master l
  obtain ⟨m1, j1, hj1, h_m1_eq, h_m1_min, _h_none, h_some⟩ := h_nonempty h_size_pos
  -- Suppose there's a k with m1 < l[k]: contradiction with result = None.
  by_cases h_exists_above : ∃ (k : Nat) (hk : k < l.val.size), m1.toInt < (l.val[k]'hk).toInt
  · exfalso
    obtain ⟨m2, j2, hj2, h_res_some, _, _, _⟩ := h_some h_exists_above
    rw [h_res] at h_res_some
    -- h_res_some : RustM.ok None = RustM.ok (Some m2): contradiction.
    injection h_res_some with hcontra
    cases hcontra
  · -- All elements equal m1.
    have h_li_eq_m1 : (l.val[i]'hi).toInt = m1.toInt := by
      have h1 : m1.toInt ≤ (l.val[i]'hi).toInt := h_m1_min i hi
      have h2 : ¬ m1.toInt < (l.val[i]'hi).toInt :=
        fun h => h_exists_above ⟨i, hi, h⟩
      omega
    have h_lj_eq_m1 : (l.val[j]'hj).toInt = m1.toInt := by
      have h1 : m1.toInt ≤ (l.val[j]'hj).toInt := h_m1_min j hj
      have h2 : ¬ m1.toInt < (l.val[j]'hj).toInt :=
        fun h => h_exists_above ⟨j, hj, h⟩
      omega
    have h_toInt_eq : (l.val[i]'hi).toInt = (l.val[j]'hj).toInt := by
      rw [h_li_eq_m1, h_lj_eq_m1]
    exact Int64.toInt_inj.mp h_toInt_eq

/-- Success / membership clause. -/
theorem some_result_is_in_list
    (l : RustSlice i64) (x : i64)
    (h_res : clever_089_next_smallest.next_smallest l
              = RustM.ok (core_models.option.Option.Some x)) :
    ∃ (i : Nat) (hi : i < l.val.size), (l.val[i]'hi) = x := by
  -- size > 0 must hold (else result would be None).
  by_cases h_size : l.val.size = 0
  · exfalso
    obtain ⟨h_empty, _⟩ := next_smallest_master l
    rw [h_empty h_size] at h_res
    injection h_res with hcontra
    cases hcontra
  · have h_size_pos : 0 < l.val.size := Nat.pos_of_ne_zero h_size
    obtain ⟨_, h_nonempty⟩ := next_smallest_master l
    obtain ⟨m1, j1, hj1, h_m1_eq, h_m1_min, h_none, h_some⟩ := h_nonempty h_size_pos
    -- An element strictly above m1 must exist (else None, contradicting Some x).
    by_cases h_exists_above : ∃ (k : Nat) (hk : k < l.val.size), m1.toInt < (l.val[k]'hk).toInt
    · obtain ⟨m2, j2, hj2, h_res_some, h_m2_eq, h_m2_above, h_m2_min⟩ := h_some h_exists_above
      rw [h_res] at h_res_some
      injection h_res_some with h1
      injection h1 with h2
      have hx : x = m2 := core_models.option.Option.Some.inj h2
      refine ⟨j2, hj2, ?_⟩
      rw [← h_m2_eq, ← hx]
    · exfalso
      have := h_none h_exists_above
      rw [h_res] at this
      injection this with hcontra
      cases hcontra

/-- Success / not-minimum clause. -/
theorem some_result_exceeds_some_element
    (l : RustSlice i64) (x : i64)
    (h_res : clever_089_next_smallest.next_smallest l
              = RustM.ok (core_models.option.Option.Some x)) :
    ∃ (i : Nat) (hi : i < l.val.size), (l.val[i]'hi).toInt < x.toInt := by
  by_cases h_size : l.val.size = 0
  · exfalso
    obtain ⟨h_empty, _⟩ := next_smallest_master l
    rw [h_empty h_size] at h_res
    injection h_res with hcontra
    cases hcontra
  · have h_size_pos : 0 < l.val.size := Nat.pos_of_ne_zero h_size
    obtain ⟨_, h_nonempty⟩ := next_smallest_master l
    obtain ⟨m1, j1, hj1, h_m1_eq, h_m1_min, h_none, h_some⟩ := h_nonempty h_size_pos
    by_cases h_exists_above : ∃ (k : Nat) (hk : k < l.val.size), m1.toInt < (l.val[k]'hk).toInt
    · obtain ⟨m2, j2, hj2, h_res_some, h_m2_eq, h_m2_above, _⟩ := h_some h_exists_above
      rw [h_res] at h_res_some
      injection h_res_some with h1
      injection h1 with h2
      have hx : x = m2 := core_models.option.Option.Some.inj h2
      refine ⟨j1, hj1, ?_⟩
      -- l[j1].toInt = m1.toInt < m2.toInt = x.toInt
      have h_lj1 : (l.val[j1]'hj1).toInt = m1.toInt := by rw [← h_m1_eq]
      have h_m2_x : m2.toInt = x.toInt := by rw [← hx]
      have h_m1_lt_m2 : m1.toInt < m2.toInt := by rw [h_m2_eq]; exact h_m2_above
      omega
    · exfalso
      have := h_none h_exists_above
      rw [h_res] at this
      injection this with hcontra
      cases hcontra

/-- Success / next-smallest clause. -/
theorem nothing_strictly_between_min_and_result
    (l : RustSlice i64) (x : i64)
    (h_res : clever_089_next_smallest.next_smallest l
              = RustM.ok (core_models.option.Option.Some x)) :
    ∀ (i j : Nat) (hi : i < l.val.size) (hj : j < l.val.size),
      (∀ (k : Nat) (hk : k < l.val.size),
          (l.val[i]'hi).toInt ≤ (l.val[k]'hk).toInt) →
      (l.val[i]'hi).toInt < (l.val[j]'hj).toInt →
      x.toInt ≤ (l.val[j]'hj).toInt := by
  intro i j hi hj h_min_i h_lt
  -- size > 0 from hi.
  have h_size_pos : 0 < l.val.size := Nat.lt_of_le_of_lt (Nat.zero_le _) hi
  obtain ⟨_, h_nonempty⟩ := next_smallest_master l
  obtain ⟨m1, j1, hj1, h_m1_eq, h_m1_min, h_none, h_some⟩ := h_nonempty h_size_pos
  -- m1 and l[i] are both minima, so m1.toInt = l[i].toInt.
  have h_m1_le_li : m1.toInt ≤ (l.val[i]'hi).toInt := h_m1_min i hi
  have h_li_le_m1 : (l.val[i]'hi).toInt ≤ m1.toInt := by
    rw [h_m1_eq]; exact h_min_i j1 hj1
  have h_m1_eq_li : m1.toInt = (l.val[i]'hi).toInt := by omega
  -- l[j] > l[i] = m1, so the above-witness exists.
  have h_above_j : m1.toInt < (l.val[j]'hj).toInt := by
    rw [h_m1_eq_li]; exact h_lt
  obtain ⟨m2, j2, hj2, h_res_some, h_m2_eq, _, h_m2_min⟩ :=
    h_some ⟨j, hj, h_above_j⟩
  rw [h_res] at h_res_some
  injection h_res_some with h1
  injection h1 with h2
  have hx : x = m2 := core_models.option.Option.Some.inj h2
  have h_m2_le_lj : m2.toInt ≤ (l.val[j]'hj).toInt := h_m2_min j hj h_above_j
  have h_m2_eq_x : m2.toInt = x.toInt := by rw [← hx]
  omega

end Clever_089_next_smallestObligations
