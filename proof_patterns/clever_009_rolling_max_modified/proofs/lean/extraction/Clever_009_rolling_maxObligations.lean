-- Companion obligations file for the `clever_009_rolling_max` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_009_rolling_max

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_009_rolling_maxObligations

/-! ## Specification of the prefix-max oracle (Int-valued, via if/then/else
to avoid needing the `max_eq_left`/`max_eq_right` Mathlib lemmas). -/

private def prefix_max_int (numbers : RustSlice i64) : Nat → Int
  | 0     => 0
  | k + 1 =>
      if h : k < numbers.val.size then
        if k = 0 then
          (numbers.val[k]'h).toInt
        else
          if prefix_max_int numbers k < (numbers.val[k]'h).toInt then
            (numbers.val[k]'h).toInt
          else
            prefix_max_int numbers k
      else
        prefix_max_int numbers k

/-! ## Helpers -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide

private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

private theorem prefix_max_int_one
    (numbers : RustSlice i64) (h : 0 < numbers.val.size) :
    prefix_max_int numbers 1 = (numbers.val[0]'h).toInt := by
  show (if h' : 0 < numbers.val.size then
          if (0 : Nat) = 0 then (numbers.val[0]'h').toInt
          else _
        else prefix_max_int numbers 0) = (numbers.val[0]'h).toInt
  rw [dif_pos h, if_pos rfl]

private theorem prefix_max_int_succ
    (numbers : RustSlice i64) (k : Nat) (hk : k < numbers.val.size) (hk_pos : 1 ≤ k) :
    prefix_max_int numbers (k + 1) =
      (if prefix_max_int numbers k < (numbers.val[k]'hk).toInt then
        (numbers.val[k]'hk).toInt else prefix_max_int numbers k) := by
  show (if h' : k < numbers.val.size then
          if k = 0 then (numbers.val[k]'h').toInt
          else if prefix_max_int numbers k < (numbers.val[k]'h').toInt then
                  (numbers.val[k]'h').toInt
               else prefix_max_int numbers k
        else prefix_max_int numbers k)
      = _
  rw [dif_pos hk]
  have hk_ne : k ≠ 0 := by omega
  rw [if_neg hk_ne]

/-! ## Bool form helper

`(i ==? 0)` reduces to `pure (i == 0 : Bool)`, where `i == 0` is the `BEq`
instance on `USize64`. We bridge this to `decide (i.toNat = 0)`. -/

private theorem usize_beq_zero_eq (i : usize) :
    (i == (0 : usize)) = decide (i.toNat = 0) := by
  rw [show (i == (0 : usize)) = decide (i = 0) from rfl]
  by_cases h : i = 0
  · subst h; decide
  · have h_toNat : i.toNat ≠ 0 := by
      intro hn; exact h (USize64.toNat_inj.mp (by rw [hn]; rfl))
    rw [decide_eq_false h, decide_eq_false h_toNat]

/-! ## Step lemma for out-of-bounds branch. -/

private theorem rolling_max_at_oob
    (numbers : RustSlice i64) (i : usize) (max_so_far : i64)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : numbers.val.size ≤ i.toNat) :
    clever_009_rolling_max.rolling_max_at numbers i max_so_far acc = RustM.ok acc := by
  conv => lhs; unfold clever_009_rolling_max.rolling_max_at
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' numbers.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat numbers.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- Push a single element. -/
private def push_one (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec i64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

/-- Recursion step (matches the simp output's natural form). -/
private theorem rolling_max_at_step
    (numbers : RustSlice i64) (i : usize) (max_so_far : i64)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < numbers.val.size)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_009_rolling_max.rolling_max_at numbers i max_so_far acc =
      let new_max :=
        if ((i == (0 : usize)) ||
             decide (numbers.val[i.toNat]'hi > max_so_far)) = true
        then numbers.val[i.toNat]'hi else max_so_far
      clever_009_rolling_max.rolling_max_at numbers (i + 1) new_max
        (push_one acc new_max h_acc) := by
  conv => lhs; unfold clever_009_rolling_max.rolling_max_at
  have h_size_lt : numbers.val.size < USize64.size := numbers.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat numbers.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (numbers[i]_? : RustM i64) = RustM.ok (numbers.val[i.toNat]'hi) := by
    show (if h : i.toNat < numbers.val.size then pure (numbers.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (numbers.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
  have h_no_overflow : i.toNat + 1 < 2^64 := by
    have : numbers.val.size < 2^64 := by rw [h_usize_size] at h_size_lt; exact h_size_lt
    omega
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
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.cmp.eq, rust_primitives.cmp.gt,
             rust_primitives.hax.logical_op.or]
  -- Now the goal has the form:
  -- `if (i == 0 || decide (a > max_so_far)) = true then [taking_n] else [keeping_max]
  --   = rolling_max_at numbers (i+1) (if (i == 0 || decide(a > max)) then a else max_so_far) _`
  by_cases h_inner : ((i == (0 : usize)) ||
                       decide (numbers.val[i.toNat]'hi > max_so_far)) = true
  · -- Both `if`s take the first branch.
    rw [if_pos h_inner]
    rw [show (let new_max :=
                if ((i == (0 : usize)) ||
                     decide (numbers.val[i.toNat]'hi > max_so_far)) = true
                then numbers.val[i.toNat]'hi else max_so_far
              clever_009_rolling_max.rolling_max_at numbers (i + 1) new_max
                (push_one acc new_max h_acc)) =
              clever_009_rolling_max.rolling_max_at numbers (i + 1)
                (numbers.val[i.toNat]'hi)
                (push_one acc (numbers.val[i.toNat]'hi) h_acc) from by
            show clever_009_rolling_max.rolling_max_at numbers (i + 1)
                  (if ((i == (0 : usize)) || decide (numbers.val[i.toNat]'hi > max_so_far)) = true
                    then numbers.val[i.toNat]'hi else max_so_far)
                  (push_one acc
                    (if ((i == (0 : usize)) || decide (numbers.val[i.toNat]'hi > max_so_far)) = true
                      then numbers.val[i.toNat]'hi else max_so_far) h_acc) =
                clever_009_rolling_max.rolling_max_at numbers (i + 1)
                  (numbers.val[i.toNat]'hi)
                  (push_one acc (numbers.val[i.toNat]'hi) h_acc)
            rw [if_pos h_inner]]
    -- Reduce the remaining: unsize, extend, add.
    rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[numbers.val[i.toNat]'hi] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
            = RustM.ok ⟨#[numbers.val[i.toNat]'hi], one_lt_usize_size⟩ from rfl]
    simp only [RustM_ok_bind]
    have h_app_size :
        acc.val.size + (#[numbers.val[i.toNat]'hi] : Array i64).size < USize64.size := by
      show acc.val.size + 1 < USize64.size
      exact h_acc
    rw [show (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
                ⟨#[numbers.val[i.toNat]'hi], one_lt_usize_size⟩
              : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
          = RustM.ok (push_one acc (numbers.val[i.toNat]'hi) h_acc) from by
      unfold alloc.vec.Impl_2.extend_from_slice
      rw [dif_pos h_app_size]
      rfl]
    simp only [RustM_ok_bind]
    rw [h_add_eq]
    rfl
  · -- Else branch: cond is false.
    have h_inner_false :
        ((i == (0 : usize)) || decide (numbers.val[i.toNat]'hi > max_so_far)) = false := by
      cases hb : ((i == (0 : usize)) ||
                   decide (numbers.val[i.toNat]'hi > max_so_far)) with
      | true => exact absurd hb h_inner
      | false => rfl
    rw [if_neg (by rw [h_inner_false]; exact Bool.false_ne_true)]
    rw [show (let new_max :=
                if ((i == (0 : usize)) ||
                     decide (numbers.val[i.toNat]'hi > max_so_far)) = true
                then numbers.val[i.toNat]'hi else max_so_far
              clever_009_rolling_max.rolling_max_at numbers (i + 1) new_max
                (push_one acc new_max h_acc)) =
              clever_009_rolling_max.rolling_max_at numbers (i + 1) max_so_far
                (push_one acc max_so_far h_acc) from by
            show clever_009_rolling_max.rolling_max_at numbers (i + 1)
                  (if ((i == (0 : usize)) || decide (numbers.val[i.toNat]'hi > max_so_far)) = true
                    then numbers.val[i.toNat]'hi else max_so_far)
                  (push_one acc
                    (if ((i == (0 : usize)) || decide (numbers.val[i.toNat]'hi > max_so_far)) = true
                      then numbers.val[i.toNat]'hi else max_so_far) h_acc) =
                clever_009_rolling_max.rolling_max_at numbers (i + 1) max_so_far
                  (push_one acc max_so_far h_acc)
            rw [if_neg (by rw [h_inner_false]; exact Bool.false_ne_true)]]
    rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[max_so_far] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
            = RustM.ok ⟨#[max_so_far], one_lt_usize_size⟩ from rfl]
    simp only [RustM_ok_bind]
    have h_app_size :
        acc.val.size + (#[max_so_far] : Array i64).size < USize64.size := by
      show acc.val.size + 1 < USize64.size
      exact h_acc
    rw [show (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
                ⟨#[max_so_far], one_lt_usize_size⟩
              : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
          = RustM.ok (push_one acc max_so_far h_acc) from by
      unfold alloc.vec.Impl_2.extend_from_slice
      rw [dif_pos h_app_size]
      rfl]
    simp only [RustM_ok_bind]
    rw [h_add_eq]
    rfl

/-! ## Strong-induction lemma -/

private theorem rolling_max_at_correct (numbers : RustSlice i64) :
    ∀ (m : Nat) (i : usize) (max_so_far : i64)
      (acc : alloc.vec.Vec i64 alloc.alloc.Global),
      numbers.val.size - i.toNat ≤ m →
      i.toNat ≤ numbers.val.size →
      acc.val.size = i.toNat →
      (∀ (j : Nat) (hj : j < acc.val.size),
          (acc.val[j]'hj).toInt = prefix_max_int numbers (j + 1)) →
      (1 ≤ i.toNat → max_so_far.toInt = prefix_max_int numbers i.toNat) →
      ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
        clever_009_rolling_max.rolling_max_at numbers i max_so_far acc = RustM.ok v ∧
        v.val.size = numbers.val.size ∧
        ∀ (j : Nat) (hj : j < v.val.size),
          (v.val[j]'hj).toInt = prefix_max_int numbers (j + 1) := by
  intro m
  induction m with
  | zero =>
    intro i max_so_far acc hm hi_le h_acc_size h_acc_max h_max_inv
    have hi_eq : i.toNat = numbers.val.size := by omega
    have hi_ge : numbers.val.size ≤ i.toNat := by omega
    refine ⟨acc, rolling_max_at_oob numbers i max_so_far acc hi_ge, ?_, ?_⟩
    · rw [h_acc_size, hi_eq]
    · intro j hj; exact h_acc_max j hj
  | succ m ih =>
    intro i max_so_far acc hm hi_le h_acc_size h_acc_max h_max_inv
    by_cases hi_ge : numbers.val.size ≤ i.toNat
    · have hi_eq : i.toNat = numbers.val.size := by omega
      refine ⟨acc, rolling_max_at_oob numbers i max_so_far acc hi_ge, ?_, ?_⟩
      · rw [h_acc_size, hi_eq]
      · intro j hj; exact h_acc_max j hj
    · have hi_lt : i.toNat < numbers.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : numbers.val.size < USize64.size := numbers.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_acc_succ : acc.val.size + 1 < USize64.size := by
        rw [h_usize_size] at h_size_lt
        rw [h_acc_size, h_usize_size]
        omega
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      -- Apply the step lemma.
      have h_step := rolling_max_at_step numbers i max_so_far acc hi_lt h_acc_succ
      rw [h_step]
      -- Expose the `have new_max := ...; rolling_max_at ...` as a direct call.
      show ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
        clever_009_rolling_max.rolling_max_at numbers (i + 1)
          (if ((i == (0 : usize)) ||
                decide (numbers.val[i.toNat]'hi_lt > max_so_far)) = true
            then numbers.val[i.toNat]'hi_lt else max_so_far)
          (push_one acc
            (if ((i == (0 : usize)) ||
                  decide (numbers.val[i.toNat]'hi_lt > max_so_far)) = true
              then numbers.val[i.toNat]'hi_lt else max_so_far) h_acc_succ) = RustM.ok v ∧
          v.val.size = numbers.val.size ∧
          ∀ (j : Nat) (hj : j < v.val.size),
            (v.val[j]'hj).toInt = prefix_max_int numbers (j + 1)
      -- Prove the prefix-max invariant for new_max.
      have h_new_max_eq :
          (if ((i == (0 : usize)) ||
                decide (numbers.val[i.toNat]'hi_lt > max_so_far)) = true
            then numbers.val[i.toNat]'hi_lt else max_so_far).toInt =
            prefix_max_int numbers (i.toNat + 1) := by
        by_cases hi_zero : i.toNat = 0
        · -- i.toNat = 0 case: condition is true via i == 0.
          have h_i_eq : i = (0 : usize) := USize64.toNat_inj.mp hi_zero
          have h_beq_true : (i == (0 : usize)) = true := by
            rw [usize_beq_zero_eq]
            exact decide_eq_true hi_zero
          have h_cond_true :
              ((i == (0 : usize)) || decide (numbers.val[i.toNat]'hi_lt > max_so_far)) = true := by
            rw [h_beq_true]; rfl
          rw [if_pos h_cond_true]
          have h_zero_lt : 0 < numbers.val.size := by rw [← hi_zero]; exact hi_lt
          have h_succ_eq : i.toNat + 1 = 1 := by omega
          rw [h_succ_eq, prefix_max_int_one numbers h_zero_lt]
          -- We want: (numbers.val[i.toNat]'hi_lt).toInt = (numbers.val[0]'h_zero_lt).toInt
          -- Subst i = 0 to make this trivial.
          subst h_i_eq
          rfl
        · -- i.toNat ≠ 0 case
          have hi_pos : 1 ≤ i.toNat := Nat.one_le_iff_ne_zero.mpr hi_zero
          have h_max_inv' : max_so_far.toInt = prefix_max_int numbers i.toNat :=
            h_max_inv hi_pos
          have h_beq_false : (i == (0 : usize)) = false := by
            rw [usize_beq_zero_eq]
            exact decide_eq_false hi_zero
          rw [prefix_max_int_succ numbers i.toNat hi_lt hi_pos]
          by_cases h_gt : numbers.val[i.toNat]'hi_lt > max_so_far
          · have h_dec_true : decide (numbers.val[i.toNat]'hi_lt > max_so_far) = true :=
              decide_eq_true h_gt
            have h_cond_true :
                ((i == (0 : usize)) ||
                  decide (numbers.val[i.toNat]'hi_lt > max_so_far)) = true := by
              rw [h_beq_false, h_dec_true]; rfl
            rw [if_pos h_cond_true]
            have h_lt_int : max_so_far.toInt < (numbers.val[i.toNat]'hi_lt).toInt :=
              Int64.lt_iff_toInt_lt.mp h_gt
            rw [← h_max_inv']
            rw [if_pos h_lt_int]
          · have h_dec_false : decide (numbers.val[i.toNat]'hi_lt > max_so_far) = false :=
              decide_eq_false h_gt
            have h_cond_false :
                ((i == (0 : usize)) ||
                  decide (numbers.val[i.toNat]'hi_lt > max_so_far)) = false := by
              rw [h_beq_false, h_dec_false]; rfl
            rw [if_neg (by rw [h_cond_false]; exact Bool.false_ne_true)]
            have h_not_lt_int : ¬ max_so_far.toInt < (numbers.val[i.toNat]'hi_lt).toInt := by
              intro h
              exact h_gt (Int64.lt_iff_toInt_lt.mpr h)
            have h_le_int : (numbers.val[i.toNat]'hi_lt).toInt ≤ max_so_far.toInt := by
              omega
            rw [h_max_inv']
            have h_not_lt : ¬ prefix_max_int numbers i.toNat <
                              (numbers.val[i.toNat]'hi_lt).toInt := by
              rw [← h_max_inv']; omega
            rw [if_neg h_not_lt]
      -- Set up IH application.
      have h_i1_le : (i + 1).toNat ≤ numbers.val.size := by rw [h_i1]; omega
      have h_m_le : numbers.val.size - (i + 1).toNat ≤ m := by rw [h_i1]; omega
      have h_acc'_size :
          (push_one acc
            (if ((i == (0 : usize)) ||
                  decide (numbers.val[i.toNat]'hi_lt > max_so_far)) = true
              then numbers.val[i.toNat]'hi_lt else max_so_far) h_acc_succ).val.size =
            (i + 1).toNat := by
        show (acc.val ++ _).size = (i + 1).toNat
        rw [Array.size_append, h_i1]
        show acc.val.size + 1 = i.toNat + 1
        rw [h_acc_size]
      have h_acc'_max :
          ∀ (j : Nat) (hj : j <
            (push_one acc
              (if ((i == (0 : usize)) ||
                    decide (numbers.val[i.toNat]'hi_lt > max_so_far)) = true
                then numbers.val[i.toNat]'hi_lt else max_so_far) h_acc_succ).val.size),
            ((push_one acc
              (if ((i == (0 : usize)) ||
                    decide (numbers.val[i.toNat]'hi_lt > max_so_far)) = true
                then numbers.val[i.toNat]'hi_lt else max_so_far) h_acc_succ).val[j]'hj).toInt =
              prefix_max_int numbers (j + 1) := by
        intro j hj
        show ((acc.val ++ #[_])[j]'hj).toInt = _
        by_cases hjlt : j < acc.val.size
        · rw [Array.getElem_append_left hjlt]
          exact h_acc_max j hjlt
        · have h_size_raw : (acc.val ++ #[
              (if ((i == (0 : usize)) ||
                    decide (numbers.val[i.toNat]'hi_lt > max_so_far)) = true
                then numbers.val[i.toNat]'hi_lt else max_so_far)]).size =
              acc.val.size + 1 := by
            rw [Array.size_append]; rfl
          have hj_eq : j = acc.val.size := by
            have : j < acc.val.size + 1 := by rw [← h_size_raw]; exact hj
            omega
          subst hj_eq
          rw [Array.getElem_append_right (Nat.le_refl _)]
          simp only [Nat.sub_self]
          show ((#[_] : Array i64)[0]).toInt = _
          rw [h_acc_size]
          exact h_new_max_eq
      have h_new_max_inv :
          1 ≤ (i + 1).toNat →
            (if ((i == (0 : usize)) ||
                  decide (numbers.val[i.toNat]'hi_lt > max_so_far)) = true
              then numbers.val[i.toNat]'hi_lt else max_so_far).toInt =
              prefix_max_int numbers (i + 1).toNat := by
        intro _; rw [h_i1]; exact h_new_max_eq
      exact ih (i + 1) _ _ h_m_le h_i1_le h_acc'_size h_acc'_max h_new_max_inv

/-! ## Top-level theorems -/

private theorem rolling_max_aux (numbers : RustSlice i64) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_009_rolling_max.rolling_max numbers = RustM.ok v ∧
      v.val.size = numbers.val.size ∧
      ∀ (j : Nat) (hj : j < v.val.size),
        (v.val[j]'hj).toInt = prefix_max_int numbers (j + 1) := by
  unfold clever_009_rolling_max.rolling_max
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new, RustM_ok_bind]
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  let acc0 : alloc.vec.Vec i64 alloc.alloc.Global := ⟨(List.nil).toArray, by grind⟩
  have h_acc0_size : acc0.val.size = (0 : usize).toNat := by
    show (List.nil : List i64).toArray.size = 0
    rfl
  have h_acc0_max : ∀ (j : Nat) (hj : j < acc0.val.size),
      (acc0.val[j]'hj).toInt = prefix_max_int numbers (j + 1) := by
    intro j hj
    exfalso
    have h0 : acc0.val.size = 0 := by show (List.nil : List i64).toArray.size = 0; rfl
    rw [h0] at hj
    omega
  have h_max_inv : 1 ≤ (0 : usize).toNat →
                    (0 : i64).toInt = prefix_max_int numbers (0 : usize).toNat := by
    intro h; rw [h_zero_toNat] at h; omega
  have h_m_le : numbers.val.size - (0 : usize).toNat ≤ numbers.val.size := by
    rw [h_zero_toNat]; omega
  have h_i_le : (0 : usize).toNat ≤ numbers.val.size := by
    rw [h_zero_toNat]; omega
  exact rolling_max_at_correct numbers numbers.val.size (0 : usize) (0 : i64) acc0
          h_m_le h_i_le h_acc0_size h_acc0_max h_max_inv

theorem rolling_max_total
    (numbers : RustSlice i64) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_009_rolling_max.rolling_max numbers = RustM.ok v := by
  obtain ⟨v, hres, _, _⟩ := rolling_max_aux numbers
  exact ⟨v, hres⟩

theorem rolling_max_empty
    (numbers : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_009_rolling_max.rolling_max numbers = RustM.ok v)
    (hempty : numbers.val.size = 0) :
    v.val.size = 0 := by
  obtain ⟨v', hres', hlen, _⟩ := rolling_max_aux numbers
  rw [hres'] at hres
  injection hres with h_eq
  injection h_eq with h_eq'
  subst h_eq'
  rw [hlen, hempty]

theorem rolling_max_length
    (numbers : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_009_rolling_max.rolling_max numbers = RustM.ok v) :
    v.val.size = numbers.val.size := by
  obtain ⟨v', hres', hlen, _⟩ := rolling_max_aux numbers
  rw [hres'] at hres
  injection hres with h_eq
  injection h_eq with h_eq'
  subst h_eq'
  exact hlen

theorem rolling_max_prefix_max
    (numbers : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_009_rolling_max.rolling_max numbers = RustM.ok v)
    (i : Nat) (hi : i < numbers.val.size) (hi' : i < v.val.size) :
    (v.val[i]'hi').toInt = prefix_max_int numbers (i + 1) := by
  obtain ⟨v', hres', hlen, hprop⟩ := rolling_max_aux numbers
  rw [hres'] at hres
  injection hres with h_eq
  injection h_eq with h_eq'
  subst h_eq'
  exact hprop i hi'

end Clever_009_rolling_maxObligations
