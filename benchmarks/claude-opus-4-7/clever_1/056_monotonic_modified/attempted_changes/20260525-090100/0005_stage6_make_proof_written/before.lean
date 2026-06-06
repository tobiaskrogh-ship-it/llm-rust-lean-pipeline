-- Companion obligations file for the `clever_050_monotonic` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_050_monotonic

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_050_monotonicObligations

/-! ## Specification: pairwise predicates on the underlying `i64` list. -/

/-- All adjacent pairs of `l` are non-decreasing. -/
private def is_nondec (l : RustSlice i64) : Prop :=
  ∀ j : Nat, ∀ (hj1 : j + 1 < l.val.size),
    l.val[j]'(Nat.lt_of_succ_lt hj1) ≤ l.val[j+1]'hj1

/-- All adjacent pairs of `l` are non-increasing. -/
private def is_noninc (l : RustSlice i64) : Prop :=
  ∀ j : Nat, ∀ (hj1 : j + 1 < l.val.size),
    l.val[j+1]'hj1 ≤ l.val[j]'(Nat.lt_of_succ_lt hj1)

/-! ## Numeric helpers -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem u64_zero_toNat : (0 : u64).toNat = 0 := rfl
private theorem u64_one_toNat : (1 : u64).toNat = 1 := rfl

private theorem u64_toUSize64_toNat (i : u64) : (UInt64.toUSize64 i).toNat = i.toNat := by
  show (USize64.ofNat i.toNat).toNat = i.toNat
  exact USize64.toNat_ofNat_of_lt' i.toNat_lt

private theorem usize_toUInt64_toNat_of_lt (x : usize) (h : x.toNat < 2^64) :
    (USize64.toUInt64 x).toNat = x.toNat := by
  show (Nat.toUInt64 x.toNat).toNat = x.toNat
  exact UInt64.toNat_ofNat_of_lt h

private theorem u64_add_one_toNat (i : u64) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h' : i.toNat + (1 : u64).toNat < 2^64 := by rw [u64_one_toNat]; exact h
  rw [UInt64.toNat_add_of_lt h', u64_one_toNat]

private theorem u64_add_one_no_bv (i : u64) (h : i.toNat + 1 < 2^64) :
    BitVec.uaddOverflow i.toBitVec (1 : u64).toBitVec = false := by
  generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : u64).toBitVec = bo
  cases bo with
  | false => rfl
  | true =>
    exfalso
    have h1 : UInt64.addOverflow i 1 = true := hbo
    rw [UInt64.addOverflow_iff] at h1
    rw [u64_one_toNat] at h1
    omega

/-- `(i +? 1 : RustM u64) = pure (i + 1)` when `i.toNat + 1 < 2^64`. -/
private theorem u64_add_one_pure (i : u64) (h : i.toNat + 1 < 2^64) :
    (i +? (1 : u64) : RustM u64) = pure (i + 1) := by
  show (rust_primitives.ops.arith.Add.add i 1 : RustM u64) = pure (i + 1)
  show (if BitVec.uaddOverflow i.toBitVec (1 : u64).toBitVec
        then (.fail .integerOverflow : RustM u64)
        else pure (i + 1)) = _
  rw [u64_add_one_no_bv i h]
  rfl

/-! ## Step lemmas for `is_nondecreasing_from`. -/

/-- Out-of-bounds step: when `i + 1 ≥ l.val.size` (and `i + 1` does not overflow),
    the function returns `RustM.ok true`. -/
private theorem is_nondecreasing_from_oob (l : RustSlice i64) (i : u64)
    (hi_add : i.toNat + 1 < 2^64)
    (hi_ge : l.val.size ≤ i.toNat + 1) :
    clever_050_monotonic.is_nondecreasing_from l i = RustM.ok true := by
  conv => lhs; unfold clever_050_monotonic.is_nondecreasing_from
  have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
  -- `core_models.slice.Impl.len i64 l = pure (USize64.ofNat l.val.size)`
  have h_len : (core_models.slice.Impl.len i64 l : RustM usize)
      = pure (USize64.ofNat l.val.size) := rfl
  -- `cast_op ... : RustM u64 = pure (USize64.toUInt64 ...)`
  have h_cast_n : ∀ x : usize,
      (rust_primitives.hax.cast_op x : RustM u64) = pure (USize64.toUInt64 x) := by
    intro x; rfl
  -- The computed `n` value:
  set n_val : u64 := USize64.toUInt64 (USize64.ofNat l.val.size) with hn_def
  have hn_toNat : n_val.toNat = l.val.size := by
    rw [hn_def]
    show (Nat.toUInt64 (USize64.ofNat l.val.size).toNat).toNat = l.val.size
    rw [USize64.toNat_ofNat_of_lt' h_size_lt]
    exact UInt64.toNat_ofNat_of_lt h_size_lt
  -- `i +? 1 = pure (i + 1)`
  have h_add : (i +? (1 : u64) : RustM u64) = pure (i + 1) := u64_add_one_pure i hi_add
  have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := u64_add_one_toNat i hi_add
  -- Condition `(i+1) >=? n_val` is true.
  have h_cond : decide ((i + 1) >= n_val) = true := by
    rw [decide_eq_true_iff]
    rw [UInt64.le_iff_toNat_le, hn_toNat, h_i1_toNat]
    exact hi_ge
  rw [h_len]
  simp only [pure_bind]
  rw [h_cast_n]
  simp only [pure_bind]
  rw [h_add]
  simp only [pure_bind]
  show (((i + 1) >=? n_val : RustM Bool) >>= _) = _
  rw [show ((i + 1) >=? n_val : RustM Bool) = pure (decide ((i + 1) >= n_val)) from rfl]
  simp only [pure_bind]
  rw [h_cond]
  rfl

/-- Violation step: when `i + 1 < l.val.size` and `l[i] > l[i+1]`, returns `ok false`. -/
private theorem is_nondecreasing_from_violation (l : RustSlice i64) (i : u64)
    (hi1 : i.toNat + 1 < l.val.size)
    (h_gt : l.val[i.toNat]'(Nat.lt_of_succ_lt hi1) > l.val[i.toNat + 1]'hi1) :
    clever_050_monotonic.is_nondecreasing_from l i = RustM.ok false := by
  conv => lhs; unfold clever_050_monotonic.is_nondecreasing_from
  have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
  have hi_add : i.toNat + 1 < 2^64 := Nat.lt_trans hi1 h_size_lt
  have h_len : (core_models.slice.Impl.len i64 l : RustM usize)
      = pure (USize64.ofNat l.val.size) := rfl
  have h_cast_n : ∀ x : usize,
      (rust_primitives.hax.cast_op x : RustM u64) = pure (USize64.toUInt64 x) := by
    intro x; rfl
  have h_cast_u : ∀ x : u64,
      (rust_primitives.hax.cast_op x : RustM usize) = pure (UInt64.toUSize64 x) := by
    intro x; rfl
  set n_val : u64 := USize64.toUInt64 (USize64.ofNat l.val.size) with hn_def
  have hn_toNat : n_val.toNat = l.val.size := by
    rw [hn_def]
    show (Nat.toUInt64 (USize64.ofNat l.val.size).toNat).toNat = l.val.size
    rw [USize64.toNat_ofNat_of_lt' h_size_lt]
    exact UInt64.toNat_ofNat_of_lt h_size_lt
  have h_add : (i +? (1 : u64) : RustM u64) = pure (i + 1) := u64_add_one_pure i hi_add
  have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := u64_add_one_toNat i hi_add
  have h_cond_ge : decide ((i + 1) >= n_val) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [UInt64.le_iff_toNat_le, hn_toNat, h_i1_toNat] at hle
    omega
  -- Indexing equations.
  have h_iu_toNat : (UInt64.toUSize64 i).toNat = i.toNat := u64_toUSize64_toNat i
  have h_i1u_toNat : (UInt64.toUSize64 (i + 1)).toNat = i.toNat + 1 := by
    rw [u64_toUSize64_toNat]; exact h_i1_toNat
  have h_idx_i_lt : (UInt64.toUSize64 i).toNat < l.val.size := by
    rw [h_iu_toNat]; omega
  have h_idx_i1_lt : (UInt64.toUSize64 (i + 1)).toNat < l.val.size := by
    rw [h_i1u_toNat]; exact hi1
  have h_idx_i :
      (l[UInt64.toUSize64 i]_? : RustM i64) = RustM.ok (l.val[(UInt64.toUSize64 i).toNat]'h_idx_i_lt) := by
    show (if h : (UInt64.toUSize64 i).toNat < l.val.size then pure (l.val[UInt64.toUSize64 i])
            else .fail .arrayOutOfBounds)
        = _
    rw [dif_pos h_idx_i_lt]; rfl
  have h_idx_i1 :
      (l[UInt64.toUSize64 (i + 1)]_? : RustM i64) =
        RustM.ok (l.val[(UInt64.toUSize64 (i + 1)).toNat]'h_idx_i1_lt) := by
    show (if h : (UInt64.toUSize64 (i + 1)).toNat < l.val.size then pure (l.val[UInt64.toUSize64 (i + 1)])
            else .fail .arrayOutOfBounds)
        = _
    rw [dif_pos h_idx_i1_lt]; rfl
  have h_a_eq : l.val[(UInt64.toUSize64 i).toNat]'h_idx_i_lt =
      l.val[i.toNat]'(Nat.lt_of_succ_lt hi1) := by
    congr 1; exact h_iu_toNat
  have h_b_eq : l.val[(UInt64.toUSize64 (i + 1)).toNat]'h_idx_i1_lt =
      l.val[i.toNat + 1]'hi1 := by
    congr 1; exact h_i1u_toNat
  have h_gt_cond : decide
      (l.val[(UInt64.toUSize64 i).toNat]'h_idx_i_lt >
       l.val[(UInt64.toUSize64 (i + 1)).toNat]'h_idx_i1_lt) = true := by
    rw [decide_eq_true_iff]
    rw [h_a_eq, h_b_eq]
    exact h_gt
  rw [h_len]
  simp only [pure_bind]
  rw [h_cast_n]
  simp only [pure_bind]
  rw [h_add]
  simp only [pure_bind]
  show (((i + 1) >=? n_val : RustM Bool) >>= _) = _
  rw [show ((i + 1) >=? n_val : RustM Bool) = pure (decide ((i + 1) >= n_val)) from rfl]
  simp only [pure_bind]
  rw [h_cond_ge]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [h_cast_u i]
  simp only [pure_bind]
  rw [h_idx_i]
  simp only [RustM_ok_bind]
  rw [h_add]
  simp only [pure_bind]
  rw [h_cast_u (i + 1)]
  simp only [pure_bind]
  rw [h_idx_i1]
  simp only [RustM_ok_bind]
  show ((_ >? _ : RustM Bool) >>= _) = _
  rw [show ((l.val[(UInt64.toUSize64 i).toNat]'h_idx_i_lt >?
              l.val[(UInt64.toUSize64 (i + 1)).toNat]'h_idx_i1_lt : RustM Bool) =
            pure (decide
              (l.val[(UInt64.toUSize64 i).toNat]'h_idx_i_lt >
               l.val[(UInt64.toUSize64 (i + 1)).toNat]'h_idx_i1_lt)) from rfl]
  simp only [pure_bind]
  rw [h_gt_cond]
  rfl

/-- Recursion step: when `i + 1 < l.val.size` and `l[i] ≤ l[i+1]`, recurse with `i+1`. -/
private theorem is_nondecreasing_from_recurse (l : RustSlice i64) (i : u64)
    (hi1 : i.toNat + 1 < l.val.size)
    (h_le : l.val[i.toNat]'(Nat.lt_of_succ_lt hi1) ≤ l.val[i.toNat + 1]'hi1) :
    clever_050_monotonic.is_nondecreasing_from l i =
      clever_050_monotonic.is_nondecreasing_from l (i + 1) := by
  conv => lhs; unfold clever_050_monotonic.is_nondecreasing_from
  have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
  have hi_add : i.toNat + 1 < 2^64 := Nat.lt_trans hi1 h_size_lt
  have h_len : (core_models.slice.Impl.len i64 l : RustM usize)
      = pure (USize64.ofNat l.val.size) := rfl
  have h_cast_n : ∀ x : usize,
      (rust_primitives.hax.cast_op x : RustM u64) = pure (USize64.toUInt64 x) := by
    intro x; rfl
  have h_cast_u : ∀ x : u64,
      (rust_primitives.hax.cast_op x : RustM usize) = pure (UInt64.toUSize64 x) := by
    intro x; rfl
  set n_val : u64 := USize64.toUInt64 (USize64.ofNat l.val.size) with hn_def
  have hn_toNat : n_val.toNat = l.val.size := by
    rw [hn_def]
    show (Nat.toUInt64 (USize64.ofNat l.val.size).toNat).toNat = l.val.size
    rw [USize64.toNat_ofNat_of_lt' h_size_lt]
    exact UInt64.toNat_ofNat_of_lt h_size_lt
  have h_add : (i +? (1 : u64) : RustM u64) = pure (i + 1) := u64_add_one_pure i hi_add
  have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := u64_add_one_toNat i hi_add
  have h_cond_ge : decide ((i + 1) >= n_val) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [UInt64.le_iff_toNat_le, hn_toNat, h_i1_toNat] at hle
    omega
  have h_iu_toNat : (UInt64.toUSize64 i).toNat = i.toNat := u64_toUSize64_toNat i
  have h_i1u_toNat : (UInt64.toUSize64 (i + 1)).toNat = i.toNat + 1 := by
    rw [u64_toUSize64_toNat]; exact h_i1_toNat
  have h_idx_i_lt : (UInt64.toUSize64 i).toNat < l.val.size := by
    rw [h_iu_toNat]; omega
  have h_idx_i1_lt : (UInt64.toUSize64 (i + 1)).toNat < l.val.size := by
    rw [h_i1u_toNat]; exact hi1
  have h_idx_i :
      (l[UInt64.toUSize64 i]_? : RustM i64) = RustM.ok (l.val[(UInt64.toUSize64 i).toNat]'h_idx_i_lt) := by
    show (if h : (UInt64.toUSize64 i).toNat < l.val.size then pure (l.val[UInt64.toUSize64 i])
            else .fail .arrayOutOfBounds)
        = _
    rw [dif_pos h_idx_i_lt]; rfl
  have h_idx_i1 :
      (l[UInt64.toUSize64 (i + 1)]_? : RustM i64) =
        RustM.ok (l.val[(UInt64.toUSize64 (i + 1)).toNat]'h_idx_i1_lt) := by
    show (if h : (UInt64.toUSize64 (i + 1)).toNat < l.val.size then pure (l.val[UInt64.toUSize64 (i + 1)])
            else .fail .arrayOutOfBounds)
        = _
    rw [dif_pos h_idx_i1_lt]; rfl
  have h_a_eq : l.val[(UInt64.toUSize64 i).toNat]'h_idx_i_lt =
      l.val[i.toNat]'(Nat.lt_of_succ_lt hi1) := by
    congr 1; exact h_iu_toNat
  have h_b_eq : l.val[(UInt64.toUSize64 (i + 1)).toNat]'h_idx_i1_lt =
      l.val[i.toNat + 1]'hi1 := by
    congr 1; exact h_i1u_toNat
  have h_gt_cond : decide
      (l.val[(UInt64.toUSize64 i).toNat]'h_idx_i_lt >
       l.val[(UInt64.toUSize64 (i + 1)).toNat]'h_idx_i1_lt) = false := by
    rw [decide_eq_false_iff_not]
    intro h_gt
    rw [h_a_eq, h_b_eq] at h_gt
    have h_lt : l.val[i.toNat + 1]'hi1 < l.val[i.toNat]'(Nat.lt_of_succ_lt hi1) := h_gt
    -- h_le says first ≤ second, h_lt says second < first.
    exact absurd h_le (Int64.not_le.mpr h_lt)
  rw [h_len]
  simp only [pure_bind]
  rw [h_cast_n]
  simp only [pure_bind]
  rw [h_add]
  simp only [pure_bind]
  show (((i + 1) >=? n_val : RustM Bool) >>= _) = _
  rw [show ((i + 1) >=? n_val : RustM Bool) = pure (decide ((i + 1) >= n_val)) from rfl]
  simp only [pure_bind]
  rw [h_cond_ge]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [h_cast_u i]
  simp only [pure_bind]
  rw [h_idx_i]
  simp only [RustM_ok_bind]
  rw [h_add]
  simp only [pure_bind]
  rw [h_cast_u (i + 1)]
  simp only [pure_bind]
  rw [h_idx_i1]
  simp only [RustM_ok_bind]
  show ((_ >? _ : RustM Bool) >>= _) = _
  rw [show ((l.val[(UInt64.toUSize64 i).toNat]'h_idx_i_lt >?
              l.val[(UInt64.toUSize64 (i + 1)).toNat]'h_idx_i1_lt : RustM Bool) =
            pure (decide
              (l.val[(UInt64.toUSize64 i).toNat]'h_idx_i_lt >
               l.val[(UInt64.toUSize64 (i + 1)).toNat]'h_idx_i1_lt)) from rfl]
  simp only [pure_bind]
  rw [h_gt_cond]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [h_add]
  simp only [pure_bind]

/-! ## Boundary clause: lists of length 0 or 1 are vacuously monotonic. -/

theorem monotonic_small_lists (l : RustSlice i64) (h : l.val.size ≤ 1) :
    clever_050_monotonic.monotonic l = RustM.ok true := by
  sorry

theorem monotonic_returns_true (l : RustSlice i64) (h : is_nondec l ∨ is_noninc l) :
    clever_050_monotonic.monotonic l = RustM.ok true := by
  sorry

theorem monotonic_returns_false (l : RustSlice i64)
    (h : ¬ is_nondec l ∧ ¬ is_noninc l) :
    clever_050_monotonic.monotonic l = RustM.ok false := by
  sorry

theorem monotonic_constant (l : RustSlice i64) (c : i64)
    (hconst : ∀ i : Nat, ∀ (hi : i < l.val.size), l.val[i]'hi = c) :
    clever_050_monotonic.monotonic l = RustM.ok true := by
  sorry

end Clever_050_monotonicObligations
