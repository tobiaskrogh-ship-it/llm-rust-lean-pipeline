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

private def is_nondec (l : RustSlice i64) : Prop :=
  ∀ j : Nat, ∀ (hj1 : j + 1 < l.val.size),
    l.val[j]'(Nat.lt_of_succ_lt hj1) ≤ l.val[j+1]'hj1

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
private theorem add_one_pure_u64 (i : u64) (h : i.toNat + 1 < 2^64) :
    (i +? (1 : u64) : RustM u64) = pure (i + 1) := by
  show (rust_primitives.ops.arith.Add.add i 1 : RustM u64) = pure (i + 1)
  show (if BitVec.uaddOverflow i.toBitVec (1 : u64).toBitVec
        then (.fail .integerOverflow : RustM u64)
        else pure (i + 1)) = _
  rw [u64_add_one_no_bv i h]
  rfl

private theorem n_val_toNat (l : RustSlice i64) :
    ((USize64.ofNat l.val.size).toUInt64).toNat = l.val.size := by
  have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
  show (Nat.toUInt64 (USize64.ofNat l.val.size).toNat).toNat = l.val.size
  rw [USize64.toNat_ofNat_of_lt' h_size_lt]
  exact UInt64.toNat_ofNat_of_lt h_size_lt

private theorem slice_idx_ok (l : RustSlice i64) (i : usize)
    (hi : i.toNat < l.val.size) :
    (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi) := by
  show (if h : i.toNat < l.val.size then (pure (l.val[i]) : RustM i64)
        else RustM.fail Error.arrayOutOfBounds) = RustM.ok (l.val[i.toNat]'hi)
  rw [dif_pos hi]; rfl

/-! ## Step lemmas for `is_nondecreasing_from`. -/

private theorem is_nondecreasing_from_oob (l : RustSlice i64) (i : u64)
    (hi_add : i.toNat + 1 < 2^64)
    (hi_ge : l.val.size ≤ i.toNat + 1) :
    clever_050_monotonic.is_nondecreasing_from l i = RustM.ok true := by
  conv => lhs; unfold clever_050_monotonic.is_nondecreasing_from
  have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
  have hn_toNat : ((USize64.ofNat l.val.size).toUInt64).toNat = l.val.size := n_val_toNat l
  have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := u64_add_one_toNat i hi_add
  have h_add : (i +? (1 : u64) : RustM u64) = pure (i + 1) := add_one_pure_u64 i hi_add
  have h_cond : decide ((i + 1) ≥ (USize64.ofNat l.val.size).toUInt64) = true := by
    rw [decide_eq_true_iff]
    change ((USize64.ofNat l.val.size).toUInt64) ≤ (i + 1)
    rw [UInt64.le_iff_toNat_le, hn_toNat, h_i1_toNat]
    exact hi_ge
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.hax.cast_op, Cast.cast,
             h_add, rust_primitives.cmp.ge,
             pure_bind, RustM_ok_bind, h_cond, ↓reduceIte]
  rfl

private theorem is_nondecreasing_from_violation (l : RustSlice i64) (i : u64)
    (hi1 : i.toNat + 1 < l.val.size)
    (h_gt : l.val[i.toNat]'(Nat.lt_of_succ_lt hi1) > l.val[i.toNat + 1]'hi1) :
    clever_050_monotonic.is_nondecreasing_from l i = RustM.ok false := by
  conv => lhs; unfold clever_050_monotonic.is_nondecreasing_from
  have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
  have hi_add : i.toNat + 1 < 2^64 := Nat.lt_trans hi1 h_size_lt
  have hn_toNat : ((USize64.ofNat l.val.size).toUInt64).toNat = l.val.size := n_val_toNat l
  have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := u64_add_one_toNat i hi_add
  have h_add : (i +? (1 : u64) : RustM u64) = pure (i + 1) := add_one_pure_u64 i hi_add
  have h_cond_ge : decide ((i + 1) ≥ (USize64.ofNat l.val.size).toUInt64) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    change ((USize64.ofNat l.val.size).toUInt64) ≤ (i + 1) at hle
    rw [UInt64.le_iff_toNat_le, hn_toNat, h_i1_toNat] at hle
    omega
  have h_iu_toNat : (UInt64.toUSize64 i).toNat = i.toNat := u64_toUSize64_toNat i
  have h_i1u_toNat : (UInt64.toUSize64 (i + 1)).toNat = i.toNat + 1 := by
    rw [u64_toUSize64_toNat]; exact h_i1_toNat
  have h_idx_i_lt : (UInt64.toUSize64 i).toNat < l.val.size := by
    rw [h_iu_toNat]; omega
  have h_idx_i1_lt : (UInt64.toUSize64 (i + 1)).toNat < l.val.size := by
    rw [h_i1u_toNat]; exact hi1
  have h_idx_i := slice_idx_ok l (UInt64.toUSize64 i) h_idx_i_lt
  have h_idx_i1 := slice_idx_ok l (UInt64.toUSize64 (i + 1)) h_idx_i1_lt
  have h_a_eq : l.val[(UInt64.toUSize64 i).toNat]'h_idx_i_lt =
      l.val[i.toNat]'(Nat.lt_of_succ_lt hi1) := by congr 1
  have h_b_eq : l.val[(UInt64.toUSize64 (i + 1)).toNat]'h_idx_i1_lt =
      l.val[i.toNat + 1]'hi1 := by congr 1
  have h_gt_cond :
      decide (l.val[(UInt64.toUSize64 i).toNat]'h_idx_i_lt >
              l.val[(UInt64.toUSize64 (i + 1)).toNat]'h_idx_i1_lt) = true := by
    rw [decide_eq_true_iff, h_a_eq, h_b_eq]; exact h_gt
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.hax.cast_op, Cast.cast,
             h_add, rust_primitives.cmp.ge, rust_primitives.cmp.gt,
             pure_bind, RustM_ok_bind, h_cond_ge, Bool.false_eq_true, ↓reduceIte,
             h_idx_i, h_idx_i1, h_gt_cond]
  rfl

private theorem is_nondecreasing_from_recurse (l : RustSlice i64) (i : u64)
    (hi1 : i.toNat + 1 < l.val.size)
    (h_le : l.val[i.toNat]'(Nat.lt_of_succ_lt hi1) ≤ l.val[i.toNat + 1]'hi1) :
    clever_050_monotonic.is_nondecreasing_from l i =
      clever_050_monotonic.is_nondecreasing_from l (i + 1) := by
  conv => lhs; unfold clever_050_monotonic.is_nondecreasing_from
  have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
  have hi_add : i.toNat + 1 < 2^64 := Nat.lt_trans hi1 h_size_lt
  have hn_toNat : ((USize64.ofNat l.val.size).toUInt64).toNat = l.val.size := n_val_toNat l
  have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := u64_add_one_toNat i hi_add
  have h_add : (i +? (1 : u64) : RustM u64) = pure (i + 1) := add_one_pure_u64 i hi_add
  have h_cond_ge : decide ((i + 1) ≥ (USize64.ofNat l.val.size).toUInt64) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    change ((USize64.ofNat l.val.size).toUInt64) ≤ (i + 1) at hle
    rw [UInt64.le_iff_toNat_le, hn_toNat, h_i1_toNat] at hle
    omega
  have h_iu_toNat : (UInt64.toUSize64 i).toNat = i.toNat := u64_toUSize64_toNat i
  have h_i1u_toNat : (UInt64.toUSize64 (i + 1)).toNat = i.toNat + 1 := by
    rw [u64_toUSize64_toNat]; exact h_i1_toNat
  have h_idx_i_lt : (UInt64.toUSize64 i).toNat < l.val.size := by
    rw [h_iu_toNat]; omega
  have h_idx_i1_lt : (UInt64.toUSize64 (i + 1)).toNat < l.val.size := by
    rw [h_i1u_toNat]; exact hi1
  have h_idx_i := slice_idx_ok l (UInt64.toUSize64 i) h_idx_i_lt
  have h_idx_i1 := slice_idx_ok l (UInt64.toUSize64 (i + 1)) h_idx_i1_lt
  have h_a_eq : l.val[(UInt64.toUSize64 i).toNat]'h_idx_i_lt =
      l.val[i.toNat]'(Nat.lt_of_succ_lt hi1) := by congr 1
  have h_b_eq : l.val[(UInt64.toUSize64 (i + 1)).toNat]'h_idx_i1_lt =
      l.val[i.toNat + 1]'hi1 := by congr 1
  have h_gt_cond :
      decide (l.val[(UInt64.toUSize64 i).toNat]'h_idx_i_lt >
              l.val[(UInt64.toUSize64 (i + 1)).toNat]'h_idx_i1_lt) = false := by
    rw [decide_eq_false_iff_not]
    intro h_gt
    rw [h_a_eq, h_b_eq] at h_gt
    have h_le_int : (l.val[i.toNat]'(Nat.lt_of_succ_lt hi1)).toInt ≤
                    (l.val[i.toNat + 1]'hi1).toInt := Int64.le_iff_toInt_le.mp h_le
    have h_lt_int : (l.val[i.toNat + 1]'hi1).toInt <
                    (l.val[i.toNat]'(Nat.lt_of_succ_lt hi1)).toInt :=
      Int64.lt_iff_toInt_lt.mp h_gt
    omega
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.hax.cast_op, Cast.cast,
             h_add, rust_primitives.cmp.ge, rust_primitives.cmp.gt,
             pure_bind, RustM_ok_bind, h_cond_ge, Bool.false_eq_true, ↓reduceIte,
             h_idx_i, h_idx_i1, h_gt_cond]

/-! ## Step lemmas for `is_nonincreasing_from`. -/

private theorem is_nonincreasing_from_oob (l : RustSlice i64) (i : u64)
    (hi_add : i.toNat + 1 < 2^64)
    (hi_ge : l.val.size ≤ i.toNat + 1) :
    clever_050_monotonic.is_nonincreasing_from l i = RustM.ok true := by
  conv => lhs; unfold clever_050_monotonic.is_nonincreasing_from
  have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
  have hn_toNat : ((USize64.ofNat l.val.size).toUInt64).toNat = l.val.size := n_val_toNat l
  have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := u64_add_one_toNat i hi_add
  have h_add : (i +? (1 : u64) : RustM u64) = pure (i + 1) := add_one_pure_u64 i hi_add
  have h_cond : decide ((i + 1) ≥ (USize64.ofNat l.val.size).toUInt64) = true := by
    rw [decide_eq_true_iff]
    change ((USize64.ofNat l.val.size).toUInt64) ≤ (i + 1)
    rw [UInt64.le_iff_toNat_le, hn_toNat, h_i1_toNat]
    exact hi_ge
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.hax.cast_op, Cast.cast,
             h_add, rust_primitives.cmp.ge,
             pure_bind, RustM_ok_bind, h_cond, ↓reduceIte]
  rfl

private theorem is_nonincreasing_from_violation (l : RustSlice i64) (i : u64)
    (hi1 : i.toNat + 1 < l.val.size)
    (h_lt : l.val[i.toNat]'(Nat.lt_of_succ_lt hi1) < l.val[i.toNat + 1]'hi1) :
    clever_050_monotonic.is_nonincreasing_from l i = RustM.ok false := by
  conv => lhs; unfold clever_050_monotonic.is_nonincreasing_from
  have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
  have hi_add : i.toNat + 1 < 2^64 := Nat.lt_trans hi1 h_size_lt
  have hn_toNat : ((USize64.ofNat l.val.size).toUInt64).toNat = l.val.size := n_val_toNat l
  have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := u64_add_one_toNat i hi_add
  have h_add : (i +? (1 : u64) : RustM u64) = pure (i + 1) := add_one_pure_u64 i hi_add
  have h_cond_ge : decide ((i + 1) ≥ (USize64.ofNat l.val.size).toUInt64) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    change ((USize64.ofNat l.val.size).toUInt64) ≤ (i + 1) at hle
    rw [UInt64.le_iff_toNat_le, hn_toNat, h_i1_toNat] at hle
    omega
  have h_iu_toNat : (UInt64.toUSize64 i).toNat = i.toNat := u64_toUSize64_toNat i
  have h_i1u_toNat : (UInt64.toUSize64 (i + 1)).toNat = i.toNat + 1 := by
    rw [u64_toUSize64_toNat]; exact h_i1_toNat
  have h_idx_i_lt : (UInt64.toUSize64 i).toNat < l.val.size := by
    rw [h_iu_toNat]; omega
  have h_idx_i1_lt : (UInt64.toUSize64 (i + 1)).toNat < l.val.size := by
    rw [h_i1u_toNat]; exact hi1
  have h_idx_i := slice_idx_ok l (UInt64.toUSize64 i) h_idx_i_lt
  have h_idx_i1 := slice_idx_ok l (UInt64.toUSize64 (i + 1)) h_idx_i1_lt
  have h_a_eq : l.val[(UInt64.toUSize64 i).toNat]'h_idx_i_lt =
      l.val[i.toNat]'(Nat.lt_of_succ_lt hi1) := by congr 1
  have h_b_eq : l.val[(UInt64.toUSize64 (i + 1)).toNat]'h_idx_i1_lt =
      l.val[i.toNat + 1]'hi1 := by congr 1
  have h_lt_cond :
      decide (l.val[(UInt64.toUSize64 i).toNat]'h_idx_i_lt <
              l.val[(UInt64.toUSize64 (i + 1)).toNat]'h_idx_i1_lt) = true := by
    rw [decide_eq_true_iff, h_a_eq, h_b_eq]; exact h_lt
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.hax.cast_op, Cast.cast,
             h_add, rust_primitives.cmp.ge, rust_primitives.cmp.lt,
             pure_bind, RustM_ok_bind, h_cond_ge, Bool.false_eq_true, ↓reduceIte,
             h_idx_i, h_idx_i1, h_lt_cond]
  rfl

private theorem is_nonincreasing_from_recurse (l : RustSlice i64) (i : u64)
    (hi1 : i.toNat + 1 < l.val.size)
    (h_ge : l.val[i.toNat + 1]'hi1 ≤ l.val[i.toNat]'(Nat.lt_of_succ_lt hi1)) :
    clever_050_monotonic.is_nonincreasing_from l i =
      clever_050_monotonic.is_nonincreasing_from l (i + 1) := by
  conv => lhs; unfold clever_050_monotonic.is_nonincreasing_from
  have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
  have hi_add : i.toNat + 1 < 2^64 := Nat.lt_trans hi1 h_size_lt
  have hn_toNat : ((USize64.ofNat l.val.size).toUInt64).toNat = l.val.size := n_val_toNat l
  have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := u64_add_one_toNat i hi_add
  have h_add : (i +? (1 : u64) : RustM u64) = pure (i + 1) := add_one_pure_u64 i hi_add
  have h_cond_ge : decide ((i + 1) ≥ (USize64.ofNat l.val.size).toUInt64) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    change ((USize64.ofNat l.val.size).toUInt64) ≤ (i + 1) at hle
    rw [UInt64.le_iff_toNat_le, hn_toNat, h_i1_toNat] at hle
    omega
  have h_iu_toNat : (UInt64.toUSize64 i).toNat = i.toNat := u64_toUSize64_toNat i
  have h_i1u_toNat : (UInt64.toUSize64 (i + 1)).toNat = i.toNat + 1 := by
    rw [u64_toUSize64_toNat]; exact h_i1_toNat
  have h_idx_i_lt : (UInt64.toUSize64 i).toNat < l.val.size := by
    rw [h_iu_toNat]; omega
  have h_idx_i1_lt : (UInt64.toUSize64 (i + 1)).toNat < l.val.size := by
    rw [h_i1u_toNat]; exact hi1
  have h_idx_i := slice_idx_ok l (UInt64.toUSize64 i) h_idx_i_lt
  have h_idx_i1 := slice_idx_ok l (UInt64.toUSize64 (i + 1)) h_idx_i1_lt
  have h_a_eq : l.val[(UInt64.toUSize64 i).toNat]'h_idx_i_lt =
      l.val[i.toNat]'(Nat.lt_of_succ_lt hi1) := by congr 1
  have h_b_eq : l.val[(UInt64.toUSize64 (i + 1)).toNat]'h_idx_i1_lt =
      l.val[i.toNat + 1]'hi1 := by congr 1
  have h_lt_cond :
      decide (l.val[(UInt64.toUSize64 i).toNat]'h_idx_i_lt <
              l.val[(UInt64.toUSize64 (i + 1)).toNat]'h_idx_i1_lt) = false := by
    rw [decide_eq_false_iff_not]
    intro h_lt
    rw [h_a_eq, h_b_eq] at h_lt
    have h_le_int : (l.val[i.toNat + 1]'hi1).toInt ≤
                    (l.val[i.toNat]'(Nat.lt_of_succ_lt hi1)).toInt :=
      Int64.le_iff_toInt_le.mp h_ge
    have h_lt_int : (l.val[i.toNat]'(Nat.lt_of_succ_lt hi1)).toInt <
                    (l.val[i.toNat + 1]'hi1).toInt :=
      Int64.lt_iff_toInt_lt.mp h_lt
    omega
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.hax.cast_op, Cast.cast,
             h_add, rust_primitives.cmp.ge, rust_primitives.cmp.lt,
             pure_bind, RustM_ok_bind, h_cond_ge, Bool.false_eq_true, ↓reduceIte,
             h_idx_i, h_idx_i1, h_lt_cond]

/-! ## Strong-induction lemmas: completeness of each helper. -/

/-- Forward (true) direction for `is_nondecreasing_from`: if every adjacent pair from
    index `i.toNat` onwards is non-decreasing, the function returns `ok true`. -/
private theorem is_nondecreasing_from_ok_true_aux (l : RustSlice i64) :
    ∀ (m : Nat) (i : u64),
      l.val.size - i.toNat ≤ m →
      i.toNat + 1 < 2^64 →
      (∀ j : Nat, i.toNat ≤ j → ∀ (hj1 : j + 1 < l.val.size),
          l.val[j]'(Nat.lt_of_succ_lt hj1) ≤ l.val[j+1]'hj1) →
      clever_050_monotonic.is_nondecreasing_from l i = RustM.ok true := by
  intro m
  induction m with
  | zero =>
    intro i hm hi_add hall
    -- l.val.size - i.toNat = 0, so i.toNat ≥ l.val.size ≥ l.val.size - 1, so i.toNat + 1 ≥ l.val.size.
    have h_size_le : l.val.size ≤ i.toNat + 1 := by omega
    exact is_nondecreasing_from_oob l i hi_add h_size_le
  | succ m ih =>
    intro i hm hi_add hall
    by_cases hi1_ge : l.val.size ≤ i.toNat + 1
    · exact is_nondecreasing_from_oob l i hi_add hi1_ge
    · have hi1 : i.toNat + 1 < l.val.size := Nat.lt_of_not_le hi1_ge
      have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
      have h_le := hall i.toNat (Nat.le_refl _) hi1
      rw [is_nondecreasing_from_recurse l i hi1 h_le]
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := u64_add_one_toNat i hi_add
      have h_next_add : (i + 1).toNat + 1 < 2^64 := by
        rw [h_i1_toNat]; omega
      have h_next_m : l.val.size - (i + 1).toNat ≤ m := by
        rw [h_i1_toNat]; omega
      have h_next_all :
          ∀ j : Nat, (i + 1).toNat ≤ j → ∀ (hj1 : j + 1 < l.val.size),
            l.val[j]'(Nat.lt_of_succ_lt hj1) ≤ l.val[j+1]'hj1 := by
        intro j hj hj1
        apply hall j _ hj1
        rw [h_i1_toNat] at hj
        omega
      exact ih (i + 1) h_next_m h_next_add h_next_all

/-- Backward (false) direction for `is_nondecreasing_from`: if there is some
    adjacent pair from index `i.toNat` onwards that violates non-decreasing,
    the function returns `ok false`. -/
private theorem is_nondecreasing_from_ok_false_aux (l : RustSlice i64) :
    ∀ (m : Nat) (i : u64),
      l.val.size - i.toNat ≤ m →
      i.toNat + 1 < 2^64 →
      (∃ j : Nat, i.toNat ≤ j ∧ ∃ (hj1 : j + 1 < l.val.size),
          l.val[j]'(Nat.lt_of_succ_lt hj1) > l.val[j+1]'hj1) →
      clever_050_monotonic.is_nondecreasing_from l i = RustM.ok false := by
  intro m
  induction m with
  | zero =>
    intro i hm hi_add ⟨j, hij, hj1, _⟩
    omega
  | succ m ih =>
    intro i hm hi_add ⟨j, hij, hj1, hwit⟩
    have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
    have hi1 : i.toNat + 1 < l.val.size := by omega
    by_cases h_now : l.val[i.toNat]'(Nat.lt_of_succ_lt hi1) > l.val[i.toNat + 1]'hi1
    · exact is_nondecreasing_from_violation l i hi1 h_now
    · have h_now_le : l.val[i.toNat]'(Nat.lt_of_succ_lt hi1) ≤
                      l.val[i.toNat + 1]'hi1 := by
        rcases Int.lt_or_le (l.val[i.toNat + 1]'hi1).toInt
                            (l.val[i.toNat]'(Nat.lt_of_succ_lt hi1)).toInt with h | h
        · exfalso; apply h_now; exact Int64.lt_iff_toInt_lt.mpr h
        · exact Int64.le_iff_toInt_le.mpr h
      -- The witness `j` cannot be at `i.toNat` (would contradict `h_now`), so `j ≥ i.toNat + 1`.
      have h_j_ne : j ≠ i.toNat := by
        intro heq
        apply h_now
        -- Show `l[i.toNat] > l[i.toNat + 1]` follows from `hwit : l[j] > l[j+1]` when `j = i.toNat`.
        have heq1 : j + 1 = i.toNat + 1 := by rw [heq]
        have h_a : l.val[j]'(Nat.lt_of_succ_lt hj1) =
                   l.val[i.toNat]'(Nat.lt_of_succ_lt hi1) := by
          subst heq; rfl
        have h_b : l.val[j+1]'hj1 = l.val[i.toNat + 1]'hi1 := by
          subst heq; rfl
        rw [h_a, h_b] at hwit
        exact hwit
      have h_j_ge : i.toNat + 1 ≤ j := by omega
      rw [is_nondecreasing_from_recurse l i hi1 h_now_le]
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := u64_add_one_toNat i hi_add
      have h_next_add : (i + 1).toNat + 1 < 2^64 := by rw [h_i1_toNat]; omega
      have h_next_m : l.val.size - (i + 1).toNat ≤ m := by rw [h_i1_toNat]; omega
      have h_next_witness :
          ∃ j' : Nat, (i + 1).toNat ≤ j' ∧ ∃ (hj1' : j' + 1 < l.val.size),
            l.val[j']'(Nat.lt_of_succ_lt hj1') > l.val[j'+1]'hj1' := by
        refine ⟨j, ?_, hj1, hwit⟩
        rw [h_i1_toNat]; exact h_j_ge
      exact ih (i + 1) h_next_m h_next_add h_next_witness

/-! Same for `is_nonincreasing_from`. -/

private theorem is_nonincreasing_from_ok_true_aux (l : RustSlice i64) :
    ∀ (m : Nat) (i : u64),
      l.val.size - i.toNat ≤ m →
      i.toNat + 1 < 2^64 →
      (∀ j : Nat, i.toNat ≤ j → ∀ (hj1 : j + 1 < l.val.size),
          l.val[j+1]'hj1 ≤ l.val[j]'(Nat.lt_of_succ_lt hj1)) →
      clever_050_monotonic.is_nonincreasing_from l i = RustM.ok true := by
  intro m
  induction m with
  | zero =>
    intro i hm hi_add hall
    have h_size_le : l.val.size ≤ i.toNat + 1 := by omega
    exact is_nonincreasing_from_oob l i hi_add h_size_le
  | succ m ih =>
    intro i hm hi_add hall
    by_cases hi1_ge : l.val.size ≤ i.toNat + 1
    · exact is_nonincreasing_from_oob l i hi_add hi1_ge
    · have hi1 : i.toNat + 1 < l.val.size := Nat.lt_of_not_le hi1_ge
      have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
      have h_ge := hall i.toNat (Nat.le_refl _) hi1
      rw [is_nonincreasing_from_recurse l i hi1 h_ge]
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := u64_add_one_toNat i hi_add
      have h_next_add : (i + 1).toNat + 1 < 2^64 := by
        rw [h_i1_toNat]; omega
      have h_next_m : l.val.size - (i + 1).toNat ≤ m := by
        rw [h_i1_toNat]; omega
      have h_next_all :
          ∀ j : Nat, (i + 1).toNat ≤ j → ∀ (hj1 : j + 1 < l.val.size),
            l.val[j+1]'hj1 ≤ l.val[j]'(Nat.lt_of_succ_lt hj1) := by
        intro j hj hj1
        apply hall j _ hj1
        rw [h_i1_toNat] at hj
        omega
      exact ih (i + 1) h_next_m h_next_add h_next_all

private theorem is_nonincreasing_from_ok_false_aux (l : RustSlice i64) :
    ∀ (m : Nat) (i : u64),
      l.val.size - i.toNat ≤ m →
      i.toNat + 1 < 2^64 →
      (∃ j : Nat, i.toNat ≤ j ∧ ∃ (hj1 : j + 1 < l.val.size),
          l.val[j]'(Nat.lt_of_succ_lt hj1) < l.val[j+1]'hj1) →
      clever_050_monotonic.is_nonincreasing_from l i = RustM.ok false := by
  intro m
  induction m with
  | zero =>
    intro i hm hi_add ⟨j, hij, hj1, _⟩
    omega
  | succ m ih =>
    intro i hm hi_add ⟨j, hij, hj1, hwit⟩
    have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
    have hi1 : i.toNat + 1 < l.val.size := by omega
    by_cases h_now : l.val[i.toNat]'(Nat.lt_of_succ_lt hi1) < l.val[i.toNat + 1]'hi1
    · exact is_nonincreasing_from_violation l i hi1 h_now
    · have h_now_ge : l.val[i.toNat + 1]'hi1 ≤
                      l.val[i.toNat]'(Nat.lt_of_succ_lt hi1) := by
        rcases Int.lt_or_le (l.val[i.toNat]'(Nat.lt_of_succ_lt hi1)).toInt
                            (l.val[i.toNat + 1]'hi1).toInt with h | h
        · exfalso; apply h_now; exact Int64.lt_iff_toInt_lt.mpr h
        · exact Int64.le_iff_toInt_le.mpr h
      have h_j_ne : j ≠ i.toNat := by
        intro heq
        apply h_now
        have h_a : l.val[j]'(Nat.lt_of_succ_lt hj1) =
                   l.val[i.toNat]'(Nat.lt_of_succ_lt hi1) := by
          subst heq; rfl
        have h_b : l.val[j+1]'hj1 = l.val[i.toNat + 1]'hi1 := by
          subst heq; rfl
        rw [h_a, h_b] at hwit
        exact hwit
      have h_j_ge : i.toNat + 1 ≤ j := by omega
      rw [is_nonincreasing_from_recurse l i hi1 h_now_ge]
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := u64_add_one_toNat i hi_add
      have h_next_add : (i + 1).toNat + 1 < 2^64 := by rw [h_i1_toNat]; omega
      have h_next_m : l.val.size - (i + 1).toNat ≤ m := by rw [h_i1_toNat]; omega
      have h_next_witness :
          ∃ j' : Nat, (i + 1).toNat ≤ j' ∧ ∃ (hj1' : j' + 1 < l.val.size),
            l.val[j']'(Nat.lt_of_succ_lt hj1') < l.val[j'+1]'hj1' := by
        refine ⟨j, ?_, hj1, hwit⟩
        rw [h_i1_toNat]; exact h_j_ge
      exact ih (i + 1) h_next_m h_next_add h_next_witness

/-! ## Totality lemma for `is_nondecreasing_from`. -/

private theorem is_nondecreasing_from_total_aux (l : RustSlice i64) :
    ∀ (m : Nat) (i : u64),
      l.val.size - i.toNat ≤ m →
      i.toNat + 1 < 2^64 →
      clever_050_monotonic.is_nondecreasing_from l i = RustM.ok true ∨
      clever_050_monotonic.is_nondecreasing_from l i = RustM.ok false := by
  intro m
  induction m with
  | zero =>
    intro i hm hi_add
    have h_size_le : l.val.size ≤ i.toNat + 1 := by omega
    left
    exact is_nondecreasing_from_oob l i hi_add h_size_le
  | succ m ih =>
    intro i hm hi_add
    by_cases hi1_ge : l.val.size ≤ i.toNat + 1
    · left; exact is_nondecreasing_from_oob l i hi_add hi1_ge
    · have hi1 : i.toNat + 1 < l.val.size := Nat.lt_of_not_le hi1_ge
      have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
      by_cases h_gt : l.val[i.toNat]'(Nat.lt_of_succ_lt hi1) >
                      l.val[i.toNat + 1]'hi1
      · right; exact is_nondecreasing_from_violation l i hi1 h_gt
      · have h_le : l.val[i.toNat]'(Nat.lt_of_succ_lt hi1) ≤
                    l.val[i.toNat + 1]'hi1 := by
          rcases Int.lt_or_le (l.val[i.toNat + 1]'hi1).toInt
                              (l.val[i.toNat]'(Nat.lt_of_succ_lt hi1)).toInt with h | h
          · exfalso; apply h_gt; exact Int64.lt_iff_toInt_lt.mpr h
          · exact Int64.le_iff_toInt_le.mpr h
        rw [is_nondecreasing_from_recurse l i hi1 h_le]
        have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := u64_add_one_toNat i hi_add
        have h_next_add : (i + 1).toNat + 1 < 2^64 := by rw [h_i1_toNat]; omega
        have h_next_m : l.val.size - (i + 1).toNat ≤ m := by rw [h_i1_toNat]; omega
        exact ih (i + 1) h_next_m h_next_add

/-! ## Negation-of-universal extraction (classical) for the soundness clause. -/

private theorem not_is_nondec_to_exists (l : RustSlice i64) (h : ¬ is_nondec l) :
    ∃ j : Nat, ∃ (hj1 : j + 1 < l.val.size),
      l.val[j]'(Nat.lt_of_succ_lt hj1) > l.val[j+1]'hj1 := by
  apply Classical.not_not.mp
  intro hno
  apply h
  intro j hj1
  rcases Int.lt_or_le (l.val[j+1]'hj1).toInt
                      (l.val[j]'(Nat.lt_of_succ_lt hj1)).toInt with hh | hh
  · exfalso; apply hno; exact ⟨j, hj1, Int64.lt_iff_toInt_lt.mpr hh⟩
  · exact Int64.le_iff_toInt_le.mpr hh

private theorem not_is_noninc_to_exists (l : RustSlice i64) (h : ¬ is_noninc l) :
    ∃ j : Nat, ∃ (hj1 : j + 1 < l.val.size),
      l.val[j]'(Nat.lt_of_succ_lt hj1) < l.val[j+1]'hj1 := by
  apply Classical.not_not.mp
  intro hno
  apply h
  intro j hj1
  rcases Int.lt_or_le (l.val[j]'(Nat.lt_of_succ_lt hj1)).toInt
                      (l.val[j+1]'hj1).toInt with hh | hh
  · exfalso; apply hno; exact ⟨j, hj1, Int64.lt_iff_toInt_lt.mpr hh⟩
  · exact Int64.le_iff_toInt_le.mpr hh

/-! ## Top-level contract clauses. -/

/-- Helper: precondition values for applying the strong-induction lemmas at `i = 0`. -/
private theorem zero_preconds (l : RustSlice i64) :
    l.val.size - (0 : u64).toNat ≤ l.val.size ∧ (0 : u64).toNat + 1 < 2^64 := by
  refine ⟨?_, ?_⟩
  · rw [u64_zero_toNat]; omega
  · rw [u64_zero_toNat]; decide

theorem monotonic_small_lists (l : RustSlice i64) (h : l.val.size ≤ 1) :
    clever_050_monotonic.monotonic l = RustM.ok true := by
  -- A list of size ≤ 1 is vacuously non-decreasing, so the first helper returns ok true.
  have ⟨h_m_le, h_add⟩ := zero_preconds l
  have h_eq : clever_050_monotonic.is_nondecreasing_from l 0 = RustM.ok true := by
    apply is_nondecreasing_from_ok_true_aux l l.val.size 0 h_m_le h_add
    intro j hj hj1
    -- j + 1 < l.val.size ≤ 1, impossible.
    omega
  unfold clever_050_monotonic.monotonic
  rw [h_eq]
  rfl

theorem monotonic_returns_true (l : RustSlice i64) (h : is_nondec l ∨ is_noninc l) :
    clever_050_monotonic.monotonic l = RustM.ok true := by
  have ⟨h_m_le, h_add⟩ := zero_preconds l
  unfold clever_050_monotonic.monotonic
  rcases h with h_nondec | h_noninc
  · have h_eq : clever_050_monotonic.is_nondecreasing_from l 0 = RustM.ok true := by
      apply is_nondecreasing_from_ok_true_aux l l.val.size 0 h_m_le h_add
      intro j hj hj1
      exact h_nondec j hj1
    rw [h_eq]
    rfl
  · -- Case is_noninc l: case split on the result of is_nondecreasing_from l 0.
    have h_total := is_nondecreasing_from_total_aux l l.val.size 0 h_m_le h_add
    rcases h_total with h_true | h_false
    · rw [h_true]; rfl
    · have h_noninc_eq : clever_050_monotonic.is_nonincreasing_from l 0 = RustM.ok true := by
        apply is_nonincreasing_from_ok_true_aux l l.val.size 0 h_m_le h_add
        intro j hj hj1
        exact h_noninc j hj1
      rw [h_false]
      simp only [RustM_ok_bind, Bool.false_eq_true, ↓reduceIte]
      exact h_noninc_eq

theorem monotonic_returns_false (l : RustSlice i64)
    (h : ¬ is_nondec l ∧ ¬ is_noninc l) :
    clever_050_monotonic.monotonic l = RustM.ok false := by
  have ⟨h_m_le, h_add⟩ := zero_preconds l
  obtain ⟨h_not_nondec, h_not_noninc⟩ := h
  -- Extract witnesses.
  obtain ⟨j1, hj1_bound, hj1_gt⟩ := not_is_nondec_to_exists l h_not_nondec
  obtain ⟨j2, hj2_bound, hj2_lt⟩ := not_is_noninc_to_exists l h_not_noninc
  -- Apply false-direction lemmas.
  have h_nondec_false : clever_050_monotonic.is_nondecreasing_from l 0 = RustM.ok false := by
    apply is_nondecreasing_from_ok_false_aux l l.val.size 0 h_m_le h_add
    exact ⟨j1, by rw [u64_zero_toNat]; omega, hj1_bound, hj1_gt⟩
  have h_noninc_false : clever_050_monotonic.is_nonincreasing_from l 0 = RustM.ok false := by
    apply is_nonincreasing_from_ok_false_aux l l.val.size 0 h_m_le h_add
    exact ⟨j2, by rw [u64_zero_toNat]; omega, hj2_bound, hj2_lt⟩
  unfold clever_050_monotonic.monotonic
  rw [h_nondec_false]
  simp only [RustM_ok_bind, Bool.false_eq_true, ↓reduceIte]
  exact h_noninc_false

theorem monotonic_constant (l : RustSlice i64) (c : i64)
    (hconst : ∀ i : Nat, ∀ (hi : i < l.val.size), l.val[i]'hi = c) :
    clever_050_monotonic.monotonic l = RustM.ok true := by
  -- A constant list satisfies `is_nondec`, so we reuse `monotonic_returns_true`.
  apply monotonic_returns_true l
  left
  intro j hj1
  rw [hconst j (Nat.lt_of_succ_lt hj1), hconst (j+1) hj1]
  exact Int64.le_iff_toInt_le.mpr (Int.le_refl _)

end Clever_050_monotonicObligations
