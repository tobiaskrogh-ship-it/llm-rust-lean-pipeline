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

/-! ## Top-level contract clauses. -/

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
