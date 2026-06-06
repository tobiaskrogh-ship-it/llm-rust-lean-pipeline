-- Companion obligations file for the `clever_108_move_one_ball` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_108_move_one_ball

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_108_move_one_ballObligations

/-! ## Specification: cyclic-rotation sortedness predicate. -/

private def is_sorted_rotation
    (arr : RustSlice i64) (k : Nat) (hk : k < arr.val.size) : Prop :=
  ∀ i : Nat, ∀ (_hi1 : i + 1 < arr.val.size),
    arr.val[(i + k) % arr.val.size]'(Nat.mod_lt _ (by omega)) ≤
    arr.val[(i + 1 + k) % arr.val.size]'(Nat.mod_lt _ (by omega))

/-! ## Scaffolding. -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl
private theorem usize_zero_toNat : (0 : usize).toNat = 0 := rfl

private theorem usize_add_toNat (i j : usize) (h : i.toNat + j.toNat < 2^64) :
    (i + j).toNat = i.toNat + j.toNat := USize64.toNat_add_of_lt h

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

private theorem usize_no_add_overflow (i j : usize) (h : i.toNat + j.toNat < 2^64) :
    BitVec.uaddOverflow i.toBitVec j.toBitVec = false := by
  generalize hbo : BitVec.uaddOverflow i.toBitVec j.toBitVec = bo
  cases bo with
  | false => rfl
  | true =>
    exfalso
    have hov := (USize64.uaddOverflow_iff i j).mp hbo
    omega

private theorem usize_no_add_one_overflow (i : usize) (h : i.toNat + 1 < 2^64) :
    BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
  apply usize_no_add_overflow
  rw [usize_one_toNat]; exact h

private theorem add_one_pure_usize (i : usize) (h : i.toNat + 1 < 2^64) :
    (i +? (1 : usize) : RustM usize) = pure (i + 1) := by
  show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = pure (i + 1)
  show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure (i + 1)) = _
  rw [usize_no_add_one_overflow i h]
  rfl

private theorem add_pure_usize (i j : usize) (h : i.toNat + j.toNat < 2^64) :
    (i +? j : RustM usize) = pure (i + j) := by
  show (rust_primitives.ops.arith.Add.add i j : RustM usize) = pure (i + j)
  show (if BitVec.uaddOverflow i.toBitVec j.toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure (i + j)) = _
  rw [usize_no_add_overflow i j h]
  rfl

private theorem mod_pure_usize (i n : usize) (h : n ≠ 0) :
    (i %? n : RustM usize) = pure (i % n) := by
  show (rust_primitives.ops.arith.Rem.rem i n : RustM usize) = pure (i % n)
  show (if n = 0 then (.fail .divisionByZero : RustM usize)
        else pure (i % n)) = _
  rw [if_neg h]

private theorem n_size_ofNat_toNat (l : RustSlice i64) :
    (USize64.ofNat l.val.size).toNat = l.val.size :=
  USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize

private theorem slice_idx_ok (l : RustSlice i64) (i : usize)
    (hi : i.toNat < l.val.size) :
    (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi) := by
  show (if h : i.toNat < l.val.size then (pure (l.val[i]) : RustM i64)
        else RustM.fail Error.arrayOutOfBounds) = RustM.ok (l.val[i.toNat]'hi)
  rw [dif_pos hi]; rfl

private theorem usize_toNat_mod (i n : usize) (h : n ≠ 0) :
    (i % n).toNat = i.toNat % n.toNat := by
  show (i.toBitVec % n.toBitVec).toNat = i.toNat % n.toNat
  rw [BitVec.toNat_umod]
  rfl

/-! ## Step lemmas for `is_sorted_split_at`. -/

/-- Out-of-bounds step: `i + 1 ≥ size` triggers the early-exit `ok true` branch.
    Requires `i.toNat + 1 < 2^64` for the `+? 1` to succeed. -/
private theorem iss_oob (l : RustSlice i64) (k i : usize)
    (h_i1_lt : i.toNat + 1 < 2^64)
    (hi_ge : l.val.size ≤ i.toNat + 1) :
    clever_108_move_one_ball.is_sorted_split_at l k i = RustM.ok true := by
  conv => lhs; unfold clever_108_move_one_ball.is_sorted_split_at
  have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
  have h_n_toNat : (USize64.ofNat l.val.size).toNat = l.val.size := n_size_ofNat_toNat l
  have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_i1_lt
  have h_add : (i +? (1 : usize) : RustM usize) = pure (i + 1) :=
    add_one_pure_usize i h_i1_lt
  have h_cond : decide ((i + 1) ≥ (USize64.ofNat l.val.size)) = true := by
    rw [decide_eq_true_iff]
    change (USize64.ofNat l.val.size) ≤ (i + 1)
    rw [USize64.le_iff_toNat_le, h_n_toNat, h_i1_toNat]
    exact hi_ge
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             pure_bind, h_add, rust_primitives.cmp.ge, h_cond, ↓reduceIte]
  rfl

/-- Violation step: when the adjacent pair at indices `(i+k) % n, (i+1+k) % n`
    is strictly decreasing, the function returns `ok false`. -/
private theorem iss_violation (l : RustSlice i64) (k i : usize)
    (hi1 : i.toNat + 1 < l.val.size)
    (h_size : 2 * l.val.size < 2^64)
    (hk : k.toNat < l.val.size)
    (h_gt : l.val[(i.toNat + k.toNat) % l.val.size]'(Nat.mod_lt _ (by omega)) >
            l.val[(i.toNat + 1 + k.toNat) % l.val.size]'(Nat.mod_lt _ (by omega))) :
    clever_108_move_one_ball.is_sorted_split_at l k i = RustM.ok false := by
  conv => lhs; unfold clever_108_move_one_ball.is_sorted_split_at
  have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
  have h_n_pos : 0 < l.val.size := by omega
  have h_n_toNat : (USize64.ofNat l.val.size).toNat = l.val.size := n_size_ofNat_toNat l
  have h_i1_lt : i.toNat + 1 < 2^64 := by omega
  have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_i1_lt
  have h_add_1 : (i +? (1 : usize) : RustM usize) = pure (i + 1) :=
    add_one_pure_usize i h_i1_lt
  have h_cond_ge : decide ((i + 1) ≥ (USize64.ofNat l.val.size)) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    change USize64.ofNat l.val.size ≤ i + 1 at hle
    rw [USize64.le_iff_toNat_le, h_n_toNat, h_i1_toNat] at hle
    omega
  -- i + k arithmetic
  have h_ik_lt : i.toNat + k.toNat < 2^64 := by omega
  have h_ik_toNat : (i + k).toNat = i.toNat + k.toNat := usize_add_toNat i k h_ik_lt
  have h_add_ik : (i +? k : RustM usize) = pure (i + k) := add_pure_usize i k h_ik_lt
  -- i + 1 + k arithmetic
  have h_i1k_lt : (i + 1).toNat + k.toNat < 2^64 := by rw [h_i1_toNat]; omega
  have h_i1k_toNat : (i + 1 + k).toNat = i.toNat + 1 + k.toNat := by
    rw [usize_add_toNat (i + 1) k h_i1k_lt, h_i1_toNat]
  have h_add_i1k : ((i + 1) +? k : RustM usize) = pure (i + 1 + k) :=
    add_pure_usize (i + 1) k h_i1k_lt
  -- n ≠ 0
  have h_n_ne : (USize64.ofNat l.val.size) ≠ 0 := by
    intro h_eq
    have : (USize64.ofNat l.val.size).toNat = (0 : usize).toNat := congrArg USize64.toNat h_eq
    rw [h_n_toNat, usize_zero_toNat] at this
    omega
  have h_mod_ik : ((i + k) %? (USize64.ofNat l.val.size) : RustM usize) =
      pure ((i + k) % (USize64.ofNat l.val.size)) := mod_pure_usize (i + k) _ h_n_ne
  have h_mod_i1k : ((i + 1 + k) %? (USize64.ofNat l.val.size) : RustM usize) =
      pure ((i + 1 + k) % (USize64.ofNat l.val.size)) := mod_pure_usize (i + 1 + k) _ h_n_ne
  -- Indices in bounds
  have h_ik_mod_toNat : ((i + k) % (USize64.ofNat l.val.size)).toNat =
      (i.toNat + k.toNat) % l.val.size := by
    rw [usize_toNat_mod (i + k) _ h_n_ne, h_ik_toNat, h_n_toNat]
  have h_i1k_mod_toNat : ((i + 1 + k) % (USize64.ofNat l.val.size)).toNat =
      (i.toNat + 1 + k.toNat) % l.val.size := by
    rw [usize_toNat_mod (i + 1 + k) _ h_n_ne, h_i1k_toNat, h_n_toNat]
  have h_ik_mod_lt : ((i + k) % (USize64.ofNat l.val.size)).toNat < l.val.size := by
    rw [h_ik_mod_toNat]; exact Nat.mod_lt _ h_n_pos
  have h_i1k_mod_lt : ((i + 1 + k) % (USize64.ofNat l.val.size)).toNat < l.val.size := by
    rw [h_i1k_mod_toNat]; exact Nat.mod_lt _ h_n_pos
  have h_idx_a := slice_idx_ok l ((i + k) % (USize64.ofNat l.val.size)) h_ik_mod_lt
  have h_idx_b := slice_idx_ok l ((i + 1 + k) % (USize64.ofNat l.val.size)) h_i1k_mod_lt
  -- Equate `l.val[idx_a]` with the Nat-level form
  have h_a_eq : l.val[((i + k) % (USize64.ofNat l.val.size)).toNat]'h_ik_mod_lt =
      l.val[(i.toNat + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos) := by congr 1
  have h_b_eq : l.val[((i + 1 + k) % (USize64.ofNat l.val.size)).toNat]'h_i1k_mod_lt =
      l.val[(i.toNat + 1 + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos) := by congr 1
  have h_gt_cond : decide
      ((l.val[((i + k) % (USize64.ofNat l.val.size)).toNat]'h_ik_mod_lt) >
       (l.val[((i + 1 + k) % (USize64.ofNat l.val.size)).toNat]'h_i1k_mod_lt)) = true := by
    rw [decide_eq_true_iff, h_a_eq, h_b_eq]; exact h_gt
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             pure_bind, RustM_ok_bind,
             h_add_1, rust_primitives.cmp.ge, h_cond_ge, Bool.false_eq_true, ↓reduceIte,
             h_add_ik, h_add_i1k, h_mod_ik, h_mod_i1k,
             h_idx_a, h_idx_b, rust_primitives.cmp.gt, h_gt_cond]
  rfl

/-- Recurse step: when the adjacent pair is non-decreasing, the function delegates
    to `is_sorted_split_at l k (i+1)`. -/
private theorem iss_recurse (l : RustSlice i64) (k i : usize)
    (hi1 : i.toNat + 1 < l.val.size)
    (h_size : 2 * l.val.size < 2^64)
    (hk : k.toNat < l.val.size)
    (h_le : l.val[(i.toNat + k.toNat) % l.val.size]'(Nat.mod_lt _ (by omega)) ≤
            l.val[(i.toNat + 1 + k.toNat) % l.val.size]'(Nat.mod_lt _ (by omega))) :
    clever_108_move_one_ball.is_sorted_split_at l k i =
      clever_108_move_one_ball.is_sorted_split_at l k (i + 1) := by
  conv => lhs; unfold clever_108_move_one_ball.is_sorted_split_at
  have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
  have h_n_pos : 0 < l.val.size := by omega
  have h_n_toNat : (USize64.ofNat l.val.size).toNat = l.val.size := n_size_ofNat_toNat l
  have h_i1_lt : i.toNat + 1 < 2^64 := by omega
  have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_i1_lt
  have h_add_1 : (i +? (1 : usize) : RustM usize) = pure (i + 1) :=
    add_one_pure_usize i h_i1_lt
  have h_cond_ge : decide ((i + 1) ≥ (USize64.ofNat l.val.size)) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    change USize64.ofNat l.val.size ≤ i + 1 at hle
    rw [USize64.le_iff_toNat_le, h_n_toNat, h_i1_toNat] at hle
    omega
  have h_ik_lt : i.toNat + k.toNat < 2^64 := by omega
  have h_ik_toNat : (i + k).toNat = i.toNat + k.toNat := usize_add_toNat i k h_ik_lt
  have h_add_ik : (i +? k : RustM usize) = pure (i + k) := add_pure_usize i k h_ik_lt
  have h_i1k_lt : (i + 1).toNat + k.toNat < 2^64 := by rw [h_i1_toNat]; omega
  have h_i1k_toNat : (i + 1 + k).toNat = i.toNat + 1 + k.toNat := by
    rw [usize_add_toNat (i + 1) k h_i1k_lt, h_i1_toNat]
  have h_add_i1k : ((i + 1) +? k : RustM usize) = pure (i + 1 + k) :=
    add_pure_usize (i + 1) k h_i1k_lt
  have h_n_ne : (USize64.ofNat l.val.size) ≠ 0 := by
    intro h_eq
    have : (USize64.ofNat l.val.size).toNat = (0 : usize).toNat := congrArg USize64.toNat h_eq
    rw [h_n_toNat, usize_zero_toNat] at this
    omega
  have h_mod_ik : ((i + k) %? (USize64.ofNat l.val.size) : RustM usize) =
      pure ((i + k) % (USize64.ofNat l.val.size)) := mod_pure_usize (i + k) _ h_n_ne
  have h_mod_i1k : ((i + 1 + k) %? (USize64.ofNat l.val.size) : RustM usize) =
      pure ((i + 1 + k) % (USize64.ofNat l.val.size)) := mod_pure_usize (i + 1 + k) _ h_n_ne
  have h_ik_mod_toNat : ((i + k) % (USize64.ofNat l.val.size)).toNat =
      (i.toNat + k.toNat) % l.val.size := by
    rw [usize_toNat_mod (i + k) _ h_n_ne, h_ik_toNat, h_n_toNat]
  have h_i1k_mod_toNat : ((i + 1 + k) % (USize64.ofNat l.val.size)).toNat =
      (i.toNat + 1 + k.toNat) % l.val.size := by
    rw [usize_toNat_mod (i + 1 + k) _ h_n_ne, h_i1k_toNat, h_n_toNat]
  have h_ik_mod_lt : ((i + k) % (USize64.ofNat l.val.size)).toNat < l.val.size := by
    rw [h_ik_mod_toNat]; exact Nat.mod_lt _ h_n_pos
  have h_i1k_mod_lt : ((i + 1 + k) % (USize64.ofNat l.val.size)).toNat < l.val.size := by
    rw [h_i1k_mod_toNat]; exact Nat.mod_lt _ h_n_pos
  have h_idx_a := slice_idx_ok l ((i + k) % (USize64.ofNat l.val.size)) h_ik_mod_lt
  have h_idx_b := slice_idx_ok l ((i + 1 + k) % (USize64.ofNat l.val.size)) h_i1k_mod_lt
  have h_a_eq : l.val[((i + k) % (USize64.ofNat l.val.size)).toNat]'h_ik_mod_lt =
      l.val[(i.toNat + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos) := by congr 1
  have h_b_eq : l.val[((i + 1 + k) % (USize64.ofNat l.val.size)).toNat]'h_i1k_mod_lt =
      l.val[(i.toNat + 1 + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos) := by congr 1
  have h_gt_cond : decide
      ((l.val[((i + k) % (USize64.ofNat l.val.size)).toNat]'h_ik_mod_lt) >
       (l.val[((i + 1 + k) % (USize64.ofNat l.val.size)).toNat]'h_i1k_mod_lt)) = false := by
    rw [decide_eq_false_iff_not]
    intro h_gt
    rw [h_a_eq, h_b_eq] at h_gt
    have h_le_int : (l.val[(i.toNat + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos)).toInt ≤
                    (l.val[(i.toNat + 1 + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos)).toInt :=
      Int64.le_iff_toInt_le.mp h_le
    have h_lt_int :
      (l.val[(i.toNat + 1 + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos)).toInt <
      (l.val[(i.toNat + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos)).toInt :=
      Int64.lt_iff_toInt_lt.mp h_gt
    omega
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             pure_bind, RustM_ok_bind,
             h_add_1, rust_primitives.cmp.ge, h_cond_ge, Bool.false_eq_true, ↓reduceIte,
             h_add_ik, h_add_i1k, h_mod_ik, h_mod_i1k,
             h_idx_a, h_idx_b, rust_primitives.cmp.gt, h_gt_cond]

/-! ## Strong-induction lemmas for `is_sorted_split_at`. -/

private theorem iss_ok_true_aux (l : RustSlice i64) (k : usize)
    (h_size : 2 * l.val.size < 2^64) (hk : k.toNat < l.val.size) :
    ∀ (m : Nat) (i : usize),
      l.val.size - i.toNat ≤ m →
      i.toNat + 1 < 2^64 →
      (∀ j : Nat, i.toNat ≤ j → ∀ (hj1 : j + 1 < l.val.size),
          l.val[(j + k.toNat) % l.val.size]'(Nat.mod_lt _ (by omega)) ≤
          l.val[(j + 1 + k.toNat) % l.val.size]'(Nat.mod_lt _ (by omega))) →
      clever_108_move_one_ball.is_sorted_split_at l k i = RustM.ok true := by
  intro m
  induction m with
  | zero =>
    intro i hm hi_add hall
    have h_size_le : l.val.size ≤ i.toNat + 1 := by omega
    exact iss_oob l k i hi_add h_size_le
  | succ m ih =>
    intro i hm hi_add hall
    by_cases hi1_ge : l.val.size ≤ i.toNat + 1
    · exact iss_oob l k i hi_add hi1_ge
    · have hi1 : i.toNat + 1 < l.val.size := Nat.lt_of_not_le hi1_ge
      have h_le := hall i.toNat (Nat.le_refl _) hi1
      rw [iss_recurse l k i hi1 h_size hk h_le]
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i hi_add
      have h_next_add : (i + 1).toNat + 1 < 2^64 := by rw [h_i1_toNat]; omega
      have h_next_m : l.val.size - (i + 1).toNat ≤ m := by rw [h_i1_toNat]; omega
      have h_next_all :
          ∀ j : Nat, (i + 1).toNat ≤ j → ∀ (hj1 : j + 1 < l.val.size),
            l.val[(j + k.toNat) % l.val.size]'(Nat.mod_lt _ (by omega)) ≤
            l.val[(j + 1 + k.toNat) % l.val.size]'(Nat.mod_lt _ (by omega)) := by
        intro j hj hj1
        apply hall j _ hj1
        rw [h_i1_toNat] at hj
        omega
      exact ih (i + 1) h_next_m h_next_add h_next_all

private theorem iss_ok_false_aux (l : RustSlice i64) (k : usize)
    (h_size : 2 * l.val.size < 2^64) (hk : k.toNat < l.val.size) :
    ∀ (m : Nat) (i : usize),
      l.val.size - i.toNat ≤ m →
      i.toNat + 1 < 2^64 →
      (∃ j : Nat, i.toNat ≤ j ∧ ∃ (hj1 : j + 1 < l.val.size),
          l.val[(j + k.toNat) % l.val.size]'(Nat.mod_lt _ (by omega)) >
          l.val[(j + 1 + k.toNat) % l.val.size]'(Nat.mod_lt _ (by omega))) →
      clever_108_move_one_ball.is_sorted_split_at l k i = RustM.ok false := by
  intro m
  induction m with
  | zero =>
    intro i hm hi_add ⟨j, hij, hj1, _⟩
    omega
  | succ m ih =>
    intro i hm hi_add ⟨j, hij, hj1, hwit⟩
    have hi1 : i.toNat + 1 < l.val.size := by omega
    have h_n_pos : 0 < l.val.size := by omega
    by_cases h_now :
        l.val[(i.toNat + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos) >
        l.val[(i.toNat + 1 + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos)
    · exact iss_violation l k i hi1 h_size hk h_now
    · have h_now_le :
          l.val[(i.toNat + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos) ≤
          l.val[(i.toNat + 1 + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos) := by
        rcases Int.lt_or_le
            (l.val[(i.toNat + 1 + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos)).toInt
            (l.val[(i.toNat + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos)).toInt with h | h
        · exfalso; apply h_now; exact Int64.lt_iff_toInt_lt.mpr h
        · exact Int64.le_iff_toInt_le.mpr h
      have h_j_ne : j ≠ i.toNat := by
        intro heq
        apply h_now
        have h_a : l.val[(j + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos) =
                   l.val[(i.toNat + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos) := by
          subst heq; rfl
        have h_b : l.val[(j + 1 + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos) =
                   l.val[(i.toNat + 1 + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos) := by
          subst heq; rfl
        rw [h_a, h_b] at hwit
        exact hwit
      have h_j_ge : i.toNat + 1 ≤ j := by omega
      rw [iss_recurse l k i hi1 h_size hk h_now_le]
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i hi_add
      have h_next_add : (i + 1).toNat + 1 < 2^64 := by rw [h_i1_toNat]; omega
      have h_next_m : l.val.size - (i + 1).toNat ≤ m := by rw [h_i1_toNat]; omega
      have h_next_witness :
          ∃ j' : Nat, (i + 1).toNat ≤ j' ∧ ∃ (hj1' : j' + 1 < l.val.size),
            l.val[(j' + k.toNat) % l.val.size]'(Nat.mod_lt _ (by omega)) >
            l.val[(j' + 1 + k.toNat) % l.val.size]'(Nat.mod_lt _ (by omega)) := by
        refine ⟨j, ?_, hj1, hwit⟩
        rw [h_i1_toNat]; exact h_j_ge
      exact ih (i + 1) h_next_m h_next_add h_next_witness

private theorem iss_total_aux (l : RustSlice i64) (k : usize)
    (h_size : 2 * l.val.size < 2^64) (hk : k.toNat < l.val.size) :
    ∀ (m : Nat) (i : usize),
      l.val.size - i.toNat ≤ m →
      i.toNat + 1 < 2^64 →
      clever_108_move_one_ball.is_sorted_split_at l k i = RustM.ok true ∨
      clever_108_move_one_ball.is_sorted_split_at l k i = RustM.ok false := by
  intro m
  induction m with
  | zero =>
    intro i hm hi_add
    have h_size_le : l.val.size ≤ i.toNat + 1 := by omega
    left
    exact iss_oob l k i hi_add h_size_le
  | succ m ih =>
    intro i hm hi_add
    by_cases hi1_ge : l.val.size ≤ i.toNat + 1
    · left; exact iss_oob l k i hi_add hi1_ge
    · have hi1 : i.toNat + 1 < l.val.size := Nat.lt_of_not_le hi1_ge
      have h_n_pos : 0 < l.val.size := by omega
      by_cases h_gt :
          l.val[(i.toNat + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos) >
          l.val[(i.toNat + 1 + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos)
      · right; exact iss_violation l k i hi1 h_size hk h_gt
      · have h_le :
            l.val[(i.toNat + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos) ≤
            l.val[(i.toNat + 1 + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos) := by
          rcases Int.lt_or_le
              (l.val[(i.toNat + 1 + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos)).toInt
              (l.val[(i.toNat + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos)).toInt with h | h
          · exfalso; apply h_gt; exact Int64.lt_iff_toInt_lt.mpr h
          · exact Int64.le_iff_toInt_le.mpr h
        rw [iss_recurse l k i hi1 h_size hk h_le]
        have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i hi_add
        have h_next_add : (i + 1).toNat + 1 < 2^64 := by rw [h_i1_toNat]; omega
        have h_next_m : l.val.size - (i + 1).toNat ≤ m := by rw [h_i1_toNat]; omega
        exact ih (i + 1) h_next_m h_next_add

/-! ## Step lemmas for `try_at`. -/

/-- Out-of-bounds: `k.toNat ≥ size` triggers the early-exit `ok false`. -/
private theorem ta_oob (l : RustSlice i64) (k : usize)
    (hk : l.val.size ≤ k.toNat) :
    clever_108_move_one_ball.try_at l k = RustM.ok false := by
  conv => lhs; unfold clever_108_move_one_ball.try_at
  have h_n_toNat : (USize64.ofNat l.val.size).toNat = l.val.size := n_size_ofNat_toNat l
  have h_cond : decide (k ≥ (USize64.ofNat l.val.size)) = true := by
    rw [decide_eq_true_iff]
    change (USize64.ofNat l.val.size) ≤ k
    rw [USize64.le_iff_toNat_le, h_n_toNat]
    exact hk
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             pure_bind, rust_primitives.cmp.ge, h_cond, ↓reduceIte]
  rfl

/-- Match: when `k.toNat < size` and `is_sorted_split_at l k 0 = ok true`,
    the function returns `ok true`. -/
private theorem ta_match (l : RustSlice i64) (k : usize)
    (hk : k.toNat < l.val.size)
    (h_iss : clever_108_move_one_ball.is_sorted_split_at l k (0 : usize) = RustM.ok true) :
    clever_108_move_one_ball.try_at l k = RustM.ok true := by
  conv => lhs; unfold clever_108_move_one_ball.try_at
  have h_n_toNat : (USize64.ofNat l.val.size).toNat = l.val.size := n_size_ofNat_toNat l
  have h_cond : decide (k ≥ (USize64.ofNat l.val.size)) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    change (USize64.ofNat l.val.size) ≤ k at hle
    rw [USize64.le_iff_toNat_le, h_n_toNat] at hle
    omega
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             pure_bind, RustM_ok_bind, rust_primitives.cmp.ge,
             h_cond, Bool.false_eq_true, ↓reduceIte, h_iss]
  rfl

/-- Recurse: when `k.toNat < size` and `is_sorted_split_at l k 0 = ok false`,
    the function delegates to `try_at l (k+1)`. -/
private theorem ta_recurse (l : RustSlice i64) (k : usize)
    (hk : k.toNat < l.val.size)
    (h_k1 : k.toNat + 1 < 2^64)
    (h_iss : clever_108_move_one_ball.is_sorted_split_at l k (0 : usize) = RustM.ok false) :
    clever_108_move_one_ball.try_at l k =
      clever_108_move_one_ball.try_at l (k + 1) := by
  conv => lhs; unfold clever_108_move_one_ball.try_at
  have h_n_toNat : (USize64.ofNat l.val.size).toNat = l.val.size := n_size_ofNat_toNat l
  have h_cond : decide (k ≥ (USize64.ofNat l.val.size)) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    change (USize64.ofNat l.val.size) ≤ k at hle
    rw [USize64.le_iff_toNat_le, h_n_toNat] at hle
    omega
  have h_add_1 : (k +? (1 : usize) : RustM usize) = pure (k + 1) :=
    add_one_pure_usize k h_k1
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             pure_bind, RustM_ok_bind, rust_primitives.cmp.ge,
             h_cond, Bool.false_eq_true, ↓reduceIte, h_iss, h_add_1]

/-! ## Step analysis: extracting structure from `iss l k i = ok true`. -/

/-- Helper: if `(x +? y) >>= f = ok true`, then there is no overflow. -/
private theorem usize_add_no_ov_of_ok {α : Type} (x y : usize) (f : usize → RustM α)
    (a : α) (h : ((x +? y : RustM usize) >>= f) = RustM.ok a) :
    x.toNat + y.toNat < 2^64 := by
  rcases Nat.lt_or_ge (x.toNat + y.toNat) (2^64) with hlt | hge
  · exact hlt
  · exfalso
    have h_bv : BitVec.uaddOverflow x.toBitVec y.toBitVec = true :=
      (USize64.uaddOverflow_iff x y).mpr hge
    have h_fail : (x +? y : RustM usize) = RustM.fail .integerOverflow := by
      show (if BitVec.uaddOverflow x.toBitVec y.toBitVec then
              (.fail .integerOverflow : RustM usize)
            else pure (x + y)) = _
      rw [h_bv]; rfl
    rw [h_fail] at h
    simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, Option.bind] at h
    cases h

private theorem usize_add_no_ov_of_iss_ok (l : RustSlice i64) (k i : usize)
    (h : clever_108_move_one_ball.is_sorted_split_at l k i = RustM.ok true) :
    i.toNat + 1 < 2^64 := by
  rcases Nat.lt_or_ge (i.toNat + 1) (2^64) with hlt | hge
  · exact hlt
  · exfalso
    have h_bv : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = true := by
      apply (USize64.uaddOverflow_iff i 1).mpr
      rw [usize_one_toNat]; exact hge
    have h_fail : (i +? (1 : usize) : RustM usize) = RustM.fail .integerOverflow := by
      show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec then
              (.fail .integerOverflow : RustM usize)
            else pure (i + 1)) = _
      rw [h_bv]; rfl
    conv at h => lhs; unfold clever_108_move_one_ball.is_sorted_split_at
    simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
               pure_bind, h_fail] at h
    cases h

/-- Main step lemma for soundness. From `iss l k i = ok true`, derive either the
    early-exit condition or the body's properties (a ≤ b and recurses to ok true).
    No global size precondition required — all needed no-overflow facts are
    extracted from the assumption. -/
private theorem iss_step_ok_true (l : RustSlice i64) (k i : usize)
    (h : clever_108_move_one_ball.is_sorted_split_at l k i = RustM.ok true) :
    (l.val.size ≤ i.toNat + 1) ∨
    (∃ (hi1 : i.toNat + 1 < l.val.size) (h_n_pos : 0 < l.val.size),
      l.val[(i.toNat + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos) ≤
      l.val[(i.toNat + 1 + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos) ∧
      clever_108_move_one_ball.is_sorted_split_at l k (i + 1) = RustM.ok true) := by
  have h_i1_lt : i.toNat + 1 < 2^64 := usize_add_no_ov_of_iss_ok l k i h
  have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
  have h_n_toNat : (USize64.ofNat l.val.size).toNat = l.val.size := n_size_ofNat_toNat l
  have h_add_1 : (i +? (1 : usize) : RustM usize) = pure (i + 1) :=
    add_one_pure_usize i h_i1_lt
  have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_i1_lt
  -- Decide the early-exit predicate.
  by_cases h_oob : l.val.size ≤ i.toNat + 1
  · left; exact h_oob
  · right
    have hi1 : i.toNat + 1 < l.val.size := Nat.lt_of_not_le h_oob
    have h_n_pos : 0 < l.val.size := by omega
    have h_n_ne : (USize64.ofNat l.val.size) ≠ 0 := by
      intro h_eq
      have : (USize64.ofNat l.val.size).toNat = (0 : usize).toNat :=
        congrArg USize64.toNat h_eq
      rw [h_n_toNat, usize_zero_toNat] at this
      omega
    -- Now reduce h to the body form using iss_recurse's reverse direction.
    -- Strategy: walk through the body, extract no-overflow conditions, derive a ≤ b
    -- and the recursive call.
    -- First: reduce h to expose the body branch.
    conv at h => lhs; unfold clever_108_move_one_ball.is_sorted_split_at
    have h_cond_ge_f :
        decide ((i + 1) ≥ (USize64.ofNat l.val.size)) = false := by
      rw [decide_eq_false_iff_not]
      intro hle
      change (USize64.ofNat l.val.size) ≤ (i + 1) at hle
      rw [USize64.le_iff_toNat_le, h_n_toNat, h_i1_toNat] at hle
      omega
    simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
               pure_bind, h_add_1, rust_primitives.cmp.ge, RustM_ok_bind,
               h_cond_ge_f, Bool.false_eq_true, ↓reduceIte] at h
    -- Extract i + k no-overflow.
    have h_ik_lt : i.toNat + k.toNat < 2^64 := by
      rcases Nat.lt_or_ge (i.toNat + k.toNat) (2^64) with hlt | hge
      · exact hlt
      · exfalso
        have h_bv : BitVec.uaddOverflow i.toBitVec k.toBitVec = true :=
          (USize64.uaddOverflow_iff i k).mpr hge
        have h_fail : (i +? k : RustM usize) = RustM.fail .integerOverflow := by
          show (if BitVec.uaddOverflow i.toBitVec k.toBitVec then
                  (.fail .integerOverflow : RustM usize)
                else pure (i + k)) = _
          rw [h_bv]; rfl
        rw [h_fail] at h
        simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, Option.bind] at h
        cases h
    have h_add_ik : (i +? k : RustM usize) = pure (i + k) := add_pure_usize i k h_ik_lt
    have h_ik_toNat : (i + k).toNat = i.toNat + k.toNat := usize_add_toNat i k h_ik_lt
    have h_mod_ik : ((i + k) %? (USize64.ofNat l.val.size) : RustM usize) =
        pure ((i + k) % (USize64.ofNat l.val.size)) := mod_pure_usize (i + k) _ h_n_ne
    have h_ik_mod_toNat : ((i + k) % (USize64.ofNat l.val.size)).toNat =
        (i.toNat + k.toNat) % l.val.size := by
      rw [usize_toNat_mod (i + k) _ h_n_ne, h_ik_toNat, h_n_toNat]
    have h_ik_mod_lt : ((i + k) % (USize64.ofNat l.val.size)).toNat < l.val.size := by
      rw [h_ik_mod_toNat]; exact Nat.mod_lt _ h_n_pos
    have h_idx_a := slice_idx_ok l ((i + k) % (USize64.ofNat l.val.size)) h_ik_mod_lt
    rw [h_add_ik] at h
    simp only [pure_bind, RustM_ok_bind] at h
    rw [h_mod_ik] at h
    simp only [pure_bind, RustM_ok_bind] at h
    rw [h_idx_a] at h
    simp only [pure_bind, RustM_ok_bind] at h
    -- Extract (i+1) + k no-overflow.
    have h_i1k_lt : (i + 1).toNat + k.toNat < 2^64 := by
      rcases Nat.lt_or_ge ((i + 1).toNat + k.toNat) (2^64) with hlt | hge
      · exact hlt
      · exfalso
        have h_bv : BitVec.uaddOverflow (i + 1).toBitVec k.toBitVec = true :=
          (USize64.uaddOverflow_iff (i + 1) k).mpr hge
        have h_fail : ((i + 1) +? k : RustM usize) = RustM.fail .integerOverflow := by
          show (if BitVec.uaddOverflow (i + 1).toBitVec k.toBitVec then
                  (.fail .integerOverflow : RustM usize)
                else pure (i + 1 + k)) = _
          rw [h_bv]; rfl
        rw [h_fail] at h
        simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, Option.bind] at h
        cases h
    have h_add_i1k : ((i + 1) +? k : RustM usize) = pure (i + 1 + k) :=
      add_pure_usize (i + 1) k h_i1k_lt
    have h_i1k_toNat : (i + 1 + k).toNat = i.toNat + 1 + k.toNat := by
      rw [usize_add_toNat (i + 1) k h_i1k_lt, h_i1_toNat]
    have h_mod_i1k : ((i + 1 + k) %? (USize64.ofNat l.val.size) : RustM usize) =
        pure ((i + 1 + k) % (USize64.ofNat l.val.size)) :=
      mod_pure_usize (i + 1 + k) _ h_n_ne
    have h_i1k_mod_toNat : ((i + 1 + k) % (USize64.ofNat l.val.size)).toNat =
        (i.toNat + 1 + k.toNat) % l.val.size := by
      rw [usize_toNat_mod (i + 1 + k) _ h_n_ne, h_i1k_toNat, h_n_toNat]
    have h_i1k_mod_lt : ((i + 1 + k) % (USize64.ofNat l.val.size)).toNat < l.val.size := by
      rw [h_i1k_mod_toNat]; exact Nat.mod_lt _ h_n_pos
    have h_idx_b := slice_idx_ok l ((i + 1 + k) % (USize64.ofNat l.val.size)) h_i1k_mod_lt
    rw [h_add_i1k] at h
    simp only [pure_bind, RustM_ok_bind] at h
    rw [h_mod_i1k] at h
    simp only [pure_bind, RustM_ok_bind] at h
    rw [h_idx_b] at h
    simp only [pure_bind, RustM_ok_bind] at h
    -- Now h has the form `(a >? b) >>= fun c => if c then ok false else iss(...) = ok true`.
    -- a > b case is impossible (returns ok false). So a ≤ b and recurses to ok true.
    by_cases h_a_gt_b :
        decide ((l.val[((i + k) % (USize64.ofNat l.val.size)).toNat]'h_ik_mod_lt) >
                (l.val[((i + 1 + k) % (USize64.ofNat l.val.size)).toNat]'h_i1k_mod_lt))
            = true
    · exfalso
      simp only [rust_primitives.cmp.gt, pure_bind, h_a_gt_b, ↓reduceIte] at h
      cases h
    · have h_a_gt_b_f :
          decide ((l.val[((i + k) % (USize64.ofNat l.val.size)).toNat]'h_ik_mod_lt) >
                  (l.val[((i + 1 + k) % (USize64.ofNat l.val.size)).toNat]'h_i1k_mod_lt))
              = false := by
        cases hh : decide
            ((l.val[((i + k) % (USize64.ofNat l.val.size)).toNat]'h_ik_mod_lt) >
             (l.val[((i + 1 + k) % (USize64.ofNat l.val.size)).toNat]'h_i1k_mod_lt)) with
        | false => rfl
        | true => exact absurd hh h_a_gt_b
      simp only [rust_primitives.cmp.gt, pure_bind, h_a_gt_b_f,
                 Bool.false_eq_true, ↓reduceIte, h_add_1, RustM_ok_bind] at h
      -- h : iss l k (i+1) = ok true.
      have h_a_eq : l.val[((i + k) % (USize64.ofNat l.val.size)).toNat]'h_ik_mod_lt =
          l.val[(i.toNat + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos) := by congr 1
      have h_b_eq : l.val[((i + 1 + k) % (USize64.ofNat l.val.size)).toNat]'h_i1k_mod_lt =
          l.val[(i.toNat + 1 + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos) := by congr 1
      have h_a_le_b :
          l.val[(i.toNat + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos) ≤
          l.val[(i.toNat + 1 + k.toNat) % l.val.size]'(Nat.mod_lt _ h_n_pos) := by
        rw [← h_a_eq, ← h_b_eq]
        rw [decide_eq_false_iff_not] at h_a_gt_b_f
        rcases Int.lt_or_le
            (l.val[((i + 1 + k) % (USize64.ofNat l.val.size)).toNat]'h_i1k_mod_lt).toInt
            (l.val[((i + k) % (USize64.ofNat l.val.size)).toNat]'h_ik_mod_lt).toInt with hh | hh
        · exfalso; apply h_a_gt_b_f; exact Int64.lt_iff_toInt_lt.mpr hh
        · exact Int64.le_iff_toInt_le.mpr hh
      exact ⟨hi1, h_n_pos, h_a_le_b, h⟩

/-- Inductive lemma: from `iss l k 0 = ok true`, derive the universal rotation property. -/
private theorem iss_ok_true_implies_sorted_aux (l : RustSlice i64) (k : usize) :
    ∀ (m : Nat) (i : usize),
      l.val.size - i.toNat ≤ m →
      clever_108_move_one_ball.is_sorted_split_at l k i = RustM.ok true →
      ∀ j : Nat, i.toNat ≤ j → ∀ (hj1 : j + 1 < l.val.size),
        l.val[(j + k.toNat) % l.val.size]'(Nat.mod_lt _ (by omega)) ≤
        l.val[(j + 1 + k.toNat) % l.val.size]'(Nat.mod_lt _ (by omega)) := by
  intro m
  induction m with
  | zero =>
    intro i hm h_iss j hj hj1
    omega
  | succ m ih =>
    intro i hm h_iss j hj hj1
    rcases iss_step_ok_true l k i h_iss with h_oob | ⟨hi1, h_n_pos, h_a_le_b, h_rec⟩
    · -- early exit; the conclusion at j is vacuous because j ≥ i and j + 1 < size ≤ i + 1
      -- so j < i, contradicting j ≥ i.
      omega
    · -- body branch
      have h_i1_lt : i.toNat + 1 < 2^64 := by
        have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
        omega
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_i1_lt
      by_cases h_j_eq : j = i.toNat
      · -- The pair at j = i is the one we just extracted.
        subst h_j_eq
        exact h_a_le_b
      · -- j ≥ i.toNat + 1; recurse via IH.
        have h_j_ge : (i + 1).toNat ≤ j := by rw [h_i1_toNat]; omega
        have h_next_m : l.val.size - (i + 1).toNat ≤ m := by rw [h_i1_toNat]; omega
        exact ih (i + 1) h_next_m h_rec j h_j_ge hj1

/-! ## Strong-induction lemma for `try_at`. -/

/-- Forward direction: if some `k₀ ≥ k_start, k₀ < size` matches
    `is_sorted_split_at l k₀ 0 = ok true`, then `try_at l k_start = ok true`. -/
private theorem ta_ok_true_aux (l : RustSlice i64)
    (h_size : 2 * l.val.size < 2^64) :
    ∀ (m : Nat) (k_start : usize),
      l.val.size - k_start.toNat ≤ m →
      (∃ k₀ : Nat, k_start.toNat ≤ k₀ ∧ ∃ (hk₀ : k₀ < l.val.size),
          clever_108_move_one_ball.is_sorted_split_at l (USize64.ofNat k₀) (0 : usize) =
            RustM.ok true) →
      clever_108_move_one_ball.try_at l k_start = RustM.ok true := by
  intro m
  induction m with
  | zero =>
    intro k_start hm ⟨k₀, hk₀_ge, hk₀_lt, _⟩
    omega
  | succ m ih =>
    intro k_start hm ⟨k₀, hk₀_ge, hk₀_lt, h_iss_k₀⟩
    by_cases h_oob : l.val.size ≤ k_start.toNat
    · -- contradiction: k_start.toNat ≤ k₀ < size
      omega
    · have hk_start_lt : k_start.toNat < l.val.size := Nat.lt_of_not_le h_oob
      have hk_start_k1 : k_start.toNat + 1 < 2^64 := by omega
      by_cases h_eq : k₀ = k_start.toNat
      · -- match!
        have h_k_start_eq : USize64.ofNat k₀ = k_start := by
          apply USize64.toNat_inj.mp
          rw [USize64.toNat_ofNat_of_lt' (by omega : k₀ < 2^64)]
          rw [h_eq]
        rw [h_k_start_eq] at h_iss_k₀
        exact ta_match l k_start hk_start_lt h_iss_k₀
      · -- recurse
        have h_k₀_gt : k_start.toNat + 1 ≤ k₀ := by omega
        -- We need is_sorted_split_at l k_start 0 = ok ? to determine the branch
        -- Use iss_total_aux to get the result of is_sorted_split_at at k_start.
        have h_k_start_lt_2_64 : k_start.toNat < 2^64 := by omega
        have h_iss_total :=
          iss_total_aux l k_start h_size hk_start_lt
            l.val.size (0 : usize) (by simp [usize_zero_toNat]) (by decide)
        rcases h_iss_total with h_iss_true | h_iss_false
        · -- matched at k_start
          exact ta_match l k_start hk_start_lt h_iss_true
        · -- false, recurse
          rw [ta_recurse l k_start hk_start_lt hk_start_k1 h_iss_false]
          have h_k1_toNat : (k_start + 1).toNat = k_start.toNat + 1 :=
            usize_add_one_toNat k_start hk_start_k1
          have h_next_m : l.val.size - (k_start + 1).toNat ≤ m := by
            rw [h_k1_toNat]; omega
          have h_next_witness :
              ∃ k₀' : Nat, (k_start + 1).toNat ≤ k₀' ∧ ∃ (hk₀' : k₀' < l.val.size),
                clever_108_move_one_ball.is_sorted_split_at l (USize64.ofNat k₀') (0 : usize) =
                  RustM.ok true := by
            refine ⟨k₀, ?_, hk₀_lt, h_iss_k₀⟩
            rw [h_k1_toNat]; exact h_k₀_gt
          exact ih (k_start + 1) h_next_m h_next_witness

/-- Analysis: if `try_at l k_start = ok true`, then some `k₀ ≥ k_start, k₀ < size`
    has `is_sorted_split_at l k₀ 0 = ok true`. -/
private theorem ta_analysis (l : RustSlice i64)
    (h_size : 2 * l.val.size < 2^64) :
    ∀ (m : Nat) (k_start : usize),
      l.val.size - k_start.toNat ≤ m →
      clever_108_move_one_ball.try_at l k_start = RustM.ok true →
      ∃ k₀ : Nat, k_start.toNat ≤ k₀ ∧ ∃ (hk₀ : k₀ < l.val.size),
        clever_108_move_one_ball.is_sorted_split_at l (USize64.ofNat k₀) (0 : usize) =
          RustM.ok true := by
  intro m
  induction m with
  | zero =>
    intro k_start hm h_ta
    -- If size = 0, no witness possible — but then ta_oob fires and ta returns false.
    by_cases h_oob : l.val.size ≤ k_start.toNat
    · -- The function returned ok true, but it should have returned ok false.
      rw [ta_oob l k_start h_oob] at h_ta
      exact absurd h_ta (by decide)
    · -- size - k_start.toNat ≤ 0, so size ≤ k_start.toNat, contradiction.
      omega
  | succ m ih =>
    intro k_start hm h_ta
    by_cases h_oob : l.val.size ≤ k_start.toNat
    · rw [ta_oob l k_start h_oob] at h_ta
      exact absurd h_ta (by decide)
    · have hk_start_lt : k_start.toNat < l.val.size := Nat.lt_of_not_le h_oob
      have hk_start_k1 : k_start.toNat + 1 < 2^64 := by omega
      have h_iss_total :=
        iss_total_aux l k_start h_size hk_start_lt
          l.val.size (0 : usize) (by simp [usize_zero_toNat]) (by decide)
      rcases h_iss_total with h_iss_true | h_iss_false
      · -- matched at k_start
        refine ⟨k_start.toNat, Nat.le_refl _, hk_start_lt, ?_⟩
        have h_k_start_eq : USize64.ofNat k_start.toNat = k_start := by
          apply USize64.toNat_inj.mp
          rw [USize64.toNat_ofNat_of_lt' (by omega : k_start.toNat < 2^64)]
        rw [h_k_start_eq]
        exact h_iss_true
      · -- recursed
        rw [ta_recurse l k_start hk_start_lt hk_start_k1 h_iss_false] at h_ta
        have h_k1_toNat : (k_start + 1).toNat = k_start.toNat + 1 :=
          usize_add_one_toNat k_start hk_start_k1
        have h_next_m : l.val.size - (k_start + 1).toNat ≤ m := by
          rw [h_k1_toNat]; omega
        obtain ⟨k₀, hk₀_ge, hk₀_lt, h_iss_k₀⟩ := ih (k_start + 1) h_next_m h_ta
        refine ⟨k₀, ?_, hk₀_lt, h_iss_k₀⟩
        rw [h_k1_toNat] at hk₀_ge; omega

/-! ## Top-level theorems. -/

theorem move_one_ball_empty (arr : RustSlice i64) (h : arr.val.size = 0) :
    clever_108_move_one_ball.move_one_ball arr = RustM.ok true := by
  unfold clever_108_move_one_ball.move_one_ball
  unfold core_models.slice.Impl.is_empty
  unfold core_models.slice.Impl.len
  simp only [rust_primitives.slice.slice_length, pure_bind]
  have h_n_toNat : (USize64.ofNat arr.val.size).toNat = arr.val.size :=
    n_size_ofNat_toNat arr
  have h_n_eq_0 : (USize64.ofNat arr.val.size) = (0 : usize) := by
    apply USize64.toNat_inj.mp
    rw [h_n_toNat, usize_zero_toNat]; exact h
  rw [h_n_eq_0]
  show ((((0 : usize) ==? (0 : usize) : RustM Bool)) >>= _) = _
  simp only [rust_primitives.cmp.eq, pure_bind, beq_self_eq_true, ↓reduceIte]
  rfl

theorem move_one_ball_complete
    (arr : RustSlice i64)
    (h_size : 2 * arr.val.size < 2 ^ 64)
    (h : ∃ k : Nat, ∃ (hk : k < arr.val.size), is_sorted_rotation arr k hk) :
    clever_108_move_one_ball.move_one_ball arr = RustM.ok true := by
  by_cases h_empty : arr.val.size = 0
  · exact move_one_ball_empty arr h_empty
  · have h_pos : 0 < arr.val.size := Nat.pos_of_ne_zero h_empty
    -- Reduce `move_one_ball` to `try_at arr 0`.
    have h_n_toNat : (USize64.ofNat arr.val.size).toNat = arr.val.size :=
      n_size_ofNat_toNat arr
    have h_n_ne_0 : (USize64.ofNat arr.val.size) ≠ 0 := by
      intro h_eq
      have : (USize64.ofNat arr.val.size).toNat = (0 : usize).toNat :=
        congrArg USize64.toNat h_eq
      rw [h_n_toNat, usize_zero_toNat] at this
      omega
    have h_mob_eq : clever_108_move_one_ball.move_one_ball arr =
        clever_108_move_one_ball.try_at arr (0 : usize) := by
      unfold clever_108_move_one_ball.move_one_ball
      unfold core_models.slice.Impl.is_empty
      unfold core_models.slice.Impl.len
      simp only [rust_primitives.slice.slice_length, pure_bind]
      have h_eq_cond :
          ((USize64.ofNat arr.val.size) ==? (0 : usize) : RustM Bool) =
            pure false := by
        show (rust_primitives.cmp.eq (USize64.ofNat arr.val.size) (0 : usize) : RustM Bool) =
              pure false
        simp only [rust_primitives.cmp.eq]
        show pure (((USize64.ofNat arr.val.size) == (0 : usize)) : Bool) = pure false
        rw [beq_eq_false_iff_ne.mpr h_n_ne_0]
      rw [h_eq_cond]
      simp only [pure_bind, Bool.false_eq_true, ↓reduceIte]
    rw [h_mob_eq]
    obtain ⟨k, hk, h_rot⟩ := h
    -- Use ta_ok_true_aux with witness USize64.ofNat k.
    apply ta_ok_true_aux arr h_size arr.val.size (0 : usize)
      (by simp [usize_zero_toNat])
    refine ⟨k, by simp [usize_zero_toNat], hk, ?_⟩
    -- Need to invoke iss_ok_true_aux at (USize64.ofNat k).
    have h_k_lt_2_64 : k < 2^64 := by omega
    have h_ofNat_k_toNat : (USize64.ofNat k).toNat = k :=
      USize64.toNat_ofNat_of_lt' h_k_lt_2_64
    apply iss_ok_true_aux arr (USize64.ofNat k) h_size
      (by rw [h_ofNat_k_toNat]; exact hk)
      arr.val.size (0 : usize)
      (by simp [usize_zero_toNat])
      (by decide)
    intro j hj hj1
    have h_eq_k : (USize64.ofNat k).toNat = k := h_ofNat_k_toNat
    rw [h_eq_k]
    exact h_rot j hj1

/-- Raw step-analysis for `try_at l k = ok true`: extracts `k < size` and
    either the match case (iss returns ok true) or the recurse case
    (iss returns ok false and try_at l (k+1) returns ok true). No size
    precondition. -/
private theorem ta_step_ok_true (l : RustSlice i64) (k : usize)
    (h : clever_108_move_one_ball.try_at l k = RustM.ok true) :
    k.toNat < l.val.size ∧
    ((clever_108_move_one_ball.is_sorted_split_at l k (0 : usize) = RustM.ok true) ∨
     (clever_108_move_one_ball.is_sorted_split_at l k (0 : usize) = RustM.ok false ∧
      clever_108_move_one_ball.try_at l (k + 1) = RustM.ok true)) := by
  have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
  have h_n_toNat : (USize64.ofNat l.val.size).toNat = l.val.size := n_size_ofNat_toNat l
  conv at h => lhs; unfold clever_108_move_one_ball.try_at
  -- First show k < size (else try_at returns ok false, contradicting ok true).
  have hk_lt : k.toNat < l.val.size := by
    rcases Nat.lt_or_ge k.toNat l.val.size with hlt | hge
    · exact hlt
    · exfalso
      have h_cond : decide (k ≥ (USize64.ofNat l.val.size)) = true := by
        rw [decide_eq_true_iff]
        change (USize64.ofNat l.val.size) ≤ k
        rw [USize64.le_iff_toNat_le, h_n_toNat]
        exact hge
      simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
                 pure_bind, rust_primitives.cmp.ge, h_cond, ↓reduceIte] at h
      cases h
  refine ⟨hk_lt, ?_⟩
  -- Now reduce the body: k < size means the early-exit branch is false.
  have h_cond_f : decide (k ≥ (USize64.ofNat l.val.size)) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    change (USize64.ofNat l.val.size) ≤ k at hle
    rw [USize64.le_iff_toNat_le, h_n_toNat] at hle
    omega
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             pure_bind, RustM_ok_bind, rust_primitives.cmp.ge,
             h_cond_f, Bool.false_eq_true, ↓reduceIte] at h
  -- Now h : (iss l k 0) >>= (fun b => if b then ok true else (k +? 1) >>= try_at l) = ok true.
  -- The iss must succeed (return ok of something).
  -- Generalize over the iss result via cases on the bind.
  generalize h_iss_eq : clever_108_move_one_ball.is_sorted_split_at l k (0 : usize) = iss_res
  rw [h_iss_eq] at h
  -- RustM Bool = Option (Except Error Bool); cases analyse the Option then Except then Bool.
  cases iss_res with
  | none =>
    exfalso
    simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, Option.bind] at h
    cases h
  | some res =>
    cases res with
    | error e =>
      exfalso
      simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, Option.bind] at h
      cases h
    | ok b =>
      cases b with
      | true =>
        left
        rfl
      | false =>
        right
        refine ⟨rfl, ?_⟩
        -- h : RustM.ok false >>= ... = ok true ⇒ unfolds to the else branch.
        simp only [show (some (Except.ok false) : RustM Bool) = RustM.ok false from rfl,
                   RustM_ok_bind, Bool.false_eq_true, ↓reduceIte] at h
        have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
        have h_k1_lt : k.toNat + 1 < 2^64 := by omega
        have h_add_1 : (k +? (1 : usize) : RustM usize) = pure (k + 1) :=
          add_one_pure_usize k h_k1_lt
        rw [h_add_1] at h
        simp only [pure_bind] at h
        exact h

/-- Strong-induction: find a witness from `try_at l k_start = ok true`. -/
private theorem ta_find_witness (l : RustSlice i64) :
    ∀ (m : Nat) (k_start : usize),
      l.val.size - k_start.toNat ≤ m →
      clever_108_move_one_ball.try_at l k_start = RustM.ok true →
      ∃ k₀ : usize, k_start.toNat ≤ k₀.toNat ∧ k₀.toNat < l.val.size ∧
        clever_108_move_one_ball.is_sorted_split_at l k₀ (0 : usize) = RustM.ok true := by
  intro m
  induction m with
  | zero =>
    intro k_start hm h_ta
    rcases ta_step_ok_true l k_start h_ta with ⟨hk_lt, _⟩
    -- size - k_start ≤ 0 means k_start ≥ size, but hk_lt says k_start < size.
    omega
  | succ m ih =>
    intro k_start hm h_ta
    rcases ta_step_ok_true l k_start h_ta with ⟨hk_lt, h_match | ⟨_, h_rec⟩⟩
    · -- match at k_start
      exact ⟨k_start, Nat.le_refl _, hk_lt, h_match⟩
    · -- recurse on k_start + 1
      have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
      have h_k1_lt : k_start.toNat + 1 < 2^64 := by omega
      have h_k1_toNat : (k_start + 1).toNat = k_start.toNat + 1 :=
        usize_add_one_toNat k_start h_k1_lt
      have h_next_m : l.val.size - (k_start + 1).toNat ≤ m := by
        rw [h_k1_toNat]; omega
      obtain ⟨k₀, h_k₀_ge, h_k₀_lt, h_k₀_iss⟩ := ih (k_start + 1) h_next_m h_rec
      refine ⟨k₀, ?_, h_k₀_lt, h_k₀_iss⟩
      rw [h_k1_toNat] at h_k₀_ge; omega

theorem move_one_ball_sound
    (arr : RustSlice i64)
    (h : clever_108_move_one_ball.move_one_ball arr = RustM.ok true) :
    arr.val.size = 0 ∨
    ∃ k : Nat, ∃ (hk : k < arr.val.size), is_sorted_rotation arr k hk := by
  by_cases h_empty : arr.val.size = 0
  · left; exact h_empty
  · right
    have h_pos : 0 < arr.val.size := Nat.pos_of_ne_zero h_empty
    have h_size_lt : arr.val.size < 2^64 := arr.size_lt_usizeSize
    -- Reduce move_one_ball to try_at arr 0.
    have h_n_toNat : (USize64.ofNat arr.val.size).toNat = arr.val.size :=
      n_size_ofNat_toNat arr
    have h_n_ne_0 : (USize64.ofNat arr.val.size) ≠ 0 := by
      intro h_eq
      have : (USize64.ofNat arr.val.size).toNat = (0 : usize).toNat :=
        congrArg USize64.toNat h_eq
      rw [h_n_toNat, usize_zero_toNat] at this
      omega
    have h_mob_eq : clever_108_move_one_ball.move_one_ball arr =
        clever_108_move_one_ball.try_at arr (0 : usize) := by
      unfold clever_108_move_one_ball.move_one_ball
      unfold core_models.slice.Impl.is_empty
      unfold core_models.slice.Impl.len
      simp only [rust_primitives.slice.slice_length, pure_bind]
      have h_eq_cond :
          ((USize64.ofNat arr.val.size) ==? (0 : usize) : RustM Bool) =
            pure false := by
        show (rust_primitives.cmp.eq (USize64.ofNat arr.val.size) (0 : usize) : RustM Bool) =
              pure false
        simp only [rust_primitives.cmp.eq]
        show pure (((USize64.ofNat arr.val.size) == (0 : usize)) : Bool) = pure false
        rw [beq_eq_false_iff_ne.mpr h_n_ne_0]
      rw [h_eq_cond]
      simp only [pure_bind, Bool.false_eq_true, ↓reduceIte]
    rw [h_mob_eq] at h
    -- Extract a witness k₀ via ta_find_witness.
    obtain ⟨k₀, _, h_k₀_lt, h_k₀_iss⟩ := ta_find_witness arr arr.val.size (0 : usize)
      (by simp [usize_zero_toNat]) h
    -- Convert to the rotation property using iss_ok_true_implies_sorted_aux.
    refine ⟨k₀.toNat, h_k₀_lt, ?_⟩
    intro j hj1
    apply iss_ok_true_implies_sorted_aux arr k₀ arr.val.size (0 : usize)
      (by simp [usize_zero_toNat]) h_k₀_iss j
    · simp [usize_zero_toNat]
    · exact hj1

end Clever_108_move_one_ballObligations
