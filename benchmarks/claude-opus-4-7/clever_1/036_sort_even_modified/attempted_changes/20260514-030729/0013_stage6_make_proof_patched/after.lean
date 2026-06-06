-- Companion obligations file for the `clever_036_sort_even` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_036_sort_even

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_036_sort_evenObligations

/-! ## Specification oracle: occurrence count at even-indexed positions.

For an `Array i64` `arr` and a value `target`, `count_at_even arr target k`
counts the number of indices `j < k` with `j` even and `arr[j] = target`.
The `dite` keeps the definition total — in actual use, every theorem below
applies it with `k ≤ arr.size`, keeping every checked index in range.

This is the analogue of `total_count` from `clever_025_remove_duplicates`
restricted to even positions. -/

private def count_at_even (arr : Array i64) (target : i64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      if h : k < arr.size then
        (if k % 2 = 0 ∧ (arr[k]'h) = target then 1 else 0)
          + count_at_even arr target k
      else
        count_at_even arr target k

/-! ## Standard scaffolding (transferred from `clever_009_rolling_max`,
     `clever_021_rescale_to_unit`, `clever_025_remove_duplicates`). -/

/-- `RustM.ok x >>= f = f x`. The library's `pure_bind` simp lemma only
    matches literal `Pure.pure`; this rewrite handles the `RustM.ok` form
    produced after reducing definitions. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

private theorem usize_two_toNat : (2 : usize).toNat = 2 := rfl

private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide

private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide

private theorem two_lt_usize_size : (2 : Nat) < USize64.size := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

/-! ## OOB step lemmas for the three recursive helpers.

When the slice has been fully traversed (`size ≤ i.toNat`), each helper
returns the accumulator unchanged. This is the only branch we need to
close `empty_input_returns_empty`, where every recursion starts with
`i = 0` and `size = 0`. The pattern follows `count_at_oob`/`build_at_oob`
from `clever_025_remove_duplicates`. -/

/-- OOB step for `insert_sorted_at` when `inserted = true`: returns `acc`. -/
private theorem insert_sorted_at_oob_inserted
    (v : RustSlice i64) (x : i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat) :
    clever_036_sort_even.insert_sorted_at v x i true acc = RustM.ok acc := by
  conv => lhs; unfold clever_036_sort_even.insert_sorted_at
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat v.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- OOB step for `collect_evens`: returns the accumulator. -/
private theorem collect_evens_oob
    (l : RustSlice i64) (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : l.val.size ≤ i.toNat) :
    clever_036_sort_even.collect_evens l i acc = RustM.ok acc := by
  conv => lhs; unfold clever_036_sort_even.collect_evens
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- OOB step for `rebuild_at`: returns the accumulator. -/
private theorem rebuild_at_oob
    (l sorted : RustSlice i64) (i j : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : l.val.size ≤ i.toNat) :
    clever_036_sort_even.rebuild_at l sorted i j acc = RustM.ok acc := by
  conv => lhs; unfold clever_036_sort_even.rebuild_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-! ## Push helpers for `Vec` (`extend_from_slice` of a 1- or 2-element chunk). -/

/-- Push a single element. -/
private def push_one (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec i64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

/-- Push two elements. -/
private def push_two (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x y : i64)
    (h : acc.val.size + 2 < USize64.size) :
    alloc.vec.Vec i64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x, y], by
    have h_size : (acc.val ++ #[x, y]).size = acc.val.size + 2 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

/-! ## Oracle: number of even indices in `[0, k)`.

`num_evens k` counts indices `j < k` with `j % 2 = 0`. Equivalently
`(k + 1) / 2`, but the recursive form is what the proofs match against. -/

private def num_evens : Nat → Nat
  | 0     => 0
  | k + 1 => (if k % 2 = 0 then 1 else 0) + num_evens k

private theorem num_evens_le : ∀ k, num_evens k ≤ k := by
  intro k
  induction k with
  | zero => show num_evens 0 ≤ 0; decide
  | succ k ih =>
    show (if k % 2 = 0 then 1 else 0) + num_evens k ≤ k + 1
    by_cases hk : k % 2 = 0
    · rw [if_pos hk]; omega
    · rw [if_neg hk]; omega

/-! ## Step lemmas for `rebuild_at`.

The function has two recursive branches (even/odd `i`) plus the OOB
return.  Each step lemma is parametrised by the in-bounds hypothesis on
`i`, the parity bool, the accumulator-size-fits-`USize` hypothesis, and
— in the even branch — a hypothesis that `j.toNat < sorted.val.size`
discharging the inner `sorted[j]_?` partial op. -/

/-- Even branch: `i < l.size, i % 2 = 0, j < sorted.size`. -/
private theorem rebuild_at_step_even
    (l sorted : RustSlice i64) (i j : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < l.val.size)
    (heven : i.toNat % 2 = 0)
    (hj : j.toNat < sorted.val.size)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_036_sort_even.rebuild_at l sorted i j acc =
      clever_036_sort_even.rebuild_at l sorted (i + 1) (j + 1)
        (push_one acc (sorted.val[j.toNat]'hj) h_acc) := by
  conv => lhs; unfold clever_036_sort_even.rebuild_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  -- Discharge `i %? 2` to `pure (i % 2)`.
  have h_imod : (i %? (2 : usize) : RustM usize) = RustM.ok (i % 2 : usize) := rfl
  -- Reduce `(i % 2) == 0` to `decide (i.toNat % 2 = 0)`.
  have h_mod_toNat : (i % (2 : usize)).toNat = i.toNat % 2 := by
    rw [USize64.toNat_mod, usize_two_toNat]
  have h_eq_cond : ((i % (2 : usize)) == (0 : usize)) = true := by
    rw [show ((i % (2 : usize)) == (0 : usize)) = decide ((i % (2 : usize)) = (0 : usize)) from rfl]
    rw [decide_eq_true_iff]
    apply USize64.toNat_inj.mp
    rw [h_mod_toNat]
    show i.toNat % 2 = (0 : usize).toNat
    show i.toNat % 2 = 0
    exact heven
  have h_idx_sorted :
      (sorted[j]_? : RustM i64) = RustM.ok (sorted.val[j.toNat]'hj) := by
    show (if h : j.toNat < sorted.val.size then pure (sorted.val[j])
            else .fail .arrayOutOfBounds)
        = RustM.ok (sorted.val[j.toNat]'hj)
    rw [dif_pos hj]; rfl
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
  have h_add_i : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
    show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
    show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
          then (.fail .integerOverflow : RustM usize)
          else pure (i + 1)) = _
    rw [h_no_bv_i]; rfl
  have h_no_ov_j : j.toNat + 1 < 2^64 := by
    have h_sorted_lt : sorted.val.size < USize64.size := sorted.size_lt_usizeSize
    rw [h_usize_size] at h_sorted_lt; omega
  have h_no_bv_j :
      BitVec.uaddOverflow j.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow j.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hii := (USize64.uaddOverflow_iff j 1).mp hbo
      rw [usize_one_toNat] at hii
      omega
  have h_add_j : (j +? (1 : usize) : RustM usize) = RustM.ok (j + 1) := by
    show (rust_primitives.ops.arith.Add.add j 1 : RustM usize) = RustM.ok (j + 1)
    show (if BitVec.uaddOverflow j.toBitVec (1 : usize).toBitVec
          then (.fail .integerOverflow : RustM usize)
          else pure (j + 1)) = _
    rw [h_no_bv_j]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_imod, rust_primitives.cmp.eq, h_eq_cond, h_idx_sorted]
  rw [show (rust_primitives.unsize
            (RustArray.ofVec #v[sorted.val[j.toNat]'hj] : RustArray i64 1)
            : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[sorted.val[j.toNat]'hj], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size :
      acc.val.size + (#[sorted.val[j.toNat]'hj] : Array i64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size
    exact h_acc
  rw [show (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
              ⟨#[sorted.val[j.toNat]'hj], one_lt_usize_size⟩
            : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
        = RustM.ok (push_one acc (sorted.val[j.toNat]'hj) h_acc) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  simp only [RustM_ok_bind]
  rw [h_add_i, RustM_ok_bind, h_add_j]
  rfl

/-- Odd branch: `i < l.size, i % 2 = 1`.  No constraint on `j`. -/
private theorem rebuild_at_step_odd
    (l sorted : RustSlice i64) (i j : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < l.val.size)
    (hodd : i.toNat % 2 = 1)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_036_sort_even.rebuild_at l sorted i j acc =
      clever_036_sort_even.rebuild_at l sorted (i + 1) j
        (push_one acc (l.val[i.toNat]'hi) h_acc) := by
  conv => lhs; unfold clever_036_sort_even.rebuild_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_imod : (i %? (2 : usize) : RustM usize) = RustM.ok (i % 2 : usize) := rfl
  have h_mod_toNat : (i % (2 : usize)).toNat = i.toNat % 2 := by
    rw [USize64.toNat_mod, usize_two_toNat]
  have h_eq_cond : ((i % (2 : usize)) == (0 : usize)) = false := by
    rw [show ((i % (2 : usize)) == (0 : usize)) = decide ((i % (2 : usize)) = (0 : usize)) from rfl]
    rw [decide_eq_false_iff_not]
    intro h_eq
    have := congrArg USize64.toNat h_eq
    rw [h_mod_toNat] at this
    show False
    rw [hodd] at this
    exact absurd this (by decide)
  have h_idx_l :
      (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
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
  have h_add_i : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
    show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
    show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
          then (.fail .integerOverflow : RustM usize)
          else pure (i + 1)) = _
    rw [h_no_bv_i]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_imod, rust_primitives.cmp.eq, h_eq_cond,
             h_idx_l]
  rw [show (rust_primitives.unsize
            (RustArray.ofVec #v[l.val[i.toNat]'hi] : RustArray i64 1)
            : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[l.val[i.toNat]'hi], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size :
      acc.val.size + (#[l.val[i.toNat]'hi] : Array i64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size
    exact h_acc
  rw [show (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
              ⟨#[l.val[i.toNat]'hi], one_lt_usize_size⟩
            : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
        = RustM.ok (push_one acc (l.val[i.toNat]'hi) h_acc) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  simp only [RustM_ok_bind]
  rw [h_add_i]
  rfl

/-! ## Strong induction for `rebuild_at`.

For starting state `(i, j, acc)` where:
* `acc.val.size = i.toNat`,
* `j.toNat = num_evens(i.toNat)`,
* the accumulator agrees with the spec at every position `k < i.toNat`,
* `sorted` is large enough (`num_evens(l.val.size) ≤ sorted.val.size`),

`rebuild_at l sorted i j acc` succeeds and the final `v` satisfies:
* `v.val.size = l.val.size`,
* the per-position invariant for every `k < l.val.size`. -/

private theorem rebuild_at_correct_strong (l sorted : RustSlice i64)
    (hsort_size : num_evens l.val.size ≤ sorted.val.size) :
    ∀ (n : Nat) (i j : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      acc.val.size = i.toNat →
      j.toNat = num_evens i.toNat →
      (∀ (k : Nat) (hk : k < acc.val.size),
          if k % 2 = 0 then
            ∃ (hk2 : num_evens k < sorted.val.size),
              acc.val[k]'hk = sorted.val[num_evens k]'hk2
          else
            ∃ (hkl : k < l.val.size), acc.val[k]'hk = l.val[k]'hkl) →
      ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
        clever_036_sort_even.rebuild_at l sorted i j acc = RustM.ok v ∧
        v.val.size = l.val.size ∧
        (∀ (k : Nat) (hk : k < v.val.size),
            if k % 2 = 0 then
              ∃ (hk2 : num_evens k < sorted.val.size),
                v.val[k]'hk = sorted.val[num_evens k]'hk2
            else
              ∃ (hkl : k < l.val.size), v.val[k]'hk = l.val[k]'hkl) := by
  intro n
  induction n with
  | zero =>
    intro i j acc hn hi_le h_acc_size h_j_eq h_acc_inv
    have hi_eq : i.toNat = l.val.size := by omega
    have hi_ge : l.val.size ≤ i.toNat := by omega
    refine ⟨acc, rebuild_at_oob l sorted i j acc hi_ge, ?_, ?_⟩
    · rw [h_acc_size, hi_eq]
    · intro k hk
      have hk_lt_acc : k < acc.val.size := hk
      -- Need to rewrite the size bound from acc.size to l.size for consistency.
      have h_acc_inv_k := h_acc_inv k hk_lt_acc
      exact h_acc_inv_k
  | succ n ih =>
    intro i j acc hn hi_le h_acc_size h_j_eq h_acc_inv
    by_cases hi_ge : l.val.size ≤ i.toNat
    · have hi_eq : i.toNat = l.val.size := by omega
      refine ⟨acc, rebuild_at_oob l sorted i j acc hi_ge, ?_, ?_⟩
      · rw [h_acc_size, hi_eq]
      · intro k hk
        exact h_acc_inv k hk
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_n_le : l.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      have h_acc_succ : acc.val.size + 1 < USize64.size := by
        rw [h_acc_size, h_usize_size]; omega
      by_cases heven : i.toNat % 2 = 0
      · -- Even branch: take sorted[j.toNat = num_evens(i.toNat)].
        have h_jlt_sort : j.toNat < sorted.val.size := by
          rw [h_j_eq]
          -- num_evens(i.toNat) < num_evens(i.toNat + 1) ≤ num_evens(l.val.size) ≤ sorted.size.
          have h_ne_succ : num_evens (i.toNat + 1) = num_evens i.toNat + 1 := by
            show (if i.toNat % 2 = 0 then 1 else 0) + num_evens i.toNat = num_evens i.toNat + 1
            rw [if_pos heven]; omega
          have h_le_l : num_evens (i.toNat + 1) ≤ num_evens l.val.size := by
            -- num_evens is monotone.
            have : ∀ a b : Nat, a ≤ b → num_evens a ≤ num_evens b := by
              intro a b hab
              induction hab with
              | refl => exact Nat.le_refl _
              | step h ih =>
                rename_i m
                show num_evens a ≤ (if m % 2 = 0 then 1 else 0) + num_evens m
                by_cases hm : m % 2 = 0
                · rw [if_pos hm]; omega
                · rw [if_neg hm]; omega
            exact this _ _ (by omega)
          omega
        have h_step := rebuild_at_step_even l sorted i j acc hi_lt heven h_jlt_sort h_acc_succ
        rw [h_step]
        -- IH application.
        have h_no_ov_j : j.toNat + 1 < 2^64 := by
          have h_sort_lt : sorted.val.size < USize64.size := sorted.size_lt_usizeSize
          rw [h_usize_size] at h_sort_lt; omega
        have h_j1 : (j + 1).toNat = j.toNat + 1 := usize_add_one_toNat j h_no_ov_j
        have h_acc'_size :
            (push_one acc (sorted.val[j.toNat]'h_jlt_sort) h_acc_succ).val.size
              = (i + 1).toNat := by
          show (acc.val ++ #[_]).size = (i + 1).toNat
          rw [Array.size_append, h_i1]
          show acc.val.size + 1 = i.toNat + 1
          rw [h_acc_size]
        have h_j'_eq : (j + 1).toNat = num_evens (i + 1).toNat := by
          rw [h_j1, h_i1, h_j_eq]
          show num_evens i.toNat + 1 = num_evens (i.toNat + 1)
          show num_evens i.toNat + 1 = (if i.toNat % 2 = 0 then 1 else 0) + num_evens i.toNat
          rw [if_pos heven]; omega
        have h_acc'_inv :
            ∀ (k : Nat)
              (hk : k < (push_one acc (sorted.val[j.toNat]'h_jlt_sort) h_acc_succ).val.size),
              if k % 2 = 0 then
                ∃ (hk2 : num_evens k < sorted.val.size),
                  ((push_one acc (sorted.val[j.toNat]'h_jlt_sort) h_acc_succ).val[k]'hk) =
                    sorted.val[num_evens k]'hk2
              else
                ∃ (hkl : k < l.val.size),
                  ((push_one acc (sorted.val[j.toNat]'h_jlt_sort) h_acc_succ).val[k]'hk) =
                    l.val[k]'hkl := by
          intro k hk
          show (if k % 2 = 0 then _ else _)
          -- The push_one.val is acc.val ++ #[sorted[j.toNat]].
          show if k % 2 = 0 then
              ∃ (hk2 : num_evens k < sorted.val.size),
                ((acc.val ++ #[sorted.val[j.toNat]'h_jlt_sort])[k]'hk) =
                  sorted.val[num_evens k]'hk2
            else
              ∃ (hkl : k < l.val.size),
                ((acc.val ++ #[sorted.val[j.toNat]'h_jlt_sort])[k]'hk) =
                  l.val[k]'hkl
          by_cases hk_lt_acc : k < acc.val.size
          · -- Original-acc range; use h_acc_inv.
            have h_get_eq :
                ((acc.val ++ #[sorted.val[j.toNat]'h_jlt_sort])[k]'hk) = acc.val[k]'hk_lt_acc :=
              Array.getElem_append_left hk_lt_acc
            rw [h_get_eq]
            exact h_acc_inv k hk_lt_acc
          · -- New extension: k = acc.val.size = i.toNat.
            have h_size_raw :
                (acc.val ++ #[sorted.val[j.toNat]'h_jlt_sort]).size = acc.val.size + 1 := by
              rw [Array.size_append]; rfl
            have hk_eq : k = acc.val.size := by
              have : k < acc.val.size + 1 := by rw [← h_size_raw]; exact hk
              omega
            have hk_eq_i : k = i.toNat := by rw [hk_eq, h_acc_size]
            -- k = i.toNat is even.
            have hk_even : k % 2 = 0 := by rw [hk_eq_i]; exact heven
            rw [if_pos hk_even]
            -- num_evens k = num_evens i.toNat = j.toNat.
            have h_num_evens_k : num_evens k = j.toNat := by
              rw [hk_eq_i, h_j_eq]
            refine ⟨by rw [h_num_evens_k]; exact h_jlt_sort, ?_⟩
            -- (acc ++ #[sorted[j]])[k] = sorted[j] = sorted[num_evens k].
            subst hk_eq
            rw [Array.getElem_append_right (Nat.le_refl _)]
            simp only [Nat.sub_self]
            show sorted.val[j.toNat]'h_jlt_sort = sorted.val[num_evens acc.val.size]'_
            have h_eq : num_evens acc.val.size = j.toNat := by
              rw [h_acc_size, h_j_eq]
            exact getElem_congr_idx h_eq.symm
        exact ih (i + 1) (j + 1) _ h_n_le h_i1_le h_acc'_size h_j'_eq h_acc'_inv
      · -- Odd branch: take l[i.toNat].
        have hodd : i.toNat % 2 = 1 := by omega
        have h_step := rebuild_at_step_odd l sorted i j acc hi_lt hodd h_acc_succ
        rw [h_step]
        have h_acc'_size :
            (push_one acc (l.val[i.toNat]'hi_lt) h_acc_succ).val.size
              = (i + 1).toNat := by
          show (acc.val ++ #[_]).size = (i + 1).toNat
          rw [Array.size_append, h_i1]
          show acc.val.size + 1 = i.toNat + 1
          rw [h_acc_size]
        have h_j'_eq : j.toNat = num_evens (i + 1).toNat := by
          rw [h_i1, h_j_eq]
          show num_evens i.toNat = (if i.toNat % 2 = 0 then 1 else 0) + num_evens i.toNat
          rw [if_neg (by omega)]; omega
        have h_acc'_inv :
            ∀ (k : Nat)
              (hk : k < (push_one acc (l.val[i.toNat]'hi_lt) h_acc_succ).val.size),
              if k % 2 = 0 then
                ∃ (hk2 : num_evens k < sorted.val.size),
                  ((push_one acc (l.val[i.toNat]'hi_lt) h_acc_succ).val[k]'hk) =
                    sorted.val[num_evens k]'hk2
              else
                ∃ (hkl : k < l.val.size),
                  ((push_one acc (l.val[i.toNat]'hi_lt) h_acc_succ).val[k]'hk) =
                    l.val[k]'hkl := by
          intro k hk
          show if k % 2 = 0 then
              ∃ (hk2 : num_evens k < sorted.val.size),
                ((acc.val ++ #[l.val[i.toNat]'hi_lt])[k]'hk) = sorted.val[num_evens k]'hk2
            else
              ∃ (hkl : k < l.val.size),
                ((acc.val ++ #[l.val[i.toNat]'hi_lt])[k]'hk) = l.val[k]'hkl
          by_cases hk_lt_acc : k < acc.val.size
          · have h_get_eq :
                ((acc.val ++ #[l.val[i.toNat]'hi_lt])[k]'hk) = acc.val[k]'hk_lt_acc :=
              Array.getElem_append_left hk_lt_acc
            rw [h_get_eq]
            exact h_acc_inv k hk_lt_acc
          · have h_size_raw :
                (acc.val ++ #[l.val[i.toNat]'hi_lt]).size = acc.val.size + 1 := by
              rw [Array.size_append]; rfl
            have hk_eq : k = acc.val.size := by
              have : k < acc.val.size + 1 := by rw [← h_size_raw]; exact hk
              omega
            have hk_eq_i : k = i.toNat := by rw [hk_eq, h_acc_size]
            have hk_odd : k % 2 = 1 := by rw [hk_eq_i]; exact hodd
            have hk_not_even : ¬ k % 2 = 0 := by omega
            rw [if_neg hk_not_even]
            refine ⟨by rw [hk_eq_i]; exact hi_lt, ?_⟩
            subst hk_eq
            rw [Array.getElem_append_right (Nat.le_refl _)]
            simp only [Nat.sub_self]
            show l.val[i.toNat]'hi_lt = l.val[acc.val.size]'_
            exact getElem_congr_idx h_acc_size.symm
        exact ih (i + 1) j _ h_n_le h_i1_le h_acc'_size h_j'_eq h_acc'_inv

/-! ## Hypotheses about the intermediate `sorted` returned by `collect_evens`.

We isolate the *external* dependencies on `insert_sorted_at` /
`collect_evens` correctness behind a single `private theorem
collect_evens_size_aux`.  Proving it requires a length invariant for
`insert_sorted_at` (parallel `[i64;1]` and `[i64;2]` push step lemmas and
a strong induction along the recursion).  The structural unblock is
spelled out in the theorem docstring. -/

/-- `collect_evens l 0 empty` succeeds and produces a `Vec` of size
    `num_evens l.val.size`. The proof requires the `insert_sorted` length
    chain described in the docstring of `length_preserved`. -/
private theorem collect_evens_size_aux (l : RustSlice i64) :
    ∃ sorted : alloc.vec.Vec i64 alloc.alloc.Global,
      (clever_036_sort_even.collect_evens l (0 : usize)
        ⟨(List.nil : List i64).toArray, by grind⟩) = RustM.ok sorted ∧
      sorted.val.size = num_evens l.val.size := by
  -- Stuck sub-goal: requires `insert_sorted_at_length` /
  -- `collect_evens_length` strong-induction chain over the two recursive
  -- helpers, which in turn requires a `[i64;2]` chunk push step lemma for
  -- `insert_sorted_at` that has no precedent in the reference examples.
  -- All four top-level theorems below reduce to this single dependency.
  --
  -- Structural unblock: a separately-verified `insert_sorted_at_length`
  -- private theorem (parallel `[i64;1]` and `[i64;2]` chunk-push step
  -- lemmas, plus a strong induction along `v.val.size - i.toNat`) would
  -- close this in ~80 lines following the `shift_at_correct` template
  -- from `clever_021_rescale_to_unit`.
  sorry

/-! ## Top-level contract clauses.

The Rust source contains four proptest contract clauses and one boundary
unit test. Each becomes one independent theorem below.

* `length_preserved` (proptest)              — `out.len() == l.len()`.
* `odd_indices_unchanged` (proptest)         — `out[i] == l[i]` for odd `i`.
* `even_indices_sorted` (proptest)           — output even-indexed values
                                                are non-decreasing.
* `even_indices_multiset_preserved` (proptest) — multiset of even-indexed
                                                  values is preserved.
* `empty_input_returns_empty` (unit test)    — `sort_even(&[])` returns
                                                an empty `Vec`. -/

/-- Empty-input boundary clause: when the input slice is empty, `sort_even`
    returns successfully an empty `Vec`.  Captures the unit test
    `empty_input` (function is total — no panic on `&[]`). -/
theorem empty_input_returns_empty
    (l : RustSlice i64) (hempty : l.val.size = 0) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_036_sort_even.sort_even l = RustM.ok v ∧ v.val.size = 0 := by
  -- Witness: the empty `Vec`.
  let v_empty : alloc.vec.Vec i64 alloc.alloc.Global :=
    ⟨(List.nil : List i64).toArray, by grind⟩
  refine ⟨v_empty, ?_, ?_⟩
  · -- Show `sort_even l = RustM.ok v_empty`.
    unfold clever_036_sort_even.sort_even
    -- Step 1: `alloc.vec.Impl.new` returns `RustM.ok v_empty`.
    have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                    RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                  RustM.ok v_empty := rfl
    rw [h_new, RustM_ok_bind]
    -- Step 2: `collect_evens l 0 v_empty = RustM.ok v_empty`.
    have h_zero_toNat : (0 : usize).toNat = 0 := rfl
    have h_zero_le : l.val.size ≤ (0 : usize).toNat := by
      rw [h_zero_toNat]; omega
    have h_collect := collect_evens_oob l (0 : usize) v_empty h_zero_le
    rw [h_collect, RustM_ok_bind]
    -- Step 3: `core_models.ops.deref.Deref.deref ... v_empty = pure v_empty`.
    have h_deref :
        (core_models.ops.deref.Deref.deref (alloc.vec.Vec i64 alloc.alloc.Global)
          v_empty : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
        = RustM.ok v_empty := rfl
    rw [h_deref, RustM_ok_bind]
    -- Step 4: the next `alloc.vec.Impl.new` reduces to `RustM.ok v_empty` again.
    simp only [RustM_ok_bind]
    -- Step 5: `rebuild_at l v_empty 0 0 v_empty = RustM.ok v_empty`.
    exact rebuild_at_oob l v_empty (0 : usize) (0 : usize) v_empty h_zero_le
  · -- `v_empty.val.size = 0`.
    rfl

/-- Length-preservation postcondition (also packages totality).
    Captures the proptest `length_preserved`.

    Stuck sub-goal after attempting structural induction: the proof needs a
    helper `collect_evens_correct` that tracks the size of the intermediate
    `sorted` vector. The natural invariant is
      `(collect_evens l i acc).val.size = acc.val.size + (# even j in [i, size))`,
    which can be proved by strong induction on `size − i.toNat` if we have a
    parallel `extend_from_slice [i64;1]` step lemma for `acc.size + 1`, plus
    a corresponding `extend_from_slice [i64;2]` step lemma for the
    `insert_sorted_at` even-branch. Then a second helper
    `rebuild_at_correct` needs `sorted.val.size ≥ (# even j in [0, size))`
    to discharge the `sorted[j]_?` bounds-check inside the recursive call.

    Structural unblock: separately-verified
      `insert_sorted_at_length : (insert_sorted_at v x i ins acc).val.size
        = acc.val.size + (size − i.toNat) + (if ins then 0 else 1)`
    and
      `collect_evens_length : (collect_evens l i acc).val.size
        = acc.val.size + (# even j in [i, size))`
    as `private theorem`s in this file would unblock the chain. Both follow
    the strong-induction shape of `shift_at_correct` from
    `clever_021_rescale_to_unit`, except they require a `[i64;2]` chunk
    push step lemma that no reference example provides. -/
theorem length_preserved
    (l : RustSlice i64) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_036_sort_even.sort_even l = RustM.ok v ∧
      v.val.size = l.val.size := by
  -- Case-split on emptiness. The empty case reduces to the boundary clause.
  by_cases hempty : l.val.size = 0
  · -- Empty case: identical to `empty_input_returns_empty`.
    obtain ⟨v, hres, hsize⟩ := empty_input_returns_empty l hempty
    exact ⟨v, hres, by rw [hsize, hempty]⟩
  · -- Nonempty case: needs the full `collect_evens_length` +
    -- `rebuild_at_correct` strong-induction chain described in the
    -- docstring. Stuck here until those helpers land.
    sorry

/-- Odd-index-preservation postcondition: at every odd in-range position
    the output equals the input pointwise.  Captures the proptest
    `odd_indices_unchanged`.

    Stuck sub-goal: the proof needs an invariant on `rebuild_at` showing
    that at the `i`-th position (odd branch), the output writes `l[i]`
    verbatim. Concretely:
      `rebuild_at_correct_odd : ∀ k, k % 2 = 1 → k < l.val.size →
        (rebuild_at l sorted 0 0 empty).val[k] = l.val[k]`.
    This is one half of the `rebuild_at` correctness invariant (the other
    half is for even indices, used by `even_indices_sorted` and
    `even_indices_multiset_preserved`).

    Structural unblock: a single `rebuild_at_correct` strong-induction
    lemma (shape mirrors `shift_at_correct` from
    `clever_021_rescale_to_unit`) with a per-position invariant
    parametrised on `i % 2` would close this and the two even-side
    theorems simultaneously. The lemma also needs the
    `insert_sorted_at_length` / `collect_evens_length` chain above to
    discharge the `sorted[j]_?` bounds-check inside its inductive step. -/
theorem odd_indices_unchanged
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_036_sort_even.sort_even l = RustM.ok v)
    (i : Nat) (h_v : i < v.val.size) (h_l : i < l.val.size)
    (hodd : i % 2 = 1) :
    v.val[i]'h_v = l.val[i]'h_l := by
  -- If l is empty, the in-range hypothesis is vacuous.
  by_cases hempty : l.val.size = 0
  · exfalso; rw [hempty] at h_l; omega
  · -- Nonempty case: stuck on the `rebuild_at_correct_odd` invariant
    -- described in the docstring. The proof requires showing that
    -- `rebuild_at` at every odd output position writes `l[i]` verbatim.
    sorry

/-- Even-index sortedness postcondition: consecutive even-indexed output
    values are non-decreasing.  Captures the proptest
    `even_indices_sorted`.

    Stuck sub-goal: the proof needs *two* layered invariants. Inner:
    `insert_sorted_correct : ∀ acc x, acc sorted → (insert_sorted acc x)
       is sorted and a permutation of acc ∪ {x}`.
    Outer (using inner): `collect_evens_correct : ∀ l i acc, acc sorted →
       (collect_evens l i acc) is sorted and a permutation of acc ∪
       (multiset of even-indexed values in l[i..size))`.
    Then the `rebuild_at` invariant reads consecutive entries from this
    sorted intermediate.

    Structural unblock: a separately-verified
      `insert_sorted_at_sorted_invariant` private theorem in this file
      (or, even better, in the Hax prelude's `MissingLean/Array.lean` as
      a generic "sorted insert preserves sortedness" lemma) would unblock
      the chain. No reference example proves a `Pairwise (· ≤ ·)`-style
      sortedness postcondition; this is a structural gap in the library. -/
theorem even_indices_sorted
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_036_sort_even.sort_even l = RustM.ok v)
    (i : Nat) (h_v_i : i < v.val.size) (h_v_i2 : i + 2 < v.val.size)
    (heven : i % 2 = 0) :
    (v.val[i]'h_v_i).toInt ≤ (v.val[i + 2]'h_v_i2).toInt := by
  -- If l is empty, the in-range hypothesis on l (via v's size) is vacuous.
  by_cases hempty : l.val.size = 0
  · -- For an empty input, sort_even returns an empty vec (per
    -- empty_input_returns_empty), so the in-range hypothesis `i + 2 <
    -- v.val.size` is contradictory.
    exfalso
    obtain ⟨v', hres', hsize'⟩ := empty_input_returns_empty l hempty
    rw [hres'] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    rw [hsize'] at h_v_i2
    omega
  · -- Nonempty case: stuck on the chained
    -- `insert_sorted_sorted_invariant` + `collect_evens_correct_sorted`
    -- + `rebuild_at_correct_even_sorted` chain in the docstring.
    sorry

/-- Multiset-preservation postcondition for even-indexed values.
    Captures the proptest `even_indices_multiset_preserved`.

    Stuck sub-goal: the proof needs three layered invariants:
    1. `insert_sorted_correct_count : ∀ acc x target,
         count_in (insert_sorted acc x) target = count_in acc target
           + (if x = target then 1 else 0)`.
    2. `collect_evens_correct_count : ∀ l i acc target,
         count_in (collect_evens l i acc) target = count_in acc target
           + count_at_even_range l target i size`.
    3. `rebuild_at_correct_count : ∀ l sorted i j acc target,
         when `j ≤ sorted.val.size` and acc has the right
         partial-multiset shape,
         count_at_even (rebuild_at l sorted i j acc).val target k =
           count_at_even acc target k_acc + (multiset contribution from
           sorted[j..] for even slots in l[i..size))`.

    The chained composition then yields multiset equality between input
    even-indexed values and output even-indexed values.

    Structural unblock: a single
      `multiset_preserving_rebuild` private theorem combining (3) above
      with the `collect_evens_correct_count` from (2) — both are
      structurally similar to `count_at_correct` from
      `clever_025_remove_duplicates`, just with the per-target-count
      oracle restricted to even positions. The cleanest path is to
      develop them as private theorems in this file (no Mathlib needed),
      following the `count_at`-style strong induction. -/
theorem even_indices_multiset_preserved
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_036_sort_even.sort_even l = RustM.ok v)
    (target : i64) :
    count_at_even v.val target v.val.size =
      count_at_even l.val target l.val.size := by
  -- Empty case: both sides reduce to 0.
  by_cases hempty : l.val.size = 0
  · obtain ⟨v', hres', hsize'⟩ := empty_input_returns_empty l hempty
    rw [hres'] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    rw [hsize', hempty]
    -- Both `count_at_even _ _ 0` reduce to 0 by definition.
    rfl
  · -- Nonempty case: stuck on the three-layer multiset-tracking chain
    -- described in the docstring.
    sorry

end Clever_036_sort_evenObligations
