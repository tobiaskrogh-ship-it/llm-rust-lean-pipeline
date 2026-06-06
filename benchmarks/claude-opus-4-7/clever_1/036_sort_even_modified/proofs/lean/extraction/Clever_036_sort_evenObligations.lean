-- Companion obligations file for the `clever_036_sort_even` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

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

/-! ## Specification oracle for the multiset clause.

`count_evens s target k` is the number of indices `j < k` for which
`j` is even and `s[j] = target`. The `dite` on `j < s.size` keeps the
definition total — every theorem below applies it with `k = s.size`,
so the bounded indices always exist. Pattern reused from
`clever_025_remove_duplicates`'s `total_count`. -/

private def count_evens (s : Array i64) (target : i64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      if h : k < s.size then
        (if k % 2 = 0 ∧ (s[k]'h) = target then 1 else 0)
          + count_evens s target k
      else
        count_evens s target k

/-- `total_count s target k` counts indices `j < k` for which `s[j] = target`,
    independent of parity. Used to bridge `collect_evens`'s output (which is a
    flat array of values) to `count_evens` at even positions of the
    `rebuild_at` output. -/
private def total_count (s : Array i64) (target : i64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      if h : k < s.size then
        (if (s[k]'h) = target then 1 else 0) + total_count s target k
      else
        total_count s target k

/-! ## Standard scaffolding. -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

private theorem usize_zero_toNat : (0 : usize).toNat = 0 := rfl

private theorem usize_two_toNat : (2 : usize).toNat = 2 := rfl

private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide

private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide

private theorem two_lt_usize_size : (2 : Nat) < USize64.size := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

private theorem usize_add_one_ok (i : usize) (h : i.toNat + 1 < 2^64) :
    (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
  show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
  show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure (i + 1)) = _
  have h_no_bv :
      BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hii := (USize64.uaddOverflow_iff i 1).mp hbo
      rw [usize_one_toNat] at hii
      omega
  rw [h_no_bv]; rfl

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

/-! ## OOB lemmas for the three `partial_fixpoint` helpers. -/

private theorem insert_sorted_at_oob_inserted (v : RustSlice i64) (i : usize) (x : i64)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat) :
    clever_036_sort_even.insert_sorted_at v i x true acc = RustM.ok acc := by
  unfold clever_036_sort_even.insert_sorted_at
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat v.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]; rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, ↓reduceIte,
             rust_primitives.hax.logical_op.not, Bool.not_true,
             Bool.false_eq_true]
  rfl

private theorem insert_sorted_at_oob_not_inserted (v : RustSlice i64) (i : usize) (x : i64)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_036_sort_even.insert_sorted_at v i x false acc =
      RustM.ok (push_one acc x h_acc) := by
  unfold clever_036_sort_even.insert_sorted_at
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat v.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]; rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  have h_app_size :
      acc.val.size + (#[x] : Array i64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  have h_extend :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[x], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.ok (push_one acc x h_acc) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, ↓reduceIte,
             rust_primitives.hax.logical_op.not, Bool.not_false,
             ↓reduceIte]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[x] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[x], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend]
  rfl

private theorem collect_evens_oob (l : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : l.val.size ≤ i.toNat) :
    clever_036_sort_even.collect_evens l i acc = RustM.ok acc := by
  unfold clever_036_sort_even.collect_evens
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]; rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

private theorem rebuild_at_oob (l : RustSlice i64) (sorted : RustSlice i64)
    (i j : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : l.val.size ≤ i.toNat) :
    clever_036_sort_even.rebuild_at l sorted i j acc = RustM.ok acc := by
  unfold clever_036_sort_even.rebuild_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]; rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-! ## Modular arithmetic helper.

`(i %? (2 : usize)) == (0 : usize)` reduces to `decide (i.toNat % 2 = 0)`. -/

private theorem usize_mod_two_ok (i : usize) :
    (i %? (2 : usize) : RustM usize) = RustM.ok (i % (2 : usize)) := by
  show (rust_primitives.ops.arith.Rem.rem i (2 : usize) : RustM usize) = RustM.ok _
  show (if (2 : usize) = 0 then (.fail .divisionByZero : RustM usize)
         else pure (i % 2)) = _
  have h_ne : (2 : usize) ≠ 0 := by decide
  rw [if_neg h_ne]; rfl

private theorem usize_mod_two_toNat (i : usize) :
    (i % (2 : usize)).toNat = i.toNat % 2 := by
  show ((⟨i.toBitVec % (2 : usize).toBitVec⟩ : USize64)).toNat = _
  show (i.toBitVec % (2 : usize).toBitVec).toNat = i.toNat % 2
  rw [BitVec.toNat_umod]
  rfl

private theorem usize_mod_two_eq_zero_iff (i : usize) :
    ((i % (2 : usize)) == (0 : usize)) = decide (i.toNat % 2 = 0) := by
  by_cases h : i.toNat % 2 = 0
  · rw [decide_eq_true h]
    have : i % (2 : usize) = (0 : usize) := by
      apply USize64.toNat_inj.mp
      rw [usize_mod_two_toNat, usize_zero_toNat]
      exact h
    rw [this]; rfl
  · rw [decide_eq_false h]
    have h_ne : i % (2 : usize) ≠ (0 : usize) := by
      intro heq
      apply h
      have := congrArg USize64.toNat heq
      rw [usize_mod_two_toNat, usize_zero_toNat] at this
      exact this
    rw [show ((i % (2 : usize)) == (0 : usize)) = false from by
          rw [beq_eq_false_iff_ne]; exact h_ne]

/-! ## Step lemmas for `rebuild_at`. -/

private theorem rebuild_at_step_even (l : RustSlice i64) (sorted : RustSlice i64)
    (i j : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
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
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_size_lt_s : sorted.val.size < USize64.size := sorted.size_lt_usizeSize
  have h_no_ov_j : j.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt_s; omega
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_mod : (i %? (2 : usize) : RustM usize) = RustM.ok (i % (2 : usize)) :=
    usize_mod_two_ok i
  have h_mod_zero : ((i % (2 : usize)) == (0 : usize)) = true := by
    rw [usize_mod_two_eq_zero_iff]; exact decide_eq_true heven
  have h_idx_s : (sorted[j]_? : RustM i64) = RustM.ok (sorted.val[j.toNat]'hj) := by
    show (if h : j.toNat < sorted.val.size then pure (sorted.val[j])
            else .fail .arrayOutOfBounds)
        = RustM.ok (sorted.val[j.toNat]'hj)
    rw [dif_pos hj]; rfl
  have h_add_i : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
    usize_add_one_ok i h_no_ov_i
  have h_add_j : (j +? (1 : usize) : RustM usize) = RustM.ok (j + 1) :=
    usize_add_one_ok j h_no_ov_j
  have h_app_size :
      acc.val.size + (#[sorted.val[j.toNat]'hj] : Array i64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  have h_extend :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[sorted.val[j.toNat]'hj], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.ok (push_one acc (sorted.val[j.toNat]'hj) h_acc) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_mod, rust_primitives.cmp.eq, h_mod_zero,
             h_idx_s]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[sorted.val[j.toNat]'hj] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[sorted.val[j.toNat]'hj], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend]
  simp only [RustM_ok_bind]
  rw [h_add_i, h_add_j]
  simp only [RustM_ok_bind]

private theorem rebuild_at_step_odd (l : RustSlice i64) (sorted : RustSlice i64)
    (i j : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < l.val.size)
    (hodd : i.toNat % 2 = 1)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_036_sort_even.rebuild_at l sorted i j acc =
      clever_036_sort_even.rebuild_at l sorted (i + 1) j
        (push_one acc (l.val[i.toNat]'hi) h_acc) := by
  conv => lhs; unfold clever_036_sort_even.rebuild_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_mod : (i %? (2 : usize) : RustM usize) = RustM.ok (i % (2 : usize)) :=
    usize_mod_two_ok i
  have h_mod_one : ((i % (2 : usize)) == (0 : usize)) = false := by
    rw [usize_mod_two_eq_zero_iff]
    exact decide_eq_false (by omega)
  have h_idx_l : (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_add_i : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
    usize_add_one_ok i h_no_ov_i
  have h_app_size :
      acc.val.size + (#[l.val[i.toNat]'hi] : Array i64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  have h_extend :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[l.val[i.toNat]'hi], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.ok (push_one acc (l.val[i.toNat]'hi) h_acc) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_mod, rust_primitives.cmp.eq, h_mod_one,
             h_idx_l]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[l.val[i.toNat]'hi] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[l.val[i.toNat]'hi], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend]
  simp only [RustM_ok_bind]
  rw [h_add_i]
  simp only [RustM_ok_bind]

/-! ## Step lemmas for `collect_evens`. -/

private theorem collect_evens_step_even (l : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < l.val.size)
    (heven : i.toNat % 2 = 0) :
    clever_036_sort_even.collect_evens l i acc =
      (do
        let acc' ← clever_036_sort_even.insert_sorted acc (l.val[i.toNat]'hi)
        clever_036_sort_even.collect_evens l (i + 1) acc') := by
  conv => lhs; unfold clever_036_sort_even.collect_evens
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_mod : (i %? (2 : usize) : RustM usize) = RustM.ok (i % (2 : usize)) :=
    usize_mod_two_ok i
  have h_mod_zero : ((i % (2 : usize)) == (0 : usize)) = true := by
    rw [usize_mod_two_eq_zero_iff]; exact decide_eq_true heven
  have h_idx_l : (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_add_i : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
    usize_add_one_ok i h_no_ov_i
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_mod, rust_primitives.cmp.eq, h_mod_zero,
             h_idx_l]
  rw [h_add_i]
  simp only [RustM_ok_bind]

private theorem collect_evens_step_odd (l : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < l.val.size)
    (hodd : i.toNat % 2 = 1) :
    clever_036_sort_even.collect_evens l i acc =
      clever_036_sort_even.collect_evens l (i + 1) acc := by
  conv => lhs; unfold clever_036_sort_even.collect_evens
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_mod : (i %? (2 : usize) : RustM usize) = RustM.ok (i % (2 : usize)) :=
    usize_mod_two_ok i
  have h_mod_one : ((i % (2 : usize)) == (0 : usize)) = false := by
    rw [usize_mod_two_eq_zero_iff]
    exact decide_eq_false (by omega)
  have h_add_i : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
    usize_add_one_ok i h_no_ov_i
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_mod, rust_primitives.cmp.eq, h_mod_one]
  rw [h_add_i]
  simp only [RustM_ok_bind]

/-! ## Fail variants of step lemmas (used to derive preconditions from success). -/

private theorem rebuild_at_step_even_idx_fail (l : RustSlice i64) (sorted : RustSlice i64)
    (i j : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < l.val.size)
    (heven : i.toNat % 2 = 0)
    (hj : sorted.val.size ≤ j.toNat) :
    clever_036_sort_even.rebuild_at l sorted i j acc =
      RustM.fail .arrayOutOfBounds := by
  conv => lhs; unfold clever_036_sort_even.rebuild_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_mod : (i %? (2 : usize) : RustM usize) = RustM.ok (i % (2 : usize)) :=
    usize_mod_two_ok i
  have h_mod_zero : ((i % (2 : usize)) == (0 : usize)) = true := by
    rw [usize_mod_two_eq_zero_iff]; exact decide_eq_true heven
  have h_idx_fail : (sorted[j]_? : RustM i64) = RustM.fail .arrayOutOfBounds := by
    show (if h : j.toNat < sorted.val.size then pure (sorted.val[j])
            else .fail .arrayOutOfBounds)
        = RustM.fail .arrayOutOfBounds
    rw [dif_neg (Nat.not_lt.mpr hj)]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_mod, rust_primitives.cmp.eq, h_mod_zero,
             h_idx_fail]
  rfl

private theorem rebuild_at_step_even_size_fail (l : RustSlice i64) (sorted : RustSlice i64)
    (i j : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < l.val.size)
    (heven : i.toNat % 2 = 0)
    (hj : j.toNat < sorted.val.size)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_036_sort_even.rebuild_at l sorted i j acc =
      RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_036_sort_even.rebuild_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_mod : (i %? (2 : usize) : RustM usize) = RustM.ok (i % (2 : usize)) :=
    usize_mod_two_ok i
  have h_mod_zero : ((i % (2 : usize)) == (0 : usize)) = true := by
    rw [usize_mod_two_eq_zero_iff]; exact decide_eq_true heven
  have h_idx_s : (sorted[j]_? : RustM i64) = RustM.ok (sorted.val[j.toNat]'hj) := by
    show (if h : j.toNat < sorted.val.size then pure (sorted.val[j])
            else .fail .arrayOutOfBounds)
        = RustM.ok (sorted.val[j.toNat]'hj)
    rw [dif_pos hj]; rfl
  have h_app_size_neg :
      ¬ acc.val.size + (#[sorted.val[j.toNat]'hj] : Array i64).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[sorted.val[j.toNat]'hj], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_mod, rust_primitives.cmp.eq, h_mod_zero,
             h_idx_s]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[sorted.val[j.toNat]'hj] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[sorted.val[j.toNat]'hj], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

private theorem rebuild_at_step_odd_size_fail (l : RustSlice i64) (sorted : RustSlice i64)
    (i j : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < l.val.size)
    (hodd : i.toNat % 2 = 1)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_036_sort_even.rebuild_at l sorted i j acc =
      RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_036_sort_even.rebuild_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_mod : (i %? (2 : usize) : RustM usize) = RustM.ok (i % (2 : usize)) :=
    usize_mod_two_ok i
  have h_mod_one : ((i % (2 : usize)) == (0 : usize)) = false := by
    rw [usize_mod_two_eq_zero_iff]
    exact decide_eq_false (by omega)
  have h_idx_l : (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_app_size_neg :
      ¬ acc.val.size + (#[l.val[i.toNat]'hi] : Array i64).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[l.val[i.toNat]'hi], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_mod, rust_primitives.cmp.eq, h_mod_one,
             h_idx_l]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[l.val[i.toNat]'hi] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[l.val[i.toNat]'hi], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

/-! ## Size invariant for `rebuild_at`.

If `rebuild_at l sorted i j acc = ok r`, then `r.val.size = acc.val.size + (l.val.size - i.toNat)`.
The induction works because failure of any sub-step contradicts `hres = ok r`. -/

private theorem rebuild_at_size :
    ∀ (n : Nat) (l : RustSlice i64) (sorted : RustSlice i64)
      (i j : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      clever_036_sort_even.rebuild_at l sorted i j acc = RustM.ok r →
      r.val.size = acc.val.size + (l.val.size - i.toNat) := by
  intro n
  induction n with
  | zero =>
    intro l sorted i j acc r hm hi_le hres
    have hi_ge : l.val.size ≤ i.toNat := by omega
    rw [rebuild_at_oob l sorted i j acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    omega
  | succ n ih =>
    intro l sorted i j acc r hm hi_le hres
    by_cases hi_ge : l.val.size ≤ i.toNat
    · rw [rebuild_at_oob l sorted i j acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      omega
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_meas : l.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      by_cases heven : i.toNat % 2 = 0
      · -- Even case
        by_cases hj : j.toNat < sorted.val.size
        · by_cases h_acc : acc.val.size + 1 < USize64.size
          · rw [rebuild_at_step_even l sorted i j acc hi_lt heven hj h_acc] at hres
            have h_push_size :
                (push_one acc (sorted.val[j.toNat]'hj) h_acc).val.size = acc.val.size + 1 := by
              show (acc.val ++ #[sorted.val[j.toNat]'hj]).size = acc.val.size + 1
              rw [Array.size_append]; rfl
            have h_ind := ih l sorted (i + 1) (j + 1)
              (push_one acc (sorted.val[j.toNat]'hj) h_acc) r h_meas h_i1_le hres
            rw [h_push_size, h_i1] at h_ind
            omega
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 1 := by omega
            rw [rebuild_at_step_even_size_fail l sorted i j acc hi_lt heven hj h_big] at hres
            cases hres
        · exfalso
          have hj_ge : sorted.val.size ≤ j.toNat := Nat.le_of_not_lt hj
          rw [rebuild_at_step_even_idx_fail l sorted i j acc hi_lt heven hj_ge] at hres
          cases hres
      · -- Odd case
        have hodd : i.toNat % 2 = 1 := by omega
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [rebuild_at_step_odd l sorted i j acc hi_lt hodd h_acc] at hres
          have h_push_size :
              (push_one acc (l.val[i.toNat]'hi_lt) h_acc).val.size = acc.val.size + 1 := by
            show (acc.val ++ #[l.val[i.toNat]'hi_lt]).size = acc.val.size + 1
            rw [Array.size_append]; rfl
          have h_ind := ih l sorted (i + 1) j
            (push_one acc (l.val[i.toNat]'hi_lt) h_acc) r h_meas h_i1_le hres
          rw [h_push_size, h_i1] at h_ind
          omega
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [rebuild_at_step_odd_size_fail l sorted i j acc hi_lt hodd h_big] at hres
          cases hres

/-! ## Append lemmas for `count_evens` and `total_count`. -/

/-- `count_evens (acc ++ [x]) target (acc.size + 1) =
    count_evens acc target acc.size + (if acc.size even ∧ x = target then 1 else 0)`. -/
private theorem count_evens_append_singleton (acc : Array i64) (x target : i64) :
    count_evens (acc ++ #[x]) target (acc.size + 1) =
      count_evens acc target acc.size
        + (if acc.size % 2 = 0 ∧ x = target then 1 else 0) := by
  have h_size_app : (acc ++ #[x]).size = acc.size + 1 := by
    rw [Array.size_append]; rfl
  have h_lt : acc.size < (acc ++ #[x]).size := by rw [h_size_app]; omega
  show (if h : acc.size < (acc ++ #[x]).size then
          (if acc.size % 2 = 0 ∧ ((acc ++ #[x])[acc.size]'h) = target then 1 else 0)
            + count_evens (acc ++ #[x]) target acc.size
        else count_evens (acc ++ #[x]) target acc.size) =
        count_evens acc target acc.size
          + (if acc.size % 2 = 0 ∧ x = target then 1 else 0)
  rw [dif_pos h_lt]
  have h_get :
      (acc ++ #[x])[acc.size]'h_lt = x := by
    rw [Array.getElem_append_right (Nat.le_refl _)]
    simp
  rw [h_get]
  -- Need: count_evens (acc ++ [x]) target acc.size = count_evens acc target acc.size
  -- (since access positions < acc.size match acc by getElem_append_left)
  have h_prefix : count_evens (acc ++ #[x]) target acc.size = count_evens acc target acc.size := by
    -- Induction on k from 0 to acc.size; for k < acc.size, (acc ++ [x])[k] = acc[k]
    suffices h : ∀ k, k ≤ acc.size →
                  count_evens (acc ++ #[x]) target k = count_evens acc target k by
      exact h acc.size (Nat.le_refl _)
    intro k hk_le
    induction k with
    | zero => rfl
    | succ k ih =>
      have hk_lt : k < acc.size := by omega
      have hk_lt_app : k < (acc ++ #[x]).size := by rw [h_size_app]; omega
      have h_app : (acc ++ #[x])[k]'hk_lt_app = acc[k]'hk_lt := by
        exact Array.getElem_append_left hk_lt
      show (if h : k < (acc ++ #[x]).size then
              (if k % 2 = 0 ∧ ((acc ++ #[x])[k]'h) = target then 1 else 0)
                + count_evens (acc ++ #[x]) target k
            else count_evens (acc ++ #[x]) target k) =
          (if h : k < acc.size then
              (if k % 2 = 0 ∧ (acc[k]'h) = target then 1 else 0)
                + count_evens acc target k
            else count_evens acc target k)
      rw [dif_pos hk_lt_app, dif_pos hk_lt, h_app, ih (Nat.le_of_lt hk_le)]
  rw [h_prefix]
  omega

/-- `total_count s target (k+1) = total_count s target k + (if s[k] = target then 1 else 0)`
    when `k < s.size`. -/
private theorem total_count_succ (s : Array i64) (target : i64) (k : Nat) (hk : k < s.size) :
    total_count s target (k + 1) =
      (if (s[k]'hk) = target then 1 else 0) + total_count s target k := by
  show (if h : k < s.size then
          (if (s[k]'h) = target then 1 else 0) + total_count s target k
        else total_count s target k) = _
  rw [dif_pos hk]

/-- `count_evens s target (k+1) = count_evens s target k +
      (if k % 2 = 0 ∧ s[k] = target then 1 else 0)` when `k < s.size`. -/
private theorem count_evens_succ (s : Array i64) (target : i64) (k : Nat) (hk : k < s.size) :
    count_evens s target (k + 1) =
      (if k % 2 = 0 ∧ (s[k]'hk) = target then 1 else 0) + count_evens s target k := by
  show (if h : k < s.size then
          (if k % 2 = 0 ∧ (s[k]'h) = target then 1 else 0) + count_evens s target k
        else count_evens s target k) = _
  rw [dif_pos hk]

/-- Prefix-invariance of `total_count`: appending an element doesn't change counts at smaller indices. -/
private theorem total_count_prefix (acc : Array i64) (y target : i64) :
    ∀ k, k ≤ acc.size →
      total_count (acc ++ #[y]) target k = total_count acc target k := by
  have h_size_app : (acc ++ #[y]).size = acc.size + 1 := by rw [Array.size_append]; rfl
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk_lt : k < acc.size := by omega
    have hk_lt_app : k < (acc ++ #[y]).size := by rw [h_size_app]; omega
    have h_app : (acc ++ #[y])[k]'hk_lt_app = acc[k]'hk_lt :=
      Array.getElem_append_left hk_lt
    show (if h : k < (acc ++ #[y]).size then
            (if ((acc ++ #[y])[k]'h) = target then 1 else 0)
              + total_count (acc ++ #[y]) target k
          else total_count (acc ++ #[y]) target k) = _
    rw [dif_pos hk_lt_app, h_app, ih (Nat.le_of_lt hk)]
    show _ = (if h : k < acc.size then
                (if (acc[k]'h) = target then 1 else 0) + total_count acc target k
              else total_count acc target k)
    rw [dif_pos hk_lt]

private theorem total_count_append_singleton (acc : Array i64) (y target : i64) :
    total_count (acc ++ #[y]) target (acc.size + 1) =
      total_count acc target acc.size + (if y = target then 1 else 0) := by
  have h_size_app : (acc ++ #[y]).size = acc.size + 1 := by rw [Array.size_append]; rfl
  have h_lt : acc.size < (acc ++ #[y]).size := by rw [h_size_app]; omega
  have h_get :
      (acc ++ #[y])[acc.size]'h_lt = y := by
    rw [Array.getElem_append_right (Nat.le_refl _)]
    simp
  have h_step := total_count_succ (acc ++ #[y]) target acc.size h_lt
  rw [h_step, h_get, total_count_prefix acc y target acc.size (Nat.le_refl _)]
  omega


private theorem total_count_append_pair (acc : Array i64) (x y target : i64) :
    total_count (acc ++ #[x, y]) target (acc.size + 2) =
      total_count acc target acc.size + (if x = target then 1 else 0) + (if y = target then 1 else 0) := by
  -- Reduce #[x, y] to #[x] ++ #[y] is too involved. Direct computation via two steps.
  have h_size_app : (acc ++ #[x, y]).size = acc.size + 2 := by rw [Array.size_append]; rfl
  have h_lt_succ : acc.size + 1 < (acc ++ #[x, y]).size := by rw [h_size_app]; omega
  have h_lt : acc.size < (acc ++ #[x, y]).size := by rw [h_size_app]; omega
  -- (acc ++ #[x, y])[acc.size] = x, (acc ++ #[x, y])[acc.size + 1] = y
  have h_get_x : (acc ++ #[x, y])[acc.size]'h_lt = x := by
    rw [Array.getElem_append_right (Nat.le_refl _)]
    simp
  have h_get_y : (acc ++ #[x, y])[acc.size + 1]'h_lt_succ = y := by
    rw [Array.getElem_append_right (Nat.le_add_right _ 1)]
    -- (acc.size + 1) - acc.size = 1, and #[x, y][1] = y
    have h_sub : acc.size + 1 - acc.size = 1 := by omega
    simp [h_sub]
  -- Step 1: total_count s t (acc.size + 2) = (if s[acc.size + 1] = t then 1 else 0) + total_count s t (acc.size + 1)
  have h_step2 := total_count_succ (acc ++ #[x, y]) target (acc.size + 1) h_lt_succ
  rw [h_step2, h_get_y]
  -- Step 2: total_count s t (acc.size + 1) = (if s[acc.size] = t then 1 else 0) + total_count s t acc.size
  have h_step1 := total_count_succ (acc ++ #[x, y]) target acc.size h_lt
  rw [h_step1, h_get_x]
  -- Now reduce total_count (acc ++ [x, y]) target acc.size = total_count acc target acc.size
  have h_prefix : total_count (acc ++ #[x, y]) target acc.size = total_count acc target acc.size := by
    suffices h : ∀ k, k ≤ acc.size → total_count (acc ++ #[x, y]) target k = total_count acc target k by
      exact h acc.size (Nat.le_refl _)
    intro k hk_le
    induction k with
    | zero => rfl
    | succ k ih =>
      have hk_lt : k < acc.size := by omega
      have hk_lt_app : k < (acc ++ #[x, y]).size := by rw [h_size_app]; omega
      have h_app : (acc ++ #[x, y])[k]'hk_lt_app = acc[k]'hk_lt :=
        Array.getElem_append_left hk_lt
      show (if h : k < (acc ++ #[x, y]).size then
              (if ((acc ++ #[x, y])[k]'h) = target then 1 else 0)
                + total_count (acc ++ #[x, y]) target k
            else total_count (acc ++ #[x, y]) target k) = _
      rw [dif_pos hk_lt_app, h_app, ih (Nat.le_of_lt hk_le)]
      show _ = (if h : k < acc.size then
                  (if (acc[k]'h) = target then 1 else 0) + total_count acc target k
                else total_count acc target k)
      rw [dif_pos hk_lt]
  rw [h_prefix]
  omega

/-! ## Content invariant for `rebuild_at`.

Given `acc.val.size = i.toNat` (so the accumulator covers exactly positions
`[0, i.toNat)`), the output `r` of `rebuild_at l sorted i j acc` satisfies:

* `k < i.toNat`: `r.val[k] = acc.val[k]` (acc is preserved as a prefix)
* `k ∈ [i.toNat, l.size)` with `k % 2 = 1`: `r.val[k] = l.val[k]`
* `k ∈ [i.toNat, l.size)` with `k % 2 = 0`: `r.val[k] = sorted.val[j' for some j']`
  (we don't need this for odd-indices; even-indices uses an offset lemma below). -/

private theorem rebuild_at_prefix_preserved :
    ∀ (n : Nat) (l : RustSlice i64) (sorted : RustSlice i64)
      (i j : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      clever_036_sort_even.rebuild_at l sorted i j acc = RustM.ok r →
      ∀ (k : Nat) (hk_acc : k < acc.val.size)
        (hk_r : k < r.val.size),
        r.val[k]'hk_r = acc.val[k]'hk_acc := by
  intro n
  induction n with
  | zero =>
    intro l sorted i j acc r hm hi_le hres k hk_acc hk_r
    have hi_ge : l.val.size ≤ i.toNat := by omega
    rw [rebuild_at_oob l sorted i j acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    rfl
  | succ n ih =>
    intro l sorted i j acc r hm hi_le hres k hk_acc hk_r
    by_cases hi_ge : l.val.size ≤ i.toNat
    · rw [rebuild_at_oob l sorted i j acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      rfl
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_meas : l.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      by_cases heven : i.toNat % 2 = 0
      · by_cases hj : j.toNat < sorted.val.size
        · by_cases h_acc : acc.val.size + 1 < USize64.size
          · rw [rebuild_at_step_even l sorted i j acc hi_lt heven hj h_acc] at hres
            have h_push_size :
                (push_one acc (sorted.val[j.toNat]'hj) h_acc).val.size = acc.val.size + 1 := by
              show (acc.val ++ #[sorted.val[j.toNat]'hj]).size = acc.val.size + 1
              rw [Array.size_append]; rfl
            have hk_push : k < (push_one acc (sorted.val[j.toNat]'hj) h_acc).val.size := by
              rw [h_push_size]; omega
            have h_ih := ih l sorted (i + 1) (j + 1)
              (push_one acc (sorted.val[j.toNat]'hj) h_acc) r h_meas h_i1_le hres
              k hk_push hk_r
            rw [h_ih]
            show ((acc.val ++ #[sorted.val[j.toNat]'hj])[k]'(by
              rw [Array.size_append]
              have : (#[sorted.val[j.toNat]'hj] : Array i64).size = 1 := rfl
              omega)) = acc.val[k]'hk_acc
            exact Array.getElem_append_left hk_acc
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 1 := by omega
            rw [rebuild_at_step_even_size_fail l sorted i j acc hi_lt heven hj h_big] at hres
            cases hres
        · exfalso
          have hj_ge : sorted.val.size ≤ j.toNat := Nat.le_of_not_lt hj
          rw [rebuild_at_step_even_idx_fail l sorted i j acc hi_lt heven hj_ge] at hres
          cases hres
      · have hodd : i.toNat % 2 = 1 := by omega
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [rebuild_at_step_odd l sorted i j acc hi_lt hodd h_acc] at hres
          have h_push_size :
              (push_one acc (l.val[i.toNat]'hi_lt) h_acc).val.size = acc.val.size + 1 := by
            show (acc.val ++ #[l.val[i.toNat]'hi_lt]).size = acc.val.size + 1
            rw [Array.size_append]; rfl
          have hk_push : k < (push_one acc (l.val[i.toNat]'hi_lt) h_acc).val.size := by
            rw [h_push_size]; omega
          have h_ih := ih l sorted (i + 1) j
            (push_one acc (l.val[i.toNat]'hi_lt) h_acc) r h_meas h_i1_le hres
            k hk_push hk_r
          rw [h_ih]
          show ((acc.val ++ #[l.val[i.toNat]'hi_lt])[k]'(by
            rw [Array.size_append]
            have : (#[l.val[i.toNat]'hi_lt] : Array i64).size = 1 := rfl
            omega)) = acc.val[k]'hk_acc
          exact Array.getElem_append_left hk_acc
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [rebuild_at_step_odd_size_fail l sorted i j acc hi_lt hodd h_big] at hres
          cases hres

/-! ## Odd-index invariant for `rebuild_at`.

Given `acc.val.size = i.toNat`, for every odd `k ∈ [i.toNat, l.size)`, `r.val[k] = l.val[k]`. -/

private theorem rebuild_at_odd_indices :
    ∀ (n : Nat) (l : RustSlice i64) (sorted : RustSlice i64)
      (i j : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      acc.val.size = i.toNat →
      clever_036_sort_even.rebuild_at l sorted i j acc = RustM.ok r →
      ∀ (k : Nat) (hk_r : k < r.val.size) (hk_odd : k % 2 = 1)
        (hk_lt_l : k < l.val.size) (hk_ge_i : i.toNat ≤ k),
        r.val[k]'hk_r = l.val[k]'hk_lt_l := by
  intro n
  induction n with
  | zero =>
    intro l sorted i j acc r hm hi_le h_acc_eq hres k hk_r hk_odd hk_lt_l hk_ge_i
    have hi_ge : l.val.size ≤ i.toNat := by omega
    exfalso; omega
  | succ n ih =>
    intro l sorted i j acc r hm hi_le h_acc_eq hres k hk_r hk_odd hk_lt_l hk_ge_i
    by_cases hi_ge : l.val.size ≤ i.toNat
    · exfalso; omega
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_meas : l.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      by_cases heven : i.toNat % 2 = 0
      · -- Even step. i.toNat is even, but k is odd, so k ≠ i.toNat.
        -- Thus i.toNat + 1 ≤ k, so we can apply IH after the step.
        by_cases hj : j.toNat < sorted.val.size
        · by_cases h_acc : acc.val.size + 1 < USize64.size
          · rw [rebuild_at_step_even l sorted i j acc hi_lt heven hj h_acc] at hres
            have h_push_size :
                (push_one acc (sorted.val[j.toNat]'hj) h_acc).val.size = acc.val.size + 1 := by
              show (acc.val ++ #[sorted.val[j.toNat]'hj]).size = acc.val.size + 1
              rw [Array.size_append]; rfl
            have h_acc_new_eq :
                (push_one acc (sorted.val[j.toNat]'hj) h_acc).val.size = (i + 1).toNat := by
              rw [h_push_size, h_acc_eq, h_i1]
            have hk_ne_i : k ≠ i.toNat := by intro h; rw [h] at hk_odd; omega
            have hk_ge_i1 : (i + 1).toNat ≤ k := by rw [h_i1]; omega
            exact ih l sorted (i + 1) (j + 1)
              (push_one acc (sorted.val[j.toNat]'hj) h_acc) r h_meas h_i1_le
              h_acc_new_eq hres k hk_r hk_odd hk_lt_l hk_ge_i1
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 1 := by omega
            rw [rebuild_at_step_even_size_fail l sorted i j acc hi_lt heven hj h_big] at hres
            cases hres
        · exfalso
          have hj_ge : sorted.val.size ≤ j.toNat := Nat.le_of_not_lt hj
          rw [rebuild_at_step_even_idx_fail l sorted i j acc hi_lt heven hj_ge] at hres
          cases hres
      · -- Odd step. i.toNat is odd, k may equal i.toNat.
        have hodd : i.toNat % 2 = 1 := by omega
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [rebuild_at_step_odd l sorted i j acc hi_lt hodd h_acc] at hres
          have h_push_size :
              (push_one acc (l.val[i.toNat]'hi_lt) h_acc).val.size = acc.val.size + 1 := by
            show (acc.val ++ #[l.val[i.toNat]'hi_lt]).size = acc.val.size + 1
            rw [Array.size_append]; rfl
          have h_acc_new_eq :
              (push_one acc (l.val[i.toNat]'hi_lt) h_acc).val.size = (i + 1).toNat := by
            rw [h_push_size, h_acc_eq, h_i1]
          by_cases h_eq_k : k = i.toNat
          · -- k = i.toNat: the just-appended element is l[i.toNat]
            -- Use rebuild_at_prefix_preserved on (acc ++ #[l[i.toNat]]) at position i.toNat
            have hk_push_acc : k < (push_one acc (l.val[i.toNat]'hi_lt) h_acc).val.size := by
              rw [h_push_size, h_acc_eq]; omega
            have h_prefix := rebuild_at_prefix_preserved _ l sorted (i + 1) j
              (push_one acc (l.val[i.toNat]'hi_lt) h_acc) r (Nat.le_refl _) h_i1_le hres
              k hk_push_acc hk_r
            rw [h_prefix]
            -- Now show (acc ++ #[l[i.toNat]])[k] = l[k] when k = i.toNat = acc.val.size
            subst h_eq_k
            -- Use `(push_one acc x).val[acc.val.size] = x` directly.
            have h_value :
                ((push_one acc (l.val[i.toNat]'hi_lt) h_acc).val[i.toNat]'hk_push_acc)
                = l.val[i.toNat]'hi_lt := by
              show ((acc.val ++ #[l.val[i.toNat]'hi_lt])[i.toNat]'hk_push_acc) = _
              have h_acc_le_i : acc.val.size ≤ i.toNat := by rw [h_acc_eq]; exact Nat.le_refl _
              rw [Array.getElem_append_right h_acc_le_i]
              have h_sub_zero : i.toNat - acc.val.size = 0 := by rw [h_acc_eq]; omega
              -- Index 0 of a singleton array is the element.
              simp [h_sub_zero]
            rw [h_value]
          · -- k ≠ i.toNat, so i.toNat < k (since i ≤ k and k ≠ i)
            have hk_ge_i1 : (i + 1).toNat ≤ k := by rw [h_i1]; omega
            exact ih l sorted (i + 1) j
              (push_one acc (l.val[i.toNat]'hi_lt) h_acc) r h_meas h_i1_le
              h_acc_new_eq hres k hk_r hk_odd hk_lt_l hk_ge_i1
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [rebuild_at_step_odd_size_fail l sorted i j acc hi_lt hodd h_big] at hres
          cases hres

/-! ## Multiset (count) invariant for `rebuild_at`. -/

/-- Number of evens in [i, l_size) = (l_size + 1)/2 - (i + 1)/2 when i ≤ l_size. -/
private theorem evens_count (l_size i : Nat) (h : i ≤ l_size) :
    (l_size + 1) / 2 - (i + 1) / 2 = (l_size + 1) / 2 - (i + 1) / 2 := rfl

/-- The number of evens consumed in [i, l_size) equals (l_size+1)/2 - (i+1)/2. -/
private theorem evens_step_succ_even (l_size i : Nat) (hi : i < l_size) (heven : i % 2 = 0) :
    (l_size + 1) / 2 - (i + 1) / 2 = (l_size + 1) / 2 - (i + 2) / 2 + 1 := by
  have h1 : (i + 1) / 2 = i / 2 := by omega
  have h2 : (i + 2) / 2 = i / 2 + 1 := by omega
  omega

private theorem evens_step_succ_odd (l_size i : Nat) (hi : i < l_size) (hodd : i % 2 = 1) :
    (l_size + 1) / 2 - (i + 1) / 2 = (l_size + 1) / 2 - (i + 2) / 2 := by
  have h1 : (i + 1) / 2 = i / 2 + 1 := by omega
  have h2 : (i + 2) / 2 = i / 2 + 1 := by omega
  omega

private theorem rebuild_at_count :
    ∀ (n : Nat) (l : RustSlice i64) (sorted : RustSlice i64)
      (i j : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global) (target : i64),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      acc.val.size = i.toNat →
      j.toNat ≤ sorted.val.size →
      clever_036_sort_even.rebuild_at l sorted i j acc = RustM.ok r →
      let E := (l.val.size + 1) / 2 - (i.toNat + 1) / 2
      j.toNat + E ≤ sorted.val.size ∧
      count_evens r.val target r.val.size + total_count sorted.val target j.toNat =
        count_evens acc.val target acc.val.size + total_count sorted.val target (j.toNat + E) := by
  intro n
  induction n with
  | zero =>
    intro l sorted i j acc r target hm hi_le h_acc_eq h_j_le hres
    have hi_ge : l.val.size ≤ i.toNat := by omega
    have hi_eq : i.toNat = l.val.size := by omega
    rw [rebuild_at_oob l sorted i j acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    simp only
    have h_E_zero : (l.val.size + 1) / 2 - (i.toNat + 1) / 2 = 0 := by
      rw [hi_eq]; omega
    rw [h_E_zero]
    refine ⟨by omega, ?_⟩
    rw [Nat.add_zero]
  | succ n ih =>
    intro l sorted i j acc r target hm hi_le h_acc_eq h_j_le hres
    by_cases hi_ge : l.val.size ≤ i.toNat
    · have hi_eq : i.toNat = l.val.size := by omega
      rw [rebuild_at_oob l sorted i j acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      simp only
      have h_E_zero : (l.val.size + 1) / 2 - (i.toNat + 1) / 2 = 0 := by
        rw [hi_eq]; omega
      rw [h_E_zero]
      refine ⟨by omega, ?_⟩
      rw [Nat.add_zero]
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_meas : l.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      by_cases heven : i.toNat % 2 = 0
      · -- Even step
        by_cases hj : j.toNat < sorted.val.size
        · by_cases h_acc : acc.val.size + 1 < USize64.size
          · rw [rebuild_at_step_even l sorted i j acc hi_lt heven hj h_acc] at hres
            have h_push_size :
                (push_one acc (sorted.val[j.toNat]'hj) h_acc).val.size = acc.val.size + 1 := by
              show (acc.val ++ #[sorted.val[j.toNat]'hj]).size = acc.val.size + 1
              rw [Array.size_append]; rfl
            have h_acc_new_eq :
                (push_one acc (sorted.val[j.toNat]'hj) h_acc).val.size = (i + 1).toNat := by
              rw [h_push_size, h_acc_eq, h_i1]
            have h_size_lt_s : sorted.val.size < USize64.size := sorted.size_lt_usizeSize
            have h_no_ov_j : j.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt_s; omega
            have h_j1 : (j + 1).toNat = j.toNat + 1 := usize_add_one_toNat j h_no_ov_j
            have h_j1_le : (j + 1).toNat ≤ sorted.val.size := by rw [h_j1]; omega
            have ih_app := ih l sorted (i + 1) (j + 1)
              (push_one acc (sorted.val[j.toNat]'hj) h_acc) r target h_meas h_i1_le h_acc_new_eq h_j1_le hres
            simp only at ih_app
            have h_E_succ :
                (l.val.size + 1) / 2 - (i.toNat + 1) / 2 =
                  ((l.val.size + 1) / 2 - ((i.toNat + 1) + 1) / 2) + 1 := by
              have hA : (i.toNat + 1) / 2 = i.toNat / 2 := by omega
              have hB : ((i.toNat + 1) + 1) / 2 = i.toNat / 2 + 1 := by omega
              have hC : i.toNat / 2 + 1 ≤ (l.val.size + 1) / 2 := by omega
              omega
            rw [h_i1, h_j1] at ih_app
            obtain ⟨h_bound, h_count⟩ := ih_app
            refine ⟨?_, ?_⟩
            · rw [h_E_succ]; omega
            · -- count_evens of pushed acc = count_evens acc + (if sorted[j] = target then 1 else 0)
              have h_count_evens_app :
                  count_evens (push_one acc (sorted.val[j.toNat]'hj) h_acc).val target
                    (push_one acc (sorted.val[j.toNat]'hj) h_acc).val.size =
                  count_evens acc.val target acc.val.size +
                    (if sorted.val[j.toNat]'hj = target then 1 else 0) := by
                show count_evens (acc.val ++ #[sorted.val[j.toNat]'hj]) target
                       (acc.val ++ #[sorted.val[j.toNat]'hj]).size = _
                rw [show (acc.val ++ #[sorted.val[j.toNat]'hj]).size = acc.val.size + 1 from by
                      rw [Array.size_append]; rfl]
                rw [count_evens_append_singleton]
                have h_even_acc : acc.val.size % 2 = 0 := by rw [h_acc_eq]; exact heven
                by_cases h_sj_eq : sorted.val[j.toNat]'hj = target
                · rw [if_pos (And.intro h_even_acc h_sj_eq), if_pos h_sj_eq]
                · rw [if_neg (fun h => h_sj_eq h.right), if_neg h_sj_eq]
              rw [h_count_evens_app] at h_count
              -- total_count sorted target (j.toNat + 1) = (if sorted[j] = target then 1 else 0) + total_count sorted target j.toNat
              have h_total_succ :
                  total_count sorted.val target (j.toNat + 1) =
                    (if sorted.val[j.toNat]'hj = target then 1 else 0) +
                    total_count sorted.val target j.toNat :=
                total_count_succ sorted.val target j.toNat hj
              rw [h_total_succ] at h_count
              -- Now h_count :
              --   count_evens r + ((if sj=t then 1 else 0) + total j) = 
              --   (count_evens acc + (if sj=t then 1 else 0)) + total (j+1+E')
              -- Want goal:
              --   count_evens r + total j = count_evens acc + total (j+E)
              -- where E = E' + 1. j + 1 + E' = j + E.
              rw [h_E_succ]
              have h_j1E : j.toNat + 1 + ((l.val.size + 1) / 2 - (i.toNat + 1 + 1) / 2) =
                            j.toNat + ((l.val.size + 1) / 2 - (i.toNat + 1 + 1) / 2 + 1) := by omega
              rw [h_j1E] at h_count
              omega
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 1 := by omega
            rw [rebuild_at_step_even_size_fail l sorted i j acc hi_lt heven hj h_big] at hres
            cases hres
        · exfalso
          have hj_ge : sorted.val.size ≤ j.toNat := Nat.le_of_not_lt hj
          rw [rebuild_at_step_even_idx_fail l sorted i j acc hi_lt heven hj_ge] at hres
          cases hres
      · -- Odd step
        have hodd : i.toNat % 2 = 1 := by omega
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [rebuild_at_step_odd l sorted i j acc hi_lt hodd h_acc] at hres
          have h_push_size :
              (push_one acc (l.val[i.toNat]'hi_lt) h_acc).val.size = acc.val.size + 1 := by
            show (acc.val ++ #[l.val[i.toNat]'hi_lt]).size = acc.val.size + 1
            rw [Array.size_append]; rfl
          have h_acc_new_eq :
              (push_one acc (l.val[i.toNat]'hi_lt) h_acc).val.size = (i + 1).toNat := by
            rw [h_push_size, h_acc_eq, h_i1]
          have ih_app := ih l sorted (i + 1) j
            (push_one acc (l.val[i.toNat]'hi_lt) h_acc) r target h_meas h_i1_le h_acc_new_eq h_j_le hres
          simp only at ih_app
          have h_E_same :
              (l.val.size + 1) / 2 - (i.toNat + 1) / 2 =
                (l.val.size + 1) / 2 - ((i.toNat + 1) + 1) / 2 := by
            have h1 : (i.toNat + 1) / 2 = i.toNat / 2 + 1 := by omega
            have h2 : ((i.toNat + 1) + 1) / 2 = i.toNat / 2 + 1 := by omega
            omega
          rw [h_i1] at ih_app
          obtain ⟨h_bound, h_count⟩ := ih_app
          refine ⟨?_, ?_⟩
          · rw [h_E_same]; exact h_bound
          · have h_count_evens_app :
                count_evens (push_one acc (l.val[i.toNat]'hi_lt) h_acc).val target
                  (push_one acc (l.val[i.toNat]'hi_lt) h_acc).val.size =
                count_evens acc.val target acc.val.size := by
              show count_evens (acc.val ++ #[l.val[i.toNat]'hi_lt]) target (acc.val ++ #[l.val[i.toNat]'hi_lt]).size = _
              rw [show (acc.val ++ #[l.val[i.toNat]'hi_lt]).size = acc.val.size + 1 from by
                    rw [Array.size_append]; rfl]
              rw [count_evens_append_singleton]
              have h_odd_acc : ¬ (acc.val.size % 2 = 0) := by rw [h_acc_eq]; omega
              rw [if_neg (fun h => h_odd_acc h.left)]
            rw [h_count_evens_app] at h_count
            rw [h_E_same]
            exact h_count
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [rebuild_at_step_odd_size_fail l sorted i j acc hi_lt hodd h_big] at hres
          cases hres

/-! ## Step lemmas for `insert_sorted_at`. -/

private theorem insert_sorted_at_step_insert (v : RustSlice i64) (i : usize) (x : i64)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_vi : (v.val[i.toNat]'hi).toInt ≥ x.toInt)
    (h_acc : acc.val.size + 2 < USize64.size) :
    clever_036_sort_even.insert_sorted_at v i x false acc =
      clever_036_sort_even.insert_sorted_at v (i + 1) x true
        (push_two acc x (v.val[i.toNat]'hi) h_acc) := by
  conv => lhs; unfold clever_036_sort_even.insert_sorted_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM i64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_ge_true : (decide ((v.val[i.toNat]'hi) ≥ x)) = true := by
    rw [decide_eq_true_iff]
    rw [show ((v.val[i.toNat]'hi) ≥ x) = (x ≤ (v.val[i.toNat]'hi)) from rfl]
    rw [Int64.le_iff_toInt_le]
    exact h_vi
  have h_add : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := usize_add_one_ok i h_no_ov_i
  have h_app_size :
      acc.val.size + (#[x, v.val[i.toNat]'hi] : Array i64).size < USize64.size := by
    show acc.val.size + 2 < USize64.size; exact h_acc
  have h_extend :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[x, v.val[i.toNat]'hi], two_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.ok (push_two acc x (v.val[i.toNat]'hi) h_acc) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.hax.logical_op.not, Bool.not_false,
             rust_primitives.hax.logical_op.and, h_ge_true,
             Bool.true_and, ↓reduceIte]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[x, v.val[i.toNat]'hi] : RustArray i64 2)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[x, v.val[i.toNat]'hi], two_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend]
  simp only [RustM_ok_bind]
  rw [h_add]
  simp only [RustM_ok_bind]

/-- `insert_sorted_at` pass step: covers (a) `inserted = true`, and
    (b) `inserted = false` with `vi < x`. In both cases the extend chunk is
    just `[vi]` and `inserted` is unchanged. -/
private theorem insert_sorted_at_step_pass (v : RustSlice i64) (i : usize) (x : i64)
    (inserted : Bool) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_skip : inserted = true ∨ (v.val[i.toNat]'hi).toInt < x.toInt)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_036_sort_even.insert_sorted_at v i x inserted acc =
      clever_036_sort_even.insert_sorted_at v (i + 1) x inserted
        (push_one acc (v.val[i.toNat]'hi) h_acc) := by
  conv => lhs; unfold clever_036_sort_even.insert_sorted_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM i64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_and_false : ((!inserted) && decide ((v.val[i.toNat]'hi) ≥ x)) = false := by
    cases h_skip with
    | inl h_ins_true =>
      subst h_ins_true; rfl
    | inr h_lt =>
      have h_not_ge : ¬ ((v.val[i.toNat]'hi) ≥ x) := by
        rw [show ((v.val[i.toNat]'hi) ≥ x) = (x ≤ (v.val[i.toNat]'hi)) from rfl]
        rw [Int64.le_iff_toInt_le]
        omega
      rw [decide_eq_false h_not_ge]
      exact Bool.and_false _
  have h_add : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := usize_add_one_ok i h_no_ov_i
  have h_app_size :
      acc.val.size + (#[v.val[i.toNat]'hi] : Array i64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  have h_extend :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[v.val[i.toNat]'hi], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.ok (push_one acc (v.val[i.toNat]'hi) h_acc) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.hax.logical_op.not,
             rust_primitives.hax.logical_op.and]
  rw [h_and_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[v.val[i.toNat]'hi] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[v.val[i.toNat]'hi], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend]
  simp only [RustM_ok_bind]
  rw [h_add]
  simp only [RustM_ok_bind]

/-! ## Fail variants for `insert_sorted_at`. -/

private theorem insert_sorted_at_oob_not_inserted_fail (v : RustSlice i64) (i : usize) (x : i64)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_036_sort_even.insert_sorted_at v i x false acc =
      RustM.fail .maximumSizeExceeded := by
  unfold clever_036_sort_even.insert_sorted_at
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat v.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]; rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  have h_app_size_neg :
      ¬ acc.val.size + (#[x] : Array i64).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[x], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, ↓reduceIte,
             rust_primitives.hax.logical_op.not, Bool.not_false,
             ↓reduceIte]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[x] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[x], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

private theorem insert_sorted_at_step_insert_fail (v : RustSlice i64) (i : usize) (x : i64)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_vi : (v.val[i.toNat]'hi).toInt ≥ x.toInt)
    (h_big : USize64.size ≤ acc.val.size + 2) :
    clever_036_sort_even.insert_sorted_at v i x false acc = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_036_sort_even.insert_sorted_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM i64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_ge_true : (decide ((v.val[i.toNat]'hi) ≥ x)) = true := by
    rw [decide_eq_true_iff]
    rw [show ((v.val[i.toNat]'hi) ≥ x) = (x ≤ (v.val[i.toNat]'hi)) from rfl]
    rw [Int64.le_iff_toInt_le]
    exact h_vi
  have h_app_size_neg :
      ¬ acc.val.size + (#[x, v.val[i.toNat]'hi] : Array i64).size < USize64.size := by
    show ¬ acc.val.size + 2 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[x, v.val[i.toNat]'hi], two_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.hax.logical_op.not, Bool.not_false,
             rust_primitives.hax.logical_op.and, h_ge_true,
             Bool.true_and, ↓reduceIte]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[x, v.val[i.toNat]'hi] : RustArray i64 2)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[x, v.val[i.toNat]'hi], two_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

private theorem insert_sorted_at_step_pass_fail (v : RustSlice i64) (i : usize) (x : i64)
    (inserted : Bool) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_skip : inserted = true ∨ (v.val[i.toNat]'hi).toInt < x.toInt)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_036_sort_even.insert_sorted_at v i x inserted acc = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_036_sort_even.insert_sorted_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM i64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_and_false : ((!inserted) && decide ((v.val[i.toNat]'hi) ≥ x)) = false := by
    cases h_skip with
    | inl h_ins_true => subst h_ins_true; rfl
    | inr h_lt =>
      have h_not_ge : ¬ ((v.val[i.toNat]'hi) ≥ x) := by
        rw [show ((v.val[i.toNat]'hi) ≥ x) = (x ≤ (v.val[i.toNat]'hi)) from rfl]
        rw [Int64.le_iff_toInt_le]
        omega
      rw [decide_eq_false h_not_ge]
      exact Bool.and_false _
  have h_app_size_neg :
      ¬ acc.val.size + (#[v.val[i.toNat]'hi] : Array i64).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[v.val[i.toNat]'hi], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.hax.logical_op.not,
             rust_primitives.hax.logical_op.and]
  rw [h_and_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[v.val[i.toNat]'hi] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[v.val[i.toNat]'hi], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

/-! ## Invariant for `insert_sorted_at`: size and total_count.

Combined into one strong induction with both clauses. -/

private theorem insert_sorted_at_inv :
    ∀ (n : Nat) (v : RustSlice i64) (i : usize) (x : i64) (inserted : Bool)
      (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global) (target : i64),
      v.val.size - i.toNat ≤ n →
      i.toNat ≤ v.val.size →
      clever_036_sort_even.insert_sorted_at v i x inserted acc = RustM.ok r →
      r.val.size = acc.val.size + (v.val.size - i.toNat) + (if inserted then 0 else 1) ∧
      total_count r.val target r.val.size + total_count v.val target i.toNat =
        total_count acc.val target acc.val.size + total_count v.val target v.val.size
          + (if inserted then 0 else (if x = target then 1 else 0)) := by
  intro n
  induction n with
  | zero =>
    intro v i x inserted acc r target hm hi_le hres
    have hi_ge : v.val.size ≤ i.toNat := by omega
    have hi_eq : i.toNat = v.val.size := by omega
    cases inserted with
    | true =>
      rw [insert_sorted_at_oob_inserted v i x acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      refine ⟨?_, ?_⟩
      · simp [hi_eq]
      · rw [hi_eq]
        simp
    | false =>
      by_cases h_acc : acc.val.size + 1 < USize64.size
      · rw [insert_sorted_at_oob_not_inserted v i x acc hi_ge h_acc] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        refine ⟨?_, ?_⟩
        · show (acc.val ++ #[x]).size = acc.val.size + (v.val.size - i.toNat) + 1
          rw [Array.size_append]; simp; omega
        · show total_count (acc.val ++ #[x]) target (acc.val ++ #[x]).size + total_count v.val target i.toNat
              = total_count acc.val target acc.val.size + total_count v.val target v.val.size
                + (if x = target then 1 else 0)
          have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by rw [Array.size_append]; rfl
          rw [h_size, total_count_append_singleton, hi_eq]
          omega
      · exfalso
        have h_big : USize64.size ≤ acc.val.size + 1 := by omega
        rw [insert_sorted_at_oob_not_inserted_fail v i x acc hi_ge h_big] at hres
        cases hres
  | succ n ih =>
    intro v i x inserted acc r target hm hi_le hres
    by_cases hi_ge : v.val.size ≤ i.toNat
    · -- OOB case — same as base case
      have hi_eq : i.toNat = v.val.size := by omega
      cases inserted with
      | true =>
        rw [insert_sorted_at_oob_inserted v i x acc hi_ge] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        refine ⟨?_, ?_⟩
        · simp [hi_eq]
        · rw [hi_eq]; simp
      | false =>
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [insert_sorted_at_oob_not_inserted v i x acc hi_ge h_acc] at hres
          injection hres with h_eq
          injection h_eq with h_eq'
          subst h_eq'
          refine ⟨?_, ?_⟩
          · show (acc.val ++ #[x]).size = acc.val.size + (v.val.size - i.toNat) + 1
            rw [Array.size_append]; simp; omega
          · show total_count (acc.val ++ #[x]) target (acc.val ++ #[x]).size + total_count v.val target i.toNat
                = total_count acc.val target acc.val.size + total_count v.val target v.val.size
                  + (if x = target then 1 else 0)
            have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by rw [Array.size_append]; rfl
            rw [h_size, total_count_append_singleton, hi_eq]
            omega
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_sorted_at_oob_not_inserted_fail v i x acc hi_ge h_big] at hres
          cases hres
    · -- Inductive case: i.toNat < v.val.size
      have hi_lt : i.toNat < v.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ v.val.size := by rw [h_i1]; omega
      have h_meas : v.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      have h_total_succ_v :
          total_count v.val target (i.toNat + 1) =
            (if v.val[i.toNat]'hi_lt = target then 1 else 0) + total_count v.val target i.toNat :=
        total_count_succ v.val target i.toNat hi_lt
      cases inserted with
      | true =>
        -- Pass step with h_skip = Or.inl rfl
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [insert_sorted_at_step_pass v i x true acc hi_lt (Or.inl rfl) h_acc] at hres
          have h_push_size :
              (push_one acc (v.val[i.toNat]'hi_lt) h_acc).val.size = acc.val.size + 1 := by
            show (acc.val ++ #[v.val[i.toNat]'hi_lt]).size = acc.val.size + 1
            rw [Array.size_append]; rfl
          have h_count_pushed :
              total_count (push_one acc (v.val[i.toNat]'hi_lt) h_acc).val target
                (acc.val.size + 1) =
              total_count acc.val target acc.val.size +
                (if v.val[i.toNat]'hi_lt = target then 1 else 0) := by
            show total_count (acc.val ++ #[v.val[i.toNat]'hi_lt]) target (acc.val.size + 1) = _
            exact total_count_append_singleton acc.val (v.val[i.toNat]'hi_lt) target
          have ih_app := ih v (i + 1) x true (push_one acc (v.val[i.toNat]'hi_lt) h_acc) r target
            h_meas h_i1_le hres
          rw [h_i1] at ih_app
          obtain ⟨h_size_eq, h_count_eq⟩ := ih_app
          rw [h_push_size] at h_size_eq h_count_eq
          simp only [if_true, if_pos rfl] at h_size_eq h_count_eq
          refine ⟨?_, ?_⟩
          · simp only [if_true, if_pos rfl]; rw [h_size_eq]
            have : 0 < v.val.size - i.toNat := by omega
            omega
          · simp only [if_true, if_pos rfl]
            rw [h_count_pushed] at h_count_eq
            rw [h_total_succ_v] at h_count_eq
            omega
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_sorted_at_step_pass_fail v i x true acc hi_lt (Or.inl rfl) h_big] at hres
          cases hres
      | false =>
        by_cases h_vi : (v.val[i.toNat]'hi_lt).toInt ≥ x.toInt
        · -- Insert step
          by_cases h_acc : acc.val.size + 2 < USize64.size
          · rw [insert_sorted_at_step_insert v i x acc hi_lt h_vi h_acc] at hres
            have h_push_size :
                (push_two acc x (v.val[i.toNat]'hi_lt) h_acc).val.size = acc.val.size + 2 := by
              show (acc.val ++ #[x, v.val[i.toNat]'hi_lt]).size = acc.val.size + 2
              rw [Array.size_append]; rfl
            have h_count_pushed :
                total_count (push_two acc x (v.val[i.toNat]'hi_lt) h_acc).val target
                  (acc.val.size + 2) =
                total_count acc.val target acc.val.size + (if x = target then 1 else 0) +
                  (if v.val[i.toNat]'hi_lt = target then 1 else 0) := by
              show total_count (acc.val ++ #[x, v.val[i.toNat]'hi_lt]) target (acc.val.size + 2) = _
              exact total_count_append_pair acc.val x (v.val[i.toNat]'hi_lt) target
            have ih_app := ih v (i + 1) x true (push_two acc x (v.val[i.toNat]'hi_lt) h_acc) r target
              h_meas h_i1_le hres
            rw [h_i1] at ih_app
            obtain ⟨h_size_eq, h_count_eq⟩ := ih_app
            rw [h_push_size] at h_size_eq h_count_eq
            rw [if_pos (rfl : true = true)] at h_size_eq h_count_eq
            rw [if_neg (Bool.false_ne_true), if_neg (Bool.false_ne_true)]
            rw [h_count_pushed] at h_count_eq
            rw [h_total_succ_v] at h_count_eq
            refine ⟨?_, ?_⟩
            · rw [h_size_eq]
              have : 0 < v.val.size - i.toNat := by omega
              omega
            · omega
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 2 := by omega
            rw [insert_sorted_at_step_insert_fail v i x acc hi_lt h_vi h_big] at hres
            cases hres
        · -- Pass step with h_skip = Or.inr h_lt
          have h_lt : (v.val[i.toNat]'hi_lt).toInt < x.toInt := by omega
          by_cases h_acc : acc.val.size + 1 < USize64.size
          · rw [insert_sorted_at_step_pass v i x false acc hi_lt (Or.inr h_lt) h_acc] at hres
            have h_push_size :
                (push_one acc (v.val[i.toNat]'hi_lt) h_acc).val.size = acc.val.size + 1 := by
              show (acc.val ++ #[v.val[i.toNat]'hi_lt]).size = acc.val.size + 1
              rw [Array.size_append]; rfl
            have h_count_pushed :
                total_count (push_one acc (v.val[i.toNat]'hi_lt) h_acc).val target
                  (acc.val.size + 1) =
                total_count acc.val target acc.val.size +
                  (if v.val[i.toNat]'hi_lt = target then 1 else 0) := by
              show total_count (acc.val ++ #[v.val[i.toNat]'hi_lt]) target (acc.val.size + 1) = _
              exact total_count_append_singleton acc.val (v.val[i.toNat]'hi_lt) target
            have ih_app := ih v (i + 1) x false (push_one acc (v.val[i.toNat]'hi_lt) h_acc) r target
              h_meas h_i1_le hres
            rw [h_i1] at ih_app
            obtain ⟨h_size_eq, h_count_eq⟩ := ih_app
            rw [h_push_size] at h_size_eq h_count_eq
            rw [if_neg (Bool.false_ne_true)] at h_size_eq h_count_eq
            rw [if_neg (Bool.false_ne_true), if_neg (Bool.false_ne_true)]
            rw [h_count_pushed] at h_count_eq
            rw [h_total_succ_v] at h_count_eq
            refine ⟨?_, ?_⟩
            · rw [h_size_eq]
              have : 0 < v.val.size - i.toNat := by omega
              omega
            · omega
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 1 := by omega
            rw [insert_sorted_at_step_pass_fail v i x false acc hi_lt (Or.inr h_lt) h_big] at hres
            cases hres

/-- Specialization: insert_sorted v x has size v.size + 1, total_count adds 1 if x = target. -/
private theorem insert_sorted_inv (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (r : alloc.vec.Vec i64 alloc.alloc.Global) (target : i64)
    (hres : clever_036_sort_even.insert_sorted v x = RustM.ok r) :
    r.val.size = v.val.size + 1 ∧
    total_count r.val target r.val.size =
      total_count v.val target v.val.size + (if x = target then 1 else 0) := by
  unfold clever_036_sort_even.insert_sorted at hres
  have h_deref :
      (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec i64 alloc.alloc.Global) v : RustM _) = RustM.ok v := rfl
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_deref, h_new] at hres
  simp only [RustM_ok_bind] at hres
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_meas : v.val.size - (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  have h_le : (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  have inv := insert_sorted_at_inv v.val.size v (0 : usize) x false
    ⟨(List.nil).toArray, by grind⟩ r target h_meas h_le hres
  obtain ⟨h_size_eq, h_count_eq⟩ := inv
  have h_empty_size : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
  rw [h_empty_size, h_zero_toNat] at h_size_eq
  rw [h_empty_size, h_zero_toNat] at h_count_eq
  have h_empty_count : total_count ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val target 0 = 0 := rfl
  refine ⟨?_, ?_⟩
  · rw [h_size_eq]; simp
  · rw [h_empty_count] at h_count_eq
    have h_total_zero : total_count v.val target 0 = 0 := rfl
    rw [h_total_zero] at h_count_eq
    simp at h_count_eq
    omega

/-! ## Sortedness predicate and append lemmas. -/

private def sorted_asc (arr : Array i64) : Prop :=
  ∀ (k₁ k₂ : Nat) (h₁ : k₁ < arr.size) (h₂ : k₂ < arr.size),
    k₁ ≤ k₂ → (arr[k₁]'h₁).toInt ≤ (arr[k₂]'h₂).toInt

private theorem sorted_asc_empty : sorted_asc #[] := by
  intro k₁ k₂ h₁ _ _
  have : (#[] : Array i64).size = 0 := rfl
  omega

private theorem sorted_asc_append_singleton (acc : Array i64) (y : i64)
    (h_acc : sorted_asc acc)
    (h_le : ∀ (k : Nat) (hk : k < acc.size), (acc[k]'hk).toInt ≤ y.toInt) :
    sorted_asc (acc ++ #[y]) := by
  intro k₁ k₂ h₁ h₂ hle12
  rw [Array.size_append] at h₁ h₂
  have h_one : (#[y] : Array i64).size = 1 := rfl
  by_cases h_k1_lt : k₁ < acc.size
  · by_cases h_k2_lt : k₂ < acc.size
    · rw [Array.getElem_append_left h_k1_lt, Array.getElem_append_left h_k2_lt]
      exact h_acc k₁ k₂ h_k1_lt h_k2_lt hle12
    · have h_k2_ge : acc.size ≤ k₂ := by omega
      rw [Array.getElem_append_left h_k1_lt]
      rw [Array.getElem_append_right h_k2_ge]
      have h_idx : k₂ - acc.size = 0 := by omega
      have h_zero : (0 : Nat) < (#[y] : Array i64).size := by rw [h_one]; omega
      rw [show ((#[y] : Array i64)[k₂ - acc.size]'(by rw [h_idx]; exact h_zero))
              = (#[y] : Array i64)[0]'h_zero from by simp [h_idx]]
      show (acc[k₁]'h_k1_lt).toInt ≤ y.toInt
      exact h_le k₁ h_k1_lt
  · have h_k1_ge : acc.size ≤ k₁ := by omega
    have h_k2_ge : acc.size ≤ k₂ := by omega
    rw [Array.getElem_append_right h_k1_ge, Array.getElem_append_right h_k2_ge]
    have h_k1_idx : k₁ - acc.size = 0 := by omega
    have h_k2_idx : k₂ - acc.size = 0 := by omega
    have h_zero : (0 : Nat) < (#[y] : Array i64).size := by rw [h_one]; omega
    rw [show ((#[y] : Array i64)[k₁ - acc.size]'(by rw [h_k1_idx]; exact h_zero))
            = (#[y] : Array i64)[0]'h_zero from by simp [h_k1_idx]]
    rw [show ((#[y] : Array i64)[k₂ - acc.size]'(by rw [h_k2_idx]; exact h_zero))
            = (#[y] : Array i64)[0]'h_zero from by simp [h_k2_idx]]
    exact Int.le_refl _

private theorem sorted_asc_append_pair (acc : Array i64) (a b : i64)
    (h_acc : sorted_asc acc)
    (h_le_a : ∀ (k : Nat) (hk : k < acc.size), (acc[k]'hk).toInt ≤ a.toInt)
    (h_le_ab : a.toInt ≤ b.toInt) :
    sorted_asc (acc ++ #[a, b]) := by
  intro k₁ k₂ h₁ h₂ hle12
  rw [Array.size_append] at h₁ h₂
  have h_two : (#[a, b] : Array i64).size = 2 := rfl
  by_cases h_k1_lt : k₁ < acc.size
  · by_cases h_k2_lt : k₂ < acc.size
    · rw [Array.getElem_append_left h_k1_lt, Array.getElem_append_left h_k2_lt]
      exact h_acc k₁ k₂ h_k1_lt h_k2_lt hle12
    · have h_k2_ge : acc.size ≤ k₂ := by omega
      rw [Array.getElem_append_left h_k1_lt, Array.getElem_append_right h_k2_ge]
      have h_acc_k1 := h_le_a k₁ h_k1_lt
      by_cases h_k2_sub_eq : k₂ - acc.size = 0
      · have h_zero : (0 : Nat) < (#[a, b] : Array i64).size := by rw [h_two]; omega
        rw [show ((#[a, b] : Array i64)[k₂ - acc.size]'(by rw [h_k2_sub_eq]; exact h_zero))
                = (#[a, b] : Array i64)[0]'h_zero from by simp [h_k2_sub_eq]]
        show (acc[k₁]'h_k1_lt).toInt ≤ a.toInt
        exact h_acc_k1
      · have h_k2_sub_eq1 : k₂ - acc.size = 1 := by omega
        have h_one_lt : (1 : Nat) < (#[a, b] : Array i64).size := by rw [h_two]; omega
        rw [show ((#[a, b] : Array i64)[k₂ - acc.size]'(by rw [h_k2_sub_eq1]; exact h_one_lt))
                = (#[a, b] : Array i64)[1]'h_one_lt from by simp [h_k2_sub_eq1]]
        show (acc[k₁]'h_k1_lt).toInt ≤ b.toInt
        omega
  · have h_k1_ge : acc.size ≤ k₁ := by omega
    have h_k2_ge : acc.size ≤ k₂ := by omega
    rw [Array.getElem_append_right h_k1_ge, Array.getElem_append_right h_k2_ge]
    by_cases h_k1_eq : k₁ - acc.size = 0
    · have h_zero : (0 : Nat) < (#[a, b] : Array i64).size := by rw [h_two]; omega
      rw [show ((#[a, b] : Array i64)[k₁ - acc.size]'(by rw [h_k1_eq]; exact h_zero))
              = (#[a, b] : Array i64)[0]'h_zero from by simp [h_k1_eq]]
      by_cases h_k2_eq : k₂ - acc.size = 0
      · rw [show ((#[a, b] : Array i64)[k₂ - acc.size]'(by rw [h_k2_eq]; exact h_zero))
                = (#[a, b] : Array i64)[0]'h_zero from by simp [h_k2_eq]]
        show a.toInt ≤ a.toInt
        exact Int.le_refl _
      · have h_k2_eq1 : k₂ - acc.size = 1 := by omega
        have h_one_lt : (1 : Nat) < (#[a, b] : Array i64).size := by rw [h_two]; omega
        rw [show ((#[a, b] : Array i64)[k₂ - acc.size]'(by rw [h_k2_eq1]; exact h_one_lt))
                = (#[a, b] : Array i64)[1]'h_one_lt from by simp [h_k2_eq1]]
        show a.toInt ≤ b.toInt
        exact h_le_ab
    · have h_k1_eq1 : k₁ - acc.size = 1 := by omega
      have h_k2_eq1 : k₂ - acc.size = 1 := by omega
      have h_one_lt : (1 : Nat) < (#[a, b] : Array i64).size := by rw [h_two]; omega
      rw [show ((#[a, b] : Array i64)[k₁ - acc.size]'(by rw [h_k1_eq1]; exact h_one_lt))
              = (#[a, b] : Array i64)[1]'h_one_lt from by simp [h_k1_eq1]]
      rw [show ((#[a, b] : Array i64)[k₂ - acc.size]'(by rw [h_k2_eq1]; exact h_one_lt))
              = (#[a, b] : Array i64)[1]'h_one_lt from by simp [h_k2_eq1]]
      show b.toInt ≤ b.toInt
      exact Int.le_refl _

/-! ## `insert_sorted_at_sorted`: insertion sort correctness. -/

private theorem insert_sorted_at_sorted (v : RustSlice i64) (x : i64)
    (h_v_sorted : sorted_asc v.val) :
    ∀ (n : Nat) (i : usize) (inserted : Bool)
      (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      v.val.size - i.toNat ≤ n →
      i.toNat ≤ v.val.size →
      clever_036_sort_even.insert_sorted_at v i x inserted acc = RustM.ok r →
      sorted_asc acc.val →
      (∀ (k : Nat) (hk : k < acc.val.size) (hi_lt : i.toNat < v.val.size),
          (acc.val[k]'hk).toInt ≤ (v.val[i.toNat]'hi_lt).toInt) →
      (inserted = false →
          ∀ (k : Nat) (hk : k < acc.val.size), (acc.val[k]'hk).toInt ≤ x.toInt) →
      sorted_asc r.val := by
  intro n
  induction n with
  | zero =>
    intro i inserted acc r hm hi_le hres h_acc_sorted h_acc_le_vi h_acc_le_x
    have hi_ge : v.val.size ≤ i.toNat := by omega
    cases inserted with
    | true =>
      rw [insert_sorted_at_oob_inserted v i x acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      exact h_acc_sorted
    | false =>
      by_cases h_acc : acc.val.size + 1 < USize64.size
      · rw [insert_sorted_at_oob_not_inserted v i x acc hi_ge h_acc] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        show sorted_asc (acc.val ++ #[x])
        apply sorted_asc_append_singleton acc.val x h_acc_sorted
        exact h_acc_le_x rfl
      · exfalso
        have h_big : USize64.size ≤ acc.val.size + 1 := by omega
        rw [insert_sorted_at_oob_not_inserted_fail v i x acc hi_ge h_big] at hres
        cases hres
  | succ n ih =>
    intro i inserted acc r hm hi_le hres h_acc_sorted h_acc_le_vi h_acc_le_x
    by_cases hi_ge : v.val.size ≤ i.toNat
    · cases inserted with
      | true =>
        rw [insert_sorted_at_oob_inserted v i x acc hi_ge] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        exact h_acc_sorted
      | false =>
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [insert_sorted_at_oob_not_inserted v i x acc hi_ge h_acc] at hres
          injection hres with h_eq
          injection h_eq with h_eq'
          subst h_eq'
          show sorted_asc (acc.val ++ #[x])
          apply sorted_asc_append_singleton acc.val x h_acc_sorted
          exact h_acc_le_x rfl
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_sorted_at_oob_not_inserted_fail v i x acc hi_ge h_big] at hres
          cases hres
    · have hi_lt : i.toNat < v.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ v.val.size := by rw [h_i1]; omega
      have h_meas : v.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      cases inserted with
      | true =>
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [insert_sorted_at_step_pass v i x true acc hi_lt (Or.inl rfl) h_acc] at hres
          have h_new_sorted : sorted_asc (acc.val ++ #[v.val[i.toNat]'hi_lt]) := by
            apply sorted_asc_append_singleton acc.val (v.val[i.toNat]'hi_lt) h_acc_sorted
            intro k hk
            exact h_acc_le_vi k hk hi_lt
          have h_new_le_vi :
              ∀ (k : Nat) (hk : k < (acc.val ++ #[v.val[i.toNat]'hi_lt]).size)
                (hi_i1 : (i + 1).toNat < v.val.size),
                ((acc.val ++ #[v.val[i.toNat]'hi_lt])[k]'hk).toInt
                  ≤ (v.val[(i + 1).toNat]'hi_i1).toInt := by
            intro k hk hi_i1
            rw [Array.size_append] at hk
            have h_one : (#[v.val[i.toNat]'hi_lt] : Array i64).size = 1 := rfl
            by_cases h_k_lt : k < acc.val.size
            · rw [Array.getElem_append_left h_k_lt]
              have h_acc_k := h_acc_le_vi k h_k_lt hi_lt
              have h_v_step : (v.val[i.toNat]'hi_lt).toInt ≤ (v.val[(i + 1).toNat]'hi_i1).toInt := by
                have h_le : i.toNat ≤ (i + 1).toNat := by rw [h_i1]; omega
                exact h_v_sorted i.toNat (i + 1).toNat hi_lt hi_i1 h_le
              omega
            · have h_k_ge : acc.val.size ≤ k := by omega
              rw [Array.getElem_append_right h_k_ge]
              have h_idx : k - acc.val.size = 0 := by omega
              have h_zero_lt : (0 : Nat) < (#[v.val[i.toNat]'hi_lt] : Array i64).size := by
                rw [h_one]; omega
              rw [show ((#[v.val[i.toNat]'hi_lt] : Array i64)[k - acc.val.size]'(by rw [h_idx]; exact h_zero_lt))
                      = (#[v.val[i.toNat]'hi_lt] : Array i64)[0]'h_zero_lt from by simp [h_idx]]
              show (v.val[i.toNat]'hi_lt).toInt ≤ (v.val[(i + 1).toNat]'hi_i1).toInt
              have h_le : i.toNat ≤ (i + 1).toNat := by rw [h_i1]; omega
              exact h_v_sorted i.toNat (i + 1).toNat hi_lt hi_i1 h_le
          exact ih (i + 1) true _ r h_meas h_i1_le hres h_new_sorted h_new_le_vi
            (fun h => by cases h)
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_sorted_at_step_pass_fail v i x true acc hi_lt (Or.inl rfl) h_big] at hres
          cases hres
      | false =>
        by_cases h_vi_ge : (v.val[i.toNat]'hi_lt).toInt ≥ x.toInt
        · by_cases h_acc : acc.val.size + 2 < USize64.size
          · rw [insert_sorted_at_step_insert v i x acc hi_lt h_vi_ge h_acc] at hres
            have h_new_sorted : sorted_asc (acc.val ++ #[x, v.val[i.toNat]'hi_lt]) := by
              apply sorted_asc_append_pair acc.val x (v.val[i.toNat]'hi_lt) h_acc_sorted
              · intro k hk; exact h_acc_le_x rfl k hk
              · exact h_vi_ge
            have h_new_le_vi :
                ∀ (k : Nat) (hk : k < (acc.val ++ #[x, v.val[i.toNat]'hi_lt]).size)
                  (hi_i1 : (i + 1).toNat < v.val.size),
                  ((acc.val ++ #[x, v.val[i.toNat]'hi_lt])[k]'hk).toInt
                    ≤ (v.val[(i + 1).toNat]'hi_i1).toInt := by
              intro k hk hi_i1
              rw [Array.size_append] at hk
              have h_two : (#[x, v.val[i.toNat]'hi_lt] : Array i64).size = 2 := rfl
              have h_v_step : (v.val[i.toNat]'hi_lt).toInt ≤ (v.val[(i + 1).toNat]'hi_i1).toInt := by
                have h_le : i.toNat ≤ (i + 1).toNat := by rw [h_i1]; omega
                exact h_v_sorted i.toNat (i + 1).toNat hi_lt hi_i1 h_le
              by_cases h_k_lt : k < acc.val.size
              · rw [Array.getElem_append_left h_k_lt]
                have h_acc_k := h_acc_le_vi k h_k_lt hi_lt
                omega
              · have h_k_ge : acc.val.size ≤ k := by omega
                rw [Array.getElem_append_right h_k_ge]
                by_cases h_k_eq0 : k - acc.val.size = 0
                · have h_zero_lt : (0 : Nat) < (#[x, v.val[i.toNat]'hi_lt] : Array i64).size := by
                    rw [h_two]; omega
                  rw [show ((#[x, v.val[i.toNat]'hi_lt] : Array i64)[k - acc.val.size]'(by rw [h_k_eq0]; exact h_zero_lt))
                          = (#[x, v.val[i.toNat]'hi_lt] : Array i64)[0]'h_zero_lt from by simp [h_k_eq0]]
                  show x.toInt ≤ (v.val[(i + 1).toNat]'hi_i1).toInt
                  omega
                · have h_k_eq1 : k - acc.val.size = 1 := by omega
                  have h_one_lt : (1 : Nat) < (#[x, v.val[i.toNat]'hi_lt] : Array i64).size := by
                    rw [h_two]; omega
                  rw [show ((#[x, v.val[i.toNat]'hi_lt] : Array i64)[k - acc.val.size]'(by rw [h_k_eq1]; exact h_one_lt))
                          = (#[x, v.val[i.toNat]'hi_lt] : Array i64)[1]'h_one_lt from by simp [h_k_eq1]]
                  show (v.val[i.toNat]'hi_lt).toInt ≤ (v.val[(i + 1).toNat]'hi_i1).toInt
                  exact h_v_step
            exact ih (i + 1) true _ r h_meas h_i1_le hres h_new_sorted h_new_le_vi
              (fun h => by cases h)
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 2 := by omega
            rw [insert_sorted_at_step_insert_fail v i x acc hi_lt h_vi_ge h_big] at hres
            cases hres
        · have h_lt : (v.val[i.toNat]'hi_lt).toInt < x.toInt := by omega
          by_cases h_acc : acc.val.size + 1 < USize64.size
          · rw [insert_sorted_at_step_pass v i x false acc hi_lt (Or.inr h_lt) h_acc] at hres
            have h_new_sorted : sorted_asc (acc.val ++ #[v.val[i.toNat]'hi_lt]) := by
              apply sorted_asc_append_singleton acc.val (v.val[i.toNat]'hi_lt) h_acc_sorted
              intro k hk
              exact h_acc_le_vi k hk hi_lt
            have h_new_le_vi :
                ∀ (k : Nat) (hk : k < (acc.val ++ #[v.val[i.toNat]'hi_lt]).size)
                  (hi_i1 : (i + 1).toNat < v.val.size),
                  ((acc.val ++ #[v.val[i.toNat]'hi_lt])[k]'hk).toInt
                    ≤ (v.val[(i + 1).toNat]'hi_i1).toInt := by
              intro k hk hi_i1
              rw [Array.size_append] at hk
              have h_one : (#[v.val[i.toNat]'hi_lt] : Array i64).size = 1 := rfl
              have h_v_step : (v.val[i.toNat]'hi_lt).toInt ≤ (v.val[(i + 1).toNat]'hi_i1).toInt := by
                have h_le : i.toNat ≤ (i + 1).toNat := by rw [h_i1]; omega
                exact h_v_sorted i.toNat (i + 1).toNat hi_lt hi_i1 h_le
              by_cases h_k_lt : k < acc.val.size
              · rw [Array.getElem_append_left h_k_lt]
                have h_acc_k := h_acc_le_vi k h_k_lt hi_lt
                omega
              · have h_k_ge : acc.val.size ≤ k := by omega
                rw [Array.getElem_append_right h_k_ge]
                have h_idx : k - acc.val.size = 0 := by omega
                have h_zero_lt : (0 : Nat) < (#[v.val[i.toNat]'hi_lt] : Array i64).size := by
                  rw [h_one]; omega
                rw [show ((#[v.val[i.toNat]'hi_lt] : Array i64)[k - acc.val.size]'(by rw [h_idx]; exact h_zero_lt))
                        = (#[v.val[i.toNat]'hi_lt] : Array i64)[0]'h_zero_lt from by simp [h_idx]]
                exact h_v_step
            have h_new_le_x :
                false = false → ∀ (k : Nat) (hk : k < (acc.val ++ #[v.val[i.toNat]'hi_lt]).size),
                  ((acc.val ++ #[v.val[i.toNat]'hi_lt])[k]'hk).toInt ≤ x.toInt := by
              intro _ k hk
              rw [Array.size_append] at hk
              have h_one : (#[v.val[i.toNat]'hi_lt] : Array i64).size = 1 := rfl
              by_cases h_k_lt : k < acc.val.size
              · rw [Array.getElem_append_left h_k_lt]
                exact h_acc_le_x rfl k h_k_lt
              · have h_k_ge : acc.val.size ≤ k := by omega
                rw [Array.getElem_append_right h_k_ge]
                have h_idx : k - acc.val.size = 0 := by omega
                have h_zero_lt : (0 : Nat) < (#[v.val[i.toNat]'hi_lt] : Array i64).size := by
                  rw [h_one]; omega
                rw [show ((#[v.val[i.toNat]'hi_lt] : Array i64)[k - acc.val.size]'(by rw [h_idx]; exact h_zero_lt))
                        = (#[v.val[i.toNat]'hi_lt] : Array i64)[0]'h_zero_lt from by simp [h_idx]]
                show (v.val[i.toNat]'hi_lt).toInt ≤ x.toInt
                omega
            exact ih (i + 1) false _ r h_meas h_i1_le hres h_new_sorted h_new_le_vi h_new_le_x
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 1 := by omega
            rw [insert_sorted_at_step_pass_fail v i x false acc hi_lt (Or.inr h_lt) h_big] at hres
            cases hres

private theorem insert_sorted_sorted (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (r : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_036_sort_even.insert_sorted v x = RustM.ok r)
    (h_v_sorted : sorted_asc v.val) :
    sorted_asc r.val := by
  unfold clever_036_sort_even.insert_sorted at hres
  have h_deref :
      (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec i64 alloc.alloc.Global) v : RustM _) = RustM.ok v := rfl
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_deref, h_new] at hres
  simp only [RustM_ok_bind] at hres
  -- hres : insert_sorted_at v 0 x false #[] = ok r
  -- (Vec and RustSlice are both Seq via abbrev, so this matches.)
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_meas : v.val.size - (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  have h_le : (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  have h_empty_sorted : sorted_asc ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val := by
    intro k₁ k₂ h₁ _ _
    have : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  have h_empty_le_vi :
      ∀ (k : Nat) (hk : k < ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size)
        (_ : (0 : usize).toNat < v.val.size),
      (((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val[k]'hk).toInt
        ≤ (v.val[(0 : usize).toNat]'(by assumption)).toInt := by
    intro k hk _
    have h_empty : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  have h_empty_le_x : false = false →
      ∀ (k : Nat) (hk : k < ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size),
      (((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val[k]'hk).toInt ≤ x.toInt := by
    intro _ k hk
    have h_empty : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  exact insert_sorted_at_sorted v x h_v_sorted v.val.size (0 : usize) false
    ⟨(List.nil).toArray, by grind⟩ r h_meas h_le hres h_empty_sorted h_empty_le_vi h_empty_le_x

/-! ## `collect_evens` invariant: size and count. -/

private theorem collect_evens_inv :
    ∀ (n : Nat) (l : RustSlice i64)
      (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global) (target : i64),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      clever_036_sort_even.collect_evens l i acc = RustM.ok r →
      r.val.size = acc.val.size + ((l.val.size + 1) / 2 - (i.toNat + 1) / 2) ∧
      total_count r.val target r.val.size + count_evens l.val target i.toNat =
        total_count acc.val target acc.val.size + count_evens l.val target l.val.size := by
  intro n
  induction n with
  | zero =>
    intro l i acc r target hm hi_le hres
    have hi_ge : l.val.size ≤ i.toNat := by omega
    have hi_eq : i.toNat = l.val.size := by omega
    rw [collect_evens_oob l i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    refine ⟨?_, ?_⟩
    · have h_E_zero : (l.val.size + 1) / 2 - (i.toNat + 1) / 2 = 0 := by rw [hi_eq]; omega
      rw [h_E_zero]
    · rw [hi_eq]
  | succ n ih =>
    intro l i acc r target hm hi_le hres
    by_cases hi_ge : l.val.size ≤ i.toNat
    · have hi_eq : i.toNat = l.val.size := by omega
      rw [collect_evens_oob l i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      refine ⟨?_, ?_⟩
      · have h_E_zero : (l.val.size + 1) / 2 - (i.toNat + 1) / 2 = 0 := by rw [hi_eq]; omega
        rw [h_E_zero]
      · rw [hi_eq]
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_meas : l.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      have h_count_evens_succ_l :
          count_evens l.val target (i.toNat + 1) =
            (if i.toNat % 2 = 0 ∧ l.val[i.toNat]'hi_lt = target then 1 else 0) +
            count_evens l.val target i.toNat :=
        count_evens_succ l.val target i.toNat hi_lt
      by_cases heven : i.toNat % 2 = 0
      · -- Even step: calls insert_sorted acc l[i]
        rw [collect_evens_step_even l i acc hi_lt heven] at hres
        generalize h_ins : clever_036_sort_even.insert_sorted acc (l.val[i.toNat]'hi_lt) = ins_res at hres
        cases ins_res with
        | none =>
          exfalso
          have hh : (do let acc' ← (none : RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                         clever_036_sort_even.collect_evens l (i + 1) acc')
                    = RustM.ok r := hres
          cases hh
        | some res' =>
          cases res' with
          | error e =>
            exfalso
            have hh : (do let acc' ← (some (Except.error e) :
                                        RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                           clever_036_sort_even.collect_evens l (i + 1) acc')
                      = RustM.ok r := hres
            cases hh
          | ok acc' =>
            have h_ins_ok : clever_036_sort_even.insert_sorted acc (l.val[i.toNat]'hi_lt) = RustM.ok acc' :=
              h_ins
            simp only [RustM_ok_bind] at hres
            -- Apply insert_sorted_inv
            have h_ins_inv := insert_sorted_inv acc (l.val[i.toNat]'hi_lt) acc' target h_ins_ok
            obtain ⟨h_acc'_size, h_acc'_count⟩ := h_ins_inv
            -- Apply IH
            have ih_app := ih l (i + 1) acc' r target h_meas h_i1_le hres
            rw [h_i1] at ih_app
            obtain ⟨h_size_eq, h_count_eq⟩ := ih_app
            rw [h_acc'_size] at h_size_eq
            rw [h_acc'_count] at h_count_eq
            -- Simplify E with i even
            have h_E_succ :
                (l.val.size + 1) / 2 - (i.toNat + 1) / 2 =
                  ((l.val.size + 1) / 2 - (i.toNat + 1 + 1) / 2) + 1 := by
              have hA : (i.toNat + 1) / 2 = i.toNat / 2 := by omega
              have hB : (i.toNat + 1 + 1) / 2 = i.toNat / 2 + 1 := by omega
              have hC : i.toNat / 2 + 1 ≤ (l.val.size + 1) / 2 := by omega
              omega
            refine ⟨?_, ?_⟩
            · rw [h_size_eq, h_E_succ]; omega
            · rw [h_count_evens_succ_l] at h_count_eq
              -- Now h_count_eq has: (if i even ∧ l[i]=t then 1 else 0) + count_evens l target i
              -- Case on l[i] = target
              by_cases h_li : l.val[i.toNat]'hi_lt = target
              · rw [if_pos (And.intro heven h_li)] at h_count_eq
                rw [if_pos h_li] at h_count_eq
                omega
              · rw [if_neg (fun h => h_li h.right)] at h_count_eq
                rw [if_neg h_li] at h_count_eq
                omega
      · -- Odd step
        have hodd : i.toNat % 2 = 1 := by omega
        rw [collect_evens_step_odd l i acc hi_lt hodd] at hres
        have ih_app := ih l (i + 1) acc r target h_meas h_i1_le hres
        rw [h_i1] at ih_app
        obtain ⟨h_size_eq, h_count_eq⟩ := ih_app
        have h_E_same :
            (l.val.size + 1) / 2 - (i.toNat + 1) / 2 =
              (l.val.size + 1) / 2 - ((i.toNat + 1) + 1) / 2 := by
          have h1 : (i.toNat + 1) / 2 = i.toNat / 2 + 1 := by omega
          have h2 : ((i.toNat + 1) + 1) / 2 = i.toNat / 2 + 1 := by omega
          omega
        refine ⟨?_, ?_⟩
        · rw [h_size_eq, h_E_same]
        · rw [h_count_evens_succ_l] at h_count_eq
          have h_odd_check : ¬ (i.toNat % 2 = 0 ∧ l.val[i.toNat]'hi_lt = target) := by
            intro h; rw [h.left] at hodd; omega
          rw [if_neg h_odd_check] at h_count_eq
          omega

/-! ## `collect_evens_sorted`: collect_evens preserves sortedness. -/

private theorem collect_evens_sorted :
    ∀ (n : Nat) (l : RustSlice i64)
      (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      clever_036_sort_even.collect_evens l i acc = RustM.ok r →
      sorted_asc acc.val →
      sorted_asc r.val := by
  intro n
  induction n with
  | zero =>
    intro l i acc r hm hi_le hres h_acc_sorted
    have hi_ge : l.val.size ≤ i.toNat := by omega
    rw [collect_evens_oob l i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    exact h_acc_sorted
  | succ n ih =>
    intro l i acc r hm hi_le hres h_acc_sorted
    by_cases hi_ge : l.val.size ≤ i.toNat
    · rw [collect_evens_oob l i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      exact h_acc_sorted
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_meas : l.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      by_cases heven : i.toNat % 2 = 0
      · rw [collect_evens_step_even l i acc hi_lt heven] at hres
        generalize h_ins : clever_036_sort_even.insert_sorted acc (l.val[i.toNat]'hi_lt) = ins_res at hres
        cases ins_res with
        | none =>
          exfalso
          have hh : (do let acc' ← (none : RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                         clever_036_sort_even.collect_evens l (i + 1) acc')
                    = RustM.ok r := hres
          cases hh
        | some res' =>
          cases res' with
          | error e =>
            exfalso
            have hh : (do let acc' ← (some (Except.error e) :
                                        RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                           clever_036_sort_even.collect_evens l (i + 1) acc')
                      = RustM.ok r := hres
            cases hh
          | ok acc' =>
            have h_ins_ok : clever_036_sort_even.insert_sorted acc (l.val[i.toNat]'hi_lt) = RustM.ok acc' :=
              h_ins
            simp only [RustM_ok_bind] at hres
            -- Apply insert_sorted_sorted
            have h_acc'_sorted : sorted_asc acc'.val :=
              insert_sorted_sorted acc (l.val[i.toNat]'hi_lt) acc' h_ins_ok h_acc_sorted
            exact ih l (i + 1) acc' r h_meas h_i1_le hres h_acc'_sorted
      · have hodd : i.toNat % 2 = 1 := by omega
        rw [collect_evens_step_odd l i acc hi_lt hodd] at hres
        exact ih l (i + 1) acc r h_meas h_i1_le hres h_acc_sorted

/-! ## `rebuild_at_even_indices`: at even output position k, v[k] = sorted[k/2 - i.toNat/2 + j.toNat].

Specialized for the initial call (i=0, j=0), this gives v[k] = sorted[k/2] for even k. -/

private theorem rebuild_at_even_indices :
    ∀ (n : Nat) (l : RustSlice i64) (sorted : RustSlice i64)
      (i j : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      acc.val.size = i.toNat →
      j.toNat ≤ sorted.val.size →
      clever_036_sort_even.rebuild_at l sorted i j acc = RustM.ok r →
      ∀ (k : Nat) (hk_r : k < r.val.size) (hk_even : k % 2 = 0)
        (hk_lt_l : k < l.val.size) (hk_ge_i : i.toNat ≤ k),
        -- Position k in r corresponds to position `j.toNat + (#evens in [i.toNat, k))` in sorted.
        -- #evens in [i.toNat, k) when both i, k are even = (k - i.toNat) / 2
        -- (since i.toNat is even and we go i, i+1, ..., k-1: evens are i, i+2, ..., k-2)
        -- Actually #evens in [i.toNat, k) = (k - i.toNat + 1) / 2 when i.toNat even.
        --                                = (k - i.toNat) / 2 when i.toNat odd.
        -- For simplicity: (k+1)/2 - (i.toNat+1)/2
        ∃ (hj : j.toNat + ((k + 1) / 2 - (i.toNat + 1) / 2) < sorted.val.size),
        r.val[k]'hk_r = sorted.val[j.toNat + ((k + 1) / 2 - (i.toNat + 1) / 2)]'hj := by
  intro n
  induction n with
  | zero =>
    intro l sorted i j acc r hm hi_le h_acc_eq h_j_le hres k hk_r hk_even hk_lt_l hk_ge_i
    exfalso; omega
  | succ n ih =>
    intro l sorted i j acc r hm hi_le h_acc_eq h_j_le hres k hk_r hk_even hk_lt_l hk_ge_i
    by_cases hi_ge : l.val.size ≤ i.toNat
    · exfalso; omega
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_meas : l.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      by_cases heven : i.toNat % 2 = 0
      · -- Even step. Use sorted[j] at position acc.size = i.toNat.
        by_cases hj : j.toNat < sorted.val.size
        · by_cases h_acc : acc.val.size + 1 < USize64.size
          · rw [rebuild_at_step_even l sorted i j acc hi_lt heven hj h_acc] at hres
            have h_push_size :
                (push_one acc (sorted.val[j.toNat]'hj) h_acc).val.size = acc.val.size + 1 := by
              show (acc.val ++ #[sorted.val[j.toNat]'hj]).size = acc.val.size + 1
              rw [Array.size_append]; rfl
            have h_acc_new_eq :
                (push_one acc (sorted.val[j.toNat]'hj) h_acc).val.size = (i + 1).toNat := by
              rw [h_push_size, h_acc_eq, h_i1]
            have h_size_lt_s : sorted.val.size < USize64.size := sorted.size_lt_usizeSize
            have h_no_ov_j : j.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt_s; omega
            have h_j1 : (j + 1).toNat = j.toNat + 1 := usize_add_one_toNat j h_no_ov_j
            have h_j1_le : (j + 1).toNat ≤ sorted.val.size := by rw [h_j1]; omega
            by_cases h_eq_k : k = i.toNat
            · -- k = i.toNat: the just-appended sorted[j]
              subst h_eq_k
              have hk_push : i.toNat < (push_one acc (sorted.val[j.toNat]'hj) h_acc).val.size := by
                rw [h_push_size, h_acc_eq]; omega
              have h_prefix := rebuild_at_prefix_preserved _ l sorted (i + 1) (j + 1)
                (push_one acc (sorted.val[j.toNat]'hj) h_acc) r (Nat.le_refl _) h_i1_le hres
                i.toNat hk_push hk_r
              rw [h_prefix]
              have h_index_eq : (i.toNat + 1) / 2 - (i.toNat + 1) / 2 = 0 := by omega
              refine ⟨?_, ?_⟩
              · rw [h_index_eq]; rw [Nat.add_zero]; exact hj
              · show ((acc.val ++ #[sorted.val[j.toNat]'hj])[i.toNat]'hk_push) =
                  sorted.val[j.toNat + ((i.toNat + 1) / 2 - (i.toNat + 1) / 2)]'(by rw [h_index_eq, Nat.add_zero]; exact hj)
                have h_acc_le_i : acc.val.size ≤ i.toNat := by rw [h_acc_eq]; exact Nat.le_refl _
                rw [Array.getElem_append_right h_acc_le_i]
                have h_sub_zero : i.toNat - acc.val.size = 0 := by rw [h_acc_eq]; omega
                simp [h_sub_zero, h_index_eq]
            · -- k > i.toNat (since hk_ge_i + k ≠ i.toNat). Apply IH.
              have hk_gt_i : i.toNat < k := by omega
              have hk_ge_i1 : (i + 1).toNat ≤ k := by rw [h_i1]; omega
              -- IH with (i+1, j+1, push_one acc sorted[j]) gives a proof.
              -- The IH conclusion involves (i+1).toNat instead of i.toNat.
              have ih_app := ih l sorted (i + 1) (j + 1)
                (push_one acc (sorted.val[j.toNat]'hj) h_acc) r h_meas h_i1_le
                h_acc_new_eq h_j1_le hres k hk_r hk_even hk_lt_l hk_ge_i1
              obtain ⟨hj', h_val⟩ := ih_app
              -- ih: r[k] = sorted[(j+1).toNat + ((k+1)/2 - ((i+1).toNat + 1)/2)]
              -- We want: r[k] = sorted[j.toNat + ((k+1)/2 - (i.toNat+1)/2)]
              -- Show these indices are equal:
              -- j.toNat + ((k+1)/2 - (i.toNat+1)/2) = (j+1).toNat + ((k+1)/2 - ((i+1).toNat+1)/2)
              -- j.toNat + ((k+1)/2 - i.toNat/2) = j.toNat + 1 + ((k+1)/2 - (i.toNat+2)/2)
              -- Since i.toNat even: i.toNat/2 = (i.toNat+1)/2, (i.toNat+2)/2 = i.toNat/2 + 1
              -- So LHS = j.toNat + ((k+1)/2 - i.toNat/2)
              --    RHS = j.toNat + 1 + ((k+1)/2 - i.toNat/2 - 1) = j.toNat + ((k+1)/2 - i.toNat/2)  ✓
              have h_idx_eq :
                  j.toNat + ((k + 1) / 2 - (i.toNat + 1) / 2) =
                  (j + 1).toNat + ((k + 1) / 2 - ((i + 1).toNat + 1) / 2) := by
                rw [h_j1, h_i1]
                have h1 : (i.toNat + 1) / 2 = i.toNat / 2 := by omega
                have h2 : (i.toNat + 1 + 1) / 2 = i.toNat / 2 + 1 := by omega
                have h3 : i.toNat / 2 + 1 ≤ (k + 1) / 2 := by omega
                omega
              refine ⟨?_, ?_⟩
              · rw [h_idx_eq]; exact hj'
              · rw [h_val]
                congr 1
                exact h_idx_eq.symm
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 1 := by omega
            rw [rebuild_at_step_even_size_fail l sorted i j acc hi_lt heven hj h_big] at hres
            cases hres
        · exfalso
          have hj_ge : sorted.val.size ≤ j.toNat := Nat.le_of_not_lt hj
          rw [rebuild_at_step_even_idx_fail l sorted i j acc hi_lt heven hj_ge] at hres
          cases hres
      · -- Odd step. k must be > i.toNat since i is odd and k is even.
        have hodd : i.toNat % 2 = 1 := by omega
        have hk_ne_i : k ≠ i.toNat := by intro h; rw [h] at hk_even; omega
        have hk_ge_i1 : (i + 1).toNat ≤ k := by rw [h_i1]; omega
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [rebuild_at_step_odd l sorted i j acc hi_lt hodd h_acc] at hres
          have h_push_size :
              (push_one acc (l.val[i.toNat]'hi_lt) h_acc).val.size = acc.val.size + 1 := by
            show (acc.val ++ #[l.val[i.toNat]'hi_lt]).size = acc.val.size + 1
            rw [Array.size_append]; rfl
          have h_acc_new_eq :
              (push_one acc (l.val[i.toNat]'hi_lt) h_acc).val.size = (i + 1).toNat := by
            rw [h_push_size, h_acc_eq, h_i1]
          have ih_app := ih l sorted (i + 1) j
            (push_one acc (l.val[i.toNat]'hi_lt) h_acc) r h_meas h_i1_le
            h_acc_new_eq h_j_le hres k hk_r hk_even hk_lt_l hk_ge_i1
          obtain ⟨hj', h_val⟩ := ih_app
          have h_idx_eq :
              j.toNat + ((k + 1) / 2 - (i.toNat + 1) / 2) =
              j.toNat + ((k + 1) / 2 - ((i + 1).toNat + 1) / 2) := by
            rw [h_i1]
            have h1 : (i.toNat + 1) / 2 = i.toNat / 2 + 1 := by omega
            have h2 : (i.toNat + 1 + 1) / 2 = i.toNat / 2 + 1 := by omega
            omega
          refine ⟨?_, ?_⟩
          · rw [h_idx_eq]; exact hj'
          · rw [h_val]; congr 1; exact h_idx_eq.symm
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [rebuild_at_step_odd_size_fail l sorted i j acc hi_lt hodd h_big] at hres
          cases hres

/-! ## Theorem statements.

Each of the five obligations below corresponds to one property test in
the Rust source. Proofs are `sorry` and are filled in by the proof
stage. Stated universally in the slice size: the function only shuffles
`i64` values (no value-level arithmetic), and every intermediate
`extend_from_slice` keeps the accumulator bounded by `2^64` (the
half-size `sorted` vec built by `collect_evens` reaches at most
`(l.val.size + 1) / 2 ≤ 2^63`, and the final `rebuild_at` accumulator
reaches at most `l.val.size < 2^64`), so no precondition on
`l.val.size` is required. -/

/-- Anchor: empty input yields a successful empty output. Captures the
    Rust unit test `empty_input`. -/
theorem sort_even_empty_input_yields_empty_output
    (l : RustSlice i64) (hempty : l.val.size = 0) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_036_sort_even.sort_even l = RustM.ok v ∧ v.val.size = 0 := by
  refine ⟨⟨#[], by decide⟩, ?_, rfl⟩
  unfold clever_036_sort_even.sort_even
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new]
  simp only [RustM_ok_bind]
  have h_zero_le : l.val.size ≤ (0 : usize).toNat := by
    rw [usize_zero_toNat]; omega
  have h_collect_oob :
      clever_036_sort_even.collect_evens l (0 : usize)
        ⟨(List.nil).toArray, by grind⟩
      = RustM.ok ⟨(List.nil).toArray, by grind⟩ :=
    collect_evens_oob l (0 : usize) ⟨(List.nil).toArray, by grind⟩ h_zero_le
  rw [h_collect_oob]
  simp only [RustM_ok_bind]
  have h_deref :
      (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec i64 alloc.alloc.Global)
        ⟨(List.nil).toArray, by grind⟩ :
        RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
        RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_deref]
  simp only [RustM_ok_bind]
  -- Now the goal is rebuild_at l deref(sorted) 0 0 #[] = ok #[]
  -- Since l.val.size = 0, rebuild_at returns acc directly.
  exact rebuild_at_oob l ⟨(List.nil).toArray, by grind⟩ (0 : usize) (0 : usize)
      ⟨(List.nil).toArray, by grind⟩ h_zero_le

/-- Length-preservation postcondition: `out.len() = l.len()`. Captures
    the Rust proptest `length_preserved`. -/
theorem sort_even_length_preserved
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_036_sort_even.sort_even l = RustM.ok v) :
    v.val.size = l.val.size := by
  -- Reduce hres to expose the rebuild_at call.
  unfold clever_036_sort_even.sort_even at hres
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  -- Case on collect_evens' result.
  generalize h_collect :
      clever_036_sort_even.collect_evens l (0 : usize) ⟨(List.nil).toArray, by grind⟩ = ce_res at hres
  cases ce_res with
  | none =>
    exfalso
    have hh : (do let sorted ← (none : RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                  let sorted_deref ← (core_models.ops.deref.Deref.deref
                    (alloc.vec.Vec i64 alloc.alloc.Global) sorted :
                    RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                  let acc0 ← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                              RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                  clever_036_sort_even.rebuild_at l sorted_deref (0 : usize) (0 : usize) acc0)
              = RustM.ok v := hres
    cases hh
  | some ce_res' =>
    cases ce_res' with
    | error e =>
      exfalso
      have hh : (do let sorted ← (some (Except.error e) :
                                    RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                    let sorted_deref ← (core_models.ops.deref.Deref.deref
                      (alloc.vec.Vec i64 alloc.alloc.Global) sorted :
                      RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                    let acc0 ← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                                RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                    clever_036_sort_even.rebuild_at l sorted_deref (0 : usize) (0 : usize) acc0)
                = RustM.ok v := hres
      cases hh
    | ok sorted =>
      simp only [RustM_ok_bind] at hres
      have h_deref :
          (core_models.ops.deref.Deref.deref
            (alloc.vec.Vec i64 alloc.alloc.Global) sorted : RustM _) = RustM.ok sorted := rfl
      rw [h_deref] at hres
      simp only [RustM_ok_bind] at hres
      -- hres : rebuild_at l sorted 0 0 #[] = ok v
      have h_zero_toNat : (0 : usize).toNat = 0 := rfl
      have h_meas : l.val.size - (0 : usize).toNat ≤ l.val.size := by rw [h_zero_toNat]; omega
      have h_le : (0 : usize).toNat ≤ l.val.size := by rw [h_zero_toNat]; omega
      have h_size :=
        rebuild_at_size l.val.size l sorted (0 : usize) (0 : usize)
          ⟨(List.nil).toArray, by grind⟩ v h_meas h_le hres
      have h_empty : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
      rw [h_empty, h_zero_toNat] at h_size
      omega

/-- Odd-index identity postcondition: at every odd index `i`, the output
    equals the input pointwise. Captures the Rust proptest
    `odd_indices_unchanged`. -/
theorem sort_even_odd_indices_unchanged
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_036_sort_even.sort_even l = RustM.ok v)
    (i : Nat) (hi_v : i < v.val.size) (hi_l : i < l.val.size)
    (hodd : i % 2 = 1) :
    v.val[i]'hi_v = l.val[i]'hi_l := by
  unfold clever_036_sort_even.sort_even at hres
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  generalize h_collect :
      clever_036_sort_even.collect_evens l (0 : usize) ⟨(List.nil).toArray, by grind⟩ = ce_res at hres
  cases ce_res with
  | none =>
    exfalso
    have hh : (do let sorted ← (none : RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                  let sorted_deref ← (core_models.ops.deref.Deref.deref
                    (alloc.vec.Vec i64 alloc.alloc.Global) sorted :
                    RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                  let acc0 ← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                              RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                  clever_036_sort_even.rebuild_at l sorted_deref (0 : usize) (0 : usize) acc0)
              = RustM.ok v := hres
    cases hh
  | some ce_res' =>
    cases ce_res' with
    | error e =>
      exfalso
      have hh : (do let sorted ← (some (Except.error e) :
                                    RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                    let sorted_deref ← (core_models.ops.deref.Deref.deref
                      (alloc.vec.Vec i64 alloc.alloc.Global) sorted :
                      RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                    let acc0 ← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                                RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                    clever_036_sort_even.rebuild_at l sorted_deref (0 : usize) (0 : usize) acc0)
                = RustM.ok v := hres
      cases hh
    | ok sorted =>
      simp only [RustM_ok_bind] at hres
      have h_deref :
          (core_models.ops.deref.Deref.deref
            (alloc.vec.Vec i64 alloc.alloc.Global) sorted : RustM _) = RustM.ok sorted := rfl
      rw [h_deref] at hres
      simp only [RustM_ok_bind] at hres
      have h_zero_toNat : (0 : usize).toNat = 0 := rfl
      have h_meas : l.val.size - (0 : usize).toNat ≤ l.val.size := by rw [h_zero_toNat]; omega
      have h_le : (0 : usize).toNat ≤ l.val.size := by rw [h_zero_toNat]; omega
      have h_acc_eq : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = (0 : usize).toNat := by
        rw [h_zero_toNat]; rfl
      have h_ge_i : (0 : usize).toNat ≤ i := by rw [h_zero_toNat]; omega
      exact rebuild_at_odd_indices l.val.size l sorted (0 : usize) (0 : usize)
        ⟨(List.nil).toArray, by grind⟩ v h_meas h_le h_acc_eq hres
        i hi_v hodd hi_l h_ge_i

/-- Even-index sorted postcondition: at consecutive even output
    positions `k` and `k + 2`, the values are non-decreasing. Stated on
    pairs of stride-2 entries — exactly the proptest's `windows(2)` form
    over the `step_by(2)` projection. Captures the Rust proptest
    `even_indices_sorted`. -/
theorem sort_even_even_indices_sorted
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_036_sort_even.sort_even l = RustM.ok v)
    (k : Nat) (hk : k + 2 < v.val.size) (heven : k % 2 = 0) :
    (v.val[k]'(Nat.lt_of_succ_lt (Nat.lt_of_succ_lt hk))).toInt ≤
      (v.val[k + 2]'hk).toInt := by
  unfold clever_036_sort_even.sort_even at hres
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  generalize h_collect :
      clever_036_sort_even.collect_evens l (0 : usize) ⟨(List.nil).toArray, by grind⟩ = ce_res at hres
  cases ce_res with
  | none =>
    exfalso
    have hh : (do let sorted ← (none : RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                  let sorted_deref ← (core_models.ops.deref.Deref.deref
                    (alloc.vec.Vec i64 alloc.alloc.Global) sorted :
                    RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                  let acc0 ← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                              RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                  clever_036_sort_even.rebuild_at l sorted_deref (0 : usize) (0 : usize) acc0)
              = RustM.ok v := hres
    cases hh
  | some ce_res' =>
    cases ce_res' with
    | error e =>
      exfalso
      have hh : (do let sorted ← (some (Except.error e) :
                                    RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                    let sorted_deref ← (core_models.ops.deref.Deref.deref
                      (alloc.vec.Vec i64 alloc.alloc.Global) sorted :
                      RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                    let acc0 ← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                                RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                    clever_036_sort_even.rebuild_at l sorted_deref (0 : usize) (0 : usize) acc0)
                = RustM.ok v := hres
      cases hh
    | ok sorted =>
      have h_collect_ok :
          clever_036_sort_even.collect_evens l (0 : usize) ⟨(List.nil).toArray, by grind⟩
            = RustM.ok sorted := h_collect
      simp only [RustM_ok_bind] at hres
      have h_deref :
          (core_models.ops.deref.Deref.deref
            (alloc.vec.Vec i64 alloc.alloc.Global) sorted : RustM _) = RustM.ok sorted := rfl
      rw [h_deref] at hres
      simp only [RustM_ok_bind] at hres
      -- hres : rebuild_at l sorted 0 0 #[] = ok v
      have h_zero_toNat : (0 : usize).toNat = 0 := rfl
      have h_meas : l.val.size - (0 : usize).toNat ≤ l.val.size := by rw [h_zero_toNat]; omega
      have h_le : (0 : usize).toNat ≤ l.val.size := by rw [h_zero_toNat]; omega
      -- Step 1: sorted is sorted_asc.
      have h_empty_sorted : sorted_asc ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val := by
        intro k₁ k₂ h₁ _ _
        have : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
        omega
      have h_sorted_sorted : sorted_asc sorted.val :=
        collect_evens_sorted l.val.size l (0 : usize) ⟨(List.nil).toArray, by grind⟩
          sorted h_meas h_le h_collect_ok h_empty_sorted
      -- Step 2: length of v is l.val.size, so k+2 < v.val.size means k+2 < l.val.size.
      have h_v_size := sort_even_length_preserved l v (by
        unfold clever_036_sort_even.sort_even
        rw [h_new]
        simp only [RustM_ok_bind]
        rw [h_collect_ok]
        simp only [RustM_ok_bind]
        rw [h_deref]
        simp only [RustM_ok_bind]
        exact hres)
      have hk_lt_l : k + 2 < l.val.size := by rw [← h_v_size]; exact hk
      have hk_l_minus_2 : k < l.val.size := Nat.lt_of_succ_lt (Nat.lt_of_succ_lt hk_lt_l)
      -- Step 3: rebuild_at gives v[k] = sorted[?]
      have h_acc_eq : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = (0 : usize).toNat := by
        rw [h_zero_toNat]; rfl
      have h_j_le : (0 : usize).toNat ≤ sorted.val.size := by rw [h_zero_toNat]; omega
      have h_k_lt_r : k < v.val.size := Nat.lt_of_succ_lt (Nat.lt_of_succ_lt hk)
      have h_k_ge_zero : (0 : usize).toNat ≤ k := by rw [h_zero_toNat]; omega
      have h_inv_k := rebuild_at_even_indices l.val.size l sorted (0 : usize) (0 : usize)
        ⟨(List.nil).toArray, by grind⟩ v h_meas h_le h_acc_eq h_j_le hres
        k h_k_lt_r heven hk_l_minus_2 h_k_ge_zero
      obtain ⟨hj1, h_val_k⟩ := h_inv_k
      have h_k2_even : (k + 2) % 2 = 0 := by omega
      have h_inv_k2 := rebuild_at_even_indices l.val.size l sorted (0 : usize) (0 : usize)
        ⟨(List.nil).toArray, by grind⟩ v h_meas h_le h_acc_eq h_j_le hres
        (k + 2) hk h_k2_even hk_lt_l (by rw [h_zero_toNat]; omega)
      obtain ⟨hj2, h_val_k2⟩ := h_inv_k2
      -- Step 4: simplify indices
      -- For k (even), j.toNat + ((k+1)/2 - (0+1)/2) = 0 + ((k+1)/2 - 0) = (k+1)/2 = k/2
      -- (since k is even, (k+1)/2 = k/2)
      have h_idx_k_eq :
          ((0 : usize).toNat + ((k + 1) / 2 - ((0 : usize).toNat + 1) / 2)) = k / 2 := by
        rw [h_zero_toNat]; omega
      have h_idx_k2_eq :
          ((0 : usize).toNat + ((k + 2 + 1) / 2 - ((0 : usize).toNat + 1) / 2)) = k / 2 + 1 := by
        rw [h_zero_toNat]; omega
      -- Now we have: v[k] = sorted[idx_k] = sorted[k/2]
      --              v[k+2] = sorted[idx_k2] = sorted[k/2 + 1]
      -- And sortedness gives: sorted[k/2].toInt ≤ sorted[k/2 + 1].toInt
      -- Setup the sortedness application.
      have hj1_k : k / 2 < sorted.val.size := by
        have := hj1; rw [h_idx_k_eq] at this; exact this
      have hj2_k : k / 2 + 1 < sorted.val.size := by
        have := hj2; rw [h_idx_k2_eq] at this; exact this
      have h_sorted_step :
          (sorted.val[k / 2]'hj1_k).toInt ≤ (sorted.val[k / 2 + 1]'hj2_k).toInt :=
        h_sorted_sorted (k / 2) (k / 2 + 1) hj1_k hj2_k (Nat.le_succ _)
      -- Conclude.
      rw [h_val_k, h_val_k2]
      have h_lhs : sorted.val[(0 : usize).toNat + ((k + 1) / 2 - ((0 : usize).toNat + 1) / 2)]'hj1 =
                    sorted.val[k / 2]'hj1_k := by
        congr 1
      have h_rhs : sorted.val[(0 : usize).toNat + ((k + 2 + 1) / 2 - ((0 : usize).toNat + 1) / 2)]'hj2 =
                    sorted.val[k / 2 + 1]'hj2_k := by
        congr 1
      rw [h_lhs, h_rhs]
      exact h_sorted_step

/-- Even-index multiset preservation: for every target value, the
    number of occurrences at even output positions equals the number at
    even input positions. Captures the Rust proptest
    `even_indices_multiset_preserved`. Independent from
    `sort_even_even_indices_sorted`: catches implementations that
    produce a sorted-but-wrong sequence (e.g. all zeros) at even
    positions. -/
theorem sort_even_even_indices_multiset_preserved
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_036_sort_even.sort_even l = RustM.ok v)
    (target : i64) :
    count_evens v.val target v.val.size = count_evens l.val target l.val.size := by
  unfold clever_036_sort_even.sort_even at hres
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  generalize h_collect :
      clever_036_sort_even.collect_evens l (0 : usize) ⟨(List.nil).toArray, by grind⟩ = ce_res at hres
  cases ce_res with
  | none =>
    exfalso
    have hh : (do let sorted ← (none : RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                  let sorted_deref ← (core_models.ops.deref.Deref.deref
                    (alloc.vec.Vec i64 alloc.alloc.Global) sorted :
                    RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                  let acc0 ← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                              RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                  clever_036_sort_even.rebuild_at l sorted_deref (0 : usize) (0 : usize) acc0)
              = RustM.ok v := hres
    cases hh
  | some ce_res' =>
    cases ce_res' with
    | error e =>
      exfalso
      have hh : (do let sorted ← (some (Except.error e) :
                                    RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                    let sorted_deref ← (core_models.ops.deref.Deref.deref
                      (alloc.vec.Vec i64 alloc.alloc.Global) sorted :
                      RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                    let acc0 ← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                                RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                    clever_036_sort_even.rebuild_at l sorted_deref (0 : usize) (0 : usize) acc0)
                = RustM.ok v := hres
      cases hh
    | ok sorted =>
      have h_collect_ok :
          clever_036_sort_even.collect_evens l (0 : usize) ⟨(List.nil).toArray, by grind⟩
            = RustM.ok sorted := h_collect
      simp only [RustM_ok_bind] at hres
      have h_deref :
          (core_models.ops.deref.Deref.deref
            (alloc.vec.Vec i64 alloc.alloc.Global) sorted : RustM _) = RustM.ok sorted := rfl
      rw [h_deref] at hres
      simp only [RustM_ok_bind] at hres
      -- hres : rebuild_at l sorted 0 0 #[] = ok v
      have h_zero_toNat : (0 : usize).toNat = 0 := rfl
      have h_meas : l.val.size - (0 : usize).toNat ≤ l.val.size := by rw [h_zero_toNat]; omega
      have h_le : (0 : usize).toNat ≤ l.val.size := by rw [h_zero_toNat]; omega
      -- Apply collect_evens_inv
      have ce_inv := collect_evens_inv l.val.size l (0 : usize) ⟨(List.nil).toArray, by grind⟩
        sorted target h_meas h_le h_collect_ok
      obtain ⟨h_sorted_size, h_sorted_count⟩ := ce_inv
      have h_empty_size : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
      rw [h_empty_size, h_zero_toNat] at h_sorted_size
      rw [h_empty_size, h_zero_toNat] at h_sorted_count
      have h_empty_total : total_count ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val target 0 = 0 := rfl
      rw [h_empty_total] at h_sorted_count
      have h_zero_count : count_evens l.val target 0 = 0 := rfl
      rw [h_zero_count] at h_sorted_count
      -- Apply rebuild_at_count: count_evens v target v.size + total_count sorted target 0 = 
      --   count_evens #[] target 0 + total_count sorted target ((l.size+1)/2)
      have h_j_le : (0 : usize).toNat ≤ sorted.val.size := by rw [h_zero_toNat]; omega
      have h_acc_eq_zero : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = (0 : usize).toNat := by
        rw [h_empty_size, h_zero_toNat]
      have rb_count := rebuild_at_count l.val.size l sorted (0 : usize) (0 : usize)
        ⟨(List.nil).toArray, by grind⟩ v target h_meas h_le h_acc_eq_zero h_j_le hres
      simp only at rb_count
      obtain ⟨h_bound, h_count_eq⟩ := rb_count
      have h_empty_total2 : total_count ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val target ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
      have h_empty_count : count_evens ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val target ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
      rw [h_empty_count] at h_count_eq
      have h_zero_total : total_count sorted.val target ((0 : usize).toNat) = 0 := by
        rw [h_zero_toNat]; rfl
      rw [h_zero_total] at h_count_eq
      have h_zero_add_E : (0 : usize).toNat + ((l.val.size + 1) / 2 - (USize64.toNat (0 : usize) + 1) / 2) =
                            (l.val.size + 1) / 2 := by
        rw [h_zero_toNat]; simp
      rw [h_zero_add_E] at h_count_eq
      -- h_count_eq : count_evens v target v.size + 0 = 0 + total_count sorted target ((l.size+1)/2)
      -- which gives count_evens v target v.size = total_count sorted target ((l.size+1)/2)
      have h_step1 : count_evens v.val target v.val.size = total_count sorted.val target ((l.val.size + 1) / 2) := by
        omega
      -- h_sorted_count : total_count sorted target sorted.size = count_evens l target l.size
      -- h_sorted_size : sorted.size = (l.size + 1) / 2
      rw [h_step1]
      -- Need: total_count sorted target ((l.size+1)/2) = count_evens l target l.size
      -- We have: total_count sorted target sorted.size = count_evens l target l.size and sorted.size = (l.size+1)/2
      have h_sorted_size_eq : sorted.val.size = (l.val.size + 1) / 2 := by
        rw [h_sorted_size]; simp
      rw [← h_sorted_size_eq]
      omega

end Clever_036_sort_evenObligations
