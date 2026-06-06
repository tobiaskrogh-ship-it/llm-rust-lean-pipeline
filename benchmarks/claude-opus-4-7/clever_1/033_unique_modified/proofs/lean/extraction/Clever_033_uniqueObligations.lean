-- Companion obligations file for the `clever_033_unique` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_033_unique

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_033_uniqueObligations

/-! ## Standard scaffolding (transferred from `clever_009_rolling_max`,
     `clever_021_rescale_to_unit`, `clever_025_remove_duplicates`). -/

/-- `RustM.ok x >>= f = f x`. The library's `pure_bind` simp lemma only
    matches literal `Pure.pure`; this rewrite handles the `RustM.ok` form
    produced after reducing definitions. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

private theorem usize_zero_toNat : (0 : usize).toNat = 0 := rfl

private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide

private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide

private theorem two_lt_usize_size : (2 : Nat) < USize64.size := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

/-! ## Anchor: empty input yields empty output. -/

/-- Anchor unit test: `unique(&[]) = []`. The function succeeds on the
    empty slice and returns a `Vec` of size `0`. Captures the Rust unit
    test `empty_input_yields_empty_output`. -/
theorem empty_input_yields_empty_output
    (l : RustSlice i64) (hempty : l.val.size = 0) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_033_unique.unique l = RustM.ok v ∧ v.val.size = 0 := by
  refine ⟨⟨#[], by decide⟩, ?_, rfl⟩
  unfold clever_033_unique.unique
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new]
  simp only [RustM_ok_bind]
  have h_sort_oob :
      clever_033_unique.sort_at l (0 : usize)
        ⟨(List.nil).toArray, by grind⟩ =
      RustM.ok ⟨(List.nil).toArray, by grind⟩ := by
    unfold clever_033_unique.sort_at
    have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
      USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
    have h_cond : decide (USize64.ofNat l.val.size ≤ (0 : usize)) = true := by
      rw [decide_eq_true_iff]
      rw [USize64.le_iff_toNat_le, h_ofNat, usize_zero_toNat]
      exact Nat.le_of_eq hempty
    simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
               rust_primitives.cmp.ge, pure_bind,
               h_cond, ↓reduceIte]
    rfl
  rw [h_sort_oob]
  simp only [RustM_ok_bind]
  show (do
    let sorted_deref ← (core_models.ops.deref.Deref.deref
      (alloc.vec.Vec i64 alloc.alloc.Global)
      ⟨(List.nil).toArray, by grind⟩ : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
    let acc0 ← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global))
    clever_033_unique.dedupe_at sorted_deref (0 : usize) acc0) =
    RustM.ok ⟨#[], by decide⟩
  have h_deref :
      (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec i64 alloc.alloc.Global)
        ⟨(List.nil).toArray, by grind⟩ :
        RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
        RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_deref]
  simp only [RustM_ok_bind]
  rw [h_new]
  simp only [RustM_ok_bind]
  have h_sorted_size : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
  unfold clever_033_unique.dedupe_at
  have h_ofNat : (USize64.ofNat ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size).toNat
                  = ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size :=
    USize64.toNat_ofNat_of_lt' ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).size_lt_usizeSize
  have h_cond : decide
      (USize64.ofNat ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size ≤ (0 : usize)) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat, usize_zero_toNat]
    exact Nat.le_of_eq h_sorted_size
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-! ## Membership predicates on Array (cleaner than `Seq.has` because no
     size constraint to thread through). -/

private def arr_has (s : Array i64) (x : i64) : Prop :=
  ∃ (i : Nat) (hi : i < s.size), s[i]'hi = x

private theorem arr_has_empty (x : i64) : ¬ arr_has #[] x := by
  rintro ⟨i, hi, _⟩
  have : (#[] : Array i64).size = 0 := rfl
  omega

private theorem arr_has_append (a b : Array i64) (x : i64) :
    arr_has (a ++ b) x ↔ arr_has a x ∨ arr_has b x := by
  unfold arr_has
  constructor
  · rintro ⟨i, hi, hx⟩
    rw [Array.size_append] at hi
    by_cases h : i < a.size
    · left
      refine ⟨i, h, ?_⟩
      rw [Array.getElem_append_left h] at hx
      exact hx
    · right
      have hi' : i - a.size < b.size := by omega
      refine ⟨i - a.size, hi', ?_⟩
      have h_le : a.size ≤ i := Nat.le_of_not_lt h
      rw [Array.getElem_append_right h_le] at hx
      exact hx
  · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx⟩)
    · refine ⟨i, ?_, ?_⟩
      · rw [Array.size_append]; omega
      · rw [Array.getElem_append_left hi]; exact hx
    · refine ⟨i + a.size, ?_, ?_⟩
      · rw [Array.size_append]; omega
      · have h_ge : a.size ≤ i + a.size := by omega
        have h_sub : i + a.size - a.size = i := by omega
        have h_app : a.size ≤ i + a.size := h_ge
        have h_size_ab : i + a.size < (a ++ b).size := by
          rw [Array.size_append]; omega
        rw [show (a ++ b)[i + a.size]'h_size_ab = b[i + a.size - a.size]'(by omega)
              from Array.getElem_append_right h_app]
        simp only [h_sub]
        exact hx

private theorem arr_has_singleton (x y : i64) :
    arr_has #[y] x ↔ x = y := by
  unfold arr_has
  constructor
  · rintro ⟨i, hi, hx⟩
    have h_sz : (#[y] : Array i64).size = 1 := rfl
    have : i < 1 := by rw [← h_sz]; exact hi
    have hi0 : i = 0 := by omega
    subst hi0
    exact hx.symm
  · intro hxy
    have h0_lt : (0 : Nat) < (#[y] : Array i64).size := by
      have : (#[y] : Array i64).size = 1 := rfl
      omega
    refine ⟨0, h0_lt, ?_⟩
    show (#[y] : Array i64)[0]'h0_lt = x
    exact hxy.symm

private theorem arr_has_pair (x a b : i64) :
    arr_has #[a, b] x ↔ x = a ∨ x = b := by
  unfold arr_has
  constructor
  · rintro ⟨i, hi, hx⟩
    have h_sz : (#[a, b] : Array i64).size = 2 := rfl
    have hi2 : i < 2 := by rw [← h_sz]; exact hi
    by_cases h0 : i = 0
    · subst h0; left; exact hx.symm
    · have hi1 : i = 1 := by omega
      subst hi1; right; exact hx.symm
  · have h0_lt : (0 : Nat) < (#[a, b] : Array i64).size := by
      have : (#[a, b] : Array i64).size = 2 := rfl; omega
    have h1_lt : (1 : Nat) < (#[a, b] : Array i64).size := by
      have : (#[a, b] : Array i64).size = 2 := rfl; omega
    rintro (rfl | rfl)
    · exact ⟨0, h0_lt, rfl⟩
    · exact ⟨1, h1_lt, rfl⟩

/-! ## Step lemmas for the four `partial_fixpoint` helpers.

We need OOB and step lemmas for each helper. The OOB lemmas were used for
the empty-input case (already inlined above). The step lemmas reduce a
single recursive call to its body. -/

/-- `sort_at l i acc = RustM.ok acc` when `i ≥ len l`. -/
private theorem sort_at_oob (l : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : l.val.size ≤ i.toNat) :
    clever_033_unique.sort_at l i acc = RustM.ok acc := by
  unfold clever_033_unique.sort_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- `dedupe_at sorted i acc = RustM.ok acc` when `i ≥ len sorted`. -/
private theorem dedupe_at_oob (sorted : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : sorted.val.size ≤ i.toNat) :
    clever_033_unique.dedupe_at sorted i acc = RustM.ok acc := by
  unfold clever_033_unique.dedupe_at
  have h_ofNat : (USize64.ofNat sorted.val.size).toNat = sorted.val.size :=
    USize64.toNat_ofNat_of_lt' sorted.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat sorted.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-! ## Step lemma: `dedupe_at` in-bounds case.

We use a generalised "either we extended acc, or we did not" formulation
to sidestep the inner `if (i ==? 0)` conditional. This is enough for both
postconditions: the membership predicate is preserved either way. -/

/-- Helper: rewriting the `i +? (1 : usize)` shape on a non-overflowing index. -/
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

/-- Helper: `i -? (1 : usize) = ok (i - 1)` when `i ≥ 1` (i.e. `i.toNat > 0`). -/
private theorem usize_sub_one_ok (i : usize) (h : 0 < i.toNat) :
    (i -? (1 : usize) : RustM usize) = RustM.ok (i - 1) := by
  show (rust_primitives.ops.arith.Sub.sub i 1 : RustM usize) = RustM.ok (i - 1)
  show (if BitVec.usubOverflow i.toBitVec (1 : usize).toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure (i - 1)) = _
  have h_no_bv :
      BitVec.usubOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.usubOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have h_sub_ov : USize64.subOverflow i 1 = true := hbo
      have hii : i.toNat < (1 : usize).toNat := USize64.subOverflow_iff.mp h_sub_ov
      rw [usize_one_toNat] at hii
      omega
  rw [h_no_bv]; rfl

private theorem usize_sub_one_toNat (i : usize) (h : 0 < i.toNat) :
    (i - 1).toNat = i.toNat - 1 := by
  have h_pre : (1 : usize).toNat ≤ i.toNat := by rw [usize_one_toNat]; omega
  rw [USize64.toNat_sub_of_le' h_pre, usize_one_toNat]

/-! ### `dedupe_at` step lemmas.

`dedupe_at_step_first`: at `i = 0`, the inner `if (i ==? 0)` forces
`keep = true`, so we extend `acc` with `[sorted[0]]` and recurse.

`dedupe_at_step_neq`: at `i > 0` with `sorted[i] ≠ sorted[i-1]`, the inner
else branch evaluates to `true`, so we extend and recurse.

`dedupe_at_step_eq`: at `i > 0` with `sorted[i] = sorted[i-1]`, the inner
else branch evaluates to `false`, so we just recurse without extending. -/

private theorem dedupe_at_step_first (sorted : RustSlice i64)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (h0 : 0 < sorted.val.size)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_033_unique.dedupe_at sorted (0 : usize) acc =
      clever_033_unique.dedupe_at sorted (1 : usize)
        ⟨acc.val ++ #[sorted.val[0]'h0], by
          rw [Array.size_append]
          have h_one : (#[sorted.val[0]'h0] : Array i64).size = 1 := rfl
          omega⟩ := by
  conv => lhs; unfold clever_033_unique.dedupe_at
  have h_ofNat : (USize64.ofNat sorted.val.size).toNat = sorted.val.size :=
    USize64.toNat_ofNat_of_lt' sorted.size_lt_usizeSize
  have h_cond_outer : decide (USize64.ofNat sorted.val.size ≤ (0 : usize)) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat, usize_zero_toNat] at hle
    omega
  have h0' : (0 : usize).toNat < sorted.val.size := by rw [usize_zero_toNat]; exact h0
  have h_idx0 : (sorted[(0 : usize)]_? : RustM i64) = RustM.ok (sorted.val[0]'h0) := by
    show (if h : (0 : usize).toNat < sorted.val.size then pure (sorted.val[0])
            else .fail .arrayOutOfBounds)
        = RustM.ok (sorted.val[0]'h0)
    rw [dif_pos h0']; rfl
  have h_no_ov : (0 : usize).toNat + 1 < 2^64 := by
    rw [usize_zero_toNat]; decide
  have h_add : ((0 : usize) +? (1 : usize) : RustM usize) = RustM.ok ((0 : usize) + 1) :=
    usize_add_one_ok 0 h_no_ov
  have h_01 : ((0 : usize) + 1) = (1 : usize) := by decide
  have h_app_size :
      acc.val.size + (#[sorted.val[0]'h0] : Array i64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  have h_extend :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[sorted.val[0]'h0], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.ok ⟨acc.val ++ #[sorted.val[0]'h0], by
          have h_size_eq : (acc.val ++ #[sorted.val[0]'h0]).size
                            = acc.val.size + 1 := by
            rw [Array.size_append]; rfl
          rw [h_size_eq]; exact h_acc⟩ := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             rust_primitives.cmp.eq, BEq.beq, decide_true,
             h_idx0]
  -- After the outer reduction, the inner `if (0 ==? 0)` should be evaluable.
  -- We rewrite the unsize chunk, extend_from_slice, and final +? 1.
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[sorted.val[0]'h0] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[sorted.val[0]'h0], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend]
  simp only [RustM_ok_bind]
  rw [h_add]
  simp only [RustM_ok_bind, h_01]

/-- `dedupe_at_step_neq`: i > 0, sorted[i] ≠ sorted[i-1] → extend and recurse. -/
private theorem dedupe_at_step_neq (sorted : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < sorted.val.size)
    (hi_pos : 0 < i.toNat)
    (h_neq : sorted.val[i.toNat]'hi ≠ sorted.val[i.toNat - 1]'(by omega))
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_033_unique.dedupe_at sorted i acc =
      clever_033_unique.dedupe_at sorted (i + 1)
        ⟨acc.val ++ #[sorted.val[i.toNat]'hi], by
          rw [Array.size_append]
          have h_one : (#[sorted.val[i.toNat]'hi] : Array i64).size = 1 := rfl
          omega⟩ := by
  conv => lhs; unfold clever_033_unique.dedupe_at
  have h_size_lt : sorted.val.size < USize64.size := sorted.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat sorted.val.size).toNat = sorted.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat sorted.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (sorted[i]_? : RustM i64) = RustM.ok (sorted.val[i.toNat]'hi) := by
    show (if h : i.toNat < sorted.val.size then pure (sorted.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (sorted.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_sub : (i -? (1 : usize) : RustM usize) = RustM.ok (i - 1) := usize_sub_one_ok i hi_pos
  have h_sub_toNat : (i - 1).toNat = i.toNat - 1 := usize_sub_one_toNat i hi_pos
  have hi_sub_lt : (i - 1).toNat < sorted.val.size := by rw [h_sub_toNat]; omega
  have h_idx_sub : (sorted[(i - 1)]_? : RustM i64)
                    = RustM.ok (sorted.val[(i - 1).toNat]'hi_sub_lt) := by
    show (if h : (i - 1).toNat < sorted.val.size then pure (sorted.val[i - 1])
            else .fail .arrayOutOfBounds)
        = RustM.ok (sorted.val[(i - 1).toNat]'hi_sub_lt)
    rw [dif_pos hi_sub_lt]; rfl
  -- The equality `i.toNat = 0` is false because i.toNat > 0.
  have h_eq0_false : ((i ==? (0 : usize)) : RustM Bool) = RustM.ok false := by
    show rust_primitives.cmp.eq i (0 : usize) = RustM.ok false
    show pure (i == (0 : usize)) = RustM.ok false
    have h_ne : i ≠ 0 := by
      intro h_eq
      have : i.toNat = (0 : usize).toNat := by rw [h_eq]
      rw [usize_zero_toNat] at this
      omega
    rw [show (i == (0 : usize)) = false from by
          rw [beq_eq_false_iff_ne]; exact h_ne]
    rfl
  -- `sorted[i] !=? sorted[i-1] = pure (sorted[i] != sorted[i-1]) = pure true`.
  have h_ne_eq : (rust_primitives.cmp.ne (sorted.val[i.toNat]'hi)
                    (sorted.val[(i - 1).toNat]'hi_sub_lt) : RustM Bool)
                  = RustM.ok true := by
    show pure ((sorted.val[i.toNat]'hi) != (sorted.val[(i - 1).toNat]'hi_sub_lt)) = RustM.ok true
    rw [show ((sorted.val[i.toNat]'hi) != (sorted.val[(i - 1).toNat]'hi_sub_lt)) = true from by
          rw [bne_iff_ne]
          have h_idx_eq : sorted.val[(i - 1).toNat]'hi_sub_lt = sorted.val[i.toNat - 1]'(by omega) := by
            congr 1
          rw [h_idx_eq]
          exact h_neq]
    rfl
  have h_add : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := usize_add_one_ok i h_no_ov_i
  have h_app_size :
      acc.val.size + (#[sorted.val[i.toNat]'hi] : Array i64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  have h_extend :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[sorted.val[i.toNat]'hi], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.ok ⟨acc.val ++ #[sorted.val[i.toNat]'hi], by
          have h_size_eq : (acc.val ++ #[sorted.val[i.toNat]'hi]).size
                            = acc.val.size + 1 := by
            rw [Array.size_append]; rfl
          rw [h_size_eq]; exact h_acc⟩ := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_eq0_false, h_idx, h_sub, h_idx_sub, h_ne_eq]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[sorted.val[i.toNat]'hi] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[sorted.val[i.toNat]'hi], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend]
  simp only [RustM_ok_bind]
  rw [h_add]
  simp only [RustM_ok_bind]

/-- `dedupe_at_step_eq`: i > 0, sorted[i] = sorted[i-1] → just recurse. -/
private theorem dedupe_at_step_eq (sorted : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < sorted.val.size)
    (hi_pos : 0 < i.toNat)
    (h_eq : sorted.val[i.toNat]'hi = sorted.val[i.toNat - 1]'(by omega)) :
    clever_033_unique.dedupe_at sorted i acc =
      clever_033_unique.dedupe_at sorted (i + 1) acc := by
  conv => lhs; unfold clever_033_unique.dedupe_at
  have h_size_lt : sorted.val.size < USize64.size := sorted.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat sorted.val.size).toNat = sorted.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat sorted.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (sorted[i]_? : RustM i64) = RustM.ok (sorted.val[i.toNat]'hi) := by
    show (if h : i.toNat < sorted.val.size then pure (sorted.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (sorted.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_sub : (i -? (1 : usize) : RustM usize) = RustM.ok (i - 1) := usize_sub_one_ok i hi_pos
  have h_sub_toNat : (i - 1).toNat = i.toNat - 1 := usize_sub_one_toNat i hi_pos
  have hi_sub_lt : (i - 1).toNat < sorted.val.size := by rw [h_sub_toNat]; omega
  have h_idx_sub : (sorted[(i - 1)]_? : RustM i64)
                    = RustM.ok (sorted.val[(i - 1).toNat]'hi_sub_lt) := by
    show (if h : (i - 1).toNat < sorted.val.size then pure (sorted.val[i - 1])
            else .fail .arrayOutOfBounds)
        = RustM.ok (sorted.val[(i - 1).toNat]'hi_sub_lt)
    rw [dif_pos hi_sub_lt]; rfl
  have h_eq0_false : ((i ==? (0 : usize)) : RustM Bool) = RustM.ok false := by
    show rust_primitives.cmp.eq i (0 : usize) = RustM.ok false
    show pure (i == (0 : usize)) = RustM.ok false
    have h_ne : i ≠ 0 := by
      intro h_eq2
      have : i.toNat = (0 : usize).toNat := by rw [h_eq2]
      rw [usize_zero_toNat] at this
      omega
    rw [show (i == (0 : usize)) = false from by
          rw [beq_eq_false_iff_ne]; exact h_ne]
    rfl
  have h_ne_eq : (rust_primitives.cmp.ne (sorted.val[i.toNat]'hi)
                    (sorted.val[(i - 1).toNat]'hi_sub_lt) : RustM Bool)
                  = RustM.ok false := by
    show pure ((sorted.val[i.toNat]'hi) != (sorted.val[(i - 1).toNat]'hi_sub_lt)) = RustM.ok false
    rw [show ((sorted.val[i.toNat]'hi) != (sorted.val[(i - 1).toNat]'hi_sub_lt)) = false from by
          rw [bne_eq_false_iff_eq]
          have h_idx_eq : sorted.val[(i - 1).toNat]'hi_sub_lt = sorted.val[i.toNat - 1]'(by omega) := by
            congr 1
          rw [h_idx_eq]
          exact h_eq]
    rfl
  have h_add : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := usize_add_one_ok i h_no_ov_i
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_eq0_false, h_idx, h_sub, h_idx_sub, h_ne_eq]
  rw [h_add]
  simp only [RustM_ok_bind]

/-- Fail variant of `dedupe_at_step_first`: when `acc` is too large, the
    extend fails. Used to derive `h_acc_size_lt` from `hres = ok r` in the
    induction proof. -/
private theorem dedupe_at_step_first_fail (sorted : RustSlice i64)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (h0 : 0 < sorted.val.size)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_033_unique.dedupe_at sorted (0 : usize) acc
      = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_033_unique.dedupe_at
  have h_ofNat : (USize64.ofNat sorted.val.size).toNat = sorted.val.size :=
    USize64.toNat_ofNat_of_lt' sorted.size_lt_usizeSize
  have h_cond_outer : decide (USize64.ofNat sorted.val.size ≤ (0 : usize)) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat, usize_zero_toNat] at hle
    omega
  have h0' : (0 : usize).toNat < sorted.val.size := by rw [usize_zero_toNat]; exact h0
  have h_idx0 : (sorted[(0 : usize)]_? : RustM i64) = RustM.ok (sorted.val[0]'h0) := by
    show (if h : (0 : usize).toNat < sorted.val.size then pure (sorted.val[0])
            else .fail .arrayOutOfBounds)
        = RustM.ok (sorted.val[0]'h0)
    rw [dif_pos h0']; rfl
  have h_app_size_neg :
      ¬ acc.val.size + (#[sorted.val[0]'h0] : Array i64).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[sorted.val[0]'h0], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             rust_primitives.cmp.eq, BEq.beq, decide_true,
             h_idx0]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[sorted.val[0]'h0] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[sorted.val[0]'h0], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

/-- Fail variant of `dedupe_at_step_neq`: when `acc` is too large, the extend fails. -/
private theorem dedupe_at_step_neq_fail (sorted : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < sorted.val.size)
    (hi_pos : 0 < i.toNat)
    (h_neq : sorted.val[i.toNat]'hi ≠ sorted.val[i.toNat - 1]'(by omega))
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_033_unique.dedupe_at sorted i acc
      = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_033_unique.dedupe_at
  have h_size_lt : sorted.val.size < USize64.size := sorted.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat sorted.val.size).toNat = sorted.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat sorted.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (sorted[i]_? : RustM i64) = RustM.ok (sorted.val[i.toNat]'hi) := by
    show (if h : i.toNat < sorted.val.size then pure (sorted.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (sorted.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_sub : (i -? (1 : usize) : RustM usize) = RustM.ok (i - 1) := usize_sub_one_ok i hi_pos
  have h_sub_toNat : (i - 1).toNat = i.toNat - 1 := usize_sub_one_toNat i hi_pos
  have hi_sub_lt : (i - 1).toNat < sorted.val.size := by rw [h_sub_toNat]; omega
  have h_idx_sub : (sorted[(i - 1)]_? : RustM i64)
                    = RustM.ok (sorted.val[(i - 1).toNat]'hi_sub_lt) := by
    show (if h : (i - 1).toNat < sorted.val.size then pure (sorted.val[i - 1])
            else .fail .arrayOutOfBounds)
        = RustM.ok (sorted.val[(i - 1).toNat]'hi_sub_lt)
    rw [dif_pos hi_sub_lt]; rfl
  have h_eq0_false : ((i ==? (0 : usize)) : RustM Bool) = RustM.ok false := by
    show rust_primitives.cmp.eq i (0 : usize) = RustM.ok false
    show pure (i == (0 : usize)) = RustM.ok false
    have h_ne : i ≠ 0 := by
      intro h_eq
      have : i.toNat = (0 : usize).toNat := by rw [h_eq]
      rw [usize_zero_toNat] at this; omega
    rw [show (i == (0 : usize)) = false from by
          rw [beq_eq_false_iff_ne]; exact h_ne]
    rfl
  have h_ne_eq : (rust_primitives.cmp.ne (sorted.val[i.toNat]'hi)
                    (sorted.val[(i - 1).toNat]'hi_sub_lt) : RustM Bool)
                  = RustM.ok true := by
    show pure ((sorted.val[i.toNat]'hi) != (sorted.val[(i - 1).toNat]'hi_sub_lt)) = RustM.ok true
    rw [show ((sorted.val[i.toNat]'hi) != (sorted.val[(i - 1).toNat]'hi_sub_lt)) = true from by
          rw [bne_iff_ne]
          have h_idx_eq : sorted.val[(i - 1).toNat]'hi_sub_lt = sorted.val[i.toNat - 1]'(by omega) := by
            congr 1
          rw [h_idx_eq]
          exact h_neq]
    rfl
  have h_app_size_neg :
      ¬ acc.val.size + (#[sorted.val[i.toNat]'hi] : Array i64).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
        ⟨#[sorted.val[i.toNat]'hi], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_eq0_false, h_idx, h_sub, h_idx_sub, h_ne_eq]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[sorted.val[i.toNat]'hi] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[sorted.val[i.toNat]'hi], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

/-- Strong induction for `dedupe_at`: every output element comes from `acc ∪ sorted`. -/
private theorem dedupe_at_subset (sorted : RustSlice i64) :
    ∀ (n : Nat) (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      sorted.val.size - i.toNat ≤ n →
      i.toNat ≤ sorted.val.size →
      clever_033_unique.dedupe_at sorted i acc = RustM.ok r →
      ∀ y, arr_has r.val y → arr_has acc.val y ∨ arr_has sorted.val y := by
  intro n
  induction n with
  | zero =>
    intro i acc r hm hi_le hres y hy
    have hi_ge : sorted.val.size ≤ i.toNat := by omega
    rw [dedupe_at_oob sorted i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    left; exact hy
  | succ n ih =>
    intro i acc r hm hi_le hres y hy
    by_cases hi_ge : sorted.val.size ≤ i.toNat
    · rw [dedupe_at_oob sorted i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      left; exact hy
    · have hi_lt : i.toNat < sorted.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : sorted.val.size < USize64.size := sorted.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ sorted.val.size := by rw [h_i1]; omega
      have h_meas : sorted.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      by_cases h0 : i.toNat = 0
      · -- Keep branch (i = 0).
        have h0_usize : i = (0 : usize) := by
          have : i.toNat = (0 : usize).toNat := by rw [h0, usize_zero_toNat]
          exact USize64.toNat_inj.mp this
        subst h0_usize
        have h_sz : 0 < sorted.val.size := by rw [usize_zero_toNat] at hi_lt; exact hi_lt
        -- Derive h_acc_size_lt or contradict.
        by_cases h_acc_size_lt : acc.val.size + 1 < USize64.size
        · rw [dedupe_at_step_first sorted acc h_sz h_acc_size_lt] at hres
          have h_one_toNat : (1 : usize).toNat = 1 := usize_one_toNat
          have h_meas' : sorted.val.size - (1 : usize).toNat ≤ n := by
            rw [h_one_toNat]; omega
          have h_le' : (1 : usize).toNat ≤ sorted.val.size := by rw [h_one_toNat]; omega
          have ih_app := ih (1 : usize) _ r h_meas' h_le' hres y hy
          rcases ih_app with h_acc' | h_sorted
          · rw [show ((⟨acc.val ++ #[sorted.val[0]'h_sz], by
                          rw [Array.size_append]
                          have h_one : (#[sorted.val[0]'h_sz] : Array i64).size = 1 := rfl
                          omega⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val
                    = acc.val ++ #[sorted.val[0]'h_sz] from rfl] at h_acc'
            rw [arr_has_append] at h_acc'
            rcases h_acc' with h_in_acc | h_in_sing
            · left; exact h_in_acc
            · right
              rw [arr_has_singleton] at h_in_sing
              subst h_in_sing
              exact ⟨0, h_sz, rfl⟩
          · right; exact h_sorted
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [dedupe_at_step_first_fail sorted acc h_sz h_big] at hres
          cases hres
      · -- i > 0.
        have hi_pos : 0 < i.toNat := Nat.pos_of_ne_zero h0
        by_cases h_data_eq : sorted.val[i.toNat]'hi_lt = sorted.val[i.toNat - 1]'(by omega)
        · -- Skip branch.
          rw [dedupe_at_step_eq sorted i acc hi_lt hi_pos h_data_eq] at hres
          exact ih (i + 1) acc r h_meas h_i1_le hres y hy
        · -- Keep branch (i > 0, sorted[i] ≠ sorted[i-1]).
          by_cases h_acc_size_lt : acc.val.size + 1 < USize64.size
          · rw [dedupe_at_step_neq sorted i acc hi_lt hi_pos h_data_eq h_acc_size_lt] at hres
            have ih_app := ih (i + 1) _ r h_meas h_i1_le hres y hy
            rcases ih_app with h_acc' | h_sorted
            · rw [show ((⟨acc.val ++ #[sorted.val[i.toNat]'hi_lt], by
                            rw [Array.size_append]
                            have h_one : (#[sorted.val[i.toNat]'hi_lt] : Array i64).size = 1 := rfl
                            omega⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val
                      = acc.val ++ #[sorted.val[i.toNat]'hi_lt] from rfl] at h_acc'
              rw [arr_has_append] at h_acc'
              rcases h_acc' with h_in_acc | h_in_sing
              · left; exact h_in_acc
              · right
                rw [arr_has_singleton] at h_in_sing
                subst h_in_sing
                exact ⟨i.toNat, hi_lt, rfl⟩
            · right; exact h_sorted
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 1 := by omega
            rw [dedupe_at_step_neq_fail sorted i acc hi_lt hi_pos h_data_eq h_big] at hres
            cases hres

/-! ### `insert_sorted_at` step lemmas.

Four branches:
* OOB + inserted: returns acc unchanged.
* OOB + not inserted: extends acc with `[x]` and returns.
* In-bounds + `¬inserted ∧ vi ≥ x`: extends acc with `[x, vi]`, recurses
  with `inserted = true`.
* In-bounds + `inserted ∨ vi < x`: extends acc with `[vi]`, recurses with
  the same `inserted` flag. -/

private theorem insert_sorted_at_step_oob_inserted (v : RustSlice i64) (x : i64)
    (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat) :
    clever_033_unique.insert_sorted_at v x i true acc = RustM.ok acc := by
  unfold clever_033_unique.insert_sorted_at
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

private theorem insert_sorted_at_step_oob_not_inserted (v : RustSlice i64) (x : i64)
    (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_033_unique.insert_sorted_at v x i false acc =
      RustM.ok ⟨acc.val ++ #[x], by
        rw [Array.size_append]
        have h_one : (#[x] : Array i64).size = 1 := rfl; omega⟩ := by
  unfold clever_033_unique.insert_sorted_at
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
      = RustM.ok ⟨acc.val ++ #[x], by
          have h_size_eq : (acc.val ++ #[x]).size = acc.val.size + 1 := by
            rw [Array.size_append]; rfl
          rw [h_size_eq]; exact h_acc⟩ := by
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

private theorem insert_sorted_at_step_oob_not_inserted_fail (v : RustSlice i64) (x : i64)
    (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_033_unique.insert_sorted_at v x i false acc
      = RustM.fail .maximumSizeExceeded := by
  unfold clever_033_unique.insert_sorted_at
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

private theorem insert_sorted_at_step_insert (v : RustSlice i64) (x : i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_vi : (v.val[i.toNat]'hi).toInt ≥ x.toInt)
    (h_acc : acc.val.size + 2 < USize64.size) :
    clever_033_unique.insert_sorted_at v x i false acc =
      clever_033_unique.insert_sorted_at v x (i + 1) true
        ⟨acc.val ++ #[x, v.val[i.toNat]'hi], by
          rw [Array.size_append]
          have h_two : (#[x, v.val[i.toNat]'hi] : Array i64).size = 2 := rfl
          omega⟩ := by
  conv => lhs; unfold clever_033_unique.insert_sorted_at
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
      = RustM.ok ⟨acc.val ++ #[x, v.val[i.toNat]'hi], by
          have h_size_eq : (acc.val ++ #[x, v.val[i.toNat]'hi]).size = acc.val.size + 2 := by
            rw [Array.size_append]; rfl
          rw [h_size_eq]; exact h_acc⟩ := by
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

private theorem insert_sorted_at_step_insert_fail (v : RustSlice i64) (x : i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_vi : (v.val[i.toNat]'hi).toInt ≥ x.toInt)
    (h_big : USize64.size ≤ acc.val.size + 2) :
    clever_033_unique.insert_sorted_at v x i false acc = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_033_unique.insert_sorted_at
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

/-- `insert_sorted_at` pass step: covers (a) `inserted = true`, and
    (b) `inserted = false` with `vi < x`. In both cases the extend chunk is
    just `[vi]` and `inserted` is unchanged. -/
private theorem insert_sorted_at_step_pass (v : RustSlice i64) (x : i64) (i : usize)
    (inserted : Bool) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_skip : inserted = true ∨ (v.val[i.toNat]'hi).toInt < x.toInt)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_033_unique.insert_sorted_at v x i inserted acc =
      clever_033_unique.insert_sorted_at v x (i + 1) inserted
        ⟨acc.val ++ #[v.val[i.toNat]'hi], by
          rw [Array.size_append]
          have h_one : (#[v.val[i.toNat]'hi] : Array i64).size = 1 := rfl
          omega⟩ := by
  conv => lhs; unfold clever_033_unique.insert_sorted_at
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
      = RustM.ok ⟨acc.val ++ #[v.val[i.toNat]'hi], by
          have h_size_eq : (acc.val ++ #[v.val[i.toNat]'hi]).size = acc.val.size + 1 := by
            rw [Array.size_append]; rfl
          rw [h_size_eq]; exact h_acc⟩ := by
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

private theorem insert_sorted_at_step_pass_fail (v : RustSlice i64) (x : i64) (i : usize)
    (inserted : Bool) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_skip : inserted = true ∨ (v.val[i.toNat]'hi).toInt < x.toInt)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_033_unique.insert_sorted_at v x i inserted acc = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_033_unique.insert_sorted_at
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
    | inl h_ins_true =>
      subst h_ins_true; rfl
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

/-! ### Strong induction for `insert_sorted_at`.

Every element of the output is in `acc.val ∪ {x} ∪ v.val`. -/

private theorem insert_sorted_at_subset (v : RustSlice i64) (x : i64) :
    ∀ (n : Nat) (i : usize) (inserted : Bool)
      (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      v.val.size - i.toNat ≤ n →
      i.toNat ≤ v.val.size →
      clever_033_unique.insert_sorted_at v x i inserted acc = RustM.ok r →
      ∀ y, arr_has r.val y → arr_has acc.val y ∨ y = x ∨ arr_has v.val y := by
  intro n
  induction n with
  | zero =>
    intro i inserted acc r hm hi_le hres y hy
    have hi_ge : v.val.size ≤ i.toNat := by omega
    cases inserted with
    | true =>
      rw [insert_sorted_at_step_oob_inserted v x i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      left; exact hy
    | false =>
      by_cases h_acc : acc.val.size + 1 < USize64.size
      · rw [insert_sorted_at_step_oob_not_inserted v x i acc hi_ge h_acc] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        rw [arr_has_append] at hy
        rcases hy with h_in_acc | h_in_x
        · left; exact h_in_acc
        · right; left
          rw [arr_has_singleton] at h_in_x
          exact h_in_x
      · exfalso
        have h_big : USize64.size ≤ acc.val.size + 1 := by omega
        rw [insert_sorted_at_step_oob_not_inserted_fail v x i acc hi_ge h_big] at hres
        cases hres
  | succ n ih =>
    intro i inserted acc r hm hi_le hres y hy
    by_cases hi_ge : v.val.size ≤ i.toNat
    · cases inserted with
      | true =>
        rw [insert_sorted_at_step_oob_inserted v x i acc hi_ge] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        left; exact hy
      | false =>
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [insert_sorted_at_step_oob_not_inserted v x i acc hi_ge h_acc] at hres
          injection hres with h_eq
          injection h_eq with h_eq'
          subst h_eq'
          rw [arr_has_append] at hy
          rcases hy with h_in_acc | h_in_x
          · left; exact h_in_acc
          · right; left
            rw [arr_has_singleton] at h_in_x
            exact h_in_x
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_sorted_at_step_oob_not_inserted_fail v x i acc hi_ge h_big] at hres
          cases hres
    · have hi_lt : i.toNat < v.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ v.val.size := by rw [h_i1]; omega
      have h_meas : v.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      -- Three cases:
      --   A) inserted = false ∧ vi ≥ x (insert branch, size-2 chunk)
      --   B) inserted = false ∧ vi < x (pass branch with inserted=false)
      --   C) inserted = true (pass branch with inserted=true)
      cases inserted with
      | true =>
        -- C: pass branch
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [insert_sorted_at_step_pass v x i true acc hi_lt (Or.inl rfl) h_acc] at hres
          have ih_app := ih (i + 1) true _ r h_meas h_i1_le hres y hy
          rcases ih_app with h_acc' | h_eq_x | h_in_v
          · rw [show ((⟨acc.val ++ #[v.val[i.toNat]'hi_lt], by
                          rw [Array.size_append]
                          have h_one : (#[v.val[i.toNat]'hi_lt] : Array i64).size = 1 := rfl
                          omega⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val
                    = acc.val ++ #[v.val[i.toNat]'hi_lt] from rfl] at h_acc'
            rw [arr_has_append] at h_acc'
            rcases h_acc' with h_in_acc | h_in_sing
            · left; exact h_in_acc
            · right; right
              rw [arr_has_singleton] at h_in_sing
              subst h_in_sing
              exact ⟨i.toNat, hi_lt, rfl⟩
          · right; left; exact h_eq_x
          · right; right; exact h_in_v
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_sorted_at_step_pass_fail v x i true acc hi_lt (Or.inl rfl) h_big] at hres
          cases hres
      | false =>
        by_cases h_vi_ge : (v.val[i.toNat]'hi_lt).toInt ≥ x.toInt
        · -- A: insert branch, size-2 chunk
          by_cases h_acc : acc.val.size + 2 < USize64.size
          · rw [insert_sorted_at_step_insert v x i acc hi_lt h_vi_ge h_acc] at hres
            have ih_app := ih (i + 1) true _ r h_meas h_i1_le hres y hy
            rcases ih_app with h_acc' | h_eq_x | h_in_v
            · rw [show ((⟨acc.val ++ #[x, v.val[i.toNat]'hi_lt], by
                            rw [Array.size_append]
                            have h_two : (#[x, v.val[i.toNat]'hi_lt] : Array i64).size = 2 := rfl
                            omega⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val
                      = acc.val ++ #[x, v.val[i.toNat]'hi_lt] from rfl] at h_acc'
              rw [arr_has_append] at h_acc'
              rcases h_acc' with h_in_acc | h_in_pair
              · left; exact h_in_acc
              · rw [arr_has_pair] at h_in_pair
                rcases h_in_pair with h_eq_x' | h_eq_vi
                · right; left; exact h_eq_x'
                · right; right
                  subst h_eq_vi
                  exact ⟨i.toNat, hi_lt, rfl⟩
            · right; left; exact h_eq_x
            · right; right; exact h_in_v
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 2 := by omega
            rw [insert_sorted_at_step_insert_fail v x i acc hi_lt h_vi_ge h_big] at hres
            cases hres
        · -- B: pass branch with vi < x
          have h_lt : (v.val[i.toNat]'hi_lt).toInt < x.toInt := by omega
          by_cases h_acc : acc.val.size + 1 < USize64.size
          · rw [insert_sorted_at_step_pass v x i false acc hi_lt (Or.inr h_lt) h_acc] at hres
            have ih_app := ih (i + 1) false _ r h_meas h_i1_le hres y hy
            rcases ih_app with h_acc' | h_eq_x | h_in_v
            · rw [show ((⟨acc.val ++ #[v.val[i.toNat]'hi_lt], by
                            rw [Array.size_append]
                            have h_one : (#[v.val[i.toNat]'hi_lt] : Array i64).size = 1 := rfl
                            omega⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val
                      = acc.val ++ #[v.val[i.toNat]'hi_lt] from rfl] at h_acc'
              rw [arr_has_append] at h_acc'
              rcases h_acc' with h_in_acc | h_in_sing
              · left; exact h_in_acc
              · right; right
                rw [arr_has_singleton] at h_in_sing
                subst h_in_sing
                exact ⟨i.toNat, hi_lt, rfl⟩
            · right; left; exact h_eq_x
            · right; right; exact h_in_v
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 1 := by omega
            rw [insert_sorted_at_step_pass_fail v x i false acc hi_lt (Or.inr h_lt) h_big] at hres
            cases hres

/-- Corollary specialized to `insert_sorted v x` (initial state). -/
private theorem insert_sorted_subset
    (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (r : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_033_unique.insert_sorted v x = RustM.ok r) :
    ∀ y, arr_has r.val y → arr_has v.val y ∨ y = x := by
  intro y hy
  unfold clever_033_unique.insert_sorted at hres
  have h_deref :
      (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec i64 alloc.alloc.Global) v : RustM _)
      = RustM.ok v := rfl
  have h_new :
      (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk : RustM _)
      = RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_deref, h_new] at hres
  simp only [RustM_ok_bind] at hres
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_meas : v.val.size - (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  have h_le : (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  have ih_app := insert_sorted_at_subset v x v.val.size (0 : usize) false
                    ⟨(List.nil).toArray, by grind⟩ r h_meas h_le hres y hy
  rcases ih_app with h_acc | h_eq | h_in_v
  · exfalso
    obtain ⟨k, hk, _⟩ := h_acc
    have h_empty_size : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
    rw [h_empty_size] at hk
    omega
  · right; exact h_eq
  · left; exact h_in_v

/-! ### `sort_at` step lemmas. -/

private theorem sort_at_step (l : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < l.val.size) :
    clever_033_unique.sort_at l i acc =
      (do
        let acc' ← clever_033_unique.insert_sorted acc (l.val[i.toNat]'hi)
        clever_033_unique.sort_at l (i + 1) acc') := by
  conv => lhs; unfold clever_033_unique.sort_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_add : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := usize_add_one_ok i h_no_ov_i
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx]
  rw [h_add]
  simp only [RustM_ok_bind]

/-- Strong induction for `sort_at`: every output element is in `acc.val ∪ l.val`. -/
private theorem sort_at_subset (l : RustSlice i64) :
    ∀ (n : Nat) (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      clever_033_unique.sort_at l i acc = RustM.ok r →
      ∀ y, arr_has r.val y → arr_has acc.val y ∨ arr_has l.val y := by
  intro n
  induction n with
  | zero =>
    intro i acc r hm hi_le hres y hy
    have hi_ge : l.val.size ≤ i.toNat := by omega
    rw [sort_at_oob l i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    left; exact hy
  | succ n ih =>
    intro i acc r hm hi_le hres y hy
    by_cases hi_ge : l.val.size ≤ i.toNat
    · rw [sort_at_oob l i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      left; exact hy
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_meas : l.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      rw [sort_at_step l i acc hi_lt] at hres
      -- hres : (do let acc' ← insert_sorted acc l[i.toNat]; sort_at l (i+1) acc') = ok r
      -- Case on insert_sorted's result.
      generalize hins : clever_033_unique.insert_sorted acc (l.val[i.toNat]'hi_lt) = ins_result
      rw [hins] at hres
      cases ins_result with
      | none =>
        exfalso
        show False
        have hh : (do let acc' ← (none : RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                       clever_033_unique.sort_at l (i + 1) acc')
                  = RustM.ok r := hres
        cases hh
      | some res' =>
        cases res' with
        | error e =>
          exfalso
          show False
          have hh : (do let acc' ← (some (Except.error e) : RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                         clever_033_unique.sort_at l (i + 1) acc')
                    = RustM.ok r := hres
          cases hh
        | ok acc' =>
          show arr_has acc.val y ∨ arr_has l.val y
          have h_ins_ok : clever_033_unique.insert_sorted acc (l.val[i.toNat]'hi_lt) = RustM.ok acc' := hins
          simp only [RustM_ok_bind] at hres
          have ih_app := ih (i + 1) acc' r h_meas h_i1_le hres y hy
          rcases ih_app with h_in_acc' | h_in_l
          · -- y in acc'
            have h_acc'_mem := insert_sorted_subset acc (l.val[i.toNat]'hi_lt) acc' h_ins_ok y h_in_acc'
            rcases h_acc'_mem with h_in_acc | h_eq_li
            · left; exact h_in_acc
            · right; subst h_eq_li
              exact ⟨i.toNat, hi_lt, rfl⟩
          · right; exact h_in_l

/-! ### Coverage lemmas (input ⊆ output). -/

/-- Every element of `acc` plus every element of `v.val[i..]` plus `x`
    (when `inserted = false`) is in the output of `insert_sorted_at`. -/
private theorem insert_sorted_at_covers (v : RustSlice i64) (x : i64) :
    ∀ (n : Nat) (i : usize) (inserted : Bool)
      (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      v.val.size - i.toNat ≤ n →
      i.toNat ≤ v.val.size →
      clever_033_unique.insert_sorted_at v x i inserted acc = RustM.ok r →
      (∀ y, arr_has acc.val y → arr_has r.val y) ∧
      (∀ (j : Nat) (hj : j < v.val.size) (_ : i.toNat ≤ j),
          arr_has r.val (v.val[j]'hj)) ∧
      (inserted = false → arr_has r.val x) := by
  intro n
  induction n with
  | zero =>
    intro i inserted acc r hm hi_le hres
    have hi_ge : v.val.size ≤ i.toNat := by omega
    cases inserted with
    | true =>
      rw [insert_sorted_at_step_oob_inserted v x i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      refine ⟨fun y h => h, ?_, ?_⟩
      · intro j hj h_ge; exfalso; omega
      · intro h; cases h
    | false =>
      by_cases h_acc : acc.val.size + 1 < USize64.size
      · rw [insert_sorted_at_step_oob_not_inserted v x i acc hi_ge h_acc] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        refine ⟨?_, ?_, ?_⟩
        · intro y hy
          show arr_has (acc.val ++ #[x]) y
          rw [arr_has_append]; left; exact hy
        · intro j hj h_ge; exfalso; omega
        · intro _
          show arr_has (acc.val ++ #[x]) x
          rw [arr_has_append]; right; rw [arr_has_singleton]
      · exfalso
        have h_big : USize64.size ≤ acc.val.size + 1 := by omega
        rw [insert_sorted_at_step_oob_not_inserted_fail v x i acc hi_ge h_big] at hres
        cases hres
  | succ n ih =>
    intro i inserted acc r hm hi_le hres
    by_cases hi_ge : v.val.size ≤ i.toNat
    · cases inserted with
      | true =>
        rw [insert_sorted_at_step_oob_inserted v x i acc hi_ge] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        refine ⟨fun y h => h, ?_, ?_⟩
        · intro j hj h_ge; exfalso; omega
        · intro h; cases h
      | false =>
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [insert_sorted_at_step_oob_not_inserted v x i acc hi_ge h_acc] at hres
          injection hres with h_eq
          injection h_eq with h_eq'
          subst h_eq'
          refine ⟨?_, ?_, ?_⟩
          · intro y hy
            show arr_has (acc.val ++ #[x]) y
            rw [arr_has_append]; left; exact hy
          · intro j hj h_ge; exfalso; omega
          · intro _
            show arr_has (acc.val ++ #[x]) x
            rw [arr_has_append]; right; rw [arr_has_singleton]
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_sorted_at_step_oob_not_inserted_fail v x i acc hi_ge h_big] at hres
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
        · rw [insert_sorted_at_step_pass v x i true acc hi_lt (Or.inl rfl) h_acc] at hres
          obtain ⟨h_acc', h_v', h_x'⟩ := ih (i + 1) true _ r h_meas h_i1_le hres
          refine ⟨?_, ?_, ?_⟩
          · intro y hy
            apply h_acc'
            show arr_has (acc.val ++ #[v.val[i.toNat]'hi_lt]) y
            rw [arr_has_append]; left; exact hy
          · intro j hj h_ge
            by_cases h_eq_i : j = i.toNat
            · subst h_eq_i
              apply h_acc'
              show arr_has (acc.val ++ #[v.val[i.toNat]'hi_lt]) (v.val[i.toNat]'hi_lt)
              rw [arr_has_append]; right; rw [arr_has_singleton]
            · apply h_v' j hj
              rw [h_i1]; omega
          · intro h; cases h
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_sorted_at_step_pass_fail v x i true acc hi_lt (Or.inl rfl) h_big] at hres
          cases hres
      | false =>
        by_cases h_vi_ge : (v.val[i.toNat]'hi_lt).toInt ≥ x.toInt
        · -- Insert branch
          by_cases h_acc : acc.val.size + 2 < USize64.size
          · rw [insert_sorted_at_step_insert v x i acc hi_lt h_vi_ge h_acc] at hres
            obtain ⟨h_acc', h_v', _⟩ := ih (i + 1) true _ r h_meas h_i1_le hres
            refine ⟨?_, ?_, ?_⟩
            · intro y hy
              apply h_acc'
              show arr_has (acc.val ++ #[x, v.val[i.toNat]'hi_lt]) y
              rw [arr_has_append]; left; exact hy
            · intro j hj h_ge
              by_cases h_eq_i : j = i.toNat
              · subst h_eq_i
                apply h_acc'
                show arr_has (acc.val ++ #[x, v.val[i.toNat]'hi_lt]) (v.val[i.toNat]'hi_lt)
                rw [arr_has_append]; right; rw [arr_has_pair]; right; rfl
              · apply h_v' j hj
                rw [h_i1]; omega
            · intro _
              apply h_acc'
              show arr_has (acc.val ++ #[x, v.val[i.toNat]'hi_lt]) x
              rw [arr_has_append]; right; rw [arr_has_pair]; left; rfl
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 2 := by omega
            rw [insert_sorted_at_step_insert_fail v x i acc hi_lt h_vi_ge h_big] at hres
            cases hres
        · -- Pass branch with vi < x
          have h_lt : (v.val[i.toNat]'hi_lt).toInt < x.toInt := by omega
          by_cases h_acc : acc.val.size + 1 < USize64.size
          · rw [insert_sorted_at_step_pass v x i false acc hi_lt (Or.inr h_lt) h_acc] at hres
            obtain ⟨h_acc', h_v', h_x'⟩ := ih (i + 1) false _ r h_meas h_i1_le hres
            refine ⟨?_, ?_, ?_⟩
            · intro y hy
              apply h_acc'
              show arr_has (acc.val ++ #[v.val[i.toNat]'hi_lt]) y
              rw [arr_has_append]; left; exact hy
            · intro j hj h_ge
              by_cases h_eq_i : j = i.toNat
              · subst h_eq_i
                apply h_acc'
                show arr_has (acc.val ++ #[v.val[i.toNat]'hi_lt]) (v.val[i.toNat]'hi_lt)
                rw [arr_has_append]; right; rw [arr_has_singleton]
              · apply h_v' j hj
                rw [h_i1]; omega
            · intro _
              exact h_x' rfl
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 1 := by omega
            rw [insert_sorted_at_step_pass_fail v x i false acc hi_lt (Or.inr h_lt) h_big] at hres
            cases hres

/-- Specialization at the initial state. -/
private theorem insert_sorted_covers
    (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (r : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_033_unique.insert_sorted v x = RustM.ok r) :
    (∀ y, arr_has v.val y → arr_has r.val y) ∧ arr_has r.val x := by
  unfold clever_033_unique.insert_sorted at hres
  have h_deref :
      (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec i64 alloc.alloc.Global) v : RustM _) = RustM.ok v := rfl
  have h_new :
      (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk : RustM _)
      = RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_deref, h_new] at hres
  simp only [RustM_ok_bind] at hres
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_meas : v.val.size - (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  have h_le : (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  obtain ⟨h_acc, h_v, h_x⟩ :=
    insert_sorted_at_covers v x v.val.size (0 : usize) false
      ⟨(List.nil).toArray, by grind⟩ r h_meas h_le hres
  refine ⟨?_, h_x rfl⟩
  intro y hy
  obtain ⟨j, hj, h_eq⟩ := hy
  have h_ge : (0 : usize).toNat ≤ j := by rw [h_zero_toNat]; omega
  have := h_v j hj h_ge
  rw [h_eq] at this
  exact this

/-- Coverage for `sort_at`: every element of acc and every l[j] for j ≥ i is in r. -/
private theorem sort_at_covers (l : RustSlice i64) :
    ∀ (n : Nat) (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      clever_033_unique.sort_at l i acc = RustM.ok r →
      (∀ y, arr_has acc.val y → arr_has r.val y) ∧
      (∀ (j : Nat) (hj : j < l.val.size) (_ : i.toNat ≤ j),
          arr_has r.val (l.val[j]'hj)) := by
  intro n
  induction n with
  | zero =>
    intro i acc r hm hi_le hres
    have hi_ge : l.val.size ≤ i.toNat := by omega
    rw [sort_at_oob l i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    refine ⟨fun y h => h, ?_⟩
    intro j hj h_ge; exfalso; omega
  | succ n ih =>
    intro i acc r hm hi_le hres
    by_cases hi_ge : l.val.size ≤ i.toNat
    · rw [sort_at_oob l i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      refine ⟨fun y h => h, ?_⟩
      intro j hj h_ge; exfalso; omega
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_meas : l.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      rw [sort_at_step l i acc hi_lt] at hres
      generalize hins : clever_033_unique.insert_sorted acc (l.val[i.toNat]'hi_lt) = ins_result
      rw [hins] at hres
      cases ins_result with
      | none =>
        exfalso
        have hh : (do let acc' ← (none : RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                       clever_033_unique.sort_at l (i + 1) acc') = RustM.ok r := hres
        cases hh
      | some res' =>
        cases res' with
        | error e =>
          exfalso
          have hh : (do let acc' ← (some (Except.error e) :
                                      RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                         clever_033_unique.sort_at l (i + 1) acc') = RustM.ok r := hres
          cases hh
        | ok acc' =>
          have h_ins_ok : clever_033_unique.insert_sorted acc (l.val[i.toNat]'hi_lt) = RustM.ok acc' :=
            hins
          simp only [RustM_ok_bind] at hres
          obtain ⟨h_acc'_in_r, h_l_in_r⟩ := ih (i + 1) acc' r h_meas h_i1_le hres
          obtain ⟨h_acc_in_acc', h_li_in_acc'⟩ := insert_sorted_covers acc (l.val[i.toNat]'hi_lt) acc' h_ins_ok
          refine ⟨?_, ?_⟩
          · intro y hy
            exact h_acc'_in_r y (h_acc_in_acc' y hy)
          · intro j hj h_ge
            by_cases h_eq_i : j = i.toNat
            · subst h_eq_i
              exact h_acc'_in_r (l.val[i.toNat]'hj) h_li_in_acc'
            · apply h_l_in_r j hj
              rw [h_i1]; omega

/-- Coverage for `dedupe_at`: given that every sorted[j] for j < i is already
    represented in `acc`, every value of `sorted` ends up in `r`. -/
private theorem dedupe_at_covers (sorted : RustSlice i64) :
    ∀ (n : Nat) (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      sorted.val.size - i.toNat ≤ n →
      i.toNat ≤ sorted.val.size →
      clever_033_unique.dedupe_at sorted i acc = RustM.ok r →
      (∀ (j : Nat) (hj_lt_size : j < sorted.val.size) (_ : j < i.toNat),
          arr_has acc.val (sorted.val[j]'hj_lt_size)) →
      ∀ (j : Nat) (hj : j < sorted.val.size), arr_has r.val (sorted.val[j]'hj) := by
  intro n
  induction n with
  | zero =>
    intro i acc r hm hi_le hres h_cov j hj
    have hi_ge : sorted.val.size ≤ i.toNat := by omega
    rw [dedupe_at_oob sorted i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    apply h_cov j hj
    omega
  | succ n ih =>
    intro i acc r hm hi_le hres h_cov j hj
    by_cases hi_ge : sorted.val.size ≤ i.toNat
    · rw [dedupe_at_oob sorted i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      apply h_cov j hj
      omega
    · have hi_lt : i.toNat < sorted.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : sorted.val.size < USize64.size := sorted.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ sorted.val.size := by rw [h_i1]; omega
      have h_meas : sorted.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      by_cases h0 : i.toNat = 0
      · -- Keep branch (i = 0).
        have h0_usize : i = (0 : usize) := by
          have : i.toNat = (0 : usize).toNat := by rw [h0, usize_zero_toNat]
          exact USize64.toNat_inj.mp this
        subst h0_usize
        have h_sz : 0 < sorted.val.size := by rw [usize_zero_toNat] at hi_lt; exact hi_lt
        by_cases h_acc_size_lt : acc.val.size + 1 < USize64.size
        · rw [dedupe_at_step_first sorted acc h_sz h_acc_size_lt] at hres
          have h_one_toNat : (1 : usize).toNat = 1 := usize_one_toNat
          have h_meas' : sorted.val.size - (1 : usize).toNat ≤ n := by rw [h_one_toNat]; omega
          have h_le' : (1 : usize).toNat ≤ sorted.val.size := by rw [h_one_toNat]; omega
          have h_cov' :
              ∀ (k : Nat) (hk_lt_size : k < sorted.val.size) (_ : k < (1 : usize).toNat),
                arr_has (⟨acc.val ++ #[sorted.val[0]'h_sz], by
                          rw [Array.size_append]
                          have h_one : (#[sorted.val[0]'h_sz] : Array i64).size = 1 := rfl
                          omega⟩ : alloc.vec.Vec i64 alloc.alloc.Global).val
                  (sorted.val[k]'hk_lt_size) := by
            intro k hk_lt_size hk_lt_1
            rw [h_one_toNat] at hk_lt_1
            have hk0 : k = 0 := by omega
            subst hk0
            show arr_has (acc.val ++ #[sorted.val[0]'h_sz]) (sorted.val[0]'hk_lt_size)
            rw [arr_has_append]; right; rw [arr_has_singleton]
          exact ih (1 : usize) _ r h_meas' h_le' hres h_cov' j hj
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [dedupe_at_step_first_fail sorted acc h_sz h_big] at hres
          cases hres
      · -- i > 0.
        have hi_pos : 0 < i.toNat := Nat.pos_of_ne_zero h0
        have hi_sub_lt : i.toNat - 1 < sorted.val.size := by omega
        by_cases h_data_eq : sorted.val[i.toNat]'hi_lt = sorted.val[i.toNat - 1]'hi_sub_lt
        · -- Skip branch.
          rw [dedupe_at_step_eq sorted i acc hi_lt hi_pos h_data_eq] at hres
          have h_cov' :
              ∀ (k : Nat) (hk_lt_size : k < sorted.val.size) (_ : k < (i + 1).toNat),
                arr_has acc.val (sorted.val[k]'hk_lt_size) := by
            intro k hk_lt_size hk_lt_i1
            rw [h_i1] at hk_lt_i1
            by_cases h_eq_i : k = i.toNat
            · subst h_eq_i
              have h_im1 : i.toNat - 1 < i.toNat := by omega
              have h_cov_im1 := h_cov (i.toNat - 1) hi_sub_lt h_im1
              have h_idx_eq : sorted.val[i.toNat]'hk_lt_size = sorted.val[i.toNat - 1]'hi_sub_lt :=
                h_data_eq
              rw [h_idx_eq]
              exact h_cov_im1
            · apply h_cov k hk_lt_size; omega
          exact ih (i + 1) acc r h_meas h_i1_le hres h_cov' j hj
        · -- Keep branch (i > 0, sorted[i] ≠ sorted[i-1]).
          by_cases h_acc_size_lt : acc.val.size + 1 < USize64.size
          · rw [dedupe_at_step_neq sorted i acc hi_lt hi_pos h_data_eq h_acc_size_lt] at hres
            have h_cov' :
                ∀ (k : Nat) (hk_lt_size : k < sorted.val.size) (_ : k < (i + 1).toNat),
                  arr_has (⟨acc.val ++ #[sorted.val[i.toNat]'hi_lt], by
                            rw [Array.size_append]
                            have h_one : (#[sorted.val[i.toNat]'hi_lt] : Array i64).size = 1 := rfl
                            omega⟩ : alloc.vec.Vec i64 alloc.alloc.Global).val
                    (sorted.val[k]'hk_lt_size) := by
              intro k hk_lt_size hk_lt_i1
              rw [h_i1] at hk_lt_i1
              show arr_has (acc.val ++ #[sorted.val[i.toNat]'hi_lt]) (sorted.val[k]'hk_lt_size)
              by_cases h_eq_i : k = i.toNat
              · subst h_eq_i
                rw [arr_has_append]; right
                rw [arr_has_singleton]
              · have h_lt_i : k < i.toNat := by omega
                have h_cov_k := h_cov k hk_lt_size h_lt_i
                rw [arr_has_append]; left; exact h_cov_k
            exact ih (i + 1) _ r h_meas h_i1_le hres h_cov' j hj
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 1 := by omega
            rw [dedupe_at_step_neq_fail sorted i acc hi_lt hi_pos h_data_eq h_big] at hres
            cases hres

/-! ### Sortedness predicates and `dedupe_at` strict-increasing lemma.

`sorted_asc arr` is the non-strict ascending predicate (`arr[k] ≤ arr[k+1]`).
`strict_inc arr` is the strict ascending predicate (`arr[k] < arr[k+1]`). -/

private def sorted_asc (arr : Array i64) : Prop :=
  ∀ (k₁ k₂ : Nat) (h₁ : k₁ < arr.size) (h₂ : k₂ < arr.size),
    k₁ ≤ k₂ → (arr[k₁]'h₁).toInt ≤ (arr[k₂]'h₂).toInt

private def strict_inc (arr : Array i64) : Prop :=
  ∀ (k₁ k₂ : Nat) (h₁ : k₁ < arr.size) (h₂ : k₂ < arr.size),
    k₁ < k₂ → (arr[k₁]'h₁).toInt < (arr[k₂]'h₂).toInt

private theorem sorted_asc_empty : sorted_asc #[] := by
  intro k₁ k₂ h₁ _ _
  have : (#[] : Array i64).size = 0 := rfl
  omega

private theorem strict_inc_empty : strict_inc #[] := by
  intro k₁ k₂ h₁ _ _
  have : (#[] : Array i64).size = 0 := rfl
  omega

/-- Strict-increasing of `acc ++ #[y]` from strict-increasing of `acc` and
    every element of `acc` being strictly less than `y`. -/
private theorem strict_inc_append_singleton (acc : Array i64) (y : i64)
    (h_acc : strict_inc acc)
    (h_lt : ∀ (k : Nat) (hk : k < acc.size), (acc[k]'hk).toInt < y.toInt) :
    strict_inc (acc ++ #[y]) := by
  intro k₁ k₂ h₁ h₂ hlt12
  rw [Array.size_append] at h₁ h₂
  have h_one : (#[y] : Array i64).size = 1 := rfl
  by_cases h_k1_lt : k₁ < acc.size
  · by_cases h_k2_lt : k₂ < acc.size
    · -- both in original acc
      rw [Array.getElem_append_left h_k1_lt, Array.getElem_append_left h_k2_lt]
      exact h_acc k₁ k₂ h_k1_lt h_k2_lt hlt12
    · -- k₂ ≥ acc.size, i.e. k₂ = acc.size (singleton)
      have h_k2_eq : k₂ = acc.size := by omega
      rw [Array.getElem_append_left h_k1_lt]
      have h_k2_ge : acc.size ≤ k₂ := by omega
      rw [Array.getElem_append_right h_k2_ge]
      have h_idx : k₂ - acc.size = 0 := by omega
      have h_zero : (0 : Nat) < (#[y] : Array i64).size := by rw [h_one]; omega
      rw [show ((#[y] : Array i64)[k₂ - acc.size]'(by rw [h_idx]; exact h_zero))
              = (#[y] : Array i64)[0]'h_zero from by simp [h_idx]]
      show (acc[k₁]'h_k1_lt).toInt < y.toInt
      exact h_lt k₁ h_k1_lt
  · exfalso
    have h_k1_ge : acc.size ≤ k₁ := by omega
    have h_k1_eq : k₁ = acc.size := by omega
    -- k₂ > k₁ = acc.size, but k₂ < acc.size + 1, so k₂ ≤ acc.size — contradiction.
    omega

/-- Sortedness preserved by sub-slice: if `sorted_asc s.val` then every pair
    from indices `k₁ ≤ k₂ < size` satisfies `s[k₁] ≤ s[k₂]`. (Direct from def.) -/
private theorem sorted_asc_pair (s : RustSlice i64) (h_sorted : sorted_asc s.val)
    (k₁ k₂ : Nat) (h₁ : k₁ < s.val.size) (h₂ : k₂ < s.val.size) (hle : k₁ ≤ k₂) :
    (s.val[k₁]'h₁).toInt ≤ (s.val[k₂]'h₂).toInt :=
  h_sorted k₁ k₂ h₁ h₂ hle

/-- Strong induction for `dedupe_at`: under sortedness of input + boundary
    condition on acc, the output is strictly increasing. -/
private theorem dedupe_at_strict_inc (sorted : RustSlice i64)
    (h_sorted : sorted_asc sorted.val) :
    ∀ (n : Nat) (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      sorted.val.size - i.toNat ≤ n →
      i.toNat ≤ sorted.val.size →
      clever_033_unique.dedupe_at sorted i acc = RustM.ok r →
      strict_inc acc.val →
      (∀ (k : Nat) (hk : k < acc.val.size) (hi_pos : 0 < i.toNat)
        (h_im1 : i.toNat - 1 < sorted.val.size),
          (acc.val[k]'hk).toInt ≤ (sorted.val[i.toNat - 1]'h_im1).toInt) →
      (0 < i.toNat ∨ acc.val.size = 0) →
      strict_inc r.val := by
  intro n
  induction n with
  | zero =>
    intro i acc r hm hi_le hres h_acc_inc h_acc_bound h_extra
    have hi_ge : sorted.val.size ≤ i.toNat := by omega
    rw [dedupe_at_oob sorted i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    exact h_acc_inc
  | succ n ih =>
    intro i acc r hm hi_le hres h_acc_inc h_acc_bound h_extra
    by_cases hi_ge : sorted.val.size ≤ i.toNat
    · rw [dedupe_at_oob sorted i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      exact h_acc_inc
    · have hi_lt : i.toNat < sorted.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : sorted.val.size < USize64.size := sorted.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ sorted.val.size := by rw [h_i1]; omega
      have h_meas : sorted.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      by_cases h0 : i.toNat = 0
      · -- i = 0: keep branch, no boundary condition needed (i.toNat = 0).
        have h0_usize : i = (0 : usize) := by
          have : i.toNat = (0 : usize).toNat := by rw [h0, usize_zero_toNat]
          exact USize64.toNat_inj.mp this
        subst h0_usize
        have h_sz : 0 < sorted.val.size := by rw [usize_zero_toNat] at hi_lt; exact hi_lt
        have h_acc_empty : acc.val.size = 0 := by
          rcases h_extra with h_pos | h_e
          · exfalso
            rw [usize_zero_toNat] at h_pos; omega
          · exact h_e
        by_cases h_acc_size_lt : acc.val.size + 1 < USize64.size
        · rw [dedupe_at_step_first sorted acc h_sz h_acc_size_lt] at hres
          have h_one_toNat : (1 : usize).toNat = 1 := usize_one_toNat
          have h_meas' : sorted.val.size - (1 : usize).toNat ≤ n := by rw [h_one_toNat]; omega
          have h_le' : (1 : usize).toNat ≤ sorted.val.size := by rw [h_one_toNat]; omega
          have h_new_inc :
              strict_inc ((⟨acc.val ++ #[sorted.val[0]'h_sz], by
                            rw [Array.size_append]
                            have h_one : (#[sorted.val[0]'h_sz] : Array i64).size = 1 := rfl
                            omega⟩ : alloc.vec.Vec i64 alloc.alloc.Global).val) := by
            show strict_inc (acc.val ++ #[sorted.val[0]'h_sz])
            apply strict_inc_append_singleton acc.val (sorted.val[0]'h_sz) h_acc_inc
            intro k hk
            exfalso; omega
          have h_new_bound :
              ∀ (k : Nat) (hk : k < (⟨acc.val ++ #[sorted.val[0]'h_sz], by
                                        rw [Array.size_append]
                                        have h_one : (#[sorted.val[0]'h_sz] : Array i64).size = 1 := rfl
                                        omega⟩ : alloc.vec.Vec i64 alloc.alloc.Global).val.size)
                (_ : 0 < (1 : usize).toNat)
                (h_im1 : (1 : usize).toNat - 1 < sorted.val.size),
                ((⟨acc.val ++ #[sorted.val[0]'h_sz], by
                     rw [Array.size_append]
                     have h_one : (#[sorted.val[0]'h_sz] : Array i64).size = 1 := rfl
                     omega⟩ : alloc.vec.Vec i64 alloc.alloc.Global).val[k]'hk).toInt
                  ≤ (sorted.val[(1 : usize).toNat - 1]'h_im1).toInt := by
            intro k hk _ h_im1
            rw [h_one_toNat] at h_im1
            show ((acc.val ++ #[sorted.val[0]'h_sz])[k]'hk).toInt
                ≤ (sorted.val[1 - 1]'h_im1).toInt
            show ((acc.val ++ #[sorted.val[0]'h_sz])[k]'hk).toInt
                ≤ (sorted.val[0]'h_im1).toInt
            have h_size : ((acc.val ++ #[sorted.val[0]'h_sz])).size = 1 := by
              rw [Array.size_append]
              have h_one : (#[sorted.val[0]'h_sz] : Array i64).size = 1 := rfl
              omega
            have hk_lt_1 : k < 1 := by rw [← h_size]; exact hk
            have hk_eq : k = 0 := by omega
            subst hk_eq
            have h_ge : acc.val.size ≤ 0 := by omega
            rw [Array.getElem_append_right h_ge]
            have h_zero_idx : 0 - acc.val.size = 0 := by omega
            simp only [h_zero_idx]
            have h_zero_lt : (0 : Nat) < (#[sorted.val[0]'h_sz] : Array i64).size := by
              have h_one : (#[sorted.val[0]'h_sz] : Array i64).size = 1 := rfl
              omega
            show ((#[sorted.val[0]'h_sz] : Array i64)[0]'h_zero_lt).toInt
                ≤ (sorted.val[0]'h_im1).toInt
            show (sorted.val[0]'h_sz).toInt ≤ (sorted.val[0]'h_im1).toInt
            exact Int.le_refl _
          have h_new_extra : 0 < (1 : usize).toNat ∨
              ((⟨acc.val ++ #[sorted.val[0]'h_sz], by
                  rw [Array.size_append]
                  have h_one : (#[sorted.val[0]'h_sz] : Array i64).size = 1 := rfl
                  omega⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := by
            left; rw [usize_one_toNat]; omega
          exact ih (1 : usize) _ r h_meas' h_le' hres h_new_inc h_new_bound h_new_extra
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [dedupe_at_step_first_fail sorted acc h_sz h_big] at hres
          cases hres
      · -- i > 0.
        have hi_pos : 0 < i.toNat := Nat.pos_of_ne_zero h0
        have hi_sub_lt : i.toNat - 1 < sorted.val.size := by omega
        by_cases h_data_eq : sorted.val[i.toNat]'hi_lt = sorted.val[i.toNat - 1]'hi_sub_lt
        · -- Skip branch.
          rw [dedupe_at_step_eq sorted i acc hi_lt hi_pos h_data_eq] at hres
          -- New invariant for IH: acc still strict_inc.
          -- Boundary: every elem of acc ≤ sorted[i+1-1] = sorted[i] = sorted[i-1].
          have h_new_bound :
              ∀ (k : Nat) (hk : k < acc.val.size) (_ : 0 < (i + 1).toNat)
                (h_im1 : (i + 1).toNat - 1 < sorted.val.size),
                (acc.val[k]'hk).toInt ≤ (sorted.val[(i + 1).toNat - 1]'h_im1).toInt := by
            intro k hk _ h_im1
            have h_idx_eq : (i + 1).toNat - 1 = i.toNat := by rw [h_i1]; omega
            -- (i+1).toNat - 1 = i.toNat.
            rw [show (sorted.val[(i + 1).toNat - 1]'h_im1) = (sorted.val[i.toNat]'hi_lt) from by
                  congr 1]
            rw [show ((sorted.val[i.toNat]'hi_lt) : i64) = (sorted.val[i.toNat - 1]'hi_sub_lt) from h_data_eq]
            exact h_acc_bound k hk hi_pos hi_sub_lt
          have h_new_extra : 0 < (i + 1).toNat ∨ acc.val.size = 0 := by
            left; rw [h_i1]; omega
          exact ih (i + 1) acc r h_meas h_i1_le hres h_acc_inc h_new_bound h_new_extra
        · -- Keep branch (i > 0).
          by_cases h_acc_size_lt : acc.val.size + 1 < USize64.size
          · rw [dedupe_at_step_neq sorted i acc hi_lt hi_pos h_data_eq h_acc_size_lt] at hres
            -- Need acc.last < sorted[i].
            -- sorted is sorted_asc: sorted[i-1] ≤ sorted[i].
            -- h_data_eq says sorted[i] ≠ sorted[i-1].
            -- So sorted[i-1] < sorted[i].
            have h_sorted_im1_le_i : (sorted.val[i.toNat - 1]'hi_sub_lt).toInt
                                      ≤ (sorted.val[i.toNat]'hi_lt).toInt :=
              h_sorted (i.toNat - 1) i.toNat hi_sub_lt hi_lt (by omega)
            have h_neq_int : (sorted.val[i.toNat - 1]'hi_sub_lt).toInt
                              ≠ (sorted.val[i.toNat]'hi_lt).toInt := by
              intro h_eq
              apply h_data_eq
              -- The eq is on i64, need to deduce from toInt eq.
              -- Use Int64.ofInt_toInt (or similar).
              have h_ofInt1 : Int64.ofInt (sorted.val[i.toNat]'hi_lt).toInt
                              = sorted.val[i.toNat]'hi_lt := Int64.ofInt_toInt _
              have h_ofInt2 : Int64.ofInt (sorted.val[i.toNat - 1]'hi_sub_lt).toInt
                              = sorted.val[i.toNat - 1]'hi_sub_lt := Int64.ofInt_toInt _
              rw [← h_ofInt1, ← h_ofInt2, h_eq]
            have h_sorted_im1_lt_i : (sorted.val[i.toNat - 1]'hi_sub_lt).toInt
                                      < (sorted.val[i.toNat]'hi_lt).toInt := by
              omega
            -- New acc' = acc ++ [sorted[i]]. Strict_inc preserved.
            have h_new_inc :
                strict_inc ((⟨acc.val ++ #[sorted.val[i.toNat]'hi_lt], by
                              rw [Array.size_append]
                              have h_one : (#[sorted.val[i.toNat]'hi_lt] : Array i64).size = 1 := rfl
                              omega⟩ : alloc.vec.Vec i64 alloc.alloc.Global).val) := by
              show strict_inc (acc.val ++ #[sorted.val[i.toNat]'hi_lt])
              apply strict_inc_append_singleton acc.val (sorted.val[i.toNat]'hi_lt) h_acc_inc
              intro k hk
              have h_acc_k_le := h_acc_bound k hk hi_pos hi_sub_lt
              omega
            have h_new_bound :
                ∀ (k : Nat) (hk : k < (⟨acc.val ++ #[sorted.val[i.toNat]'hi_lt], by
                                          rw [Array.size_append]
                                          have h_one : (#[sorted.val[i.toNat]'hi_lt] : Array i64).size = 1 := rfl
                                          omega⟩ : alloc.vec.Vec i64 alloc.alloc.Global).val.size)
                  (_ : 0 < (i + 1).toNat)
                  (h_im1 : (i + 1).toNat - 1 < sorted.val.size),
                  ((⟨acc.val ++ #[sorted.val[i.toNat]'hi_lt], by
                       rw [Array.size_append]
                       have h_one : (#[sorted.val[i.toNat]'hi_lt] : Array i64).size = 1 := rfl
                       omega⟩ : alloc.vec.Vec i64 alloc.alloc.Global).val[k]'hk).toInt
                    ≤ (sorted.val[(i + 1).toNat - 1]'h_im1).toInt := by
              intro k hk _ h_im1
              show ((acc.val ++ #[sorted.val[i.toNat]'hi_lt])[k]'hk).toInt
                  ≤ (sorted.val[(i + 1).toNat - 1]'h_im1).toInt
              have h_idx_eq : (i + 1).toNat - 1 = i.toNat := by rw [h_i1]; omega
              rw [show (sorted.val[(i + 1).toNat - 1]'h_im1) = (sorted.val[i.toNat]'hi_lt) from by
                    congr 1]
              by_cases h_k_lt : k < acc.val.size
              · rw [Array.getElem_append_left h_k_lt]
                have h_acc_k := h_acc_bound k h_k_lt hi_pos hi_sub_lt
                omega
              · -- k = acc.val.size
                have h_k_size : k = acc.val.size := by
                  rw [Array.size_append] at hk
                  have h_one : (#[sorted.val[i.toNat]'hi_lt] : Array i64).size = 1 := rfl
                  omega
                subst h_k_size
                have h_ge : acc.val.size ≤ acc.val.size := Nat.le_refl _
                rw [Array.getElem_append_right h_ge]
                simp only [Nat.sub_self]
                show (sorted.val[i.toNat]'hi_lt).toInt ≤ (sorted.val[i.toNat]'hi_lt).toInt
                exact Int.le_refl _
            have h_new_extra : 0 < (i + 1).toNat ∨
                ((⟨acc.val ++ #[sorted.val[i.toNat]'hi_lt], by
                    rw [Array.size_append]
                    have h_one : (#[sorted.val[i.toNat]'hi_lt] : Array i64).size = 1 := rfl
                    omega⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := by
              left; rw [h_i1]; omega
            exact ih (i + 1) _ r h_meas h_i1_le hres h_new_inc h_new_bound h_new_extra
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 1 := by omega
            rw [dedupe_at_step_neq_fail sorted i acc hi_lt hi_pos h_data_eq h_big] at hres
            cases hres

/-! ### Sortedness preservation for insertion sort. -/

/-- `sorted_asc (acc ++ #[y])` from `sorted_asc acc` and "every elem of acc ≤ y". -/
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
    · -- k₂ = acc.size
      have h_k2_eq : k₂ = acc.size := by omega
      rw [Array.getElem_append_left h_k1_lt]
      have h_k2_ge : acc.size ≤ k₂ := by omega
      rw [Array.getElem_append_right h_k2_ge]
      have h_idx : k₂ - acc.size = 0 := by omega
      have h_zero : (0 : Nat) < (#[y] : Array i64).size := by rw [h_one]; omega
      rw [show ((#[y] : Array i64)[k₂ - acc.size]'(by rw [h_idx]; exact h_zero))
              = (#[y] : Array i64)[0]'h_zero from by simp [h_idx]]
      show (acc[k₁]'h_k1_lt).toInt ≤ y.toInt
      exact h_le k₁ h_k1_lt
  · -- k₁ ≥ acc.size, both in singleton
    have h_k1_ge : acc.size ≤ k₁ := by omega
    have h_k2_ge : acc.size ≤ k₂ := by omega
    rw [Array.getElem_append_right h_k1_ge, Array.getElem_append_right h_k2_ge]
    have h_k1_idx : k₁ - acc.size = 0 := by omega
    have h_k2_idx : k₂ - acc.size = 0 := by omega
    have h_zero : (0 : Nat) < (#[y] : Array i64).size := by rw [h_one]; omega
    show ((#[y] : Array i64)[k₁ - acc.size]'(by rw [h_k1_idx]; exact h_zero)).toInt
        ≤ ((#[y] : Array i64)[k₂ - acc.size]'(by rw [h_k2_idx]; exact h_zero)).toInt
    rw [show ((#[y] : Array i64)[k₁ - acc.size]'(by rw [h_k1_idx]; exact h_zero))
            = (#[y] : Array i64)[0]'h_zero from by simp [h_k1_idx]]
    rw [show ((#[y] : Array i64)[k₂ - acc.size]'(by rw [h_k2_idx]; exact h_zero))
            = (#[y] : Array i64)[0]'h_zero from by simp [h_k2_idx]]
    exact Int.le_refl _

/-- `sorted_asc (acc ++ #[a, b])` from `sorted_asc acc` and the right bounds. -/
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
      -- k₂ - acc.size is either 0 (a) or 1 (b).
      have h_k2_sub : k₂ - acc.size < 2 := by omega
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
    -- Both in #[a, b].
    have h_k1_sub : k₁ - acc.size < 2 := by omega
    have h_k2_sub : k₂ - acc.size < 2 := by omega
    have h_le_sub : k₁ - acc.size ≤ k₂ - acc.size := by omega
    -- 0 ≤ 0, 0 ≤ 1, 1 ≤ 1 cases.
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

/-- Strong induction: insert_sorted_at maintains sortedness invariant. -/
private theorem insert_sorted_at_sorted (v : RustSlice i64) (x : i64)
    (h_v_sorted : sorted_asc v.val) :
    ∀ (n : Nat) (i : usize) (inserted : Bool)
      (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      v.val.size - i.toNat ≤ n →
      i.toNat ≤ v.val.size →
      clever_033_unique.insert_sorted_at v x i inserted acc = RustM.ok r →
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
      rw [insert_sorted_at_step_oob_inserted v x i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      exact h_acc_sorted
    | false =>
      by_cases h_acc : acc.val.size + 1 < USize64.size
      · rw [insert_sorted_at_step_oob_not_inserted v x i acc hi_ge h_acc] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        show sorted_asc (acc.val ++ #[x])
        apply sorted_asc_append_singleton acc.val x h_acc_sorted
        exact h_acc_le_x rfl
      · exfalso
        have h_big : USize64.size ≤ acc.val.size + 1 := by omega
        rw [insert_sorted_at_step_oob_not_inserted_fail v x i acc hi_ge h_big] at hres
        cases hres
  | succ n ih =>
    intro i inserted acc r hm hi_le hres h_acc_sorted h_acc_le_vi h_acc_le_x
    by_cases hi_ge : v.val.size ≤ i.toNat
    · cases inserted with
      | true =>
        rw [insert_sorted_at_step_oob_inserted v x i acc hi_ge] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        exact h_acc_sorted
      | false =>
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [insert_sorted_at_step_oob_not_inserted v x i acc hi_ge h_acc] at hres
          injection hres with h_eq
          injection h_eq with h_eq'
          subst h_eq'
          show sorted_asc (acc.val ++ #[x])
          apply sorted_asc_append_singleton acc.val x h_acc_sorted
          exact h_acc_le_x rfl
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_sorted_at_step_oob_not_inserted_fail v x i acc hi_ge h_big] at hres
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
        · rw [insert_sorted_at_step_pass v x i true acc hi_lt (Or.inl rfl) h_acc] at hres
          -- New acc' = acc ++ [v[i]]. Sorted: acc.last ≤ v[i] (from h_acc_le_vi).
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
              have h_k_eq : k = acc.val.size := by omega
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
          rw [insert_sorted_at_step_pass_fail v x i true acc hi_lt (Or.inl rfl) h_big] at hres
          cases hres
      | false =>
        by_cases h_vi_ge : (v.val[i.toNat]'hi_lt).toInt ≥ x.toInt
        · -- Insert branch (size-2 chunk).
          by_cases h_acc : acc.val.size + 2 < USize64.size
          · rw [insert_sorted_at_step_insert v x i acc hi_lt h_vi_ge h_acc] at hres
            -- New acc' = acc ++ [x, v[i]]. Sorted: acc.last ≤ x ≤ v[i].
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
            rw [insert_sorted_at_step_insert_fail v x i acc hi_lt h_vi_ge h_big] at hres
            cases hres
        · -- Pass branch with vi < x.
          have h_lt : (v.val[i.toNat]'hi_lt).toInt < x.toInt := by omega
          by_cases h_acc : acc.val.size + 1 < USize64.size
          · rw [insert_sorted_at_step_pass v x i false acc hi_lt (Or.inr h_lt) h_acc] at hres
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
            rw [insert_sorted_at_step_pass_fail v x i false acc hi_lt (Or.inr h_lt) h_big] at hres
            cases hres

/-- `insert_sorted` preserves sortedness. -/
private theorem insert_sorted_sorted (v : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (r : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_033_unique.insert_sorted v x = RustM.ok r)
    (h_v_sorted : sorted_asc v.val) :
    sorted_asc r.val := by
  unfold clever_033_unique.insert_sorted at hres
  have h_deref :
      (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec i64 alloc.alloc.Global) v : RustM _) = RustM.ok v := rfl
  have h_new :
      (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk : RustM _)
      = RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_deref, h_new] at hres
  simp only [RustM_ok_bind] at hres
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_meas : v.val.size - (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  have h_le : (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  apply insert_sorted_at_sorted v x h_v_sorted v.val.size (0 : usize) false
    ⟨(List.nil).toArray, by grind⟩ r h_meas h_le hres
  · -- sorted_asc empty
    intro k₁ k₂ h₁ _ _
    exfalso
    have : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  · intro k hk _; exfalso
    have : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  · intro _ k hk; exfalso
    have : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
    omega

/-- Strong induction: `sort_at` preserves sortedness — if acc is sorted, output is sorted. -/
private theorem sort_at_sorted (l : RustSlice i64) :
    ∀ (n : Nat) (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (r : alloc.vec.Vec i64 alloc.alloc.Global),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      clever_033_unique.sort_at l i acc = RustM.ok r →
      sorted_asc acc.val →
      sorted_asc r.val := by
  intro n
  induction n with
  | zero =>
    intro i acc r hm hi_le hres h_acc_sorted
    have hi_ge : l.val.size ≤ i.toNat := by omega
    rw [sort_at_oob l i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    exact h_acc_sorted
  | succ n ih =>
    intro i acc r hm hi_le hres h_acc_sorted
    by_cases hi_ge : l.val.size ≤ i.toNat
    · rw [sort_at_oob l i acc hi_ge] at hres
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
      rw [sort_at_step l i acc hi_lt] at hres
      generalize hins : clever_033_unique.insert_sorted acc (l.val[i.toNat]'hi_lt) = ins_result
      rw [hins] at hres
      cases ins_result with
      | none =>
        exfalso
        have hh : (do let acc' ← (none : RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                       clever_033_unique.sort_at l (i + 1) acc') = RustM.ok r := hres
        cases hh
      | some res' =>
        cases res' with
        | error e =>
          exfalso
          have hh : (do let acc' ← (some (Except.error e) :
                                      RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                         clever_033_unique.sort_at l (i + 1) acc') = RustM.ok r := hres
          cases hh
        | ok acc' =>
          have h_ins_ok : clever_033_unique.insert_sorted acc (l.val[i.toNat]'hi_lt) = RustM.ok acc' :=
            hins
          simp only [RustM_ok_bind] at hres
          -- acc' is sorted because acc is sorted and we inserted via insert_sorted.
          -- But insert_sorted_sorted requires acc to be sorted, which we have.
          have h_acc'_sorted : sorted_asc acc'.val :=
            insert_sorted_sorted acc (l.val[i.toNat]'hi_lt) acc' h_ins_ok h_acc_sorted
          exact ih (i + 1) acc' r h_meas h_i1_le hres h_acc'_sorted

/-! ## Postcondition 1: output is strictly increasing.

Stated on consecutive entries (`k`, `k+1`) — matching the proptest's
`windows(2)` form. Strict ordering captures BOTH "sorted ascending" and
"no duplicates" in one clause, exactly as the proptest comment notes. -/

/-- Postcondition 1: consecutive output entries are strictly increasing.
    Captures the proptest `output_is_strictly_increasing`.

    Proved by composing `sort_at_sorted` (sort_at produces sorted output —
    classic insertion-sort correctness) with `dedupe_at_strict_inc`
    (dedupe over a sorted input produces strictly increasing output, because
    consecutive distinct elements in a sorted sequence are strictly less). -/
theorem output_is_strictly_increasing
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_033_unique.unique l = RustM.ok v)
    (k : Nat) (hk : k + 1 < v.val.size) :
    (v.val[k]'(Nat.lt_of_succ_lt hk)).toInt < (v.val[k + 1]'hk).toInt := by
  -- Reduce hres.
  unfold clever_033_unique.unique at hres
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  generalize h_sort : clever_033_unique.sort_at l (0 : usize)
                        ⟨(List.nil).toArray, by grind⟩ = sort_res at hres
  cases sort_res with
  | none =>
    exfalso
    have hh : (do let sorted ← (none : RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                  let sorted_deref ← (core_models.ops.deref.Deref.deref
                    (alloc.vec.Vec i64 alloc.alloc.Global) sorted :
                    RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                  let acc0 ← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                              RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                  clever_033_unique.dedupe_at sorted_deref (0 : usize) acc0)
              = RustM.ok v := hres
    cases hh
  | some sort_res' =>
    cases sort_res' with
    | error e =>
      exfalso
      have hh : (do let sorted ← (some (Except.error e) :
                                    RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                    let sorted_deref ← (core_models.ops.deref.Deref.deref
                      (alloc.vec.Vec i64 alloc.alloc.Global) sorted :
                      RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                    let acc0 ← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                                RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                    clever_033_unique.dedupe_at sorted_deref (0 : usize) acc0)
                = RustM.ok v := hres
      cases hh
    | ok sorted =>
      have h_sort_ok : clever_033_unique.sort_at l (0 : usize)
                          ⟨(List.nil).toArray, by grind⟩ = RustM.ok sorted := h_sort
      simp only [RustM_ok_bind] at hres
      have h_deref :
          (core_models.ops.deref.Deref.deref
            (alloc.vec.Vec i64 alloc.alloc.Global) sorted : RustM _) = RustM.ok sorted := rfl
      rw [h_deref] at hres
      simp only [RustM_ok_bind] at hres
      -- Step 1: sorted is sorted_asc.
      have h_empty_sorted : sorted_asc
          ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val := by
        intro k₁ k₂ h₁ _ _
        exfalso
        have : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
        omega
      have h_zero_toNat : (0 : usize).toNat = 0 := rfl
      have h_meas_sort : l.val.size - (0 : usize).toNat ≤ l.val.size := by rw [h_zero_toNat]; omega
      have h_le_sort : (0 : usize).toNat ≤ l.val.size := by rw [h_zero_toNat]; omega
      have h_sorted_asc : sorted_asc sorted.val :=
        sort_at_sorted l l.val.size (0 : usize)
          ⟨(List.nil).toArray, by grind⟩ sorted h_meas_sort h_le_sort h_sort_ok h_empty_sorted
      -- Step 2: dedupe_at on sorted gives strict_inc.
      have h_meas_dedupe : sorted.val.size - (0 : usize).toNat ≤ sorted.val.size := by
        rw [h_zero_toNat]; omega
      have h_le_dedupe : (0 : usize).toNat ≤ sorted.val.size := by rw [h_zero_toNat]; omega
      have h_empty_strict : strict_inc
          ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val := by
        intro k₁ k₂ h₁ _ _
        exfalso
        have : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
        omega
      have h_empty_bound :
          ∀ (j : Nat) (hj : j < ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size)
            (_ : 0 < (0 : usize).toNat)
            (h_im1 : (0 : usize).toNat - 1 < sorted.val.size),
            (((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val[j]'hj).toInt
              ≤ (sorted.val[(0 : usize).toNat - 1]'h_im1).toInt := by
        intro j hj _ _
        exfalso
        have : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
        omega
      have h_empty_extra : 0 < (0 : usize).toNat ∨
          ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := by
        right; rfl
      have h_v_strict_inc : strict_inc v.val :=
        dedupe_at_strict_inc sorted h_sorted_asc sorted.val.size (0 : usize)
          ⟨(List.nil).toArray, by grind⟩ v h_meas_dedupe h_le_dedupe hres
          h_empty_strict h_empty_bound h_empty_extra
      -- Apply strict_inc to k, k+1.
      exact h_v_strict_inc k (k + 1) (Nat.lt_of_succ_lt hk) hk (Nat.lt_succ_self k)

/-! ## Postcondition 2: every input element appears in the output.

Existential index witness: for each input position `i`, there is some
output position `k` with `v[k] = l[i]`. Matches the proptest's
`out.contains(x)` check translated to an index witness. -/

/-- Postcondition 2: every input element appears somewhere in the output.
    Captures the proptest `output_contains_every_input_element`.

    Proved by chaining `sort_at_covers` (every l[i] is in sort_at's
    output) with `dedupe_at_covers` (every value in sorted is in v —
    even without sortedness, because the only way a value is skipped
    by dedupe is to equal its immediate predecessor, which is itself
    represented in the output). -/
theorem output_contains_every_input_element
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_033_unique.unique l = RustM.ok v)
    (i : Nat) (hi : i < l.val.size) :
    ∃ (k : Nat) (hk : k < v.val.size), v.val[k]'hk = l.val[i]'hi := by
  -- Reduce hres.
  unfold clever_033_unique.unique at hres
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  generalize h_sort : clever_033_unique.sort_at l (0 : usize)
                        ⟨(List.nil).toArray, by grind⟩ = sort_res at hres
  cases sort_res with
  | none =>
    exfalso
    have hh : (do let sorted ← (none : RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                  let sorted_deref ← (core_models.ops.deref.Deref.deref
                    (alloc.vec.Vec i64 alloc.alloc.Global) sorted :
                    RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                  let acc0 ← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                              RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                  clever_033_unique.dedupe_at sorted_deref (0 : usize) acc0)
              = RustM.ok v := hres
    cases hh
  | some sort_res' =>
    cases sort_res' with
    | error e =>
      exfalso
      have hh : (do let sorted ← (some (Except.error e) :
                                    RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                    let sorted_deref ← (core_models.ops.deref.Deref.deref
                      (alloc.vec.Vec i64 alloc.alloc.Global) sorted :
                      RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                    let acc0 ← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                                RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                    clever_033_unique.dedupe_at sorted_deref (0 : usize) acc0)
                = RustM.ok v := hres
      cases hh
    | ok sorted =>
      have h_sort_ok : clever_033_unique.sort_at l (0 : usize)
                          ⟨(List.nil).toArray, by grind⟩ = RustM.ok sorted := h_sort
      simp only [RustM_ok_bind] at hres
      have h_deref :
          (core_models.ops.deref.Deref.deref
            (alloc.vec.Vec i64 alloc.alloc.Global) sorted : RustM _) = RustM.ok sorted := rfl
      rw [h_deref] at hres
      simp only [RustM_ok_bind] at hres
      -- hres : dedupe_at sorted 0 ⟨#[], _⟩ = RustM.ok v
      -- Step 1: l.val[i] is in sorted (by sort_at_covers).
      have h_zero_toNat : (0 : usize).toNat = 0 := rfl
      have h_meas_sort : l.val.size - (0 : usize).toNat ≤ l.val.size := by rw [h_zero_toNat]; omega
      have h_le_sort : (0 : usize).toNat ≤ l.val.size := by rw [h_zero_toNat]; omega
      obtain ⟨_, h_l_in_sorted⟩ :=
        sort_at_covers l l.val.size (0 : usize)
          ⟨(List.nil).toArray, by grind⟩ sorted h_meas_sort h_le_sort h_sort_ok
      have h_ge : (0 : usize).toNat ≤ i := by rw [h_zero_toNat]; omega
      have h_li_in_sorted := h_l_in_sorted i hi h_ge
      -- h_li_in_sorted : arr_has sorted.val (l.val[i])
      obtain ⟨m, hm_lt, hm_eq⟩ := h_li_in_sorted
      -- Step 2: sorted.val[m] is in v (by dedupe_at_covers).
      have h_meas_dedupe : sorted.val.size - (0 : usize).toNat ≤ sorted.val.size := by
        rw [h_zero_toNat]; omega
      have h_le_dedupe : (0 : usize).toNat ≤ sorted.val.size := by rw [h_zero_toNat]; omega
      have h_cov_init :
          ∀ (k : Nat) (_ : k < sorted.val.size) (_ : k < (0 : usize).toNat),
            arr_has ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val
              (sorted.val[k]'(by assumption)) := by
        intro k _ hk_lt_0
        rw [h_zero_toNat] at hk_lt_0; exfalso; omega
      have h_sorted_m_in_v :=
        dedupe_at_covers sorted sorted.val.size (0 : usize)
          ⟨(List.nil).toArray, by grind⟩ v h_meas_dedupe h_le_dedupe hres h_cov_init m hm_lt
      -- h_sorted_m_in_v : arr_has v.val (sorted.val[m])
      obtain ⟨k, hk, hk_eq⟩ := h_sorted_m_in_v
      refine ⟨k, hk, ?_⟩
      rw [hk_eq, hm_eq]

/-! ## Postcondition 3: every output element came from the input.

Existential index witness: for each output position `k`, there is some
input position `i` with `l[i] = v[k]`. Matches the proptest's
`l.contains(y)` check translated to an index witness. -/

/-- Postcondition 3: every output element occurs in the input.
    Captures the proptest `output_only_contains_input_elements`.

    Proved by strong induction over `sort_at` and `dedupe_at`. Every
    output element of `dedupe_at sorted 0 #[]` is in `sorted`, and
    every element of `sorted = sort_at l 0 #[]` is in `l`. The
    membership predicate `arr_has` and the bridging lemmas in
    `arr_has_append` / `arr_has_singleton` / `arr_has_pair` carry the
    invariant through the four `partial_fixpoint` extraction shapes. -/
theorem output_only_contains_input_elements
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_033_unique.unique l = RustM.ok v)
    (k : Nat) (hk : k < v.val.size) :
    ∃ (i : Nat) (hi : i < l.val.size), l.val[i]'hi = v.val[k]'hk := by
  -- Reduce hres: unique l = (sort_at l 0 #[]) >>= λ sorted → dedupe_at (deref sorted) 0 #[]
  unfold clever_033_unique.unique at hres
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  -- Case on sort_at result.
  generalize h_sort : clever_033_unique.sort_at l (0 : usize)
                        ⟨(List.nil).toArray, by grind⟩ = sort_res at hres
  cases sort_res with
  | none =>
    exfalso
    have hh : (do let sorted ← (none : RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                  let sorted_deref ← (core_models.ops.deref.Deref.deref
                    (alloc.vec.Vec i64 alloc.alloc.Global) sorted :
                    RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                  let acc0 ← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                              RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                  clever_033_unique.dedupe_at sorted_deref (0 : usize) acc0)
              = RustM.ok v := hres
    cases hh
  | some sort_res' =>
    cases sort_res' with
    | error e =>
      exfalso
      have hh : (do let sorted ← (some (Except.error e) :
                                    RustM (alloc.vec.Vec i64 alloc.alloc.Global));
                    let sorted_deref ← (core_models.ops.deref.Deref.deref
                      (alloc.vec.Vec i64 alloc.alloc.Global) sorted :
                      RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                    let acc0 ← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                                RustM (alloc.vec.Vec i64 alloc.alloc.Global))
                    clever_033_unique.dedupe_at sorted_deref (0 : usize) acc0)
                = RustM.ok v := hres
      cases hh
    | ok sorted =>
      have h_sort_ok : clever_033_unique.sort_at l (0 : usize)
                          ⟨(List.nil).toArray, by grind⟩ = RustM.ok sorted := h_sort
      simp only [RustM_ok_bind] at hres
      have h_deref :
          (core_models.ops.deref.Deref.deref
            (alloc.vec.Vec i64 alloc.alloc.Global) sorted : RustM _) = RustM.ok sorted := rfl
      rw [h_deref] at hres
      simp only [RustM_ok_bind] at hres
      -- hres : dedupe_at sorted 0 ⟨(List.nil).toArray, _⟩ = RustM.ok v
      -- Goal: ∃ i hi, l.val[i] = v.val[k]
      have h_v_k_has : arr_has v.val (v.val[k]'hk) := ⟨k, hk, rfl⟩
      -- dedupe_at_subset on (sorted, 0, ⟨#[], _⟩, v).
      have h_zero_toNat : (0 : usize).toNat = 0 := rfl
      have h_meas_dedupe : sorted.val.size - (0 : usize).toNat ≤ sorted.val.size := by
        rw [h_zero_toNat]; omega
      have h_le_dedupe : (0 : usize).toNat ≤ sorted.val.size := by rw [h_zero_toNat]; omega
      have h_dedupe_app :=
        dedupe_at_subset sorted sorted.val.size (0 : usize)
          ⟨(List.nil).toArray, by grind⟩ v h_meas_dedupe h_le_dedupe hres
          (v.val[k]'hk) h_v_k_has
      rcases h_dedupe_app with h_in_empty | h_in_sorted
      · exfalso
        obtain ⟨j, hj, _⟩ := h_in_empty
        have h_empty_size :
            ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
        rw [h_empty_size] at hj
        omega
      · -- v.val[k] is in sorted. Now apply sort_at_subset.
        have h_meas_sort : l.val.size - (0 : usize).toNat ≤ l.val.size := by
          rw [h_zero_toNat]; omega
        have h_le_sort : (0 : usize).toNat ≤ l.val.size := by rw [h_zero_toNat]; omega
        have h_sort_app :=
          sort_at_subset l l.val.size (0 : usize)
            ⟨(List.nil).toArray, by grind⟩ sorted h_meas_sort h_le_sort h_sort_ok
            (v.val[k]'hk) h_in_sorted
        rcases h_sort_app with h_in_empty | h_in_l
        · exfalso
          obtain ⟨j, hj, _⟩ := h_in_empty
          have h_empty_size :
              ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec i64 alloc.alloc.Global)).val.size = 0 := rfl
          rw [h_empty_size] at hj
          omega
        · obtain ⟨i, hi, h_eq⟩ := h_in_l
          exact ⟨i, hi, h_eq⟩

end Clever_033_uniqueObligations
