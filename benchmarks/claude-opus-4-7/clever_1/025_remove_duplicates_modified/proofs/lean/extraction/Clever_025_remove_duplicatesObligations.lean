-- Companion obligations file for the `clever_025_remove_duplicates` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_025_remove_duplicates

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_025_remove_duplicatesObligations

/-! ## Specification oracle: total count of an element in a slice.

`total_count numbers target k` is the number of indices `j < k` for which
`numbers.val[j] = target`. The `dite` on `j < numbers.val.size` keeps the
definition total — every theorem below applies it with `k ≤ numbers.val.size`,
so the bounded indices always exist. -/

private def total_count (numbers : RustSlice i64) (target : i64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      if h : k < numbers.val.size then
        (if (numbers.val[k]'h) = target then 1 else 0)
          + total_count numbers target k
      else
        total_count numbers target k

/-! ## Standard scaffolding (transferred from `clever_009_rolling_max`,
     `clever_021_rescale_to_unit`, `clever_003_below_zero`,
     `contains_u64`). -/

/-- `RustM.ok x >>= f = f x`. The library's `pure_bind` simp lemma only
    matches literal `Pure.pure`; this rewrite handles the `RustM.ok` form
    produced after reducing definitions. -/
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

private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide

private theorem i64_one_toInt : (1 : i64).toInt = 1 := by decide

/-! ## Push helper for `Vec` (`extend_from_slice` of a 1-element chunk). -/

private def push_one (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec i64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

/-! ## Step lemmas for `count_at`.

Three branches of the recursive body, packaged so subsequent induction can
rewrite directly. Pattern follows `contains_u64`'s `contains_at_*`. -/

/-- Out-of-bounds step: `count_at` returns the accumulator. -/
private theorem count_at_oob (numbers : RustSlice i64) (target : i64) (i : usize)
    (acc : i64) (hi : numbers.val.size ≤ i.toNat) :
    clever_025_remove_duplicates.count_at numbers target i acc = RustM.ok acc := by
  conv => lhs; unfold clever_025_remove_duplicates.count_at
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

/-- Match step: `numbers[i] = target`, no overflow → recurse with `acc + 1`. -/
private theorem count_at_step_match (numbers : RustSlice i64) (target : i64) (i : usize)
    (acc : i64) (hi : i.toNat < numbers.val.size)
    (heq : (numbers.val[i.toNat]'hi) = target)
    (hno : ¬ Int64.addOverflow acc (1 : i64)) :
    clever_025_remove_duplicates.count_at numbers target i acc =
      clever_025_remove_duplicates.count_at numbers target (i + 1) (acc + 1) := by
  conv => lhs; unfold clever_025_remove_duplicates.count_at
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
    rw [dif_pos hi]; rfl
  have h_beq : (numbers.val[i.toNat]'hi == target) = true := by
    rw [beq_iff_eq]; exact heq
  have h_no_overflow_i : i.toNat + 1 < 2^64 := by
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
  have h_no_bv_acc :
      BitVec.saddOverflow acc.toBitVec (1 : i64).toBitVec = false := by
    cases hb : BitVec.saddOverflow acc.toBitVec (1 : i64).toBitVec with
    | false => rfl
    | true => exact absurd hb hno
  have h_add_acc : (acc +? (1 : i64) : RustM i64) = RustM.ok (acc + 1) := by
    show (rust_primitives.ops.arith.Add.add acc (1 : i64) : RustM i64) = _
    show (if BitVec.saddOverflow acc.toBitVec (1 : i64).toBitVec
          then (.fail .integerOverflow : RustM i64)
          else pure (acc + 1)) = _
    rw [h_no_bv_acc]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.cmp.eq, h_beq, h_add_i, h_add_acc]

/-- Miss step: `numbers[i] ≠ target` → recurse with same `acc`. -/
private theorem count_at_step_miss (numbers : RustSlice i64) (target : i64) (i : usize)
    (acc : i64) (hi : i.toNat < numbers.val.size)
    (hne : (numbers.val[i.toNat]'hi) ≠ target) :
    clever_025_remove_duplicates.count_at numbers target i acc =
      clever_025_remove_duplicates.count_at numbers target (i + 1) acc := by
  conv => lhs; unfold clever_025_remove_duplicates.count_at
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
    rw [dif_pos hi]; rfl
  have h_beq : (numbers.val[i.toNat]'hi == target) = false := by
    rw [beq_eq_false_iff_ne]; exact hne
  have h_no_overflow_i : i.toNat + 1 < 2^64 := by
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
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.cmp.eq, h_beq,
             rust_primitives.ops.arith.Add.add, h_no_bv_i]

/-! ## Strong-induction lemma for `count_at`.

Captures: if `count_at numbers target i acc` succeeds with result `r`, then
`r.toInt = acc.toInt + (count of target in numbers[i, size))`. The proof
unfolds the function once per match/miss step; in the match step we discharge
the no-overflow precondition by inverting on the `RustM.ok r` hypothesis. -/

private theorem count_at_correct (numbers : RustSlice i64) (target : i64) :
    ∀ (m : Nat) (i : usize) (acc : i64) (r : i64),
      numbers.val.size - i.toNat ≤ m →
      i.toNat ≤ numbers.val.size →
      clever_025_remove_duplicates.count_at numbers target i acc = RustM.ok r →
      r.toInt = acc.toInt +
        ((total_count numbers target numbers.val.size : Int) -
          (total_count numbers target i.toNat : Int)) := by
  intro m
  induction m with
  | zero =>
    intro i acc r hm hi_le hres
    have hi_eq : i.toNat = numbers.val.size := by omega
    have hi_ge : numbers.val.size ≤ i.toNat := by omega
    rw [count_at_oob numbers target i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    rw [hi_eq]
    omega
  | succ m ih =>
    intro i acc r hm hi_le hres
    by_cases hi_ge : numbers.val.size ≤ i.toNat
    · have hi_eq : i.toNat = numbers.val.size := by omega
      rw [count_at_oob numbers target i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      rw [hi_eq]
      omega
    · have hi_lt : i.toNat < numbers.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : numbers.val.size < USize64.size := numbers.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ numbers.val.size := by rw [h_i1]; omega
      have h_m_le : numbers.val.size - (i + 1).toNat ≤ m := by rw [h_i1]; omega
      -- Nat-level total_count successor equation (the Int form is bridged
      -- via `omega` at the use site, which can fold `Nat → Int` coercions).
      have h_tot_succ_nat :
          total_count numbers target (i.toNat + 1) =
            (if (numbers.val[i.toNat]'hi_lt) = target then 1 else 0)
              + total_count numbers target i.toNat := by
        show (if h : i.toNat < numbers.val.size then
                 (if (numbers.val[i.toNat]'h) = target then 1 else 0)
                   + total_count numbers target i.toNat
               else total_count numbers target i.toNat) = _
        rw [dif_pos hi_lt]
      by_cases heq : (numbers.val[i.toNat]'hi_lt) = target
      · -- Match branch.
        by_cases hov : Int64.addOverflow acc (1 : i64)
        · -- If acc+1 overflows, count_at fails — contradiction with hres.
          exfalso
          conv at hres => lhs; unfold clever_025_remove_duplicates.count_at
          have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
            USize64.toNat_ofNat_of_lt' h_size_lt
          have h_cond_outer : decide (USize64.ofNat numbers.val.size ≤ i) = false := by
            rw [decide_eq_false_iff_not]
            intro hle
            rw [USize64.le_iff_toNat_le, h_ofNat] at hle
            omega
          have h_idx : (numbers[i]_? : RustM i64) = RustM.ok (numbers.val[i.toNat]'hi_lt) := by
            show (if h : i.toNat < numbers.val.size then pure (numbers.val[i])
                    else .fail .arrayOutOfBounds)
                = RustM.ok (numbers.val[i.toNat]'hi_lt)
            rw [dif_pos hi_lt]; rfl
          have h_beq : (numbers.val[i.toNat]'hi_lt == target) = true := by
            rw [beq_iff_eq]; exact heq
          have h_bv_true : BitVec.saddOverflow acc.toBitVec (1 : i64).toBitVec = true := hov
          have h_add_fail :
              (acc +? (1 : i64) : RustM i64) = RustM.fail Error.integerOverflow := by
            show (rust_primitives.ops.arith.Add.add acc (1 : i64) : RustM i64) = _
            show (if BitVec.saddOverflow acc.toBitVec (1 : i64).toBitVec
                  then (.fail .integerOverflow : RustM i64)
                  else pure (acc + 1)) = _
            rw [h_bv_true]; rfl
          have h_add_i : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
            show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
            show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
                  then (.fail .integerOverflow : RustM usize)
                  else pure (i + 1)) = _
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
            rw [h_no_bv_i]; rfl
          simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
                     rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
                     h_cond_outer, Bool.false_eq_true, ↓reduceIte,
                     h_idx,
                     rust_primitives.cmp.eq, h_beq, h_add_i, h_add_fail] at hres
          simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, Option.bind] at hres
          cases hres
        · have h_step := count_at_step_match numbers target i acc hi_lt heq hov
          rw [h_step] at hres
          have h_acc1 : (acc + 1).toInt = acc.toInt + 1 := by
            have h := Int64.toInt_add_of_not_addOverflow hov
            rw [h, i64_one_toInt]
          have ih_app := ih (i + 1) (acc + 1) r h_m_le h_i1_le hres
          rw [ih_app, h_acc1, h_i1]
          have h_tot_match :
              total_count numbers target (i.toNat + 1) =
                1 + total_count numbers target i.toNat := by
            rw [h_tot_succ_nat, if_pos heq]
          omega
      · -- Miss branch.
        have h_step := count_at_step_miss numbers target i acc hi_lt heq
        rw [h_step] at hres
        have ih_app := ih (i + 1) acc r h_m_le h_i1_le hres
        rw [ih_app, h_i1]
        have h_tot_miss :
            total_count numbers target (i.toNat + 1) =
              total_count numbers target i.toNat := by
          rw [h_tot_succ_nat, if_neg heq]; omega
        omega

/-- Corollary: at `i = 0, acc = 0`, the result equals the total count. -/
private theorem count_at_zero (numbers : RustSlice i64) (target : i64) (r : i64)
    (hres : clever_025_remove_duplicates.count_at numbers target (0 : usize) (0 : i64)
              = RustM.ok r) :
    r.toInt = (total_count numbers target numbers.val.size : Int) := by
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h := count_at_correct numbers target numbers.val.size (0 : usize) (0 : i64) r
    (by rw [h_zero_toNat]; omega)
    (by rw [h_zero_toNat]; omega)
    hres
  rw [h_zero_toNat] at h
  rw [h, i64_zero_toInt]
  show (0 : Int) + ((total_count numbers target numbers.val.size : Int) -
    (total_count numbers target 0 : Int)) = _
  show (0 : Int) + ((total_count numbers target numbers.val.size : Int) - 0) = _
  omega

/-! ## Step lemmas for `build_at`.

Three branches: out-of-bounds, extend (count == 1), skip (count ≠ 1). The
`extend`/`skip` lemmas take the inner `count_at` result as a parameter so
they can be used after `count_at_correct` has identified the count value. -/

/-- Out-of-bounds step. -/
private theorem build_at_oob (numbers : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : numbers.val.size ≤ i.toNat) :
    clever_025_remove_duplicates.build_at numbers i acc = RustM.ok acc := by
  conv => lhs; unfold clever_025_remove_duplicates.build_at
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

/-- Extend step: in-bounds, `count_at = 1` → append and recurse. -/
private theorem build_at_step_extend (numbers : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < numbers.val.size)
    (c : i64)
    (hcount : clever_025_remove_duplicates.count_at numbers (numbers.val[i.toNat]'hi)
                (0 : usize) (0 : i64) = RustM.ok c)
    (hc_eq : c = (1 : i64))
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_025_remove_duplicates.build_at numbers i acc =
      clever_025_remove_duplicates.build_at numbers (i + 1)
        (push_one acc (numbers.val[i.toNat]'hi) h_acc) := by
  conv => lhs; unfold clever_025_remove_duplicates.build_at
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
    rw [dif_pos hi]; rfl
  have h_beq : (c == (1 : i64)) = true := by
    rw [beq_iff_eq]; exact hc_eq
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
             h_idx, hcount,
             rust_primitives.cmp.eq, h_beq]
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
  rw [h_add_i]
  rfl

/-- Skip step: in-bounds, `count_at = c ≠ 1` → recurse without appending. -/
private theorem build_at_step_skip (numbers : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < numbers.val.size)
    (c : i64)
    (hcount : clever_025_remove_duplicates.count_at numbers (numbers.val[i.toNat]'hi)
                (0 : usize) (0 : i64) = RustM.ok c)
    (hc_ne : c ≠ (1 : i64)) :
    clever_025_remove_duplicates.build_at numbers i acc =
      clever_025_remove_duplicates.build_at numbers (i + 1) acc := by
  conv => lhs; unfold clever_025_remove_duplicates.build_at
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
    rw [dif_pos hi]; rfl
  have h_beq : (c == (1 : i64)) = false := by
    rw [beq_eq_false_iff_ne]; exact hc_ne
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
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, hcount,
             rust_primitives.cmp.eq, h_beq,
             rust_primitives.ops.arith.Add.add, h_no_bv_i]

/-! ## Spec for which input indices survive into the output.

`build_indices numbers k` is the list of indices `j < k` for which
`total_count numbers numbers[j] numbers.val.size = 1`. By construction the
list is strictly increasing (appended at the right) and within range. The
output of `build_at numbers 0 []` corresponds element-wise to this list
indexed back into `numbers`. -/

private def build_indices (numbers : RustSlice i64) : Nat → List Nat
  | 0     => []
  | k + 1 =>
      if h : k < numbers.val.size then
        if total_count numbers (numbers.val[k]'h) numbers.val.size = 1 then
          build_indices numbers k ++ [k]
        else
          build_indices numbers k
      else
        build_indices numbers k

/-- All elements of `build_indices numbers k` are `< k`. -/
private theorem build_indices_lt (numbers : RustSlice i64) :
    ∀ (k : Nat) (j : Nat), j ∈ build_indices numbers k → j < k := by
  intro k
  induction k with
  | zero =>
    intro j hj
    simp [build_indices] at hj
  | succ k ih =>
    intro j hj
    show j < k + 1
    by_cases hk : k < numbers.val.size
    · by_cases hcnt : total_count numbers (numbers.val[k]'hk) numbers.val.size = 1
      · have hbody :
            build_indices numbers (k + 1) = build_indices numbers k ++ [k] := by
          show (if h : k < numbers.val.size then
                 (if total_count numbers (numbers.val[k]'h) numbers.val.size = 1 then
                    build_indices numbers k ++ [k]
                  else build_indices numbers k)
               else build_indices numbers k) = _
          rw [dif_pos hk, if_pos hcnt]
        rw [hbody] at hj
        rw [List.mem_append] at hj
        rcases hj with hj_l | hj_r
        · have := ih j hj_l; omega
        · simp at hj_r; omega
      · have hbody :
            build_indices numbers (k + 1) = build_indices numbers k := by
          show (if h : k < numbers.val.size then
                 (if total_count numbers (numbers.val[k]'h) numbers.val.size = 1 then
                    build_indices numbers k ++ [k]
                  else build_indices numbers k)
               else build_indices numbers k) = _
          rw [dif_pos hk, if_neg hcnt]
        rw [hbody] at hj
        have := ih j hj; omega
    · have hbody :
          build_indices numbers (k + 1) = build_indices numbers k := by
        show (if h : k < numbers.val.size then _ else build_indices numbers k) = _
        rw [dif_neg hk]
      rw [hbody] at hj
      have := ih j hj; omega

/-- Membership characterisation: `i ∈ build_indices numbers k` iff `i < k` and
    `numbers[i]` has total count `= 1`. -/
private theorem build_indices_mem (numbers : RustSlice i64) :
    ∀ (k : Nat) (i : Nat),
      i ∈ build_indices numbers k ↔
      (∃ (hi : i < numbers.val.size), i < k ∧
        total_count numbers (numbers.val[i]'hi) numbers.val.size = 1) := by
  intro k
  induction k with
  | zero =>
    intro i
    constructor
    · intro h; simp [build_indices] at h
    · rintro ⟨_, hlt, _⟩; omega
  | succ k ih =>
    intro i
    by_cases hk : k < numbers.val.size
    · by_cases hcnt : total_count numbers (numbers.val[k]'hk) numbers.val.size = 1
      · have hbody :
            build_indices numbers (k + 1) = build_indices numbers k ++ [k] := by
          show (if h : k < numbers.val.size then
                 (if total_count numbers (numbers.val[k]'h) numbers.val.size = 1 then
                    build_indices numbers k ++ [k]
                  else build_indices numbers k)
               else build_indices numbers k) = _
          rw [dif_pos hk, if_pos hcnt]
        rw [hbody]
        constructor
        · intro h
          rw [List.mem_append] at h
          rcases h with h_l | h_r
          · obtain ⟨hi, hlt, hcc⟩ := (ih i).mp h_l
            exact ⟨hi, by omega, hcc⟩
          · simp at h_r
            subst h_r
            exact ⟨hk, by omega, hcnt⟩
        · rintro ⟨hi, hlt, hcc⟩
          rw [List.mem_append]
          by_cases h_eq : i = k
          · subst h_eq; right; simp
          · left; exact (ih i).mpr ⟨hi, by omega, hcc⟩
      · have hbody :
            build_indices numbers (k + 1) = build_indices numbers k := by
          show (if h : k < numbers.val.size then
                 (if total_count numbers (numbers.val[k]'h) numbers.val.size = 1 then
                    build_indices numbers k ++ [k]
                  else build_indices numbers k)
               else build_indices numbers k) = _
          rw [dif_pos hk, if_neg hcnt]
        rw [hbody]
        constructor
        · intro h
          obtain ⟨hi, hlt, hcc⟩ := (ih i).mp h
          exact ⟨hi, by omega, hcc⟩
        · rintro ⟨hi, hlt, hcc⟩
          by_cases h_eq : i = k
          · -- contradiction: hcnt says numbers[k] has count ≠ 1
            exfalso
            apply hcnt
            have h_ix_eq : numbers.val[k]'hk = numbers.val[i]'hi :=
              getElem_congr_idx h_eq.symm
            rw [h_ix_eq]; exact hcc
          · exact (ih i).mpr ⟨hi, by omega, hcc⟩
    · have hbody :
          build_indices numbers (k + 1) = build_indices numbers k := by
        show (if h : k < numbers.val.size then _ else build_indices numbers k) = _
        rw [dif_neg hk]
      rw [hbody]
      constructor
      · intro h
        obtain ⟨hi, hlt, hcc⟩ := (ih i).mp h
        exact ⟨hi, by omega, hcc⟩
      · rintro ⟨hi, hlt, hcc⟩
        have h_lt_k : i < k := by
          rcases Nat.lt_or_ge i k with h | h
          · exact h
          · omega
        exact (ih i).mpr ⟨hi, h_lt_k, hcc⟩

/-! ## Structural sub-lemmas the aux delegates to.

The full structural invariant of `build_at` decomposes into two pieces.
The first (strict monotonicity of the spec list) is closed below using
`List.pairwise_iff_getElem` from the Lean stdlib; the second (the deep
strong-induction lemma over `build_at` mirroring `shift_at_correct` from
`clever_021_rescale_to_unit`) is closed via `build_at_correct_strong`
further down. The aux lemma after them combines these (plus
`build_indices_mem`, which is already closed above) to derive the
three-conjunct contract used by the top-level obligations. -/

/-- The spec list `build_indices numbers k` is sorted strictly increasing. -/
private theorem build_indices_pairwise (numbers : RustSlice i64) :
    ∀ k : Nat, (build_indices numbers k).Pairwise (· < ·) := by
  intro k
  induction k with
  | zero =>
    show ([] : List Nat).Pairwise (· < ·)
    exact List.Pairwise.nil
  | succ k ih =>
    by_cases hk : k < numbers.val.size
    · by_cases hcnt : total_count numbers (numbers.val[k]'hk) numbers.val.size = 1
      · have hbody :
            build_indices numbers (k + 1) = build_indices numbers k ++ [k] := by
          show (if h : k < numbers.val.size then
                 (if total_count numbers (numbers.val[k]'h) numbers.val.size = 1 then
                    build_indices numbers k ++ [k]
                  else build_indices numbers k)
               else build_indices numbers k) = _
          rw [dif_pos hk, if_pos hcnt]
        rw [hbody, List.pairwise_append]
        refine ⟨ih, List.pairwise_singleton _ _, ?_⟩
        intro x hx y hy
        simp at hy
        -- hy : y = k. Rewrite the goal `x < y` to `x < k`, then apply.
        rw [hy]
        exact build_indices_lt numbers k x hx
      · have hbody :
            build_indices numbers (k + 1) = build_indices numbers k := by
          show (if h : k < numbers.val.size then
                 (if total_count numbers (numbers.val[k]'h) numbers.val.size = 1 then
                    build_indices numbers k ++ [k]
                  else build_indices numbers k)
               else build_indices numbers k) = _
          rw [dif_pos hk, if_neg hcnt]
        rw [hbody]; exact ih
    · have hbody :
          build_indices numbers (k + 1) = build_indices numbers k := by
        show (if h : k < numbers.val.size then _ else build_indices numbers k) = _
        rw [dif_neg hk]
      rw [hbody]; exact ih

/-- Strict monotonicity of `build_indices`, in the `getD`-with-default form
    that `build_at_correct_aux` consumes. Closed via `build_indices_pairwise`
    + `List.pairwise_iff_getElem` + the `getD ↔ []` bridge. -/
private theorem build_indices_strict_mono (numbers : RustSlice i64) (k : Nat) :
    ∀ j₁ j₂ : Nat, j₁ < j₂ → j₂ < (build_indices numbers k).length →
      (build_indices numbers k).getD j₁ 0 < (build_indices numbers k).getD j₂ 0 := by
  intro j₁ j₂ hlt hj₂
  have hj₁ : j₁ < (build_indices numbers k).length := by omega
  have h_pw := build_indices_pairwise numbers k
  have h_get_lt :
      (build_indices numbers k)[j₁]'hj₁ < (build_indices numbers k)[j₂]'hj₂ :=
    List.pairwise_iff_getElem.mp h_pw j₁ j₂ hj₁ hj₂ hlt
  rw [show (build_indices numbers k).getD j₁ 0 = (build_indices numbers k)[j₁]'hj₁ from
        (List.getElem_eq_getD (l := build_indices numbers k) (i := j₁)
                              (h := hj₁) 0).symm]
  rw [show (build_indices numbers k).getD j₂ 0 = (build_indices numbers k)[j₂]'hj₂ from
        (List.getElem_eq_getD (l := build_indices numbers k) (i := j₂)
                              (h := hj₂) 0).symm]
  exact h_get_lt

/-! ## Helpers for the strong induction over `build_at`. -/

/-- Injectivity of `Int64.toInt`. Follows from `Int64.ofInt_toInt`
    (provided by the Hax prelude's `additional_int_lemmas` macro). -/
private theorem i64_eq_of_toInt_eq {a b : i64} (h : a.toInt = b.toInt) : a = b := by
  have ha : (Int64.ofInt a.toInt : i64) = a := Int64.ofInt_toInt a
  have hb : (Int64.ofInt b.toInt : i64) = b := Int64.ofInt_toInt b
  rw [← ha, ← hb, h]

/-- `build_indices numbers k` has length at most `k`: by construction it is
    a strict subsequence of `[0, …, k)`. -/
private theorem build_indices_length_le (numbers : RustSlice i64) :
    ∀ k : Nat, (build_indices numbers k).length ≤ k := by
  intro k
  induction k with
  | zero =>
    show ([] : List Nat).length ≤ 0
    simp
  | succ k ih =>
    by_cases hk : k < numbers.val.size
    · by_cases hcnt : total_count numbers (numbers.val[k]'hk) numbers.val.size = 1
      · have hbody :
            build_indices numbers (k + 1) = build_indices numbers k ++ [k] := by
          show (if h : k < numbers.val.size then
                  (if total_count numbers (numbers.val[k]'h) numbers.val.size = 1 then
                     build_indices numbers k ++ [k]
                   else build_indices numbers k)
                else build_indices numbers k) = _
          rw [dif_pos hk, if_pos hcnt]
        rw [hbody, List.length_append]
        show (build_indices numbers k).length + [k].length ≤ k + 1
        have : [k].length = 1 := rfl
        omega
      · have hbody :
            build_indices numbers (k + 1) = build_indices numbers k := by
          show (if h : k < numbers.val.size then _ else build_indices numbers k) = _
          rw [dif_pos hk, if_neg hcnt]
        rw [hbody]; omega
    · have hbody :
          build_indices numbers (k + 1) = build_indices numbers k := by
        show (if h : k < numbers.val.size then _ else build_indices numbers k) = _
        rw [dif_neg hk]
      rw [hbody]; omega

/-- `(L ++ M).getD k d = L.getD k d` when `k < L.length`. -/
private theorem list_getD_append_left {α} (L M : List α) (k : Nat) (d : α)
    (h : k < L.length) : (L ++ M).getD k d = L.getD k d := by
  have h_lt_app : k < (L ++ M).length := by
    rw [List.length_append]; omega
  rw [(List.getElem_eq_getD (l := L ++ M) (i := k) (h := h_lt_app) d).symm]
  rw [(List.getElem_eq_getD (l := L) (i := k) (h := h) d).symm]
  exact List.getElem_append_left h

/-- `(L ++ [x]).getD L.length d = x`. -/
private theorem list_getD_append_singleton_at_len {α} (L : List α) (x d : α) :
    (L ++ [x]).getD L.length d = x := by
  have h_lt : L.length < (L ++ [x]).length := by
    rw [List.length_append]
    show L.length < L.length + [x].length
    have : [x].length = 1 := rfl
    omega
  rw [(List.getElem_eq_getD (l := L ++ [x]) (i := L.length) (h := h_lt) d).symm]
  rw [List.getElem_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self]
  rfl

/-- `count_at fail` propagates: if the inner `count_at` fails with `e`,
    then `build_at` at this position also fails with `e`. -/
private theorem build_at_step_count_fail (numbers : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < numbers.val.size)
    (e : Error)
    (hcount : clever_025_remove_duplicates.count_at numbers (numbers.val[i.toNat]'hi)
                (0 : usize) (0 : i64) = RustM.fail e) :
    clever_025_remove_duplicates.build_at numbers i acc = RustM.fail e := by
  conv => lhs; unfold clever_025_remove_duplicates.build_at
  have h_size_lt : numbers.val.size < USize64.size := numbers.size_lt_usizeSize
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
    rw [dif_pos hi]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, hcount]
  rfl

/-- `count_at div` propagates: if the inner `count_at` diverges, so does
    `build_at` at this position. -/
private theorem build_at_step_count_div (numbers : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < numbers.val.size)
    (hcount : clever_025_remove_duplicates.count_at numbers (numbers.val[i.toNat]'hi)
                (0 : usize) (0 : i64) = RustM.div) :
    clever_025_remove_duplicates.build_at numbers i acc = RustM.div := by
  conv => lhs; unfold clever_025_remove_duplicates.build_at
  have h_size_lt : numbers.val.size < USize64.size := numbers.size_lt_usizeSize
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
    rw [dif_pos hi]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, hcount]
  rfl

/-- Helper to close the "i.toNat = numbers.val.size" out-of-bounds case
    without running into rewrite motive issues. Uses `simp only [← h_getD_eq]`
    to rewrite the goal's index expression back to the `i.toNat` form that
    matches the inductive hypothesis. -/
private theorem build_at_oob_finish (numbers : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi_eq : i.toNat = numbers.val.size)
    (h_acc_size : acc.val.size = (build_indices numbers i.toNat).length)
    (h_acc_inv :
        ∀ (k : Nat) (hk : k < acc.val.size),
          ∃ (hbi : (build_indices numbers i.toNat).getD k 0 < numbers.val.size),
              acc.val[k]'hk = numbers.val[(build_indices numbers i.toNat).getD k 0]'hbi) :
    acc.val.size = (build_indices numbers numbers.val.size).length ∧
    (∀ (k : Nat) (hk : k < acc.val.size),
        ∃ (hbi : (build_indices numbers numbers.val.size).getD k 0 < numbers.val.size),
            acc.val[k]'hk = numbers.val[(build_indices numbers numbers.val.size).getD k 0]'hbi) := by
  have h_bi_eq : build_indices numbers i.toNat = build_indices numbers numbers.val.size := by
    rw [hi_eq]
  have h_getD_eq : ∀ k : Nat,
      (build_indices numbers i.toNat).getD k 0 =
        (build_indices numbers numbers.val.size).getD k 0 := by
    intro k; rw [h_bi_eq]
  refine ⟨?_, ?_⟩
  · rw [h_acc_size, h_bi_eq]
  · intro k hk
    obtain ⟨hbi, hacc_eq⟩ := h_acc_inv k hk
    have hbi' : (build_indices numbers numbers.val.size).getD k 0 < numbers.val.size := by
      rw [← h_getD_eq k]; exact hbi
    refine ⟨hbi', ?_⟩
    -- Goal: acc.val[k]'hk = numbers.val[(build_indices size).getD k 0]'hbi'
    -- Rewrite RHS index back to `(build_indices i.toNat).getD k 0`.
    have h_rewrite :
        numbers.val[(build_indices numbers numbers.val.size).getD k 0]'hbi' =
          numbers.val[(build_indices numbers i.toNat).getD k 0]'hbi := by
      congr 1
      exact (h_getD_eq k).symm
    rw [h_rewrite]
    exact hacc_eq

/-- Strong induction over `build_at`. Mirrors `shift_at_correct` from
    `clever_021_rescale_to_unit`: at any starting `(i, acc)` where the
    accumulator's contents agree with `build_indices numbers i.toNat`
    (the indices into `numbers` that have been kept so far), the final
    `RustM.ok` result agrees with `build_indices numbers numbers.val.size`.

    The recursive case dispatches on the inner `count_at` result:
    `count_at = ok 1` → extend step + `build_indices` grows by `[i.toNat]`;
    `count_at = ok c` with `c ≠ 1` → skip step + `build_indices` unchanged;
    `count_at = fail` or `div` → contradicts `hres = RustM.ok v` via the
    fail/div propagation lemmas. -/
private theorem build_at_correct_strong (numbers : RustSlice i64) :
    ∀ (n : Nat) (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (v : alloc.vec.Vec i64 alloc.alloc.Global),
      numbers.val.size - i.toNat ≤ n →
      i.toNat ≤ numbers.val.size →
      acc.val.size = (build_indices numbers i.toNat).length →
      (∀ (k : Nat) (hk : k < acc.val.size),
          ∃ (hbi : (build_indices numbers i.toNat).getD k 0 < numbers.val.size),
              acc.val[k]'hk = numbers.val[(build_indices numbers i.toNat).getD k 0]'hbi) →
      clever_025_remove_duplicates.build_at numbers i acc = RustM.ok v →
      v.val.size = (build_indices numbers numbers.val.size).length ∧
      (∀ (k : Nat) (hk : k < v.val.size),
          ∃ (hbi : (build_indices numbers numbers.val.size).getD k 0 < numbers.val.size),
              v.val[k]'hk = numbers.val[(build_indices numbers numbers.val.size).getD k 0]'hbi) := by
  intro n
  induction n with
  | zero =>
    intro i acc v hm hi_le h_acc_size h_acc_inv hres
    have hi_eq : i.toNat = numbers.val.size := by omega
    have hi_ge : numbers.val.size ≤ i.toNat := by omega
    rw [build_at_oob numbers i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    exact build_at_oob_finish numbers i acc hi_eq h_acc_size h_acc_inv
  | succ n ih =>
    intro i acc v hm hi_le h_acc_size h_acc_inv hres
    by_cases hi_ge : numbers.val.size ≤ i.toNat
    · have hi_eq : i.toNat = numbers.val.size := by omega
      rw [build_at_oob numbers i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      exact build_at_oob_finish numbers i acc hi_eq h_acc_size h_acc_inv
    · have hi_lt : i.toNat < numbers.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : numbers.val.size < USize64.size := numbers.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_acc_le_i : acc.val.size ≤ i.toNat := by
        rw [h_acc_size]; exact build_indices_length_le numbers i.toNat
      have h_acc_succ : acc.val.size + 1 < USize64.size := by
        rw [h_usize_size]; omega
      have h_i1_le : (i + 1).toNat ≤ numbers.val.size := by rw [h_i1]; omega
      have h_meas : numbers.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      -- Generalize and case on the count_at result. The fail / div branches
      -- contradict `hres = RustM.ok v` via the propagation lemmas above.
      generalize h_count_def :
        clever_025_remove_duplicates.count_at numbers (numbers.val[i.toNat]'hi_lt)
          (0 : usize) (0 : i64) = rcount
      cases rcount with
      | none =>
        exfalso
        have h_count : clever_025_remove_duplicates.count_at numbers (numbers.val[i.toNat]'hi_lt)
            (0 : usize) (0 : i64) = RustM.div := h_count_def
        rw [build_at_step_count_div numbers i acc hi_lt h_count] at hres
        cases hres
      | some res =>
        cases res with
        | error e =>
          exfalso
          have h_count : clever_025_remove_duplicates.count_at numbers (numbers.val[i.toNat]'hi_lt)
              (0 : usize) (0 : i64) = RustM.fail e := h_count_def
          rw [build_at_step_count_fail numbers i acc hi_lt e h_count] at hres
          cases hres
        | ok c =>
          have h_count : clever_025_remove_duplicates.count_at numbers (numbers.val[i.toNat]'hi_lt)
              (0 : usize) (0 : i64) = RustM.ok c := h_count_def
          have h_c_int := count_at_zero numbers (numbers.val[i.toNat]'hi_lt) c h_count
          by_cases hc1 : c = (1 : i64)
          · -- Extend branch: count = 1, build_indices grows by [i.toNat].
            rw [build_at_step_extend numbers i acc hi_lt c h_count hc1 h_acc_succ] at hres
            have h_tc_eq_1 :
                total_count numbers (numbers.val[i.toNat]'hi_lt) numbers.val.size = 1 := by
              have hc1_int : c.toInt = 1 := by rw [hc1]; exact i64_one_toInt
              rw [hc1_int] at h_c_int
              omega
            have h_bi_succ_extend :
                build_indices numbers (i.toNat + 1) =
                  build_indices numbers i.toNat ++ [i.toNat] := by
              show (if h : i.toNat < numbers.val.size then
                      (if total_count numbers (numbers.val[i.toNat]'h) numbers.val.size = 1 then
                         build_indices numbers i.toNat ++ [i.toNat]
                       else build_indices numbers i.toNat)
                    else build_indices numbers i.toNat) = _
              rw [dif_pos hi_lt, if_pos h_tc_eq_1]
            have h_acc'_size :
                (push_one acc (numbers.val[i.toNat]'hi_lt) h_acc_succ).val.size =
                  (build_indices numbers (i + 1).toNat).length := by
              show (acc.val ++ #[numbers.val[i.toNat]'hi_lt]).size =
                (build_indices numbers (i + 1).toNat).length
              rw [Array.size_append, h_i1, h_bi_succ_extend, List.length_append]
              show acc.val.size + 1 = (build_indices numbers i.toNat).length + [i.toNat].length
              rw [h_acc_size]; rfl
            have h_acc'_inv :
                ∀ (k : Nat)
                  (hk : k < (push_one acc (numbers.val[i.toNat]'hi_lt) h_acc_succ).val.size),
                  ∃ (hbi : (build_indices numbers (i + 1).toNat).getD k 0 < numbers.val.size),
                    (push_one acc (numbers.val[i.toNat]'hi_lt) h_acc_succ).val[k]'hk =
                      numbers.val[(build_indices numbers (i + 1).toNat).getD k 0]'hbi := by
              intro k hk
              have h_bi_i1_eq :
                  build_indices numbers (i + 1).toNat =
                    build_indices numbers i.toNat ++ [i.toNat] := by
                rw [h_i1]; exact h_bi_succ_extend
              -- The push_one.val is acc.val ++ #[numbers.val[i.toNat]'hi_lt]
              show ∃ (hbi : (build_indices numbers (i + 1).toNat).getD k 0 < numbers.val.size),
                    ((acc.val ++ #[numbers.val[i.toNat]'hi_lt])[k]'hk) =
                      numbers.val[(build_indices numbers (i + 1).toNat).getD k 0]'hbi
              by_cases hk_lt : k < acc.val.size
              · -- Original-acc range.
                have hk_lt_bi : k < (build_indices numbers i.toNat).length := by
                  rw [← h_acc_size]; exact hk_lt
                -- (L ++ [x]).getD k 0 = L.getD k 0 for k < L.length.
                have h_getD_eq :
                    (build_indices numbers (i + 1).toNat).getD k 0 =
                      (build_indices numbers i.toNat).getD k 0 := by
                  rw [h_bi_i1_eq]
                  exact list_getD_append_left _ _ k 0 hk_lt_bi
                obtain ⟨hbi, hacc_eq⟩ := h_acc_inv k hk_lt
                have hbi' : (build_indices numbers (i + 1).toNat).getD k 0 < numbers.val.size := by
                  rw [h_getD_eq]; exact hbi
                refine ⟨hbi', ?_⟩
                rw [Array.getElem_append_left hk_lt]
                -- Goal: acc.val[k]'hk_lt = numbers.val[(build_indices_(i+1)).getD k 0]'hbi'
                have h_rhs_eq :
                    numbers.val[(build_indices numbers (i + 1).toNat).getD k 0]'hbi' =
                      numbers.val[(build_indices numbers i.toNat).getD k 0]'hbi := by
                  simp only [h_getD_eq]
                rw [h_rhs_eq]
                exact hacc_eq
              · -- New extension: k = acc.val.size.
                have h_size_raw :
                    (acc.val ++ #[numbers.val[i.toNat]'hi_lt]).size = acc.val.size + 1 := by
                  rw [Array.size_append]; rfl
                have hk_eq_acc : k = acc.val.size := by
                  have : k < acc.val.size + 1 := by rw [← h_size_raw]; exact hk
                  omega
                -- (L ++ [x]).getD L.length 0 = x.
                have h_getD_eq :
                    (build_indices numbers (i + 1).toNat).getD k 0 = i.toNat := by
                  rw [h_bi_i1_eq, hk_eq_acc, h_acc_size]
                  exact list_getD_append_singleton_at_len _ _ 0
                have hbi' : (build_indices numbers (i + 1).toNat).getD k 0 < numbers.val.size := by
                  rw [h_getD_eq]; exact hi_lt
                refine ⟨hbi', ?_⟩
                -- Goal: (acc.val ++ #[..])[k]'hk = numbers.val[(build_indices_(i+1)).getD k 0]'hbi'
                -- Step 1: rewrite the RHS index using h_getD_eq to numbers.val[i.toNat]'hi_lt.
                have h_rhs_eq :
                    numbers.val[(build_indices numbers (i + 1).toNat).getD k 0]'hbi' =
                      numbers.val[i.toNat]'hi_lt := by
                  simp only [h_getD_eq]
                rw [h_rhs_eq]
                -- Step 2: show (acc.val ++ #[x])[k]'hk = x.
                -- Subst k = acc.val.size to clear the index.
                subst hk_eq_acc
                rw [Array.getElem_append_right (Nat.le_refl _)]
                simp only [Nat.sub_self]
                rfl
            exact ih (i + 1) _ v h_meas h_i1_le h_acc'_size h_acc'_inv hres
          · -- Skip branch: count ≠ 1, build_indices unchanged.
            rw [build_at_step_skip numbers i acc hi_lt c h_count hc1] at hres
            have h_tc_ne_1 :
                total_count numbers (numbers.val[i.toNat]'hi_lt) numbers.val.size ≠ 1 := by
              intro h_eq
              apply hc1
              apply i64_eq_of_toInt_eq
              rw [h_c_int, h_eq, i64_one_toInt]
              rfl
            have h_bi_succ_skip :
                build_indices numbers (i.toNat + 1) = build_indices numbers i.toNat := by
              show (if h : i.toNat < numbers.val.size then
                      (if total_count numbers (numbers.val[i.toNat]'h) numbers.val.size = 1 then
                         build_indices numbers i.toNat ++ [i.toNat]
                       else build_indices numbers i.toNat)
                    else build_indices numbers i.toNat) = _
              rw [dif_pos hi_lt, if_neg h_tc_ne_1]
            have h_bi_i1_eq :
                build_indices numbers (i + 1).toNat = build_indices numbers i.toNat := by
              rw [h_i1]; exact h_bi_succ_skip
            have h_acc'_size :
                acc.val.size = (build_indices numbers (i + 1).toNat).length := by
              rw [h_bi_i1_eq]; exact h_acc_size
            have h_acc'_inv :
                ∀ (k : Nat) (hk : k < acc.val.size),
                  ∃ (hbi : (build_indices numbers (i + 1).toNat).getD k 0 < numbers.val.size),
                    acc.val[k]'hk =
                      numbers.val[(build_indices numbers (i + 1).toNat).getD k 0]'hbi := by
              intro k hk
              obtain ⟨hbi, hacc_eq⟩ := h_acc_inv k hk
              have h_getD_eq :
                  (build_indices numbers (i + 1).toNat).getD k 0 =
                    (build_indices numbers i.toNat).getD k 0 := by
                rw [h_bi_i1_eq]
              have hbi' :
                  (build_indices numbers (i + 1).toNat).getD k 0 < numbers.val.size := by
                rw [h_getD_eq]; exact hbi
              refine ⟨hbi', ?_⟩
              have h_rhs_eq :
                  numbers.val[(build_indices numbers (i + 1).toNat).getD k 0]'hbi' =
                    numbers.val[(build_indices numbers i.toNat).getD k 0]'hbi := by
                simp only [h_getD_eq]
              rw [h_rhs_eq]
              exact hacc_eq
            exact ih (i + 1) acc v h_meas h_i1_le h_acc'_size h_acc'_inv hres

/-- The output of `build_at numbers 0 []` agrees, element-wise, with
    `build_indices numbers numbers.val.size` indexed back into `numbers`.
    Specialises `build_at_correct_strong` to the initial state `i = 0,
    acc = #[]`. -/
private theorem build_at_size_correspondence (numbers : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_025_remove_duplicates.remove_duplicates numbers = RustM.ok v) :
    v.val.size = (build_indices numbers numbers.val.size).length ∧
    (∀ (k : Nat) (hk : k < v.val.size)
       (hk' : k < (build_indices numbers numbers.val.size).length),
       ∃ (hi : (build_indices numbers numbers.val.size).getD k 0 < numbers.val.size),
         v.val[k]'hk =
           numbers.val[(build_indices numbers numbers.val.size).getD k 0]'hi) := by
  unfold clever_025_remove_duplicates.remove_duplicates at hres
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new, RustM_ok_bind] at hres
  let acc0 : alloc.vec.Vec i64 alloc.alloc.Global := ⟨(List.nil).toArray, by grind⟩
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_acc0_size :
      acc0.val.size = (build_indices numbers (0 : usize).toNat).length := by
    show (List.nil : List i64).toArray.size = (build_indices numbers (0 : usize).toNat).length
    rw [h_zero_toNat]
    show 0 = ([] : List Nat).length
    rfl
  have h_acc0_inv :
      ∀ (k : Nat) (hk : k < acc0.val.size),
        ∃ (hbi : (build_indices numbers (0 : usize).toNat).getD k 0 < numbers.val.size),
          acc0.val[k]'hk =
            numbers.val[(build_indices numbers (0 : usize).toNat).getD k 0]'hbi := by
    intro k hk
    exfalso
    have h0 : acc0.val.size = 0 := rfl
    rw [h0] at hk
    omega
  have h_meas : numbers.val.size - (0 : usize).toNat ≤ numbers.val.size := by
    rw [h_zero_toNat]; omega
  have h_i_le : (0 : usize).toNat ≤ numbers.val.size := by
    rw [h_zero_toNat]; omega
  obtain ⟨h_v_size, h_v_inv⟩ :=
    build_at_correct_strong numbers numbers.val.size (0 : usize) acc0 v
      h_meas h_i_le h_acc0_size h_acc0_inv hres
  refine ⟨h_v_size, ?_⟩
  intro k hk _hk'
  exact h_v_inv k hk

/-! ## Auxiliary lemma combining the two structural pieces.

This is fully closed using `build_indices_strict_mono`,
`build_at_size_correspondence`, and `build_indices_mem`. Each conjunct of
the contract resolves cleanly to one of these. -/

private theorem build_at_correct_aux (numbers : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_025_remove_duplicates.remove_duplicates numbers = RustM.ok v) :
    ∃ idx : Nat → Nat,
      (∀ k₁ k₂ : Nat, k₁ < k₂ → k₂ < v.val.size → idx k₁ < idx k₂) ∧
      (∀ k : Nat, ∀ (hk : k < v.val.size),
          ∃ (hi : idx k < numbers.val.size),
              v.val[k]'hk = numbers.val[idx k]'hi ∧
              total_count numbers (numbers.val[idx k]'hi) numbers.val.size = 1) ∧
      (∀ i : Nat, ∀ (hi : i < numbers.val.size),
          total_count numbers (numbers.val[i]'hi) numbers.val.size = 1 →
          ∃ k : Nat, ∃ (hk : k < v.val.size), idx k = i) := by
  obtain ⟨hsize, hcorresp⟩ := build_at_size_correspondence numbers v hres
  refine ⟨fun k => (build_indices numbers numbers.val.size).getD k 0, ?_, ?_, ?_⟩
  · -- Strict monotonicity follows from `build_indices_strict_mono`.
    intro k₁ k₂ hk_lt hk₂_lt
    have hk₂' : k₂ < (build_indices numbers numbers.val.size).length := by
      rw [← hsize]; exact hk₂_lt
    show (build_indices numbers numbers.val.size).getD k₁ 0 <
          (build_indices numbers numbers.val.size).getD k₂ 0
    exact build_indices_strict_mono numbers numbers.val.size k₁ k₂ hk_lt hk₂'
  · -- Per-output-position correspondence + soundness via `build_indices_mem`.
    intro k hk
    have hk' : k < (build_indices numbers numbers.val.size).length := by
      rw [← hsize]; exact hk
    obtain ⟨hi, hveq⟩ := hcorresp k hk hk'
    show ∃ (hi : (build_indices numbers numbers.val.size).getD k 0 < numbers.val.size),
            v.val[k]'hk = numbers.val[(build_indices numbers numbers.val.size).getD k 0]'hi ∧
            total_count numbers
              (numbers.val[(build_indices numbers numbers.val.size).getD k 0]'hi)
              numbers.val.size = 1
    refine ⟨hi, hveq, ?_⟩
    -- Construct membership in the `getD` form directly to avoid dependent
    -- rewrite issues. `(build_indices ...).getD k 0` equals `[k]` for k in
    -- range, and `[k]` is trivially a member.
    have h_getD_eq :
        (build_indices numbers numbers.val.size).getD k 0 =
          (build_indices numbers numbers.val.size)[k]'hk' :=
      (List.getElem_eq_getD (l := build_indices numbers numbers.val.size)
                            (i := k) (h := hk') 0).symm
    have h_mem :
        (build_indices numbers numbers.val.size).getD k 0
          ∈ build_indices numbers numbers.val.size := by
      rw [h_getD_eq]; exact List.getElem_mem _
    obtain ⟨_, _, hcc⟩ :=
      (build_indices_mem numbers numbers.val.size _).mp h_mem
    -- `hcc` already has the right shape; the implicit `< numbers.val.size`
    -- proof matches `hi` by proof irrelevance.
    exact hcc
  · -- Completeness: `i ∈ build_indices` (via `_mem.mpr`), then `List.mem_iff_getElem`.
    intro i hi hcc
    have h_i_mem : i ∈ build_indices numbers numbers.val.size :=
      (build_indices_mem numbers numbers.val.size i).mpr ⟨hi, hi, hcc⟩
    obtain ⟨n, hn_lt, hget⟩ := List.mem_iff_getElem.mp h_i_mem
    have hn_v : n < v.val.size := by rw [hsize]; exact hn_lt
    refine ⟨n, hn_v, ?_⟩
    show (build_indices numbers numbers.val.size).getD n 0 = i
    -- Bridge `getD n 0` = `[n]` for in-range n.
    rw [(List.getElem_eq_getD (l := build_indices numbers numbers.val.size)
                              (i := n) (h := hn_lt) 0).symm]
    exact hget

/-! ## Top-level obligations on `remove_duplicates`.

Each theorem corresponds to one property test in the Rust source. The
signatures take the function's `RustM.ok` result as a hypothesis, so they
speak about the value the function actually returns whenever it succeeds.
Each obligation reduces to one of the three conjuncts of `build_at_correct_aux`. -/

/-- Order-preservation postcondition: the output is a subsequence of the
    input, i.e. there is a strictly-increasing map from output positions
    to input positions such that the picked elements match. Captures the
    proptest `output_is_subsequence_of_input`. -/
theorem output_is_subsequence_of_input
    (numbers : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_025_remove_duplicates.remove_duplicates numbers = RustM.ok v) :
    ∃ idx : Nat → Nat,
      (∀ k₁ k₂ : Nat, k₁ < k₂ → k₂ < v.val.size → idx k₁ < idx k₂) ∧
      (∀ k : Nat, ∀ (hk : k < v.val.size),
          ∃ (hi : idx k < numbers.val.size),
              v.val[k]'hk = numbers.val[idx k]'hi) := by
  obtain ⟨idx, hmono, hcorr, _⟩ := build_at_correct_aux numbers v hres
  refine ⟨idx, hmono, ?_⟩
  intro k hk
  obtain ⟨hi, hveq, _⟩ := hcorr k hk
  exact ⟨hi, hveq⟩

/-- Soundness postcondition: every element appearing in the output occurs
    exactly once in the input. Captures the proptest
    `every_output_element_appears_exactly_once_in_input`. -/
theorem every_output_element_appears_exactly_once_in_input
    (numbers : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_025_remove_duplicates.remove_duplicates numbers = RustM.ok v)
    (k : Nat) (hk : k < v.val.size) :
    total_count numbers (v.val[k]'hk) numbers.val.size = 1 := by
  obtain ⟨idx, _, hcorr, _⟩ := build_at_correct_aux numbers v hres
  obtain ⟨hi, hveq, hcc⟩ := hcorr k hk
  rw [hveq]
  exact hcc

/-- Completeness postcondition: every input element whose total count is
    exactly one must appear in the output. Captures the proptest
    `every_unique_input_element_is_in_output`. -/
theorem every_unique_input_element_is_in_output
    (numbers : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_025_remove_duplicates.remove_duplicates numbers = RustM.ok v)
    (i : Nat) (hi : i < numbers.val.size)
    (h_count : total_count numbers (numbers.val[i]'hi) numbers.val.size = 1) :
    ∃ k : Nat, ∃ (hk : k < v.val.size), v.val[k]'hk = numbers.val[i]'hi := by
  obtain ⟨idx, _, hcorr, hcomplete⟩ := build_at_correct_aux numbers v hres
  obtain ⟨k, hk, hidx_eq⟩ := hcomplete i hi h_count
  refine ⟨k, hk, ?_⟩
  obtain ⟨hi', hveq, _⟩ := hcorr k hk
  rw [hveq]
  exact getElem_congr_idx hidx_eq

end Clever_025_remove_duplicatesObligations
