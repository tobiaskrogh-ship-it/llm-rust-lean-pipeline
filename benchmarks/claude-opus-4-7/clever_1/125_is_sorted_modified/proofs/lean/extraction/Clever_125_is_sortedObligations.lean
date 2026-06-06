-- Companion obligations file for the `clever_125_is_sorted` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_125_is_sorted

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_125_is_sortedObligations

/-! ## Specification predicates. -/

/-- `total_count l target k` is the number of indices `j < k` for which
`l.val[j] = target`. -/
private def total_count (l : RustSlice u64) (target : u64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      if h : k < l.val.size then
        (if (l.val[k]'h) = target then 1 else 0)
          + total_count l target k
      else
        total_count l target k

/-- Adjacent-pair non-decreasing predicate. -/
private def is_nondec (l : RustSlice u64) : Prop :=
  ∀ j : Nat, ∀ (hj1 : j + 1 < l.val.size),
    l.val[j]'(Nat.lt_of_succ_lt hj1) ≤ l.val[j+1]'hj1

/-- Every value appears at most twice in `l`. -/
private def multiplicity_ok (l : RustSlice u64) : Prop :=
  ∀ i : Nat, ∀ (hi : i < l.val.size),
    total_count l (l.val[i]'hi) l.val.size ≤ 2

/-! ## Standard scaffolding. -/

/-- `RustM.ok x >>= f = f x`. The library's `pure_bind` simp lemma only
    matches literal `Pure.pure`; this rewrite handles the `RustM.ok` form. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl
private theorem usize_zero_toNat : (0 : usize).toNat = 0 := rfl
private theorem u64_zero_toNat : (0 : u64).toNat = 0 := rfl
private theorem u64_one_toNat : (1 : u64).toNat = 1 := rfl
private theorem u64_two_toNat : (2 : u64).toNat = 2 := rfl
private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

private theorem u64_add_one_toNat (a : u64) (h : a.toNat + 1 < 2^64) :
    (a + 1).toNat = a.toNat + 1 := by
  have h_pre : a.toNat + (1 : u64).toNat < 2^64 := by
    rw [u64_one_toNat]; exact h
  rw [UInt64.toNat_add_of_lt h_pre, u64_one_toNat]

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

private theorem u64_add_one_no_bv (a : u64) (h : a.toNat + 1 < 2^64) :
    BitVec.uaddOverflow a.toBitVec (1 : u64).toBitVec = false := by
  generalize hbo : BitVec.uaddOverflow a.toBitVec (1 : u64).toBitVec = bo
  cases bo with
  | false => rfl
  | true =>
    exfalso
    have hii : UInt64.addOverflow a 1 := hbo
    rw [UInt64.addOverflow_iff] at hii
    rw [u64_one_toNat] at hii
    omega

private theorem slice_idx_ok (l : RustSlice u64) (i : usize)
    (hi : i.toNat < l.val.size) :
    (l[i]_? : RustM u64) = RustM.ok (l.val[i.toNat]'hi) := by
  show (if h : i.toNat < l.val.size then (pure (l.val[i]) : RustM u64)
        else RustM.fail Error.arrayOutOfBounds) = RustM.ok (l.val[i.toNat]'hi)
  rw [dif_pos hi]; rfl

private theorem usize_add_one_ok (i : usize) (h : i.toNat + 1 < 2^64) :
    (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
  show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
  show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure (i + 1)) = _
  rw [usize_add_one_no_bv i h]; rfl

private theorem u64_add_one_ok (a : u64) (h : a.toNat + 1 < 2^64) :
    (a +? (1 : u64) : RustM u64) = RustM.ok (a + 1) := by
  show (rust_primitives.ops.arith.Add.add a 1 : RustM u64) = RustM.ok (a + 1)
  show (if BitVec.uaddOverflow a.toBitVec (1 : u64).toBitVec
        then (.fail .integerOverflow : RustM u64)
        else pure (a + 1)) = _
  rw [u64_add_one_no_bv a h]; rfl

/-! ## Bound for `total_count`. -/

private theorem total_count_le (l : RustSlice u64) (target : u64) :
    ∀ k : Nat, total_count l target k ≤ k := by
  intro k
  induction k with
  | zero => show 0 ≤ 0; omega
  | succ k ih =>
    show (if h : k < l.val.size then
           (if (l.val[k]'h) = target then 1 else 0)
             + total_count l target k
          else total_count l target k) ≤ k + 1
    by_cases hk : k < l.val.size
    · rw [dif_pos hk]
      by_cases heq : (l.val[k]'hk) = target
      · rw [if_pos heq]; omega
      · rw [if_neg heq]; omega
    · rw [dif_neg hk]; omega

/-! ## Step lemmas for `count_at`. -/

private theorem count_at_oob (l : RustSlice u64) (target : u64) (i : usize)
    (acc : u64) (hi : l.val.size ≤ i.toNat) :
    clever_125_is_sorted.count_at l target i acc = RustM.ok acc := by
  conv => lhs; unfold clever_125_is_sorted.count_at
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

private theorem count_at_step_match (l : RustSlice u64) (target : u64) (i : usize)
    (acc : u64) (hi : i.toNat < l.val.size)
    (heq : (l.val[i.toNat]'hi) = target)
    (h_acc : acc.toNat + 1 < 2^64) :
    clever_125_is_sorted.count_at l target i acc =
      clever_125_is_sorted.count_at l target (i + 1) (acc + 1) := by
  conv => lhs; unfold clever_125_is_sorted.count_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx := slice_idx_ok l i hi
  have h_beq : (l.val[i.toNat]'hi == target) = true := by
    rw [beq_iff_eq]; exact heq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_size_lt; omega
  have h_add_i := usize_add_one_ok i h_no_ov_i
  have h_add_acc := u64_add_one_ok acc h_acc
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.cmp.eq, h_beq, h_add_i, h_add_acc]

private theorem count_at_step_miss (l : RustSlice u64) (target : u64) (i : usize)
    (acc : u64) (hi : i.toNat < l.val.size)
    (hne : (l.val[i.toNat]'hi) ≠ target) :
    clever_125_is_sorted.count_at l target i acc =
      clever_125_is_sorted.count_at l target (i + 1) acc := by
  conv => lhs; unfold clever_125_is_sorted.count_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx := slice_idx_ok l i hi
  have h_beq : (l.val[i.toNat]'hi == target) = false := by
    rw [beq_eq_false_iff_ne]; exact hne
  have h_no_ov_i : i.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_size_lt; omega
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.cmp.eq, h_beq,
             rust_primitives.ops.arith.Add.add, usize_add_one_no_bv i h_no_ov_i]

/-! ## Count_at correctness: existence + nat-level oracle. -/

/-- Additive (subtraction-free) correctness for `count_at`. Stating it as
    `c.toNat + total_count l target i.toNat = acc.toNat + total_count l target size`
    keeps omega happy without needing a monotonicity hint. -/
private theorem count_at_correct (l : RustSlice u64) (target : u64) :
    ∀ (m : Nat) (i : usize) (acc : u64),
      l.val.size - i.toNat ≤ m →
      i.toNat ≤ l.val.size →
      acc.toNat + (l.val.size - i.toNat) < 2^64 →
      ∃ c : u64,
        clever_125_is_sorted.count_at l target i acc = RustM.ok c ∧
        c.toNat + total_count l target i.toNat =
          acc.toNat + total_count l target l.val.size := by
  intro m
  induction m with
  | zero =>
    intro i acc hm hi_le h_acc_bound
    have hi_eq : i.toNat = l.val.size := by omega
    have hi_ge : l.val.size ≤ i.toNat := by omega
    refine ⟨acc, count_at_oob l target i acc hi_ge, ?_⟩
    rw [hi_eq]
  | succ m ih =>
    intro i acc hm hi_le h_acc_bound
    by_cases hi_ge : l.val.size ≤ i.toNat
    · have hi_eq : i.toNat = l.val.size := by omega
      refine ⟨acc, count_at_oob l target i acc hi_ge, ?_⟩
      rw [hi_eq]
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_m_le : l.val.size - (i + 1).toNat ≤ m := by rw [h_i1]; omega
      have h_tc_succ :
          total_count l target (i.toNat + 1) =
            (if (l.val[i.toNat]'hi_lt) = target then 1 else 0)
              + total_count l target i.toNat := by
        show (if h : i.toNat < l.val.size then
                 (if (l.val[i.toNat]'h) = target then 1 else 0)
                   + total_count l target i.toNat
               else total_count l target i.toNat) = _
        rw [dif_pos hi_lt]
      by_cases heq : (l.val[i.toNat]'hi_lt) = target
      · -- Match branch: count_at recurses with (i+1, acc+1).
        have h_step := count_at_step_match l target i acc hi_lt heq (by omega)
        have h_acc1_toNat : (acc + 1).toNat = acc.toNat + 1 := u64_add_one_toNat acc (by omega)
        have h_acc1_bound : (acc + 1).toNat + (l.val.size - (i + 1).toNat) < 2^64 := by
          rw [h_acc1_toNat, h_i1]; omega
        obtain ⟨c, hc_eq, hc_nat⟩ := ih (i + 1) (acc + 1) h_m_le h_i1_le h_acc1_bound
        refine ⟨c, ?_, ?_⟩
        · rw [h_step]; exact hc_eq
        · rw [h_acc1_toNat, h_i1] at hc_nat
          have h_tc_match :
              total_count l target (i.toNat + 1) =
                1 + total_count l target i.toNat := by
            rw [h_tc_succ, if_pos heq]
          rw [h_tc_match] at hc_nat
          omega
      · -- Miss branch: count_at recurses with (i+1, acc).
        have h_step := count_at_step_miss l target i acc hi_lt heq
        have h_acc_bound' : acc.toNat + (l.val.size - (i + 1).toNat) < 2^64 := by
          rw [h_i1]; omega
        obtain ⟨c, hc_eq, hc_nat⟩ := ih (i + 1) acc h_m_le h_i1_le h_acc_bound'
        refine ⟨c, ?_, ?_⟩
        · rw [h_step]; exact hc_eq
        · rw [h_i1] at hc_nat
          have h_tc_miss :
              total_count l target (i.toNat + 1) =
                total_count l target i.toNat := by
            rw [h_tc_succ, if_neg heq]; omega
          rw [h_tc_miss] at hc_nat
          omega

/-- Specialization at `i = 0, acc = 0`. -/
private theorem count_at_zero (l : RustSlice u64) (target : u64) :
    ∃ c : u64,
      clever_125_is_sorted.count_at l target (0 : usize) (0 : u64) = RustM.ok c ∧
      c.toNat = total_count l target l.val.size := by
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_bound : (0 : u64).toNat + (l.val.size - (0 : usize).toNat) < 2^64 := by
    rw [u64_zero_toNat, usize_zero_toNat]
    rw [h_usize_size] at h_size_lt; omega
  have h_zero_le : (0 : usize).toNat ≤ l.val.size := by
    rw [usize_zero_toNat]; omega
  obtain ⟨c, hc_eq, hc_nat⟩ :=
    count_at_correct l target l.val.size (0 : usize) (0 : u64) (by rw [usize_zero_toNat]; omega)
      h_zero_le h_bound
  refine ⟨c, hc_eq, ?_⟩
  rw [u64_zero_toNat, usize_zero_toNat] at hc_nat
  -- hc_nat : c.toNat + total_count l target 0 = 0 + total_count l target l.val.size
  -- Reduce total_count l target 0:
  have h_tc_zero : total_count l target 0 = 0 := by rfl
  rw [h_tc_zero] at hc_nat
  omega

/-! ## Step lemmas for `check_at`.

The structure: each step lemma unfolds `check_at` once and uses the appropriate
sub-case (oob, order-violation, no-violation-at-i + count > 2, no-violation +
count ≤ 2 → recurse).

We package these by reasoning about the `let order_violation : Bool ← ...`
binding directly. -/

/-- Out-of-bounds step: returns `true`. -/
private theorem check_at_oob (l : RustSlice u64) (i : usize)
    (hi : l.val.size ≤ i.toNat) :
    clever_125_is_sorted.check_at l i = RustM.ok true := by
  conv => lhs; unfold clever_125_is_sorted.check_at
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

/-- Order-violation step: in-bounds + i+1 < size + l[i] > l[i+1] → ok false. -/
private theorem check_at_step_order_violation (l : RustSlice u64) (i : usize)
    (hi : i.toNat < l.val.size)
    (h_i1 : i.toNat + 1 < l.val.size)
    (h_ov : l.val[i.toNat]'hi > l.val[i.toNat + 1]'h_i1) :
    clever_125_is_sorted.check_at l i = RustM.ok false := by
  conv => lhs; unfold clever_125_is_sorted.check_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2 ^ 64 := by
    rw [h_usize_size] at h_size_lt; omega
  have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_add_i := usize_add_one_ok i h_no_ov_i
  have h_cond_i1 : decide (USize64.ofNat l.val.size ≤ i + 1) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat, h_i1_toNat] at hle
    omega
  have h_idx_i := slice_idx_ok l i hi
  have h_i1_lt : (i + 1).toNat < l.val.size := by rw [h_i1_toNat]; exact h_i1
  have h_idx_i1 : (l[(i + 1)]_? : RustM u64) = RustM.ok (l.val[i.toNat + 1]'h_i1) := by
    have := slice_idx_ok l (i + 1) h_i1_lt
    rw [show l.val[(i + 1).toNat]'h_i1_lt = l.val[i.toNat + 1]'h_i1 from by
      congr 1] at this
    exact this
  have h_gt_cond :
      decide (l.val[i.toNat + 1]'h_i1 < l.val[i.toNat]'hi) = true := by
    rw [decide_eq_true_iff]; exact h_ov
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_add_i, h_cond_i1, h_idx_i, h_idx_i1,
             rust_primitives.cmp.gt, h_gt_cond]
  rfl

/-- Helper: when there is no order violation at `i` (either i+1 ≥ size, OR
    l[i] ≤ l[i+1]), the `order_violation` Bool evaluates to false.
    Packaging the reasoning so the two cases share the same simp recipe. -/
private theorem check_at_step_count_violation (l : RustSlice u64) (i : usize)
    (hi : i.toNat < l.val.size)
    (h_no_ov : ∀ (h_i1 : i.toNat + 1 < l.val.size),
                 l.val[i.toNat]'hi ≤ l.val[i.toNat + 1]'h_i1)
    (c : u64)
    (h_count : clever_125_is_sorted.count_at l (l.val[i.toNat]'hi) (0 : usize) (0 : u64)
                = RustM.ok c)
    (h_c : 2 < c.toNat) :
    clever_125_is_sorted.check_at l i = RustM.ok false := by
  conv => lhs; unfold clever_125_is_sorted.check_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2 ^ 64 := by
    rw [h_usize_size] at h_size_lt; omega
  have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_add_i := usize_add_one_ok i h_no_ov_i
  have h_idx_i := slice_idx_ok l i hi
  have h_dec_gt2 : decide ((2 : u64) < c) = true := by
    rw [decide_eq_true_iff]
    have h2 : (2 : u64).toNat = 2 := rfl
    rw [UInt64.lt_iff_toNat_lt, h2]; exact h_c
  -- The order_violation expression has two sub-cases.
  by_cases h_i1_lt : i.toNat + 1 < l.val.size
  · -- i+1 < size case: order violation cond is `l[i] > l[i+1]`, which is false by h_no_ov.
    have h_le := h_no_ov h_i1_lt
    have h_cond_i1 : decide (USize64.ofNat l.val.size ≤ i + 1) = false := by
      rw [decide_eq_false_iff_not]
      intro hle
      rw [USize64.le_iff_toNat_le, h_ofNat, h_i1_toNat] at hle
      omega
    have h_i1_lt' : (i + 1).toNat < l.val.size := by rw [h_i1_toNat]; exact h_i1_lt
    have h_idx_i1_inner : (l[(i + 1)]_? : RustM u64) =
        RustM.ok (l.val[i.toNat + 1]'h_i1_lt) := by
      have := slice_idx_ok l (i + 1) h_i1_lt'
      rw [show l.val[(i + 1).toNat]'h_i1_lt' = l.val[i.toNat + 1]'h_i1_lt from by
        congr 1] at this
      exact this
    have h_gt_false :
        decide (l.val[i.toNat + 1]'h_i1_lt < l.val[i.toNat]'hi) = false := by
      rw [decide_eq_false_iff_not]
      intro h_gt
      have hh : (l.val[i.toNat]'hi).toNat ≤ (l.val[i.toNat + 1]'h_i1_lt).toNat :=
        UInt64.le_iff_toNat_le.mp h_le
      have h_lt_nat : (l.val[i.toNat + 1]'h_i1_lt).toNat < (l.val[i.toNat]'hi).toNat :=
        UInt64.lt_iff_toNat_lt.mp h_gt
      omega
    simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
               rust_primitives.cmp.ge, rust_primitives.cmp.gt,
               pure_bind, RustM_ok_bind,
               h_cond_outer, Bool.false_eq_true, ↓reduceIte,
               h_add_i, h_cond_i1, h_idx_i, h_idx_i1_inner,
               h_gt_false,
               h_count, h_dec_gt2]
    rfl
  · -- i+1 ≥ size case: the inner if(i+1 ≥ size) is true, so order_violation = pure false.
    have h_i1_ge : l.val.size ≤ i.toNat + 1 := Nat.le_of_not_lt h_i1_lt
    have h_cond_i1 : decide (USize64.ofNat l.val.size ≤ i + 1) = true := by
      rw [decide_eq_true_iff]
      rw [USize64.le_iff_toNat_le, h_ofNat, h_i1_toNat]
      exact h_i1_ge
    simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
               rust_primitives.cmp.ge, rust_primitives.cmp.gt,
               pure_bind, RustM_ok_bind,
               h_cond_outer, Bool.false_eq_true, ↓reduceIte,
               h_add_i, h_cond_i1, h_idx_i,
               h_count, h_dec_gt2]
    rfl

private theorem check_at_step_recurse (l : RustSlice u64) (i : usize)
    (hi : i.toNat < l.val.size)
    (h_no_ov : ∀ (h_i1 : i.toNat + 1 < l.val.size),
                 l.val[i.toNat]'hi ≤ l.val[i.toNat + 1]'h_i1)
    (c : u64)
    (h_count : clever_125_is_sorted.count_at l (l.val[i.toNat]'hi) (0 : usize) (0 : u64)
                = RustM.ok c)
    (h_c : c.toNat ≤ 2) :
    clever_125_is_sorted.check_at l i = clever_125_is_sorted.check_at l (i + 1) := by
  conv => lhs; unfold clever_125_is_sorted.check_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2 ^ 64 := by
    rw [h_usize_size] at h_size_lt; omega
  have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_add_i := usize_add_one_ok i h_no_ov_i
  have h_idx_i := slice_idx_ok l i hi
  have h_dec_gt2 : decide ((2 : u64) < c) = false := by
    rw [decide_eq_false_iff_not]
    intro h_gt
    have h_lt_nat : (2 : u64).toNat < c.toNat := UInt64.lt_iff_toNat_lt.mp h_gt
    have h2 : (2 : u64).toNat = 2 := rfl
    omega
  by_cases h_i1_lt : i.toNat + 1 < l.val.size
  · -- i+1 < size case
    have h_le := h_no_ov h_i1_lt
    have h_cond_i1 : decide (USize64.ofNat l.val.size ≤ i + 1) = false := by
      rw [decide_eq_false_iff_not]
      intro hle
      rw [USize64.le_iff_toNat_le, h_ofNat, h_i1_toNat] at hle
      omega
    have h_i1_lt' : (i + 1).toNat < l.val.size := by rw [h_i1_toNat]; exact h_i1_lt
    have h_idx_i1_inner : (l[(i + 1)]_? : RustM u64) =
        RustM.ok (l.val[i.toNat + 1]'h_i1_lt) := by
      have := slice_idx_ok l (i + 1) h_i1_lt'
      rw [show l.val[(i + 1).toNat]'h_i1_lt' = l.val[i.toNat + 1]'h_i1_lt from by
        congr 1] at this
      exact this
    have h_gt_false :
        decide (l.val[i.toNat + 1]'h_i1_lt < l.val[i.toNat]'hi) = false := by
      rw [decide_eq_false_iff_not]
      intro h_gt
      have hh : (l.val[i.toNat]'hi).toNat ≤ (l.val[i.toNat + 1]'h_i1_lt).toNat :=
        UInt64.le_iff_toNat_le.mp h_le
      have h_lt_nat : (l.val[i.toNat + 1]'h_i1_lt).toNat < (l.val[i.toNat]'hi).toNat :=
        UInt64.lt_iff_toNat_lt.mp h_gt
      omega
    simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
               rust_primitives.cmp.ge, rust_primitives.cmp.gt,
               pure_bind, RustM_ok_bind,
               h_cond_outer, Bool.false_eq_true, ↓reduceIte,
               h_add_i, h_cond_i1, h_idx_i, h_idx_i1_inner,
               h_gt_false,
               h_count, h_dec_gt2]
  · -- i+1 ≥ size case
    have h_i1_ge : l.val.size ≤ i.toNat + 1 := Nat.le_of_not_lt h_i1_lt
    have h_cond_i1 : decide (USize64.ofNat l.val.size ≤ i + 1) = true := by
      rw [decide_eq_true_iff]
      rw [USize64.le_iff_toNat_le, h_ofNat, h_i1_toNat]
      exact h_i1_ge
    simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
               rust_primitives.cmp.ge, rust_primitives.cmp.gt,
               pure_bind, RustM_ok_bind,
               h_cond_outer, Bool.false_eq_true, ↓reduceIte,
               h_add_i, h_cond_i1, h_idx_i,
               h_count, h_dec_gt2]

/-! ## Strong-induction lemmas for the top-level obligations. -/

/-- Completeness: if every adjacent pair from `i.toNat` onwards is non-decreasing
    AND every value's total count is ≤ 2 (checked at indices from `i.toNat`),
    then `check_at l i = ok true`. -/
private theorem check_at_complete_aux (l : RustSlice u64) :
    ∀ (m : Nat) (i : usize),
      l.val.size - i.toNat ≤ m →
      i.toNat ≤ l.val.size →
      (∀ j : Nat, i.toNat ≤ j → ∀ (hj1 : j + 1 < l.val.size),
          l.val[j]'(Nat.lt_of_succ_lt hj1) ≤ l.val[j+1]'hj1) →
      (∀ j : Nat, i.toNat ≤ j → ∀ (hj : j < l.val.size),
          total_count l (l.val[j]'hj) l.val.size ≤ 2) →
      clever_125_is_sorted.check_at l i = RustM.ok true := by
  intro m
  induction m with
  | zero =>
    intro i hm hi_le h_nondec h_mult
    have hi_ge : l.val.size ≤ i.toNat := by omega
    exact check_at_oob l i hi_ge
  | succ m ih =>
    intro i hm hi_le h_nondec h_mult
    by_cases hi_ge : l.val.size ≤ i.toNat
    · exact check_at_oob l i hi_ge
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2 ^ 64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1_toNat]; omega
      have h_m_le : l.val.size - (i + 1).toNat ≤ m := by rw [h_i1_toNat]; omega
      -- The count_at at index i with the value l[i] always succeeds.
      obtain ⟨c, h_count, h_c_nat⟩ := count_at_zero l (l.val[i.toNat]'hi_lt)
      -- The multiplicity hypothesis at j = i.toNat tells us c ≤ 2.
      have h_c_le : c.toNat ≤ 2 := by
        rw [h_c_nat]
        exact h_mult i.toNat (Nat.le_refl _) hi_lt
      -- No order violation at i: from h_nondec at j = i.toNat.
      have h_no_ov : ∀ (h_i1 : i.toNat + 1 < l.val.size),
                       l.val[i.toNat]'hi_lt ≤ l.val[i.toNat + 1]'h_i1 := by
        intro h_i1
        exact h_nondec i.toNat (Nat.le_refl _) h_i1
      -- Apply the recurse step.
      rw [check_at_step_recurse l i hi_lt h_no_ov c h_count h_c_le]
      -- Apply IH on i+1 with shifted hypotheses.
      apply ih (i + 1) h_m_le h_i1_le
      · intro j hj hj1
        apply h_nondec j _ hj1
        rw [h_i1_toNat] at hj; omega
      · intro j hj hj
        apply h_mult j _ hj
        rw [h_i1_toNat] at *; omega

/-- Soundness: if `check_at l i = ok true`, then every adjacent pair from
    `i.toNat` onwards is non-decreasing AND every value's total count is ≤ 2
    (checked at indices from `i.toNat`). -/
private theorem check_at_sound_aux (l : RustSlice u64) :
    ∀ (m : Nat) (i : usize),
      l.val.size - i.toNat ≤ m →
      i.toNat ≤ l.val.size →
      clever_125_is_sorted.check_at l i = RustM.ok true →
      (∀ j : Nat, i.toNat ≤ j → ∀ (hj1 : j + 1 < l.val.size),
          l.val[j]'(Nat.lt_of_succ_lt hj1) ≤ l.val[j+1]'hj1) ∧
      (∀ j : Nat, i.toNat ≤ j → ∀ (hj : j < l.val.size),
          total_count l (l.val[j]'hj) l.val.size ≤ 2) := by
  intro m
  induction m with
  | zero =>
    intro i hm hi_le hres
    refine ⟨?_, ?_⟩
    · intro j hj hj1; omega
    · intro j hj hj; omega
  | succ m ih =>
    intro i hm hi_le hres
    by_cases hi_ge : l.val.size ≤ i.toNat
    · refine ⟨?_, ?_⟩
      · intro j hj hj1; omega
      · intro j hj hj; omega
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2 ^ 64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1_toNat]; omega
      have h_m_le : l.val.size - (i + 1).toNat ≤ m := by rw [h_i1_toNat]; omega
      obtain ⟨c, h_count, h_c_nat⟩ := count_at_zero l (l.val[i.toNat]'hi_lt)
      -- Step 1: rule out order violation at i (would give ok false, not ok true).
      have h_no_ov_at_i : ∀ (h_i1 : i.toNat + 1 < l.val.size),
                            l.val[i.toNat]'hi_lt ≤ l.val[i.toNat + 1]'h_i1 := by
        intro h_i1
        by_cases h_le : l.val[i.toNat]'hi_lt ≤ l.val[i.toNat + 1]'h_i1
        · exact h_le
        · exfalso
          have h_gt : l.val[i.toNat + 1]'h_i1 < l.val[i.toNat]'hi_lt := by
            rw [UInt64.lt_iff_toNat_lt]
            have h_nat : ¬ (l.val[i.toNat]'hi_lt).toNat ≤ (l.val[i.toNat + 1]'h_i1).toNat :=
              fun h' => h_le (UInt64.le_iff_toNat_le.mpr h')
            omega
          have h_ov_false := check_at_step_order_violation l i hi_lt h_i1 h_gt
          rw [h_ov_false] at hres
          injection hres with hh
          injection hh with hhh
          exact Bool.noConfusion hhh
      -- Step 2: rule out count violation at i.
      have h_c_le_2 : c.toNat ≤ 2 := by
        by_cases h_le_2 : c.toNat ≤ 2
        · exact h_le_2
        · exfalso
          have h_gt : 2 < c.toNat := Nat.lt_of_not_le h_le_2
          have h_cv := check_at_step_count_violation l i hi_lt h_no_ov_at_i c h_count h_gt
          rw [h_cv] at hres
          injection hres with hh
          injection hh with hhh
          exact Bool.noConfusion hhh
      -- Step 3: apply recurse step.
      have h_recurse := check_at_step_recurse l i hi_lt h_no_ov_at_i c h_count h_c_le_2
      rw [h_recurse] at hres
      -- Step 4: apply IH to (i+1).
      obtain ⟨h_nondec_next, h_mult_next⟩ := ih (i + 1) h_m_le h_i1_le hres
      refine ⟨?_, ?_⟩
      · intro j hj hj1
        by_cases hjeq : j = i.toNat
        · subst hjeq
          exact h_no_ov_at_i hj1
        · have hj' : (i + 1).toNat ≤ j := by rw [h_i1_toNat]; omega
          exact h_nondec_next j hj' hj1
      · intro j hj hj
        by_cases hjeq : j = i.toNat
        · subst hjeq
          rw [← h_c_nat]; exact h_c_le_2
        · have hj' : (i + 1).toNat ≤ j := by rw [h_i1_toNat]; omega
          exact h_mult_next j hj' hj

/-- Triple-repeat aux: if there is an index `k` from `i.toNat` onwards with
    `total_count l (l[k]) size > 2`, then `check_at l i = ok false`. -/
private theorem triple_repeat_aux (l : RustSlice u64) :
    ∀ (m : Nat) (i : usize),
      l.val.size - i.toNat ≤ m →
      i.toNat ≤ l.val.size →
      (∃ k, i.toNat ≤ k ∧ ∃ (hk : k < l.val.size),
          2 < total_count l (l.val[k]'hk) l.val.size) →
      clever_125_is_sorted.check_at l i = RustM.ok false := by
  intro m
  induction m with
  | zero =>
    intro i hm hi_le ⟨k, hk_ge, hk_lt, _⟩
    omega
  | succ m ih =>
    intro i hm hi_le ⟨k, hk_ge, hk_lt, hk_count⟩
    by_cases hi_ge : l.val.size ≤ i.toNat
    · -- i ≥ size: k ≥ i ≥ size, but k < size. Contradiction.
      omega
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2 ^ 64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1_toNat]; omega
      have h_m_le : l.val.size - (i + 1).toNat ≤ m := by rw [h_i1_toNat]; omega
      -- Compute count at index i.
      obtain ⟨c, h_count, h_c_nat⟩ := count_at_zero l (l.val[i.toNat]'hi_lt)
      -- Branch 1: order violation at i.
      by_cases h_ov_case :
          ∃ (h_i1 : i.toNat + 1 < l.val.size),
            l.val[i.toNat + 1]'h_i1 < l.val[i.toNat]'hi_lt
      · obtain ⟨h_i1, h_gt⟩ := h_ov_case
        exact check_at_step_order_violation l i hi_lt h_i1 h_gt
      · -- No order violation at i.
        have h_no_ov_at_i : ∀ (h_i1 : i.toNat + 1 < l.val.size),
                              l.val[i.toNat]'hi_lt ≤ l.val[i.toNat + 1]'h_i1 := by
          intro h_i1
          by_cases h_le : l.val[i.toNat]'hi_lt ≤ l.val[i.toNat + 1]'h_i1
          · exact h_le
          · exfalso
            apply h_ov_case
            refine ⟨h_i1, ?_⟩
            rw [UInt64.lt_iff_toNat_lt]
            have h_nat : ¬ (l.val[i.toNat]'hi_lt).toNat ≤ (l.val[i.toNat + 1]'h_i1).toNat :=
              fun h' => h_le (UInt64.le_iff_toNat_le.mpr h')
            omega
        -- Branch 2: count violation at i (i.e., the witness happens to be at i).
        by_cases h_c_at_i_gt2 : 2 < c.toNat
        · exact check_at_step_count_violation l i hi_lt h_no_ov_at_i c h_count h_c_at_i_gt2
        · -- Neither violation at i. The witness `k` must be > i.toNat.
          have h_c_le_2 : c.toNat ≤ 2 := Nat.le_of_not_lt h_c_at_i_gt2
          have h_count_i_le_2 : total_count l (l.val[i.toNat]'hi_lt) l.val.size ≤ 2 := by
            rw [← h_c_nat]; exact h_c_le_2
          -- Witness k ≠ i, since at k we have count > 2 but at i count ≤ 2.
          have h_k_ne_i : k ≠ i.toNat := by
            intro h_eq
            subst h_eq
            have h_idx_eq : l.val[i.toNat]'hk_lt = l.val[i.toNat]'hi_lt := rfl
            rw [h_idx_eq] at hk_count
            omega
          have h_k_gt_i : i.toNat < k := by omega
          rw [check_at_step_recurse l i hi_lt h_no_ov_at_i c h_count h_c_le_2]
          apply ih (i + 1) h_m_le h_i1_le
          refine ⟨k, ?_, hk_lt, hk_count⟩
          rw [h_i1_toNat]; omega

/-- Helper: if `total_count l v size > 0`, then `l` contains `v` at some index. -/
private theorem total_count_pos_witness (l : RustSlice u64) (v : u64) :
    ∀ k : Nat,
      0 < total_count l v k →
      ∃ j : Nat, ∃ (hj : j < l.val.size), j < k ∧ l.val[j]'hj = v := by
  intro k
  induction k with
  | zero =>
    intro h
    exfalso
    have heq : total_count l v 0 = 0 := rfl
    rw [heq] at h
    omega
  | succ k ih =>
    intro h
    have h_unfold : total_count l v (k + 1) =
        (if hk : k < l.val.size then
           (if (l.val[k]'hk) = v then 1 else 0) + total_count l v k
         else total_count l v k) := rfl
    rw [h_unfold] at h
    by_cases hk : k < l.val.size
    · rw [dif_pos hk] at h
      by_cases h_eq : (l.val[k]'hk) = v
      · refine ⟨k, hk, ?_, h_eq⟩; omega
      · rw [if_neg h_eq] at h
        simp only [Nat.zero_add] at h
        obtain ⟨j, hj_lt, hj_k, hj_eq⟩ := ih h
        refine ⟨j, hj_lt, ?_, hj_eq⟩; omega
    · rw [dif_neg hk] at h
      obtain ⟨j, hj_lt, hj_k, hj_eq⟩ := ih h
      refine ⟨j, hj_lt, ?_, hj_eq⟩; omega

/-! ## Top-level contract clauses. -/

theorem nondec_of_is_sorted_true
    (lst : RustSlice u64)
    (h : clever_125_is_sorted.is_sorted lst = RustM.ok true) :
    is_nondec lst := by
  unfold clever_125_is_sorted.is_sorted at h
  have h_zero : (0 : usize).toNat = 0 := rfl
  have h_zero_le : (0 : usize).toNat ≤ lst.val.size := by rw [h_zero]; omega
  obtain ⟨h_nondec, _⟩ := check_at_sound_aux lst lst.val.size (0 : usize)
    (by rw [h_zero]; omega) h_zero_le h
  intro j hj1
  exact h_nondec j (by rw [h_zero]; omega) hj1

theorem multiplicity_ok_of_is_sorted_true
    (lst : RustSlice u64)
    (h : clever_125_is_sorted.is_sorted lst = RustM.ok true) :
    multiplicity_ok lst := by
  unfold clever_125_is_sorted.is_sorted at h
  have h_zero : (0 : usize).toNat = 0 := rfl
  have h_zero_le : (0 : usize).toNat ≤ lst.val.size := by rw [h_zero]; omega
  obtain ⟨_, h_mult⟩ := check_at_sound_aux lst lst.val.size (0 : usize)
    (by rw [h_zero]; omega) h_zero_le h
  intro i hi
  exact h_mult i (by rw [h_zero]; omega) hi

theorem is_sorted_returns_true
    (lst : RustSlice u64)
    (h_nondec : is_nondec lst)
    (h_mult : multiplicity_ok lst) :
    clever_125_is_sorted.is_sorted lst = RustM.ok true := by
  unfold clever_125_is_sorted.is_sorted
  have h_zero : (0 : usize).toNat = 0 := rfl
  have h_zero_le : (0 : usize).toNat ≤ lst.val.size := by rw [h_zero]; omega
  apply check_at_complete_aux lst lst.val.size (0 : usize)
    (by rw [h_zero]; omega) h_zero_le
  · intro j _ hj1; exact h_nondec j hj1
  · intro i _ hi; exact h_mult i hi

theorem triple_repeat_rejected
    (lst : RustSlice u64)
    (h : ∃ v : u64, 2 < total_count lst v lst.val.size) :
    clever_125_is_sorted.is_sorted lst = RustM.ok false := by
  unfold clever_125_is_sorted.is_sorted
  have h_zero : (0 : usize).toNat = 0 := rfl
  have h_zero_le : (0 : usize).toNat ≤ lst.val.size := by rw [h_zero]; omega
  -- Extract a witness index k from the value-level existential.
  obtain ⟨v, h_count_v⟩ := h
  have h_pos : 0 < total_count lst v lst.val.size := by omega
  obtain ⟨k, hk_lt, _, hk_eq⟩ := total_count_pos_witness lst v lst.val.size h_pos
  -- At index k we have l[k] = v, so count l (l[k]) > 2.
  have h_count_k : 2 < total_count lst (lst.val[k]'hk_lt) lst.val.size := by
    rw [hk_eq]; exact h_count_v
  apply triple_repeat_aux lst lst.val.size (0 : usize)
    (by rw [h_zero]; omega) h_zero_le
  exact ⟨k, by rw [h_zero]; omega, hk_lt, h_count_k⟩

end Clever_125_is_sortedObligations
