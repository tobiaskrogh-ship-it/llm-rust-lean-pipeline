-- Companion obligations file for the `clever_114_max_fill_count` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_114_max_fill_count

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_114_max_fill_countObligations

/-! ## Specification oracle (Nat-valued).

`countNonzeroFrom row j` counts the indices `k ∈ [j, row.val.size)` whose
entry is non-zero.  Total on `Nat` and well-founded on `row.val.size - j`.
This is the Lean mirror of the inner Rust helper `count_row_at`. -/

private def countNonzeroFrom (row : RustSlice u64) (j : Nat) : Nat :=
  if h : j < row.val.size then
    (if (row.val[j]'h) = (0 : u64) then 0 else 1) + countNonzeroFrom row (j + 1)
  else 0
termination_by row.val.size - j

/-- `maxFillSpecFrom grid capacity i` is the running spec total starting
from row `i`: the sum, over rows `r ∈ [i, grid.val.size)`, of the ceiling
`(countNonzeroFrom r 0 + capacity - 1) / capacity` (Nat division).  This
mirrors the Rust reference `spec` used by the `matches_spec` proptest. -/
private def maxFillSpecFrom
    (grid : RustSlice (RustSlice u64)) (capacity : Nat) (i : Nat) : Nat :=
  if h : i < grid.val.size then
    ((countNonzeroFrom (grid.val[i]'h) 0 + capacity - 1) / capacity)
      + maxFillSpecFrom grid capacity (i + 1)
  else 0
termination_by grid.val.size - i

/-! ## Concrete grid for the `known` unit pins. -/

private def known_row_0 : RustSlice u64 := ⟨#[0, 0, 1, 0], by decide⟩
private def known_row_1 : RustSlice u64 := ⟨#[0, 1, 0, 0], by decide⟩
private def known_row_2 : RustSlice u64 := ⟨#[1, 1, 1, 1], by decide⟩
private def known_grid : RustSlice (RustSlice u64) :=
  ⟨#[known_row_0, known_row_1, known_row_2], by decide⟩

/-! ## Standard scaffolding helpers. -/

/-- `RustM.ok x >>= f = f x`. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_zero_toNat : (0 : usize).toNat = 0 := rfl
private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl
private theorem u64_zero_toNat : (0 : u64).toNat = 0 := rfl
private theorem u64_one_toNat : (1 : u64).toNat = 1 := rfl
private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide

private theorem usize_add_one_no_bv (i : usize) (h : i.toNat + 1 < 2^64) :
    BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
  generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
  cases bo with
  | false => rfl
  | true =>
    exfalso
    have hi := (USize64.uaddOverflow_iff i 1).mp hbo
    rw [usize_one_toNat] at hi
    omega

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

/-! ## Step lemmas for `count_row_at`. -/

/-- Out-of-bounds: `j ≥ row.size` → return `acc`. -/
private theorem count_row_at_oob
    (row : RustSlice u64) (j : usize) (acc : u64)
    (hj : row.val.size ≤ j.toNat) :
    clever_114_max_fill_count.count_row_at row j acc = RustM.ok acc := by
  conv => lhs; unfold clever_114_max_fill_count.count_row_at
  have h_ofNat : (USize64.ofNat row.val.size).toNat = row.val.size :=
    USize64.toNat_ofNat_of_lt' row.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat row.val.size ≤ j) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hj
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- Nonzero step: in-bounds, `row[j] ≠ 0`, `acc+1` no overflow → recurse with `(j+1, acc+1)`. -/
private theorem count_row_at_step_nz
    (row : RustSlice u64) (j : usize) (acc : u64)
    (hj : j.toNat < row.val.size)
    (hne : row.val[j.toNat]'hj ≠ (0 : u64))
    (h_acc_ov : acc.toNat + 1 < 2^64) :
    clever_114_max_fill_count.count_row_at row j acc =
      clever_114_max_fill_count.count_row_at row (j + 1) (acc + 1) := by
  conv => lhs; unfold clever_114_max_fill_count.count_row_at
  have h_size_lt : row.val.size < USize64.size := row.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat row.val.size).toNat = row.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat row.val.size ≤ j) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (row[j]_? : RustM u64) = RustM.ok (row.val[j.toNat]'hj) := by
    show (if h : j.toNat < row.val.size then pure (row.val[j]) else .fail .arrayOutOfBounds)
        = RustM.ok (row.val[j.toNat]'hj)
    rw [dif_pos hj]; rfl
  have h_bne_true : (row.val[j.toNat]'hj != (0 : u64)) = true := by
    rw [bne_iff_ne]; exact hne
  have h_no_ov_j : j.toNat + 1 < 2^64 := by
    have : (USize64.size : Nat) = 2^64 := usize_size_eq
    rw [this] at h_size_lt; omega
  have h_no_bv_j : BitVec.uaddOverflow j.toBitVec (1 : usize).toBitVec = false :=
    usize_add_one_no_bv j h_no_ov_j
  have h_no_bv_acc : BitVec.uaddOverflow acc.toBitVec ((1 : u64).toBitVec) = false := by
    generalize hbo : BitVec.uaddOverflow acc.toBitVec ((1 : u64).toBitVec) = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have : UInt64.addOverflow acc 1 := hbo
      rw [UInt64.addOverflow_iff] at this
      rw [u64_one_toNat] at this
      omega
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.cmp.ne, h_bne_true,
             rust_primitives.ops.arith.Add.add, h_no_bv_j, h_no_bv_acc]

/-- Zero step: in-bounds, `row[j] = 0` → recurse with `(j+1, acc)`. -/
private theorem count_row_at_step_z
    (row : RustSlice u64) (j : usize) (acc : u64)
    (hj : j.toNat < row.val.size)
    (heq : row.val[j.toNat]'hj = (0 : u64)) :
    clever_114_max_fill_count.count_row_at row j acc =
      clever_114_max_fill_count.count_row_at row (j + 1) acc := by
  conv => lhs; unfold clever_114_max_fill_count.count_row_at
  have h_size_lt : row.val.size < USize64.size := row.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat row.val.size).toNat = row.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat row.val.size ≤ j) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (row[j]_? : RustM u64) = RustM.ok (row.val[j.toNat]'hj) := by
    show (if h : j.toNat < row.val.size then pure (row.val[j]) else .fail .arrayOutOfBounds)
        = RustM.ok (row.val[j.toNat]'hj)
    rw [dif_pos hj]; rfl
  have h_bne_false : (row.val[j.toNat]'hj != (0 : u64)) = false := by
    rw [bne_eq_false_iff_eq]; exact heq
  have h_no_ov_j : j.toNat + 1 < 2^64 := by
    have : (USize64.size : Nat) = 2^64 := usize_size_eq
    rw [this] at h_size_lt; omega
  have h_no_bv_j : BitVec.uaddOverflow j.toBitVec (1 : usize).toBitVec = false :=
    usize_add_one_no_bv j h_no_ov_j
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.cmp.ne, h_bne_false,
             rust_primitives.ops.arith.Add.add, h_no_bv_j]

/-! ## Equational lemmas for `countNonzeroFrom`. -/

private theorem countNonzeroFrom_oob (row : RustSlice u64) (j : Nat)
    (h : ¬ j < row.val.size) :
    countNonzeroFrom row j = 0 := by
  unfold countNonzeroFrom; rw [dif_neg h]

private theorem countNonzeroFrom_succ (row : RustSlice u64) (j : Nat)
    (h : j < row.val.size) :
    countNonzeroFrom row j =
      (if (row.val[j]'h) = (0 : u64) then 0 else 1) + countNonzeroFrom row (j + 1) := by
  conv => lhs; unfold countNonzeroFrom
  rw [dif_pos h]

/-- `countNonzeroFrom row j ≤ row.size - j`. -/
private theorem countNonzeroFrom_le (row : RustSlice u64) (j : Nat) :
    countNonzeroFrom row j ≤ row.val.size - j := by
  induction hk : (row.val.size - j) using Nat.strongRecOn generalizing j with
  | _ k ih =>
    by_cases h : j < row.val.size
    · rw [countNonzeroFrom_succ row j h]
      have h_meas : row.val.size - (j + 1) < k := by rw [← hk]; omega
      have h_ih := ih (row.val.size - (j + 1)) h_meas (j + 1) rfl
      by_cases hz : (row.val[j]'h) = (0 : u64)
      · rw [if_pos hz]; omega
      · rw [if_neg hz]; omega
    · rw [countNonzeroFrom_oob row j h]; omega

/-! ## `count_row_at` correctness. -/

private theorem count_row_at_correct
    (row : RustSlice u64) :
    ∀ (m : Nat) (j : usize) (acc : u64),
      acc.toNat + (row.val.size - j.toNat) < 2^64 →
      j.toNat ≤ row.val.size →
      row.val.size - j.toNat = m →
      ∃ v : u64,
        clever_114_max_fill_count.count_row_at row j acc = RustM.ok v
        ∧ v.toNat = acc.toNat + countNonzeroFrom row j.toNat := by
  intro m
  induction m with
  | zero =>
    intro j acc h_acc h_le hm
    have h_oob : row.val.size ≤ j.toNat := by omega
    refine ⟨acc, count_row_at_oob row j acc h_oob, ?_⟩
    have h_z : countNonzeroFrom row j.toNat = 0 :=
      countNonzeroFrom_oob row j.toNat (by omega)
    omega
  | succ m ih =>
    intro j acc h_acc h_le hm
    by_cases h_oob : row.val.size ≤ j.toNat
    · refine ⟨acc, count_row_at_oob row j acc h_oob, ?_⟩
      have h_z : countNonzeroFrom row j.toNat = 0 :=
        countNonzeroFrom_oob row j.toNat (by omega)
      omega
    · have hj : j.toNat < row.val.size := Nat.lt_of_not_le h_oob
      have h_size_lt : row.val.size < USize64.size := row.size_lt_usizeSize
      have h_us_size : (USize64.size : Nat) = 2^64 := usize_size_eq
      have h_no_ov_j : j.toNat + 1 < 2^64 := by rw [h_us_size] at h_size_lt; omega
      have h_j1 : (j + 1).toNat = j.toNat + 1 := usize_add_one_toNat j h_no_ov_j
      have h_count_le := countNonzeroFrom_le row (j.toNat + 1)
      have h_csz := countNonzeroFrom_succ row j.toNat hj
      have h_meas : row.val.size - (j + 1).toNat = m := by rw [h_j1]; omega
      have h_j1_le : (j + 1).toNat ≤ row.val.size := by rw [h_j1]; omega
      by_cases hz : (row.val[j.toNat]'hj) = (0 : u64)
      · -- zero branch: recurse with (j+1, acc)
        have h_step := count_row_at_step_z row j acc hj hz
        have h_acc' : acc.toNat + (row.val.size - (j + 1).toNat) < 2^64 := by
          rw [h_j1]; omega
        obtain ⟨v, hv_eq, hv_nat⟩ :=
          ih (j + 1) acc h_acc' h_j1_le h_meas
        refine ⟨v, ?_, ?_⟩
        · rw [h_step]; exact hv_eq
        · rw [hv_nat, h_j1, h_csz, if_pos hz]; omega
      · -- nonzero branch: recurse with (j+1, acc+1)
        have h_acc_ov : acc.toNat + 1 < 2^64 := by
          have : countNonzeroFrom row j.toNat ≥ 1 := by
            rw [h_csz, if_neg hz]; omega
          have h_rem_pos : row.val.size - j.toNat ≥ 1 := by omega
          omega
        have h_step := count_row_at_step_nz row j acc hj hz h_acc_ov
        have h_acc1_toNat : (acc + 1).toNat = acc.toNat + 1 := by
          have h_pre : acc.toNat + (1 : u64).toNat < 2^64 := by
            rw [u64_one_toNat]; exact h_acc_ov
          rw [UInt64.toNat_add_of_lt h_pre, u64_one_toNat]
        have h_acc' : (acc + 1).toNat + (row.val.size - (j + 1).toNat) < 2^64 := by
          rw [h_acc1_toNat, h_j1]; omega
        obtain ⟨v, hv_eq, hv_nat⟩ :=
          ih (j + 1) (acc + 1) h_acc' h_j1_le h_meas
        refine ⟨v, ?_, ?_⟩
        · rw [h_step]; exact hv_eq
        · rw [hv_nat, h_acc1_toNat, h_j1, h_csz, if_neg hz]; omega

/-! ## Step lemmas for `rows_at`. -/

/-- Out-of-bounds step: when `i.toNat ≥ grid.val.size`, `rows_at` returns `acc`. -/
private theorem rows_at_oob
    (grid : RustSlice (RustSlice u64)) (capacity : u64) (i : usize) (acc : u64)
    (hi : grid.val.size ≤ i.toNat) :
    clever_114_max_fill_count.rows_at grid capacity i acc = RustM.ok acc := by
  conv => lhs; unfold clever_114_max_fill_count.rows_at
  have h_ofNat : (USize64.ofNat grid.val.size).toNat = grid.val.size :=
    USize64.toNat_ofNat_of_lt' grid.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat grid.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- In-bounds step: when `i.toNat < grid.val.size`, the inner `count_row_at`
returns `w`, `capacity > 0` and no overflows occur, `rows_at` delegates to
`rows_at` at `(i+1, acc + trips)` where `trips = (w + capacity - 1) / capacity`. -/
private theorem rows_at_step
    (grid : RustSlice (RustSlice u64)) (capacity : u64) (i : usize) (acc : u64)
    (hi : i.toNat < grid.val.size)
    (w : u64)
    (h_w : clever_114_max_fill_count.count_row_at (grid.val[i.toNat]'hi)
             (0 : usize) (0 : u64) = RustM.ok w)
    (h_cap_pos : 0 < capacity.toNat)
    (h_w_cap_ov : w.toNat + capacity.toNat < 2^64)
    (h_acc_trips_ov :
       acc.toNat + (w.toNat + capacity.toNat - 1) / capacity.toNat < 2^64) :
    clever_114_max_fill_count.rows_at grid capacity i acc =
      clever_114_max_fill_count.rows_at grid capacity (i + 1)
        (acc + (w + capacity - 1) / capacity) := by
  conv => lhs; unfold clever_114_max_fill_count.rows_at
  have h_size_lt : grid.val.size < USize64.size := grid.size_lt_usizeSize
  have h_us_size : (USize64.size : Nat) = 2^64 := usize_size_eq
  have h_ofNat : (USize64.ofNat grid.val.size).toNat = grid.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  -- Outer if reduces to false
  have h_cond_outer : decide (USize64.ofNat grid.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  -- grid[i]_? reduces
  have h_idx : (grid[i]_? : RustM (RustSlice u64))
      = RustM.ok (grid.val[i.toNat]'hi) := by
    show (if h : i.toNat < grid.val.size then pure (grid.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (grid.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  -- i + 1 in bounds
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_us_size] at h_size_lt; omega
  have h_no_bv_i : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false :=
    usize_add_one_no_bv i h_no_ov_i
  have h_add_i : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
    show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = _
    show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
          then (.fail .integerOverflow : RustM usize)
          else pure (i + 1)) = _
    rw [h_no_bv_i]; rfl
  -- w + capacity no overflow
  have h_no_bv_wcap : BitVec.uaddOverflow w.toBitVec capacity.toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow w.toBitVec capacity.toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have : UInt64.addOverflow w capacity := hbo
      rw [UInt64.addOverflow_iff] at this
      omega
  have h_wcap : (w +? capacity : RustM u64) = RustM.ok (w + capacity) := by
    show (rust_primitives.ops.arith.Add.add w capacity : RustM u64) = _
    show (if BitVec.uaddOverflow w.toBitVec capacity.toBitVec
          then (.fail .integerOverflow : RustM u64)
          else pure (w + capacity)) = _
    rw [h_no_bv_wcap]; rfl
  have h_wcap_toNat : (w + capacity).toNat = w.toNat + capacity.toNat :=
    UInt64.toNat_add_of_lt h_w_cap_ov
  -- (w + capacity) - 1 no underflow
  have h_no_bv_sub : BitVec.usubOverflow (w + capacity).toBitVec (1 : u64).toBitVec = false := by
    generalize hbo : BitVec.usubOverflow (w + capacity).toBitVec (1 : u64).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have h_ov : UInt64.subOverflow (w + capacity) 1 := hbo
      have h_sub_lt := UInt64.subOverflow_iff.mp h_ov
      rw [u64_one_toNat, h_wcap_toNat] at h_sub_lt
      omega
  have h_sub : ((w + capacity) -? (1 : u64) : RustM u64)
      = RustM.ok (w + capacity - 1) := by
    show (rust_primitives.ops.arith.Sub.sub (w + capacity) 1 : RustM u64) = _
    show (if BitVec.usubOverflow (w + capacity).toBitVec (1 : u64).toBitVec
          then (.fail .integerOverflow : RustM u64)
          else pure (w + capacity - 1)) = _
    rw [h_no_bv_sub]; rfl
  have h_sub_toNat : (w + capacity - 1).toNat = w.toNat + capacity.toNat - 1 := by
    have h_le : (1 : u64).toNat ≤ (w + capacity).toNat := by
      rw [u64_one_toNat, h_wcap_toNat]; omega
    rw [UInt64.toNat_sub_of_le' h_le, h_wcap_toNat, u64_one_toNat]
  -- (w + cap - 1) / capacity no div by zero
  have h_cap_ne : capacity ≠ 0 := by
    intro h
    have h_zero : capacity.toNat = (0 : u64).toNat := by rw [h]
    rw [u64_zero_toNat] at h_zero; omega
  have h_div : ((w + capacity - 1) /? capacity : RustM u64)
      = RustM.ok ((w + capacity - 1) / capacity) := by
    show (rust_primitives.ops.arith.Div.div (w + capacity - 1) capacity : RustM u64) = _
    show (if capacity = 0 then (.fail .divisionByZero : RustM u64)
          else pure ((w + capacity - 1) / capacity)) = _
    rw [if_neg h_cap_ne]; rfl
  have h_div_toNat :
      ((w + capacity - 1) / capacity).toNat
        = (w.toNat + capacity.toNat - 1) / capacity.toNat := by
    rw [UInt64.toNat_div, h_sub_toNat]
  -- acc + trips no overflow
  have h_no_bv_acc :
      BitVec.uaddOverflow acc.toBitVec ((w + capacity - 1) / capacity).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow acc.toBitVec
                       ((w + capacity - 1) / capacity).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have h_ov : UInt64.addOverflow acc ((w + capacity - 1) / capacity) := hbo
      rw [UInt64.addOverflow_iff] at h_ov
      rw [h_div_toNat] at h_ov
      omega
  have h_acc_add : (acc +? ((w + capacity - 1) / capacity) : RustM u64)
      = RustM.ok (acc + ((w + capacity - 1) / capacity)) := by
    show (rust_primitives.ops.arith.Add.add acc ((w + capacity - 1) / capacity) : RustM u64) = _
    show (if BitVec.uaddOverflow acc.toBitVec ((w + capacity - 1) / capacity).toBitVec
          then (.fail .integerOverflow : RustM u64)
          else pure (acc + ((w + capacity - 1) / capacity))) = _
    rw [h_no_bv_acc]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_w, h_wcap, h_sub, h_div, h_add_i, h_acc_add]

/-! ## Equational lemmas for `maxFillSpecFrom`. -/

private theorem maxFillSpecFrom_oob
    (grid : RustSlice (RustSlice u64)) (capacity : Nat) (i : Nat)
    (h : ¬ i < grid.val.size) :
    maxFillSpecFrom grid capacity i = 0 := by
  unfold maxFillSpecFrom; rw [dif_neg h]

private theorem maxFillSpecFrom_succ
    (grid : RustSlice (RustSlice u64)) (capacity : Nat) (i : Nat)
    (h : i < grid.val.size) :
    maxFillSpecFrom grid capacity i =
      ((countNonzeroFrom (grid.val[i]'h) 0 + capacity - 1) / capacity)
        + maxFillSpecFrom grid capacity (i + 1) := by
  conv => lhs; unfold maxFillSpecFrom
  rw [dif_pos h]

/-! ## `rows_at` correctness. -/

private theorem rows_at_correct
    (grid : RustSlice (RustSlice u64)) (capacity : u64)
    (h_cap_pos : 0 < capacity.toNat)
    (h_rows_no_ov :
       ∀ (i : Nat) (hi : i < grid.val.size),
         countNonzeroFrom (grid.val[i]'hi) 0 + capacity.toNat < 2 ^ 64) :
    ∀ (m : Nat) (i : usize) (acc : u64),
      acc.toNat + maxFillSpecFrom grid capacity.toNat i.toNat < 2^64 →
      i.toNat ≤ grid.val.size →
      grid.val.size - i.toNat = m →
      ∃ v : u64,
        clever_114_max_fill_count.rows_at grid capacity i acc = RustM.ok v
        ∧ v.toNat = acc.toNat + maxFillSpecFrom grid capacity.toNat i.toNat := by
  intro m
  induction m with
  | zero =>
    intro i acc h_sum_ov h_le hm
    have h_oob : grid.val.size ≤ i.toNat := by omega
    refine ⟨acc, rows_at_oob grid capacity i acc h_oob, ?_⟩
    have h_z : maxFillSpecFrom grid capacity.toNat i.toNat = 0 :=
      maxFillSpecFrom_oob grid capacity.toNat i.toNat (by omega)
    omega
  | succ m ih =>
    intro i acc h_sum_ov h_le hm
    by_cases h_oob : grid.val.size ≤ i.toNat
    · refine ⟨acc, rows_at_oob grid capacity i acc h_oob, ?_⟩
      have h_z : maxFillSpecFrom grid capacity.toNat i.toNat = 0 :=
        maxFillSpecFrom_oob grid capacity.toNat i.toNat (by omega)
      omega
    · have hi : i.toNat < grid.val.size := Nat.lt_of_not_le h_oob
      -- Get the inner count_row_at result
      have h_row_size_lt : (grid.val[i.toNat]'hi).val.size < 2^64 := by
        have := (grid.val[i.toNat]'hi).size_lt_usizeSize
        rw [usize_size_eq] at this
        exact this
      have h_zero_toNat : (0 : usize).toNat = 0 := rfl
      have h_zero_u64_toNat : (0 : u64).toNat = 0 := rfl
      have h_row_acc :
          (0 : u64).toNat + ((grid.val[i.toNat]'hi).val.size - (0 : usize).toNat) < 2^64 := by
        rw [h_zero_toNat, h_zero_u64_toNat]; omega
      have h_zero_le : (0 : usize).toNat ≤ (grid.val[i.toNat]'hi).val.size := by
        rw [h_zero_toNat]; omega
      obtain ⟨w, hw_eq, hw_nat⟩ :=
        count_row_at_correct (grid.val[i.toNat]'hi)
          ((grid.val[i.toNat]'hi).val.size) (0 : usize) (0 : u64)
          h_row_acc h_zero_le rfl
      have h_w_nat : w.toNat = countNonzeroFrom (grid.val[i.toNat]'hi) 0 := by
        rw [hw_nat, h_zero_u64_toNat, h_zero_toNat]; omega
      have h_w_cap_ov : w.toNat + capacity.toNat < 2^64 := by
        rw [h_w_nat]; exact h_rows_no_ov i.toNat hi
      have h_spec_succ := maxFillSpecFrom_succ grid capacity.toNat i.toNat hi
      have h_trips_eq :
          (w.toNat + capacity.toNat - 1) / capacity.toNat =
            (countNonzeroFrom (grid.val[i.toNat]'hi) 0 + capacity.toNat - 1) / capacity.toNat := by
        rw [h_w_nat]
      have h_acc_trips_ov :
          acc.toNat + (w.toNat + capacity.toNat - 1) / capacity.toNat < 2^64 := by
        rw [h_trips_eq]
        have h_rest_nn : 0 ≤ maxFillSpecFrom grid capacity.toNat (i.toNat + 1) := Nat.zero_le _
        omega
      have h_step :=
        rows_at_step grid capacity i acc hi w hw_eq h_cap_pos h_w_cap_ov h_acc_trips_ov
      -- Set up the IH at (i+1, acc + trips)
      have h_us_size : (USize64.size : Nat) = 2^64 := usize_size_eq
      have h_size_lt : grid.val.size < USize64.size := grid.size_lt_usizeSize
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_us_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ grid.val.size := by rw [h_i1]; omega
      have h_meas : grid.val.size - (i + 1).toNat = m := by rw [h_i1]; omega
      let trips : u64 := (w + capacity - 1) / capacity
      have h_trips_toNat : trips.toNat = (w.toNat + capacity.toNat - 1) / capacity.toNat := by
        show ((w + capacity - 1) / capacity).toNat = _
        rw [UInt64.toNat_div]
        have h_wcap_toNat : (w + capacity).toNat = w.toNat + capacity.toNat :=
          UInt64.toNat_add_of_lt h_w_cap_ov
        have h_le : (1 : u64).toNat ≤ (w + capacity).toNat := by
          rw [u64_one_toNat, h_wcap_toNat]; omega
        rw [UInt64.toNat_sub_of_le' h_le, h_wcap_toNat, u64_one_toNat]
      have h_acc_plus_trips_toNat :
          (acc + trips).toNat = acc.toNat + trips.toNat := by
        apply UInt64.toNat_add_of_lt
        rw [h_trips_toNat]; exact h_acc_trips_ov
      have h_ih_sum_ov :
          (acc + trips).toNat + maxFillSpecFrom grid capacity.toNat (i + 1).toNat < 2^64 := by
        rw [h_acc_plus_trips_toNat, h_trips_toNat, h_i1, h_trips_eq]
        rw [h_spec_succ] at h_sum_ov
        omega
      obtain ⟨v, hv_eq, hv_nat⟩ := ih (i + 1) (acc + trips) h_ih_sum_ov h_i1_le h_meas
      refine ⟨v, ?_, ?_⟩
      · rw [h_step]; show clever_114_max_fill_count.rows_at grid capacity (i + 1) (acc + trips) = _
        exact hv_eq
      · rw [hv_nat, h_acc_plus_trips_toNat, h_trips_toNat, h_i1, h_trips_eq, h_spec_succ]
        omega

/-! ## Contract theorems. -/

/-- Failure-avoidance clause (proptest `capacity_zero_returns_zero`):
    for any grid, `max_fill_count grid 0 = 0`.  The wrapper short-circuits
    on `capacity = 0`, side-stepping the inner `_ /? capacity` divisor. -/
theorem capacity_zero_returns_zero (grid : RustSlice (RustSlice u64)) :
    clever_114_max_fill_count.max_fill_count grid 0 = RustM.ok 0 := by
  unfold clever_114_max_fill_count.max_fill_count
  simp only [show ((0 : u64) ==? (0 : u64)) =
                 (pure (decide ((0 : u64) = (0 : u64))) : RustM Bool) from rfl,
             pure_bind, decide_true, ↓reduceIte]
  rfl

/-- Base case (proptest `empty_grid_returns_zero`): an empty grid has
    no wells, hence no trips, for every `capacity` (including 0). -/
theorem empty_grid_returns_zero
    (grid : RustSlice (RustSlice u64)) (capacity : u64)
    (hempty : grid.val.size = 0) :
    clever_114_max_fill_count.max_fill_count grid capacity = RustM.ok 0 := by
  unfold clever_114_max_fill_count.max_fill_count
  by_cases h_cap_zero : capacity = 0
  · subst h_cap_zero
    simp only [show ((0 : u64) ==? (0 : u64)) =
                   (pure (decide ((0 : u64) = (0 : u64))) : RustM Bool) from rfl,
               pure_bind, decide_true, ↓reduceIte]
    rfl
  · have h_dec : decide (capacity = (0 : u64)) = false := decide_eq_false h_cap_zero
    simp only [show (capacity ==? (0 : u64)) =
                   (pure (decide (capacity = (0 : u64))) : RustM Bool) from rfl,
               h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
    -- rows_at grid capacity 0 0 with grid empty
    have h_zero_toNat : (0 : usize).toNat = 0 := rfl
    have h_oob : grid.val.size ≤ (0 : usize).toNat := by
      rw [h_zero_toNat, hempty]; omega
    exact rows_at_oob grid capacity (0 : usize) 0 h_oob

/-- Main postcondition (proptest `matches_spec`).

When `capacity > 0` and no overflow occurs at the per-row or accumulator
level, `max_fill_count grid capacity` equals
`Σ_{row in grid} ⌈count_nonzero(row) / capacity⌉` (Nat ceiling).

The feasibility preconditions are needed because the natural Lean
generalisation quantifies over `RustSlice` inputs of any `size < 2^64`,
where the proptest bounds `0..8 × 0..8 × 1..1_000_000` are far below the
overflow edges:

* `h_cap_pos` — `capacity ≠ 0`; without this, the wrapper short-circuits
  and the universal closed form does not hold.
* `h_rows_no_overflow` — for every row, `count_nonzero(row) + capacity`
  fits in `u64`.  Rules out overflow at `w +? capacity` inside `rows_at`.
* `h_sum_no_overflow` — the Nat-level spec sum fits in `u64`.  Rules out
  overflow at `acc +? trips` across rows.

Outside these bounds the function fails with `integerOverflow`, so the
universal equation truly does not hold; these preconditions are the
strongest honest formulation in the Lean model. -/
theorem matches_spec
    (grid : RustSlice (RustSlice u64)) (capacity : u64)
    (h_cap_pos : 0 < capacity.toNat)
    (h_rows_no_overflow :
       ∀ (i : Nat) (hi : i < grid.val.size),
         countNonzeroFrom (grid.val[i]'hi) 0 + capacity.toNat < 2 ^ 64)
    (h_sum_no_overflow : maxFillSpecFrom grid capacity.toNat 0 < 2 ^ 64) :
    clever_114_max_fill_count.max_fill_count grid capacity
      = RustM.ok (UInt64.ofNat (maxFillSpecFrom grid capacity.toNat 0)) := by
  unfold clever_114_max_fill_count.max_fill_count
  -- Wrapper branches on capacity == 0.
  have h_cap_ne : capacity ≠ 0 := by
    intro h
    have h_zero : capacity.toNat = (0 : u64).toNat := by rw [h]
    rw [u64_zero_toNat] at h_zero; omega
  have h_dec : decide (capacity = (0 : u64)) = false := decide_eq_false h_cap_ne
  simp only [show (capacity ==? (0 : u64)) =
                 (pure (decide (capacity = (0 : u64))) : RustM Bool) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
  -- Apply rows_at_correct with m = grid.val.size, i = 0, acc = 0.
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_zero_u64_toNat : (0 : u64).toNat = 0 := rfl
  have h_sum_ov0 :
      (0 : u64).toNat + maxFillSpecFrom grid capacity.toNat (0 : usize).toNat < 2^64 := by
    rw [h_zero_u64_toNat, h_zero_toNat]; omega
  have h_zero_le : (0 : usize).toNat ≤ grid.val.size := by
    rw [h_zero_toNat]; omega
  have h_meas : grid.val.size - (0 : usize).toNat = grid.val.size := by
    rw [h_zero_toNat, Nat.sub_zero]
  obtain ⟨v, hv_eq, hv_nat⟩ :=
    rows_at_correct grid capacity h_cap_pos h_rows_no_overflow
      grid.val.size (0 : usize) (0 : u64) h_sum_ov0 h_zero_le h_meas
  rw [hv_eq]
  congr 1
  -- v.toNat = maxFillSpecFrom grid capacity.toNat 0
  have h_v_eq : v.toNat = maxFillSpecFrom grid capacity.toNat 0 := by
    rw [hv_nat, h_zero_u64_toNat, h_zero_toNat]; omega
  -- v = UInt64.ofNat (maxFillSpecFrom grid capacity.toNat 0)
  apply UInt64.toNat_inj.mp
  rw [h_v_eq]
  -- Goal: maxFillSpecFrom grid capacity.toNat 0 = (UInt64.ofNat (maxFillSpecFrom grid capacity.toNat 0)).toNat
  have h_lt_64 : maxFillSpecFrom grid capacity.toNat 0 < 2^64 := h_sum_no_overflow
  show maxFillSpecFrom grid capacity.toNat 0
        = (UInt64.ofNat (maxFillSpecFrom grid capacity.toNat 0)).toNat
  simp [Nat.mod_eq_of_lt h_lt_64]

/-- Unit pin (test `known`, capacity 1): on the grid
    `[[0,0,1,0], [0,1,0,0], [1,1,1,1]]`, capacity-1 buckets need
    `1 + 1 + 4 = 6` trips. -/
theorem known_capacity_one :
    clever_114_max_fill_count.max_fill_count known_grid 1 = RustM.ok 6 := by
  native_decide

/-- Unit pin (test `known`, capacity 2): on the same grid, capacity-2
    buckets need `⌈1/2⌉ + ⌈1/2⌉ + ⌈4/2⌉ = 1 + 1 + 2 = 4` trips. -/
theorem known_capacity_two :
    clever_114_max_fill_count.max_fill_count known_grid 2 = RustM.ok 4 := by
  native_decide

end Clever_114_max_fill_countObligations
