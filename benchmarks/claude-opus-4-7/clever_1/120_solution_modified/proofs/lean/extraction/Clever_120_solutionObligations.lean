-- Companion obligations file for the `clever_120_solution` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_120_solution

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_120_solutionObligations

/-! ## Integer-valued specification

The Rust source `solution(lst)` returns the sum of `lst[i]` over indices
`i` such that `i` is even AND `lst[i]` is odd.  We mirror this at the
`Int` level via a primitive-recursive prefix oracle so the spec side
cannot overflow on any input the Lean model permits. -/

/-- Integer-valued conditional prefix sum:
    `cond_sum_int lst k = Σ_{j<k, j%2=0, (lst.val[j]).toInt%2≠0} (lst.val[j]).toInt`. -/
private def cond_sum_int (lst : RustSlice i64) : Nat → Int
  | 0     => 0
  | k + 1 =>
      cond_sum_int lst k +
        (if h : k < lst.val.size then
           (if k % 2 = 0 ∧ (lst.val[k]'h).toInt % 2 ≠ 0
            then (lst.val[k]'h).toInt
            else 0)
         else 0)

/-! ## Standard helpers (mirrored from `clever_084_solve_modified` /
    `below_zero_modified` / `pluck_modified`). -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl
private theorem usize_zero_toNat : (0 : usize).toNat = 0 := rfl
private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

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

private theorem usize_add_one_eq (i : usize) (h : i.toNat + 1 < 2^64) :
    (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
  show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
  show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure (i + 1)) = _
  rw [usize_add_one_no_bv i h]; rfl

private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide

private theorem slice_index_eq (l : RustSlice i64) (i : usize)
    (hi : i.toNat < l.val.size) :
    (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi) := by
  show (if h : i.toNat < l.val.size then pure (l.val[i])
          else .fail .arrayOutOfBounds)
      = RustM.ok (l.val[i.toNat]'hi)
  rw [dif_pos hi]; rfl

/-! ## `usize`-modulo helpers. -/

/-- `(i %? 2 : RustM usize) = RustM.ok (i % 2)` since `2 ≠ 0`. -/
private theorem usize_rem_two_eq (i : usize) :
    (i %? (2 : usize) : RustM usize) = RustM.ok (i % 2) := by
  show (rust_primitives.ops.arith.Rem.rem i (2 : usize) : RustM usize) =
        RustM.ok (i % 2)
  show (if (2 : usize) = 0 then (.fail .divisionByZero : RustM usize)
        else pure (i % 2)) = _
  rw [if_neg (by decide : (2 : usize) ≠ 0)]
  rfl

/-- `(i % 2 : usize).toNat = i.toNat % 2`. -/
private theorem usize_mod_two_toNat (i : usize) :
    (i % 2 : usize).toNat = i.toNat % 2 := by
  show (i.toBitVec % (2 : usize).toBitVec).toNat = i.toNat % 2
  rw [BitVec.toNat_umod]
  rfl

/-! ## `i64`-modulo helpers (mirrored from `pluck_modified`). -/

/-- `(x %? 2 : RustM i64) = RustM.ok (x % 2)` (since `2 ≠ -1, 0`). -/
private theorem i64_rem_two_eq (x : i64) :
    (x %? (2 : i64) : RustM i64) = RustM.ok (x % 2) := by
  show (rust_primitives.ops.arith.Rem.rem x 2 : RustM i64) = RustM.ok (x % 2)
  show (if (x = Int64.minValue && (2 : i64) = -1) then
          (.fail .integerOverflow : RustM i64)
        else if (2 : i64) = 0 then .fail .divisionByZero
        else pure (x % 2)) = _
  have h_and : (x = Int64.minValue && decide ((2 : i64) = -1)) = false := by
    rw [show (decide ((2 : i64) = -1)) = false from by decide]
    exact Bool.and_false _
  rw [h_and]
  rw [if_neg (by decide : ¬ ((2 : i64) = 0))]
  rfl

/-- `x % 2 = 0 ↔ x.toInt % 2 = 0` for `i64`. Bridges Rust evenness to
    the integer-level spec. -/
private theorem i64_mod_two_eq_zero_iff (x : i64) :
    ((x % (2 : i64)) = (0 : i64)) ↔ x.toInt % 2 = 0 := by
  constructor
  · intro h
    have h_toInt : (x % 2 : i64).toInt = (0 : i64).toInt := by rw [h]
    have h_via128 : (x % 2 : i64).toInt128.toInt = (x.toInt128 % (2 : i64).toInt128).toInt := by
      rw [Int64.toInt128_mod]
    rw [Int64.toInt_toInt128] at h_via128
    rw [h_via128] at h_toInt
    rw [Int128.toInt_mod] at h_toInt
    rw [Int64.toInt_toInt128] at h_toInt
    rw [show (((2 : i64).toInt128).toInt) = (2 : Int) from rfl] at h_toInt
    rw [show ((0 : i64).toInt) = (0 : Int) from by decide] at h_toInt
    have h_dvd : (2 : Int) ∣ x.toInt := Int.dvd_of_tmod_eq_zero h_toInt
    exact Int.emod_eq_zero_of_dvd h_dvd
  · intro h
    apply Int64.toInt_inj.mp
    have h_via128 : (x % 2 : i64).toInt128.toInt = (x.toInt128 % (2 : i64).toInt128).toInt := by
      rw [Int64.toInt128_mod]
    rw [Int64.toInt_toInt128] at h_via128
    rw [h_via128]
    rw [Int128.toInt_mod]
    rw [Int64.toInt_toInt128]
    rw [show (((2 : i64).toInt128).toInt) = (2 : Int) from rfl]
    rw [show ((0 : i64).toInt) = (0 : Int) from by decide]
    have h_dvd : (2 : Int) ∣ x.toInt := Int.dvd_of_emod_eq_zero h
    exact Int.tmod_eq_zero_of_dvd h_dvd

/-! ## Spec helpers. -/

/-- Step of `cond_sum_int`: when `k < lst.val.size`, the outer `dite`
    reduces. -/
private theorem cond_sum_int_succ
    (lst : RustSlice i64) (k : Nat) (hk : k < lst.val.size) :
    cond_sum_int lst (k + 1) =
      cond_sum_int lst k +
        (if k % 2 = 0 ∧ (lst.val[k]'hk).toInt % 2 ≠ 0
         then (lst.val[k]'hk).toInt
         else 0) := by
  show cond_sum_int lst k
        + (if h : k < lst.val.size then
             (if k % 2 = 0 ∧ (lst.val[k]'h).toInt % 2 ≠ 0
              then (lst.val[k]'h).toInt
              else 0)
           else 0)
       = cond_sum_int lst k +
         (if k % 2 = 0 ∧ (lst.val[k]'hk).toInt % 2 ≠ 0
          then (lst.val[k]'hk).toInt
          else 0)
  rw [dif_pos hk]

/-! ## Step lemmas for `sum_at`. -/

/-- Out-of-bounds step. -/
private theorem sum_at_oob (l : RustSlice i64) (i : usize) (acc : i64)
    (hi : l.val.size ≤ i.toNat) :
    clever_120_solution.sum_at l i acc = RustM.ok acc := by
  conv => lhs; unfold clever_120_solution.sum_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = true := by
    rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, h_cond, ↓reduceIte]
  rfl

/-- Take step: when `i.toNat < l.val.size`, the index is even, the
    element is odd, and the signed addition does not overflow, the
    function delegates to `sum_at l (i+1) (acc + l[i])`. -/
private theorem sum_at_take
    (l : RustSlice i64) (i : usize) (acc : i64)
    (hi : i.toNat < l.val.size)
    (h_even_i : i.toNat % 2 = 0)
    (h_odd_x : (l.val[i.toNat]'hi).toInt % 2 ≠ 0)
    (hno : ¬ Int64.addOverflow acc (l.val[i.toNat]'hi)) :
    clever_120_solution.sum_at l i acc =
      clever_120_solution.sum_at l (i + 1) (acc + l.val[i.toNat]'hi) := by
  conv => lhs; unfold clever_120_solution.sum_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]
    omega
  have h_idx := slice_index_eq l i hi
  have h_imod_eq_zero : (i % 2 : usize) = (0 : usize) := by
    apply USize64.toNat_inj.mp
    rw [usize_mod_two_toNat, usize_zero_toNat]
    exact h_even_i
  have h_beq_zero : ((i % 2 : usize) == (0 : usize)) = true := by
    rw [beq_iff_eq]; exact h_imod_eq_zero
  have h_xmod_ne_zero : ((l.val[i.toNat]'hi) % 2 : i64) ≠ 0 := by
    intro h_eq
    exact h_odd_x ((i64_mod_two_eq_zero_iff (l.val[i.toNat]'hi)).mp h_eq)
  have h_bne_zero : ((l.val[i.toNat]'hi) % 2 != (0 : i64)) = true := by
    rw [bne_iff_ne]; exact h_xmod_ne_zero
  have h_and_true :
      ((i % 2 : usize) == (0 : usize)
        && ((l.val[i.toNat]'hi) % 2 != (0 : i64))) = true := by
    rw [h_beq_zero, h_bne_zero]; rfl
  have h_no_bv :
      BitVec.saddOverflow acc.toBitVec (l.val[i.toNat]'hi).toBitVec = false := by
    have hno' : ¬ (BitVec.saddOverflow acc.toBitVec
                                       (l.val[i.toNat]'hi).toBitVec = true) := hno
    cases hb : BitVec.saddOverflow acc.toBitVec (l.val[i.toNat]'hi).toBitVec with
    | false => rfl
    | true => exact absurd hb hno'
  have h_add :
      (acc +? (l.val[i.toNat]'hi) : RustM i64) =
        RustM.ok (acc + l.val[i.toNat]'hi) := by
    show (rust_primitives.ops.arith.Add.add acc (l.val[i.toNat]'hi) : RustM i64) = _
    show (if BitVec.saddOverflow acc.toBitVec (l.val[i.toNat]'hi).toBitVec
          then (.fail .integerOverflow : RustM i64)
          else pure (acc + l.val[i.toNat]'hi)) = _
    rw [h_no_bv]; rfl
  have h_add_i := usize_add_one_eq i h_no_ov_i
  have h_urem := usize_rem_two_eq i
  have h_irem := i64_rem_two_eq (l.val[i.toNat]'hi)
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_urem, h_irem,
             rust_primitives.cmp.eq, rust_primitives.cmp.ne,
             rust_primitives.hax.logical_op.and,
             h_and_true, h_add, h_add_i]

/-- Skip step: when `i.toNat < l.val.size` and either the index is not
    even or the element is not odd, the function delegates to
    `sum_at l (i+1) acc`. -/
private theorem sum_at_skip
    (l : RustSlice i64) (i : usize) (acc : i64)
    (hi : i.toNat < l.val.size)
    (h_cond : i.toNat % 2 ≠ 0 ∨ (l.val[i.toNat]'hi).toInt % 2 = 0) :
    clever_120_solution.sum_at l i acc =
      clever_120_solution.sum_at l (i + 1) acc := by
  conv => lhs; unfold clever_120_solution.sum_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]
    omega
  have h_idx := slice_index_eq l i hi
  have h_urem := usize_rem_two_eq i
  have h_irem := i64_rem_two_eq (l.val[i.toNat]'hi)
  have h_add_i := usize_add_one_eq i h_no_ov_i
  have h_and_false :
      ((i % 2 : usize) == (0 : usize)
        && ((l.val[i.toNat]'hi) % 2 != (0 : i64))) = false := by
    rcases h_cond with h_even_no | h_odd_no
    · have h_imod_neq : (i % 2 : usize) ≠ (0 : usize) := by
        intro h_eq
        apply h_even_no
        have h_to : (i % 2 : usize).toNat = (0 : usize).toNat := by rw [h_eq]
        rw [usize_mod_two_toNat, usize_zero_toNat] at h_to
        exact h_to
      have h_dec : ((i % 2 : usize) == (0 : usize)) = false := by
        rw [beq_eq_false_iff_ne]; exact h_imod_neq
      rw [h_dec]; rfl
    · have h_xmod_eq : ((l.val[i.toNat]'hi) % 2 : i64) = 0 :=
        (i64_mod_two_eq_zero_iff (l.val[i.toNat]'hi)).mpr h_odd_no
      have h_dec : ((l.val[i.toNat]'hi) % 2 != (0 : i64)) = false := by
        rw [bne_eq_false_iff_eq]; exact h_xmod_eq
      rw [h_dec]; exact Bool.and_false _
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_urem, h_irem,
             rust_primitives.cmp.eq, rust_primitives.cmp.ne,
             rust_primitives.hax.logical_op.and,
             h_and_false, h_add_i]

/-! ## Strong-induction master lemma. -/

private theorem sum_at_correct (l : RustSlice i64)
    (hfit : ∀ k : Nat, k ≤ l.val.size →
              -(2^63 : Int) ≤ cond_sum_int l k ∧ cond_sum_int l k < 2^63) :
    ∀ (m : Nat) (i : usize) (acc : i64),
      l.val.size - i.toNat ≤ m →
      i.toNat ≤ l.val.size →
      acc.toInt = cond_sum_int l i.toNat →
      ∃ r : i64,
        clever_120_solution.sum_at l i acc = RustM.ok r ∧
        r.toInt = cond_sum_int l l.val.size := by
  intro m
  induction m with
  | zero =>
    intro i acc hm hi_le hinv
    have hi_eq : i.toNat = l.val.size := by omega
    have hi_ge : l.val.size ≤ i.toNat := by omega
    refine ⟨acc, sum_at_oob l i acc hi_ge, ?_⟩
    rw [hinv, hi_eq]
  | succ m ih =>
    intro i acc hm hi_le hinv
    by_cases hi_ge : l.val.size ≤ i.toNat
    · have hi_eq : i.toNat = l.val.size := by omega
      refine ⟨acc, sum_at_oob l i acc hi_ge, ?_⟩
      rw [hinv, hi_eq]
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_m_le : l.val.size - (i + 1).toNat ≤ m := by rw [h_i1]; omega
      have h_succ_eq := cond_sum_int_succ l i.toNat hi_lt
      by_cases h_take :
          i.toNat % 2 = 0 ∧ (l.val[i.toNat]'hi_lt).toInt % 2 ≠ 0
      · obtain ⟨h_even_i, h_odd_x⟩ := h_take
        have h_psum_succ :
            cond_sum_int l (i.toNat + 1) =
              cond_sum_int l i.toNat + (l.val[i.toNat]'hi_lt).toInt := by
          rw [h_succ_eq]
          rw [if_pos ⟨h_even_i, h_odd_x⟩]
        have h_fit_succ := hfit (i.toNat + 1) (by omega)
        have h_no_ov : ¬ Int64.addOverflow acc (l.val[i.toNat]'hi_lt) := by
          intro hov
          rw [Int64.addOverflow_iff] at hov
          rcases hov with hov_pos | hov_neg
          · have h_sum_eq :
                acc.toInt + (l.val[i.toNat]'hi_lt).toInt = cond_sum_int l (i.toNat + 1) := by
              rw [h_psum_succ, hinv]
            rw [h_sum_eq] at hov_pos
            have := h_fit_succ.2
            omega
          · have h_sum_eq :
                acc.toInt + (l.val[i.toNat]'hi_lt).toInt = cond_sum_int l (i.toNat + 1) := by
              rw [h_psum_succ, hinv]
            rw [h_sum_eq] at hov_neg
            have := h_fit_succ.1
            omega
        have h_step := sum_at_take l i acc hi_lt h_even_i h_odd_x h_no_ov
        have h_new_toInt :
            (acc + (l.val[i.toNat]'hi_lt)).toInt =
              acc.toInt + (l.val[i.toNat]'hi_lt).toInt :=
          Int64.toInt_add_of_not_addOverflow h_no_ov
        have h_new_inv :
            (acc + (l.val[i.toNat]'hi_lt)).toInt = cond_sum_int l (i + 1).toNat := by
          rw [h_new_toInt, hinv, h_i1, ← h_psum_succ]
        obtain ⟨r, h_rec_eq, h_r_int⟩ :=
          ih (i + 1) (acc + (l.val[i.toNat]'hi_lt)) h_m_le h_i1_le h_new_inv
        refine ⟨r, ?_, h_r_int⟩
        rw [h_step]; exact h_rec_eq
      · have h_or : i.toNat % 2 ≠ 0 ∨ (l.val[i.toNat]'hi_lt).toInt % 2 = 0 := by
          by_cases h_even : i.toNat % 2 = 0
          · by_cases h_odd : (l.val[i.toNat]'hi_lt).toInt % 2 = 0
            · right; exact h_odd
            · -- h_odd : ¬ (... % 2 = 0), so the conjunction holds and we
              -- contradict h_take.
              exact absurd ⟨h_even, h_odd⟩ h_take
          · left; exact h_even
        have h_psum_succ_skip :
            cond_sum_int l (i.toNat + 1) = cond_sum_int l i.toNat := by
          rw [h_succ_eq]
          rw [if_neg]
          · omega
          · intro h_both; exact h_take h_both
        have h_step := sum_at_skip l i acc hi_lt h_or
        have h_new_inv : acc.toInt = cond_sum_int l (i + 1).toNat := by
          rw [hinv, h_i1, h_psum_succ_skip]
        obtain ⟨r, h_rec_eq, h_r_int⟩ :=
          ih (i + 1) acc h_m_le h_i1_le h_new_inv
        refine ⟨r, ?_, h_r_int⟩
        rw [h_step]; exact h_rec_eq

/-! ## Top-level theorems. -/

/-- Boundary clause: an empty slice yields `0`. -/
theorem empty_returns_zero
    (lst : RustSlice i64) (hempty : lst.val.size = 0) :
    clever_120_solution.solution lst = RustM.ok (0 : i64) := by
  unfold clever_120_solution.solution
  have hi_ge : lst.val.size ≤ (0 : usize).toNat := by
    rw [usize_zero_toNat, hempty]; omega
  exact sum_at_oob lst (0 : usize) (0 : i64) hi_ge

/-- Main postcondition. -/
theorem matches_spec
    (lst : RustSlice i64)
    (hfit : ∀ k : Nat, k ≤ lst.val.size →
              -(2^63 : Int) ≤ cond_sum_int lst k ∧ cond_sum_int lst k < 2^63) :
    ∃ r : i64,
      clever_120_solution.solution lst = RustM.ok r ∧
      r.toInt = cond_sum_int lst lst.val.size := by
  unfold clever_120_solution.solution
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_inv : (0 : i64).toInt = cond_sum_int lst (0 : usize).toNat := by
    rw [h_zero_toNat, i64_zero_toInt]; rfl
  have h_m_le : lst.val.size - (0 : usize).toNat ≤ lst.val.size := by
    rw [h_zero_toNat]; omega
  have h_i_le : (0 : usize).toNat ≤ lst.val.size := by
    rw [h_zero_toNat]; omega
  exact sum_at_correct lst hfit lst.val.size (0 : usize) (0 : i64) h_m_le h_i_le h_inv

/-- Helper: two slices that agree at every even index have equal
    conditional prefix sums on every common prefix. -/
private theorem cond_sum_int_of_even_agree
    (lst lst' : RustSlice i64)
    (h_size : lst.val.size = lst'.val.size)
    (h_even : ∀ (k : Nat) (h : k < lst.val.size) (h' : k < lst'.val.size),
                k % 2 = 0 → (lst.val[k]'h) = (lst'.val[k]'h')) :
    ∀ k : Nat, k ≤ lst.val.size →
      cond_sum_int lst k = cond_sum_int lst' k := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk_le : k ≤ lst.val.size := by omega
    have hk_lt : k < lst.val.size := by omega
    have hk_lt' : k < lst'.val.size := by rw [← h_size]; exact hk_lt
    have h_ih := ih hk_le
    rw [cond_sum_int_succ lst k hk_lt, cond_sum_int_succ lst' k hk_lt', h_ih]
    by_cases h_even_k : k % 2 = 0
    · have h_eq := h_even k hk_lt hk_lt' h_even_k
      rw [h_eq]
    · have h_lhs : ¬ (k % 2 = 0 ∧ (lst.val[k]'hk_lt).toInt % 2 ≠ 0) := by
        intro ⟨h1, _⟩; exact h_even_k h1
      have h_rhs : ¬ (k % 2 = 0 ∧ (lst'.val[k]'hk_lt').toInt % 2 ≠ 0) := by
        intro ⟨h1, _⟩; exact h_even_k h1
      rw [if_neg h_lhs, if_neg h_rhs]

/-- Independence clause. -/
theorem ignores_odd_indices
    (lst lst' : RustSlice i64)
    (h_size : lst.val.size = lst'.val.size)
    (h_even : ∀ (k : Nat) (h : k < lst.val.size) (h' : k < lst'.val.size),
                k % 2 = 0 → (lst.val[k]'h) = (lst'.val[k]'h'))
    (hfit  : ∀ k : Nat, k ≤ lst.val.size →
              -(2^63 : Int) ≤ cond_sum_int lst  k ∧ cond_sum_int lst  k < 2^63)
    (hfit' : ∀ k : Nat, k ≤ lst'.val.size →
              -(2^63 : Int) ≤ cond_sum_int lst' k ∧ cond_sum_int lst' k < 2^63) :
    ∃ r : i64,
      clever_120_solution.solution lst  = RustM.ok r ∧
      clever_120_solution.solution lst' = RustM.ok r := by
  obtain ⟨r,  hr,  hr_int⟩  := matches_spec lst  hfit
  obtain ⟨r', hr', hr'_int⟩ := matches_spec lst' hfit'
  -- cond_sum_int lst lst.val.size = cond_sum_int lst' lst'.val.size
  have h_csi :
      cond_sum_int lst lst.val.size = cond_sum_int lst' lst'.val.size := by
    have hle : lst.val.size ≤ lst.val.size := Nat.le_refl _
    have h_eq := cond_sum_int_of_even_agree lst lst' h_size h_even lst.val.size hle
    rw [h_eq, h_size]
  have h_r_eq_r' : r = r' := by
    apply Int64.toInt_inj.mp
    rw [hr_int, hr'_int, h_csi]
  refine ⟨r, hr, ?_⟩
  rw [h_r_eq_r']
  exact hr'

end Clever_120_solutionObligations
