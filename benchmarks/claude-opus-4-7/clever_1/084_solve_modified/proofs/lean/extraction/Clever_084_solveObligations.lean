-- Companion obligations file for the `clever_084_solve` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_084_solve

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_084_solveObligations

/-! ## Integer-valued specification

The Rust source `solve(n)` returns the sum of `n[i]` over indices `i` such
that `i` is odd and `n[i]` is even.  We mirror this at the `Int` level via
a primitive-recursive prefix oracle, so the spec side cannot overflow on
any input the Lean model permits.

The Rust test `naive` is `n.iter().enumerate().filter(|(i,v)| i%2==1 && *v%2==0).map(|(_,v)| *v).sum()`,
which is exactly `cond_sum_int n n.val.size` below. -/

/-- Integer-valued conditional prefix sum:
    `cond_sum_int n k = Σ_{j<k, j%2=1, n[j].toInt%2=0} (n.val[j]).toInt`.

    The outer `dite` keeps the function total — every theorem below
    quantifies `k` with `k ≤ n.val.size`, so the index stays in range. -/
private def cond_sum_int (n : RustSlice i64) : Nat → Int
  | 0     => 0
  | k + 1 =>
      cond_sum_int n k +
        (if h : k < n.val.size then
           (if k % 2 = 1 ∧ (n.val[k]'h).toInt % 2 = 0
            then (n.val[k]'h).toInt
            else 0)
         else 0)

/-! ## Standard helpers (mirrored from `below_zero_modified` /
    `pluck_modified`). -/

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

private theorem slice_index_eq (n : RustSlice i64) (i : usize)
    (hi : i.toNat < n.val.size) :
    (n[i]_? : RustM i64) = RustM.ok (n.val[i.toNat]'hi) := by
  show (if h : i.toNat < n.val.size then pure (n.val[i])
          else .fail .arrayOutOfBounds)
      = RustM.ok (n.val[i.toNat]'hi)
  rw [dif_pos hi]; rfl

/-! ## `usize`-modulo helpers (analogue of pluck's `i64_rem_two_eq`). -/

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

/-- Step of `cond_sum_int`: when `k < n.val.size`, the outer `dite`
    reduces. -/
private theorem cond_sum_int_succ
    (n : RustSlice i64) (k : Nat) (hk : k < n.val.size) :
    cond_sum_int n (k + 1) =
      cond_sum_int n k +
        (if k % 2 = 1 ∧ (n.val[k]'hk).toInt % 2 = 0
         then (n.val[k]'hk).toInt
         else 0) := by
  show cond_sum_int n k
        + (if h : k < n.val.size then
             (if k % 2 = 1 ∧ (n.val[k]'h).toInt % 2 = 0
              then (n.val[k]'h).toInt
              else 0)
           else 0)
       = cond_sum_int n k +
         (if k % 2 = 1 ∧ (n.val[k]'hk).toInt % 2 = 0
          then (n.val[k]'hk).toInt
          else 0)
  rw [dif_pos hk]

/-! ## Step lemmas for `sum_at`. -/

/-- Out-of-bounds step: when `i.toNat ≥ n.val.size`, the function
    returns `RustM.ok acc`. -/
private theorem sum_at_oob (n : RustSlice i64) (i : usize) (acc : i64)
    (hi : n.val.size ≤ i.toNat) :
    clever_084_solve.sum_at n i acc = RustM.ok acc := by
  conv => lhs; unfold clever_084_solve.sum_at
  have h_ofNat : (USize64.ofNat n.val.size).toNat = n.val.size :=
    USize64.toNat_ofNat_of_lt' n.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat n.val.size ≤ i) = true := by
    rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, h_cond, ↓reduceIte]
  rfl

/-- Take step: when `i.toNat < n.val.size`, the index is odd, the
    element is even, and the signed addition does not overflow, the
    function delegates to `sum_at n (i+1) (acc + n[i])`. -/
private theorem sum_at_take
    (n : RustSlice i64) (i : usize) (acc : i64)
    (hi : i.toNat < n.val.size)
    (h_odd_i : i.toNat % 2 = 1)
    (h_even_x : (n.val[i.toNat]'hi).toInt % 2 = 0)
    (hno : ¬ Int64.addOverflow acc (n.val[i.toNat]'hi)) :
    clever_084_solve.sum_at n i acc =
      clever_084_solve.sum_at n (i + 1) (acc + n.val[i.toNat]'hi) := by
  conv => lhs; unfold clever_084_solve.sum_at
  have h_size_lt : n.val.size < USize64.size := n.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat n.val.size).toNat = n.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat n.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]
    omega
  have h_idx := slice_index_eq n i hi
  have h_imod_eq_one : (i % 2 : usize) = (1 : usize) := by
    apply USize64.toNat_inj.mp
    rw [usize_mod_two_toNat, usize_one_toNat]
    exact h_odd_i
  have h_beq_one : ((i % 2 : usize) == (1 : usize)) = true := by
    rw [beq_iff_eq]; exact h_imod_eq_one
  have h_xmod_eq_zero : ((n.val[i.toNat]'hi) % 2 : i64) = 0 :=
    (i64_mod_two_eq_zero_iff (n.val[i.toNat]'hi)).mpr h_even_x
  have h_beq_zero : ((n.val[i.toNat]'hi) % 2 == (0 : i64)) = true := by
    rw [beq_iff_eq]; exact h_xmod_eq_zero
  have h_and_true :
      ((i % 2 : usize) == (1 : usize)
        && (n.val[i.toNat]'hi) % 2 == (0 : i64)) = true := by
    rw [h_beq_one, h_beq_zero]; rfl
  have h_no_bv :
      BitVec.saddOverflow acc.toBitVec (n.val[i.toNat]'hi).toBitVec = false := by
    have hno' : ¬ (BitVec.saddOverflow acc.toBitVec
                                       (n.val[i.toNat]'hi).toBitVec = true) := hno
    cases hb : BitVec.saddOverflow acc.toBitVec (n.val[i.toNat]'hi).toBitVec with
    | false => rfl
    | true => exact absurd hb hno'
  have h_add :
      (acc +? (n.val[i.toNat]'hi) : RustM i64) =
        RustM.ok (acc + n.val[i.toNat]'hi) := by
    show (rust_primitives.ops.arith.Add.add acc (n.val[i.toNat]'hi) : RustM i64) = _
    show (if BitVec.saddOverflow acc.toBitVec (n.val[i.toNat]'hi).toBitVec
          then (.fail .integerOverflow : RustM i64)
          else pure (acc + n.val[i.toNat]'hi)) = _
    rw [h_no_bv]; rfl
  have h_add_i := usize_add_one_eq i h_no_ov_i
  have h_urem := usize_rem_two_eq i
  have h_irem := i64_rem_two_eq (n.val[i.toNat]'hi)
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_urem, h_irem,
             rust_primitives.cmp.eq,
             rust_primitives.hax.logical_op.and,
             h_and_true, h_add, h_add_i]

/-- Skip step: when `i.toNat < n.val.size` and either the index is not
    odd or the element is not even, the function delegates to
    `sum_at n (i+1) acc`. -/
private theorem sum_at_skip
    (n : RustSlice i64) (i : usize) (acc : i64)
    (hi : i.toNat < n.val.size)
    (h_cond : i.toNat % 2 ≠ 1 ∨ (n.val[i.toNat]'hi).toInt % 2 ≠ 0) :
    clever_084_solve.sum_at n i acc =
      clever_084_solve.sum_at n (i + 1) acc := by
  conv => lhs; unfold clever_084_solve.sum_at
  have h_size_lt : n.val.size < USize64.size := n.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat n.val.size).toNat = n.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat n.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]
    omega
  have h_idx := slice_index_eq n i hi
  have h_urem := usize_rem_two_eq i
  have h_irem := i64_rem_two_eq (n.val[i.toNat]'hi)
  have h_add_i := usize_add_one_eq i h_no_ov_i
  have h_and_false :
      ((i % 2 : usize) == (1 : usize)
        && (n.val[i.toNat]'hi) % 2 == (0 : i64)) = false := by
    rcases h_cond with h_odd_no | h_even_no
    · have h_imod_neq : (i % 2 : usize) ≠ (1 : usize) := by
        intro h_eq
        apply h_odd_no
        have h_to : (i % 2 : usize).toNat = (1 : usize).toNat := by rw [h_eq]
        rw [usize_mod_two_toNat, usize_one_toNat] at h_to
        exact h_to
      have h_dec : ((i % 2 : usize) == (1 : usize)) = false := by
        rw [beq_eq_false_iff_ne]; exact h_imod_neq
      rw [h_dec]; rfl
    · have h_xmod_neq : ((n.val[i.toNat]'hi) % 2 : i64) ≠ 0 := by
        intro h_eq
        exact h_even_no ((i64_mod_two_eq_zero_iff (n.val[i.toNat]'hi)).mp h_eq)
      have h_dec : ((n.val[i.toNat]'hi) % 2 == (0 : i64)) = false := by
        rw [beq_eq_false_iff_ne]; exact h_xmod_neq
      rw [h_dec]; exact Bool.and_false _
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_urem, h_irem,
             rust_primitives.cmp.eq,
             rust_primitives.hax.logical_op.and,
             h_and_false, h_add_i]

/-! ## Strong-induction master lemma. -/

private theorem sum_at_correct (n : RustSlice i64)
    (hfit : ∀ k : Nat, k ≤ n.val.size →
              -(2^63 : Int) ≤ cond_sum_int n k ∧ cond_sum_int n k < 2^63) :
    ∀ (m : Nat) (i : usize) (acc : i64),
      n.val.size - i.toNat ≤ m →
      i.toNat ≤ n.val.size →
      acc.toInt = cond_sum_int n i.toNat →
      ∃ r : i64,
        clever_084_solve.sum_at n i acc = RustM.ok r ∧
        r.toInt = cond_sum_int n n.val.size := by
  intro m
  induction m with
  | zero =>
    intro i acc hm hi_le hinv
    have hi_eq : i.toNat = n.val.size := by omega
    have hi_ge : n.val.size ≤ i.toNat := by omega
    refine ⟨acc, sum_at_oob n i acc hi_ge, ?_⟩
    rw [hinv, hi_eq]
  | succ m ih =>
    intro i acc hm hi_le hinv
    by_cases hi_ge : n.val.size ≤ i.toNat
    · have hi_eq : i.toNat = n.val.size := by omega
      refine ⟨acc, sum_at_oob n i acc hi_ge, ?_⟩
      rw [hinv, hi_eq]
    · have hi_lt : i.toNat < n.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : n.val.size < USize64.size := n.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ n.val.size := by rw [h_i1]; omega
      have h_m_le : n.val.size - (i + 1).toNat ≤ m := by rw [h_i1]; omega
      have h_succ_eq := cond_sum_int_succ n i.toNat hi_lt
      by_cases h_take :
          i.toNat % 2 = 1 ∧ (n.val[i.toNat]'hi_lt).toInt % 2 = 0
      · obtain ⟨h_odd_i, h_even_x⟩ := h_take
        have h_psum_succ :
            cond_sum_int n (i.toNat + 1) =
              cond_sum_int n i.toNat + (n.val[i.toNat]'hi_lt).toInt := by
          rw [h_succ_eq]
          rw [if_pos ⟨h_odd_i, h_even_x⟩]
        have h_fit_succ := hfit (i.toNat + 1) (by omega)
        have h_no_ov : ¬ Int64.addOverflow acc (n.val[i.toNat]'hi_lt) := by
          intro hov
          rw [Int64.addOverflow_iff] at hov
          rcases hov with hov_pos | hov_neg
          · have h_sum_eq :
                acc.toInt + (n.val[i.toNat]'hi_lt).toInt = cond_sum_int n (i.toNat + 1) := by
              rw [h_psum_succ, hinv]
            rw [h_sum_eq] at hov_pos
            have := h_fit_succ.2
            omega
          · have h_sum_eq :
                acc.toInt + (n.val[i.toNat]'hi_lt).toInt = cond_sum_int n (i.toNat + 1) := by
              rw [h_psum_succ, hinv]
            rw [h_sum_eq] at hov_neg
            have := h_fit_succ.1
            omega
        have h_step := sum_at_take n i acc hi_lt h_odd_i h_even_x h_no_ov
        have h_new_toInt :
            (acc + (n.val[i.toNat]'hi_lt)).toInt =
              acc.toInt + (n.val[i.toNat]'hi_lt).toInt :=
          Int64.toInt_add_of_not_addOverflow h_no_ov
        have h_new_inv :
            (acc + (n.val[i.toNat]'hi_lt)).toInt = cond_sum_int n (i + 1).toNat := by
          rw [h_new_toInt, hinv, h_i1, ← h_psum_succ]
        obtain ⟨r, h_rec_eq, h_r_int⟩ :=
          ih (i + 1) (acc + (n.val[i.toNat]'hi_lt)) h_m_le h_i1_le h_new_inv
        refine ⟨r, ?_, h_r_int⟩
        rw [h_step]; exact h_rec_eq
      · have h_or : i.toNat % 2 ≠ 1 ∨ (n.val[i.toNat]'hi_lt).toInt % 2 ≠ 0 := by
          by_cases h_odd : i.toNat % 2 = 1
          · by_cases h_even : (n.val[i.toNat]'hi_lt).toInt % 2 = 0
            · exact absurd ⟨h_odd, h_even⟩ h_take
            · right; exact h_even
          · left; exact h_odd
        have h_psum_succ_skip :
            cond_sum_int n (i.toNat + 1) = cond_sum_int n i.toNat := by
          rw [h_succ_eq]
          rw [if_neg]
          · omega
          · intro h_both; exact h_take h_both
        have h_step := sum_at_skip n i acc hi_lt h_or
        have h_new_inv : acc.toInt = cond_sum_int n (i + 1).toNat := by
          rw [hinv, h_i1, h_psum_succ_skip]
        obtain ⟨r, h_rec_eq, h_r_int⟩ :=
          ih (i + 1) acc h_m_le h_i1_le h_new_inv
        refine ⟨r, ?_, h_r_int⟩
        rw [h_step]; exact h_rec_eq

/-! ## Top-level theorems. -/

/-- Boundary clause: an empty slice yields `0`. -/
theorem empty_returns_zero
    (n : RustSlice i64) (hempty : n.val.size = 0) :
    clever_084_solve.solve n = RustM.ok (0 : i64) := by
  unfold clever_084_solve.solve
  have hi_ge : n.val.size ≤ (0 : usize).toNat := by
    rw [usize_zero_toNat, hempty]; omega
  exact sum_at_oob n (0 : usize) (0 : i64) hi_ge

/-- Boundary clause: a one-element slice yields `0` regardless of the
    element's value, since index `0` is even (not odd). -/
theorem singleton_returns_zero
    (n : RustSlice i64) (hsingleton : n.val.size = 1) :
    clever_084_solve.solve n = RustM.ok (0 : i64) := by
  unfold clever_084_solve.solve
  -- At i = 0, index parity is 0 % 2 = 0 ≠ 1, so SKIP fires and we
  -- recurse to i = 1, where i.toNat = 1 = n.val.size triggers OOB.
  have h0_lt : (0 : usize).toNat < n.val.size := by
    rw [usize_zero_toNat, hsingleton]; omega
  have h_odd_no : (0 : usize).toNat % 2 ≠ 1 := by
    rw [usize_zero_toNat]; decide
  have h_or : (0 : usize).toNat % 2 ≠ 1 ∨
              (n.val[(0 : usize).toNat]'h0_lt).toInt % 2 ≠ 0 :=
    Or.inl h_odd_no
  have h_step := sum_at_skip n (0 : usize) (0 : i64) h0_lt h_or
  rw [h_step]
  have h_no_ov : (0 : usize).toNat + 1 < 2 ^ 64 := by
    rw [usize_zero_toNat]; decide
  have h_i1_toNat : ((0 : usize) + 1).toNat = 1 := by
    rw [usize_add_one_toNat (0 : usize) h_no_ov, usize_zero_toNat]
  have h_i1_ge : n.val.size ≤ ((0 : usize) + 1).toNat := by
    rw [h_i1_toNat, hsingleton]; omega
  exact sum_at_oob n ((0 : usize) + 1) (0 : i64) h_i1_ge

/-- Main postcondition: under a no-overflow precondition on every prefix
    of the conditional sum, `solve n` succeeds and its result equals the
    `Int`-valued spec `cond_sum_int` evaluated at the full slice length.

    The `hfit` hypothesis states that every running accumulator value
    `cond_sum_int n k` (for `0 ≤ k ≤ n.val.size`) fits in `i64`.  This is
    the natural Lean generalisation of the proptest's bounded element
    range (`-1000..=1000` × length `0..32` keeps every running sum well
    below `2^63`); the universal claim without `hfit` is false in the
    model because for sufficiently large i64-valued inputs the `+?` step
    can overflow and the function fails. -/
theorem matches_spec
    (n : RustSlice i64)
    (hfit : ∀ k : Nat, k ≤ n.val.size →
              -(2^63 : Int) ≤ cond_sum_int n k ∧ cond_sum_int n k < 2^63) :
    ∃ r : i64,
      clever_084_solve.solve n = RustM.ok r ∧
      r.toInt = cond_sum_int n n.val.size := by
  unfold clever_084_solve.solve
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_inv : (0 : i64).toInt = cond_sum_int n (0 : usize).toNat := by
    rw [h_zero_toNat, i64_zero_toInt]; rfl
  have h_m_le : n.val.size - (0 : usize).toNat ≤ n.val.size := by
    rw [h_zero_toNat]; omega
  have h_i_le : (0 : usize).toNat ≤ n.val.size := by
    rw [h_zero_toNat]; omega
  exact sum_at_correct n hfit n.val.size (0 : usize) (0 : i64) h_m_le h_i_le h_inv

end Clever_084_solveObligations
