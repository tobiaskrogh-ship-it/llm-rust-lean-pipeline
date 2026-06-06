-- Companion obligations file for the `clever_134_can_arrange` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_134_can_arrange

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_134_can_arrangeObligations

/-! ## Helper predicate. -/

/-- The slice has no descending adjacent pair (i.e., it is non-decreasing
    in the `arr[j] ≤ arr[j+1]` sense). -/
private def is_nondec (arr : RustSlice i64) : Prop :=
  ∀ j : Nat, ∀ (hj1 : j + 1 < arr.val.size),
    arr.val[j]'(Nat.lt_of_succ_lt hj1) ≤ arr.val[j+1]'hj1

/-! ## Standard scaffolding. -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl
private theorem usize_zero_toNat : (0 : usize).toNat = 0 := rfl
private theorem usize_two_toNat : (2 : usize).toNat = 2 := rfl
private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide

private theorem i64_neg_one_toInt : (-1 : i64).toInt = -1 := by decide

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

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

private theorem usize_add_one_ok (i : usize) (h : i.toNat + 1 < 2^64) :
    (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
  show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = _
  show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure (i + 1)) = _
  rw [usize_add_one_no_bv i h]; rfl

private theorem usize_sub_one_no_bv (i : usize) (h : 1 ≤ i.toNat) :
    BitVec.usubOverflow i.toBitVec (1 : usize).toBitVec = false := by
  generalize hbo : BitVec.usubOverflow i.toBitVec (1 : usize).toBitVec = bo
  cases bo with
  | false => rfl
  | true =>
    exfalso
    have h_sov : USize64.subOverflow i (1 : usize) = true := hbo
    have hh := USize64.subOverflow_iff.mp h_sov
    rw [usize_one_toNat] at hh
    omega

private theorem usize_sub_one_ok (i : usize) (h : 1 ≤ i.toNat) :
    (i -? (1 : usize) : RustM usize) = RustM.ok (i - 1) := by
  show (rust_primitives.ops.arith.Sub.sub i 1 : RustM usize) = _
  show (if BitVec.usubOverflow i.toBitVec (1 : usize).toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure (i - 1)) = _
  rw [usize_sub_one_no_bv i h]; rfl

private theorem usize_sub_one_toNat (i : usize) (h : 1 ≤ i.toNat) :
    (i - 1).toNat = i.toNat - 1 := by
  have h1 : (1 : usize).toNat ≤ i.toNat := by rw [usize_one_toNat]; exact h
  rw [USize64.toNat_sub_of_le' h1, usize_one_toNat]

/-- Indexing via `arr[i]_?` evaluates to `ok` when bounds-checked. -/
private theorem slice_idx_ok (arr : RustSlice i64) (i : usize)
    (hi : i.toNat < arr.val.size) :
    (arr[i]_? : RustM i64) = RustM.ok (arr.val[i.toNat]'hi) := by
  show (if h : i.toNat < arr.val.size then (pure (arr.val[i]) : RustM i64)
        else RustM.fail Error.arrayOutOfBounds) = RustM.ok (arr.val[i.toNat]'hi)
  rw [dif_pos hi]; rfl

/-- Length of the slice as a `usize`. -/
private theorem n_val_toNat (arr : RustSlice i64) :
    (USize64.ofNat arr.val.size).toNat = arr.val.size :=
  USize64.toNat_ofNat_of_lt' arr.size_lt_usizeSize

/-- The cast `(i : usize) as i64` equals `USize64.toInt64 i`. -/
private theorem cast_usize_to_i64 (i : usize) :
    (rust_primitives.hax.cast_op i : RustM i64) = RustM.ok (USize64.toInt64 i) := rfl

/-- For `i.toNat < 2^63`, the signed cast is just `i.toNat`. -/
private theorem USize64_toInt64_toInt (i : usize) (h : i.toNat < 2^63) :
    (USize64.toInt64 i).toInt = (i.toNat : Int) := by
  show (Int64.ofNat i.toNat).toInt = (i.toNat : Int)
  exact Int64.toInt_ofNat_of_lt h

/-- `(i as i64) ≠ -1` whenever `i.toNat < 2^64 - 1`. -/
private theorem USize64_toInt64_ne_neg_one (i : usize) (h : i.toNat < 2^64 - 1) :
    USize64.toInt64 i ≠ (-1 : i64) := by
  intro heq
  -- Compare BitVec representations.
  have h_bv : (USize64.toInt64 i).toBitVec = (-1 : i64).toBitVec := by rw [heq]
  have hi_lt : i.toNat < 2^64 := i.toNat_lt
  -- LHS computes to BitVec.ofNat 64 i.toNat
  have h_lhs_toNat : ((USize64.toInt64 i).toBitVec).toNat = i.toNat % 2^64 := by
    show (BitVec.ofNat 64 i.toNat).toNat = i.toNat % 2^64
    rw [BitVec.toNat_ofNat]
  -- RHS is the all-ones 64-bit BitVec, with toNat = 2^64 - 1
  have h_neg1_toNat : ((-1 : i64).toBitVec).toNat = 2^64 - 1 := by decide
  have h_eq_toNat : ((USize64.toInt64 i).toBitVec).toNat = ((-1 : i64).toBitVec).toNat := by
    rw [h_bv]
  rw [h_lhs_toNat, h_neg1_toNat] at h_eq_toNat
  rw [Nat.mod_eq_of_lt hi_lt] at h_eq_toNat
  omega

/-! ## Step lemmas for `scan_at`. -/

/-- OOB step: `i ≥ size` returns `best` unchanged. -/
private theorem sa_oob (arr : RustSlice i64) (i : usize) (best : i64)
    (hi : arr.val.size ≤ i.toNat) :
    clever_134_can_arrange.scan_at arr i best = RustM.ok best := by
  conv => lhs; unfold clever_134_can_arrange.scan_at
  have h_ofNat : (USize64.ofNat arr.val.size).toNat = arr.val.size := n_val_toNat arr
  have h_cond : decide (USize64.ofNat arr.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- Descent step: in-bounds, `1 ≤ i.toNat < size`, and `arr[i] < arr[i-1]`.
    Recurses with `(i+1, i as i64)`. -/
private theorem sa_descent (arr : RustSlice i64) (i : usize) (best : i64)
    (h_lo : 1 ≤ i.toNat) (hi : i.toNat < arr.val.size)
    (h_desc : arr.val[i.toNat]'hi < arr.val[i.toNat - 1]'(by omega)) :
    clever_134_can_arrange.scan_at arr i best =
      clever_134_can_arrange.scan_at arr (i + 1) (USize64.toInt64 i) := by
  conv => lhs; unfold clever_134_can_arrange.scan_at
  have h_size_lt : arr.val.size < 2^64 := arr.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat arr.val.size).toNat = arr.val.size := n_val_toNat arr
  have h_no_ov_i : i.toNat + 1 < 2^64 := by omega
  have h_cond : decide (USize64.ofNat arr.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_add_i := usize_add_one_ok i h_no_ov_i
  have h_sub_i := usize_sub_one_ok i h_lo
  have h_sub_toNat : (i - 1).toNat = i.toNat - 1 := usize_sub_one_toNat i h_lo
  have h_im1_lt : (i - 1).toNat < arr.val.size := by rw [h_sub_toNat]; omega
  have h_idx_i := slice_idx_ok arr i hi
  have h_idx_im1 : (arr[(i - 1)]_? : RustM i64) =
      RustM.ok (arr.val[i.toNat - 1]'(by omega)) := by
    have := slice_idx_ok arr (i - 1) h_im1_lt
    rw [show arr.val[(i - 1).toNat]'h_im1_lt = arr.val[i.toNat - 1]'(by omega) from by
      congr 1] at this
    exact this
  have h_lt_cond :
      decide (arr.val[i.toNat]'hi < arr.val[i.toNat - 1]'(by omega)) = true := by
    rw [decide_eq_true_iff]; exact h_desc
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, rust_primitives.cmp.lt,
             pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_add_i, h_sub_i, h_idx_i, h_idx_im1,
             h_lt_cond, rust_primitives.hax.cast_op, Cast.cast]

/-- Normal step: in-bounds, `1 ≤ i.toNat < size`, and `arr[i] ≥ arr[i-1]`.
    Recurses with `(i+1, best)`. -/
private theorem sa_normal (arr : RustSlice i64) (i : usize) (best : i64)
    (h_lo : 1 ≤ i.toNat) (hi : i.toNat < arr.val.size)
    (h_le : arr.val[i.toNat - 1]'(by omega) ≤ arr.val[i.toNat]'hi) :
    clever_134_can_arrange.scan_at arr i best =
      clever_134_can_arrange.scan_at arr (i + 1) best := by
  conv => lhs; unfold clever_134_can_arrange.scan_at
  have h_size_lt : arr.val.size < 2^64 := arr.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat arr.val.size).toNat = arr.val.size := n_val_toNat arr
  have h_no_ov_i : i.toNat + 1 < 2^64 := by omega
  have h_cond : decide (USize64.ofNat arr.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_add_i := usize_add_one_ok i h_no_ov_i
  have h_sub_i := usize_sub_one_ok i h_lo
  have h_sub_toNat : (i - 1).toNat = i.toNat - 1 := usize_sub_one_toNat i h_lo
  have h_im1_lt : (i - 1).toNat < arr.val.size := by rw [h_sub_toNat]; omega
  have h_idx_i := slice_idx_ok arr i hi
  have h_idx_im1 : (arr[(i - 1)]_? : RustM i64) =
      RustM.ok (arr.val[i.toNat - 1]'(by omega)) := by
    have := slice_idx_ok arr (i - 1) h_im1_lt
    rw [show arr.val[(i - 1).toNat]'h_im1_lt = arr.val[i.toNat - 1]'(by omega) from by
      congr 1] at this
    exact this
  have h_lt_cond :
      decide (arr.val[i.toNat]'hi < arr.val[i.toNat - 1]'(by omega)) = false := by
    rw [decide_eq_false_iff_not]
    intro h_lt
    have h_le_int : (arr.val[i.toNat - 1]'(by omega)).toInt ≤
                    (arr.val[i.toNat]'hi).toInt := Int64.le_iff_toInt_le.mp h_le
    have h_lt_int : (arr.val[i.toNat]'hi).toInt <
                    (arr.val[i.toNat - 1]'(by omega)).toInt :=
      Int64.lt_iff_toInt_lt.mp h_lt
    omega
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, rust_primitives.cmp.lt,
             pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_add_i, h_sub_i, h_idx_i, h_idx_im1,
             h_lt_cond]

/-! ## Auxiliary induction lemmas. -/

/-- If every adjacent pair from index `i.toNat - 1` onwards is non-descending,
    `scan_at arr i best` returns `best` unchanged.

    We require `1 ≤ i.toNat` so that `i - 1` is well-defined.  The condition
    is over pairs `(k, k+1)` where the smaller index `k ≥ i.toNat - 1`. -/
private theorem scan_at_no_descent_aux (arr : RustSlice i64) :
    ∀ (m : Nat) (i : usize) (best : i64),
      arr.val.size - i.toNat ≤ m →
      1 ≤ i.toNat →
      (∀ k : Nat, i.toNat - 1 ≤ k → ∀ (hk1 : k + 1 < arr.val.size),
          arr.val[k]'(Nat.lt_of_succ_lt hk1) ≤ arr.val[k+1]'hk1) →
      clever_134_can_arrange.scan_at arr i best = RustM.ok best := by
  intro m
  induction m with
  | zero =>
    intro i best hm h_lo h_nondec
    have h_oob : arr.val.size ≤ i.toNat := by omega
    exact sa_oob arr i best h_oob
  | succ m ih =>
    intro i best hm h_lo h_nondec
    by_cases h_oob : arr.val.size ≤ i.toNat
    · exact sa_oob arr i best h_oob
    · have hi_lt : i.toNat < arr.val.size := Nat.lt_of_not_le h_oob
      have h_size_lt : arr.val.size < 2^64 := arr.size_lt_usizeSize
      have h_no_ov : i.toNat + 1 < 2^64 := by omega
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 :=
        usize_add_one_toNat i h_no_ov
      have h_i1_lo : 1 ≤ (i + 1).toNat := by rw [h_i1_toNat]; omega
      have h_m_le : arr.val.size - (i + 1).toNat ≤ m := by rw [h_i1_toNat]; omega
      -- The check at i: arr[i-1] ≤ arr[i] by the hypothesis at k = i.toNat - 1.
      have h_le : arr.val[i.toNat - 1]'(by omega) ≤ arr.val[i.toNat]'hi_lt := by
        have h_eq : i.toNat = (i.toNat - 1) + 1 := by omega
        have h_k1 : (i.toNat - 1) + 1 < arr.val.size := by rw [← h_eq]; exact hi_lt
        have := h_nondec (i.toNat - 1) (Nat.le_refl _) h_k1
        -- this : arr[i.toNat - 1] ≤ arr[(i.toNat - 1) + 1]
        have h_idx : arr.val[(i.toNat - 1) + 1]'h_k1 = arr.val[i.toNat]'hi_lt := by
          congr 1; omega
        rw [h_idx] at this
        exact this
      rw [sa_normal arr i best h_lo hi_lt h_le]
      apply ih (i + 1) best h_m_le h_i1_lo
      intro k hk hk1
      apply h_nondec k _ hk1
      rw [h_i1_toNat] at hk; omega

/-- If the input `best ≠ -1`, then `scan_at` cannot produce `-1` as output.
    The reason: the only paths that change `best` set it to `(i' as i64)` for
    some `i' < arr.val.size`. Since `arr.val.size < 2^64`, all such `i'` have
    `i'.toNat ≤ 2^64 - 2 < 2^64 - 1`, so the cast never coincidentally equals
    `-1`. Hence the returned `r` is either the original `best` or some such
    cast — never `-1`. -/
private theorem scan_at_keeps_nonneg_aux (arr : RustSlice i64) :
    ∀ (m : Nat) (i : usize) (best : i64) (r : i64),
      arr.val.size - i.toNat ≤ m →
      1 ≤ i.toNat →
      best ≠ (-1 : i64) →
      clever_134_can_arrange.scan_at arr i best = RustM.ok r →
      r ≠ (-1 : i64) := by
  intro m
  induction m with
  | zero =>
    intro i best r hm h_lo h_ne hres
    have h_oob : arr.val.size ≤ i.toNat := by omega
    rw [sa_oob arr i best h_oob] at hres
    have h_eq : r = best := by
      injection hres with h1
      injection h1 with h2
      exact h2.symm
    rw [h_eq]; exact h_ne
  | succ m ih =>
    intro i best r hm h_lo h_ne hres
    by_cases h_oob : arr.val.size ≤ i.toNat
    · rw [sa_oob arr i best h_oob] at hres
      have h_eq : r = best := by
        injection hres with h1
        injection h1 with h2
        exact h2.symm
      rw [h_eq]; exact h_ne
    · have hi_lt : i.toNat < arr.val.size := Nat.lt_of_not_le h_oob
      have h_size_lt : arr.val.size < 2^64 := arr.size_lt_usizeSize
      have h_no_ov : i.toNat + 1 < 2^64 := by omega
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 :=
        usize_add_one_toNat i h_no_ov
      have h_i1_lo : 1 ≤ (i + 1).toNat := by rw [h_i1_toNat]; omega
      have h_m_le : arr.val.size - (i + 1).toNat ≤ m := by rw [h_i1_toNat]; omega
      by_cases h_desc : arr.val[i.toNat]'hi_lt < arr.val[i.toNat - 1]'(by omega)
      · rw [sa_descent arr i best h_lo hi_lt h_desc] at hres
        have h_cast_ne : USize64.toInt64 i ≠ (-1 : i64) := by
          apply USize64_toInt64_ne_neg_one
          omega
        exact ih (i + 1) (USize64.toInt64 i) r h_m_le h_i1_lo h_cast_ne hres
      · have h_le : arr.val[i.toNat - 1]'(by omega) ≤ arr.val[i.toNat]'hi_lt := by
          rcases Int.lt_or_le (arr.val[i.toNat]'hi_lt).toInt
                              (arr.val[i.toNat - 1]'(by omega)).toInt with h | h
          · exfalso; apply h_desc; exact Int64.lt_iff_toInt_lt.mpr h
          · exact Int64.le_iff_toInt_le.mpr h
        rw [sa_normal arr i best h_lo hi_lt h_le] at hres
        exact ih (i + 1) best r h_m_le h_i1_lo h_ne hres

/-- Soundness for the sentinel: if `scan_at arr i (-1) = ok (-1)`, then no
    descent occurs at any pair `(k, k+1)` with `k ≥ i.toNat - 1`. -/
private theorem scan_at_minus_one_imp_no_descent_aux (arr : RustSlice i64) :
    ∀ (m : Nat) (i : usize),
      arr.val.size - i.toNat ≤ m →
      1 ≤ i.toNat →
      clever_134_can_arrange.scan_at arr i (-1 : i64) = RustM.ok (-1 : i64) →
      (∀ k : Nat, i.toNat - 1 ≤ k → ∀ (hk1 : k + 1 < arr.val.size),
          arr.val[k]'(Nat.lt_of_succ_lt hk1) ≤ arr.val[k+1]'hk1) := by
  intro m
  induction m with
  | zero =>
    intro i hm h_lo hres k hk hk1
    -- arr.val.size - i.toNat = 0, so i.toNat ≥ arr.val.size, so k ≥ i.toNat - 1
    -- combined with k+1 < arr.val.size means impossible.
    omega
  | succ m ih =>
    intro i hm h_lo hres k hk hk1
    by_cases h_oob : arr.val.size ≤ i.toNat
    · omega
    · have hi_lt : i.toNat < arr.val.size := Nat.lt_of_not_le h_oob
      have h_size_lt : arr.val.size < 2^64 := arr.size_lt_usizeSize
      have h_no_ov : i.toNat + 1 < 2^64 := by omega
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 :=
        usize_add_one_toNat i h_no_ov
      have h_i1_lo : 1 ≤ (i + 1).toNat := by rw [h_i1_toNat]; omega
      have h_m_le : arr.val.size - (i + 1).toNat ≤ m := by rw [h_i1_toNat]; omega
      -- First, the check at i (pair (i-1, i)) must not be a descent.
      -- Otherwise, the descent branch sets best to (i as i64) ≠ -1, and by
      -- scan_at_keeps_nonneg, the output would not be -1, contradicting hres.
      have h_no_desc_at_i : arr.val[i.toNat - 1]'(by omega) ≤ arr.val[i.toNat]'hi_lt := by
        by_cases h_le : arr.val[i.toNat - 1]'(by omega) ≤ arr.val[i.toNat]'hi_lt
        · exact h_le
        · exfalso
          have h_desc : arr.val[i.toNat]'hi_lt < arr.val[i.toNat - 1]'(by omega) := by
            rcases Int.lt_or_le (arr.val[i.toNat]'hi_lt).toInt
                                (arr.val[i.toNat - 1]'(by omega)).toInt with hh | hh
            · exact Int64.lt_iff_toInt_lt.mpr hh
            · exfalso; apply h_le; exact Int64.le_iff_toInt_le.mpr hh
          rw [sa_descent arr i (-1 : i64) h_lo hi_lt h_desc] at hres
          have h_cast_ne : USize64.toInt64 i ≠ (-1 : i64) := by
            apply USize64_toInt64_ne_neg_one; omega
          have h_r_ne :=
            scan_at_keeps_nonneg_aux arr m (i + 1) (USize64.toInt64 i) (-1 : i64)
              h_m_le h_i1_lo h_cast_ne hres
          exact h_r_ne rfl
      -- Now we have the normal step; recurse with i+1.
      rw [sa_normal arr i (-1 : i64) h_lo hi_lt h_no_desc_at_i] at hres
      -- The conclusion for k ≥ i.toNat - 1:
      --   * k = i.toNat - 1: directly h_no_desc_at_i (with appropriate index alignment).
      --   * k ≥ i.toNat: by IH.
      by_cases h_k_eq : k = i.toNat - 1
      · -- k = i.toNat - 1, k+1 = i.toNat
        subst h_k_eq
        have h_idx_a : arr.val[i.toNat - 1]'(Nat.lt_of_succ_lt hk1) =
            arr.val[i.toNat - 1]'(by omega) := rfl
        have h_k1_eq : (i.toNat - 1) + 1 = i.toNat := by omega
        have h_idx_b : arr.val[(i.toNat - 1) + 1]'hk1 = arr.val[i.toNat]'hi_lt := by
          congr 1
        rw [h_idx_a, h_idx_b]
        exact h_no_desc_at_i
      · have hk_ge : (i + 1).toNat - 1 ≤ k := by rw [h_i1_toNat]; omega
        exact ih (i + 1) h_m_le h_i1_lo hres k hk_ge hk1

/-- The carried-best invariant. Either `best = -1` (no descent has been
    found yet), or `best` encodes a descent position `p + 1`. -/
private def best_inv (arr : RustSlice i64) (best : i64) : Prop :=
  best = (-1 : i64) ∨
    ∃ p : Nat, ∃ (hp : p + 1 < arr.val.size),
      best.toInt = (p + 1 : Int) ∧
      arr.val[p + 1]'hp < arr.val[p]'(Nat.lt_of_succ_lt hp)

/-- The maximality invariant. Every descent at pair `(p, p+1)` with
    `p + 1 < bound` has `p + 1 ≤ best.toInt`. -/
private def max_inv (arr : RustSlice i64) (best : i64) (bound : Nat) : Prop :=
  ∀ p : Nat, p + 1 < bound → ∀ (hp : p + 1 < arr.val.size),
    arr.val[p + 1]'hp < arr.val[p]'(Nat.lt_of_succ_lt hp) →
    ((p + 1 : Nat) : Int) ≤ best.toInt

/-- Strong correctness of `scan_at`. Given the invariants hold for input
    `best` at bound `i.toNat`, they hold for output `r` at bound
    `arr.val.size`. -/
private theorem scan_at_correct_aux (arr : RustSlice i64) (h_size : arr.val.size < 2^63) :
    ∀ (m : Nat) (i : usize) (best : i64) (r : i64),
      arr.val.size - i.toNat ≤ m →
      1 ≤ i.toNat →
      i.toNat ≤ arr.val.size →
      best_inv arr best →
      max_inv arr best i.toNat →
      clever_134_can_arrange.scan_at arr i best = RustM.ok r →
      best_inv arr r ∧ max_inv arr r arr.val.size := by
  intro m
  induction m with
  | zero =>
    intro i best r hm h_lo hi_le h_binv h_minv hres
    have h_oob : arr.val.size ≤ i.toNat := by omega
    rw [sa_oob arr i best h_oob] at hres
    have h_r_eq : r = best := by
      injection hres with h1
      injection h1 with h2
      exact h2.symm
    have h_size_eq : i.toNat = arr.val.size := by omega
    rw [h_r_eq]
    refine ⟨h_binv, ?_⟩
    intro p hp_lt hp h_desc
    apply h_minv p _ hp h_desc
    rw [h_size_eq]; exact hp_lt
  | succ m ih =>
    intro i best r hm h_lo hi_le h_binv h_minv hres
    by_cases h_oob : arr.val.size ≤ i.toNat
    · rw [sa_oob arr i best h_oob] at hres
      have h_r_eq : r = best := by
        injection hres with h1
        injection h1 with h2
        exact h2.symm
      have h_size_eq : i.toNat = arr.val.size := by omega
      rw [h_r_eq]
      refine ⟨h_binv, ?_⟩
      intro p hp_lt hp h_desc
      apply h_minv p _ hp h_desc
      rw [h_size_eq]; exact hp_lt
    · have hi_lt : i.toNat < arr.val.size := Nat.lt_of_not_le h_oob
      have hi_lt_2_63 : i.toNat < 2^63 := by omega
      have h_size_lt : arr.val.size < 2^64 := arr.size_lt_usizeSize
      have h_no_ov : i.toNat + 1 < 2^64 := by omega
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 :=
        usize_add_one_toNat i h_no_ov
      have h_i1_lo : 1 ≤ (i + 1).toNat := by rw [h_i1_toNat]; omega
      have h_i1_le : (i + 1).toNat ≤ arr.val.size := by rw [h_i1_toNat]; omega
      have h_m_le : arr.val.size - (i + 1).toNat ≤ m := by rw [h_i1_toNat]; omega
      -- Decompose the i.toNat = p+1 form: i.toNat ≥ 1 so let p = i.toNat - 1.
      have hp_def : (i.toNat - 1) + 1 = i.toNat := by omega
      have h_pair_lt : (i.toNat - 1) + 1 < arr.val.size := by rw [hp_def]; exact hi_lt
      have h_idx_a : arr.val[(i.toNat - 1) + 1]'h_pair_lt = arr.val[i.toNat]'hi_lt := by
        congr 1
      have h_idx_b : arr.val[i.toNat - 1]'(Nat.lt_of_succ_lt h_pair_lt) =
                     arr.val[i.toNat - 1]'(by omega) := rfl
      by_cases h_desc : arr.val[i.toNat]'hi_lt < arr.val[i.toNat - 1]'(by omega)
      · -- Descent branch: new best = USize64.toInt64 i.
        rw [sa_descent arr i best h_lo hi_lt h_desc] at hres
        -- New best is a valid descent.
        have h_new_toInt : (USize64.toInt64 i).toInt = (i.toNat : Int) :=
          USize64_toInt64_toInt i hi_lt_2_63
        have h_new_binv : best_inv arr (USize64.toInt64 i) := by
          right
          refine ⟨i.toNat - 1, h_pair_lt, ?_, ?_⟩
          · rw [h_new_toInt]; push_cast; omega
          · rw [h_idx_a, h_idx_b]; exact h_desc
        -- New best is ≥ old best, so the maximality invariant is preserved + extended.
        have h_new_minv : max_inv arr (USize64.toInt64 i) (i + 1).toNat := by
          intro p hp_lt hp h_desc_p
          rw [h_i1_toNat] at hp_lt
          by_cases h_p_eq : p + 1 = i.toNat
          · -- p+1 = i.toNat: descent index = i.toNat = new best
            rw [h_new_toInt, h_p_eq]; exact Int.le_refl _
          · -- p+1 < i.toNat: by h_minv, p+1 ≤ old best.toInt.
            -- Then p+1 ≤ old best.toInt ≤ i.toNat (since old best is -1 or a descent < i.toNat).
            have h_p_lt : p + 1 < i.toNat := by omega
            have h_old_le := h_minv p h_p_lt hp h_desc_p
            rw [h_new_toInt]
            -- Need (p+1 : Int) ≤ i.toNat. We have p+1 < i.toNat as naturals.
            push_cast; omega
        exact ih (i + 1) (USize64.toInt64 i) r h_m_le h_i1_lo h_i1_le h_new_binv h_new_minv hres
      · -- Normal branch: best unchanged.
        have h_le : arr.val[i.toNat - 1]'(by omega) ≤ arr.val[i.toNat]'hi_lt := by
          rcases Int.lt_or_le (arr.val[i.toNat]'hi_lt).toInt
                              (arr.val[i.toNat - 1]'(by omega)).toInt with h | h
          · exfalso; apply h_desc; exact Int64.lt_iff_toInt_lt.mpr h
          · exact Int64.le_iff_toInt_le.mpr h
        rw [sa_normal arr i best h_lo hi_lt h_le] at hres
        -- best invariant unchanged.
        -- Maximality invariant: extends to (i+1).toNat, since the only new pair
        -- (p+1 = i.toNat) is not a descent.
        have h_new_minv : max_inv arr best (i + 1).toNat := by
          intro p hp_lt hp h_desc_p
          rw [h_i1_toNat] at hp_lt
          by_cases h_p_eq : p + 1 = i.toNat
          · -- p+1 = i.toNat: descent at this position. But we just proved no descent.
            exfalso
            -- h_desc_p : arr[p+1] < arr[p]
            -- After rewriting with h_p_eq: arr[i.toNat] < arr[i.toNat - 1]
            -- But h_le : arr[i.toNat - 1] ≤ arr[i.toNat]. Contradiction.
            have h_p_eq_pred : p = i.toNat - 1 := by omega
            subst h_p_eq_pred
            rw [h_idx_a, h_idx_b] at h_desc_p
            have h_lt_int : (arr.val[i.toNat]'hi_lt).toInt <
                            (arr.val[i.toNat - 1]'(by omega)).toInt :=
              Int64.lt_iff_toInt_lt.mp h_desc_p
            have h_le_int : (arr.val[i.toNat - 1]'(by omega)).toInt ≤
                            (arr.val[i.toNat]'hi_lt).toInt :=
              Int64.le_iff_toInt_le.mp h_le
            omega
          · have h_p_lt : p + 1 < i.toNat := by omega
            exact h_minv p h_p_lt hp h_desc_p
        exact ih (i + 1) best r h_m_le h_i1_lo h_i1_le h_binv h_new_minv hres

/-! ## Top-level unfolding lemmas for `can_arrange`. -/

/-- When `size < 2`, `can_arrange` short-circuits to `-1`. -/
private theorem can_arrange_small (arr : RustSlice i64) (h : arr.val.size < 2) :
    clever_134_can_arrange.can_arrange arr = RustM.ok (-1 : i64) := by
  unfold clever_134_can_arrange.can_arrange
  have h_size_lt : arr.val.size < 2^64 := arr.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat arr.val.size).toNat = arr.val.size := n_val_toNat arr
  have h_cond : decide (USize64.ofNat arr.val.size < (2 : usize)) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.lt_iff_toNat_lt, h_ofNat, usize_two_toNat]
    exact h
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.lt, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- When `size ≥ 2`, `can_arrange` delegates to `scan_at arr 1 (-1)`. -/
private theorem can_arrange_large (arr : RustSlice i64) (h : 2 ≤ arr.val.size) :
    clever_134_can_arrange.can_arrange arr =
      clever_134_can_arrange.scan_at arr (1 : usize) (-1 : i64) := by
  unfold clever_134_can_arrange.can_arrange
  have h_size_lt : arr.val.size < 2^64 := arr.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat arr.val.size).toNat = arr.val.size := n_val_toNat arr
  have h_cond : decide (USize64.ofNat arr.val.size < (2 : usize)) = false := by
    rw [decide_eq_false_iff_not]
    intro hlt
    rw [USize64.lt_iff_toNat_lt, h_ofNat, usize_two_toNat] at hlt
    omega
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.lt, pure_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte]

/-! ## Theorem obligations. -/

/-- Claim 1 (witness): when the result is not `-1`, it encodes a valid index
    `k + 1 ∈ [1, arr.size)` at which the slice descends (`arr[k+1] < arr[k]`).

    Captures the proptest `result_is_a_descending_position`: `r ≥ 1`,
    `(r as usize) < arr.len()`, and `arr[r] < arr[r-1]`. The precondition
    `arr.val.size < 2^63` ensures the `i as i64` cast performed inside
    `scan_at` faithfully encodes the recursion index as a non-negative
    `i64`, so the returned `r` actually corresponds to a usize index. -/
theorem result_is_descending_position
    (arr : RustSlice i64) (r : i64)
    (h_size : arr.val.size < 2^63)
    (h_res : clever_134_can_arrange.can_arrange arr = RustM.ok r)
    (h_ne : r ≠ (-1 : i64)) :
    ∃ k : Nat, ∃ (hk1 : k + 1 < arr.val.size),
      r.toInt = ((k : Int) + 1) ∧
      arr.val[k+1]'hk1 < arr.val[k]'(Nat.lt_of_succ_lt hk1) := by
  by_cases h_small : arr.val.size < 2
  · exfalso
    rw [can_arrange_small arr h_small] at h_res
    apply h_ne
    injection h_res with h1
    injection h1 with h2
    exact h2.symm
  · have h_large : 2 ≤ arr.val.size := Nat.le_of_not_lt h_small
    rw [can_arrange_large arr h_large] at h_res
    have h_one_toNat : (1 : usize).toNat = 1 := usize_one_toNat
    have h_one_lo : 1 ≤ (1 : usize).toNat := by rw [h_one_toNat]; omega
    have h_one_le : (1 : usize).toNat ≤ arr.val.size := by rw [h_one_toNat]; omega
    have h_binv : best_inv arr (-1 : i64) := Or.inl rfl
    have h_minv : max_inv arr (-1 : i64) (1 : usize).toNat := by
      intro p hp_lt hp h_desc
      rw [h_one_toNat] at hp_lt
      omega
    obtain ⟨h_r_binv, _⟩ :=
      scan_at_correct_aux arr h_size arr.val.size (1 : usize) (-1 : i64) r
        (by omega) h_one_lo h_one_le h_binv h_minv h_res
    rcases h_r_binv with h_r_eq | ⟨p, hp, h_toInt, h_desc⟩
    · exact absurd h_r_eq h_ne
    · refine ⟨p, hp, ?_, h_desc⟩
      rw [h_toInt]

/-- Claim 2 (maximality): when the result is not `-1`, no descending adjacent
    pair exists strictly past the encoded index. Equivalently, the suffix
    starting at index `r.toInt.toNat + 1` is non-decreasing.

    Captures the proptest `result_is_the_largest_descending_position`:
    `for j in (r+1)..arr.len() { prop_assert!(arr[j] >= arr[j-1]) }`, which
    in pair-by-first-index form is `∀ k ≥ r, arr[k] ≤ arr[k+1]`. -/
theorem result_is_largest_descending_position
    (arr : RustSlice i64) (r : i64)
    (h_size : arr.val.size < 2^63)
    (h_res : clever_134_can_arrange.can_arrange arr = RustM.ok r)
    (h_ne : r ≠ (-1 : i64)) :
    ∀ k : Nat, r.toInt.toNat ≤ k → ∀ (hk1 : k + 1 < arr.val.size),
      arr.val[k]'(Nat.lt_of_succ_lt hk1) ≤ arr.val[k+1]'hk1 := by
  by_cases h_small : arr.val.size < 2
  · exfalso
    rw [can_arrange_small arr h_small] at h_res
    apply h_ne
    injection h_res with h1
    injection h1 with h2
    exact h2.symm
  · have h_large : 2 ≤ arr.val.size := Nat.le_of_not_lt h_small
    rw [can_arrange_large arr h_large] at h_res
    have h_one_toNat : (1 : usize).toNat = 1 := usize_one_toNat
    have h_one_lo : 1 ≤ (1 : usize).toNat := by rw [h_one_toNat]; omega
    have h_one_le : (1 : usize).toNat ≤ arr.val.size := by rw [h_one_toNat]; omega
    have h_binv : best_inv arr (-1 : i64) := Or.inl rfl
    have h_minv : max_inv arr (-1 : i64) (1 : usize).toNat := by
      intro p hp_lt hp h_desc
      rw [h_one_toNat] at hp_lt
      omega
    obtain ⟨h_r_binv, h_r_minv⟩ :=
      scan_at_correct_aux arr h_size arr.val.size (1 : usize) (-1 : i64) r
        (by omega) h_one_lo h_one_le h_binv h_minv h_res
    intro k hk_ge hk1
    -- Suppose for contradiction arr[k+1] < arr[k].
    by_cases h_le : arr.val[k]'(Nat.lt_of_succ_lt hk1) ≤ arr.val[k+1]'hk1
    · exact h_le
    · exfalso
      have h_desc_kp : arr.val[k+1]'hk1 < arr.val[k]'(Nat.lt_of_succ_lt hk1) := by
        rcases Int.lt_or_le (arr.val[k+1]'hk1).toInt
                            (arr.val[k]'(Nat.lt_of_succ_lt hk1)).toInt with hh | hh
        · exact Int64.lt_iff_toInt_lt.mpr hh
        · exfalso; apply h_le; exact Int64.le_iff_toInt_le.mpr hh
      -- By maximality, k + 1 ≤ r.toInt.
      have h_kp1_le_r := h_r_minv k hk1 hk1 h_desc_kp
      -- From h_r_binv: r = -1 or r.toInt = p+1 for some descent.
      rcases h_r_binv with h_r_eq | ⟨p, hp, h_toInt, _⟩
      · exact absurd h_r_eq h_ne
      · -- r.toInt = p + 1 ≥ 1. So r.toInt.toNat = p + 1.
        have h_r_toInt_nat : r.toInt.toNat = p + 1 := by
          rw [h_toInt]; push_cast; omega
        rw [h_r_toInt_nat] at hk_ge
        -- hk_ge : p + 1 ≤ k
        -- h_kp1_le_r : (k+1 : Int) ≤ r.toInt = p + 1
        have : (k + 1 : Int) ≤ (p + 1 : Int) := by rw [← h_toInt]; exact h_kp1_le_r
        push_cast at this
        omega

/-- Claim 3a (sentinel completeness): a non-decreasing slice returns `-1`.

    Captures the forward direction of `minus_one_iff_non_decreasing`:
    when every adjacent pair satisfies `arr[j] ≥ arr[j-1]`, `scan_at`
    never updates `best`, so the returned sentinel is the initial `-1`.
    No size precondition is needed: the only path where `best` could
    change is taken zero times. -/
theorem non_decreasing_returns_minus_one
    (arr : RustSlice i64) (h_nondec : is_nondec arr) :
    clever_134_can_arrange.can_arrange arr = RustM.ok (-1 : i64) := by
  by_cases h_small : arr.val.size < 2
  · exact can_arrange_small arr h_small
  · have h_large : 2 ≤ arr.val.size := Nat.le_of_not_lt h_small
    rw [can_arrange_large arr h_large]
    have h_one_toNat : (1 : usize).toNat = 1 := usize_one_toNat
    have h_one_lo : 1 ≤ (1 : usize).toNat := by rw [h_one_toNat]; omega
    apply scan_at_no_descent_aux arr arr.val.size (1 : usize) (-1 : i64)
      (by omega) h_one_lo
    intro k hk hk1
    -- is_nondec gives the conclusion for any k.
    exact h_nondec k hk1

/-- Claim 3b (sentinel soundness): returning `-1` implies the slice is
    non-decreasing.

    Captures the backward direction of `minus_one_iff_non_decreasing`.
    No size precondition is needed: because `arr.val.size < 2^64`, every
    in-scope index `i` satisfies `i < 2^64 - 1`, so the cast `i as i64`
    never produces `-1`. Hence the result equals `-1` only if `best` was
    never updated, which forces every adjacent pair to be non-descending. -/
theorem minus_one_implies_non_decreasing
    (arr : RustSlice i64)
    (h_res : clever_134_can_arrange.can_arrange arr = RustM.ok (-1 : i64)) :
    is_nondec arr := by
  by_cases h_small : arr.val.size < 2
  · -- is_nondec is vacuous: no j with j+1 < size when size < 2.
    intro j hj1
    omega
  · have h_large : 2 ≤ arr.val.size := Nat.le_of_not_lt h_small
    rw [can_arrange_large arr h_large] at h_res
    have h_one_toNat : (1 : usize).toNat = 1 := usize_one_toNat
    have h_one_lo : 1 ≤ (1 : usize).toNat := by rw [h_one_toNat]; omega
    have h_nondec_from_1 :=
      scan_at_minus_one_imp_no_descent_aux arr arr.val.size (1 : usize)
        (by omega) h_one_lo h_res
    intro j hj1
    apply h_nondec_from_1 j _ hj1
    rw [h_one_toNat]; omega

end Clever_134_can_arrangeObligations
