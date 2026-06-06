-- Companion obligations file for the `clever_061_derivative` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_061_derivative

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_061_derivativeObligations

/-! ## Helpers (transferred from rolling_max / sum_product / mean_absolute_deviation /
    rescale_to_unit references). -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide

private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide

private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

/-- `Nat.toInt64` of a Nat below `2^63` interprets back to the same Int.
    Transferred verbatim from `clever_004_mean_absolute_deviation`. -/
private theorem Nat_toInt64_toInt (n : Nat) (h : n < 2^63) :
    (n.toInt64).toInt = (n : Int) := by
  have h_n_lt_2_64 : n < 2^64 := Nat.lt_trans h (by decide)
  have h_bv_toNat : n.toInt64.toBitVec.toNat = n := by
    show (BitVec.ofNat 64 n).toNat = n
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt h_n_lt_2_64
  rw [Int64.toInt, BitVec.toInt_eq_toNat_bmod, h_bv_toNat]
  unfold Int.bmod
  have h_mod : ((n : Int) % ((2^64 : Nat) : Int)) = (n : Int) := by
    rw [show (((2^64 : Nat)) : Int) = (2^64 : Int) from by norm_cast]
    exact Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le _)
                            (by exact_mod_cast (Nat.lt_trans h (by decide : (2^63 : Nat) < 2^64)))
  rw [h_mod]
  show (if (n : Int) < (((2^64 : Nat) : Int) + 1) / 2 then (n : Int) else (n : Int) - ((2^64 : Nat) : Int)) = (n : Int)
  have h_half_eq : (((2^64 : Nat) : Int) + 1) / 2 = 2^63 := by decide
  rw [h_half_eq]
  have h_cond : (n : Int) < (2^63 : Int) := by exact_mod_cast h
  rw [if_pos h_cond]

/-- `(USize64.toInt64 i).toInt = (i.toNat : Int)` when `i.toNat < 2^63`. -/
private theorem usize_toInt64_toInt (i : usize) (h : i.toNat < 2^63) :
    ((USize64.toInt64 i)).toInt = (i.toNat : Int) := by
  show (i.toNat.toInt64).toInt = (i.toNat : Int)
  exact Nat_toInt64_toInt i.toNat h

/-! ## Push helper for Vec append-one (transferred from rolling_max / rescale_to_unit). -/

/-- Push a single element onto a Vec. -/
private def push_one (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec i64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

/-! ## Step lemmas for `build_at`. -/

/-- Out-of-bounds step: when `i.toNat ≥ c.val.size`, `build_at` returns `acc`. -/
private theorem build_at_oob (c : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : c.val.size ≤ i.toNat) :
    clever_061_derivative.build_at c i acc = RustM.ok acc := by
  conv => lhs; unfold clever_061_derivative.build_at
  have h_ofNat : (USize64.ofNat c.val.size).toNat = c.val.size :=
    USize64.toNat_ofNat_of_lt' c.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat c.val.size ≤ i) = true := by
    rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- Recursion step: when `i.toNat < c.val.size`, the cast is safe, the
    multiplication does not overflow, and the accumulator has room for one
    more element, the body reduces to a call with `i + 1` and `push_one acc`. -/
private theorem build_at_step (c : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < c.val.size)
    (hno_mul : ¬ Int64.mulOverflow (USize64.toInt64 i) (c.val[i.toNat]'hi))
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_061_derivative.build_at c i acc =
      clever_061_derivative.build_at c (i + 1)
        (push_one acc ((USize64.toInt64 i) * (c.val[i.toNat]'hi)) h_acc) := by
  conv => lhs; unfold clever_061_derivative.build_at
  have h_size_lt : c.val.size < USize64.size := c.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat c.val.size).toNat = c.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat c.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]
    omega
  have h_idx : (c[i]_? : RustM i64) = RustM.ok (c.val[i.toNat]'hi) := by
    show (if h : i.toNat < c.val.size then pure (c.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (c.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  -- Cast: cast_op i = pure (USize64.toInt64 i)
  have h_cast : (rust_primitives.hax.cast_op i : RustM i64) =
                  pure (USize64.toInt64 i) := rfl
  -- Mul: (USize64.toInt64 i) *? c[i] = pure ((USize64.toInt64 i) * c[i])
  have h_no_mul_bv :
      BitVec.smulOverflow (USize64.toInt64 i).toBitVec
                          (c.val[i.toNat]'hi).toBitVec = false := by
    have hno' : ¬ (BitVec.smulOverflow (USize64.toInt64 i).toBitVec
                                       (c.val[i.toNat]'hi).toBitVec = true) := hno_mul
    cases hb : BitVec.smulOverflow (USize64.toInt64 i).toBitVec
                                    (c.val[i.toNat]'hi).toBitVec with
    | false => rfl
    | true => exact absurd hb hno'
  have h_mul_eq :
      ((USize64.toInt64 i) *? (c.val[i.toNat]'hi) : RustM i64) =
        RustM.ok ((USize64.toInt64 i) * (c.val[i.toNat]'hi)) := by
    show (rust_primitives.ops.arith.Mul.mul (USize64.toInt64 i) (c.val[i.toNat]'hi)
          : RustM i64) = _
    show (if BitVec.smulOverflow (USize64.toInt64 i).toBitVec
                                  (c.val[i.toNat]'hi).toBitVec
          then (.fail .integerOverflow : RustM i64)
          else pure ((USize64.toInt64 i) * (c.val[i.toNat]'hi))) = _
    rw [h_no_mul_bv]; rfl
  -- i+1 doesn't overflow
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
  have h_add_eq : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
    show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
    show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
          then (.fail .integerOverflow : RustM usize)
          else pure (i + 1)) = _
    rw [h_no_bv_i]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_cast, h_idx, h_mul_eq]
  -- Reduce unsize and extend_from_slice using the 1-chunk pattern.
  rw [show (rust_primitives.unsize
            (RustArray.ofVec #v[((USize64.toInt64 i) * (c.val[i.toNat]'hi))]
              : RustArray i64 1)
            : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[((USize64.toInt64 i) * (c.val[i.toNat]'hi))],
                       one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size :
      acc.val.size +
        (#[((USize64.toInt64 i) * (c.val[i.toNat]'hi))] : Array i64).size
        < USize64.size := by
    show acc.val.size + 1 < USize64.size
    exact h_acc
  rw [show (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
              ⟨#[((USize64.toInt64 i) * (c.val[i.toNat]'hi))], one_lt_usize_size⟩
            : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
        = RustM.ok (push_one acc ((USize64.toInt64 i) * (c.val[i.toNat]'hi)) h_acc)
        from by
      unfold alloc.vec.Impl_2.extend_from_slice
      rw [dif_pos h_app_size]
      rfl]
  simp only [RustM_ok_bind]
  rw [h_add_eq]
  rfl

/-! ## Strong-induction lemma for `build_at`.

Invariant: at each recursive call, `acc.val.size + 1 = i.toNat` (so `acc`
stores the first `i.toNat - 1` derivative coefficients), and for every
`j < acc.val.size`, `acc[j].toInt = (j + 1) * c[j + 1].toInt`.

The recursion is launched at `i = 1`, `acc = []`, satisfying this invariant
trivially. At termination, `i.toNat = c.val.size`, so the final
`v.val.size + 1 = c.val.size`, i.e., `v.val.size = c.val.size - 1`. -/

private theorem build_at_correct
    (c : RustSlice i64)
    (hsize_fits : c.val.size ≤ 2^63)
    (hmul_fit : ∀ (i : Nat) (h1 : 1 ≤ i) (h2 : i < c.val.size),
        -(2^63 : Int) ≤ (i : Int) * (c.val[i]'h2).toInt ∧
        (i : Int) * (c.val[i]'h2).toInt < 2^63) :
    ∀ (m : Nat) (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global),
      c.val.size - i.toNat ≤ m →
      1 ≤ i.toNat →
      i.toNat ≤ c.val.size →
      acc.val.size + 1 = i.toNat →
      (∀ (j : Nat) (hj : j < acc.val.size) (hj_n : j + 1 < c.val.size),
          (acc.val[j]'hj).toInt = (j + 1 : Int) * (c.val[j + 1]'hj_n).toInt) →
      ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
        clever_061_derivative.build_at c i acc = RustM.ok v ∧
        v.val.size + 1 = c.val.size ∧
        (∀ (j : Nat) (hj_v : j < v.val.size) (hj_n : j + 1 < c.val.size),
            (v.val[j]'hj_v).toInt = (j + 1 : Int) * (c.val[j + 1]'hj_n).toInt) := by
  intro m
  induction m with
  | zero =>
    intro i acc hm hi_pos hi_le h_acc_size h_acc_inv
    have hi_eq : i.toNat = c.val.size := by omega
    have hi_ge : c.val.size ≤ i.toNat := by omega
    refine ⟨acc, build_at_oob c i acc hi_ge, ?_, ?_⟩
    · rw [h_acc_size, hi_eq]
    · intro j hj_v hj_n
      exact h_acc_inv j hj_v hj_n
  | succ m ih =>
    intro i acc hm hi_pos hi_le h_acc_size h_acc_inv
    by_cases hi_ge : c.val.size ≤ i.toNat
    · have hi_eq : i.toNat = c.val.size := by omega
      refine ⟨acc, build_at_oob c i acc hi_ge, ?_, ?_⟩
      · rw [h_acc_size, hi_eq]
      · intro j hj_v hj_n
        exact h_acc_inv j hj_v hj_n
    · have hi_lt : i.toNat < c.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : c.val.size < USize64.size := c.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i_lt_2_63 : i.toNat < 2^63 := by omega
      -- Cast value: USize64.toInt64 i has toInt = i.toNat.
      have h_cast_toInt : (USize64.toInt64 i).toInt = (i.toNat : Int) :=
        usize_toInt64_toInt i h_i_lt_2_63
      -- Use hmul_fit at index i.toNat
      have h_mul_fit_i := hmul_fit i.toNat hi_pos hi_lt
      have h_mul_bound :
          -(2^63 : Int) ≤ (USize64.toInt64 i).toInt * (c.val[i.toNat]'hi_lt).toInt ∧
          (USize64.toInt64 i).toInt * (c.val[i.toNat]'hi_lt).toInt < 2^63 := by
        rw [h_cast_toInt]
        exact h_mul_fit_i
      -- No mul overflow
      have hno_mul :
          ¬ Int64.mulOverflow (USize64.toInt64 i) (c.val[i.toNat]'hi_lt) := by
        intro hov
        rw [Int64.mulOverflow_iff] at hov
        rcases hov with hov_pos | hov_neg
        · have := h_mul_bound.2; omega
        · have := h_mul_bound.1; omega
      -- Accumulator has room (size + 1 < USize64.size).
      have h_acc_succ : acc.val.size + 1 < USize64.size := by
        rw [h_acc_size, h_usize_size]; omega
      -- Apply step lemma.
      have h_step := build_at_step c i acc hi_lt hno_mul h_acc_succ
      rw [h_step]
      -- New accumulator: push_one with x := (USize64.toInt64 i) * c[i.toNat]
      let new_x : i64 := (USize64.toInt64 i) * (c.val[i.toNat]'hi_lt)
      have h_new_toInt :
          new_x.toInt = (i.toNat : Int) * (c.val[i.toNat]'hi_lt).toInt := by
        show ((USize64.toInt64 i) * (c.val[i.toNat]'hi_lt)).toInt = _
        rw [Int64.toInt_mul_of_not_mulOverflow hno_mul, h_cast_toInt]
      -- IH application
      have h_m_le : c.val.size - (i + 1).toNat ≤ m := by rw [h_i1]; omega
      have h_i1_pos : 1 ≤ (i + 1).toNat := by rw [h_i1]; omega
      have h_i1_le : (i + 1).toNat ≤ c.val.size := by rw [h_i1]; omega
      have h_acc'_size :
          (push_one acc new_x h_acc_succ).val.size + 1 = (i + 1).toNat := by
        show (acc.val ++ #[new_x]).size + 1 = (i + 1).toNat
        rw [Array.size_append, h_i1]
        show acc.val.size + 1 + 1 = i.toNat + 1
        rw [h_acc_size]
      have h_acc'_inv :
          ∀ (j : Nat) (hj : j < (push_one acc new_x h_acc_succ).val.size)
            (hj_n : j + 1 < c.val.size),
          ((push_one acc new_x h_acc_succ).val[j]'hj).toInt =
            (j + 1 : Int) * (c.val[j + 1]'hj_n).toInt := by
        intro j hj hj_n
        show ((acc.val ++ #[new_x])[j]'hj).toInt = _
        by_cases hj_lt : j < acc.val.size
        · rw [Array.getElem_append_left hj_lt]
          exact h_acc_inv j hj_lt hj_n
        · have h_size_raw : (acc.val ++ #[new_x]).size = acc.val.size + 1 := by
            rw [Array.size_append]; rfl
          have hj_eq : j = acc.val.size := by
            have : j < acc.val.size + 1 := by rw [← h_size_raw]; exact hj
            omega
          subst hj_eq
          rw [Array.getElem_append_right (Nat.le_refl _)]
          simp only [Nat.sub_self]
          show (#[new_x][0] : i64).toInt = _
          show new_x.toInt = _
          rw [h_new_toInt]
          have h_idx_eq : acc.val.size + 1 = i.toNat := h_acc_size
          have h_c_eq :
              (c.val[acc.val.size + 1]'hj_n) = (c.val[i.toNat]'hi_lt) :=
            getElem_congr_idx h_idx_eq
          rw [h_c_eq]
          -- Goal: (i.toNat : Int) * c[i.toNat].toInt = (acc.val.size + 1 : Int) * c[i.toNat].toInt
          have h_cast_eq : (i.toNat : Int) = ((acc.val.size : Int) + 1) := by
            rw [← h_idx_eq]; push_cast; rfl
          rw [h_cast_eq]
      exact ih (i + 1) (push_one acc new_x h_acc_succ)
        h_m_le h_i1_pos h_i1_le h_acc'_size h_acc'_inv

/-! ## Top-level theorems. -/

/-- Boundary case: when the input slice is empty, the function returns the
    empty `Vec`. -/
theorem derivative_empty
    (numbers : RustSlice i64) (hempty : numbers.val.size = 0) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_061_derivative.derivative numbers = RustM.ok v ∧
      v.val.size = 0 := by
  unfold clever_061_derivative.derivative
  -- is_empty returns true.
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' numbers.size_lt_usizeSize
  have h_eq_zero : (USize64.ofNat numbers.val.size) = (0 : usize) := by
    apply USize64.toNat_inj.mp
    rw [h_ofNat]; exact hempty
  have h_is_empty_true :
      (core_models.slice.Impl.is_empty i64 numbers : RustM Bool) = RustM.ok true := by
    show (do
      let __do_lift ← (core_models.slice.Impl.len i64 numbers : RustM usize)
      __do_lift ==? (0 : usize) : RustM Bool) = RustM.ok true
    show (do
      let __do_lift ← (pure (USize64.ofNat numbers.val.size) : RustM usize)
      pure (decide (__do_lift = (0 : usize))) : RustM Bool) = RustM.ok true
    simp only [pure_bind]
    rw [h_eq_zero]
    rfl
  rw [h_is_empty_true, RustM_ok_bind]
  simp only [↓reduceIte]
  refine ⟨⟨(List.nil : List i64).toArray, by grind⟩, ?_, ?_⟩
  · rfl
  · rfl

/-- Auxiliary: full correctness of `derivative` under the preconditions.
    Combines the length and elementwise contracts. -/
private theorem derivative_aux
    (numbers : RustSlice i64)
    (hsize_fits : numbers.val.size ≤ 2 ^ 63)
    (hmul_fit : ∀ (i : Nat) (h1 : 1 ≤ i) (h2 : i < numbers.val.size),
        -(2 ^ 63 : Int) ≤ (i : Int) * (numbers.val[i]'h2).toInt ∧
        (i : Int) * (numbers.val[i]'h2).toInt < 2 ^ 63) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_061_derivative.derivative numbers = RustM.ok v ∧
      v.val.size =
        (if numbers.val.size = 0 then 0 else numbers.val.size - 1) ∧
      (∀ (k : Nat) (hk_n : k + 1 < numbers.val.size) (hk_v : k < v.val.size),
        (v.val[k]'hk_v).toInt = (k + 1 : Int) * (numbers.val[k + 1]'hk_n).toInt) := by
  by_cases hempty : numbers.val.size = 0
  · obtain ⟨v, hres, hsize⟩ := derivative_empty numbers hempty
    refine ⟨v, hres, ?_, ?_⟩
    · rw [hsize, if_pos hempty]
    · intro k hk_n hk_v
      rw [hsize] at hk_v
      omega
  · -- Non-empty case.
    have h_size_pos : 0 < numbers.val.size := Nat.pos_of_ne_zero hempty
    -- Unfold and reduce is_empty to false.
    have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
      USize64.toNat_ofNat_of_lt' numbers.size_lt_usizeSize
    have h_ne_zero : (USize64.ofNat numbers.val.size) ≠ (0 : usize) := by
      intro h_eq
      have h0 : (USize64.ofNat numbers.val.size).toNat = (0 : usize).toNat := by
        rw [h_eq]
      rw [h_ofNat] at h0
      show False
      exact hempty h0
    have h_is_empty_false :
        (core_models.slice.Impl.is_empty i64 numbers : RustM Bool) = RustM.ok false := by
      show (do
        let __do_lift ← (core_models.slice.Impl.len i64 numbers : RustM usize)
        __do_lift ==? (0 : usize) : RustM Bool) = RustM.ok false
      show (do
        let __do_lift ← (pure (USize64.ofNat numbers.val.size) : RustM usize)
        pure (decide (__do_lift = (0 : usize))) : RustM Bool) = RustM.ok false
      simp only [pure_bind]
      rw [decide_eq_false h_ne_zero]
      rfl
    -- Initial accumulator.
    let acc0 : alloc.vec.Vec i64 alloc.alloc.Global :=
      ⟨(List.nil : List i64).toArray, by grind⟩
    have h_acc0_new :
      (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
        RustM (alloc.vec.Vec i64 alloc.alloc.Global)) = RustM.ok acc0 := rfl
    -- Apply build_at_correct.
    have h_one_toNat : (1 : usize).toNat = 1 := usize_one_toNat
    have h_m_le : numbers.val.size - (1 : usize).toNat ≤ numbers.val.size := by
      rw [h_one_toNat]; omega
    have h_one_pos : 1 ≤ (1 : usize).toNat := by rw [h_one_toNat]; omega
    have h_one_le_size : (1 : usize).toNat ≤ numbers.val.size := by
      rw [h_one_toNat]; omega
    have h_acc0_size_inv : acc0.val.size + 1 = (1 : usize).toNat := by
      show 0 + 1 = (1 : usize).toNat
      rw [h_one_toNat]
    have h_acc0_inv :
        ∀ (j : Nat) (hj : j < acc0.val.size) (hj_n : j + 1 < numbers.val.size),
        (acc0.val[j]'hj).toInt = (j + 1 : Int) * (numbers.val[j + 1]'hj_n).toInt := by
      intro j hj hj_n
      exfalso
      have h_acc0_size_zero : acc0.val.size = 0 := rfl
      rw [h_acc0_size_zero] at hj
      omega
    obtain ⟨v, hres_at, h_v_size_succ, h_v_inv⟩ :=
      build_at_correct numbers hsize_fits hmul_fit
        numbers.val.size (1 : usize) acc0 h_m_le h_one_pos h_one_le_size
        h_acc0_size_inv h_acc0_inv
    -- Assemble the result.
    refine ⟨v, ?_, ?_, ?_⟩
    · -- The function returns RustM.ok v.
      unfold clever_061_derivative.derivative
      rw [h_is_empty_false, RustM_ok_bind]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [h_acc0_new, RustM_ok_bind]
      exact hres_at
    · rw [if_neg hempty]; omega
    · intro k hk_n hk_v
      exact h_v_inv k hk_v hk_n

/-- Length postcondition: the output Vec has length `max(0, n - 1)`. -/
theorem derivative_length
    (numbers : RustSlice i64)
    (hsize_fits : numbers.val.size ≤ 2 ^ 63)
    (hmul_fit : ∀ (i : Nat) (h1 : 1 ≤ i) (h2 : i < numbers.val.size),
        -(2 ^ 63 : Int) ≤ (i : Int) * (numbers.val[i]'h2).toInt ∧
        (i : Int) * (numbers.val[i]'h2).toInt < 2 ^ 63) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_061_derivative.derivative numbers = RustM.ok v ∧
      v.val.size =
        (if numbers.val.size = 0 then 0 else numbers.val.size - 1) := by
  obtain ⟨v, hres, hlen, _⟩ := derivative_aux numbers hsize_fits hmul_fit
  exact ⟨v, hres, hlen⟩

/-- Coefficient formula: for every index `k` of the output,
    `result[k].toInt = (k + 1) * c[k + 1].toInt`. -/
theorem derivative_coefficient_formula
    (numbers : RustSlice i64)
    (hsize_fits : numbers.val.size ≤ 2 ^ 63)
    (hmul_fit : ∀ (i : Nat) (h1 : 1 ≤ i) (h2 : i < numbers.val.size),
        -(2 ^ 63 : Int) ≤ (i : Int) * (numbers.val[i]'h2).toInt ∧
        (i : Int) * (numbers.val[i]'h2).toInt < 2 ^ 63) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_061_derivative.derivative numbers = RustM.ok v ∧
      ∀ (k : Nat) (hk_n : k + 1 < numbers.val.size) (hk_v : k < v.val.size),
        (v.val[k]'hk_v).toInt = (k + 1 : Int) * (numbers.val[k + 1]'hk_n).toInt := by
  obtain ⟨v, hres, _, hinv⟩ := derivative_aux numbers hsize_fits hmul_fit
  exact ⟨v, hres, hinv⟩

end Clever_061_derivativeObligations
