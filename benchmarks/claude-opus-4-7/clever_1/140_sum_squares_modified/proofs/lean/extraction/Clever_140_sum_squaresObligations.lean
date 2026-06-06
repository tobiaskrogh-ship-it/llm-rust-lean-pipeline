-- Companion obligations file for the `clever_140_sum_squares` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_140_sum_squares

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_140_sum_squaresObligations

/-! ## Integer-valued specification

The Rust source documents `sum_squares(lst)` as the elementwise sum after
applying an index-dependent transform: at index `i` with element `v`,
`v*v` if `i % 3 == 0`; otherwise `v*v*v` if `i % 4 == 0`; otherwise `v`. -/

/-- Per-element transform on `Int`. -/
private def transform (v : Int) (i : Nat) : Int :=
  if i % 3 = 0 then v * v
  else if i % 4 = 0 then v * v * v
  else v

/-- Integer-valued prefix sum of the transformed elements. -/
private def transform_sum_int (l : RustSlice i64) : Nat → Int
  | 0     => 0
  | k + 1 =>
      transform_sum_int l k +
        (if h : k < l.val.size then
          transform (l.val[k]'h).toInt k
        else 0)

/-! ## Standard helpers. -/

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

/-! ## `usize`-modulo helpers for divisors 3 and 4. -/

/-- `(i %? 3 : RustM usize) = RustM.ok (i % 3)`. -/
private theorem usize_rem_three_eq (i : usize) :
    (i %? (3 : usize) : RustM usize) = RustM.ok (i % 3) := by
  show (rust_primitives.ops.arith.Rem.rem i (3 : usize) : RustM usize) =
        RustM.ok (i % 3)
  show (if (3 : usize) = 0 then (.fail .divisionByZero : RustM usize)
        else pure (i % 3)) = _
  rw [if_neg (by decide : (3 : usize) ≠ 0)]
  rfl

/-- `(i %? 4 : RustM usize) = RustM.ok (i % 4)`. -/
private theorem usize_rem_four_eq (i : usize) :
    (i %? (4 : usize) : RustM usize) = RustM.ok (i % 4) := by
  show (rust_primitives.ops.arith.Rem.rem i (4 : usize) : RustM usize) =
        RustM.ok (i % 4)
  show (if (4 : usize) = 0 then (.fail .divisionByZero : RustM usize)
        else pure (i % 4)) = _
  rw [if_neg (by decide : (4 : usize) ≠ 0)]
  rfl

/-- `(i % 3 : usize).toNat = i.toNat % 3`. -/
private theorem usize_mod_three_toNat (i : usize) :
    (i % 3 : usize).toNat = i.toNat % 3 := by
  show (i.toBitVec % (3 : usize).toBitVec).toNat = i.toNat % 3
  rw [BitVec.toNat_umod]
  rfl

/-- `(i % 4 : usize).toNat = i.toNat % 4`. -/
private theorem usize_mod_four_toNat (i : usize) :
    (i % 4 : usize).toNat = i.toNat % 4 := by
  show (i.toBitVec % (4 : usize).toBitVec).toNat = i.toNat % 4
  rw [BitVec.toNat_umod]
  rfl

private theorem usize_mod_three_eq_zero_iff (i : usize) :
    (i % 3 : usize) = (0 : usize) ↔ i.toNat % 3 = 0 := by
  constructor
  · intro h
    have ht : (i % 3 : usize).toNat = (0 : usize).toNat := by rw [h]
    rw [usize_mod_three_toNat, usize_zero_toNat] at ht
    exact ht
  · intro h
    apply USize64.toNat_inj.mp
    rw [usize_mod_three_toNat, usize_zero_toNat]
    exact h

private theorem usize_mod_four_eq_zero_iff (i : usize) :
    (i % 4 : usize) = (0 : usize) ↔ i.toNat % 4 = 0 := by
  constructor
  · intro h
    have ht : (i % 4 : usize).toNat = (0 : usize).toNat := by rw [h]
    rw [usize_mod_four_toNat, usize_zero_toNat] at ht
    exact ht
  · intro h
    apply USize64.toNat_inj.mp
    rw [usize_mod_four_toNat, usize_zero_toNat]
    exact h

/-! ## Spec helpers. -/

/-- Step lemma: when `k < l.val.size`, the `dite` reduces. -/
private theorem transform_sum_int_succ
    (l : RustSlice i64) (k : Nat) (hk : k < l.val.size) :
    transform_sum_int l (k + 1) =
      transform_sum_int l k + transform (l.val[k]'hk).toInt k := by
  show transform_sum_int l k
        + (if h : k < l.val.size then
            transform (l.val[k]'h).toInt k
          else 0)
       = transform_sum_int l k + transform (l.val[k]'hk).toInt k
  rw [dif_pos hk]

/-- `0 ≤ x * x` for `x : Int`. -/
private theorem int_sq_nneg (x : Int) : 0 ≤ x * x := by
  by_cases h : x < 0
  · have h1 : 0 ≤ -x := by omega
    have h2 : 0 ≤ (-x) * (-x) := Int.mul_nonneg h1 h1
    rw [Int.neg_mul_neg] at h2
    exact h2
  · have h' : 0 ≤ x := by omega
    exact Int.mul_nonneg h' h'

/-! ## i64 arithmetic step lemmas (pure-bind form). -/

private theorem i64_mul_pure (a b : i64) (h_no : ¬ Int64.mulOverflow a b) :
    (a *? b : RustM i64) = RustM.ok (a * b) := by
  have h_bv : BitVec.smulOverflow a.toBitVec b.toBitVec = false := by
    cases hb : BitVec.smulOverflow a.toBitVec b.toBitVec with
    | false => rfl
    | true => exact absurd hb h_no
  show (rust_primitives.ops.arith.Mul.mul a b : RustM i64) = RustM.ok (a * b)
  show (if BitVec.smulOverflow a.toBitVec b.toBitVec then
          (.fail .integerOverflow : RustM i64)
        else pure (a * b)) = _
  rw [h_bv]; rfl

private theorem i64_add_pure (a b : i64) (h_no : ¬ Int64.addOverflow a b) :
    (a +? b : RustM i64) = RustM.ok (a + b) := by
  have h_bv : BitVec.saddOverflow a.toBitVec b.toBitVec = false := by
    cases hb : BitVec.saddOverflow a.toBitVec b.toBitVec with
    | false => rfl
    | true => exact absurd hb h_no
  show (rust_primitives.ops.arith.Add.add a b : RustM i64) = RustM.ok (a + b)
  show (if BitVec.saddOverflow a.toBitVec b.toBitVec then
          (.fail .integerOverflow : RustM i64)
        else pure (a + b)) = _
  rw [h_bv]; rfl

/-! ## Step lemma for `sum_at` — out-of-bounds branch. -/

private theorem sum_at_oob (l : RustSlice i64) (i : usize) (acc : i64)
    (hi : l.val.size ≤ i.toNat) :
    clever_140_sum_squares.sum_at l i acc = RustM.ok acc := by
  conv => lhs; unfold clever_140_sum_squares.sum_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = true := by
    rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, h_cond, ↓reduceIte]
  rfl

/-! ## Step lemmas for `sum_at` — three dispatch cases. -/

/-- Square step: `i.toNat % 3 = 0` triggers the `v *? v` arm. -/
private theorem sum_at_sq
    (l : RustSlice i64) (i : usize) (acc : i64)
    (hi : i.toNat < l.val.size)
    (h_mod3 : i.toNat % 3 = 0)
    (h_no_mul : ¬ Int64.mulOverflow (l.val[i.toNat]'hi) (l.val[i.toNat]'hi))
    (h_no_add : ¬ Int64.addOverflow acc
                  ((l.val[i.toNat]'hi) * (l.val[i.toNat]'hi))) :
    clever_140_sum_squares.sum_at l i acc =
      clever_140_sum_squares.sum_at l (i + 1)
        (acc + (l.val[i.toNat]'hi) * (l.val[i.toNat]'hi)) := by
  conv => lhs; unfold clever_140_sum_squares.sum_at
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
  have h_imod3_eq : (i % 3 : usize) = (0 : usize) :=
    (usize_mod_three_eq_zero_iff i).mpr h_mod3
  have h_beq3 : ((i % 3 : usize) == (0 : usize)) = true := by
    rw [beq_iff_eq]; exact h_imod3_eq
  have h_urem3 := usize_rem_three_eq i
  have h_mul := i64_mul_pure (l.val[i.toNat]'hi) (l.val[i.toNat]'hi) h_no_mul
  have h_add := i64_add_pure acc ((l.val[i.toNat]'hi) * (l.val[i.toNat]'hi)) h_no_add
  have h_add_i := usize_add_one_eq i h_no_ov_i
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_urem3,
             rust_primitives.cmp.eq,
             h_beq3, h_mul, h_add, h_add_i]

/-- Cube step: `i.toNat % 3 ≠ 0` ∧ `i.toNat % 4 = 0` triggers the
    `(v *? v) *? v` arm. -/
private theorem sum_at_cube
    (l : RustSlice i64) (i : usize) (acc : i64)
    (hi : i.toNat < l.val.size)
    (h_not_mod3 : i.toNat % 3 ≠ 0)
    (h_mod4 : i.toNat % 4 = 0)
    (h_no_mul1 : ¬ Int64.mulOverflow (l.val[i.toNat]'hi) (l.val[i.toNat]'hi))
    (h_no_mul2 : ¬ Int64.mulOverflow
                    ((l.val[i.toNat]'hi) * (l.val[i.toNat]'hi))
                    (l.val[i.toNat]'hi))
    (h_no_add : ¬ Int64.addOverflow acc
                  ((l.val[i.toNat]'hi) * (l.val[i.toNat]'hi)
                    * (l.val[i.toNat]'hi))) :
    clever_140_sum_squares.sum_at l i acc =
      clever_140_sum_squares.sum_at l (i + 1)
        (acc + (l.val[i.toNat]'hi) * (l.val[i.toNat]'hi)
              * (l.val[i.toNat]'hi)) := by
  conv => lhs; unfold clever_140_sum_squares.sum_at
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
  have h_imod3_ne : (i % 3 : usize) ≠ (0 : usize) := by
    intro h_eq
    exact h_not_mod3 ((usize_mod_three_eq_zero_iff i).mp h_eq)
  have h_beq3 : ((i % 3 : usize) == (0 : usize)) = false := by
    rw [beq_eq_false_iff_ne]; exact h_imod3_ne
  have h_imod4_eq : (i % 4 : usize) = (0 : usize) :=
    (usize_mod_four_eq_zero_iff i).mpr h_mod4
  have h_beq4 : ((i % 4 : usize) == (0 : usize)) = true := by
    rw [beq_iff_eq]; exact h_imod4_eq
  have h_urem3 := usize_rem_three_eq i
  have h_urem4 := usize_rem_four_eq i
  have h_mul1 := i64_mul_pure (l.val[i.toNat]'hi) (l.val[i.toNat]'hi) h_no_mul1
  have h_mul2 := i64_mul_pure
    ((l.val[i.toNat]'hi) * (l.val[i.toNat]'hi)) (l.val[i.toNat]'hi) h_no_mul2
  have h_add := i64_add_pure acc
    ((l.val[i.toNat]'hi) * (l.val[i.toNat]'hi) * (l.val[i.toNat]'hi)) h_no_add
  have h_add_i := usize_add_one_eq i h_no_ov_i
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_urem3, h_urem4,
             rust_primitives.cmp.eq,
             h_beq3, h_beq4, h_mul1, h_mul2, h_add, h_add_i]

/-- Identity step: `i.toNat % 3 ≠ 0` ∧ `i.toNat % 4 ≠ 0` triggers the
    passthrough arm. -/
private theorem sum_at_identity
    (l : RustSlice i64) (i : usize) (acc : i64)
    (hi : i.toNat < l.val.size)
    (h_not_mod3 : i.toNat % 3 ≠ 0)
    (h_not_mod4 : i.toNat % 4 ≠ 0)
    (h_no_add : ¬ Int64.addOverflow acc (l.val[i.toNat]'hi)) :
    clever_140_sum_squares.sum_at l i acc =
      clever_140_sum_squares.sum_at l (i + 1)
        (acc + (l.val[i.toNat]'hi)) := by
  conv => lhs; unfold clever_140_sum_squares.sum_at
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
  have h_imod3_ne : (i % 3 : usize) ≠ (0 : usize) := by
    intro h_eq
    exact h_not_mod3 ((usize_mod_three_eq_zero_iff i).mp h_eq)
  have h_beq3 : ((i % 3 : usize) == (0 : usize)) = false := by
    rw [beq_eq_false_iff_ne]; exact h_imod3_ne
  have h_imod4_ne : (i % 4 : usize) ≠ (0 : usize) := by
    intro h_eq
    exact h_not_mod4 ((usize_mod_four_eq_zero_iff i).mp h_eq)
  have h_beq4 : ((i % 4 : usize) == (0 : usize)) = false := by
    rw [beq_eq_false_iff_ne]; exact h_imod4_ne
  have h_urem3 := usize_rem_three_eq i
  have h_urem4 := usize_rem_four_eq i
  have h_add := i64_add_pure acc (l.val[i.toNat]'hi) h_no_add
  have h_add_i := usize_add_one_eq i h_no_ov_i
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_urem3, h_urem4,
             rust_primitives.cmp.eq,
             h_beq3, h_beq4, h_add, h_add_i]

/-! ## Per-element no-overflow derivation from `hfit_elem`.

`hfit_elem` says `transform (l[k]).toInt k ∈ [-2^63, 2^63)`. We unpack
this for each of the three branches, deriving the precise
non-overflow obligations the step lemmas need. -/

/-- Square branch: if `i % 3 = 0` and the squared element fits in i64,
    then `mulOverflow l[i] l[i]` is false and the product equals `v*v`. -/
private theorem sq_no_overflow_of_fit
    (l : RustSlice i64) (k : Nat) (hk : k < l.val.size)
    (h_mod3 : k % 3 = 0)
    (h_fit : -(2^63 : Int) ≤ transform (l.val[k]'hk).toInt k ∧
             transform (l.val[k]'hk).toInt k < 2^63) :
    ¬ Int64.mulOverflow (l.val[k]'hk) (l.val[k]'hk) ∧
    ((l.val[k]'hk) * (l.val[k]'hk)).toInt =
      (l.val[k]'hk).toInt * (l.val[k]'hk).toInt := by
  have h_transform_eq : transform (l.val[k]'hk).toInt k =
                          (l.val[k]'hk).toInt * (l.val[k]'hk).toInt := by
    show (if k % 3 = 0 then _ else _) = _
    rw [if_pos h_mod3]
  have h_sq_lo : -(2^63 : Int) ≤ (l.val[k]'hk).toInt * (l.val[k]'hk).toInt := by
    rw [← h_transform_eq]; exact h_fit.1
  have h_sq_hi : (l.val[k]'hk).toInt * (l.val[k]'hk).toInt < 2^63 := by
    rw [← h_transform_eq]; exact h_fit.2
  have h_no_mul : ¬ Int64.mulOverflow (l.val[k]'hk) (l.val[k]'hk) := by
    intro hov
    rw [Int64.mulOverflow_iff] at hov
    rcases hov with hp | hn
    · omega
    · omega
  refine ⟨h_no_mul, ?_⟩
  exact Int64.toInt_mul_of_not_mulOverflow h_no_mul

/-- If the cube `v*v*v` fits in `[-2^63, 2^63)`, so does `v*v`. -/
private theorem sq_fits_of_cube_fits
    (v : Int)
    (h_lo : -(2^63 : Int) ≤ v * v * v)
    (h_hi : v * v * v < 2^63) :
    -(2^63 : Int) ≤ v * v ∧ v * v < 2^63 := by
  have h_sq_nneg : 0 ≤ v * v := int_sq_nneg v
  refine ⟨?_, ?_⟩
  · -- `-2^63 ≤ v*v` trivially since v*v ≥ 0.
    have h63 : -(2^63 : Int) < 0 := by decide
    omega
  · -- `v*v < 2^63`.  Three cases: v ≥ 2, v ≤ -2, or -1 ≤ v ≤ 1.
    by_cases h_v_ge2 : 2 ≤ v
    · -- v ≥ 2.  Show `2 * (v*v) ≤ v*v*v < 2^63`.
      have h1 : 2 * (v * v) ≤ v * (v * v) :=
        Int.mul_le_mul_of_nonneg_right h_v_ge2 h_sq_nneg
      have h_assoc : v * (v * v) = v * v * v := by
        rw [← Int.mul_assoc]
      omega
    · by_cases h_v_le_neg2 : v ≤ -2
      · -- v ≤ -2.  Show `2 * (v*v) ≤ -(v*v*v) ≤ 2^63`.
        have h1 : (v * v) * v ≤ (v * v) * (-2) :=
          Int.mul_le_mul_of_nonneg_left h_v_le_neg2 h_sq_nneg
        have h_eq : (v * v) * (-2) = -(2 * (v * v)) := by
          have : (-2 : Int) = -(2 : Int) := by decide
          rw [this, Int.mul_neg, Int.mul_comm]
        have h2 : v * v * v ≤ -(2 * (v * v)) := by
          rw [← h_eq]; exact h1
        omega
      · -- -1 ≤ v ≤ 1.  v ∈ {-1, 0, 1}; in each case v*v ≤ 1 < 2^63.
        have hv_cases : v = -1 ∨ v = 0 ∨ v = 1 := by omega
        rcases hv_cases with h | h | h
        · subst h; show ((-1 : Int)) * (-1) < 2^63; decide
        · subst h; show ((0 : Int)) * 0 < 2^63; decide
        · subst h; show ((1 : Int)) * 1 < 2^63; decide

/-- Cube branch: if `i % 3 ≠ 0`, `i % 4 = 0`, and the cubed element fits
    in i64, then both `v*v` and `(v*v)*v` don't overflow, and the toInt
    of the cube equals `v.toInt * v.toInt * v.toInt`. -/
private theorem cube_no_overflow_of_fit
    (l : RustSlice i64) (k : Nat) (hk : k < l.val.size)
    (h_not_mod3 : k % 3 ≠ 0) (h_mod4 : k % 4 = 0)
    (h_fit : -(2^63 : Int) ≤ transform (l.val[k]'hk).toInt k ∧
             transform (l.val[k]'hk).toInt k < 2^63) :
    ¬ Int64.mulOverflow (l.val[k]'hk) (l.val[k]'hk) ∧
    ¬ Int64.mulOverflow
        ((l.val[k]'hk) * (l.val[k]'hk)) (l.val[k]'hk) ∧
    ((l.val[k]'hk) * (l.val[k]'hk)).toInt =
      (l.val[k]'hk).toInt * (l.val[k]'hk).toInt ∧
    ((l.val[k]'hk) * (l.val[k]'hk) * (l.val[k]'hk)).toInt =
      (l.val[k]'hk).toInt * (l.val[k]'hk).toInt * (l.val[k]'hk).toInt := by
  have h_transform_eq : transform (l.val[k]'hk).toInt k =
                          (l.val[k]'hk).toInt * (l.val[k]'hk).toInt
                          * (l.val[k]'hk).toInt := by
    show (if k % 3 = 0 then _ else if k % 4 = 0 then _ else _) = _
    rw [if_neg h_not_mod3, if_pos h_mod4]
  have h_cube_lo :
      -(2^63 : Int) ≤
        (l.val[k]'hk).toInt * (l.val[k]'hk).toInt * (l.val[k]'hk).toInt := by
    rw [← h_transform_eq]; exact h_fit.1
  have h_cube_hi :
      (l.val[k]'hk).toInt * (l.val[k]'hk).toInt * (l.val[k]'hk).toInt
        < 2^63 := by
    rw [← h_transform_eq]; exact h_fit.2
  -- v*v fits too.
  have h_sq_fits := sq_fits_of_cube_fits (l.val[k]'hk).toInt h_cube_lo h_cube_hi
  have h_no_mul1 : ¬ Int64.mulOverflow (l.val[k]'hk) (l.val[k]'hk) := by
    intro hov
    rw [Int64.mulOverflow_iff] at hov
    rcases hov with hp | hn
    · have := h_sq_fits.2; omega
    · have := h_sq_fits.1; omega
  have h_sq_toInt :
      ((l.val[k]'hk) * (l.val[k]'hk)).toInt =
        (l.val[k]'hk).toInt * (l.val[k]'hk).toInt :=
    Int64.toInt_mul_of_not_mulOverflow h_no_mul1
  have h_no_mul2 :
      ¬ Int64.mulOverflow ((l.val[k]'hk) * (l.val[k]'hk)) (l.val[k]'hk) := by
    intro hov
    rw [Int64.mulOverflow_iff] at hov
    rw [h_sq_toInt] at hov
    rcases hov with hp | hn
    · omega
    · omega
  have h_cube_toInt :
      ((l.val[k]'hk) * (l.val[k]'hk) * (l.val[k]'hk)).toInt =
        (l.val[k]'hk).toInt * (l.val[k]'hk).toInt * (l.val[k]'hk).toInt := by
    rw [Int64.toInt_mul_of_not_mulOverflow h_no_mul2, h_sq_toInt]
  exact ⟨h_no_mul1, h_no_mul2, h_sq_toInt, h_cube_toInt⟩

/-- Compute `transform_sum_int` step at index `k` under each branch. -/
private theorem transform_sum_int_sq
    (l : RustSlice i64) (k : Nat) (hk : k < l.val.size)
    (h_mod3 : k % 3 = 0) :
    transform_sum_int l (k + 1) =
      transform_sum_int l k +
        (l.val[k]'hk).toInt * (l.val[k]'hk).toInt := by
  rw [transform_sum_int_succ l k hk]
  congr 1
  show (if k % 3 = 0 then _ else _) = _
  rw [if_pos h_mod3]

private theorem transform_sum_int_cube
    (l : RustSlice i64) (k : Nat) (hk : k < l.val.size)
    (h_not_mod3 : k % 3 ≠ 0) (h_mod4 : k % 4 = 0) :
    transform_sum_int l (k + 1) =
      transform_sum_int l k +
        (l.val[k]'hk).toInt * (l.val[k]'hk).toInt * (l.val[k]'hk).toInt := by
  rw [transform_sum_int_succ l k hk]
  congr 1
  show (if k % 3 = 0 then _ else if k % 4 = 0 then _ else _) = _
  rw [if_neg h_not_mod3, if_pos h_mod4]

private theorem transform_sum_int_id
    (l : RustSlice i64) (k : Nat) (hk : k < l.val.size)
    (h_not_mod3 : k % 3 ≠ 0) (h_not_mod4 : k % 4 ≠ 0) :
    transform_sum_int l (k + 1) =
      transform_sum_int l k + (l.val[k]'hk).toInt := by
  rw [transform_sum_int_succ l k hk]
  congr 1
  show (if k % 3 = 0 then _ else if k % 4 = 0 then _ else _) = _
  rw [if_neg h_not_mod3, if_neg h_not_mod4]

/-! ## Strong-induction master lemma. -/

private theorem sum_at_correct (lst : RustSlice i64)
    (hfit_elem : ∀ (k : Nat) (h : k < lst.val.size),
                   -(2^63 : Int) ≤ transform (lst.val[k]'h).toInt k ∧
                   transform (lst.val[k]'h).toInt k < 2^63)
    (hfit_sum : ∀ k : Nat, k ≤ lst.val.size →
                  -(2^63 : Int) ≤ transform_sum_int lst k ∧
                  transform_sum_int lst k < 2^63) :
    ∀ (m : Nat) (i : usize) (acc : i64),
      lst.val.size - i.toNat ≤ m →
      i.toNat ≤ lst.val.size →
      acc.toInt = transform_sum_int lst i.toNat →
      ∃ r : i64,
        clever_140_sum_squares.sum_at lst i acc = RustM.ok r ∧
        r.toInt = transform_sum_int lst lst.val.size := by
  intro m
  induction m with
  | zero =>
    intro i acc hm hi_le hinv
    have hi_eq : i.toNat = lst.val.size := by omega
    have hi_ge : lst.val.size ≤ i.toNat := by omega
    refine ⟨acc, sum_at_oob lst i acc hi_ge, ?_⟩
    rw [hinv, hi_eq]
  | succ m ih =>
    intro i acc hm hi_le hinv
    by_cases hi_ge : lst.val.size ≤ i.toNat
    · have hi_eq : i.toNat = lst.val.size := by omega
      refine ⟨acc, sum_at_oob lst i acc hi_ge, ?_⟩
      rw [hinv, hi_eq]
    · have hi_lt : i.toNat < lst.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : lst.val.size < USize64.size := lst.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ lst.val.size := by rw [h_i1]; omega
      have h_m_le : lst.val.size - (i + 1).toNat ≤ m := by rw [h_i1]; omega
      have h_fit_succ := hfit_sum (i.toNat + 1) (by omega)
      have h_fit_elem_i := hfit_elem i.toNat hi_lt
      by_cases h_mod3 : i.toNat % 3 = 0
      · -- Square branch.
        obtain ⟨h_no_mul, h_sq_toInt⟩ :=
          sq_no_overflow_of_fit lst i.toNat hi_lt h_mod3 h_fit_elem_i
        have h_psum_succ :
            transform_sum_int lst (i.toNat + 1) =
              transform_sum_int lst i.toNat +
                (lst.val[i.toNat]'hi_lt).toInt * (lst.val[i.toNat]'hi_lt).toInt :=
          transform_sum_int_sq lst i.toNat hi_lt h_mod3
        have h_sum_eq :
            acc.toInt + (lst.val[i.toNat]'hi_lt).toInt
                       * (lst.val[i.toNat]'hi_lt).toInt
              = transform_sum_int lst (i.toNat + 1) := by
          rw [h_psum_succ, hinv]
        have h_no_add :
            ¬ Int64.addOverflow acc
                ((lst.val[i.toNat]'hi_lt) * (lst.val[i.toNat]'hi_lt)) := by
          intro hov
          rw [Int64.addOverflow_iff] at hov
          rw [h_sq_toInt] at hov
          rw [h_sum_eq] at hov
          rcases hov with hp | hn
          · have := h_fit_succ.2; omega
          · have := h_fit_succ.1; omega
        have h_step := sum_at_sq lst i acc hi_lt h_mod3 h_no_mul h_no_add
        have h_new_toInt :
            (acc + (lst.val[i.toNat]'hi_lt) * (lst.val[i.toNat]'hi_lt)).toInt =
              acc.toInt + (lst.val[i.toNat]'hi_lt).toInt
                         * (lst.val[i.toNat]'hi_lt).toInt := by
          rw [Int64.toInt_add_of_not_addOverflow h_no_add, h_sq_toInt]
        have h_new_inv :
            (acc + (lst.val[i.toNat]'hi_lt) * (lst.val[i.toNat]'hi_lt)).toInt =
              transform_sum_int lst (i + 1).toNat := by
          rw [h_new_toInt, hinv, h_i1, ← h_psum_succ]
        obtain ⟨r, h_rec_eq, h_r_int⟩ :=
          ih (i + 1) (acc + (lst.val[i.toNat]'hi_lt) * (lst.val[i.toNat]'hi_lt))
            h_m_le h_i1_le h_new_inv
        refine ⟨r, ?_, h_r_int⟩
        rw [h_step]; exact h_rec_eq
      · by_cases h_mod4 : i.toNat % 4 = 0
        · -- Cube branch.
          obtain ⟨h_no_mul1, h_no_mul2, h_sq_toInt, h_cube_toInt⟩ :=
            cube_no_overflow_of_fit lst i.toNat hi_lt h_mod3 h_mod4 h_fit_elem_i
          have h_psum_succ :
              transform_sum_int lst (i.toNat + 1) =
                transform_sum_int lst i.toNat +
                  (lst.val[i.toNat]'hi_lt).toInt
                  * (lst.val[i.toNat]'hi_lt).toInt
                  * (lst.val[i.toNat]'hi_lt).toInt :=
            transform_sum_int_cube lst i.toNat hi_lt h_mod3 h_mod4
          have h_sum_eq :
              acc.toInt + (lst.val[i.toNat]'hi_lt).toInt
                         * (lst.val[i.toNat]'hi_lt).toInt
                         * (lst.val[i.toNat]'hi_lt).toInt
                = transform_sum_int lst (i.toNat + 1) := by
            rw [h_psum_succ, hinv]
          have h_no_add :
              ¬ Int64.addOverflow acc
                  ((lst.val[i.toNat]'hi_lt) * (lst.val[i.toNat]'hi_lt)
                    * (lst.val[i.toNat]'hi_lt)) := by
            intro hov
            rw [Int64.addOverflow_iff] at hov
            rw [h_cube_toInt] at hov
            rw [h_sum_eq] at hov
            rcases hov with hp | hn
            · have := h_fit_succ.2; omega
            · have := h_fit_succ.1; omega
          have h_step :=
            sum_at_cube lst i acc hi_lt h_mod3 h_mod4 h_no_mul1 h_no_mul2 h_no_add
          have h_new_toInt :
              (acc + (lst.val[i.toNat]'hi_lt) * (lst.val[i.toNat]'hi_lt)
                    * (lst.val[i.toNat]'hi_lt)).toInt =
                acc.toInt + (lst.val[i.toNat]'hi_lt).toInt
                           * (lst.val[i.toNat]'hi_lt).toInt
                           * (lst.val[i.toNat]'hi_lt).toInt := by
            rw [Int64.toInt_add_of_not_addOverflow h_no_add, h_cube_toInt]
          have h_new_inv :
              (acc + (lst.val[i.toNat]'hi_lt) * (lst.val[i.toNat]'hi_lt)
                    * (lst.val[i.toNat]'hi_lt)).toInt =
                transform_sum_int lst (i + 1).toNat := by
            rw [h_new_toInt, hinv, h_i1, ← h_psum_succ]
          obtain ⟨r, h_rec_eq, h_r_int⟩ :=
            ih (i + 1)
              (acc + (lst.val[i.toNat]'hi_lt) * (lst.val[i.toNat]'hi_lt)
                    * (lst.val[i.toNat]'hi_lt))
              h_m_le h_i1_le h_new_inv
          refine ⟨r, ?_, h_r_int⟩
          rw [h_step]; exact h_rec_eq
        · -- Identity branch.
          have h_psum_succ :
              transform_sum_int lst (i.toNat + 1) =
                transform_sum_int lst i.toNat + (lst.val[i.toNat]'hi_lt).toInt :=
            transform_sum_int_id lst i.toNat hi_lt h_mod3 h_mod4
          have h_sum_eq :
              acc.toInt + (lst.val[i.toNat]'hi_lt).toInt
                = transform_sum_int lst (i.toNat + 1) := by
            rw [h_psum_succ, hinv]
          have h_no_add :
              ¬ Int64.addOverflow acc (lst.val[i.toNat]'hi_lt) := by
            intro hov
            rw [Int64.addOverflow_iff] at hov
            rw [h_sum_eq] at hov
            rcases hov with hp | hn
            · have := h_fit_succ.2; omega
            · have := h_fit_succ.1; omega
          have h_step := sum_at_identity lst i acc hi_lt h_mod3 h_mod4 h_no_add
          have h_new_toInt :
              (acc + (lst.val[i.toNat]'hi_lt)).toInt =
                acc.toInt + (lst.val[i.toNat]'hi_lt).toInt :=
            Int64.toInt_add_of_not_addOverflow h_no_add
          have h_new_inv :
              (acc + (lst.val[i.toNat]'hi_lt)).toInt =
                transform_sum_int lst (i + 1).toNat := by
            rw [h_new_toInt, hinv, h_i1, ← h_psum_succ]
          obtain ⟨r, h_rec_eq, h_r_int⟩ :=
            ih (i + 1) (acc + (lst.val[i.toNat]'hi_lt))
              h_m_le h_i1_le h_new_inv
          refine ⟨r, ?_, h_r_int⟩
          rw [h_step]; exact h_rec_eq

/-! ## Top-level theorems. -/

/-- Empty-slice boundary contract. -/
theorem empty_returns_zero (lst : RustSlice i64) (hempty : lst.val.size = 0) :
    clever_140_sum_squares.sum_squares lst = RustM.ok (0 : i64) := by
  unfold clever_140_sum_squares.sum_squares
  have hi_ge : lst.val.size ≤ (0 : usize).toNat := by
    rw [usize_zero_toNat, hempty]; omega
  exact sum_at_oob lst (0 : usize) (0 : i64) hi_ge

/-- General functional-correctness postcondition. -/
theorem matches_spec (lst : RustSlice i64)
    (hfit_elem : ∀ (k : Nat) (h : k < lst.val.size),
                   -(2^63 : Int) ≤ transform (lst.val[k]'h).toInt k ∧
                   transform (lst.val[k]'h).toInt k < 2^63)
    (hfit_sum : ∀ k : Nat, k ≤ lst.val.size →
                  -(2^63 : Int) ≤ transform_sum_int lst k ∧
                  transform_sum_int lst k < 2^63) :
    ∃ r : i64,
      clever_140_sum_squares.sum_squares lst = RustM.ok r ∧
      r.toInt = transform_sum_int lst lst.val.size := by
  unfold clever_140_sum_squares.sum_squares
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_inv : (0 : i64).toInt = transform_sum_int lst (0 : usize).toNat := by
    rw [h_zero_toNat, i64_zero_toInt]; rfl
  have h_m_le : lst.val.size - (0 : usize).toNat ≤ lst.val.size := by
    rw [h_zero_toNat]; omega
  have h_i_le : (0 : usize).toNat ≤ lst.val.size := by
    rw [h_zero_toNat]; omega
  exact sum_at_correct lst hfit_elem hfit_sum lst.val.size (0 : usize) (0 : i64)
    h_m_le h_i_le h_inv

end Clever_140_sum_squaresObligations
