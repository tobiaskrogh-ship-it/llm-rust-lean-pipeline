-- Companion obligations file for the `clever_132_sum_squares` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_132_sum_squares

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_132_sum_squaresObligations

/-! ## Integer-valued specification of the sum of squares

The Rust source documents `sum_squares(lst)` as returning the sum of
squares of the elements of `lst`. We compute the spec in `Int` (matching
the proptest's `i64`-iterator sum on bounded inputs) so the specification
itself cannot overflow on any input the function under verification can
legally accept; overflow shows up as a precondition on the obligation
rather than a hidden assumption in the spec. -/

/-- Integer-valued prefix sum of squares:
    `sum_squares_int xs k = Σ_{j<k} ((xs.val[j]).toInt)^2`.

    The `dite` on `k < l.val.size` makes the definition total — every
    theorem below quantifies `k` so that `k ≤ l.val.size`, keeping the
    index in range. -/
private def sum_squares_int (l : RustSlice i64) : Nat → Int
  | 0     => 0
  | k + 1 =>
      sum_squares_int l k +
        (if h : k < l.val.size then
          (l.val[k]'h).toInt * (l.val[k]'h).toInt
        else 0)

/-! ## Top-level theorems

The Rust `#[test] fn known` asserts three pointwise values:
  `sum_squares(&[1,2,3]) = 14`, `sum_squares(&[]) = 0`,
  `sum_squares(&[-1,-2,-3]) = 14`.
The first and third are concrete instances subsumed by the general
`result_matches_sum_of_squares` postcondition below (the integer-valued
spec assigns 14 to both via `1+4+9`). The empty case is a meaningful
boundary contract — it pins down the seed accumulator `0`, which the
recursive postcondition would otherwise vacuously hold for any seed —
and gets its own theorem.

The proptest `matches` asserts the general functional-correctness
property and becomes `result_matches_sum_of_squares`. -/

/-! ## Helpers (transferred from `sum_product` reference) -/

/-- `RustM.ok x >>= f = f x`. The library's `pure_bind` simp lemma only
    matches literal `Pure.pure`; this rewrite handles the `RustM.ok` form
    produced after reducing definitions. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

/-- `(0 : i64).toInt = 0`. -/
private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide

/-- Step of `sum_squares_int`: when `k < l.val.size`, the `dite` reduces
    to the `Int`-valued addition with the squared element. -/
private theorem sum_squares_int_succ
    (l : RustSlice i64) (k : Nat) (hk : k < l.val.size) :
    sum_squares_int l (k + 1) =
      sum_squares_int l k + (l.val[k]'hk).toInt * (l.val[k]'hk).toInt := by
  show sum_squares_int l k
        + (if h : k < l.val.size then (l.val[k]'h).toInt * (l.val[k]'h).toInt else 0)
       = sum_squares_int l k + (l.val[k]'hk).toInt * (l.val[k]'hk).toInt
  rw [dif_pos hk]

/-- `0 ≤ x * x` for `x : Int`. No `Mathlib.sq_nonneg` here — prove from
    `Int.mul_nonneg` plus `Int.neg_mul_neg`. -/
private theorem mul_self_nonneg_int (x : Int) : 0 ≤ x * x := by
  by_cases h : x < 0
  · have h1 : 0 ≤ -x := by omega
    have h2 : 0 ≤ (-x) * (-x) := Int.mul_nonneg h1 h1
    rw [Int.neg_mul_neg] at h2
    exact h2
  · have h' : 0 ≤ x := by omega
    exact Int.mul_nonneg h' h'

/-- The integer-valued prefix sum of squares is non-negative: it's a sum
    of squares of `Int`s. Used to dominate the per-element multiplication
    overflow by the prefix-sum bound. -/
private theorem sum_squares_int_nonneg (l : RustSlice i64) (k : Nat) :
    0 ≤ sum_squares_int l k := by
  induction k with
  | zero => show (0 : Int) ≤ 0; omega
  | succ k ih =>
    show 0 ≤ sum_squares_int l k
              + (if h : k < l.val.size then
                  (l.val[k]'h).toInt * (l.val[k]'h).toInt
                else 0)
    by_cases h : k < l.val.size
    · rw [dif_pos h]
      have h_sq : 0 ≤ (l.val[k]'h).toInt * (l.val[k]'h).toInt :=
        mul_self_nonneg_int _
      omega
    · rw [dif_neg h]; omega

/-! ## Step lemmas for `sum_at`

Two branches of the recursive body — out-of-bounds and recursion. -/

/-- Out-of-bounds step: when `i.toNat ≥ l.val.size`, the function
    returns `RustM.ok acc`. -/
private theorem sum_at_oob (l : RustSlice i64) (i : usize) (acc : i64)
    (hi : l.val.size ≤ i.toNat) :
    clever_132_sum_squares.sum_at l i acc = RustM.ok acc := by
  conv => lhs; unfold clever_132_sum_squares.sum_at
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

/-- Recursion step: when `i.toNat < l.val.size`, the per-element signed
    multiplication doesn't overflow, the accumulator signed addition
    doesn't overflow, and the index increment doesn't overflow, the
    function delegates to `sum_at l (i+1) (acc + l[i]*l[i])`. -/
private theorem sum_at_recurse
    (l : RustSlice i64) (i : usize) (acc : i64)
    (hi : i.toNat < l.val.size)
    (hno_mul : ¬ Int64.mulOverflow (l.val[i.toNat]'hi) (l.val[i.toNat]'hi))
    (hno_add : ¬ Int64.addOverflow acc
                  ((l.val[i.toNat]'hi) * (l.val[i.toNat]'hi))) :
    clever_132_sum_squares.sum_at l i acc =
      clever_132_sum_squares.sum_at l (i + 1)
        (acc + (l.val[i.toNat]'hi) * (l.val[i.toNat]'hi)) := by
  conv => lhs; unfold clever_132_sum_squares.sum_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
  have h_no_mul_bv :
      BitVec.smulOverflow (l.val[i.toNat]'hi).toBitVec
                          (l.val[i.toNat]'hi).toBitVec = false := by
    have hno' : ¬ (BitVec.smulOverflow (l.val[i.toNat]'hi).toBitVec
                                        (l.val[i.toNat]'hi).toBitVec = true) := hno_mul
    cases hb : BitVec.smulOverflow (l.val[i.toNat]'hi).toBitVec
                                    (l.val[i.toNat]'hi).toBitVec with
    | false => rfl
    | true => exact absurd hb hno'
  have h_no_add_bv :
      BitVec.saddOverflow acc.toBitVec
        ((l.val[i.toNat]'hi) * (l.val[i.toNat]'hi)).toBitVec = false := by
    have hno' : ¬ (BitVec.saddOverflow acc.toBitVec
                    ((l.val[i.toNat]'hi) * (l.val[i.toNat]'hi)).toBitVec = true) := hno_add
    cases hb : BitVec.saddOverflow acc.toBitVec
                ((l.val[i.toNat]'hi) * (l.val[i.toNat]'hi)).toBitVec with
    | false => rfl
    | true => exact absurd hb hno'
  have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
  have h_no_overflow_i : i.toNat + 1 < 2^64 := by omega
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
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.ops.arith.Mul.mul, h_no_mul_bv,
             rust_primitives.ops.arith.Add.add, h_no_add_bv, h_no_bv_i]

/-! ## Strong-induction invariant

Single invariant lemma threading the accumulator `acc.toInt = sum_squares_int l i.toNat`.
Strong induction on the measure `l.val.size - i.toNat`. The single `hfit`
precondition on prefix sums implies both no-overflow obligations:
non-negativity of `sum_squares_int` dominates per-element multiplication
overflow, and the recursive case discharges accumulator addition overflow. -/

private theorem sum_at_correct (l : RustSlice i64) :
    ∀ (m : Nat) (i : usize) (acc : i64),
      l.val.size - i.toNat ≤ m →
      i.toNat ≤ l.val.size →
      acc.toInt = sum_squares_int l i.toNat →
      (∀ k : Nat, k ≤ l.val.size →
          -(2^63 : Int) ≤ sum_squares_int l k ∧ sum_squares_int l k < 2^63) →
      ∃ r : i64,
        clever_132_sum_squares.sum_at l i acc = RustM.ok r ∧
        r.toInt = sum_squares_int l l.val.size := by
  intro m
  induction m with
  | zero =>
    intro i acc hm hi_le hinv hfit
    -- size - i.toNat = 0 with i.toNat ≤ size ⇒ i.toNat = size, OOB returns acc.
    have hi_eq : i.toNat = l.val.size := by omega
    have hi_ge : l.val.size ≤ i.toNat := by omega
    refine ⟨acc, ?_, ?_⟩
    · exact sum_at_oob l i acc hi_ge
    · rw [hinv, hi_eq]
  | succ m ih =>
    intro i acc hm hi_le hinv hfit
    by_cases hi_ge : l.val.size ≤ i.toNat
    · -- OOB branch; combined with hi_le ⇒ i.toNat = size.
      have hi_eq : i.toNat = l.val.size := by omega
      refine ⟨acc, ?_, ?_⟩
      · exact sum_at_oob l i acc hi_ge
      · rw [hinv, hi_eq]
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      -- Derive both no-overflow obligations from the prefix-sum invariant `hfit`.
      have h_psum_succ :
          sum_squares_int l (i.toNat + 1) =
            acc.toInt + (l.val[i.toNat]'hi_lt).toInt * (l.val[i.toNat]'hi_lt).toInt := by
        rw [sum_squares_int_succ l i.toNat hi_lt, hinv]
      have h_i1_le_size : i.toNat + 1 ≤ l.val.size := by omega
      have h_fit_succ := hfit (i.toNat + 1) h_i1_le_size
      -- Per-element multiplication: dominated by prefix-sum bound at k+1.
      -- l[i].toInt * l[i].toInt = sum_squares_int l (i+1) - sum_squares_int l i
      -- ≤ sum_squares_int l (i+1) (since sum_squares_int l i ≥ 0).
      have h_sq_nonneg :
          0 ≤ (l.val[i.toNat]'hi_lt).toInt * (l.val[i.toNat]'hi_lt).toInt :=
        mul_self_nonneg_int _
      have h_psum_i_nonneg : 0 ≤ sum_squares_int l i.toNat :=
        sum_squares_int_nonneg l i.toNat
      have h_sq_lt :
          (l.val[i.toNat]'hi_lt).toInt * (l.val[i.toNat]'hi_lt).toInt < 2^63 := by
        have hbnd := h_fit_succ.2
        rw [sum_squares_int_succ l i.toNat hi_lt] at hbnd
        omega
      have h_sq_ge :
          -(2^63 : Int) ≤ (l.val[i.toNat]'hi_lt).toInt * (l.val[i.toNat]'hi_lt).toInt := by
        omega
      have hno_mul : ¬ Int64.mulOverflow (l.val[i.toNat]'hi_lt) (l.val[i.toNat]'hi_lt) := by
        intro hov
        rw [Int64.mulOverflow_iff] at hov
        rcases hov with hov_pos | hov_neg
        · omega
        · omega
      -- Add overflow on `acc + l[i]^2`: dominated by prefix-sum bound on (i+1).
      -- (acc + l[i]^2).toInt = sum_squares_int l (i+1) ∈ [-2^63, 2^63).
      have h_acc_plus_sq_toInt_eq :
          acc.toInt + (l.val[i.toNat]'hi_lt).toInt * (l.val[i.toNat]'hi_lt).toInt
            = sum_squares_int l (i.toNat + 1) := h_psum_succ.symm
      have hno_add :
          ¬ Int64.addOverflow acc
              ((l.val[i.toNat]'hi_lt) * (l.val[i.toNat]'hi_lt)) := by
        intro hov
        rw [Int64.addOverflow_iff] at hov
        -- toInt of the product equals the product of toInts (no mul overflow).
        rw [Int64.toInt_mul_of_not_mulOverflow hno_mul] at hov
        rw [h_acc_plus_sq_toInt_eq] at hov
        rcases hov with hov_pos | hov_neg
        · have := h_fit_succ.2; omega
        · have := h_fit_succ.1; omega
      have h_rec := sum_at_recurse l i acc hi_lt hno_mul hno_add
      rw [h_rec]
      -- Apply IH with reduced measure and updated invariant.
      have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
      have h_no_ov_i : i.toNat + 1 < 2^64 := by omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_inv' :
          (acc + (l.val[i.toNat]'hi_lt) * (l.val[i.toNat]'hi_lt)).toInt =
            sum_squares_int l (i + 1).toNat := by
        rw [h_i1]
        rw [Int64.toInt_add_of_not_addOverflow hno_add]
        rw [Int64.toInt_mul_of_not_mulOverflow hno_mul]
        exact h_acc_plus_sq_toInt_eq
      have h_m_le : l.val.size - (i + 1).toNat ≤ m := by
        rw [h_i1]; omega
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by
        rw [h_i1]; omega
      exact ih (i + 1)
        (acc + (l.val[i.toNat]'hi_lt) * (l.val[i.toNat]'hi_lt))
        h_m_le h_i1_le h_inv' hfit

/-! ## Top-level theorems

Each obligation specialises `sum_at_correct` at `i := (0 : usize)`,
`acc := (0 : i64)`, where the prefix-sum invariant
`(0 : i64).toInt = 0 = sum_squares_int l 0` holds by definition. -/

/-- Empty-slice boundary contract.

    Captures the `known` test assertion `sum_squares(&[]) == 0`.
    Pins down the seed accumulator: without this, the general postcondition
    below would hold for any choice of initial accumulator. -/
theorem empty_returns_zero (lst : RustSlice i64) (hempty : lst.val.size = 0) :
    clever_132_sum_squares.sum_squares lst = RustM.ok (0 : i64) := by
  unfold clever_132_sum_squares.sum_squares
  have hi_ge : lst.val.size ≤ (0 : usize).toNat := by
    show lst.val.size ≤ 0
    omega
  exact sum_at_oob lst (0 : usize) (0 : i64) hi_ge

/-- General functional-correctness postcondition.

    Captures the proptest `matches`: under no-overflow preconditions, the
    result equals the integer-valued sum of squared elements.

    Feasibility / precondition. The natural universal statement is false
    in the Lean model: a `RustSlice i64` can hold any `i64` values with
    arbitrary `size < 2^64`, so both `l[i] * l[i]` (signed-mul on an
    `i64::MIN`-ish element) and the running `acc + l[i]^2` (sum of many
    large squares) can overflow. The proptest's `(-1000..=1000, 0..20)`
    bounds keep the sum under `2 · 10^7`, well inside `i64`; the
    corresponding hypothesis here is that every prefix sum of squares
    fits in `i64`. Because each squared term is non-negative, this single
    bound implies every individual `(l[i]).toInt * (l[i]).toInt < 2^63`
    too (the per-element multiplication overflow is dominated by the
    prefix bound at `k+1`). -/
theorem result_matches_sum_of_squares (lst : RustSlice i64)
    (hfit : ∀ k : Nat, k ≤ lst.val.size →
              -(2^63 : Int) ≤ sum_squares_int lst k
              ∧ sum_squares_int lst k < 2^63) :
    ∃ r : i64,
      clever_132_sum_squares.sum_squares lst = RustM.ok r ∧
      r.toInt = sum_squares_int lst lst.val.size := by
  unfold clever_132_sum_squares.sum_squares
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_inv : (0 : i64).toInt = sum_squares_int lst (0 : usize).toNat := by
    rw [h_zero_toNat, i64_zero_toInt]; rfl
  have h_m_le : lst.val.size - (0 : usize).toNat ≤ lst.val.size := by
    rw [h_zero_toNat]; omega
  have h_i_le : (0 : usize).toNat ≤ lst.val.size := by
    rw [h_zero_toNat]; omega
  exact sum_at_correct lst lst.val.size (0 : usize) (0 : i64)
    h_m_le h_i_le h_inv hfit

end Clever_132_sum_squaresObligations
