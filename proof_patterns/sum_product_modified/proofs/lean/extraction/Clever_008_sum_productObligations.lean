-- Companion obligations file for the `clever_008_sum_product` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_008_sum_product

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_008_sum_productObligations

/-! ## Integer-valued specifications of sum and product

The Rust source documents `sum_product` as returning `(Σ xs, Π xs)`, with
empty sum `0` and empty product `1`. The contract specifies the function's
return values via these mathematical operations on the slice's elements
viewed as `Int`s — that way the spec itself cannot overflow on any input,
and overflow shows up as a precondition on the obligation rather than a
hidden assumption in the spec. -/

/-- Integer-valued prefix sum: `sum_of_int xs k = Σ_{j<k} (xs.val[j]).toInt`.
    The `dite` keeps the function total — every theorem below quantifies
    `k` so that `k ≤ numbers.val.size`, keeping the index in range. -/
private def sum_of_int (numbers : RustSlice i64) : Nat → Int
  | 0     => 0
  | k + 1 =>
      sum_of_int numbers k +
        (if h : k < numbers.val.size then (numbers.val[k]'h).toInt else 0)

/-- Integer-valued prefix product: `product_of_int xs k = Π_{j<k} (xs.val[j]).toInt`.
    Empty product is `1`, matching the Rust doc comment and the seed used by
    the public wrapper. -/
private def product_of_int (numbers : RustSlice i64) : Nat → Int
  | 0     => 1
  | k + 1 =>
      product_of_int numbers k *
        (if h : k < numbers.val.size then (numbers.val[k]'h).toInt else 1)

/-! ## Helpers (transferred from `contains_u64` / `below_zero` references) -/

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

/-- `(1 : i64).toInt = 1`. -/
private theorem i64_one_toInt : (1 : i64).toInt = 1 := by decide

/-- Step of `sum_of_int`: when `k < numbers.val.size`, the `dite` reduces
    to the `Int`-valued addition. -/
private theorem sum_of_int_succ
    (numbers : RustSlice i64) (k : Nat) (hk : k < numbers.val.size) :
    sum_of_int numbers (k + 1) =
      sum_of_int numbers k + (numbers.val[k]'hk).toInt := by
  show sum_of_int numbers k
        + (if h : k < numbers.val.size then (numbers.val[k]'h).toInt else 0)
       = sum_of_int numbers k + (numbers.val[k]'hk).toInt
  rw [dif_pos hk]

/-- Step of `product_of_int`: when `k < numbers.val.size`, the `dite` reduces
    to the `Int`-valued multiplication. -/
private theorem product_of_int_succ
    (numbers : RustSlice i64) (k : Nat) (hk : k < numbers.val.size) :
    product_of_int numbers (k + 1) =
      product_of_int numbers k * (numbers.val[k]'hk).toInt := by
  show product_of_int numbers k
        * (if h : k < numbers.val.size then (numbers.val[k]'h).toInt else 1)
       = product_of_int numbers k * (numbers.val[k]'hk).toInt
  rw [dif_pos hk]

/-! ## Step lemmas for `sum_product_at`

Two branches of the recursive body — out-of-bounds and recursion. The
"found" case from `contains_u64` / `below_zero` doesn't exist here: the
Rust code unconditionally recurses or terminates at the bound. -/

/-- Out-of-bounds step: when `i.toNat ≥ numbers.val.size`, the function
    returns `RustM.ok ⟨sum, product⟩`. -/
private theorem sum_product_at_oob (numbers : RustSlice i64) (i : usize)
    (sum product : i64) (hi : numbers.val.size ≤ i.toNat) :
    clever_008_sum_product.sum_product_at numbers i sum product =
      RustM.ok (rust_primitives.hax.Tuple2.mk sum product) := by
  conv => lhs; unfold clever_008_sum_product.sum_product_at
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

/-- Recursion step: when `i.toNat < numbers.val.size`, signed addition and
    signed multiplication both do not overflow at this index, the function
    delegates to the recursive call with `i+1` and the updated accumulators. -/
private theorem sum_product_at_recurse
    (numbers : RustSlice i64) (i : usize) (sum product : i64)
    (hi : i.toNat < numbers.val.size)
    (hno_add : ¬ Int64.addOverflow sum (numbers.val[i.toNat]'hi))
    (hno_mul : ¬ Int64.mulOverflow product (numbers.val[i.toNat]'hi)) :
    clever_008_sum_product.sum_product_at numbers i sum product =
      clever_008_sum_product.sum_product_at numbers (i + 1)
        (sum + numbers.val[i.toNat]'hi)
        (product * numbers.val[i.toNat]'hi) := by
  conv => lhs; unfold clever_008_sum_product.sum_product_at
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' numbers.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat numbers.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (numbers[i]_? : RustM i64) = RustM.ok (numbers.val[i.toNat]'hi) := by
    show (if h : i.toNat < numbers.val.size then pure (numbers.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (numbers.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
  have h_no_bv :
      BitVec.saddOverflow sum.toBitVec (numbers.val[i.toNat]'hi).toBitVec = false := by
    have hno' : ¬ (BitVec.saddOverflow sum.toBitVec
                                       (numbers.val[i.toNat]'hi).toBitVec = true) := hno_add
    cases hb : BitVec.saddOverflow sum.toBitVec (numbers.val[i.toNat]'hi).toBitVec with
    | false => rfl
    | true => exact absurd hb hno'
  have h_no_mul_bv :
      BitVec.smulOverflow product.toBitVec (numbers.val[i.toNat]'hi).toBitVec = false := by
    have hno' : ¬ (BitVec.smulOverflow product.toBitVec
                                       (numbers.val[i.toNat]'hi).toBitVec = true) := hno_mul
    cases hb : BitVec.smulOverflow product.toBitVec (numbers.val[i.toNat]'hi).toBitVec with
    | false => rfl
    | true => exact absurd hb hno'
  have h_size_lt : numbers.val.size < 2^64 := numbers.size_lt_usizeSize
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
             rust_primitives.ops.arith.Add.add, h_no_bv, h_no_bv_i,
             rust_primitives.ops.arith.Mul.mul, h_no_mul_bv]

/-! ## Strong-induction invariant

Single combined invariant lemma that proves both component postconditions
together. The recursion threads `sum` and `product` in lockstep, so it is
cleanest to package both invariants into one strong induction on the
measure `numbers.val.size - i.toNat`.

We also carry `i.toNat ≤ numbers.val.size` so that at the OOB boundary,
`i.toNat = numbers.val.size` and the prefix-sum invariants collapse to the
desired equalities. -/

private theorem sum_product_at_correct (numbers : RustSlice i64) :
    ∀ (m : Nat) (i : usize) (sum product : i64),
      numbers.val.size - i.toNat ≤ m →
      i.toNat ≤ numbers.val.size →
      sum.toInt = sum_of_int numbers i.toNat →
      product.toInt = product_of_int numbers i.toNat →
      (∀ k : Nat, k ≤ numbers.val.size →
          -(2^63 : Int) ≤ sum_of_int numbers k ∧ sum_of_int numbers k < 2^63) →
      (∀ k : Nat, k ≤ numbers.val.size →
          -(2^63 : Int) ≤ product_of_int numbers k ∧ product_of_int numbers k < 2^63) →
      ∃ s p : i64,
        clever_008_sum_product.sum_product_at numbers i sum product =
          RustM.ok (rust_primitives.hax.Tuple2.mk s p) ∧
        s.toInt = sum_of_int numbers numbers.val.size ∧
        p.toInt = product_of_int numbers numbers.val.size := by
  intro m
  induction m with
  | zero =>
    intro i sum product hm hi_le hinv_s hinv_p hfit_s hfit_p
    -- size - i.toNat = 0 with i.toNat ≤ size ⇒ i.toNat = size, OOB returns ⟨sum, product⟩.
    have hi_eq : i.toNat = numbers.val.size := by omega
    have hi_ge : numbers.val.size ≤ i.toNat := by omega
    refine ⟨sum, product, ?_, ?_, ?_⟩
    · exact sum_product_at_oob numbers i sum product hi_ge
    · rw [hinv_s, hi_eq]
    · rw [hinv_p, hi_eq]
  | succ m ih =>
    intro i sum product hm hi_le hinv_s hinv_p hfit_s hfit_p
    by_cases hi_ge : numbers.val.size ≤ i.toNat
    · -- OOB branch; combined with hi_le ⇒ i.toNat = size.
      have hi_eq : i.toNat = numbers.val.size := by omega
      refine ⟨sum, product, ?_, ?_, ?_⟩
      · exact sum_product_at_oob numbers i sum product hi_ge
      · rw [hinv_s, hi_eq]
      · rw [hinv_p, hi_eq]
    · have hi_lt : i.toNat < numbers.val.size := Nat.lt_of_not_le hi_ge
      -- Derive no-overflow for both `+?` and `*?` from the prefix-sum invariants.
      have h_psum_succ :
          sum_of_int numbers (i.toNat + 1) =
            sum.toInt + (numbers.val[i.toNat]'hi_lt).toInt := by
        rw [sum_of_int_succ numbers i.toNat hi_lt, hinv_s]
      have h_pprod_succ :
          product_of_int numbers (i.toNat + 1) =
            product.toInt * (numbers.val[i.toNat]'hi_lt).toInt := by
        rw [product_of_int_succ numbers i.toNat hi_lt, hinv_p]
      have h_i1_le_size : i.toNat + 1 ≤ numbers.val.size := by omega
      have h_fit_sum_succ := hfit_s (i.toNat + 1) h_i1_le_size
      have h_fit_prod_succ := hfit_p (i.toNat + 1) h_i1_le_size
      have hno_add : ¬ Int64.addOverflow sum (numbers.val[i.toNat]'hi_lt) := by
        intro hov
        rw [Int64.addOverflow_iff] at hov
        rw [← h_psum_succ] at hov
        rcases hov with hov_pos | hov_neg
        · have := h_fit_sum_succ.2; omega
        · have := h_fit_sum_succ.1; omega
      have hno_mul : ¬ Int64.mulOverflow product (numbers.val[i.toNat]'hi_lt) := by
        intro hov
        rw [Int64.mulOverflow_iff] at hov
        rw [← h_pprod_succ] at hov
        rcases hov with hov_pos | hov_neg
        · have := h_fit_prod_succ.2; omega
        · have := h_fit_prod_succ.1; omega
      have h_rec := sum_product_at_recurse numbers i sum product hi_lt hno_add hno_mul
      rw [h_rec]
      -- Apply IH with reduced measure and updated invariants.
      have h_size_lt : numbers.val.size < 2^64 := numbers.size_lt_usizeSize
      have h_no_ov_i : i.toNat + 1 < 2^64 := by omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_inv_s' :
          (sum + numbers.val[i.toNat]'hi_lt).toInt =
            sum_of_int numbers (i + 1).toNat := by
        rw [h_i1]
        rw [Int64.toInt_add_of_not_addOverflow hno_add]
        exact h_psum_succ.symm
      have h_inv_p' :
          (product * numbers.val[i.toNat]'hi_lt).toInt =
            product_of_int numbers (i + 1).toNat := by
        rw [h_i1]
        rw [Int64.toInt_mul_of_not_mulOverflow hno_mul]
        exact h_pprod_succ.symm
      have h_m_le : numbers.val.size - (i + 1).toNat ≤ m := by
        rw [h_i1]; omega
      have h_i1_le : (i + 1).toNat ≤ numbers.val.size := by
        rw [h_i1]; omega
      exact ih (i + 1)
        (sum + numbers.val[i.toNat]'hi_lt)
        (product * numbers.val[i.toNat]'hi_lt)
        h_m_le h_i1_le h_inv_s' h_inv_p' hfit_s hfit_p

/-! ## Top-level theorems

Each obligation specialises `sum_product_at_correct` at
`i := (0 : usize), sum := (0 : i64), product := (1 : i64)`, where the
prefix-sum invariants hold by definition:
`(0 : i64).toInt = 0 = sum_of_int numbers 0` and
`(1 : i64).toInt = 1 = product_of_int numbers 0`. -/

/-- Empty-slice boundary contract.

    Captures the property test `empty_input_returns_zero_and_one`:
    `sum_product(&[]) == (0, 1)`. This pins down the identity elements
    `(0, 1)` — without it, every other seed pair would satisfy the
    recursive postconditions vacuously on the empty slice. -/
theorem empty_returns_zero_one (numbers : RustSlice i64)
    (hempty : numbers.val.size = 0) :
    clever_008_sum_product.sum_product numbers =
      RustM.ok (rust_primitives.hax.Tuple2.mk (0 : i64) (1 : i64)) := by
  unfold clever_008_sum_product.sum_product
  have hi_ge : numbers.val.size ≤ (0 : usize).toNat := by
    show numbers.val.size ≤ 0
    omega
  exact sum_product_at_oob numbers (0 : usize) (0 : i64) (1 : i64) hi_ge

/-- Sum-component postcondition.

    Captures the property test `sum_component_matches_iter_sum`: under a
    no-overflow precondition on every running sum and product (the test
    chooses bounded values so that neither overflows), the first component
    of `sum_product numbers` equals the `Int`-valued sum of the elements.

    The `hfit_prod` precondition is required because the recursion threads
    both accumulators in lockstep: if `*?` overflows, the function fails
    before producing any value at all, so even the sum claim depends on
    product not overflowing. -/
theorem sum_component_correct (numbers : RustSlice i64)
    (hfit_sum  : ∀ k : Nat, k ≤ numbers.val.size →
                  -(2^63 : Int) ≤ sum_of_int     numbers k
                  ∧ sum_of_int     numbers k < 2^63)
    (hfit_prod : ∀ k : Nat, k ≤ numbers.val.size →
                  -(2^63 : Int) ≤ product_of_int numbers k
                  ∧ product_of_int numbers k < 2^63) :
    ∃ s p : i64,
      clever_008_sum_product.sum_product numbers =
        RustM.ok (rust_primitives.hax.Tuple2.mk s p) ∧
      s.toInt = sum_of_int numbers numbers.val.size := by
  unfold clever_008_sum_product.sum_product
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_inv_s : (0 : i64).toInt = sum_of_int numbers (0 : usize).toNat := by
    rw [h_zero_toNat, i64_zero_toInt]; rfl
  have h_inv_p : (1 : i64).toInt = product_of_int numbers (0 : usize).toNat := by
    rw [h_zero_toNat, i64_one_toInt]; rfl
  have h_m_le : numbers.val.size - (0 : usize).toNat ≤ numbers.val.size := by
    rw [h_zero_toNat]; omega
  have h_i_le : (0 : usize).toNat ≤ numbers.val.size := by
    rw [h_zero_toNat]; omega
  obtain ⟨s, p, h_eq, h_s, _h_p⟩ :=
    sum_product_at_correct numbers numbers.val.size (0 : usize) (0 : i64) (1 : i64)
      h_m_le h_i_le h_inv_s h_inv_p hfit_sum hfit_prod
  exact ⟨s, p, h_eq, h_s⟩

/-- Product-component postcondition.

    Captures the property test `product_component_matches_iter_product`:
    under a no-overflow precondition on every running sum and product, the
    second component of `sum_product numbers` equals the `Int`-valued
    product of the elements.

    This is independent of `sum_component_correct`: a buggy implementation
    could compute sum correctly but accumulate product wrong (e.g.
    initialize product to `0`, or skip the first element). -/
theorem product_component_correct (numbers : RustSlice i64)
    (hfit_sum  : ∀ k : Nat, k ≤ numbers.val.size →
                  -(2^63 : Int) ≤ sum_of_int     numbers k
                  ∧ sum_of_int     numbers k < 2^63)
    (hfit_prod : ∀ k : Nat, k ≤ numbers.val.size →
                  -(2^63 : Int) ≤ product_of_int numbers k
                  ∧ product_of_int numbers k < 2^63) :
    ∃ s p : i64,
      clever_008_sum_product.sum_product numbers =
        RustM.ok (rust_primitives.hax.Tuple2.mk s p) ∧
      p.toInt = product_of_int numbers numbers.val.size := by
  unfold clever_008_sum_product.sum_product
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_inv_s : (0 : i64).toInt = sum_of_int numbers (0 : usize).toNat := by
    rw [h_zero_toNat, i64_zero_toInt]; rfl
  have h_inv_p : (1 : i64).toInt = product_of_int numbers (0 : usize).toNat := by
    rw [h_zero_toNat, i64_one_toInt]; rfl
  have h_m_le : numbers.val.size - (0 : usize).toNat ≤ numbers.val.size := by
    rw [h_zero_toNat]; omega
  have h_i_le : (0 : usize).toNat ≤ numbers.val.size := by
    rw [h_zero_toNat]; omega
  obtain ⟨s, p, h_eq, _h_s, h_p⟩ :=
    sum_product_at_correct numbers numbers.val.size (0 : usize) (0 : i64) (1 : i64)
      h_m_le h_i_le h_inv_s h_inv_p hfit_sum hfit_prod
  exact ⟨s, p, h_eq, h_p⟩

end Clever_008_sum_productObligations
