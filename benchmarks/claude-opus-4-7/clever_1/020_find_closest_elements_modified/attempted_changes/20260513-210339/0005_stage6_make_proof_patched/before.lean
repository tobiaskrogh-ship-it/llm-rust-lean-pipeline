-- Companion obligations file for the `clever_020_find_closest_elements` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_020_find_closest_elements

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_020_find_closest_elementsObligations

open clever_020_find_closest_elements

/-! ## Helpers transferred from reference obligations -/

/-- `RustM.ok x >>= f = f x`. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

private theorem usize_two_toNat : (2 : usize).toNat = 2 := rfl

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

/-- Bind-success: from `(x >>= f) = ok b`, extract a witness `a`. -/
private theorem RustM_bind_ok_iff {α β : Type} (x : RustM α) (f : α → RustM β) (b : β) :
    (x >>= f) = RustM.ok b ↔ ∃ a, x = RustM.ok a ∧ f a = RustM.ok b := by
  constructor
  · intro h
    cases hx : x with
    | none =>
      exfalso
      rw [hx] at h
      cases h
    | some r =>
      cases r with
      | error e =>
        exfalso
        rw [hx] at h
        cases h
      | ok v =>
        refine ⟨v, rfl, ?_⟩
        rw [hx] at h
        exact h
  · rintro ⟨a, hx, hfa⟩
    rw [hx]
    show f a = RustM.ok b
    exact hfa

/-- From `(numbers[i]_? : RustM i64) = ok v`, extract `i.toNat < size` and `v = numbers.val[i.toNat]`. -/
private theorem slice_get_ok_iff (numbers : RustSlice i64) (i : usize) (v : i64) :
    (numbers[i]_? : RustM i64) = RustM.ok v ↔
    ∃ (hi : i.toNat < numbers.val.size), numbers.val[i.toNat]'hi = v := by
  show (if h : i.toNat < numbers.val.size then pure (numbers.val[i])
          else (.fail .arrayOutOfBounds : RustM i64))
      = RustM.ok v ↔ _
  by_cases hi : i.toNat < numbers.val.size
  · rw [dif_pos hi]
    constructor
    · intro h
      refine ⟨hi, ?_⟩
      injection h with h1
      injection h1 with h2
      exact h2
    · rintro ⟨_, h⟩
      show (pure (numbers.val[i.toNat]'hi) : RustM i64) = RustM.ok v
      rw [h]
      rfl
  · rw [dif_neg hi]
    constructor
    · intro h
      cases h
    · rintro ⟨h, _⟩
      exact absurd h hi

/-- `i64` ≤ via `toInt`. -/
private theorem i64_le_iff_toInt_le (a b : i64) : a ≤ b ↔ a.toInt ≤ b.toInt :=
  Int64.le_iff_toInt_le

private theorem i64_lt_iff_toInt_lt (a b : i64) : a < b ↔ a.toInt < b.toInt :=
  Int64.lt_iff_toInt_lt

/-- Short-input boundary / failure contract.

    Captures the unit test `short_input_returns_zero_zero`: when the input
    slice has fewer than two elements (`numbers.len() < 2`), the function
    returns the sentinel pair `(0, 0)` and does not panic. Pins down the
    `len < 2` defensive branch — without this clause, every other pair
    would satisfy the postconditions vacuously on short inputs. -/
theorem short_input_returns_zero_zero
    (numbers : RustSlice i64) (hshort : numbers.val.size < 2) :
    find_closest_elements numbers
      = RustM.ok (rust_primitives.hax.Tuple2.mk (0 : i64) (0 : i64)) := by
  unfold find_closest_elements
  have h_size_lt : numbers.val.size < 2^64 := numbers.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat numbers.val.size < (2 : usize)) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.lt_iff_toNat_lt, h_ofNat]
    show numbers.val.size < 2
    exact hshort
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.lt, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- Postcondition 1 (ordering): the returned pair is ordered
    `(smaller, larger)`.

    Captures the property test `result_is_ordered`. We state the inequality
    over `Int` (via `toInt`) so the spec itself is free of signed-comparison
    subtleties at the `i64` level. The hypothesis `find_closest_elements
    numbers = RustM.ok ⟨a, b⟩` folds in the implicit no-overflow precondition
    — a panicking call simply doesn't reach this obligation. -/
theorem result_is_ordered
    (numbers : RustSlice i64) (a b : i64)
    (hres : find_closest_elements numbers
              = RustM.ok (rust_primitives.hax.Tuple2.mk a b)) :
    a.toInt ≤ b.toInt := by
  sorry

/-- Postcondition 2 (witness in input): both returned values appear in the
    input at two distinct positions.

    Captures the property test `result_elements_drawn_from_input`. The
    precondition `2 ≤ numbers.val.size` excludes the `len < 2` sentinel
    branch — when the slice is shorter than 2, the function returns
    `(0, 0)` regardless of whether `0` appears in the input, so the
    obligation would not hold there (and is anyway covered by
    `short_input_returns_zero_zero`). With `len ≥ 2` and a successful
    result, the function returns elements actually drawn from the slice. -/
theorem result_elements_drawn_from_input
    (numbers : RustSlice i64) (a b : i64)
    (hlen : 2 ≤ numbers.val.size)
    (hres : find_closest_elements numbers
              = RustM.ok (rust_primitives.hax.Tuple2.mk a b)) :
    ∃ i j : Nat, ∃ (hi : i < numbers.val.size) (hj : j < numbers.val.size),
      i ≠ j ∧ numbers.val[i]'hi = a ∧ numbers.val[j]'hj = b := by
  sorry

/-- Postcondition 3 (minimality): the difference `b - a` of the returned
    pair is at most the absolute difference of any other distinct index
    pair `i < j` in the input.

    Captures the property test `result_difference_is_minimum`. The
    difference and absolute value are computed in `Int` (using
    `Int.natAbs`) so the spec sidesteps `i64` subtraction overflow at the
    spec level — same encoding used by
    `Clever_000_has_close_elementsObligations.close_pair_exists`. The
    obligation is vacuous when `numbers.val.size < 2` (no `i < j` pair
    exists), so no length precondition is required here. -/
theorem result_difference_is_minimum
    (numbers : RustSlice i64) (a b : i64)
    (hres : find_closest_elements numbers
              = RustM.ok (rust_primitives.hax.Tuple2.mk a b)) :
    ∀ i j : Nat, ∀ (hi : i < numbers.val.size) (hj : j < numbers.val.size),
      i < j →
      b.toInt - a.toInt
        ≤ (((numbers.val[i]'hi).toInt - (numbers.val[j]'hj).toInt).natAbs : Int) := by
  sorry

end Clever_020_find_closest_elementsObligations
