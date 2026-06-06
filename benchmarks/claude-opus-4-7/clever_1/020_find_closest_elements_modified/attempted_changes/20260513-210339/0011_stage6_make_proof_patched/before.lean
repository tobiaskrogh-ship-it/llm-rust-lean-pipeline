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
      have h' : pure (numbers.val[i]) =
                  RustM.ok (numbers.val[i.toNat]'hi) := rfl
      rw [h'] at h
      -- h : RustM.ok (numbers.val[i.toNat]'hi) = RustM.ok v
      cases h
      rfl
    · rintro ⟨_, h⟩
      show (pure (numbers.val[i]) : RustM i64) = RustM.ok v
      have h' : (pure (numbers.val[i]) : RustM i64) =
                  RustM.ok (numbers.val[i.toNat]'hi) := rfl
      rw [h', h]
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

/-! ## Helpers for `result_is_ordered` / postconditions

The function returns `(0, 0)` on short inputs and otherwise swaps to order
the result pair. The swap is the only structural piece needed for ordering
(scan_at's correctness is irrelevant). We extract the "either swap path"
structure as a lemma. -/

/-- Structural decomposition of a successful `find_closest_elements` result
    when `2 ≤ len`. Either:
      - the function returns `⟨na, nb⟩` where `na, nb` come from valid indices
        `i, j` returned by `scan_at` and `na ≤ nb`; or
      - the function returns `⟨nb, na⟩` where `na, nb` come from valid indices
        `i, j` returned by `scan_at` and `nb < na`.

    The hypothesis on `len` is needed because the short-input branch returns
    a constant sentinel that doesn't go through the swap. -/
private theorem find_closest_elements_structure
    (numbers : RustSlice i64) (a b : i64)
    (hlen : 2 ≤ numbers.val.size)
    (hres : find_closest_elements numbers
              = RustM.ok (rust_primitives.hax.Tuple2.mk a b)) :
    ∃ (i j : usize) (hi : i.toNat < numbers.val.size)
      (hj : j.toNat < numbers.val.size),
      scan_at numbers (0 : usize) (1 : usize) (0 : usize) (1 : usize)
        = RustM.ok (rust_primitives.hax.Tuple2.mk i j) ∧
      ((numbers.val[i.toNat]'hi ≤ numbers.val[j.toNat]'hj ∧
        a = numbers.val[i.toNat]'hi ∧ b = numbers.val[j.toNat]'hj) ∨
       (¬ (numbers.val[i.toNat]'hi ≤ numbers.val[j.toNat]'hj) ∧
        a = numbers.val[j.toNat]'hj ∧ b = numbers.val[i.toNat]'hi)) := by
  unfold find_closest_elements at hres
  have h_size_lt : numbers.val.size < 2^64 := numbers.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_lt : decide (USize64.ofNat numbers.val.size < (2 : usize)) = false := by
    rw [decide_eq_false_iff_not]
    rw [USize64.lt_iff_toNat_lt, h_ofNat]
    show ¬ numbers.val.size < 2
    omega
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.lt, pure_bind,
             h_cond_lt, ↓reduceIte, Bool.false_eq_true] at hres
  -- Now hres = (scan_at ... >>= fun ⟨i, j⟩ => ...) = ok ⟨a, b⟩.
  obtain ⟨t, h_scan, h_rest⟩ := (RustM_bind_ok_iff _ _ _).mp hres
  obtain ⟨i, j⟩ := t
  -- h_rest : body[i, j] = ok ⟨a, b⟩
  simp only at h_rest
  -- Extract numbers[i]_? and numbers[j]_? success from h_rest
  obtain ⟨ni, h_ni, h_rest⟩ := (RustM_bind_ok_iff _ _ _).mp h_rest
  obtain ⟨nj, h_nj, h_rest⟩ := (RustM_bind_ok_iff _ _ _).mp h_rest
  obtain ⟨hi, h_ni_eq⟩ := (slice_get_ok_iff numbers i ni).mp h_ni
  obtain ⟨hj, h_nj_eq⟩ := (slice_get_ok_iff numbers j nj).mp h_nj
  -- h_rest is now the if-then-else on the comparison
  refine ⟨i, j, hi, hj, h_scan, ?_⟩
  -- Case-split on ni <=? nj
  show _ ∨ _
  by_cases h_le : ni ≤ nj
  · -- ni ≤ nj: first branch
    have h_le_bool : (ni <=? nj : RustM Bool) = RustM.ok true := by
      show (rust_primitives.cmp.le ni nj : RustM Bool) = RustM.ok true
      show (pure (decide (ni ≤ nj)) : RustM Bool) = RustM.ok true
      rw [decide_eq_true h_le]
      rfl
    rw [h_le_bool] at h_rest
    simp only [RustM_ok_bind, ↓reduceIte] at h_rest
    -- h_rest : (do let x ← numbers[i]_?; let y ← numbers[j]_?; pure ⟨x, y⟩) = ok ⟨a, b⟩
    obtain ⟨ni', h_ni', h_rest⟩ := (RustM_bind_ok_iff _ _ _).mp h_rest
    obtain ⟨nj', h_nj', h_rest⟩ := (RustM_bind_ok_iff _ _ _).mp h_rest
    obtain ⟨_, h_ni'_eq⟩ := (slice_get_ok_iff numbers i ni').mp h_ni'
    obtain ⟨_, h_nj'_eq⟩ := (slice_get_ok_iff numbers j nj').mp h_nj'
    -- ni' = numbers.val[i.toNat]'hi = ni, similarly nj' = nj
    have h_ni_id : ni' = ni := by rw [← h_ni'_eq]; exact h_ni_eq
    have h_nj_id : nj' = nj := by rw [← h_nj'_eq]; exact h_nj_eq
    subst h_ni_id
    subst h_nj_id
    -- h_rest : pure (Tuple2.mk ni nj) = ok ⟨a, b⟩
    have h_pure : (pure (rust_primitives.hax.Tuple2.mk ni nj) :
                   RustM (rust_primitives.hax.Tuple2 i64 i64))
                   = RustM.ok (rust_primitives.hax.Tuple2.mk ni nj) := rfl
    rw [h_pure] at h_rest
    -- Inject
    injection h_rest with h_eq
    injection h_eq with h_eq2
    have ha : a = ni := by
      injection h_eq2 with ha _
      exact ha.symm
    have hb : b = nj := by
      injection h_eq2 with _ hb
      exact hb.symm
    left
    refine ⟨?_, ?_, ?_⟩
    · rw [← h_ni_eq, ← h_nj_eq] at h_le; exact h_le
    · rw [ha, ← h_ni_eq]
    · rw [hb, ← h_nj_eq]
  · -- ¬ (ni ≤ nj): second branch
    have h_le_bool : (ni <=? nj : RustM Bool) = RustM.ok false := by
      show (rust_primitives.cmp.le ni nj : RustM Bool) = RustM.ok false
      show (pure (decide (ni ≤ nj)) : RustM Bool) = RustM.ok false
      rw [decide_eq_false h_le]
      rfl
    rw [h_le_bool] at h_rest
    simp only [RustM_ok_bind, ↓reduceIte, Bool.false_eq_true] at h_rest
    -- h_rest : (do let x ← numbers[j]_?; let y ← numbers[i]_?; pure ⟨x, y⟩) = ok ⟨a, b⟩
    obtain ⟨nj', h_nj', h_rest⟩ := (RustM_bind_ok_iff _ _ _).mp h_rest
    obtain ⟨ni', h_ni', h_rest⟩ := (RustM_bind_ok_iff _ _ _).mp h_rest
    obtain ⟨_, h_nj'_eq⟩ := (slice_get_ok_iff numbers j nj').mp h_nj'
    obtain ⟨_, h_ni'_eq⟩ := (slice_get_ok_iff numbers i ni').mp h_ni'
    have h_ni_id : ni' = ni := by rw [← h_ni'_eq]; exact h_ni_eq
    have h_nj_id : nj' = nj := by rw [← h_nj'_eq]; exact h_nj_eq
    subst h_ni_id
    subst h_nj_id
    have h_pure : (pure (rust_primitives.hax.Tuple2.mk nj ni) :
                   RustM (rust_primitives.hax.Tuple2 i64 i64))
                   = RustM.ok (rust_primitives.hax.Tuple2.mk nj ni) := rfl
    rw [h_pure] at h_rest
    injection h_rest with h_eq
    injection h_eq with h_eq2
    have ha : a = nj := by
      injection h_eq2 with ha _
      exact ha.symm
    have hb : b = ni := by
      injection h_eq2 with _ hb
      exact hb.symm
    right
    refine ⟨?_, ?_, ?_⟩
    · rw [← h_ni_eq, ← h_nj_eq]; exact h_le
    · rw [ha, ← h_nj_eq]
    · rw [hb, ← h_ni_eq]

theorem result_is_ordered
    (numbers : RustSlice i64) (a b : i64)
    (hres : find_closest_elements numbers
              = RustM.ok (rust_primitives.hax.Tuple2.mk a b)) :
    a.toInt ≤ b.toInt := by
  by_cases hshort : numbers.val.size < 2
  · -- (0, 0) case
    have h_short := short_input_returns_zero_zero numbers hshort
    rw [h_short] at hres
    -- hres : RustM.ok ⟨0, 0⟩ = RustM.ok ⟨a, b⟩
    injection hres with h1
    injection h1 with h2
    have ha : (0 : i64) = a := by injection h2 with ha _; exact ha
    have hb : (0 : i64) = b := by injection h2 with _ hb; exact hb
    rw [← ha, ← hb]
  · push_neg at hshort
    obtain ⟨i, j, hi, hj, _, h_or⟩ :=
      find_closest_elements_structure numbers a b hshort hres
    rcases h_or with ⟨h_le, ha, hb⟩ | ⟨h_nle, ha, hb⟩
    · -- a = numbers[i], b = numbers[j], numbers[i] ≤ numbers[j]
      rw [ha, hb]
      exact Int64.le_iff_toInt_le.mp h_le
    · -- a = numbers[j], b = numbers[i], ¬(numbers[i] ≤ numbers[j])
      rw [ha, hb]
      have h_lt : numbers.val[j.toNat]'hj < numbers.val[i.toNat]'hi := by
        rcases lt_or_ge (numbers.val[j.toNat]'hj) (numbers.val[i.toNat]'hi) with h | h
        · exact h
        · exact absurd h h_nle
      exact le_of_lt (Int64.lt_iff_toInt_lt.mp h_lt)

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
