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
  simp only at h_rest
  -- Extract numbers[i]_? and numbers[j]_? success from h_rest
  obtain ⟨ni, h_ni, h_rest⟩ := (RustM_bind_ok_iff _ _ _).mp h_rest
  obtain ⟨nj, h_nj, h_rest⟩ := (RustM_bind_ok_iff _ _ _).mp h_rest
  obtain ⟨hi, h_ni_eq⟩ := (slice_get_ok_iff numbers i ni).mp h_ni
  obtain ⟨hj, h_nj_eq⟩ := (slice_get_ok_iff numbers j nj).mp h_nj
  refine ⟨i, j, hi, hj, h_scan, ?_⟩
  show _ ∨ _
  by_cases h_le : ni ≤ nj
  · have h_le_bool : (ni <=? nj : RustM Bool) = RustM.ok true := by
      show (rust_primitives.cmp.le ni nj : RustM Bool) = RustM.ok true
      show (pure (decide (ni ≤ nj)) : RustM Bool) = RustM.ok true
      rw [decide_eq_true h_le]
      rfl
    rw [h_le_bool] at h_rest
    simp only [RustM_ok_bind, ↓reduceIte] at h_rest
    -- h_rest now: do let _ ← numbers[i]_?; let _ ← numbers[j]_?; pure ⟨_, _⟩ = ok ⟨a, b⟩
    -- Substitute the two later numbers[i]_? / numbers[j]_? calls using h_ni, h_nj
    rw [h_ni] at h_rest
    simp only [RustM_ok_bind] at h_rest
    rw [h_nj] at h_rest
    simp only [RustM_ok_bind] at h_rest
    -- Now h_rest : pure (Tuple2.mk ni nj) = ok ⟨a, b⟩
    have h_pure : (pure (rust_primitives.hax.Tuple2.mk ni nj) :
                   RustM (rust_primitives.hax.Tuple2 i64 i64))
                   = RustM.ok (rust_primitives.hax.Tuple2.mk ni nj) := rfl
    rw [h_pure] at h_rest
    injection h_rest with h_eq
    injection h_eq with h_eq2
    have ha : a = ni := by
      injection h_eq2 with ha _; exact ha.symm
    have hb : b = nj := by
      injection h_eq2 with _ hb; exact hb.symm
    left
    refine ⟨?_, ?_, ?_⟩
    · rw [← h_ni_eq, ← h_nj_eq] at h_le; exact h_le
    · rw [ha, ← h_ni_eq]
    · rw [hb, ← h_nj_eq]
  · have h_le_bool : (ni <=? nj : RustM Bool) = RustM.ok false := by
      show (rust_primitives.cmp.le ni nj : RustM Bool) = RustM.ok false
      show (pure (decide (ni ≤ nj)) : RustM Bool) = RustM.ok false
      rw [decide_eq_false h_le]
      rfl
    rw [h_le_bool] at h_rest
    simp only [RustM_ok_bind, ↓reduceIte, Bool.false_eq_true] at h_rest
    rw [h_nj] at h_rest
    simp only [RustM_ok_bind] at h_rest
    rw [h_ni] at h_rest
    simp only [RustM_ok_bind] at h_rest
    have h_pure : (pure (rust_primitives.hax.Tuple2.mk nj ni) :
                   RustM (rust_primitives.hax.Tuple2 i64 i64))
                   = RustM.ok (rust_primitives.hax.Tuple2.mk nj ni) := rfl
    rw [h_pure] at h_rest
    injection h_rest with h_eq
    injection h_eq with h_eq2
    have ha : a = nj := by
      injection h_eq2 with ha _; exact ha.symm
    have hb : b = ni := by
      injection h_eq2 with _ hb; exact hb.symm
    right
    refine ⟨?_, ?_, ?_⟩
    · rw [← h_ni_eq, ← h_nj_eq] at h_le; exact h_le
    · rw [ha, ← h_nj_eq]
    · rw [hb, ← h_ni_eq]

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
  by_cases hshort : numbers.val.size < 2
  · -- (0, 0) case
    have h_short := short_input_returns_zero_zero numbers hshort
    rw [h_short] at hres
    -- hres : RustM.ok ⟨0, 0⟩ = RustM.ok ⟨a, b⟩
    injection hres with h1
    injection h1 with h2
    -- h2 : Tuple2.mk 0 0 = Tuple2.mk a b
    injection h2 with ha hb
    -- ha : 0 = a, hb : 0 = b
    rw [← ha, ← hb]
    show (0 : i64).toInt ≤ (0 : i64).toInt
    omega
  · have hshort : 2 ≤ numbers.val.size := Nat.le_of_not_lt hshort
    obtain ⟨i, j, hi, hj, _, h_or⟩ :=
      find_closest_elements_structure numbers a b hshort hres
    rcases h_or with ⟨h_le, ha, hb⟩ | ⟨h_nle, ha, hb⟩
    · -- a = numbers[i], b = numbers[j], numbers[i] ≤ numbers[j]
      rw [ha, hb]
      exact Int64.le_iff_toInt_le.mp h_le
    · -- a = numbers[j], b = numbers[i], ¬(numbers[i] ≤ numbers[j])
      rw [ha, hb]
      -- Convert ¬(numbers[i] ≤ numbers[j]) to integer form via toInt
      have h_nle_int :
          ¬ (numbers.val[i.toNat]'hi).toInt ≤ (numbers.val[j.toNat]'hj).toInt := by
        intro h_le_int
        exact h_nle (Int64.le_iff_toInt_le.mpr h_le_int)
      -- Goal: (numbers.val[j.toNat]).toInt ≤ (numbers.val[i.toNat]).toInt
      omega

/-- Scan-at invariant: when `scan_at` is called with valid distinct indices
    `bi, bj` for the "best so far" pair (both < size, bi ≠ bj) and any
    cursor positions `i, j`, the returned `(retI, retJ)` is also a valid
    distinct pair of indices.

    This captures the argmin-tracking invariant of the recursion: `scan_at`
    only ever returns either its `(best_i, best_j)` arguments unchanged
    (base case `i + 1 >= n`) or updates them to `(i, j)` with `j > i ≥ 0`
    in the `cur < best` branch (where `j < n` and `i + 1 < n` from the
    branch guards). The two cases preserve "valid distinct pair".

    Left as `sorry`: the proof requires strong induction on a Nat measure
    capturing `scan_at`'s termination (e.g. `n*n - (i.toNat*n + j.toNat)`
    treated as a bounded decreasing quantity, or the lexicographic measure
    `(n - i, n - j)`). The recursion `(i+1, i+2, best_i, best_j)` strictly
    increases `i`, and `(i, j+1, ...)` strictly increases `j`, so the
    measure is well-defined. The hard parts are: (1) the `j` may exceed
    `n` in the inner branch before the `j ≥ n` check fires, requiring care
    about usize overflow on `i+1` and `i+2`; (2) `partial_fixpoint` unfolds
    require chasing the bind chain in `cur`/`best` computations through
    `abs_diff`, which can fail with overflow when `numbers[i] - numbers[j]`
    overflows `i64`. The success hypothesis on the top-level call
    propagates a no-overflow witness backwards but threading this through
    the recursion is the heart of the proof. -/
private theorem scan_at_returns_valid_pair
    (numbers : RustSlice i64) (i j bi bj retI retJ : usize)
    (hbi : bi.toNat < numbers.val.size)
    (hbj : bj.toNat < numbers.val.size)
    (hbi_ne_bj : bi.toNat ≠ bj.toNat)
    (hscan : scan_at numbers i j bi bj
              = RustM.ok (rust_primitives.hax.Tuple2.mk retI retJ)) :
    ∃ (hretI : retI.toNat < numbers.val.size)
      (hretJ : retJ.toNat < numbers.val.size),
      retI.toNat ≠ retJ.toNat := by
  sorry

/-- Postcondition 2 (witness in input): both returned values appear in the
    input at two distinct positions.

    Captures the property test `result_elements_drawn_from_input`. The
    precondition `2 ≤ numbers.val.size` excludes the `len < 2` sentinel
    branch — when the slice is shorter than 2, the function returns
    `(0, 0)` regardless of whether `0` appears in the input, so the
    obligation would not hold there (and is anyway covered by
    `short_input_returns_zero_zero`). With `len ≥ 2` and a successful
    result, the function returns elements actually drawn from the slice.

    Stuck sub-goal: showing that `scan_at`'s return indices are distinct
    (`retI ≠ retJ`) — the function definition makes this manifestly true
    by induction on the recursion (initial seed `(0, 1)` has 0 ≠ 1, and
    the only update `(best_i, best_j) := (i, j)` happens in a branch
    where `j > i` is invariant). The structural unblock is the
    `scan_at_returns_valid_pair` helper above, which captures exactly
    this invariant via strong induction on the recursion measure. -/
theorem result_elements_drawn_from_input
    (numbers : RustSlice i64) (a b : i64)
    (hlen : 2 ≤ numbers.val.size)
    (hres : find_closest_elements numbers
              = RustM.ok (rust_primitives.hax.Tuple2.mk a b)) :
    ∃ i j : Nat, ∃ (hi : i < numbers.val.size) (hj : j < numbers.val.size),
      i ≠ j ∧ numbers.val[i]'hi = a ∧ numbers.val[j]'hj = b := by
  obtain ⟨ri, rj, hri, hrj, h_scan, h_or⟩ :=
    find_closest_elements_structure numbers a b hlen hres
  -- Seed for scan_at is (0, 1), both < size (from hlen ≥ 2), and 0 ≠ 1.
  have h0_lt : (0 : usize).toNat < numbers.val.size := by
    show 0 < numbers.val.size; omega
  have h1_lt : (1 : usize).toNat < numbers.val.size := by
    show 1 < numbers.val.size; omega
  have h01_ne : (0 : usize).toNat ≠ (1 : usize).toNat := by decide
  obtain ⟨hretI, hretJ, hne⟩ :=
    scan_at_returns_valid_pair numbers (0 : usize) (1 : usize) (0 : usize) (1 : usize)
      ri rj h0_lt h1_lt h01_ne h_scan
  rcases h_or with ⟨_h_le, ha, hb⟩ | ⟨_h_nle, ha, hb⟩
  · -- a = numbers[ri], b = numbers[rj]
    refine ⟨ri.toNat, rj.toNat, hri, hrj, hne, ?_, ?_⟩
    · exact ha.symm
    · exact hb.symm
  · -- a = numbers[rj], b = numbers[ri]
    refine ⟨rj.toNat, ri.toNat, hrj, hri, hne.symm, ?_, ?_⟩
    · exact ha.symm
    · exact hb.symm

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
