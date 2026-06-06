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

/-! ## Step lemmas for `scan_at`

The function has four branches: a base case (`i+1 ≥ n`) returning
`(bi, bj)`, an "advance i" case (`j ≥ n`) recursing with `(i+1, i+2)`,
and two inner cases (`cur < best` / otherwise) recursing with `(i, j+1)`
and either `(i, j)` or `(bi, bj)` as the new best. The step lemmas below
peel one iteration of the recursion when the no-overflow side conditions
on `i+1`, `i+2`, and `j+1` are satisfied. -/

/-- Helper: `usize` add does not overflow when sum < `2 ^ 64`. -/
private theorem usize_add_no_bv (i : usize) (k : usize)
    (h : i.toNat + k.toNat < 2 ^ 64) :
    BitVec.uaddOverflow i.toBitVec k.toBitVec = false := by
  generalize hbo : BitVec.uaddOverflow i.toBitVec k.toBitVec = bo
  cases bo with
  | false => rfl
  | true =>
    exfalso
    have hii := (USize64.uaddOverflow_iff i k).mp hbo
    omega

/-- Helper: `i +? k = pure (i + k)` when no overflow. -/
private theorem usize_add_eq_pure (i k : usize)
    (h : i.toNat + k.toNat < 2 ^ 64) :
    (i +? k : RustM usize) = pure (i + k) := by
  show (rust_primitives.ops.arith.Add.add i k : RustM usize) = pure (i + k)
  show (if BitVec.uaddOverflow i.toBitVec k.toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure (i + k)) = _
  rw [usize_add_no_bv i k h]; rfl

/-- Helper: `(i + k).toNat = i.toNat + k.toNat` when no overflow. -/
private theorem usize_add_toNat_of_lt (i k : usize)
    (h : i.toNat + k.toNat < 2 ^ 64) :
    (i + k).toNat = i.toNat + k.toNat :=
  USize64.toNat_add_of_lt h

/-- Base case step lemma: when `i + 1 ≥ n` (and `i + 1` does not overflow
    `usize`), `scan_at` returns `(bi, bj)` immediately. -/
private theorem scan_at_base_case
    (numbers : RustSlice i64) (i j bi bj : usize)
    (h_no_ov : i.toNat + 1 < 2 ^ 64)
    (h_ge : numbers.val.size ≤ i.toNat + 1) :
    scan_at numbers i j bi bj
      = RustM.ok (rust_primitives.hax.Tuple2.mk bi bj) := by
  conv => lhs; unfold scan_at
  have h_n_lt : numbers.val.size < 2 ^ 64 := numbers.size_lt_usizeSize
  have h_n_eq : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' h_n_lt
  have h_no_bv :
      BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hii := (USize64.uaddOverflow_iff i 1).mp hbo
      rw [usize_one_toNat] at hii
      omega
  have h_add_eq : (i +? (1 : usize) : RustM usize) = pure (i + 1) := by
    show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = pure (i + 1)
    show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
          then (.fail .integerOverflow : RustM usize)
          else pure (i + 1)) = _
    rw [h_no_bv]; rfl
  have h_i1_toNat : (i + 1).toNat = i.toNat + 1 :=
    usize_add_one_toNat i h_no_ov
  have h_ge_cond :
      decide ((USize64.ofNat numbers.val.size) ≤ (i + 1)) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_n_eq, h_i1_toNat]
    exact h_ge
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_add_eq, h_ge_cond, ↓reduceIte]
  rfl

/-- Advance-i step lemma: when `i + 1 < n` and `j ≥ n` (and `i + 2` does
    not overflow `usize`), `scan_at i j bi bj` equals
    `scan_at (i + 1) (i + 2) bi bj`. -/
private theorem scan_at_advance_i
    (numbers : RustSlice i64) (i j bi bj : usize)
    (h_no_ov_2 : i.toNat + 2 < 2 ^ 64)
    (h_i1_lt : i.toNat + 1 < numbers.val.size)
    (h_j_ge : numbers.val.size ≤ j.toNat) :
    scan_at numbers i j bi bj
      = scan_at numbers (i + 1) (i + 2) bi bj := by
  conv => lhs; unfold scan_at
  have h_n_lt : numbers.val.size < 2 ^ 64 := numbers.size_lt_usizeSize
  have h_n_eq : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' h_n_lt
  have h_no_ov_1 : i.toNat + 1 < 2 ^ 64 := by omega
  have h_no_ov_2_usize : i.toNat + (2 : usize).toNat < 2 ^ 64 := by
    rw [usize_two_toNat]; exact h_no_ov_2
  have h_no_ov_1_usize : i.toNat + (1 : usize).toNat < 2 ^ 64 := by
    rw [usize_one_toNat]; exact h_no_ov_1
  have h_add_1_eq : (i +? (1 : usize) : RustM usize) = pure (i + 1) :=
    usize_add_eq_pure i 1 h_no_ov_1_usize
  have h_add_2_eq : (i +? (2 : usize) : RustM usize) = pure (i + 2) :=
    usize_add_eq_pure i 2 h_no_ov_2_usize
  have h_i1_toNat : (i + 1).toNat = i.toNat + 1 :=
    usize_add_one_toNat i h_no_ov_1
  have h_ge_cond_false :
      decide ((USize64.ofNat numbers.val.size) ≤ (i + 1)) = false := by
    rw [decide_eq_false_iff_not]
    rw [USize64.le_iff_toNat_le, h_n_eq, h_i1_toNat]
    omega
  have h_j_ge_cond :
      decide ((USize64.ofNat numbers.val.size) ≤ j) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_n_eq]
    exact h_j_ge
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_add_1_eq, h_add_2_eq, h_ge_cond_false, h_j_ge_cond,
             Bool.false_eq_true, ↓reduceIte]

/-- Scan-at invariant: when `scan_at` is called with valid distinct indices
    `bi, bj` for the "best so far" pair (both < size, bi ≠ bj), with the
    cursor invariant `j > i`, the returned `(retI, retJ)` is also a valid
    distinct pair of indices.

    The cursor invariant `j > i` is what links the inner-update branch
    `(bi, bj) := (i, j)` to preservation of `bi ≠ bj`: since `j > i`, the
    new best pair is distinct. The seed `(i, j) = (0, 1)` used at the
    top level satisfies `j > i`, and each recursive call preserves it
    (`(i+1, i+2)` has `i+2 > i+1`, and `(i, j+1)` has `j+1 > j > i`).

    Stuck sub-goal (despite a substantive attempt below): the strong-
    induction step requires `partial_fixpoint`-style equational unfolding
    of `scan_at` AND chasing the bind chain through the inner
    `abs_diff` calls. Specifically:
      * After `unfold scan_at`, the inner branch's `let cur ← abs_diff
        (← numbers[i]_?) (← numbers[j]_?)` requires extracting four
        ok-witnesses: `(numbers[i]_? = ok a_i)`, `(numbers[j]_? = ok a_j)`,
        `(a_i -? a_j = ok cur)` (or `a_j -? a_i` after the swap), and
        analogously for `best`.
      * Each `abs_diff` call requires `Int64.subOverflow` to be `false`
        at runtime, and the hypothesis `hscan = ok _` propagates only an
        *existential* witness — it doesn't expose the concrete values
        of `cur` and `best` symbolically.
      * The branching on `cur < best` then routes to one of two
        recursive calls, each of which needs the IH applied with a
        decreased Nat measure.
    The Clever_000 reference does this for a single-counter scan via
    `step_analyze` (~250 lines); doing it for a two-counter scan with
    paired update is roughly twice that. The structural unblock is
    porting / adapting `Clever_000_has_close_elementsObligations.step_analyze`
    to a `scan_at`-shaped two-cursor invariant. -/
private theorem scan_at_invariant_advance_i_REMOVED
    (numbers : RustSlice i64) :
    ∀ (m : Nat) (i j bi bj retI retJ : usize),
      numbers.val.size - min i.toNat numbers.val.size ≤ m →
      bi.toNat < numbers.val.size →
      bj.toNat < numbers.val.size →
      bi.toNat ≠ bj.toNat →
      -- Restrict to the advance-i regime: `j ≥ n`.
      numbers.val.size ≤ j.toNat →
      scan_at numbers i j bi bj = RustM.ok ⟨retI, retJ⟩ →
      ∃ (hretI : retI.toNat < numbers.val.size)
        (hretJ : retJ.toNat < numbers.val.size),
        retI.toNat ≠ retJ.toNat := by
  intro m
  induction m with
  | zero =>
    intro i j bi bj retI retJ hm hbi hbj hbi_ne hj_ge hscan
    -- m = 0 ⇒ size ≤ min i.toNat size, so i.toNat ≥ size, hence i + 1 ≥ size.
    have h_i_ge : numbers.val.size ≤ i.toNat := by
      by_cases hi_le : i.toNat ≤ numbers.val.size
      · have : min i.toNat numbers.val.size = i.toNat := Nat.min_eq_left hi_le
        rw [this] at hm; omega
      · omega
    have h_n_lt : numbers.val.size < 2 ^ 64 := numbers.size_lt_usizeSize
    have h_i_lt_64 : i.toNat < 2 ^ 64 := i.toNat_lt_size
    have h_no_ov : i.toNat + 1 < 2 ^ 64 := by
      -- i.toNat < 2^64. If i.toNat = 2^64 - 1 then i + 1 overflows. But since
      -- size ≤ i.toNat and size < 2^64, we have i.toNat ≥ size, but i.toNat could
      -- still be 2^64 - 1. However, scan_at = ok forces i+1 not to overflow.
      by_cases h : i.toNat + 1 < 2 ^ 64
      · exact h
      · exfalso
        -- Same reasoning as the overflow contradiction in scan_at_returns_valid_pair.
        conv at hscan => lhs; unfold scan_at
        have h_ov_bv :
            BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = true := by
          rw [USize64.uaddOverflow_iff, usize_one_toNat]
          omega
        have h_add_fail :
            (i +? (1 : usize) : RustM usize) = .fail .integerOverflow := by
          show (rust_primitives.ops.arith.Add.add i 1 : RustM usize)
                = .fail .integerOverflow
          show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
                then (.fail .integerOverflow : RustM usize)
                else pure (i + 1)) = _
          rw [h_ov_bv]; rfl
        simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
                   pure_bind, h_add_fail] at hscan
        simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
                   Option.bind] at hscan
        cases hscan
    have h_ge_one : numbers.val.size ≤ i.toNat + 1 := by omega
    have h_base := scan_at_base_case numbers i j bi bj h_no_ov h_ge_one
    rw [h_base] at hscan
    injection hscan with h_eq
    injection h_eq with h_eq2
    injection h_eq2 with h_eq_bi h_eq_bj
    refine ⟨?_, ?_, ?_⟩
    · rw [← h_eq_bi]; exact hbi
    · rw [← h_eq_bj]; exact hbj
    · rw [← h_eq_bi, ← h_eq_bj]; exact hbi_ne
  | succ m ih =>
    intro i j bi bj retI retJ hm hbi hbj hbi_ne hj_ge hscan
    -- Case-split: i + 1 ≥ n (base case) or i + 1 < n (advance-i case).
    by_cases h_no_ov : i.toNat + 1 < 2 ^ 64
    · by_cases h_ge : numbers.val.size ≤ i.toNat + 1
      · -- Base case via scan_at_base_case.
        have h_base := scan_at_base_case numbers i j bi bj h_no_ov h_ge
        rw [h_base] at hscan
        injection hscan with h_eq
        injection h_eq with h_eq2
        injection h_eq2 with h_eq_bi h_eq_bj
        refine ⟨?_, ?_, ?_⟩
        · rw [← h_eq_bi]; exact hbi
        · rw [← h_eq_bj]; exact hbj
        · rw [← h_eq_bi, ← h_eq_bj]; exact hbi_ne
      · -- Advance-i case: peel one iteration, recurse via IH.
        have h_i1_lt : i.toNat + 1 < numbers.val.size := Nat.lt_of_not_le h_ge
        have h_n_lt : numbers.val.size < 2 ^ 64 := numbers.size_lt_usizeSize
        have h_no_ov_2 : i.toNat + 2 < 2 ^ 64 := by omega
        have h_step := scan_at_advance_i numbers i j bi bj h_no_ov_2 h_i1_lt hj_ge
        rw [h_step] at hscan
        -- Apply IH with new i' = i + 1, new j' = i + 2, same (bi, bj).
        have h_i1_toNat : (i + 1).toNat = i.toNat + 1 :=
          usize_add_one_toNat i h_no_ov
        have h_i2_no_ov_usize : i.toNat + (2 : usize).toNat < 2 ^ 64 := by
          rw [usize_two_toNat]; exact h_no_ov_2
        have h_i2_toNat : (i + 2).toNat = i.toNat + 2 :=
          usize_add_toNat_of_lt i 2 h_i2_no_ov_usize
        have h_new_j_ge : numbers.val.size ≤ (i + 2).toNat := by
          rw [h_i2_toNat]; omega
        have h_new_measure :
            numbers.val.size - min (i + 1).toNat numbers.val.size ≤ m := by
          rw [h_i1_toNat]
          have hmin : min (i.toNat + 1) numbers.val.size ≤ numbers.val.size :=
            Nat.min_le_right _ _
          -- Need: size - min (i+1) size ≤ m.
          -- We have: size - min i size ≤ m + 1 (from hm).
          have hmin_orig : min i.toNat numbers.val.size ≤ numbers.val.size :=
            Nat.min_le_right _ _
          -- (i+1) ≤ size (since i+1 < size), so min (i+1) size = i+1.
          have h_min_eq : min (i.toNat + 1) numbers.val.size = i.toNat + 1 :=
            Nat.min_eq_left (Nat.le_of_lt h_i1_lt)
          rw [h_min_eq]
          -- size - min i size ≥ size - i (since min ≤ i), and we need ≤ m.
          -- Use that i.toNat ≤ size (otherwise i + 1 < size impossible), so
          -- min i.toNat size = i.toNat.
          have h_i_le : i.toNat ≤ numbers.val.size := by omega
          have h_min_orig_eq : min i.toNat numbers.val.size = i.toNat :=
            Nat.min_eq_left h_i_le
          rw [h_min_orig_eq] at hm
          omega
        exact ih (i + 1) (i + 2) bi bj retI retJ
                 h_new_measure hbi hbj hbi_ne h_new_j_ge hscan
    · -- i + 1 overflows ⇒ scan_at fails, contradiction.
      exfalso
      conv at hscan => lhs; unfold scan_at
      have h_ov_bv :
          BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = true := by
        rw [USize64.uaddOverflow_iff, usize_one_toNat]
        omega
      have h_add_fail :
          (i +? (1 : usize) : RustM usize) = .fail .integerOverflow := by
        show (rust_primitives.ops.arith.Add.add i 1 : RustM usize)
              = .fail .integerOverflow
        show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
              then (.fail .integerOverflow : RustM usize)
              else pure (i + 1)) = _
        rw [h_ov_bv]; rfl
      simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
                 pure_bind, h_add_fail] at hscan
      simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
                 Option.bind] at hscan
      cases hscan

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
  -- The base case handles `i + 1 ≥ n` directly. The advance-i case (when
  -- j ≥ n at every recursion step) is fully closed via
  -- `scan_at_invariant_advance_i`. The inner-branch case (j < n) remains
  -- as a documented sorry — see the structural-unblock note above.
  by_cases h_no_ov : i.toNat + 1 < 2 ^ 64
  · by_cases h_ge : numbers.val.size ≤ i.toNat + 1
    · -- Base case: scan_at returns (bi, bj) directly, so (retI, retJ) = (bi, bj).
      have h_base := scan_at_base_case numbers i j bi bj h_no_ov h_ge
      rw [h_base] at hscan
      injection hscan with h_eq
      injection h_eq with h_eq2
      injection h_eq2 with h_eq_bi h_eq_bj
      refine ⟨?_, ?_, ?_⟩
      · rw [← h_eq_bi]; exact hbi
      · rw [← h_eq_bj]; exact hbj
      · rw [← h_eq_bi, ← h_eq_bj]; exact hbi_ne_bj
    · -- Recursive case: i + 1 < n.
      -- Sub-case j ≥ n: handled by `scan_at_invariant_advance_i`.
      -- Sub-case j < n: inner branches with abs_diff overflow chase — sorry.
      by_cases h_j_ge : numbers.val.size ≤ j.toNat
      · -- Advance-i sub-case via strong-induction helper.
        exact scan_at_invariant_advance_i numbers numbers.val.size i j bi bj retI retJ
          (by
            have : min i.toNat numbers.val.size ≤ numbers.val.size := Nat.min_le_right _ _
            omega)
          hbi hbj hbi_ne_bj h_j_ge hscan
      · -- Inner-branch sub-case. Stuck sub-goal: after `unfold scan_at`, the
        -- branch `j < n` opens the `let cur ← abs_diff (← numbers[i]_?)
        -- (← numbers[j]_?) ; let best ← abs_diff ...; if cur < best then ...`
        -- structure. Need to:
        -- (a) extract `numbers[i]_? = ok a_i` etc. via slice_get_ok_iff;
        -- (b) extract `abs_diff a_i a_j = ok cur` requires casing on
        --     `a_i > a_j` and then on `Int64.subOverflow a_i a_j` /
        --     `Int64.subOverflow a_j a_i`;
        -- (c) likewise for the `best` computation;
        -- (d) split on `cur < best` and recurse with the appropriate
        --     new (bi, bj) ∈ {(i, j), (old bi, old bj)};
        -- (e) for the strong induction, use a 2D Nat measure decreasing
        --     on both advance-i and j-advance recursions.
        sorry
  · -- `i + 1` overflows. Then `scan_at` fails (returns .fail), contradicting hscan.
    exfalso
    conv at hscan => lhs; unfold scan_at
    have h_n_lt : numbers.val.size < 2 ^ 64 := numbers.size_lt_usizeSize
    have h_ov_bv :
        BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = true := by
      rw [USize64.uaddOverflow_iff, usize_one_toNat]
      omega
    have h_add_fail :
        (i +? (1 : usize) : RustM usize) = .fail .integerOverflow := by
      show (rust_primitives.ops.arith.Add.add i 1 : RustM usize)
            = .fail .integerOverflow
      show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
            then (.fail .integerOverflow : RustM usize)
            else pure (i + 1)) = _
      rw [h_ov_bv]; rfl
    simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
               pure_bind, h_add_fail] at hscan
    -- After the failure of the bind, the whole expression is `.fail`, not `ok`.
    simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
               Option.bind] at hscan
    cases hscan

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

/-- Integer-valued absolute difference of two slice entries, by index.
    This sidesteps `i64` subtraction overflow at the spec level — the
    same `Int`/`Int.natAbs` encoding used by `result_difference_is_minimum`
    and `Clever_000_has_close_elementsObligations.close_pair_exists`. -/
private def abs_diff_int (numbers : RustSlice i64)
    (i j : Nat) (hi : i < numbers.val.size) (hj : j < numbers.val.size) : Int :=
  (((numbers.val[i]'hi).toInt - (numbers.val[j]'hj).toInt).natAbs : Int)

/-- Argmin correctness of `scan_at`: when called with valid initial
    `(best_i, best_j)` (both < size, distinct) and a "frontier" `(i, j)`,
    if `scan_at` returns `(retI, retJ)` successfully, then `retI, retJ`
    are valid distinct indices AND the absolute difference at those
    indices is ≤ the absolute difference at ANY pair `(p, q)` with
    `p < q < size` such that `(p, q)` is "examined" by the recursion
    starting from `(i, j)`.

    For the top-level call `scan_at numbers 0 1 0 1` with size ≥ 2, every
    pair `(p, q)` with `0 ≤ p < q < size` is examined, so the conclusion
    becomes: result is argmin of abs_diff_int over all such pairs.

    Left as `sorry`: the proof requires:
      1. A precise "examined-so-far" predicate parameterising on `(i, j)`,
         e.g. `examined(i, j, p, q) := p ≤ i ∧ (p < i ∨ q < j)` (lex
         predecessor).
      2. Strong induction on the recursion measure
         `(size - i.toNat) * size + (size - j.toNat)`, decreasing on each
         recursive call.
      3. An invariant linking `best_i, best_j` to the argmin over all
         pairs "before" `(i, j)` in lex order.
      4. Discharge of the `abs_diff` overflow obligations via a precondition
         that all `numbers[p] - numbers[q]` fit in `i64` for `p, q < size`.

    Each of these pieces is independently tractable (see
    `Clever_000_has_close_elementsObligations` for the closest archetype),
    but together they exceed the budget of this proof pass. The structural
    unblock is having this lemma as a separate, focused proof — once it
    lands, `result_difference_is_minimum` is a 5-line specialisation. -/
private theorem scan_at_argmin_correct
    (numbers : RustSlice i64) (retI retJ : usize)
    (hlen : 2 ≤ numbers.val.size)
    (hscan : scan_at numbers (0 : usize) (1 : usize) (0 : usize) (1 : usize)
              = RustM.ok (rust_primitives.hax.Tuple2.mk retI retJ)) :
    ∃ (hretI : retI.toNat < numbers.val.size)
      (hretJ : retJ.toNat < numbers.val.size),
      retI.toNat ≠ retJ.toNat ∧
      ∀ (p q : Nat) (hp : p < numbers.val.size) (hq : q < numbers.val.size),
        p < q →
        abs_diff_int numbers retI.toNat retJ.toNat hretI hretJ ≤
          abs_diff_int numbers p q hp hq := by
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
    exists), so no length precondition is required here.

    Stuck sub-goal: `b.toInt - a.toInt ≤ abs_diff_int numbers p q ...` for
    arbitrary `p < q < size` — requires that `scan_at` actually found the
    argmin, which the function definition only guarantees by induction on
    the recursion. The structural unblock is the `scan_at_argmin_correct`
    helper above; once that lemma lands, this obligation follows in a few
    lines by case-splitting on the swap path (see the closed branches in
    the proof body below). The branches `len < 2` (vacuous, no `p < q`
    fits) and the swap path are already handled mechanically — only the
    argmin-correctness step is `sorry`. -/
theorem result_difference_is_minimum
    (numbers : RustSlice i64) (a b : i64)
    (hres : find_closest_elements numbers
              = RustM.ok (rust_primitives.hax.Tuple2.mk a b)) :
    ∀ i j : Nat, ∀ (hi : i < numbers.val.size) (hj : j < numbers.val.size),
      i < j →
      b.toInt - a.toInt
        ≤ (((numbers.val[i]'hi).toInt - (numbers.val[j]'hj).toInt).natAbs : Int) := by
  intro p q hp hq hpq
  -- Vacuous branch: size < 2 implies no p < q < size exists.
  by_cases hshort : numbers.val.size < 2
  · -- p < q < size < 2 means q < 2 and p < q, so p = 0, q = 1, but size < 2 means size ≤ 1.
    omega
  · have hlen : 2 ≤ numbers.val.size := Nat.le_of_not_lt hshort
    obtain ⟨ri, rj, hri, hrj, h_scan, h_or⟩ :=
      find_closest_elements_structure numbers a b hlen hres
    obtain ⟨hretI, hretJ, _hne, h_min⟩ :=
      scan_at_argmin_correct numbers ri rj hlen h_scan
    -- h_min gives the argmin property of (ri, rj) over all pairs (p, q) with p < q.
    have h_min_pq := h_min p q hp hq hpq
    -- h_min_pq : abs_diff_int numbers ri.toNat rj.toNat hretI hretJ ≤ abs_diff_int numbers p q hp hq
    -- Now show b.toInt - a.toInt ≤ abs_diff_int at (ri, rj), i.e., a.toInt ≤ b.toInt and
    -- b - a = |numbers[ri] - numbers[rj]|.
    rcases h_or with ⟨h_le, ha, hb⟩ | ⟨h_nle, ha, hb⟩
    · -- Swap branch 1: a = numbers[ri], b = numbers[rj], numbers[ri] ≤ numbers[rj].
      rw [ha, hb]
      -- Goal: (numbers[rj]).toInt - (numbers[ri]).toInt ≤ |(numbers[p]).toInt - (numbers[q]).toInt|
      have h_le_int : (numbers.val[ri.toNat]'hri).toInt ≤ (numbers.val[rj.toNat]'hrj).toInt :=
        Int64.le_iff_toInt_le.mp h_le
      have h_abs_at_r :
          (((numbers.val[ri.toNat]'hri).toInt - (numbers.val[rj.toNat]'hrj).toInt).natAbs : Int) =
            (numbers.val[rj.toNat]'hrj).toInt - (numbers.val[ri.toNat]'hri).toInt := by
        have hd : (numbers.val[ri.toNat]'hri).toInt - (numbers.val[rj.toNat]'hrj).toInt ≤ 0 := by omega
        have hsym : ((numbers.val[ri.toNat]'hri).toInt - (numbers.val[rj.toNat]'hrj).toInt).natAbs =
                    ((numbers.val[rj.toNat]'hrj).toInt - (numbers.val[ri.toNat]'hri).toInt).natAbs := by
          have : (numbers.val[ri.toNat]'hri).toInt - (numbers.val[rj.toNat]'hrj).toInt =
                 -((numbers.val[rj.toNat]'hrj).toInt - (numbers.val[ri.toNat]'hri).toInt) := by omega
          rw [this, Int.natAbs_neg]
        rw [hsym]
        apply Int.natAbs_of_nonneg; omega
      unfold abs_diff_int at h_min_pq
      -- h_min_pq : (|numbers[ri] - numbers[rj]|.natAbs : Int) ≤ (|numbers[p] - numbers[q]|.natAbs : Int)
      rw [h_abs_at_r] at h_min_pq
      exact h_min_pq
    · -- Swap branch 2: a = numbers[rj], b = numbers[ri], ¬(numbers[ri] ≤ numbers[rj]).
      rw [ha, hb]
      have h_nle_int :
          ¬ (numbers.val[ri.toNat]'hri).toInt ≤ (numbers.val[rj.toNat]'hrj).toInt := by
        intro h_le_int
        exact h_nle (Int64.le_iff_toInt_le.mpr h_le_int)
      have h_abs_at_r :
          (((numbers.val[ri.toNat]'hri).toInt - (numbers.val[rj.toNat]'hrj).toInt).natAbs : Int) =
            (numbers.val[ri.toNat]'hri).toInt - (numbers.val[rj.toNat]'hrj).toInt := by
        apply Int.natAbs_of_nonneg; omega
      unfold abs_diff_int at h_min_pq
      rw [h_abs_at_r] at h_min_pq
      exact h_min_pq

end Clever_020_find_closest_elementsObligations
