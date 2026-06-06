-- Companion obligations file for the `is_size_align_valid_usize` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import is_size_align_valid_usize

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Is_size_align_valid_usizeObligations

open is_size_align_valid_usize

/-- Helper: when `x ≠ 0` is known, the unsigned subtraction `x - 1` does not
    overflow, so `x -? 1 = RustM.ok (x - 1)`. -/
private theorem usize_sub_one_ok {x : usize} (hx : x ≠ 0) :
    (x -? (1 : usize)) = RustM.ok (x - 1) := by
  have hno : ¬ (BitVec.usubOverflow x.toBitVec (1#64) = true) := by
    have h0 : (USize64.subOverflow x 1 = true) ↔ x.toNat < (1 : usize).toNat :=
      USize64.subOverflow_iff
    have h1 : (1 : usize).toNat = 1 := rfl
    have hxnz : x.toNat ≠ 0 := by
      intro h
      apply hx
      apply USize64.toNat_inj.mp
      exact h
    show ¬ (USize64.subOverflow x 1 = true)
    rw [h0, h1]
    omega
  show (if BitVec.usubOverflow x.toBitVec (1#64) = true then
          (RustM.fail .integerOverflow : RustM usize)
        else pure (x - 1)) = RustM.ok (x - 1)
  rw [if_neg hno]
  rfl

/-- Characterization of `is_power_of_two_usize`: always returns `ok`, with the
    Boolean value `x ≠ 0 ∧ (x &&& (x - 1) = 0)` (the classic bit-trick test). -/
private theorem is_power_of_two_usize_eq (x : usize) :
    is_power_of_two_usize x =
      RustM.ok (decide (x ≠ 0) && decide (x &&& (x - 1) = 0)) := by
  unfold is_power_of_two_usize
  by_cases hx : x = 0
  · subst hx
    decide
  · have hsub : (x -? (1 : usize)) = RustM.ok (x - 1) := usize_sub_one_ok hx
    show (do
      let __do_lift ← (pure (decide (x = 0)) : RustM Bool)
      if __do_lift = true then pure false
      else do
        let __do_lift ← (x -? (1 : usize))
        (x &&& __do_lift) ==? (0 : usize))
       = RustM.ok (decide (x ≠ 0) && decide (x &&& (x - 1) = 0))
    rw [decide_eq_false hx]
    simp only [pure_bind, Bool.false_eq_true, if_false]
    rw [hsub]
    show (do
        let __do_lift ← (pure (x - 1) : RustM usize)
        (x &&& __do_lift) ==? (0 : usize))
      = RustM.ok (decide (x ≠ 0) && decide (x &&& (x - 1) = 0))
    simp only [pure_bind]
    show (pure (decide (x &&& (x - 1) = 0)) : RustM Bool)
       = RustM.ok (decide (x ≠ 0) && decide (x &&& (x - 1) = 0))
    have h1 : decide (x ≠ 0) = true := decide_eq_true hx
    rw [h1, Bool.true_and]
    rfl

/-- Bit-trick fact: every usize that is a power of two (i.e. `x ≠ 0` and
    `x &&& (x - 1) = 0`) is bounded above by `2^63`. -/
private theorem usize_pow_of_two_le {x : usize}
    (hnz : x ≠ 0) (hand : x &&& (x - 1) = 0) :
    x.toNat ≤ 2 ^ 63 := by
  have hbv : x.toBitVec ≠ 0#64 := by
    intro h
    apply hnz
    apply USize64.toBitVec_inj.mp
    exact h
  have hbvand : x.toBitVec &&& (x.toBitVec - 1#64) = 0#64 := by
    have h1 : (x &&& (x - 1)).toBitVec = x.toBitVec &&& (x - 1).toBitVec := rfl
    have h2 : (x - 1).toBitVec = x.toBitVec - 1#64 := rfl
    have h3 : (0 : usize).toBitVec = 0#64 := rfl
    have h4 : (x &&& (x - 1)).toBitVec = (0 : usize).toBitVec := by
      rw [hand]
    rw [h1, h2] at h4
    rw [h4, h3]
  -- Now we have `x.toBitVec ≠ 0` and `x.toBitVec &&& (x.toBitVec - 1) = 0`.
  -- Reduce to a BitVec 64 claim and use bv_decide.
  show x.toBitVec.toNat ≤ 2 ^ 63
  have : x.toBitVec ≤ 0x8000000000000000#64 := by
    -- BV proof: x &&& (x-1) = 0 ∧ x ≠ 0 ⟹ x ≤ 2^63
    revert hbv hbvand
    bv_decide
  have : x.toBitVec.toNat ≤ (0x8000000000000000#64).toNat := by
    exact (BitVec.le_def.mp this)
  have hb : (0x8000000000000000#64).toNat = 2 ^ 63 := by decide
  omega

/-- From `is_power_of_two_usize align = ok true` extract `align.toNat ≤ 2^63`. -/
private theorem is_power_of_two_usize_le {align : usize}
    (h : is_power_of_two_usize align = RustM.ok true) :
    align.toNat ≤ 2 ^ 63 := by
  rw [is_power_of_two_usize_eq] at h
  have hb : (decide (align ≠ 0) && decide (align &&& (align - 1) = 0)) = true := by
    have heq := h
    injection heq with heq1
    injection heq1
  rw [Bool.and_eq_true] at hb
  obtain ⟨h1, h2⟩ := hb
  have hnz : align ≠ 0 := of_decide_eq_true h1
  have hand : align &&& (align - 1) = 0 := of_decide_eq_true h2
  exact usize_pow_of_two_le hnz hand

/-- `max_size_for_align align = ok (2^63 - align)` whenever `align.toNat ≤ 2^63`. -/
private theorem max_size_for_align_ok {align : usize}
    (h : align.toNat ≤ 2 ^ 63) :
    max_size_for_align align
      = RustM.ok ((9223372036854775808 : usize) - align) := by
  unfold max_size_for_align
  have hC : ((9223372036854775808 : usize)).toNat = 2 ^ 63 := by decide
  have hno : ¬ (BitVec.usubOverflow (9223372036854775808 : usize).toBitVec align.toBitVec = true) := by
    show ¬ (USize64.subOverflow (9223372036854775808 : usize) align = true)
    rw [USize64.subOverflow_iff]
    rw [hC]
    omega
  show (if BitVec.usubOverflow (9223372036854775808 : usize).toBitVec align.toBitVec = true then
          (RustM.fail .integerOverflow : RustM usize)
        else pure ((9223372036854775808 : usize) - align))
      = RustM.ok ((9223372036854775808 : usize) - align)
  rw [if_neg hno]
  rfl

/-- Postcondition (failure / rejects non-power-of-two): when `align` is not
    a power of two (as decided by the helper `is_power_of_two_usize`), the
    function rejects regardless of `size`. Captures property tests
    `rejects_non_power_of_two` (e.g. `align ∈ {0, 3, 6}` are rejected) and
    `non_power_of_two_align_always_rejected` (sweep across non-pow-2 aligns
    and many sizes). A buggy implementation that accepted any non-power-of-two
    alignment for some size would falsify this. -/
theorem is_size_align_valid_rejects_non_power_of_two (size align : usize)
    (h : is_power_of_two_usize align = RustM.ok false) :
    is_size_align_valid size align = RustM.ok false := by
  unfold is_size_align_valid
  rw [h]
  rfl

/-- Postcondition (accepts valid input): when `align` is a power of two and
    `size.toNat + align.toNat ≤ 2^63`, the function accepts.

    The implementation rejects when `size > max_size_for_align align`, i.e.
    when `size > 2^63 - align`; equivalently (in `Nat` arithmetic), when
    `size.toNat + align.toNat > 2^63`. For a power-of-two `align ≤ 2^63`,
    this is exactly the negation of "the next multiple of `align` ≥ `size`
    fits in `isize::MAX = 2^63 - 1`", which is the round-up contract stated
    in the doc comment.

    Captures the positive branch of property test
    `power_of_two_align_matches_round_up_contract`, the low-side asserts of
    `layout_round_up_to_align_edge_cases` (`is_size_align_valid(low, align)`
    is `true`), and `layout_accepts_all_valid_alignments` (instantiated at
    `size = 0`, where `0 + align ≤ 2^63` holds for every power-of-two
    `align ≤ 2^63`). -/
theorem is_size_align_valid_accepts (size align : usize)
    (hpow : is_power_of_two_usize align = RustM.ok true)
    (hsize : size.toNat + align.toNat ≤ 2 ^ 63) :
    is_size_align_valid size align = RustM.ok true := by
  have hAlignLe : align.toNat ≤ 2 ^ 63 := is_power_of_two_usize_le hpow
  have hMax : max_size_for_align align
              = RustM.ok ((9223372036854775808 : usize) - align) :=
    max_size_for_align_ok hAlignLe
  -- Compute `size > max_size_for_align align`, which is false under hsize.
  -- `(9223372036854775808 - align).toNat = 2^63 - align.toNat`.
  have hC : ((9223372036854775808 : usize)).toNat = 2 ^ 63 := by decide
  have hSubToNat : ((9223372036854775808 : usize) - align).toNat
                    = 2 ^ 63 - align.toNat := by
    rw [USize64.toNat_sub_of_le' (by rw [hC]; exact hAlignLe), hC]
  have hNotGt : ¬ size > ((9223372036854775808 : usize) - align) := by
    rw [show (size > ((9223372036854775808 : usize) - align))
          ↔ size.toNat > ((9223372036854775808 : usize) - align).toNat
        from USize64.lt_iff_toNat_lt]
    rw [hSubToNat]
    omega
  have hGtFalse : (size >? ((9223372036854775808 : usize) - align))
                  = RustM.ok false := by
    show (pure (decide (size > ((9223372036854775808 : usize) - align))) : RustM Bool)
       = RustM.ok false
    rw [decide_eq_false hNotGt]
    rfl
  unfold is_size_align_valid
  rw [hpow]
  show (do
      let __do_lift ← (!? true : RustM Bool)
      if __do_lift = true then pure false
      else do
        let __do_lift ← max_size_for_align align
        let __do_lift ← (size >? __do_lift)
        if __do_lift = true then pure false else pure true)
    = RustM.ok true
  show (do
      let __do_lift ← (pure (!true) : RustM Bool)
      if __do_lift = true then pure false
      else do
        let __do_lift ← max_size_for_align align
        let __do_lift ← (size >? __do_lift)
        if __do_lift = true then pure false else pure true)
    = RustM.ok true
  simp only [Bool.not_true, pure_bind, Bool.false_eq_true, if_false]
  rw [hMax]
  show (do
      let __do_lift ← (pure ((9223372036854775808 : usize) - align) : RustM usize)
      let __do_lift ← (size >? __do_lift)
      if __do_lift = true then pure false else pure true)
    = RustM.ok true
  simp only [pure_bind]
  rw [hGtFalse]
  rfl

/-- Postcondition (rejects too-large size): when `align` is a power of two
    but the rounded-up size exceeds `isize::MAX`, the function rejects.

    Stated as `2^63 < size.toNat + align.toNat`, the `Nat`-arithmetic
    counterpart of the implementation check `size > 2^63 - align` (which is
    safe because a power-of-two `align ≤ 2^63`). Captures the negative
    branch of `power_of_two_align_matches_round_up_contract` and the
    high-side `assert!(!is_size_align_valid(high, align))` of
    `layout_round_up_to_align_edge_cases`. -/
theorem is_size_align_valid_rejects_large_size (size align : usize)
    (hpow : is_power_of_two_usize align = RustM.ok true)
    (hsize : 2 ^ 63 < size.toNat + align.toNat) :
    is_size_align_valid size align = RustM.ok false := by
  have hAlignLe : align.toNat ≤ 2 ^ 63 := is_power_of_two_usize_le hpow
  have hMax : max_size_for_align align
              = RustM.ok ((9223372036854775808 : usize) - align) :=
    max_size_for_align_ok hAlignLe
  have hC : ((9223372036854775808 : usize)).toNat = 2 ^ 63 := by decide
  have hSubToNat : ((9223372036854775808 : usize) - align).toNat
                    = 2 ^ 63 - align.toNat := by
    rw [USize64.toNat_sub_of_le' (by rw [hC]; exact hAlignLe), hC]
  have hGt : size > ((9223372036854775808 : usize) - align) := by
    rw [show (size > ((9223372036854775808 : usize) - align))
          ↔ size.toNat > ((9223372036854775808 : usize) - align).toNat
        from USize64.lt_iff_toNat_lt]
    rw [hSubToNat]
    omega
  have hGtTrue : (size >? ((9223372036854775808 : usize) - align))
                  = RustM.ok true := by
    show (pure (decide (size > ((9223372036854775808 : usize) - align))) : RustM Bool)
       = RustM.ok true
    rw [decide_eq_true hGt]
    rfl
  unfold is_size_align_valid
  rw [hpow]
  show (do
      let __do_lift ← (pure (!true) : RustM Bool)
      if __do_lift = true then pure false
      else do
        let __do_lift ← max_size_for_align align
        let __do_lift ← (size >? __do_lift)
        if __do_lift = true then pure false else pure true)
    = RustM.ok false
  simp only [Bool.not_true, pure_bind, Bool.false_eq_true, if_false]
  rw [hMax]
  show (do
      let __do_lift ← (pure ((9223372036854775808 : usize) - align) : RustM usize)
      let __do_lift ← (size >? __do_lift)
      if __do_lift = true then pure false else pure true)
    = RustM.ok false
  simp only [pure_bind]
  rw [hGtTrue]
  rfl

/-- Totality / no-panic: for every pair of `usize` inputs, the function
    returns a `Bool` successfully (it never panics, never overflows).

    The only operation that could panic in the model is the literal
    subtraction `2^63 - align` inside `max_size_for_align`; but that branch
    is reached only after the helper has confirmed `align` is a power of
    two, which forces `align.toNat ∈ {1, 2, 4, …, 2^63}` and in particular
    `align ≤ 2^63`, so the subtraction is safe. Captures the implicit
    "returns a `bool`" totality contract of the function and the fact that
    every property test exercises the function via direct assertions on
    its `bool` return value (no `is_ok` / `unwrap` is needed). -/
theorem is_size_align_valid_total (size align : usize) :
    ∃ b : Bool, is_size_align_valid size align = RustM.ok b := by
  -- Case-split on whether `is_power_of_two_usize align` returns true or false.
  -- (It always returns some `ok b`; characterized via `is_power_of_two_usize_eq`.)
  have hPow := is_power_of_two_usize_eq align
  by_cases hb : (decide (align ≠ 0) && decide (align &&& (align - 1) = 0)) = true
  · -- power-of-two: case-split on size + align ≤ 2^63
    rw [hb] at hPow
    by_cases hsize : size.toNat + align.toNat ≤ 2 ^ 63
    · exact ⟨true, is_size_align_valid_accepts size align hPow hsize⟩
    · have hsize' : 2 ^ 63 < size.toNat + align.toNat := Nat.lt_of_not_le hsize
      exact ⟨false, is_size_align_valid_rejects_large_size size align hPow hsize'⟩
  · -- not a power of two: rejects
    have hbf : (decide (align ≠ 0) && decide (align &&& (align - 1) = 0)) = false :=
      Bool.eq_false_iff.mpr hb
    rw [hbf] at hPow
    exact ⟨false, is_size_align_valid_rejects_non_power_of_two size align hPow⟩

end Is_size_align_valid_usizeObligations
