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

-- Bit identity: 2^k AND (2^k - 1) = 0 at the Nat level.
private theorem nat_and_pow2_sub_one (k : Nat) : (2^k) &&& (2^k - 1) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hik : i = k
  · subst hik
    simp [Nat.testBit_two_pow_self, Nat.testBit_two_pow_sub_one]
  · simp [Nat.testBit_two_pow_of_ne (Ne.symm hik)]

-- Test: try direct unfolding for is_power_of_two_usize 1
private theorem ipot_one_test : is_power_of_two_usize (1 : usize) = RustM.ok true := by
  unfold is_power_of_two_usize
  rfl

/-- Nat-level "is a power of two" predicate. Mirrors the Rust standard
    library's `usize::is_power_of_two()` — `0` is *not* a power of two
    (no `k` satisfies `2^k = 0`). -/
private def IsPowerOfTwoNat (n : Nat) : Prop := ∃ k : Nat, n = 2 ^ k

/-- Overflow-safe `Nat`-level oracle for the documented postcondition:
    `size` rounded up to the next multiple of `align` does not exceed
    `isize::MAX = 2^63 - 1`. Mirrors the property test's `u128` oracle
    `((size + a - 1) / a) * a ≤ isize::MAX`. Only meaningful when
    `align ≥ 1` (always true when `align` is a power of two). -/
private def RoundsUpFits (size align : Nat) : Prop :=
  (size + align - 1) / align * align ≤ 2 ^ 63 - 1

/-- Failure-condition clause (alignment): when `align` is not a power of
    two, the function rejects regardless of `size`.

    Captures the property test `non_power_of_two_align_always_rejected`:
    `Alignment::new(align)` is `None` unless `align` is a power of two,
    so `is_size_align_valid(size, align) == false` for every `size`.
    The `align = 0` corner is subsumed (0 is not a power of two — the
    short-circuit `align != 0` guard in `is_power_of_two_usize` rejects it).
    A buggy implementation that accepted any odd or composite alignment,
    or that panicked on `align = 0`, would falsify this. -/
theorem rejects_non_power_of_two (size align : usize)
    (h : ¬ IsPowerOfTwoNat align.toNat) :
    is_size_align_valid size align = RustM.ok false := by
  sorry

/-- Postcondition (accept): when `align` is a power of two and `size`
    rounded up to a multiple of `align` fits within `isize::MAX`, the
    function returns `true`.

    Captures the "true" half of `power_of_two_align_matches_round_up_contract`.
    A buggy implementation that rejected a valid `(size, align)` pair
    inside the rounded-up envelope (e.g. an off-by-one on the size
    threshold, or rejecting `size = 0`) would falsify this. -/
theorem accepts_when_pow2_and_fits (size align : usize)
    (h_pow2 : IsPowerOfTwoNat align.toNat)
    (h_fits : RoundsUpFits size.toNat align.toNat) :
    is_size_align_valid size align = RustM.ok true := by
  sorry

/-- Postcondition (reject): when `align` is a power of two but `size`
    rounded up to a multiple of `align` exceeds `isize::MAX`, the
    function returns `false`.

    Captures the "false" half of `power_of_two_align_matches_round_up_contract`.
    A buggy implementation that accepted `(size, align)` whose rounded-up
    layout would overflow `isize::MAX` (e.g. comparing against `usize::MAX`
    or skipping the size check) would falsify this. -/
theorem rejects_when_pow2_and_too_big (size align : usize)
    (h_pow2 : IsPowerOfTwoNat align.toNat)
    (h_too_big : ¬ RoundsUpFits size.toNat align.toNat) :
    is_size_align_valid size align = RustM.ok false := by
  sorry

/-- Totality / no-panic: for every `(size, align)` pair the function
    returns a boolean successfully — no panic, no overflow, no error.

    The short-circuit in `is_power_of_two_usize` guards the `x - 1`
    underflow at `x = 0`, and `max_size_for_align`'s `2^63 - align` is
    only evaluated when `align` is a power of two (hence `align ≤ 2^63`).
    Implicit in every property test (each `assert_eq!` presumes the
    function returns). A buggy implementation that ever panicked,
    failed, or overflowed would falsify this. -/
theorem is_size_align_valid_total (size align : usize) :
    ∃ b : Bool, is_size_align_valid size align = RustM.ok b := by
  sorry

end Is_size_align_valid_usizeObligations
