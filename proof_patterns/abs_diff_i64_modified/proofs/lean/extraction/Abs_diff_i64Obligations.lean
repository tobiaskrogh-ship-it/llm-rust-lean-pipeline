-- Companion obligations file for the `abs_diff_i64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import abs_diff_i64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Abs_diff_i64Obligations

open abs_diff_i64

/-- Postcondition (a > b branch, no overflow).

    When `a > b` and the signed subtraction `a - b` does not overflow `i64`,
    the function returns `a - b` successfully (no panic).

    Corresponds to the proptest `abs_diff_returns_a_minus_b_when_a_gt_b`: the
    proptest's `prop_assume!(a > b)` is the branch guard, its `prop_assume!`
    on the `i128` difference encodes `¬ Int64.subOverflow a b`, and the
    `prop_assert_eq!(abs_diff(a, b), a - b)` is the equational postcondition. -/
theorem abs_diff_postcondition_a_gt_b (a b : i64)
    (hgt : a > b) (hno : ¬ Int64.subOverflow a b) :
    abs_diff a b = pure (a - b) := by
  -- Unfold the function, the comparison `>?`, and the subtraction `-?`.
  simp only [abs_diff, rust_primitives.cmp.gt,
             rust_primitives.ops.arith.Sub.sub]
  -- `Int64.subOverflow a b` unfolds to `BitVec.ssubOverflow a.toBitVec b.toBitVec`.
  have hno_overflow : ¬ (BitVec.ssubOverflow a.toBitVec b.toBitVec = true) := hno
  -- `hgt : a > b` resolves the outer `if`; `hno_overflow` resolves the inner overflow `if`.
  simp [hgt, hno_overflow]

/-- Postcondition (a ≤ b branch, no overflow).

    When `a ≤ b` (covering the equality case `a = b` as well) and the signed
    subtraction `b - a` does not overflow `i64`, the function returns `b - a`
    successfully (no panic).

    Corresponds to the proptest `abs_diff_returns_b_minus_a_when_a_le_b`. -/
theorem abs_diff_postcondition_a_le_b (a b : i64)
    (hle : a ≤ b) (hno : ¬ Int64.subOverflow b a) :
    abs_diff a b = pure (b - a) := by
  simp only [abs_diff, rust_primitives.cmp.gt,
             rust_primitives.ops.arith.Sub.sub]
  -- From `a ≤ b` derive `¬ (a > b)` by bridging through `toInt`.
  have hngt : ¬ (a > b) := by
    intro hgt
    have h1 : b.toInt < a.toInt := Int64.lt_iff_toInt_lt.mp hgt
    have h2 : a.toInt ≤ b.toInt := Int64.le_iff_toInt_le.mp hle
    omega
  have hno_overflow : ¬ (BitVec.ssubOverflow b.toBitVec a.toBitVec = true) := hno
  simp [hngt, hno_overflow]

/-- Failure (a > b branch, overflow).

    When `a > b` and the signed subtraction `a - b` overflows `i64`, the
    function panics with `Error.integerOverflow`. This is the branch
    exercised by the `should_panic` test
    `abs_diff_panics_when_difference_exceeds_i64_max`, which calls
    `abs_diff(i64::MAX, i64::MIN)` — `MAX > MIN` selects this branch and
    `MAX - MIN` overflows. -/
theorem abs_diff_failure_a_gt_b (a b : i64)
    (hgt : a > b) (hov : Int64.subOverflow a b) :
    abs_diff a b = RustM.fail Error.integerOverflow := by
  simp only [abs_diff, rust_primitives.cmp.gt,
             rust_primitives.ops.arith.Sub.sub]
  -- `Int64.subOverflow a b` unfolds to `BitVec.ssubOverflow a.toBitVec b.toBitVec`.
  have hov_eq : (BitVec.ssubOverflow a.toBitVec b.toBitVec = true) := hov
  -- `hgt` resolves the outer `if`; `hov_eq` resolves the inner overflow `if` to the fail branch.
  simp [hgt, hov_eq]

/-- Failure (a ≤ b branch, overflow).

    Companion to `abs_diff_failure_a_gt_b`: when `a ≤ b` and the signed
    subtraction `b - a` overflows `i64`, the function panics with
    `Error.integerOverflow`. The `should_panic` test exercises this same
    overall failure contract; this theorem covers the second branch in which
    the contract clause can manifest. -/
theorem abs_diff_failure_a_le_b (a b : i64)
    (hle : a ≤ b) (hov : Int64.subOverflow b a) :
    abs_diff a b = RustM.fail Error.integerOverflow := by
  simp only [abs_diff, rust_primitives.cmp.gt,
             rust_primitives.ops.arith.Sub.sub]
  have hngt : ¬ (a > b) := by
    intro hgt
    have h1 : b.toInt < a.toInt := Int64.lt_iff_toInt_lt.mp hgt
    have h2 : a.toInt ≤ b.toInt := Int64.le_iff_toInt_le.mp hle
    omega
  have hov_eq : (BitVec.ssubOverflow b.toBitVec a.toBitVec = true) := hov
  simp [hngt, hov_eq]

end Abs_diff_i64Obligations
