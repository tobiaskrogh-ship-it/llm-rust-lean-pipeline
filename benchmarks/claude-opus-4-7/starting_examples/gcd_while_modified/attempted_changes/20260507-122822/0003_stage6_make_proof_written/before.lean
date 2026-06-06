-- Companion obligations file for the `gcd_while` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import gcd_while

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Gcd_whileObligations

/-- Boundary postcondition: when the second argument is `0`, the loop body
    is skipped and the result is the first argument. Captures the test
    `zero_input_returns_other` (the `gcd_while(x, 0) = x` half) and
    subsumes the `zero_zero_is_zero` boundary at `a = 0`. -/
theorem gcd_while_a_zero (a : u64) :
    gcd_while.gcd_while a 0 = RustM.ok a := by sorry

/-- Boundary postcondition: when the first argument is `0` (and the second
    is non-zero), the result is the second argument. Captures the test
    `zero_input_returns_other` (the `gcd_while(0, b) = b` half). The case
    `b = 0` is already covered by `gcd_while_a_zero` at `a = 0`. -/
theorem gcd_while_zero_b (b : u64) :
    gcd_while.gcd_while 0 b = RustM.ok b := by sorry

/-- Functional correctness / closed-form postcondition: `gcd_while a b`
    successfully returns `Nat.gcd a.toNat b.toNat` (cast back into `u64`).
    Subsumes the specific-instance test `known_values` and represents the
    "function never panics" guarantee in equational form (the right-hand
    side is `RustM.ok …`, not `RustM.fail …`). The result fits in `u64`
    because `Nat.gcd a.toNat b.toNat ≤ max a.toNat b.toNat < 2 ^ 64`. -/
theorem gcd_while_postcondition (a b : u64) :
    gcd_while.gcd_while a b
      = RustM.ok (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) := by sorry

/-- Postcondition (common divisor, left): for every `(a, b)`, the result `g`
    of `gcd_while a b` divides `a`. Captures the `result_divides_both_inputs`
    test (the `a % g == 0` half). The hypothesis `gcd_while a b = RustM.ok g`
    folds in the no-panic guarantee. The boundary case `g = 0` (which
    occurs only at `(a, b) = (0, 0)`) is admitted by `0 ∣ 0`. -/
theorem gcd_while_dvd_left (a b g : u64)
    (h : gcd_while.gcd_while a b = RustM.ok g) :
    g.toNat ∣ a.toNat := by sorry

/-- Postcondition (common divisor, right): for every `(a, b)`, the result
    `g` of `gcd_while a b` divides `b`. Captures the
    `result_divides_both_inputs` test (the `b % g == 0` half). Stated as a
    separate clause from `gcd_while_dvd_left` because each side is an
    independent fact about the result (the test asserts both, but the
    contract has two distinct divisibility obligations). -/
theorem gcd_while_dvd_right (a b g : u64)
    (h : gcd_while.gcd_while a b = RustM.ok g) :
    g.toNat ∣ b.toNat := by sorry

/-- Postcondition (greatest): for every `(a, b)`, the result `g` of
    `gcd_while a b` is the *greatest* common divisor — every common divisor
    `d` of `a` and `b` divides `g`. Captures the
    `result_is_greatest_common_divisor` test, which asserts the dual form
    "no integer larger than `g` divides both `a` and `b`"; the universal
    `d ∣ g` formulation is the standard mathematical statement and is
    equivalent for non-zero `g` (and trivially holds at `g = 0` since the
    only `(a, b)` producing `g = 0` is `(0, 0)`, where every `d` divides
    both inputs and `d ∣ 0`). The divisor `d` ranges over `Nat`, not `u64`,
    so it captures candidate divisors regardless of representation. -/
theorem gcd_while_greatest (a b g : u64)
    (h : gcd_while.gcd_while a b = RustM.ok g)
    (d : Nat) (hda : d ∣ a.toNat) (hdb : d ∣ b.toNat) :
    d ∣ g.toNat := by sorry

/-- Totality / no-panic: for every pair of `u64` inputs, `gcd_while`
    returns a value. The body uses `%?` (which panics at `b = 0`), but the
    loop guard `b ≠ 0` ensures it is never called with a zero divisor.
    Stated as an existential rather than equational form to make the
    "no failure mode" clause of the contract explicit, independent of the
    closed-form value. -/
theorem gcd_while_total (a b : u64) :
    ∃ v : u64, gcd_while.gcd_while a b = pure v := by sorry

end Gcd_whileObligations
