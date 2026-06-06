-- Companion obligations file for the `clever_096_multiply` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_096_multiply

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_096_multiplyObligations

/-! ## Contract clauses

  The Rust function `multiply(a, b)` returns the product of the decimal
  unit digits of `|a|` and `|b|`.

  * `matches_unit_digit_product` (proptest) — the main postcondition.
    The proptest restricts `a, b ∈ (i64::MIN, i64::MAX]`; the same range
    is necessary in Lean because the function's `if a < 0 then -a` branch
    panics on `i64::MIN` (negating `Int64.minValue` overflows).
  * Documented panic — when either argument equals `i64::MIN`, the
    function panics with `Error.integerOverflow`.
  * `known` (unit pins) — concrete sanity checks; subsumed by the
    universal postcondition.

  ### Feasibility

  For `a, b ≠ Int64.minValue`, both `|a|.toInt` and `|b|.toInt` fit in
  `[0, 2^63 - 1]`, so `|a| % 10 ∈ [0, 9]` and the product is bounded by
  `81`, well within `i64`.  No additional preconditions needed.
-/

/-- Main postcondition: `multiply(a, b)` returns the product of the unit
    digits of `|a|` and `|b|`, expressed via `Int.natAbs` and `%`.

    Corresponds to the proptest `matches_unit_digit_product`: the
    proptest's range `(i64::MIN + 1)..=i64::MAX` for both arguments is
    exactly captured by `a ≠ Int64.minValue ∧ b ≠ Int64.minValue`. -/
theorem multiply_matches_unit_digit_product
    (a b : i64)
    (ha : a ≠ Int64.minValue) (hb : b ≠ Int64.minValue) :
    ∃ r : i64,
      clever_096_multiply.multiply a b = RustM.ok r ∧
      (r.toInt : Int) =
        ((a.toInt.natAbs % 10 : Nat) : Int) *
          ((b.toInt.natAbs % 10 : Nat) : Int) := by
  sorry

/-- Failure when `a = i64::MIN`: the inner `-? a` overflows, so the
    function panics with `Error.integerOverflow`.

    Corresponds to the documented precondition violation in the Rust
    source: "Negating `i64::MIN` overflows, so the function … panics
    there". -/
theorem multiply_fail_when_a_is_min
    (b : i64) :
    clever_096_multiply.multiply Int64.minValue b =
      RustM.fail Error.integerOverflow := by
  sorry

/-- Failure when `a ≠ i64::MIN` but `b = i64::MIN`: the first abs block
    succeeds, but the second `-? b` overflows.

    Same documented precondition violation as the `a = i64::MIN` case, but
    surfaced on the second argument. -/
theorem multiply_fail_when_b_is_min
    (a : i64) (ha : a ≠ Int64.minValue) :
    clever_096_multiply.multiply a Int64.minValue =
      RustM.fail Error.integerOverflow := by
  sorry

end Clever_096_multiplyObligations
