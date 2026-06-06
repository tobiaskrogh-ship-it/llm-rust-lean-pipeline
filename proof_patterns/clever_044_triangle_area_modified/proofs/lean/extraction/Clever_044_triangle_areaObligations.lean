-- Companion obligations file for the `clever_044_triangle_area` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_044_triangle_area

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_044_triangle_areaObligations

/-- Postcondition: when the signed product `a * h` does not overflow `i64`,
    `triangle_area a h` returns `(a * h) / 2` successfully.

    Corresponds to the property test `returns_truncated_half_of_product` in
    the Rust source: `prop_assert_eq!(triangle_area(a, h), product / 2)` under
    bounded `a, h ∈ [-2^31, 2^31]` (which encodes the no-overflow precondition
    on `a * h`).

    Equational form is used because the only nontrivial precondition is the
    multiplication-overflow guard: the division `/? 2` is total here because
    `2 ≠ 0` and `2 ≠ -1` (so neither failure branch of signed `/?` fires). -/
theorem triangle_area_ok (a h : i64) (hno : ¬ Int64.mulOverflow a h) :
    clever_044_triangle_area.triangle_area a h = RustM.ok ((a * h) / 2) := by
  simp only [Int64.mulOverflow] at hno
  unfold clever_044_triangle_area.triangle_area
  simp only [rust_primitives.ops.arith.Mul.mul, rust_primitives.ops.arith.Div.div,
             if_neg hno, pure_bind]
  -- Goal at this point:
  --   (if (decide (a*h = Int64.minValue) && decide ((2:i64) = -1)) = true
  --      then RustM.fail Error.integerOverflow
  --      else if (2:i64) = 0 then RustM.fail Error.divisionByZero
  --           else pure (a*h/2))
  --   = RustM.ok (a*h/2)
  -- The static fact `decide ((2:i64) = -1) = false` collapses the conjunction.
  rw [show decide ((2 : i64) = -1) = false from by decide]
  simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  -- Remaining: if (2:i64) = 0 then .fail .divisionByZero else pure (a*h/2) = RustM.ok (a*h/2)
  rw [if_neg (show ((2 : i64) ≠ 0) from by decide)]
  rfl

/-- Failure condition: when the signed product `a * h` overflows `i64`,
    `triangle_area a h` panics with `Error.integerOverflow`.

    Corresponds to the property test `panics_when_product_overflows`:
    `prop_assume!(a.checked_mul(h).is_none()); ... catch_unwind(...) is_err()`.
    The Rust panic is modelled by `RustM.fail Error.integerOverflow`. -/
theorem triangle_area_overflow (a h : i64) (hov : Int64.mulOverflow a h) :
    clever_044_triangle_area.triangle_area a h = RustM.fail Error.integerOverflow := by
  simp only [Int64.mulOverflow] at hov
  unfold clever_044_triangle_area.triangle_area
  simp only [rust_primitives.ops.arith.Mul.mul, if_pos hov]
  rfl

end Clever_044_triangle_areaObligations
