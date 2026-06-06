-- Companion obligations file for the `clever_040_car_race_collision` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_040_car_race_collision

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_040_car_race_collisionObligations

/-- Postcondition: when the product `x * x` fits in `u64` (no overflow),
    `car_race_collision` succeeds and returns exactly `x * x`.

    This pins down the `postcondition_is_square` proptest in the Rust
    source: for `x ∈ [1, u32::MAX]`, `y / x = x` and `y % x = 0` jointly
    characterise `y = x * x`. The unsigned multiplication on `u64` does
    not overflow precisely when `x ≤ u32::MAX`. -/
theorem car_race_collision_ok (x : u64) (h : ¬ UInt64.mulOverflow x x) :
    clever_040_car_race_collision.car_race_collision x = RustM.ok (x * x) := by
  simp only [UInt64.mulOverflow] at h
  simp only [clever_040_car_race_collision.car_race_collision,
             rust_primitives.ops.arith.Mul.mul, if_neg h]
  rfl

/-- Failure condition: when `x * x` overflows `u64`, `car_race_collision`
    fails with `Error.integerOverflow`. Captures the
    `overflow_panics_above_u32_max` test, which exercises the failure
    above `u32::MAX`. -/
theorem car_race_collision_overflow (x : u64) (h : UInt64.mulOverflow x x) :
    clever_040_car_race_collision.car_race_collision x = RustM.fail Error.integerOverflow := by
  simp only [UInt64.mulOverflow] at h
  simp only [clever_040_car_race_collision.car_race_collision,
             rust_primitives.ops.arith.Mul.mul, if_pos h]

/-- Boundary postcondition at `x = 0`, where the division characterisation
    of `postcondition_is_square` is vacuous. Captures the dedicated
    `postcondition_at_zero` test in the Rust source. -/
theorem car_race_collision_at_zero :
    clever_040_car_race_collision.car_race_collision 0 = RustM.ok 0 := by
  have h : ¬ UInt64.mulOverflow (0 : u64) (0 : u64) := by decide
  have hok := car_race_collision_ok 0 h
  simpa using hok

end Clever_040_car_race_collisionObligations
