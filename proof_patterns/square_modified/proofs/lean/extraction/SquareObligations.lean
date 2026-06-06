-- Companion obligations file for the `square` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import square

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace SquareObligations

/-- Postcondition: when the product x * x fits in u8 (no overflow),
    `square` succeeds and returns exactly `x * x`. -/
theorem square_ok (x : u8) (h : ¬ UInt8.mulOverflow x x) :
    square.square x = RustM.ok (x * x) := by
  simp only [UInt8.mulOverflow] at h
  simp only [square.square, rust_primitives.ops.arith.Mul.mul, if_neg h]
  rfl

/-- Failure condition: when x * x overflows u8,
    `square` fails with `Error.integerOverflow`. -/
theorem square_overflow (x : u8) (h : UInt8.mulOverflow x x) :
    square.square x = RustM.fail Error.integerOverflow := by
  simp only [UInt8.mulOverflow] at h
  simp only [square.square, rust_primitives.ops.arith.Mul.mul, if_pos h]

end SquareObligations
