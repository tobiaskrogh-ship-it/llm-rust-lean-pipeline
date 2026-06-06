-- Companion obligations file for the `add_one` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import add_one

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Add_oneObligations

/-- Postcondition: for every valid input (x < 255, i.e. no u8 overflow),
    `add_one` succeeds and returns exactly `x + 1`. -/
theorem add_one_postcondition (x : u8) (h : ¬ UInt8.addOverflow x 1) :
    add_one.add_one x = RustM.ok (x + 1) := by
  -- After unfolding, the goal's Bool condition is
  --   `x.toBitVec.uaddOverflow (UInt8.toBitVec 1) = true`.
  -- `h : ¬ UInt8.addOverflow x 1` is definitionally
  --   `¬ (x.toBitVec.uaddOverflow (UInt8.toBitVec 1) = true)`
  -- because UInt8.addOverflow unfolds to BitVec.uaddOverflow … .toBitVec ….
  simp only [add_one.add_one, rust_primitives.ops.arith.Add.add]
  rw [if_neg (show ¬ (x.toBitVec.uaddOverflow (UInt8.toBitVec 1) = true) from h)]
  -- Remaining goal: pure (x + 1) = RustM.ok (x + 1) — both are `some (.ok (x+1))`.
  rfl

/-- Failure condition: when `x = 255` (addition would overflow u8),
    `add_one` fails with `Error.integerOverflow`. -/
theorem add_one_overflow_failure (x : u8) (h : UInt8.addOverflow x 1) :
    add_one.add_one x = RustM.fail Error.integerOverflow := by
  -- After unfolding, the goal's Bool condition is
  --   `x.toBitVec.uaddOverflow (UInt8.toBitVec 1) = true`.
  -- `h : UInt8.addOverflow x 1` is definitionally
  --   `x.toBitVec.uaddOverflow (UInt8.toBitVec 1) = true`.
  simp only [add_one.add_one, rust_primitives.ops.arith.Add.add]
  rw [if_pos (show x.toBitVec.uaddOverflow (UInt8.toBitVec 1) = true from h)]

end Add_oneObligations
