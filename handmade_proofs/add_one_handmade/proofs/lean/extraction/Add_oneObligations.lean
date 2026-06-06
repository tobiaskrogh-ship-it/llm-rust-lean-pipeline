
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

private theorem hax_add_def_u8 (x y : UInt8) :
    x +? y = if UInt8.addOverflow x y
             then RustM.fail Error.integerOverflow
             else pure (x + y) := rfl

-- We are trying to prove that calling the function gives us
-- RustM.ok (x + 1) if we dont have overflow
theorem add_one_postcondition (x : u8) (h : ¬ UInt8.addOverflow x 1) :
    add_one.add_one x = RustM.ok (x + 1) := by
  rw [add_one.add_one]
  rw [hax_add_def_u8]
  rw [if_neg]
  trivial
  exact h


-- We are trying to prove that calling the function gives us
-- RustM.fail Error.integerOverflow if we do have overflow
theorem add_one_overflow_failure (x : u8) (h : UInt8.addOverflow x 1) :
    add_one.add_one x = RustM.fail Error.integerOverflow := by
  rw [add_one.add_one]
  rw [hax_add_def_u8]
  rw [if_pos]
  exact h

end Add_oneObligations
