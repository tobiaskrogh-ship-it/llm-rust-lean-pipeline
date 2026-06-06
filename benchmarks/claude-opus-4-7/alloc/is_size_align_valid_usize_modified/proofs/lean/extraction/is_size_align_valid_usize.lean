
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace is_size_align_valid_usize

@[spec]
def is_power_of_two_usize (x : usize) : RustM Bool := do
  if (← (x ==? (0 : usize))) then do
    (pure false)
  else do
    ((← (x &&&? (← (x -? (1 : usize))))) ==? (0 : usize))

@[spec]
def max_size_for_align (align : usize) : RustM usize := do
  ((9223372036854775808 : usize) -? align)

--  Checks the preconditions of `Layout::from_size_align`: `align` must be a
--  power of two, and `size` rounded up to a multiple of `align` must not
--  exceed `isize::MAX`.
@[spec]
def is_size_align_valid (size : usize) (align : usize) : RustM Bool := do
  if (← (!? (← (is_power_of_two_usize align)))) then do
    (pure false)
  else do
    if (← (size >? (← (max_size_for_align align)))) then do
      (pure false)
    else do
      (pure true)

end is_size_align_valid_usize

