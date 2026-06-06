
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


namespace padding_needed_for_usize

@[spec]
def is_power_of_two_usize (x : usize) : RustM Bool := do
  if (← (x ==? (0 : usize))) then do
    (pure false)
  else do
    ((← (x &&&? (← (x -? (1 : usize))))) ==? (0 : usize))

@[spec]
def size_rounded_up_to_custom_align (size : usize) (align : usize) :
    RustM usize := do
  let align_m1 : usize ← (align -? (1 : usize));
  ((← (size +? align_m1)) &&&? (← (~? align_m1)))

--  Returns the amount of padding that must be inserted after a block of size
--  `size` so that the following address satisfies `align`.
-- 
--  The return value has no meaning if `align` is not a power of two
--  (`usize::MAX` is returned in that case).
@[spec]
def padding_needed_for (size : usize) (align : usize) : RustM usize := do
  if (← (!? (← (is_power_of_two_usize align)))) then do
    (pure (18446744073709551615 : usize))
  else do
    let len_rounded_up : usize ← (size_rounded_up_to_custom_align size align);
    (len_rounded_up -? size)

end padding_needed_for_usize

