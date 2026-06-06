
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


namespace max_size_for_align_usize

--  Returns the largest size allowed for a memory block with the given
--  power-of-two alignment.
@[spec]
def max_size_for_align (align : usize) : RustM usize := do
  ((← ((9223372036854775807 : usize) +? (1 : usize))) -? align)

end max_size_for_align_usize

