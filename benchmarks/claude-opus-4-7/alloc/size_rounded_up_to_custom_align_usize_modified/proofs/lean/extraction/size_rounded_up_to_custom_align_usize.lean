
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


namespace size_rounded_up_to_custom_align_usize

--  Returns the smallest multiple of `align` greater than or equal to `size`.
-- 
--  `align` must be a power of two.
@[spec]
def size_rounded_up_to_custom_align (size : usize) (align : usize) :
    RustM usize := do
  let align_m1 : usize ← (align -? (1 : usize));
  ((← (size +? align_m1)) &&&? (← (~? align_m1)))

end size_rounded_up_to_custom_align_usize

