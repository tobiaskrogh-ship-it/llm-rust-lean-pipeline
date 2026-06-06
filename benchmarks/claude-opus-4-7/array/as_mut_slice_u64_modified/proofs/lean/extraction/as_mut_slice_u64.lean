
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


namespace as_mut_slice_u64

--  Returns a mutable slice containing the entire array. Equivalent to `&mut s[..]`.
@[spec]
def as_mut_slice (N : usize) (a : (RustArray u64 N)) : RustM sorry := do
  (pure sorry)

end as_mut_slice_u64

