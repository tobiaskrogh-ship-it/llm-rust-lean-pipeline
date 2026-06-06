
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


namespace rsplit_array_mut_u64

--  Returns the remaining slice and a mutable array reference to the last `M`
--  items. Returns `None` if the slice is shorter than `M`.
@[spec]
def split_last_chunk_mut (M : usize) (s : (RustSlice u64)) : RustM sorry := do
  (pure sorry)

--  Divides one mutable array reference into two at an index from the end.
-- 
--  The first will contain all indices from `[0, N - M)` and the second will
--  contain all indices from `[N - M, N)`.
-- 
--  # Panics
-- 
--  Panics if `M > N`.
@[spec]
def rsplit_array_mut (M : usize) (N : usize) (a : (RustArray u64 N)) :
    RustM sorry := do
  (pure sorry)

end rsplit_array_mut_u64

