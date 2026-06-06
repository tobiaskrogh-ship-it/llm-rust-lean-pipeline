
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


namespace split_array_mut_u64

--  Returns a mutable array reference to the first `M` items in the slice and
--  the remaining slice. Returns `None` if the slice is shorter than `M`.
@[spec]
def split_first_chunk_mut (M : usize) (s : (RustSlice u64)) : RustM sorry := do
  (pure sorry)

--  Divides one mutable array reference into two at an index.
-- 
--  The first will contain all indices from `[0, M)` and the second will
--  contain all indices from `[M, N)`.
-- 
--  # Panics
-- 
--  Panics if `M > N`.
@[spec]
def split_array_mut (M : usize) (N : usize) (a : (RustArray u64 N)) :
    RustM sorry := do
  (pure sorry)

end split_array_mut_u64

