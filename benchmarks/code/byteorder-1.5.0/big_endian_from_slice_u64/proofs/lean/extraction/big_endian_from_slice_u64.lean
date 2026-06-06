
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


namespace big_endian_from_slice_u64

--  Converts the given slice of unsigned 64 bit integers to big endian.
-- 
--  If the host platform is already big endian, this is a no-op.
@[spec]
def from_slice_u64 (numbers : (RustSlice u64)) : RustM (RustSlice u64) := do
  let _ ←
    if true then do (pure sorry) else do (pure rust_primitives.hax.Tuple0.mk);
  (pure numbers)

end big_endian_from_slice_u64

