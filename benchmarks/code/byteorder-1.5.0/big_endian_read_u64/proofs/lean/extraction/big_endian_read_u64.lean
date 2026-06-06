
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


namespace big_endian_read_u64

--  Reads an unsigned 64 bit integer from `buf` in big-endian byte order.
-- 
--  # Panics
-- 
--  Panics when `buf.len() < 8`.
@[spec]
def read_u64 (buf : (RustSlice u8)) : RustM u64 := do
  (core_models.num.Impl_9.from_be_bytes
    (← (core_models.result.Impl.unwrap
      (RustArray u8 8)
      core_models.array.TryFromSliceError
      (← (core_models.convert.TryInto.try_into
        (RustSlice u8)
        (RustArray u8 8)
        (← buf[(core_models.ops.range.RangeTo.mk (_end := (8 : usize)))]_?))))))

end big_endian_read_u64

