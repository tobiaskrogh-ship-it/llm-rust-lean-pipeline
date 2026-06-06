
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


namespace utf8_is_cont_byte_u8

@[spec]
def utf8_is_cont_byte (byte : u8) : RustM Bool := do
  ((← (rust_primitives.hax.cast_op byte : RustM i8)) <? (-64 : i8))

end utf8_is_cont_byte_u8

