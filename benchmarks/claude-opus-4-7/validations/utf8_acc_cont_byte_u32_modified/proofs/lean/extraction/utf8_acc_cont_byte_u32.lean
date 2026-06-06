
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


namespace utf8_acc_cont_byte_u32

--  Mask of the value bits of a continuation byte.
def CONT_MASK : u8 := (63 : u8)

@[spec]
def utf8_acc_cont_byte (ch : u32) (byte : u8) : RustM u32 := do
  ((← (ch <<<? (6 : i32)))
    |||? (← (rust_primitives.hax.cast_op
      (← (byte &&&? CONT_MASK)) :
      RustM u32)))

end utf8_acc_cont_byte_u32

