
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


namespace next_code_point_reverse_u8

--  Mask of the value bits of a continuation byte.
def CONT_MASK : u8 := (63 : u8)

@[spec]
def utf8_first_byte (byte : u8) (width : u32) : RustM u32 := do
  (rust_primitives.hax.cast_op
    (← (byte &&&? (← ((127 : u8) >>>? width)))) :
    RustM u32)

@[spec]
def utf8_acc_cont_byte (ch : u32) (byte : u8) : RustM u32 := do
  ((← (ch <<<? (6 : i32)))
    |||? (← (rust_primitives.hax.cast_op
      (← (byte &&&? CONT_MASK)) :
      RustM u32)))

@[spec]
def utf8_is_cont_byte (byte : u8) : RustM Bool := do
  ((← (rust_primitives.hax.cast_op byte : RustM i8)) <? (-64 : i8))

--  # Safety
-- 
--  `bytes` must produce a valid UTF-8-like (UTF-8 or WTF-8) string.
@[spec]
def next_code_point_reverse (bytes : (core_models.slice.iter.Iter u8)) :
    RustM
    (rust_primitives.hax.Tuple2
      (core_models.slice.iter.Iter u8)
      (core_models.option.Option u32))
    := do
  let hax_temp_output : (core_models.option.Option u32) := sorry;
  (pure (rust_primitives.hax.Tuple2.mk bytes hax_temp_output))

end next_code_point_reverse_u8

