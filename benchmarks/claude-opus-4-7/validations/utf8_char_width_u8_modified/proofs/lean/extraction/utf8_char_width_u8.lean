
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


namespace utf8_char_width_u8

@[spec]
def utf8_char_width (b : u8) : RustM usize := do
  if (← (b <? (128 : u8))) then do
    (pure (1 : usize))
  else do
    if (← (b <? (194 : u8))) then do
      (pure (0 : usize))
    else do
      if (← (b <? (224 : u8))) then do
        (pure (2 : usize))
      else do
        if (← (b <? (240 : u8))) then do
          (pure (3 : usize))
        else do
          if (← (b <? (245 : u8))) then do
            (pure (4 : usize))
          else do
            (pure (0 : usize))

end utf8_char_width_u8

