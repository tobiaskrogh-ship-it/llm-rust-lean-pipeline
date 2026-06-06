
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


namespace little_endian_read_u64

--  Reads an unsigned 64 bit integer from `buf` in little-endian order.
-- 
--  # Panics
-- 
--  Panics when `buf.len() < 8`.
@[spec]
def read_u64 (buf : (RustSlice u8)) : RustM u64 := do
  ((← ((← ((← ((← ((← ((← ((← (rust_primitives.hax.cast_op
                  (← buf[(0 : usize)]_?) :
                  RustM u64))
                |||? (← ((← (rust_primitives.hax.cast_op
                    (← buf[(1 : usize)]_?) :
                    RustM u64))
                  <<<? (8 : i32)))))
              |||? (← ((← (rust_primitives.hax.cast_op
                  (← buf[(2 : usize)]_?) :
                  RustM u64))
                <<<? (16 : i32)))))
            |||? (← ((← (rust_primitives.hax.cast_op
                (← buf[(3 : usize)]_?) :
                RustM u64))
              <<<? (24 : i32)))))
          |||? (← ((← (rust_primitives.hax.cast_op
              (← buf[(4 : usize)]_?) :
              RustM u64))
            <<<? (32 : i32)))))
        |||? (← ((← (rust_primitives.hax.cast_op
            (← buf[(5 : usize)]_?) :
            RustM u64))
          <<<? (40 : i32)))))
      |||? (← ((← (rust_primitives.hax.cast_op
          (← buf[(6 : usize)]_?) :
          RustM u64))
        <<<? (48 : i32)))))
    |||? (← ((← (rust_primitives.hax.cast_op
        (← buf[(7 : usize)]_?) :
        RustM u64))
      <<<? (56 : i32))))

end little_endian_read_u64

