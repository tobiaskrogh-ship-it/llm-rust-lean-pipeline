
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


namespace trailing_zeros_u64

--  Number of trailing zero bits of `x`; `trailing_zeros_u64(0) == 64`.
-- 
--  For `x != 0` the result `r` satisfies: `r < 64`, `2^r` divides `x`,
--  and bit `r` of `x` is set (so `r` is the position of the lowest set
--  bit and `x` is not divisible by `2^(r + 1)`).
@[spec]
def trailing_zeros_u64 (x : u64) : RustM u32 := do
  if (← (x ==? (0 : u64))) then do
    (pure (64 : u32))
  else do
    let y : u64 := x;
    let count : u32 := (0 : u32);
    let ⟨count, y⟩ ←
      (rust_primitives.hax.while_loop
        (fun ⟨count, y⟩ => (do (pure true) : RustM Bool))
        (fun ⟨count, y⟩ =>
          (do ((← (y &&&? (1 : u64))) ==? (0 : u64)) : RustM Bool))
        (fun ⟨count, y⟩ =>
          (do
          (rust_primitives.hax.int.from_machine (0 : u32)) :
          RustM hax_lib.int.Int))
        (rust_primitives.hax.Tuple2.mk count y)
        (fun ⟨count, y⟩ =>
          (do
          let y : u64 ← (y >>>? (1 : i32));
          let count : u32 ← (count +? (1 : u32));
          (pure (rust_primitives.hax.Tuple2.mk count y)) :
          RustM (rust_primitives.hax.Tuple2 u32 u64))));
    (pure count)

end trailing_zeros_u64

