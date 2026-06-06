
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


namespace while_handmade

@[spec]
def count_to (n : u64) : RustM u64 := do
  let i : u64 := (0 : u64);
  let i : u64 ←
    (rust_primitives.hax.while_loop
      (fun i => (do (pure true) : RustM Bool))
      (fun i => (do (i !=? n) : RustM Bool))
      (fun i =>
        (do
        (rust_primitives.hax.int.from_machine (0 : u32)) :
        RustM hax_lib.int.Int))
      i
      (fun i => (do let i : u64 ← (i +? (1 : u64)); (pure i) : RustM u64)));
  (pure i)

end while_handmade

