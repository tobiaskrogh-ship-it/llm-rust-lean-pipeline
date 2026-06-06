
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


namespace while_example

@[spec]
def modulo_via_subtraction (a : u64) (b : u64) : RustM u64 := do
  let x : u64 := a;
  let x : u64 ←
    (rust_primitives.hax.while_loop
      (fun x => (do (pure true) : RustM Bool))
      (fun x => (do (x >=? b) : RustM Bool))
      (fun x =>
        (do
        (rust_primitives.hax.int.from_machine (0 : u32)) :
        RustM hax_lib.int.Int))
      x
      (fun x => (do let x : u64 ← (x -? b); (pure x) : RustM u64)));
  (pure x)

end while_example

