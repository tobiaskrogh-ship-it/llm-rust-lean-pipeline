
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


namespace gcd_while

@[spec]
def gcd_while (a : u64) (b : u64) : RustM u64 := do
  let ⟨a, b⟩ ←
    (rust_primitives.hax.while_loop
      (fun ⟨a, b⟩ => (do (pure true) : RustM Bool))
      (fun ⟨a, b⟩ => (do (b !=? (0 : u64)) : RustM Bool))
      (fun ⟨a, b⟩ =>
        (do (rust_primitives.hax.int.from_machine b) : RustM hax_lib.int.Int))
      (rust_primitives.hax.Tuple2.mk a b)
      (fun ⟨a, b⟩ =>
        (do
        let t : u64 := b;
        let b : u64 ← (a %? b);
        let a : u64 := t;
        (pure (rust_primitives.hax.Tuple2.mk a b)) :
        RustM (rust_primitives.hax.Tuple2 u64 u64))));
  (pure a)

end gcd_while

