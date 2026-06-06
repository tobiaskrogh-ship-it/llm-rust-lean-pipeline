
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


namespace forget_u64

--  Inlined from `core::mem::ManuallyDrop`. We only need construction; no
--  destructor runs because `ManuallyDrop` has no `Drop` impl.
structure ManuallyDrop (T : Type) where
  value : T

--  Inlined from `ManuallyDrop::new`.
@[spec]
def Impl.new (T : Type) (value : T) : RustM (ManuallyDrop T) := do
  (pure (ManuallyDrop.mk (value := value)))

--  Takes ownership and "forgets" about the value without running its destructor.
@[spec]
def forget (t : u64) : RustM rust_primitives.hax.Tuple0 := do
  let _ ← (Impl.new u64 t);
  (pure rust_primitives.hax.Tuple0.mk)

end forget_u64

