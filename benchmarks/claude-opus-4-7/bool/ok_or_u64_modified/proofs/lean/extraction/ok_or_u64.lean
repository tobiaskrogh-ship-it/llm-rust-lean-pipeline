
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


namespace ok_or_u64

--  Returns `Ok(())` if `b` is `true`, or `Err(err)` otherwise.
-- 
--  Arguments passed to `ok_or` are eagerly evaluated; if you are
--  passing the result of a function call, it is recommended to use
--  `ok_or_else`, which is lazily evaluated.
@[spec]
def ok_or (b : Bool) (err : u64) :
    RustM (core_models.result.Result rust_primitives.hax.Tuple0 u64) := do
  if b then do
    (pure (core_models.result.Result.Ok rust_primitives.hax.Tuple0.mk))
  else do
    (pure (core_models.result.Result.Err err))

end ok_or_u64

