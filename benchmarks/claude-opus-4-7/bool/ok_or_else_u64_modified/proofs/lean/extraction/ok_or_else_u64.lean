
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


namespace ok_or_else_u64

--  Returns `Ok(())` if `b` is `true`, or `Err(f())` otherwise.
@[spec]
def ok_or_else
    (F : Type)
    [trait_constr_ok_or_else_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      rust_primitives.hax.Tuple0]
    [trait_constr_ok_or_else_i0 : core_models.ops.function.FnOnce
      F
      rust_primitives.hax.Tuple0
      (associatedTypes := {
        show
          core_models.ops.function.FnOnce.AssociatedTypes
          F
          rust_primitives.hax.Tuple0
        by infer_instance
        with Output := u64})]
    (b : Bool)
    (f : F) :
    RustM (core_models.result.Result rust_primitives.hax.Tuple0 u64) := do
  if b then do
    (pure (core_models.result.Result.Ok rust_primitives.hax.Tuple0.mk))
  else do
    (pure (core_models.result.Result.Err
      (← (core_models.ops.function.FnOnce.call_once
        F
        rust_primitives.hax.Tuple0 f rust_primitives.hax.Tuple0.mk))))

end ok_or_else_u64

