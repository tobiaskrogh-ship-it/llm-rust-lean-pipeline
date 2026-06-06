
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


namespace then_u64

--  Returns `Some(f())` if `b` is `true`, or `None` otherwise.
@[spec]
def then_some
    (F : Type)
    [trait_constr_then_some_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      rust_primitives.hax.Tuple0]
    [trait_constr_then_some_i0 : core_models.ops.function.FnOnce
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
    RustM (core_models.option.Option u64) := do
  if b then do
    (pure (core_models.option.Option.Some
      (← (core_models.ops.function.FnOnce.call_once
        F
        rust_primitives.hax.Tuple0 f rust_primitives.hax.Tuple0.mk))))
  else do
    (pure core_models.option.Option.None)

end then_u64

