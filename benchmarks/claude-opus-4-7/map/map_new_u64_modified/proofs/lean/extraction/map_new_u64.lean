
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


namespace map_new_u64

--  Concrete monomorphization of `core::iter::adapters::map::Map<I, F>`.
structure Map where
  iter : (core_models.ops.range.Range u64)
  f : (u64 -> RustM u64)

@[instance] opaque Impl_1.AssociatedTypes :
  core_models.clone.Clone.AssociatedTypes Map :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1 :
  core_models.clone.Clone Map :=
  by constructor <;> exact Inhabited.default

--  Construct a new `Map` wrapping `iter` with mapper `f`.
@[spec]
def Impl.new
    (iter : (core_models.ops.range.Range u64))
    (f : (u64 -> RustM u64)) :
    RustM Map := do
  (pure (Map.mk (iter := iter) (f := f)))

end map_new_u64

