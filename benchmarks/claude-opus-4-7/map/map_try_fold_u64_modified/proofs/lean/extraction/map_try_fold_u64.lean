
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


namespace map_try_fold_u64

--  Compose a unary mapper `f` and a binary short-circuiting folder `g` into a
--  single try-fold step that applies `f` to the element and then folds the
--  result with `g`, propagating `None`/`Some(_)`.
@[spec]
def map_try_fold
    (impl_FnMut(u64)_-__u64 : Type)
    (impl_FnMut(u64,_u64)_-__Option_u64__+_'a : Type)
    [trait_constr_map_try_fold_associated_type_i0 :
      core_models.ops.function.FnMut.AssociatedTypes
      impl_FnMut(u64)_-__u64
      (rust_primitives.hax.Tuple1 u64)]
    [trait_constr_map_try_fold_i0 : core_models.ops.function.FnMut
      impl_FnMut(u64)_-__u64
      (rust_primitives.hax.Tuple1 u64)
      (associatedTypes := {
        show
          core_models.ops.function.FnMut.AssociatedTypes
          impl_FnMut(u64)_-__u64
          (rust_primitives.hax.Tuple1 u64)
        by infer_instance
        with sorry, sorry})]
    [trait_constr_map_try_fold_associated_type_i1 :
      core_models.ops.function.FnMut.AssociatedTypes
      impl_FnMut(u64,_u64)_-__Option_u64__+_'a
      (rust_primitives.hax.Tuple2 u64 u64)]
    [trait_constr_map_try_fold_i1 : core_models.ops.function.FnMut
      impl_FnMut(u64,_u64)_-__Option_u64__+_'a
      (rust_primitives.hax.Tuple2 u64 u64)
      (associatedTypes := {
        show
          core_models.ops.function.FnMut.AssociatedTypes
          impl_FnMut(u64,_u64)_-__Option_u64__+_'a
          (rust_primitives.hax.Tuple2 u64 u64)
        by infer_instance
        with sorry, sorry})]
    (f : impl_FnMut(u64)_-__u64)
    (g : impl_FnMut(u64,_u64)_-__Option_u64__+_'a) :
    RustM
    (rust_primitives.hax.Tuple2
      impl_FnMut(u64)_-__u64
      (u64 -> u64 -> RustM (core_models.option.Option u64)))
    := do
  (pure sorry)

end map_try_fold_u64

