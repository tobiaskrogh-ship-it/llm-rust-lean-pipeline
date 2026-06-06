
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


namespace map_try_fold_method_u64

--  Concrete monomorphization of `core::iter::adapters::map::Map<I, F>`.
structure Map where
  iter : (core_models.ops.range.Range u64)
  f : (u64 -> RustM u64)

--  Try-fold all elements through `g` after applying the inner mapper.
@[spec]
def Impl.try_fold
    (G : Type)
    [trait_constr_try_fold_associated_type_i0 :
      core_models.ops.function.FnMut.AssociatedTypes
      G
      (rust_primitives.hax.Tuple2 u64 u64)]
    [trait_constr_try_fold_i0 : core_models.ops.function.FnMut
      G
      (rust_primitives.hax.Tuple2 u64 u64)
      (associatedTypes := {
        show
          core_models.ops.function.FnMut.AssociatedTypes
          G
          (rust_primitives.hax.Tuple2 u64 u64)
        by infer_instance
        with sorry})]
    (self : Map)
    (init : u64)
    (g : G) :
    RustM (rust_primitives.hax.Tuple2 Map (core_models.option.Option u64)) := do
  let acc : u64 := init;
  let failed : Bool := false;
  let i : u64 := (core_models.ops.range.Range.start (Map.iter self));
  let _end : u64 := (core_models.ops.range.Range._end (Map.iter self));
  let ⟨acc, failed, g, i⟩ ←
    (rust_primitives.hax.while_loop
      (fun ⟨acc, failed, g, i⟩ => (do (pure true) : RustM Bool))
      (fun ⟨acc, failed, g, i⟩ =>
        (do ((← (i <? _end)) &&? (← (!? failed))) : RustM Bool))
      (fun ⟨acc, failed, g, i⟩ =>
        (do
        (rust_primitives.hax.int.from_machine (0 : u32)) :
        RustM hax_lib.int.Int))
      (rust_primitives.hax.Tuple4.mk acc failed g i)
      (fun ⟨acc, failed, g, i⟩ =>
        (do
        let ⟨tmp0, out⟩ ←
          (core_models.ops.function.FnMut.call_mut
            G
            (rust_primitives.hax.Tuple2 u64 u64)
            g
            (rust_primitives.hax.Tuple2.mk acc (← ((Map.f self) i))));
        let g : G := tmp0;
        match out with
          | (core_models.option.Option.Some  new_acc) => do
            let acc : u64 := new_acc;
            let i : u64 ← (i +? (1 : u64));
            (pure (rust_primitives.hax.Tuple4.mk acc failed g i))
          | (core_models.option.Option.None ) => do
            let i : u64 ← (i +? (1 : u64));
            let failed : Bool := true;
            (pure (rust_primitives.hax.Tuple4.mk acc failed g i)) :
        RustM (rust_primitives.hax.Tuple4 u64 Bool G u64))));
  let self : Map := {self with iter := {(Map.iter self) with start := i}};
  let hax_temp_output : (core_models.option.Option u64) ←
    if failed then do
      (pure core_models.option.Option.None)
    else do
      (pure (core_models.option.Option.Some acc));
  (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

end map_try_fold_method_u64

