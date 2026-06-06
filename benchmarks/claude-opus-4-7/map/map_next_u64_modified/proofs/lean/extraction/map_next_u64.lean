
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


namespace map_next_u64

--  Concrete monomorphization of `core::iter::adapters::map::Map<I, F>`.
structure Map where
  iter : (core_models.ops.range.Range u64)
  f : (u64 -> RustM u64)

--  Pull the next item from the inner iterator and map it.
@[spec]
def Impl.next (self : Map) :
    RustM (rust_primitives.hax.Tuple2 Map (core_models.option.Option u64)) := do
  let ⟨self, hax_temp_output⟩ ←
    if
    (← ((core_models.ops.range.Range.start (Map.iter self))
      >=? (core_models.ops.range.Range._end (Map.iter self)))) then do
      (pure (rust_primitives.hax.Tuple2.mk self core_models.option.Option.None))
    else do
      let v : u64 := (core_models.ops.range.Range.start (Map.iter self));
      let self : Map :=
        {self
        with iter := {(Map.iter self)
        with start := (← ((core_models.ops.range.Range.start (Map.iter self))
          +? (1 : u64)))}};
      (pure (rust_primitives.hax.Tuple2.mk
        self
        (core_models.option.Option.Some (← ((Map.f self) v)))));
  (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

end map_next_u64

