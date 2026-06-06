
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


namespace map_size_hint_u64

--  Concrete monomorphization of `core::iter::adapters::map::Map<I, F>`.
structure Map where
  iter : (core_models.ops.range.Range u64)
  f : (u64 -> RustM u64)

--  Return the inner iterator's `size_hint` unchanged — `Map` is 1:1.
@[spec]
def Impl.size_hint (self : Map) :
    RustM
    (rust_primitives.hax.Tuple2 usize (core_models.option.Option usize))
    := do
  if
  (← ((core_models.ops.range.Range.start (Map.iter self))
    >=? (core_models.ops.range.Range._end (Map.iter self)))) then do
    (pure (rust_primitives.hax.Tuple2.mk
      (0 : usize)
      (core_models.option.Option.Some (0 : usize))))
  else do
    let diff : u64 ←
      ((core_models.ops.range.Range._end (Map.iter self))
        -? (core_models.ops.range.Range.start (Map.iter self)));
    let n : usize ← (rust_primitives.hax.cast_op diff : RustM usize);
    (pure (rust_primitives.hax.Tuple2.mk n (core_models.option.Option.Some n)))

end map_size_hint_u64

