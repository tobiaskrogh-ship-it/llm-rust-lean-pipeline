
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


namespace map_rfold_u64

--  Concrete monomorphization of `core::iter::adapters::map::Map<I, F>`.
structure Map where
  iter : (core_models.ops.range.Range u64)
  f : (u64 -> RustM u64)

--  Consume the `Map` from the back by folding all elements through `g`
--  after applying the inner mapper.
@[spec]
def Impl.rfold (self : Map) (init : u64) (g : (u64 -> u64 -> RustM u64)) :
    RustM u64 := do
  let acc : u64 := init;
  let start : u64 := (core_models.ops.range.Range.start (Map.iter self));
  let _end : u64 := (core_models.ops.range.Range._end (Map.iter self));
  let ⟨acc, _end⟩ ←
    (rust_primitives.hax.while_loop
      (fun ⟨acc, _end⟩ => (do (pure true) : RustM Bool))
      (fun ⟨acc, _end⟩ => (do (_end >? start) : RustM Bool))
      (fun ⟨acc, _end⟩ =>
        (do
        (rust_primitives.hax.int.from_machine (0 : u32)) :
        RustM hax_lib.int.Int))
      (rust_primitives.hax.Tuple2.mk acc _end)
      (fun ⟨acc, _end⟩ =>
        (do
        let _end : u64 ← (_end -? (1 : u64));
        let acc : u64 ← (g acc (← ((Map.f self) _end)));
        (pure (rust_primitives.hax.Tuple2.mk acc _end)) :
        RustM (rust_primitives.hax.Tuple2 u64 u64))));
  (pure acc)

end map_rfold_u64

