
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


namespace map_fold_method_u64

--  Concrete monomorphization of `core::iter::adapters::map::Map<I, F>`.
structure Map where
  iter : (core_models.ops.range.Range u64)
  f : (u64 -> RustM u64)

--  Consume the `Map` by folding all elements through `g` after applying
--  the inner mapper.
-- 
--  Hax-compatible rewrite: the original used the private helper
--  `map_fold` returning `impl FnMut(...)` and delegated to
--  `Range::fold` (also `FnMut`-bound). Both `impl FnMut(...) -> u64`
--  and `Range::fold`'s bound trigger Hax's "equality constraint on
--  associated types of parent trait" error (`FnOnce::Output = u64`).
--  We replace `Fn*` bounds with `fn(...)` pointers and inline the
--  fold as an explicit `while` loop.
@[spec]
def Impl.fold (self : Map) (init : u64) (g : (u64 -> u64 -> RustM u64)) :
    RustM u64 := do
  let acc : u64 := init;
  let i : u64 := (core_models.ops.range.Range.start (Map.iter self));
  let _end : u64 := (core_models.ops.range.Range._end (Map.iter self));
  let ⟨acc, i⟩ ←
    (rust_primitives.hax.while_loop
      (fun ⟨acc, i⟩ => (do (pure true) : RustM Bool))
      (fun ⟨acc, i⟩ => (do (i <? _end) : RustM Bool))
      (fun ⟨acc, i⟩ =>
        (do
        (rust_primitives.hax.int.from_machine (0 : u32)) :
        RustM hax_lib.int.Int))
      (rust_primitives.hax.Tuple2.mk acc i)
      (fun ⟨acc, i⟩ =>
        (do
        let acc : u64 ← (g acc (← ((Map.f self) i)));
        let i : u64 ← (i +? (1 : u64));
        (pure (rust_primitives.hax.Tuple2.mk acc i)) :
        RustM (rust_primitives.hax.Tuple2 u64 u64))));
  (pure acc)

end map_fold_method_u64

