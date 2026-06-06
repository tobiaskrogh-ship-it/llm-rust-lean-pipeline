
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


namespace map_try_rfold_u64

--  Concrete monomorphization of `core::iter::adapters::map::Map<I, F>`.
structure Map where
  iter : (core_models.ops.range.Range u64)
  f : (u64 -> RustM u64)

--  Tail-recursive worker for `Map::try_rfold`. Walks the half-open range
--  `[start, end)` from the back, applying `f` to each index, threading `acc`
--  through `g`, and short-circuiting on `None`. Returns `(new_end, result)`:
--  `new_end` is the value the caller should write back to `Map.iter.end`
--  (`start` on full consumption, or the unconsumed boundary when `g` returned
--  `None`), and `result` is the fold value (`Some(final_acc)` or `None`).
-- 
--  `Range::try_rfold` and `core::iter::adapters::map::map_try_fold` cannot be
--  extracted directly: the former routes through unmodeled
--  `core_models.iter.traits.iterator.Iterator.try_rfold`, and the latter
--  returns `impl FnMut(...)` which trips HAX0001 (`Unsupported equality
--  constraints on associated types of parent trait`,
--  https://github.com/hacspec/hax/issues/1923). Tail recursion is preferred
--  over a `while` loop per the project's recursion-preference rule.
@[spec]
def try_rfold_at
    (start : u64)
    (_end : u64)
    (f : (u64 -> RustM u64))
    (acc : u64)
    (g : (u64 -> u64 -> RustM (core_models.option.Option u64))) :
    RustM (rust_primitives.hax.Tuple2 u64 (core_models.option.Option u64)) := do
  if (← (start >=? _end)) then do
    (pure (rust_primitives.hax.Tuple2.mk
      _end
      (core_models.option.Option.Some acc)))
  else do
    let new_end : u64 ← (_end -? (1 : u64));
    let x : u64 ← (f new_end);
    match (← (g acc x)) with
      | (core_models.option.Option.None ) => do
        (pure (rust_primitives.hax.Tuple2.mk
          new_end
          core_models.option.Option.None))
      | (core_models.option.Option.Some  new_acc) => do
        (try_rfold_at start new_end f new_acc g)
partial_fixpoint

--  Try-fold from the back through `g` after applying the inner mapper.
@[spec]
def Impl.try_rfold
    (self : Map)
    (init : u64)
    (g : (u64 -> u64 -> RustM (core_models.option.Option u64))) :
    RustM (rust_primitives.hax.Tuple2 Map (core_models.option.Option u64)) := do
  let ⟨new_end, result⟩ ←
    (try_rfold_at
      (core_models.ops.range.Range.start (Map.iter self))
      (core_models.ops.range.Range._end (Map.iter self))
      (Map.f self)
      init
      g);
  let self : Map := {self with iter := {(Map.iter self) with _end := new_end}};
  let hax_temp_output : (core_models.option.Option u64) := result;
  (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

end map_try_rfold_u64

