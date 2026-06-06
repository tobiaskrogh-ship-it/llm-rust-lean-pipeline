
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


namespace clever_009_rolling_max

--  From a given list of integers, generate a list of the rolling maximum
--  element found until each position in the sequence.
--  (CLEVER's signature column for problem 9 lists `sum_product(...) -> (int, int)`
--  but its docstring describes rolling-max. We follow the docstring.)
-- 
--  Hax-compatibility rewrite notes:
--    * `for &n in numbers` desugars to `Iterator::fold` over
--      `IntoIterator (RustSlice i64)`, neither modeled by the Hax Lean
--      prelude. Converted to index-based tail recursion per
--      `rewrite_patterns/for_loop_over_slice_to_recursion.rs` (also
--      preferred over `while` per the recursion-preference rule).
--    * `Vec::push` (`alloc.vec.Impl_1.push`) is undefined in the prelude;
--      `Vec::extend_from_slice` IS defined and is used here with a typed
--      let-bound `[i64; 1]` chunk so the array size appears in the type
--      ascription and Hax can resolve `unsize`'s `RustArray` size
--      parameter. See `rewrite_patterns/vec_push_to_extend_from_slice_typed_chunk.rs`.
--    * `i64::MIN` (`core_models.num.Impl_*.MIN`) is undefined in the
--      prelude. Replaced by special-casing `i == 0` inside the recursion:
--      at the first index the running maximum is unconditionally set to
--      the element itself, so no sentinel "minus infinity" is needed.
--      See `rewrite_patterns/primitive_int_assoc_const.rs`.
@[spec]
def rolling_max_at
    (numbers : (RustSlice i64))
    (i : usize)
    (max_so_far : i64)
    (acc : (alloc.vec.Vec i64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 numbers)))) then do
    (pure acc)
  else do
    let n : i64 ← numbers[i]_?;
    let new_max : i64 ←
      if (← ((← (i ==? (0 : usize))) ||? (← (n >? max_so_far)))) then do
        (pure n)
      else do
        (pure max_so_far);
    let acc : (alloc.vec.Vec i64 alloc.alloc.Global) := acc;
    let chunk : (RustArray i64 1) := (RustArray.ofVec #v[new_max]);
    let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
        acc
        (← (rust_primitives.unsize chunk)));
    (rolling_max_at numbers (← (i +? (1 : usize))) new_max acc)
partial_fixpoint

@[spec]
def rolling_max (numbers : (RustSlice i64)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  (rolling_max_at
    numbers
    (0 : usize)
    (0 : i64)
    (← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk)))

end clever_009_rolling_max

