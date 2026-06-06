
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


namespace clever_041_incr_list

--  Return a new list where each element of `numbers` is incremented by 1.
@[spec]
def incr_at
    (numbers : (RustSlice i64))
    (i : usize)
    (acc : (alloc.vec.Vec i64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 numbers)))) then do
    (pure acc)
  else do
    let acc : (alloc.vec.Vec i64 alloc.alloc.Global) := acc;
    let chunk : (RustArray i64 1) :=
      (RustArray.ofVec #v[(← ((← numbers[i]_?) +? (1 : i64)))]);
    let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
        acc
        (← (rust_primitives.unsize chunk)));
    (incr_at numbers (← (i +? (1 : usize))) acc)
partial_fixpoint

@[spec]
def incr_list (numbers : (RustSlice i64)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  (incr_at
    numbers
    (0 : usize)
    (← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk)))

end clever_041_incr_list

