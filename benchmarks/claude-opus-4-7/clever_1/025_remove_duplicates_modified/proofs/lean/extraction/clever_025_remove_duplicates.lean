
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


namespace clever_025_remove_duplicates

--  Remove all elements that occur more than once in `numbers`. Elements
--  kept appear in their original input order.
@[spec]
def count_at
    (numbers : (RustSlice i64))
    (target : i64)
    (i : usize)
    (acc : i64) :
    RustM i64 := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 numbers)))) then do
    (pure acc)
  else do
    if (← ((← numbers[i]_?) ==? target)) then do
      (count_at numbers target (← (i +? (1 : usize))) (← (acc +? (1 : i64))))
    else do
      (count_at numbers target (← (i +? (1 : usize))) acc)
partial_fixpoint

@[spec]
def build_at
    (numbers : (RustSlice i64))
    (i : usize)
    (acc : (alloc.vec.Vec i64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 numbers)))) then do
    (pure acc)
  else do
    if
    (← ((← (count_at numbers (← numbers[i]_?) (0 : usize) (0 : i64)))
      ==? (1 : i64))) then do
      let chunk : (RustArray i64 1) := (RustArray.ofVec #v[(← numbers[i]_?)]);
      let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
          acc
          (← (rust_primitives.unsize chunk)));
      (build_at numbers (← (i +? (1 : usize))) acc)
    else do
      (build_at numbers (← (i +? (1 : usize))) acc)
partial_fixpoint

@[spec]
def remove_duplicates (numbers : (RustSlice i64)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  (build_at
    numbers
    (0 : usize)
    (← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk)))

end clever_025_remove_duplicates

