
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


namespace clever_021_rescale_to_unit

--  Apply a linear shift to a list so the smallest number becomes 0.
--  Integer version of the float "scale to [0,1]" contract — without floats
--  we cannot also force the largest to be 1, so the contract is restricted
--  to the shift (subtract min). Length must be ≥ 2.
@[spec]
def min_at (numbers : (RustSlice i64)) (i : usize) (m : i64) : RustM i64 := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 numbers)))) then do
    (pure m)
  else do
    if (← ((← numbers[i]_?) <? m)) then do
      (min_at numbers (← (i +? (1 : usize))) (← numbers[i]_?))
    else do
      (min_at numbers (← (i +? (1 : usize))) m)
partial_fixpoint

@[spec]
def shift_at
    (numbers : (RustSlice i64))
    (delta : i64)
    (i : usize)
    (acc : (alloc.vec.Vec i64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 numbers)))) then do
    (pure acc)
  else do
    let chunk : (RustArray i64 1) :=
      (RustArray.ofVec #v[(← ((← numbers[i]_?) -? delta))]);
    let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
        acc
        (← (rust_primitives.unsize chunk)));
    (shift_at numbers delta (← (i +? (1 : usize))) acc)
partial_fixpoint

@[spec]
def rescale_to_unit (numbers : (RustSlice i64)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  if (← ((← (core_models.slice.Impl.len i64 numbers)) <? (2 : usize))) then do
    (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk)
  else do
    let m : i64 ← (min_at numbers (1 : usize) (← numbers[(0 : usize)]_?));
    (shift_at
      numbers
      m
      (0 : usize)
      (← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk)))

end clever_021_rescale_to_unit

