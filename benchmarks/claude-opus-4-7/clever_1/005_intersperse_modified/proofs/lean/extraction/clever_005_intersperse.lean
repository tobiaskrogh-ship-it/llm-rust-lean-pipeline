
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


namespace clever_005_intersperse

--  Insert `delimiter` between every two consecutive elements of `numbers`.
@[spec]
def intersperse_at
    (numbers : (RustSlice i64))
    (delimiter : i64)
    (i : usize)
    (acc : (alloc.vec.Vec i64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 numbers)))) then do
    (pure acc)
  else do
    let n : i64 ← numbers[i]_?;
    let acc : (alloc.vec.Vec i64 alloc.alloc.Global) := acc;
    let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
      if (← (i ==? (0 : usize))) then do
        let chunk : (RustArray i64 1) := (RustArray.ofVec #v[n]);
        let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
          (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
            acc
            (← (rust_primitives.unsize chunk)));
        (pure acc)
      else do
        let chunk : (RustArray i64 2) := (RustArray.ofVec #v[delimiter, n]);
        let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
          (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
            acc
            (← (rust_primitives.unsize chunk)));
        (pure acc);
    (intersperse_at numbers delimiter (← (i +? (1 : usize))) acc)
partial_fixpoint

@[spec]
def intersperse (numbers : (RustSlice i64)) (delimiter : i64) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  (intersperse_at
    numbers
    delimiter
    (0 : usize)
    (← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk)))

end clever_005_intersperse

