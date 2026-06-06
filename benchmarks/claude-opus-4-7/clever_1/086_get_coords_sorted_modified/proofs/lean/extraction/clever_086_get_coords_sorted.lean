
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


namespace clever_086_get_coords_sorted

--  HumanEval/87 / CLEVER 086 — `get_coords_sorted(lst, x)`.  Given a
--  jagged 2D matrix `lst` (slice of slices) and an integer `x`, find
--  every coordinate `(row, col)` where `lst[row][col] == x`.  Return
--  pairs sorted by row ascending; within a row, by column descending.
@[spec]
def scan_row_desc
    (row : (RustSlice i64))
    (r : i64)
    (x : i64)
    (j : usize)
    (acc :
    (alloc.vec.Vec (rust_primitives.hax.Tuple2 i64 i64) alloc.alloc.Global)) :
    RustM
    (alloc.vec.Vec (rust_primitives.hax.Tuple2 i64 i64) alloc.alloc.Global)
    := do
  if (← (j ==? (0 : usize))) then do
    let
      acc : (alloc.vec.Vec
        (rust_primitives.hax.Tuple2 i64 i64)
        alloc.alloc.Global) :=
      acc;
    let
      acc : (alloc.vec.Vec
        (rust_primitives.hax.Tuple2 i64 i64)
        alloc.alloc.Global) ←
      if (← (!? (← (core_models.slice.Impl.is_empty i64 row)))) then do
        if (← ((← row[(0 : usize)]_?) ==? x)) then do
          let chunk : (RustArray (rust_primitives.hax.Tuple2 i64 i64) 1) :=
            (RustArray.ofVec #v[(rust_primitives.hax.Tuple2.mk r (0 : i64))]);
          let
            acc : (alloc.vec.Vec
              (rust_primitives.hax.Tuple2 i64 i64)
              alloc.alloc.Global) ←
            (alloc.vec.Impl_2.extend_from_slice
              (rust_primitives.hax.Tuple2 i64 i64)
              alloc.alloc.Global acc (← (rust_primitives.unsize chunk)));
          (pure acc)
        else do
          (pure acc)
      else do
        (pure acc);
    (pure acc)
  else do
    let col : usize ← (j -? (1 : usize));
    let
      acc : (alloc.vec.Vec
        (rust_primitives.hax.Tuple2 i64 i64)
        alloc.alloc.Global) :=
      acc;
    let
      acc : (alloc.vec.Vec
        (rust_primitives.hax.Tuple2 i64 i64)
        alloc.alloc.Global) ←
      if (← ((← row[col]_?) ==? x)) then do
        let chunk : (RustArray (rust_primitives.hax.Tuple2 i64 i64) 1) :=
          (RustArray.ofVec #v[(rust_primitives.hax.Tuple2.mk
                                  r
                                  (← (rust_primitives.hax.cast_op
                                    col :
                                    RustM i64)))]);
        let
          acc : (alloc.vec.Vec
            (rust_primitives.hax.Tuple2 i64 i64)
            alloc.alloc.Global) ←
          (alloc.vec.Impl_2.extend_from_slice
            (rust_primitives.hax.Tuple2 i64 i64)
            alloc.alloc.Global acc (← (rust_primitives.unsize chunk)));
        (pure acc)
      else do
        (pure acc);
    (scan_row_desc row r x col acc)
partial_fixpoint

@[spec]
def scan_at
    (lst : (RustSlice (RustSlice i64)))
    (x : i64)
    (i : usize)
    (acc :
    (alloc.vec.Vec (rust_primitives.hax.Tuple2 i64 i64) alloc.alloc.Global)) :
    RustM
    (alloc.vec.Vec (rust_primitives.hax.Tuple2 i64 i64) alloc.alloc.Global)
    := do
  if (← (i >=? (← (core_models.slice.Impl.len (RustSlice i64) lst)))) then do
    (pure acc)
  else do
    let
      next : (alloc.vec.Vec
        (rust_primitives.hax.Tuple2 i64 i64)
        alloc.alloc.Global) ←
      (scan_row_desc
        (← lst[i]_?)
        (← (rust_primitives.hax.cast_op i : RustM i64))
        x
        (← (core_models.slice.Impl.len i64 (← lst[i]_?)))
        acc);
    (scan_at lst x (← (i +? (1 : usize))) next)
partial_fixpoint

@[spec]
def get_coords_sorted (lst : (RustSlice (RustSlice i64))) (x : i64) :
    RustM
    (alloc.vec.Vec (rust_primitives.hax.Tuple2 i64 i64) alloc.alloc.Global)
    := do
  (scan_at
    lst
    x
    (0 : usize)
    (← (alloc.vec.Impl.new (rust_primitives.hax.Tuple2 i64 i64)
      rust_primitives.hax.Tuple0.mk)))

end clever_086_get_coords_sorted

