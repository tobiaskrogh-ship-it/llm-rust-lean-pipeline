
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


namespace clever_114_max_fill_count

--  HumanEval/115 / CLEVER 114 — `max_fill_count(grid, capacity)`.  Each
--  row of `grid` is a well; cells contain `0` or `1` (water units).
--  Buckets all have `capacity`.  Return the total number of bucket
--  trips needed to empty every well (ceil(ones_in_row / capacity)).
@[spec]
def count_row_at (row : (RustSlice u64)) (j : usize) (acc : u64) :
    RustM u64 := do
  if (← (j >=? (← (core_models.slice.Impl.len u64 row)))) then do
    (pure acc)
  else do
    if (← ((← row[j]_?) !=? (0 : u64))) then do
      (count_row_at row (← (j +? (1 : usize))) (← (acc +? (1 : u64))))
    else do
      (count_row_at row (← (j +? (1 : usize))) acc)
partial_fixpoint

@[spec]
def rows_at
    (grid : (RustSlice (RustSlice u64)))
    (capacity : u64)
    (i : usize)
    (acc : u64) :
    RustM u64 := do
  if (← (i >=? (← (core_models.slice.Impl.len (RustSlice u64) grid)))) then do
    (pure acc)
  else do
    let w : u64 ← (count_row_at (← grid[i]_?) (0 : usize) (0 : u64));
    let trips : u64 ← ((← ((← (w +? capacity)) -? (1 : u64))) /? capacity);
    (rows_at grid capacity (← (i +? (1 : usize))) (← (acc +? trips)))
partial_fixpoint

@[spec]
def max_fill_count (grid : (RustSlice (RustSlice u64))) (capacity : u64) :
    RustM u64 := do
  if (← (capacity ==? (0 : u64))) then do
    (pure (0 : u64))
  else do
    (rows_at grid capacity (0 : usize) (0 : u64))

end clever_114_max_fill_count

