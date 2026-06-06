
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


namespace clever_020_find_closest_elements

--  From a supplied list of numbers (length ≥ 2), select the pair with the
--  smallest absolute difference and return them as `(smaller, larger)`.
@[spec]
def abs_diff (a : i64) (b : i64) : RustM i64 := do
  if (← (a >? b)) then do (a -? b) else do (b -? a)

@[spec]
def scan_at
    (numbers : (RustSlice i64))
    (i : usize)
    (j : usize)
    (best_i : usize)
    (best_j : usize) :
    RustM (rust_primitives.hax.Tuple2 usize usize) := do
  let n : usize ← (core_models.slice.Impl.len i64 numbers);
  if (← ((← (i +? (1 : usize))) >=? n)) then do
    (pure (rust_primitives.hax.Tuple2.mk best_i best_j))
  else do
    if (← (j >=? n)) then do
      (scan_at
        numbers
        (← (i +? (1 : usize)))
        (← (i +? (2 : usize)))
        best_i
        best_j)
    else do
      let cur : i64 ← (abs_diff (← numbers[i]_?) (← numbers[j]_?));
      let best : i64 ← (abs_diff (← numbers[best_i]_?) (← numbers[best_j]_?));
      if (← (cur <? best)) then do
        (scan_at numbers i (← (j +? (1 : usize))) i j)
      else do
        (scan_at numbers i (← (j +? (1 : usize))) best_i best_j)
partial_fixpoint

@[spec]
def find_closest_elements (numbers : (RustSlice i64)) :
    RustM (rust_primitives.hax.Tuple2 i64 i64) := do
  if (← ((← (core_models.slice.Impl.len i64 numbers)) <? (2 : usize))) then do
    (pure (rust_primitives.hax.Tuple2.mk (0 : i64) (0 : i64)))
  else do
    let ⟨i, j⟩ ←
      (scan_at numbers (0 : usize) (1 : usize) (0 : usize) (1 : usize));
    if (← ((← numbers[i]_?) <=? (← numbers[j]_?))) then do
      (pure (rust_primitives.hax.Tuple2.mk (← numbers[i]_?) (← numbers[j]_?)))
    else do
      (pure (rust_primitives.hax.Tuple2.mk (← numbers[j]_?) (← numbers[i]_?)))

end clever_020_find_closest_elements

