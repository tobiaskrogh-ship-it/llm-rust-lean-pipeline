
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


namespace clever_039_triples_sum_to_zero

--  Return true iff three distinct positions in `numbers` hold values that
--  sum to zero.
-- 
--  Note: CLEVER pins the type as `u64`, so the only way three non-negative
--  values can sum to 0 is if all three are 0. The function therefore
--  reduces to "at least three zero entries". A semantically richer
--  formulation requires `&[i64]`.
@[spec]
def count_zeros_at (numbers : (RustSlice u64)) (i : usize) (acc : u64) :
    RustM u64 := do
  if (← (i >=? (← (core_models.slice.Impl.len u64 numbers)))) then do
    (pure acc)
  else do
    if (← ((← numbers[i]_?) ==? (0 : u64))) then do
      (count_zeros_at numbers (← (i +? (1 : usize))) (← (acc +? (1 : u64))))
    else do
      (count_zeros_at numbers (← (i +? (1 : usize))) acc)
partial_fixpoint

@[spec]
def triples_sum_to_zero (numbers : (RustSlice u64)) : RustM Bool := do
  ((← (count_zeros_at numbers (0 : usize) (0 : u64))) >=? (3 : u64))

end clever_039_triples_sum_to_zero

