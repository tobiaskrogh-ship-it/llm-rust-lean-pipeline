
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


namespace clever_113_minSubArraySum

--  HumanEval/114 / CLEVER 113 — `minSubArraySum(nums)`.  Minimum sum
--  of any non-empty contiguous subarray.  Empty input: returns 0
--  (degenerate sentinel; spec assumes non-empty input).
@[spec]
def run_at (l : (RustSlice i64)) (i : usize) (cur : i64) (best : i64) :
    RustM i64 := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 l)))) then do
    (pure best)
  else do
    let ext : i64 ← (cur +? (← l[i]_?));
    let nc : i64 ← if (← (ext <? (← l[i]_?))) then do (pure ext) else do l[i]_?;
    let nb : i64 ← if (← (nc <? best)) then do (pure nc) else do (pure best);
    (run_at l (← (i +? (1 : usize))) nc nb)
partial_fixpoint

@[spec]
def minSubArraySum (nums : (RustSlice i64)) : RustM i64 := do
  if (← (core_models.slice.Impl.is_empty i64 nums)) then do
    (pure (0 : i64))
  else do
    (run_at nums (1 : usize) (← nums[(0 : usize)]_?) (← nums[(0 : usize)]_?))

end clever_113_minSubArraySum

