
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


namespace clever_136_is_equal_to_sum_even

--  HumanEval/138 / CLEVER 136 — `is_equal_to_sum_even(n)`.  True iff
--  `n` can be written as the sum of exactly four positive even
--  integers.  Closed form: n is even AND n >= 8.  Override to `u64`
--  since the answer is always false for negative or small n.
@[spec]
def is_equal_to_sum_even (n : u64) : RustM Bool := do
  ((← (n >=? (8 : u64))) &&? (← ((← (n %? (2 : u64))) ==? (0 : u64))))

end clever_136_is_equal_to_sum_even

