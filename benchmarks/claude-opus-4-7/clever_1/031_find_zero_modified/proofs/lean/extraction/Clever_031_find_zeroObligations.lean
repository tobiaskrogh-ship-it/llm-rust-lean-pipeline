-- Companion obligations file for the `clever_031_find_zero` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_031_find_zero

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_031_find_zeroObligations

-- Postcondition: `find_zero` returns `0` for every input slice `xs`.
--
-- This single theorem captures both property tests in the Rust source:
--   * `returns_zero_for_any_input` (proptest over randomly generated
--     `Vec<i64>` of length 0..32), and
--   * `returns_zero_on_empty_slice` (the empty-slice instance pinned as
--     a unit test).
-- The empty-slice case is just a specific instance of the universally
-- quantified postcondition.
--
-- (No precondition: the function is total on every slice; the body is
-- `let _ := xs; pure 0` and ignores `xs` entirely.)
-- (No failure condition: returning a constant cannot panic.)
theorem find_zero_returns_zero (xs : RustSlice i64) :
    clever_031_find_zero.find_zero xs = RustM.ok 0 := rfl

end Clever_031_find_zeroObligations
