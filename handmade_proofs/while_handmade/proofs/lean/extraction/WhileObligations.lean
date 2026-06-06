
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import while_handmade

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace WhileObligations

/-- Postcondition: `count_to n` returns `n`. Total — no precondition.

    Proof pattern: the two-stage `while`-loop scheme from `while_example` —
    prove a Hoare triple over `Spec.MonoLoopCombinator.while_loop` with a
    Lean-side invariant (`i ≤ n`) and a measure on `(n - i).toNat`, then
    convert it to the equation via `RustM.Triple_iff_BitVec`. -/
theorem count_to_postcondition (n : u64) :
    while_handmade.count_to n = RustM.ok n := by
  sorry

/-- Boundary: `count_to 0` returns `0` — the loop guard `i !=? n` is false
    immediately, so the loop body never runs. -/
theorem count_to_zero :
    while_handmade.count_to 0 = RustM.ok 0 := by
  sorry

end WhileObligations
