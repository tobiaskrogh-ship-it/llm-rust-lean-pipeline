-- Companion obligations file for the `while_count_up` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import while_count_up

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace While_count_upObligations

/-- Main postcondition: for every `u64` input `n`, `count_up_while n` returns
    `n`. This single equation captures all three contract-style tests in the
    Rust source:
      * `zero_returns_zero` (n = 0 boundary)
      * `known_values` (n = 1, 5, 100)
      * `returns_n` proptest (n in 0..10_000)

    The statement is universal over all `u64` (not bounded like the proptest):
    each loop iteration computes `i + 1` only when `i < n` holds, so
    `i + 1 ≤ n ≤ 2^64 - 1` and no `u64` add-overflow ever occurs, even at
    `n = u64::MAX`. -/
theorem count_up_while_postcondition (n : u64) :
    while_count_up.count_up_while n = RustM.ok n := by
  sorry

/-- Boundary clause: `count_up_while 0 = 0` (loop body never executes).
    Captures the `zero_returns_zero` test explicitly. Derived from the
    universal postcondition. -/
theorem count_up_while_zero :
    while_count_up.count_up_while 0 = RustM.ok 0 :=
  count_up_while_postcondition 0

/-- Totality / no-panic: for every `u64` input the function returns a value
    (it never overflows). Derived from the universal postcondition. -/
theorem count_up_while_total (n : u64) :
    ∃ v : u64, while_count_up.count_up_while n = RustM.ok v :=
  ⟨n, count_up_while_postcondition n⟩

end While_count_upObligations
