-- Companion obligations file for the `gcd_while` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import gcd_while

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Gcd_whileObligations

/-- Postcondition (loop-exit base case):
    when `b = 0`, the loop's exit condition `b !=? 0` is false on entry,
    so the loop body never executes. The function therefore returns `a`
    successfully.

    This is the only "what does the function return" postcondition that
    is expressible without divisibility (`%`), which the Rust source's
    comment notes is unprovable for the chosen extraction. It pins down
    the `gcd(a, 0) = a` boundary documented in the property tests
    (`zero_zero_is_zero`, `zero_input_returns_other` for `b = 0`). -/
theorem gcd_while_b_zero (a : u64) :
    gcd_while.gcd_while a 0 = pure a := by
  sorry

/-- Totality / panic-freedom:
    for every pair of `u64` inputs, `gcd_while` returns a value
    successfully. The function has two potential failure modes:
      * the modulo `a %? b` panics on `b = 0`, which is prevented by
        the loop's `b !=? 0` exit condition (the loop body only runs
        when `b ≠ 0`);
      * the `while_loop` combinator could diverge, which is prevented
        by the `loop_decreases!(b)` measure — `b` decreases strictly
        on each iteration (the new `b` is `a % old_b`, which is
        strictly less than `old_b`).
    Combined, these guarantee `gcd_while a b = pure v` for some `v`,
    excluding both `RustM.fail` (panic) and `RustM.div` (divergence).

    This is the headline contract for this extraction; the Rust source
    comment notes that divisibility / greatest-common-divisor properties
    cannot be proved downstream, so termination + panic-freedom *is* the
    full verified contract. -/
theorem gcd_while_total (a b : u64) :
    ∃ v : u64, gcd_while.gcd_while a b = pure v := by
  sorry

end Gcd_whileObligations
