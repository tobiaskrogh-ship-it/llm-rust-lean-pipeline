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

/-- **Failure condition (no panic / no divergence).**
    `gcd_while` always returns a successful result. The only fallible
    operation in the body is `a %? b`, but it is guarded by the loop
    condition `b != 0`, so the function never fails. -/
theorem gcd_while_total (a b : u64) :
    ∃ g, gcd_while.gcd_while a b = RustM.ok g := by
  sorry

/-- **Postcondition (boundary at `(0, 0)`).**
    By convention `gcd(0, 0) = 0`. This case must be stated separately
    because the `greatest` clause is vacuous when both inputs are zero
    (every natural number divides `0`). -/
theorem gcd_while_zero_zero :
    gcd_while.gcd_while (0 : u64) (0 : u64) = RustM.ok (0 : u64) := by
  sorry

/-- **Postcondition (common divisor).**
    The returned value divides both inputs. Stated with `Nat` divisibility
    (`∣`), so the boundary case `gcd_while 0 0 = 0` is consistent
    (`0 ∣ 0` holds), while a returned `0` for any non-`(0, 0)` input would
    be ruled out (since `0 ∤ n` for `n > 0`). -/
theorem gcd_while_divides_both (a b g : u64)
    (h : gcd_while.gcd_while a b = RustM.ok g) :
    g.toNat ∣ a.toNat ∧ g.toNat ∣ b.toNat := by
  sorry

/-- **Postcondition (greatest).**
    No natural number strictly greater than the returned value divides
    both inputs. Excludes the degenerate `(0, 0)` case where every natural
    divides both inputs (handled by `gcd_while_zero_zero` instead). -/
theorem gcd_while_greatest (a b g : u64)
    (h : gcd_while.gcd_while a b = RustM.ok g)
    (h_not_both_zero : a ≠ 0 ∨ b ≠ 0)
    (d : Nat) (hd : g.toNat < d) :
    ¬ (d ∣ a.toNat ∧ d ∣ b.toNat) := by
  sorry

end Gcd_whileObligations
