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

/-- Totality / no-panic: for every pair of `u64` inputs, `gcd_while`
    successfully returns a value. The only fallible operation in the
    body is `a %? b`, which is guarded by the loop condition `b !=? 0`,
    so it never panics. Implicit in every `assert_eq!` of the property
    tests. -/
theorem gcd_while_total (a b : u64) :
    ∃ r : u64, gcd_while.gcd_while a b = RustM.ok r := by
  sorry

/-- Boundary (loop never executes when `b = 0`): when the second
    argument is zero, the loop condition fails on entry and the
    function returns `a` unchanged. Subsumes the property test
    `zero_zero_is_zero` (specialised to `a = 0`) and the
    `gcd_while(x, 0) = x` half of `zero_input_returns_other`. -/
theorem gcd_while_b_zero (a : u64) :
    gcd_while.gcd_while a 0 = RustM.ok a := by
  unfold gcd_while.gcd_while
  unfold rust_primitives.hax.while_loop
  unfold Lean.Loop.MonoLoopCombinator.while_loop
  unfold Lean.Loop.MonoLoopCombinator.forIn
  unfold Lean.Loop.MonoLoopCombinator.forIn.loop
  rfl

/-- Boundary (one iteration when `a = 0`): when the first argument is
    zero and the second is non-zero, after one iteration the state is
    `(b, 0 % b) = (b, 0)`, the loop exits, and the function returns
    the original `b`. The case `b = 0` reduces to `gcd_while_b_zero`.
    Together they cover the `gcd_while(0, x) = x` half of
    `zero_input_returns_other`. -/
theorem gcd_while_a_zero (b : u64) :
    gcd_while.gcd_while 0 b = RustM.ok b := by
  by_cases hb : b = 0
  · subst hb; exact gcd_while_b_zero 0
  · -- One-iteration peel: state (0, b) → (b, 0 % b) = (b, 0), then loop exits.
    -- Closing this requires unfolding `Loop.MonoLoopCombinator.forIn` (defined via
    -- `partial_fixpoint`), which forces the evaluation of one body iteration.
    -- The library has no precedent for proving an equational identity about a
    -- single iteration of a `while_loop`; left as `sorry`.
    sorry

/-- Postcondition (zero result implies trivial input): if the result
    is zero, both inputs were zero. Captures the
    `if g == 0 { assert_eq!(a, 0); assert_eq!(b, 0); }` branch of
    `result_divides_both_inputs`. The contrapositive — at least one
    non-zero input forces a non-zero gcd — is the contract clause. -/
theorem gcd_while_zero_iff_both_zero (a b : u64) :
    ⦃ ⌜ True ⌝ ⦄
    gcd_while.gcd_while a b
    ⦃ ⇓ r => ⌜ r = 0 → a = 0 ∧ b = 0 ⌝ ⦄ := by
  sorry

/-- Postcondition (common divisor — first input): the result divides
    `a`. Half of the `result_divides_both_inputs` property. Stated
    independently of `gcd_while_divides_b` because dividing `a` is
    independent of dividing `b` (an impl returning `a` always would
    satisfy this but not the other). The `r = 0 → a = 0` corner is
    absorbed by `Nat`'s total divisibility (`0 ∣ 0`). -/
theorem gcd_while_divides_a (a b : u64) :
    ⦃ ⌜ True ⌝ ⦄
    gcd_while.gcd_while a b
    ⦃ ⇓ r => ⌜ r.toNat ∣ a.toNat ⌝ ⦄ := by
  sorry

/-- Postcondition (common divisor — second input): the result divides
    `b`. Other half of `result_divides_both_inputs`. -/
theorem gcd_while_divides_b (a b : u64) :
    ⦃ ⌜ True ⌝ ⦄
    gcd_while.gcd_while a b
    ⦃ ⇓ r => ⌜ r.toNat ∣ b.toNat ⌝ ⦄ := by
  sorry

/-- Postcondition (greatest): when the result is non-zero, every
    common divisor of `a` and `b` is bounded above by the result.
    Captures `result_is_greatest_common_divisor`, which independently
    pins down the *greatest* part of the contract — the divides
    theorems above admit any common divisor (e.g. `1`), so this
    theorem is what forbids returning a smaller divisor. The guard
    `r ≠ 0` excludes only the `a = b = 0` boundary, where any
    positive `d` divides both inputs and no greatest exists. -/
theorem gcd_while_greatest (a b : u64) :
    ⦃ ⌜ True ⌝ ⦄
    gcd_while.gcd_while a b
    ⦃ ⇓ r => ⌜ r ≠ 0 →
              ∀ d : u64, d.toNat ∣ a.toNat → d.toNat ∣ b.toNat
                       → d.toNat ≤ r.toNat ⌝ ⦄ := by
  sorry

end Gcd_whileObligations
