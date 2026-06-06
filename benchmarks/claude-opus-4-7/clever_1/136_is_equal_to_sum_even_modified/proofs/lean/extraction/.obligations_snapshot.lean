-- Companion obligations file for the `clever_136_is_equal_to_sum_even` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_136_is_equal_to_sum_even

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_136_is_equal_to_sum_evenObligations

open clever_136_is_equal_to_sum_even

/-- Closed-form postcondition: `is_equal_to_sum_even n` returns the Boolean
    `(n >= 8) && (n % 2 == 0)`. The static divisor `2` is nonzero so `%?`
    never fires its `divisionByZero` branch, and the comparisons / `&&?`
    are pure. This foundational equational form is the source from which
    the per-test contract clauses below derive. Not itself a Rust
    property test, but stated in the style preferred by the reference
    examples (`truncate_number_postcondition`, `is_zero_spec`): when the
    precondition is trivially `True`, the equational form
    `f n = RustM.ok …` is easier to prove than a Hoare triple. -/
theorem is_equal_to_sum_even_postcondition (n : u64) :
    is_equal_to_sum_even n = RustM.ok (decide ((8 : u64) ≤ n) && (n % 2 == 0)) := by
  sorry

/-- Totality / no-panic: for every `u64` input, `is_equal_to_sum_even n`
    returns a value successfully. The only partial operation on the path
    is `n %? 2`, and the divisor `2` is statically nonzero so the
    `divisionByZero` branch is unreachable. Mirrors the implicit
    "no failure mode" surface of a closed-form Boolean predicate. -/
theorem is_equal_to_sum_even_total (n : u64) :
    ∃ r : Bool, is_equal_to_sum_even n = RustM.ok r :=
  ⟨decide ((8 : u64) ≤ n) && (n % 2 == 0), is_equal_to_sum_even_postcondition n⟩

/-- Postcondition (semantic soundness on the valid domain, first half of
    `accepts_even_at_least_8_with_witness`): for every even `n ≥ 8` the
    function returns `true`. -/
theorem is_equal_to_sum_even_accepts_even_at_least_8
    (n : u64) (hge : (8 : u64) ≤ n) (heven : n % 2 = 0) :
    is_equal_to_sum_even n = RustM.ok true := by
  sorry

/-- Postcondition (witness / semantic completeness, second half of
    `accepts_even_at_least_8_with_witness`): for every even `n ≥ 8`
    there exist four positive even `u64` summands whose sum is `n`.
    Captures the proptest's concrete decomposition `2 + 2 + 2 + (n - 6)`,
    which justifies the function's name `is_equal_to_sum_even` —
    accepted inputs really are sums of four positive even integers. -/
theorem is_equal_to_sum_even_witness_exists
    (n : u64) (hge : (8 : u64) ≤ n) (heven : n % 2 = 0) :
    ∃ a b c d : u64,
      0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d
      ∧ a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 0 ∧ d % 2 = 0
      ∧ a + b + c + d = n := by
  sorry

/-- Failure condition (parity), from proptest `rejects_odd`: the sum of
    any four even integers is even, so every odd `n` is rejected.
    Phrased as `n % 2 = 1` to match the Rust test guard. -/
theorem is_equal_to_sum_even_rejects_odd
    (n : u64) (hodd : n % 2 = 1) :
    is_equal_to_sum_even n = RustM.ok false := by
  sorry

/-- Failure condition (lower bound), from unit test `rejects_below_minimum_sum`:
    the smallest sum of four positive even integers is `2 + 2 + 2 + 2 = 8`,
    so every `n < 8` is rejected. -/
theorem is_equal_to_sum_even_rejects_below_minimum
    (n : u64) (hlt : n < (8 : u64)) :
    is_equal_to_sum_even n = RustM.ok false := by
  sorry

end Clever_136_is_equal_to_sum_evenObligations
