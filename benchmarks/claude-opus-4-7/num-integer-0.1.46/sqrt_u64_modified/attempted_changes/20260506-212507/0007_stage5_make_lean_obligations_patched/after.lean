-- Companion obligations file for the `sqrt_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import sqrt_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Sqrt_u64Obligations

/-- Postcondition (lower bound): the result `r` of `sqrt x` satisfies `r² ≤ x`.

    Stated at the `Nat` level (`r.toNat * r.toNat ≤ x.toNat`) so the square is
    taken in unbounded arithmetic and never wraps. For the correct sqrt value
    `r ≤ ⌊√(2⁶⁴−1)⌋ = 2³² − 1`, so `r * r` would in fact fit in `u64`, but
    the `Nat` form is the cleanest way to state the bound without coupling
    the specification to that totality side condition.

    This is the "lower bound is a square root from below" half of the
    contract — captured by the Rust property test `prop_sqrt_lower_bound`,
    by `sqrt_test`'s `rt_sq <= i` assertion, and (vacuously) by the
    `sqrt_small`/`sqrt_doctest` spot-checks. -/
theorem sqrt_lower_bound (x : u64) :
    ⦃ ⌜ True ⌝ ⦄
      sqrt_u64.sqrt x
    ⦃ ⇓ r => ⌜ r.toNat * r.toNat ≤ x.toNat ⌝ ⦄ := by
  sorry

/-- Postcondition (upper bound): the result `r` of `sqrt x` satisfies
    `x < (r + 1)²`. Stated at the `Nat` level so `(r + 1) * (r + 1)` is
    taken in unbounded arithmetic and the bound holds *unconditionally*
    — there is no overflow caveat at the `Nat` level (the Rust property
    test guards `(r+1)²` with `checked_mul` only because it executes in
    `u64`; mathematically the inequality holds whether or not the
    machine-arithmetic square fits).

    This is the "upper bound forces `r` to be the *greatest* such root"
    half of the contract — captured by the Rust property test
    `prop_sqrt_upper_bound` and by `sqrt_test`'s `i < x` assertion. It is
    independent from `sqrt_lower_bound`: returning `0` satisfies the lower
    bound but fails this one for any positive `x`. -/
theorem sqrt_upper_bound (x : u64) :
    ⦃ ⌜ True ⌝ ⦄
      sqrt_u64.sqrt x
    ⦃ ⇓ r => ⌜ x.toNat < (r.toNat + 1) * (r.toNat + 1) ⌝ ⦄ := by
  sorry

/-- Totality / no-panic: for every `u64` input, `sqrt` returns a value
    (it never fails). The Rust source documents the failure surface
    explicitly as empty ("Failures: none — the function never panics"),
    and the `prop_sqrt_*` proptests would themselves panic on any failed
    call before reaching the postcondition assertion, so this is its own
    contract clause. -/
theorem sqrt_no_failure (x : u64) :
    ∃ v : u64, sqrt_u64.sqrt x = RustM.ok v := by
  sorry

end Sqrt_u64Obligations
