-- Companion obligations file for the `clever_148_x_or_y` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_148_x_or_y

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_148_x_or_yObligations

/-! ## Spec-side primality oracle

Mathematical primality on `Int`. Mirrors `is_prime_int` from
`clever_024_factorize_modified`: the standard "≥ 2 ∧ no proper
divisor" definition. The codomain is `Int` because `Int64.toInt`
returns `Int`. -/

/-- Mathematical primality on `Int`. -/
private def is_prime_int (p : Int) : Prop :=
  2 ≤ p ∧ ∀ k : Int, 2 ≤ k → k < p → ¬ k ∣ p

/-! ## Contract clauses

The Rust source contains three contract-style tests in `mod tests`:

  * `n_below_two_returns_y`         — edge clause: for `n < 2`, `x_or_y`
                                      returns `y`.  Pins the `n < 2`
                                      short-circuit in `is_prime`, which
                                      the property tests below also exercise
                                      but via a different code path.
  * `returns_x_when_n_is_prime`     — postcondition 1: when `n` is prime,
                                      `x_or_y` returns `x`.
  * `returns_y_when_n_is_not_prime` — postcondition 2: when `n` is not
                                      prime (including `n < 2`), `x_or_y`
                                      returns `y`.

The `known` test is a derived sanity pin over the same postconditions on
small concrete inputs (7, 15, 2, 1); not a separate clause.

The `ref_is_prime` helper in the Rust test module is *not* a contract
clause; it is the test oracle for the primality predicate, mirrored on
the spec side as `is_prime_int`.

Note on the precondition `n.toInt < 2 ^ 62` for the two positive
postconditions.

The proptest restricts `n ∈ [-100, 5_000]`; the Lean model permits any
`i64`. For very large `n` close to `i64::MAX`, the trial-division loop
reaches `d ≈ ⌈√n⌉ + 1`, at which point `d *? d` overflows `i64`
(`i64::MAX ≈ 9.22·10^18` while `(⌈√(2^63)⌉ + 1)² > i64::MAX`), so the
universal totality statement is false in the Lean model. Mirroring
`clever_024_factorize_modified`, the strongest *true* common bound is
"`d² ≤ i64::MAX` for the maximum `d` reached", which is implied by
`n.toInt < 2^62`: then `d ≤ ⌈√n⌉ + 1 ≤ 2^31 + 1`, so
`d * d ≤ 2^62 + 2^32 + 1 < 2^63`. This is strictly weaker than the
proptest's `n ≤ 5_000` and matches the safety reasoning of
`factorize_modified` / `is_prime_modified`.

The `n < 2` edge clause needs no such bound — the `n < 2` branch of
`is_prime` short-circuits to `pure false` before any arithmetic occurs,
so no overflow is possible. -/

/-- Edge clause: for any `n < 2` (including all negative inputs), `x_or_y`
    returns `y`. Captures the unit test `n_below_two_returns_y` and the
    `n < 2` slice of the `returns_y_when_n_is_not_prime` proptest. -/
theorem x_or_y_below_two
    (n x y : i64) (h : n.toInt < 2) :
    clever_148_x_or_y.x_or_y n x y = RustM.ok y := by
  sorry

/-- Postcondition 1 (prime case): when `n` is mathematically prime (and the
    overflow-safety bound `n.toInt < 2 ^ 62` holds), `x_or_y n x y` returns
    `x`. Captures the proptest `returns_x_when_n_is_prime`. -/
theorem x_or_y_returns_x_when_prime
    (n x y : i64)
    (h_lo : 2 ≤ n.toInt) (h_hi : n.toInt < 2 ^ 62)
    (h_prime : is_prime_int n.toInt) :
    clever_148_x_or_y.x_or_y n x y = RustM.ok x := by
  sorry

/-- Postcondition 2 (non-prime case, `n ≥ 2`): when `n ≥ 2` is not
    mathematically prime (and the overflow-safety bound `n.toInt < 2 ^ 62`
    holds), `x_or_y n x y` returns `y`. Together with `x_or_y_below_two`,
    this captures the full `returns_y_when_n_is_not_prime` proptest. -/
theorem x_or_y_returns_y_when_not_prime
    (n x y : i64)
    (h_lo : 2 ≤ n.toInt) (h_hi : n.toInt < 2 ^ 62)
    (h_not_prime : ¬ is_prime_int n.toInt) :
    clever_148_x_or_y.x_or_y n x y = RustM.ok y := by
  sorry

end Clever_148_x_or_yObligations
