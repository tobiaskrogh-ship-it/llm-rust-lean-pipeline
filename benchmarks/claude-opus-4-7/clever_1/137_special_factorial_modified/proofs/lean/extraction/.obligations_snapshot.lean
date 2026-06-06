-- Companion obligations file for the `clever_137_special_factorial` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_137_special_factorial

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_137_special_factorialObligations

/-! ## Specification helpers -/

/-- Mathematical factorial on `Nat`, defined locally because core Lean 4
    does not ship a `Nat.factorial` and we have no Mathlib in this build. -/
private def factorial_nat : Nat → Nat
  | 0     => 1
  | k + 1 => (k + 1) * factorial_nat k

/-- Brazilian (`special`) factorial on `Nat`: the running product
    `1! * 2! * ... * n!` with the empty-product convention
    `special_factorial_nat 0 = 1`. Mirrors the Rust test oracle
    `special_factorial_ref`. -/
private def special_factorial_nat : Nat → Nat
  | 0     => 1
  | n + 1 => special_factorial_nat n * factorial_nat (n + 1)

/-! ## Contract clauses

The Rust source contains two `proptest`-style contract tests:

  * `base_case_zero`               — `special_factorial(0) = 1`.
                                     Independent defining convention.
  * `matches_product_of_factorials` — postcondition: for `n ≤ 8`,
                                     `special_factorial(n) = ∏_{k=1}^{n} k!`.

The unit `known` test (values for `n ∈ {0,1,2,3,4}`) is fully subsumed by
`matches_product_of_factorials` and is not restated here.

### Feasibility note

The proptest caps `n` at `8` because the running product overflows at `n = 9`:

  sf(0) = 1                  sf(5) = 34_560
  sf(1) = 1                  sf(6) = 24_883_200
  sf(2) = 2                  sf(7) = 125_411_328_000
  sf(3) = 12                 sf(8) = 5_056_584_744_960_000   (< 2^64)
  sf(4) = 288                sf(9) ≈ 1.83·10^21              (> 2^64)

So we state the universal postcondition with the strongest honest precondition
`n.toNat ≤ 8` (matching the proptest exactly, since the boundary coincides
with the model's overflow boundary).  We also add a matching failure-side
theorem for `n.toNat ≥ 9`, pinning the contract boundary — this is not
itself a proptest but the docstring announces it, and the reference set
(`factorial_overflow`, `f_fails_above_21`) states the analogous theorem. -/

/-- Defining convention (independent base case):
    `special_factorial(0)` returns `1`. -/
theorem special_factorial_zero :
    clever_137_special_factorial.special_factorial 0 = RustM.ok 1 := by
  sorry

/-- Main postcondition.  For every `n` in the overflow-free range
    `n.toNat ≤ 8`, `special_factorial(n)` equals the Brazilian factorial
    `1! * 2! * ... * n!`.  Captures the proptest
    `matches_product_of_factorials`. -/
theorem special_factorial_matches_product (n : u64) (hn : n.toNat ≤ 8) :
    clever_137_special_factorial.special_factorial n
      = RustM.ok (UInt64.ofNat (special_factorial_nat n.toNat)) := by
  sorry

/-- Failure boundary.  For every `n` with `n.toNat ≥ 9`, the iteration
    inside `build_at` reaches the multiplication that yields `sf(9)`,
    which exceeds `u64::MAX`, so the wrapped function fails with
    `integerOverflow`.  Not directly asserted by a proptest, but pins the
    boundary of the precondition above and matches the
    `factorial_overflow` shape from the reference set. -/
theorem special_factorial_overflow (n : u64) (h : 9 ≤ n.toNat) :
    clever_137_special_factorial.special_factorial n
      = RustM.fail .integerOverflow := by
  sorry

end Clever_137_special_factorialObligations
