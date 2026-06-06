-- Companion obligations file for the `clever_058_largest_prime_factor` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_058_largest_prime_factor

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_058_largest_prime_factorObligations

/-! ## Spec-side primality oracle

Mathematical primality on `Nat`. Mirrors `is_prime_nat` in
`clever_038_prime_fib_modified` and `is_prime_int` in
`clever_024_factorize_modified`: the standard "≥ 2 ∧ no proper
divisor" definition, independent of the Rust implementation under
verification. Used by the primality and maximality clauses. -/

/-- Mathematical primality on `Nat`. -/
private def is_prime_nat (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ k : Nat, 2 ≤ k → k < p → ¬ k ∣ p

/-! ## Contract clauses

The Rust source contains four contract-style tests in `mod tests`:

  * `degenerate_n_le_one`        — failure/edge clause: `n ≤ 1` returns
                                   the sentinel `1`.
  * `result_divides_n`           — postcondition 1: the returned value
                                   divides `n` (for `n > 1`).
  * `result_is_prime`            — postcondition 2: the returned value
                                   is itself a prime (for `n > 1`).
  * `no_larger_prime_divides_n`  — postcondition 3: no prime strictly
                                   greater than the returned value
                                   divides `n` (for `n > 1`).

The `is_prime_oracle` helper in the Rust test module is *not* a
contract clause; it is the test oracle for clauses 2 and 3, and is
captured here as `is_prime_nat` on the spec side.

Note on the precondition for the three positive postconditions.

The proptest restricts the divides/primality clauses to `n ∈ [2, 2^18]`
and the maximality clause to `n ∈ [2, 2000]`; the Lean model permits
any `u64` (i.e. `n.toNat < 2^64`).

For very large `n` close to `u64::MAX`, the trial-division loop inside
`smallest_divisor_at` must reach `d ≈ ⌈√n⌉ + 1`. Once `d` exceeds
`2^32`, `d *? d` overflows `u64` and the function fails — so the
universal totality statement is false in the Lean model.

The strongest *true* common precondition that mirrors
`is_prime_modified` (the closest structural reference; same
`smallest_divisor_at`-style helper) is `n.toNat < 2^32`. Then
`⌈√n⌉ ≤ 2^16`, so the loop iterates with `d ≤ 2^16 + 1` and
`d *? d ≤ 2^32 + …`, well under `2^64`. We use this bound on the
three positive clauses; it is strictly weaker than the proptest's
`n ≤ 2^18` divides/primality range and the `n ≤ 2000` maximality
range, but matches the safety reasoning of the closest reference and
keeps the proof surface uniform across clauses. -/

/-- Failure/edge clause: for any `n ≤ 1`, `largest_prime_factor n`
    returns the sentinel value `1`.

    Captures the Rust property test `degenerate_n_le_one`. -/
theorem largest_prime_factor_degenerate
    (n : u64) (h : n.toNat ≤ 1) :
    clever_058_largest_prime_factor.largest_prime_factor n = RustM.ok (1 : u64) := by
  sorry

/-- Postcondition 1 (divisibility): for `n > 1`, the returned value
    divides `n`.

    Captures the Rust property test `result_divides_n`. -/
theorem largest_prime_factor_divides_n
    (n : u64) (h_lo : 2 ≤ n.toNat) (h_hi : n.toNat < 2 ^ 32) :
    ∃ p : u64,
      clever_058_largest_prime_factor.largest_prime_factor n = RustM.ok p
      ∧ p.toNat ∣ n.toNat := by
  sorry

/-- Postcondition 2 (primality): for `n > 1`, the returned value is
    itself a prime number.

    Captures the Rust property test `result_is_prime`. -/
theorem largest_prime_factor_is_prime
    (n : u64) (h_lo : 2 ≤ n.toNat) (h_hi : n.toNat < 2 ^ 32) :
    ∃ p : u64,
      clever_058_largest_prime_factor.largest_prime_factor n = RustM.ok p
      ∧ is_prime_nat p.toNat := by
  sorry

/-- Postcondition 3 (maximality): for `n > 1`, no prime strictly
    greater than the returned value divides `n`.

    Captures the Rust property test `no_larger_prime_divides_n`. -/
theorem largest_prime_factor_is_maximal
    (n : u64) (h_lo : 2 ≤ n.toNat) (h_hi : n.toNat < 2 ^ 32) :
    ∃ p : u64,
      clever_058_largest_prime_factor.largest_prime_factor n = RustM.ok p
      ∧ ∀ q : Nat, p.toNat < q → is_prime_nat q → ¬ q ∣ n.toNat := by
  sorry

end Clever_058_largest_prime_factorObligations
