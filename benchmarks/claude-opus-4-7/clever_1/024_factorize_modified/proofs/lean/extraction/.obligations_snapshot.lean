-- Companion obligations file for the `clever_024_factorize` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_024_factorize

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_024_factorizeObligations

/-! ## Helper definitions for the contract.

These are the mathematical counterparts of the Rust property tests.

* `factor_product v` is the (integer) product of the elements of the output
  vector. This is the spec-side analogue of the Rust test's
  `factors.iter().product()`.

* `is_prime_int p` is the standard mathematical primality predicate, stated
  over `Int` (the codomain of `Int64.toInt`). Pattern mirrors
  `is_prime_nat` from `clever_038_prime_fib_modified`. -/

/-- Integer product of the entries of the output `Vec`. -/
private def factor_product (v : alloc.vec.Vec i64 alloc.alloc.Global) : Int :=
  (v.val.toList.map (·.toInt)).foldr (· * ·) 1

/-- Mathematical primality on `Int`. -/
private def is_prime_int (p : Int) : Prop :=
  2 ≤ p ∧ ∀ k : Int, 2 ≤ k → k < p → ¬ k ∣ p

/-! ## Contract clauses

The Rust source contains four contract-style tests in `mod tests`:

  * `empty_for_n_le_one`            — failure/edge clause: `factorize` returns
                                      an empty `Vec` whenever `n ≤ 1`.
  * `product_of_factors_equals_n`   — postcondition 1: the product of the
                                      returned factors equals `n`.
  * `every_factor_is_prime`         — postcondition 2: every returned factor
                                      is prime.
  * `factors_non_decreasing`        — postcondition 3: factors are returned
                                      in non-decreasing order.

The reference `is_prime` helper in the Rust test module is *not* a contract
clause; it is the test oracle for clause 2, and is captured here as
`is_prime_int` on the spec side.

Note on the precondition for the three positive postconditions.

The proptest restricts `n ∈ [2, 1_000_000)`; the Lean model permits any
`i64`. For very large `n` close to `i64::MAX`, the trial-division loop
must reach `p ≈ ⌈√n⌉ + 1`, at which point `p *? p` overflows `i64`
(`i64::MAX ≈ 9.22·10^18` while `(⌈√(2^63)⌉ + 1)² ≈ 2^63 + 2^32 > i64::MAX`),
so the universal totality statement is false in the Lean model. The
strongest *true* common precondition is "`p² ≤ i64::MAX` for the maximum
`p` reached", which is implied by `n.toInt < 2^62`: then
`p ≤ ⌈√n⌉ + 1 ≤ 2^31 + 1`, so `p * p ≤ 2^62 + 2^32 + 1 < 2^63`. We use
this bound on the three positive clauses; it is strictly weaker than the
proptest's `n < 10^6` and matches the safety reasoning of
`is_prime_modified`'s `n.toNat < 2^32`. -/

/-- Failure/edge clause: for any `n ≤ 1`, `factorize n` returns an empty
    `Vec`. Captures the Rust property test `empty_for_n_le_one`. -/
theorem factorize_empty_for_n_le_one
    (n : i64) (h : n ≤ (1 : i64)) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_024_factorize.factorize n = RustM.ok v ∧ v.val.size = 0 := by
  sorry

/-- Postcondition 1 (product of factors equals `n`).

    Captures the Rust property test `product_of_factors_equals_n`. -/
theorem factorize_product_equals_n
    (n : i64) (h_lo : 2 ≤ n.toInt) (h_hi : n.toInt < 2 ^ 62) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_024_factorize.factorize n = RustM.ok v ∧
      factor_product v = n.toInt := by
  sorry

/-- Postcondition 2 (every returned factor is prime).

    Captures the Rust property test `every_factor_is_prime`. -/
theorem factorize_every_factor_is_prime
    (n : i64) (h_lo : 2 ≤ n.toInt) (h_hi : n.toInt < 2 ^ 62) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_024_factorize.factorize n = RustM.ok v ∧
      (∀ (k : Nat) (hk : k < v.val.size),
          is_prime_int (v.val[k]'hk).toInt) := by
  sorry

/-- Postcondition 3 (factors returned in non-decreasing order).

    Captures the Rust property test `factors_non_decreasing`. Stated on
    consecutive entries, matching the test's `windows(2)` form. -/
theorem factorize_factors_non_decreasing
    (n : i64) (h_lo : 2 ≤ n.toInt) (h_hi : n.toInt < 2 ^ 62) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_024_factorize.factorize n = RustM.ok v ∧
      (∀ (k : Nat) (hk : k + 1 < v.val.size),
          (v.val[k]'(Nat.lt_of_succ_lt hk)).toInt
            ≤ (v.val[k + 1]'hk).toInt) := by
  sorry

end Clever_024_factorizeObligations
