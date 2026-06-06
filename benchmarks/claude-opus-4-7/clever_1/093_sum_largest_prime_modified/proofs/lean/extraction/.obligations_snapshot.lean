-- Companion obligations file for the `clever_093_sum_largest_prime` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_093_sum_largest_prime

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_093_sum_largest_primeObligations

/-! ## Spec-side oracle definitions

`is_prime_nat` is the standard mathematical primality predicate on `Nat`,
matching the convention used in `clever_030_is_prime` and
`clever_058_largest_prime_factor`.

`digit_sum_nat` is the recursive sum-of-decimal-digits function on `Nat`,
mirroring the iterative `digit_sum_ref` in the Rust source. It is total on
`Nat` via the `n / 10` strict-decrease termination measure (the same shape
used in `clever_035_fizz_buzz`'s `count_sevens_nat`). -/

/-- Mathematical primality on `Nat`. -/
private def is_prime_nat (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ k : Nat, 2 ≤ k → k < p → ¬ k ∣ p

/-- Sum of decimal digits of `n`. -/
private def digit_sum_nat (n : Nat) : Nat :=
  if h : 0 < n then n % 10 + digit_sum_nat (n / 10)
  else 0
termination_by n
decreasing_by exact Nat.div_lt_self h (by decide)

/-! ## Contract clauses

The Rust source contains the following contract-style tests in `mod tests`:
  * unit assertions in `known` (specific input pins),
  * the proptest `prop_no_primes_is_zero` — when no element is prime, the
    result is `0`,
  * the proptest `prop_digit_sum_of_max_prime` — when at least one element
    is prime, the result equals the decimal digit sum of the *largest*
    prime in the list.

The Rust comment on `prop_digit_sum_of_max_prime` notes that the property
"captures three independent facts at once":
   * the value comes from an element actually present in `xs`,
   * that element is prime,
   * no other prime in `xs` is greater.
These are treated jointly as the precondition on the parameter `p` of the
main equational theorem below (matching the test's single assertion).

### Feasibility / precondition rationale

The proptest restricts elements to `0..1_000u64`. The model-level concern
is that `is_prime_at` may overflow on huge inputs: for `n ≥ 2^32`, the
trial-divisor `d` can reach `2^32`, at which point `d *? d` overflows
before the `d * d > n` exit fires. This is the same feasibility constraint
recorded in `clever_030_is_prime` and `clever_058_largest_prime_factor`
(both use `n.toNat < 2 ^ 32`). We add the analogous precondition
`∀ i, l[i].toNat < 2 ^ 32` to the theorems whose proofs depend on
evaluating `is_prime` on the slice elements. The empty-slice theorem
needs no such bound because `is_prime` is never invoked. -/

/-- Boundary clause (covers the empty case of `prop_no_primes_is_zero`
    and the unit `sum_largest_prime(&[]) = 0`): on an empty slice the
    function returns the sentinel `0`. -/
theorem sum_largest_prime_empty
    (lst : RustSlice u64) (hempty : lst.val.size = 0) :
    clever_093_sum_largest_prime.sum_largest_prime lst = RustM.ok (0 : u64) := by
  sorry

/-- "No primes ⇒ result 0" (proptest `prop_no_primes_is_zero`): if no
    element of `lst` is prime, the function returns the sentinel `0`. The
    `h_bound` precondition ensures `is_prime` evaluates without overflow
    on every element. -/
theorem sum_largest_prime_no_primes_zero
    (lst : RustSlice u64)
    (h_bound : ∀ (i : Nat) (hi : i < lst.val.size), (lst.val[i]'hi).toNat < 2 ^ 32)
    (h_no_primes : ∀ (i : Nat) (hi : i < lst.val.size),
        ¬ is_prime_nat (lst.val[i]'hi).toNat) :
    clever_093_sum_largest_prime.sum_largest_prime lst = RustM.ok (0 : u64) := by
  sorry

/-- Main functional clause (proptest `prop_digit_sum_of_max_prime`): when
    `p` is the maximum prime element of `lst` (parametric in the three
    independent facts: membership, primality, maximality), the function
    succeeds and returns the decimal digit sum of `p`. -/
theorem sum_largest_prime_eq_digit_sum_of_max_prime
    (lst : RustSlice u64) (p : u64)
    (h_bound : ∀ (i : Nat) (hi : i < lst.val.size), (lst.val[i]'hi).toNat < 2 ^ 32)
    (h_p_in : ∃ (i : Nat) (hi : i < lst.val.size), (lst.val[i]'hi) = p)
    (h_p_prime : is_prime_nat p.toNat)
    (h_p_max : ∀ (i : Nat) (hi : i < lst.val.size),
        is_prime_nat (lst.val[i]'hi).toNat → (lst.val[i]'hi).toNat ≤ p.toNat) :
    ∃ r : u64,
      clever_093_sum_largest_prime.sum_largest_prime lst = RustM.ok r
      ∧ r.toNat = digit_sum_nat p.toNat := by
  sorry

end Clever_093_sum_largest_primeObligations
