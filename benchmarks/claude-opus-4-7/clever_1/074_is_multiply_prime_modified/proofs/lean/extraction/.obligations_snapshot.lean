-- Companion obligations file for the `clever_074_is_multiply_prime` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_074_is_multiply_prime

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_074_is_multiply_primeObligations

/-! ## Spec-side oracles

The Rust source's `naive` oracle counts prime factors with multiplicity.
We mirror it at the `Nat` level as the existence of three primes whose
product is `n`. By unique factorization on `Nat`, this is equivalent to
"`n` has exactly three prime factors counted with multiplicity", which
is what the Rust `naive` oracle computes. -/

/-- Mathematical primality on `Nat`. Mirrors `is_prime_nat` in
    `clever_038_prime_fib_modified` and `is_prime_int` in
    `clever_024_factorize_modified`. -/
private def is_prime_nat (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ k : Nat, 2 ≤ k → k < p → ¬ k ∣ p

/-- `n` is the product of exactly three primes (counted with multiplicity). -/
private def is_multiply_prime_nat (n : Nat) : Prop :=
  ∃ p q r : Nat, is_prime_nat p ∧ is_prime_nat q ∧ is_prime_nat r
    ∧ p * q * r = n

/-! ## Concrete unit pins (from the `small_cases` test)

The Rust `small_cases` test asserts 11 specific input/output pairs. We
list each as an individual unit-pin theorem. Each can be discharged by
`native_decide` since `smallest_prime_at` (although declared
`partial_fixpoint`) is computable for concrete `u64` inputs — same
trick as `prime_fib_at_*` in `clever_038_prime_fib_modified`. -/

theorem small_cases_8 :
    clever_074_is_multiply_prime.is_multiply_prime (8 : u64) = RustM.ok true := by
  native_decide

theorem small_cases_12 :
    clever_074_is_multiply_prime.is_multiply_prime (12 : u64) = RustM.ok true := by
  native_decide

theorem small_cases_27 :
    clever_074_is_multiply_prime.is_multiply_prime (27 : u64) = RustM.ok true := by
  native_decide

theorem small_cases_30 :
    clever_074_is_multiply_prime.is_multiply_prime (30 : u64) = RustM.ok true := by
  native_decide

theorem small_cases_105 :
    clever_074_is_multiply_prime.is_multiply_prime (105 : u64) = RustM.ok true := by
  native_decide

theorem small_cases_1 :
    clever_074_is_multiply_prime.is_multiply_prime (1 : u64) = RustM.ok false := by
  native_decide

theorem small_cases_2 :
    clever_074_is_multiply_prime.is_multiply_prime (2 : u64) = RustM.ok false := by
  native_decide

theorem small_cases_4 :
    clever_074_is_multiply_prime.is_multiply_prime (4 : u64) = RustM.ok false := by
  native_decide

theorem small_cases_6 :
    clever_074_is_multiply_prime.is_multiply_prime (6 : u64) = RustM.ok false := by
  native_decide

theorem small_cases_7 :
    clever_074_is_multiply_prime.is_multiply_prime (7 : u64) = RustM.ok false := by
  native_decide

theorem small_cases_24 :
    clever_074_is_multiply_prime.is_multiply_prime (24 : u64) = RustM.ok false := by
  native_decide

/-! ## Universal contract clauses

Note on the precondition `a.toNat < 2 ^ 32` used in the postcondition
theorems below. The proptest restricts `a ∈ [1, 2^18]`; the Lean model
permits any `u64`. For very large `a` with no small prime factors,
`smallest_prime_at` iterates `d` up to `⌈√a⌉`, and at the exit check
`d *? d` would overflow once `d ≥ 2^32`. Adding `a.toNat < 2 ^ 32`
bounds `⌈√a⌉ < 2^16`, so `d * d < 2^33 < 2^64` and no overflow occurs.
This matches the safety reasoning of `clever_058_largest_prime_factor`
and `clever_030_is_prime`, and is strictly weaker than the proptest's
`a ≤ 2^18`. -/

/-- Failure / edge clause (from the `below_8_is_false` proptest):
    for every `a` with `a.toNat < 8`, the function returns `false`.
    Captured directly from the leading `a <? 8` short-circuit. -/
theorem is_multiply_prime_below_8 (a : u64) (h : a.toNat < 8) :
    clever_074_is_multiply_prime.is_multiply_prime a = RustM.ok false := by
  sorry

/-- Postcondition — soundness direction of the `matches_oracle`
    proptest: whenever the function accepts `a`, `a` is the product of
    three primes (counted with multiplicity).

    Stated without a numeric precondition: the hypothesis
    `is_multiply_prime a = RustM.ok true` already certifies that the
    underlying computation terminated successfully on this particular
    `a`, so no `a.toNat < 2^32` bound is needed. -/
theorem is_multiply_prime_sound (a : u64)
    (h : clever_074_is_multiply_prime.is_multiply_prime a = RustM.ok true) :
    is_multiply_prime_nat a.toNat := by
  sorry

/-- Postcondition — completeness direction of the `matches_oracle`
    proptest: every product of three primes within the safe arithmetic
    range is accepted by the function. -/
theorem is_multiply_prime_complete (a : u64) (h_fit : a.toNat < 2 ^ 32)
    (h_spec : is_multiply_prime_nat a.toNat) :
    clever_074_is_multiply_prime.is_multiply_prime a = RustM.ok true := by
  sorry

/-- Postcondition (from the `accepts_product_of_three_primes` proptest):
    the product of any three primes (within the safe arithmetic range)
    is accepted by the function. The shape-specific specialisation of
    `is_multiply_prime_complete`; included separately because it pins
    down the concrete "three primes" input shape used in the test. -/
theorem is_multiply_prime_accepts_product_of_three_primes
    (p q r : u64)
    (hp : is_prime_nat p.toNat) (hq : is_prime_nat q.toNat)
    (hr : is_prime_nat r.toNat)
    (h_fit : p.toNat * q.toNat * r.toNat < 2 ^ 32) :
    clever_074_is_multiply_prime.is_multiply_prime (p * q * r) = RustM.ok true := by
  sorry

/-- Postcondition (from the `rejects_semiprime` proptest):
    the product of any two primes (within the safe arithmetic range) is
    rejected by the function. Pins down the "exactly three" cardinality
    against the off-by-one error of accepting any product of primes. -/
theorem is_multiply_prime_rejects_semiprime
    (p q : u64)
    (hp : is_prime_nat p.toNat) (hq : is_prime_nat q.toNat)
    (h_fit : p.toNat * q.toNat < 2 ^ 32) :
    clever_074_is_multiply_prime.is_multiply_prime (p * q) = RustM.ok false := by
  sorry

end Clever_074_is_multiply_primeObligations
