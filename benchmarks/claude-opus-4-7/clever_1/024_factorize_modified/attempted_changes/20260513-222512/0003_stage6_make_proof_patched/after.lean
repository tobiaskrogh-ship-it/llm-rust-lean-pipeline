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

/-! ## Spec-level predicates

`IsPrime` and `array_product_int` give us pure-`Int` oracles to phrase the
post-conditions without leaking machine-int overflow concerns into the spec.
Each factor returned by `factorize` is positive (and ≥ 2 because the
algorithm only ever appends primes `p ≥ 2` or a residual `n > 1`), so the
`Int`-level statements line up with the Rust tests. -/

/-- An integer is prime iff it is at least 2 and has no proper divisor
    strictly between 1 and itself. -/
private def IsPrime (x : Int) : Prop :=
  2 ≤ x ∧ ∀ m : Int, 2 ≤ m → m < x → ¬ m ∣ x

/-- Product of an `i64` array, taken in `Int` to avoid overflow concerns.
    Matches the Rust test's `factors.iter().product()` semantically when the
    true product fits in `i64` (it does for the proptest's `n ∈ 2..10^6`). -/
private def array_product_int (a : Array i64) : Int :=
  a.foldl (fun acc x => acc * x.toInt) 1

/-! ## Contract clauses

Four independent obligations, one per property test in the Rust source:

  * `empty_for_n_le_one`        — failure / edge case: `n ≤ 1` ⇒ empty Vec
  * `product_of_factors_equals_n` — post (1/3): ∏ factors = n
  * `every_factor_is_prime`       — post (2/3): each factor is prime
  * `factors_non_decreasing`      — post (3/3): factors sorted ascending

For the three post-conditions we adopt the conservative valid-regime
`2 ≤ n` precondition (matching the Rust proptest's `n ∈ 2..10^6`). The
proof stage may need a tighter bound (e.g. `n.toInt < 2^62`) to discharge
the `p *? p` overflow obligation; if so it can strengthen the hypothesis
there. The statements remain well-typed and capture the contract. -/

/-- Edge case (proptest `empty_for_n_le_one`): for any `n ≤ 1` the function
    returns successfully with an empty `Vec`. -/
theorem empty_for_n_le_one
    (n : i64) (h : n ≤ (1 : i64)) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_024_factorize.factorize n = RustM.ok v ∧ v.val.size = 0 := by
  unfold clever_024_factorize.factorize
  have h_dec : decide (n ≤ (1 : i64)) = true := decide_eq_true h
  simp only [show (n <=? (1 : i64)) =
               (pure (decide (n ≤ (1 : i64))) : RustM Bool) from rfl,
             h_dec, pure_bind, ↓reduceIte]
  exact ⟨⟨(List.nil : List i64).toArray, by grind⟩, rfl, rfl⟩

/-- Postcondition (1/3) — product (proptest `product_of_factors_equals_n`):
    the product of the returned factors equals `n`. -/
theorem product_of_factors_equals_n
    (n : i64) (h : (2 : i64) ≤ n) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_024_factorize.factorize n = RustM.ok v ∧
      array_product_int v.val = n.toInt := by
  sorry

/-- Postcondition (2/3) — primality (proptest `every_factor_is_prime`):
    every element of the returned `Vec` is prime. -/
theorem every_factor_is_prime
    (n : i64) (h : (2 : i64) ≤ n) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_024_factorize.factorize n = RustM.ok v ∧
      ∀ (j : Nat) (hj : j < v.val.size), IsPrime ((v.val[j]'hj).toInt) := by
  sorry

/-- Postcondition (3/3) — ordering (proptest `factors_non_decreasing`):
    consecutive elements are in non-decreasing order. -/
theorem factors_non_decreasing
    (n : i64) (h : (2 : i64) ≤ n) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_024_factorize.factorize n = RustM.ok v ∧
      ∀ (j : Nat) (h₁ : j < v.val.size) (h₂ : j + 1 < v.val.size),
        (v.val[j]'h₁).toInt ≤ (v.val[j+1]'h₂).toInt := by
  sorry

end Clever_024_factorizeObligations
