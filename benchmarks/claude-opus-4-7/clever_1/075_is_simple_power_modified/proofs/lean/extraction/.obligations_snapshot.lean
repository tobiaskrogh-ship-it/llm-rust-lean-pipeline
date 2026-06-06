-- Companion obligations file for the `clever_075_is_simple_power` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_075_is_simple_power

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_075_is_simple_powerObligations

/-! ## Contract clauses derived from the Rust property tests.

The Rust source contains the following property-style tests; each becomes
one (or two) independent `theorem` below.

  * `matches_oracle`               — main bidirectional spec against a
    naive reference.  Captured by `is_simple_power_sound` together with
    `is_simple_power_actual_powers_recognized` (forward at the powers)
    and `is_simple_power_between_powers_not_recognized` (negative
    direction strictly between powers).
  * `one_is_always_simple_power`   — `x = 1`  → `true` for any `n`.
  * `zero_is_never_simple_power`   — `x = 0`  → `false` for any `n`.
  * `base_one_simple_power_iff_x_is_one`  — `n = 1` → `(x = 1)`.
  * `base_zero_simple_power_iff_x_is_one` — `n = 0` → `(x = 1)`.
  * `actual_powers_recognized`            — `n ≥ 2 ∧ n^k = x` → `true`.
  * `between_powers_not_recognized`       — `n ≥ 2 ∧ n^k < x < n^(k+1)`
    → `false` (with `n^(k+1) < 2^64` to rule out overflow).

### Feasibility notes

The body of `power_walks_to` repeatedly applies `cur ↦ cur *? n`, which
fails on `u64` overflow.  Three observations:

  1. The positive direction `actual_powers_recognized` is universally
     feasible: if `n.toNat ^ k = x.toNat`, then for every intermediate
     value `cur = n^i` with `i ≤ k` we have `n^i ≤ x < 2^64`, so the
     multiplicative chain never overflows.  No extra precondition
     beyond `n ≥ 2` is needed.
  2. The negative direction `between_powers_not_recognized` is *not*
     universal: when `n^(k+1) ≥ 2^64`, the recursion's last
     multiplication overflows and the function returns `.fail`, not
     `.ok false`.  We add the precondition `n^(k+1) < 2^64`, matching
     the proptest's `prop_assume!(hi ≤ u64::MAX as u128)`.
  3. Soundness (`ok true → ∃ k, n^k = x`) needs no precondition: if the
     function returns successfully with `true`, the chain of `cur`
     values witnesses the exponent. -/

/-- `x = 1` is a simple power of any `n` (via the `n^0 = 1` convention).
    Captures the proptest `one_is_always_simple_power`. -/
theorem is_simple_power_one (n : u64) :
    clever_075_is_simple_power.is_simple_power 1 n = RustM.ok true := by
  sorry

/-- `0` is never a simple power of any `n`.  Captures the proptest
    `zero_is_never_simple_power`. -/
theorem is_simple_power_zero (n : u64) :
    clever_075_is_simple_power.is_simple_power 0 n = RustM.ok false := by
  sorry

/-- Base `n = 1`: only `x = 1` qualifies (since `1^k = 1` for all `k`).
    Together with `is_simple_power_one` this captures the proptest
    `base_one_simple_power_iff_x_is_one`. -/
theorem is_simple_power_base_one_ne (x : u64) (h : x ≠ 1) :
    clever_075_is_simple_power.is_simple_power x 1 = RustM.ok false := by
  sorry

/-- Base `n = 0`: only `x = 1` qualifies (via the `0^0 = 1` convention).
    Together with `is_simple_power_one` this captures the proptest
    `base_zero_simple_power_iff_x_is_one`. -/
theorem is_simple_power_base_zero_ne (x : u64) (h : x ≠ 1) :
    clever_075_is_simple_power.is_simple_power x 0 = RustM.ok false := by
  sorry

/-- Soundness half of `matches_oracle`: if the function returns `true`,
    there is some `k : Nat` with `n^k = x` at the `Nat` level.  No
    precondition: a successful `ok true` already constrains the trace
    of `cur` values to expose the witness. -/
theorem is_simple_power_sound (x n : u64)
    (h : clever_075_is_simple_power.is_simple_power x n = RustM.ok true) :
    ∃ k : Nat, n.toNat ^ k = x.toNat := by
  sorry

/-- Positive direction: every actual power `n^k` is recognized for
    `n ≥ 2`.  Captures the proptest `actual_powers_recognized` and
    also serves as the completeness half of `matches_oracle` in the
    principal case (the `n = 0, 1` cases are covered by the dedicated
    edge clauses).  Universal: `n^i ≤ n^k = x < 2^64` rules out
    overflow during the chain. -/
theorem is_simple_power_actual_powers_recognized (x n : u64) (k : Nat)
    (h_n : 2 ≤ n.toNat) (h_eq : n.toNat ^ k = x.toNat) :
    clever_075_is_simple_power.is_simple_power x n = RustM.ok true := by
  sorry

/-- Negative direction: a value strictly between consecutive powers
    `n^k` and `n^(k+1)` is not a simple power of `n`.  The
    precondition `n^(k+1) < 2^64` mirrors the proptest's
    `prop_assume!(hi ≤ u64::MAX as u128)` and rules out the genuine
    overflow case the natural universal statement omits.  Captures the
    proptest `between_powers_not_recognized`. -/
theorem is_simple_power_between_powers_not_recognized (x n : u64) (k : Nat)
    (h_n : 2 ≤ n.toNat)
    (h_lo : n.toNat ^ k < x.toNat)
    (h_hi : x.toNat < n.toNat ^ (k + 1))
    (h_fit : n.toNat ^ (k + 1) < 2 ^ 64) :
    clever_075_is_simple_power.is_simple_power x n = RustM.ok false := by
  sorry

/-! ## Unit pins from the `small_cases` test.

These are sanity pins on specific values.  They are derivable from the
universal clauses above, but pinning them as separate theorems guards
against regressions on the specific examples listed in the Rust
`small_cases` test. -/

/-- `is_simple_power(8, 2) = true` (since `2³ = 8`). -/
theorem is_simple_power_8_2 :
    clever_075_is_simple_power.is_simple_power 8 2 = RustM.ok true := by
  sorry

/-- `is_simple_power(81, 3) = true` (since `3⁴ = 81`). -/
theorem is_simple_power_81_3 :
    clever_075_is_simple_power.is_simple_power 81 3 = RustM.ok true := by
  sorry

/-- `is_simple_power(3, 2) = false`. -/
theorem is_simple_power_3_2 :
    clever_075_is_simple_power.is_simple_power 3 2 = RustM.ok false := by
  sorry

/-- `is_simple_power(7, 4) = false`. -/
theorem is_simple_power_7_4 :
    clever_075_is_simple_power.is_simple_power 7 4 = RustM.ok false := by
  sorry

end Clever_075_is_simple_powerObligations
