-- Companion obligations file for the `clever_002_truncate_number` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_002_truncate_number

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_002_truncate_numberObligations

/-- Closed-form postcondition: `truncate_number n` returns `n % 1000`.
    The static divisor `1000` is nonzero, so the partial operator `%?`
    never fires its `divisionByZero` branch. This foundational equational
    form is what the contract clauses below derive from. Not itself a
    Rust property test, but stated in the style preferred by the
    references (`gcd_while_postcondition`, `average_floor_postcondition`):
    when the precondition is trivially `True`, the equational form
    `f x = RustM.ok …` is easier to prove than a Hoare triple and gives
    one place from which the per-test clauses follow. -/
theorem truncate_number_postcondition (n : u64) :
    clever_002_truncate_number.truncate_number n = RustM.ok (n % 1000) := by
  unfold clever_002_truncate_number.truncate_number
  show (n %? (1000 : u64) : RustM u64) = RustM.ok (n % 1000)
  show (rust_primitives.ops.arith.Rem.rem n (1000 : u64) : RustM u64)
       = RustM.ok (n % 1000)
  show (if (1000 : u64) = 0 then (.fail .divisionByZero : RustM u64)
        else pure (n % 1000))
       = RustM.ok (n % 1000)
  rw [if_neg (by decide : (1000 : u64) ≠ 0)]
  rfl

/-- Totality / no-panic: for every `u64` input, `truncate_number n` returns
    a value successfully. The divisor `1000` is statically nonzero so the
    partial `%?` operator cannot fail. Mirrors the explicit
    "no failure mode" clause documented in the Rust source comment
    ("a single arithmetic expression"). -/
theorem truncate_number_total (n : u64) :
    ∃ r : u64, clever_002_truncate_number.truncate_number n = RustM.ok r :=
  ⟨n % 1000, truncate_number_postcondition n⟩

/-- Postcondition (bound): the returned fractional part is strictly less
    than `1000`. Captures the property test
    `result_is_strictly_less_than_one_thousand` — the "less than one
    whole unit" half of the fixed-point fractional-part contract. -/
theorem truncate_number_bound (n : u64) :
    ∃ r : u64, clever_002_truncate_number.truncate_number n = RustM.ok r
      ∧ r < (1000 : u64) := by
  refine ⟨n % 1000, truncate_number_postcondition n, ?_⟩
  -- Lift `<` to `toNat` and discharge via `Nat.mod_lt`.
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_mod,
      show ((1000 : u64).toNat = 1000) from rfl]
  exact Nat.mod_lt _ (by decide)

/-- Postcondition (congruence): the result `r` satisfies
    `(n / 1000) * 1000 + r = n`, i.e. integer-division reconstruction
    of `n` from quotient-and-remainder recovers the input. Captures the
    property test `result_reconstructs_input_with_integer_quotient` —
    the independent half of the contract that, together with the bound,
    uniquely pins down `n % 1000`. Phrased over `u64` arithmetic (which
    matches the Rust test): the intermediate `(n / 1000) * 1000` does
    not wrap because `(n.toNat / 1000) * 1000 ≤ n.toNat < 2^64`. -/
theorem truncate_number_reconstructs (n : u64) :
    ∃ r : u64, clever_002_truncate_number.truncate_number n = RustM.ok r
      ∧ (n / (1000 : u64)) * (1000 : u64) + r = n := by
  refine ⟨n % 1000, truncate_number_postcondition n, ?_⟩
  -- Set up the standard bridges: `n.toNat / 1000`, `n.toNat % 1000`, and
  -- the Euclidean identity `Nat.div_add_mod`.
  have h1000 : (1000 : u64).toNat = 1000 := rfl
  have h_div_toNat : (n / (1000 : u64)).toNat = n.toNat / 1000 := by
    rw [UInt64.toNat_div, h1000]
  have h_mod_toNat : (n % (1000 : u64)).toNat = n.toNat % 1000 := by
    rw [UInt64.toNat_mod, h1000]
  have h_mul_bound : (n / (1000 : u64)).toNat * (1000 : u64).toNat < 2 ^ 64 := by
    rw [h_div_toNat, h1000]
    have : n.toNat / 1000 * 1000 ≤ n.toNat := Nat.div_mul_le_self n.toNat 1000
    have := n.toNat_lt
    omega
  have h_mul_toNat :
      ((n / (1000 : u64)) * (1000 : u64)).toNat
        = (n.toNat / 1000) * 1000 := by
    rw [UInt64.toNat_mul_of_lt h_mul_bound, h_div_toNat, h1000]
  have h_add_bound :
      ((n / (1000 : u64)) * (1000 : u64)).toNat
        + (n % (1000 : u64)).toNat < 2 ^ 64 := by
    rw [h_mul_toNat, h_mod_toNat]
    have h := Nat.div_add_mod n.toNat 1000
    have := n.toNat_lt
    omega
  -- Lift the goal `(n/1000)*1000 + (n%1000) = n` through `toNat`.
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add_of_lt h_add_bound, h_mul_toNat, h_mod_toNat]
  -- Goal: n.toNat / 1000 * 1000 + n.toNat % 1000 = n.toNat
  have h := Nat.div_add_mod n.toNat 1000
  omega

end Clever_002_truncate_numberObligations
