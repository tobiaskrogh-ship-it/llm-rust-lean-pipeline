-- Companion obligations file for the `clever_136_is_equal_to_sum_even` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_136_is_equal_to_sum_even

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_136_is_equal_to_sum_evenObligations

open clever_136_is_equal_to_sum_even

/-- Closed-form postcondition: `is_equal_to_sum_even n` returns the Boolean
    `(n >= 8) && (n % 2 == 0)`. The static divisor `2` is nonzero so `%?`
    never fires its `divisionByZero` branch, and the comparisons / `&&?`
    are pure. This foundational equational form is the source from which
    the per-test contract clauses below derive. Not itself a Rust
    property test, but stated in the style preferred by the reference
    examples (`truncate_number_postcondition`, `is_zero_spec`): when the
    precondition is trivially `True`, the equational form
    `f n = RustM.ok …` is easier to prove than a Hoare triple. -/
theorem is_equal_to_sum_even_postcondition (n : u64) :
    is_equal_to_sum_even n = RustM.ok (decide ((8 : u64) ≤ n) && (n % 2 == 0)) := by
  unfold is_equal_to_sum_even
  show (do
    let a ← (pure (decide ((8 : u64) ≤ n)) : RustM Bool)
    let b ← (do
      let c ← (if (2 : u64) = 0 then (.fail .divisionByZero : RustM u64) else pure (n % 2))
      (pure (c == (0 : u64)) : RustM Bool))
    (pure (a && b) : RustM Bool))
    = RustM.ok (decide ((8 : u64) ≤ n) && (n % 2 == 0))
  rw [if_neg (by decide : ¬ ((2 : u64) = 0))]
  rfl

/-- Totality / no-panic: for every `u64` input, `is_equal_to_sum_even n`
    returns a value successfully. The only partial operation on the path
    is `n %? 2`, and the divisor `2` is statically nonzero so the
    `divisionByZero` branch is unreachable. Mirrors the implicit
    "no failure mode" surface of a closed-form Boolean predicate. -/
theorem is_equal_to_sum_even_total (n : u64) :
    ∃ r : Bool, is_equal_to_sum_even n = RustM.ok r :=
  ⟨decide ((8 : u64) ≤ n) && (n % 2 == 0), is_equal_to_sum_even_postcondition n⟩

/-- Postcondition (semantic soundness on the valid domain, first half of
    `accepts_even_at_least_8_with_witness`): for every even `n ≥ 8` the
    function returns `true`. -/
theorem is_equal_to_sum_even_accepts_even_at_least_8
    (n : u64) (hge : (8 : u64) ≤ n) (heven : n % 2 = 0) :
    is_equal_to_sum_even n = RustM.ok true := by
  rw [is_equal_to_sum_even_postcondition]
  rw [decide_eq_true hge]
  rw [heven]
  rfl

/-- Postcondition (witness / semantic completeness, second half of
    `accepts_even_at_least_8_with_witness`): for every even `n ≥ 8`
    there exist four positive even `u64` summands whose sum is `n`.
    Captures the proptest's concrete decomposition `2 + 2 + 2 + (n - 6)`,
    which justifies the function's name `is_equal_to_sum_even` —
    accepted inputs really are sums of four positive even integers. -/
theorem is_equal_to_sum_even_witness_exists
    (n : u64) (hge : (8 : u64) ≤ n) (heven : n % 2 = 0) :
    ∃ a b c d : u64,
      0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d
      ∧ a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 0 ∧ d % 2 = 0
      ∧ a + b + c + d = n := by
  -- Bridges to `Nat` arithmetic on `n.toNat`.
  have h_n_ge_nat : (8 : Nat) ≤ n.toNat := by
    have := UInt64.le_iff_toNat_le.mp hge
    have h8 : ((8 : u64).toNat) = 8 := rfl
    rw [h8] at this; exact this
  have h_n_mod_nat : n.toNat % 2 = 0 := by
    have h1 : (n % 2).toNat = (0 : u64).toNat := by rw [heven]
    rw [UInt64.toNat_mod] at h1
    rw [show ((2 : u64).toNat = 2) from rfl, show ((0 : u64).toNat = 0) from rfl] at h1
    exact h1
  -- Six is ≤ n.toNat (transitively from 8 ≤ n.toNat).
  have h_6_le_n_nat : (6 : Nat) ≤ n.toNat := by omega
  -- `(n - 6).toNat = n.toNat - 6` (no underflow).
  have h_sub_toNat : (n - (6 : u64)).toNat = n.toNat - 6 := by
    rw [UInt64.toNat_sub_of_le' (by rw [show ((6 : u64).toNat = 6) from rfl]; exact h_6_le_n_nat)]
    rw [show ((6 : u64).toNat = 6) from rfl]
  refine ⟨2, 2, 2, n - 6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · -- 0 < n - 6
    rw [UInt64.lt_iff_toNat_lt, h_sub_toNat,
        show ((0 : u64).toNat = 0) from rfl]
    omega
  · decide
  · decide
  · decide
  · -- (n - 6) % 2 = 0
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_mod, h_sub_toNat,
        show ((2 : u64).toNat = 2) from rfl,
        show ((0 : u64).toNat = 0) from rfl]
    omega
  · -- 2 + 2 + 2 + (n - 6) = n
    -- Reduce `2 + 2 + 2 = 6 : u64`, then `6 + (n - 6) = n`.
    show ((2 : u64) + 2 + 2 + (n - 6)) = n
    have h_222 : ((2 : u64) + 2 + 2) = (6 : u64) := by decide
    rw [h_222]
    apply UInt64.toNat_inj.mp
    have h_add_bound :
        ((6 : u64)).toNat + (n - (6 : u64)).toNat < 2 ^ 64 := by
      rw [show ((6 : u64).toNat = 6) from rfl, h_sub_toNat]
      have h_n_lt := n.toNat_lt
      omega
    rw [UInt64.toNat_add_of_lt h_add_bound, h_sub_toNat,
        show ((6 : u64).toNat = 6) from rfl]
    omega

/-- Failure condition (parity), from proptest `rejects_odd`: the sum of
    any four even integers is even, so every odd `n` is rejected.
    Phrased as `n % 2 = 1` to match the Rust test guard. -/
theorem is_equal_to_sum_even_rejects_odd
    (n : u64) (hodd : n % 2 = 1) :
    is_equal_to_sum_even n = RustM.ok false := by
  rw [is_equal_to_sum_even_postcondition]
  rw [hodd]
  show RustM.ok (decide ((8 : u64) ≤ n) && ((1 : u64) == (0 : u64))) = RustM.ok false
  rw [show ((1 : u64) == (0 : u64)) = false from by decide]
  rw [Bool.and_false]

/-- Failure condition (lower bound), from unit test `rejects_below_minimum_sum`:
    the smallest sum of four positive even integers is `2 + 2 + 2 + 2 = 8`,
    so every `n < 8` is rejected. -/
theorem is_equal_to_sum_even_rejects_below_minimum
    (n : u64) (hlt : n < (8 : u64)) :
    is_equal_to_sum_even n = RustM.ok false := by
  rw [is_equal_to_sum_even_postcondition]
  have h_not_ge : ¬ ((8 : u64) ≤ n) := by
    intro h_le
    have h_lt_nat : n.toNat < (8 : u64).toNat := UInt64.lt_iff_toNat_lt.mp hlt
    have h_le_nat : (8 : u64).toNat ≤ n.toNat := UInt64.le_iff_toNat_le.mp h_le
    omega
  rw [decide_eq_false h_not_ge]
  rw [Bool.false_and]

end Clever_136_is_equal_to_sum_evenObligations
