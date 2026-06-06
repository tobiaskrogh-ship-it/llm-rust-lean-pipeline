-- Companion obligations file for the `gcd_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import gcd_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Gcd_u64Obligations

/-! ## Master closed-form postcondition

The function `gcd_u64.gcd` reduces to `Nat.gcd` on the `toNat` projections of
its inputs. This is the master statement: every other contract clause below
is a direct projection of it.

The function is total on all `(u64, u64)` inputs — no panics, no overflow:
the early-return path returns `x ||| y`, and in the recursive branch the
result is bounded by `max x y` so the final `<<< shift` cannot overflow. -/

theorem gcd_postcondition (x y : u64) :
    gcd_u64.gcd x y = RustM.ok (UInt64.ofNat (Nat.gcd x.toNat y.toNat)) := by
  sorry

/-! ## Contract clauses derived from the closed form

Each derived clause goes through `gcd_postcondition`; once the master closes,
every clause below closes automatically. -/

/-- Totality / no panic: `gcd` returns a value on every `(u64, u64)` input —
    no division by zero, no shift overflow, no add/sub overflow. -/
theorem gcd_total (x y : u64) :
    ∃ v : u64, gcd_u64.gcd x y = RustM.ok v := by
  sorry

/-- Postcondition (Z), case `(0, 0)`: `gcd(0, 0) = 0`. Captures the
    `gcd(0, 0) = 0` assertion of `prop_gcd_zero_cases`. -/
theorem gcd_zero_zero :
    gcd_u64.gcd 0 0 = RustM.ok 0 := by
  sorry

/-- Postcondition (Z), case `(x, 0)`: `gcd(x, 0) = x`. Captures the
    `gcd(x, 0) = x` assertion of `prop_gcd_zero_cases` (including the
    `u64::MAX` spot-check). -/
theorem gcd_x_zero (x : u64) :
    gcd_u64.gcd x 0 = RustM.ok x := by
  sorry

/-- Postcondition (Z), case `(0, y)`: `gcd(0, y) = y`. Captures the
    `gcd(0, y) = y` assertion of `prop_gcd_zero_cases` (including the
    `u64::MAX` spot-check). -/
theorem gcd_zero_y (y : u64) :
    gcd_u64.gcd 0 y = RustM.ok y := by
  sorry

/-- Postcondition (D), left half: the result divides `x`. Captures the
    `x % g == 0` arm of `prop_gcd_divides_both` (also recovers `gcd(0, y) = y`
    via the divisibility of any `v` by `0`). -/
theorem gcd_divides_x (x y : u64) :
    ∃ v : u64, gcd_u64.gcd x y = RustM.ok v ∧ v.toNat ∣ x.toNat := by
  sorry

/-- Postcondition (D), right half: the result divides `y`. Captures the
    `y % g == 0` arm of `prop_gcd_divides_both`. -/
theorem gcd_divides_y (x y : u64) :
    ∃ v : u64, gcd_u64.gcd x y = RustM.ok v ∧ v.toNat ∣ y.toNat := by
  sorry

/-- Postcondition (G): every common divisor of `x` and `y` divides the
    result. Captures `prop_gcd_is_greatest`. Combined with `gcd_divides_x` /
    `gcd_divides_y`, characterises the result as the maximum common divisor
    in the divisibility lattice. -/
theorem gcd_greatest (x y : u64) :
    ∃ v : u64, gcd_u64.gcd x y = RustM.ok v ∧
      ∀ d : Nat, d ∣ x.toNat → d ∣ y.toNat → d ∣ v.toNat := by
  sorry

/-- Postcondition (D), zero-result clause: the result is `0` only when both
    inputs are `0`. Captures the `g == 0 → x == 0 ∧ y == 0` arm of
    `prop_gcd_divides_both`. -/
theorem gcd_zero_iff (x y : u64) :
    ∃ v : u64, gcd_u64.gcd x y = RustM.ok v ∧
      (v = 0 → x = 0 ∧ y = 0) := by
  sorry

end Gcd_u64Obligations
