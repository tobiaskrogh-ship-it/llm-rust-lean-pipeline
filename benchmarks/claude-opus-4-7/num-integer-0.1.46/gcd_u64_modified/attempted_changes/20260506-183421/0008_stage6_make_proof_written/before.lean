-- Companion obligations file for the `gcd_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

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

/-- Postcondition (Z-left): `gcd(0, y) = y`.

    The early-return path (`m == 0 || n == 0` ⇒ `m | n`) is taken whenever
    the first argument is 0, and `0 | y = y`. -/
theorem gcd_zero_left (y : u64) :
    gcd_u64.gcd 0 y = RustM.ok y := by
  simp only [gcd_u64.gcd, rust_primitives.cmp.eq, rust_primitives.hax.logical_op.or,
             pure_bind, beq_self_eq_true, Bool.true_or, ↓reduceIte]
  show RustM.ok ((0 : u64) ||| y) = RustM.ok y
  congr 1
  bv_decide

/-- Postcondition (Z-right): `gcd(x, 0) = x`. -/
theorem gcd_zero_right (x : u64) :
    gcd_u64.gcd x 0 = RustM.ok x := by
  simp only [gcd_u64.gcd, rust_primitives.cmp.eq, rust_primitives.hax.logical_op.or,
             pure_bind, beq_self_eq_true, Bool.or_true, ↓reduceIte]
  show RustM.ok (x ||| (0 : u64)) = RustM.ok x
  congr 1
  bv_decide

/-- Totality / no-failure: `gcd` is total on the entire `(u64, u64)` domain. -/
theorem gcd_total (x y : u64) :
    ∃ v : u64, gcd_u64.gcd x y = RustM.ok v := by
  sorry

/-- Postcondition (D-x): the result divides the first input. -/
theorem gcd_divides_x (x y : u64) :
    ⦃ ⌜ True ⌝ ⦄
      gcd_u64.gcd x y
    ⦃ ⇓ g => ⌜ g.toNat ∣ x.toNat ⌝ ⦄ := by
  sorry

/-- Postcondition (D-y): the result divides the second input. -/
theorem gcd_divides_y (x y : u64) :
    ⦃ ⌜ True ⌝ ⦄
      gcd_u64.gcd x y
    ⦃ ⇓ g => ⌜ g.toNat ∣ y.toNat ⌝ ⦄ := by
  sorry

/-- Postcondition (G): every common divisor of `x` and `y` divides
    the result — i.e. the result is the *greatest* common divisor. -/
theorem gcd_is_greatest (x y d : u64) :
    ⦃ ⌜ d.toNat ∣ x.toNat ∧ d.toNat ∣ y.toNat ⌝ ⦄
      gcd_u64.gcd x y
    ⦃ ⇓ g => ⌜ d.toNat ∣ g.toNat ⌝ ⦄ := by
  sorry

end Gcd_u64Obligations
