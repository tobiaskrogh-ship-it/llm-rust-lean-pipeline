-- Companion obligations file for the `lcm_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import lcm_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Lcm_u64Obligations

/-! ## Concrete value tests

Captures the `assert_eq!` lines in `test_lcm` and `test_lcm_doc`. Each test
case becomes one equational obligation `lcm a b = RustM.ok r`. -/

/-- `test_lcm` case 1: `lcm(1, 0) = 0`. -/
theorem lcm_1_0 : lcm_u64.lcm 1 0 = RustM.ok 0 := by sorry

/-- `test_lcm` case 2: `lcm(0, 1) = 0`. -/
theorem lcm_0_1 : lcm_u64.lcm 0 1 = RustM.ok 0 := by sorry

/-- `test_lcm` case 3: `lcm(1, 1) = 1`. -/
theorem lcm_1_1 : lcm_u64.lcm 1 1 = RustM.ok 1 := by sorry

/-- `test_lcm` case 4: `lcm(8, 9) = 72`. -/
theorem lcm_8_9 : lcm_u64.lcm 8 9 = RustM.ok 72 := by sorry

/-- `test_lcm` case 5: `lcm(11, 5) = 55`. -/
theorem lcm_11_5 : lcm_u64.lcm 11 5 = RustM.ok 55 := by sorry

/-- `test_lcm` case 6: `lcm(15, 17) = 255`. -/
theorem lcm_15_17 : lcm_u64.lcm 15 17 = RustM.ok 255 := by sorry

/-- `test_lcm_doc` case 1: `lcm(7, 3) = 21`. -/
theorem lcm_7_3 : lcm_u64.lcm 7 3 = RustM.ok 21 := by sorry

/-- `test_lcm_doc` case 2: `lcm(2, 4) = 4`. -/
theorem lcm_2_4 : lcm_u64.lcm 2 4 = RustM.ok 4 := by sorry

/-- `test_lcm_doc` case 3: `lcm(0, 0) = 0`. Boundary case — the function
short-circuits via `if x == 0 && y == 0 { return 0 }`. -/
theorem lcm_0_0 : lcm_u64.lcm 0 0 = RustM.ok 0 := by sorry

/-! ## Overflow test (`test_lcm_overflow`)

The source test asserts that even though `x * y = 2^63 * 2 = 2^64` overflows
in plain multiplication, `lcm(x, y)` does not: the implementation computes
`x * (y / gcd) = 2^63 * (2 / 2) = 2^63`, which fits in `u64`. -/

/-- `test_lcm_overflow` first assertion: `lcm(2^63, 2) = 2^63`. -/
theorem lcm_overflow_xy :
    lcm_u64.lcm 0x8000000000000000 2 = RustM.ok 0x8000000000000000 := by sorry

/-- `test_lcm_overflow` symmetric assertion: `lcm(2, 2^63) = 2^63`. -/
theorem lcm_overflow_yx :
    lcm_u64.lcm 2 0x8000000000000000 = RustM.ok 0x8000000000000000 := by sorry

/-! ## Absorbing-zero (`prop_zero_is_absorbing`)

Universal version of the property test: for every `y`, `lcm(0, y) = 0`,
and symmetrically `lcm(x, 0) = 0`. Holds without any overflow precondition
because the function short-circuits to `gcd | 0` shortly afterwards and
multiplies by `0` (which never overflows). -/

/-- `prop_zero_is_absorbing`, left absorption: `lcm(0, y) = 0` for every `y`. -/
theorem lcm_zero_left (y : u64) : lcm_u64.lcm 0 y = RustM.ok 0 := by sorry

/-- `prop_zero_is_absorbing`, right absorption: `lcm(x, 0) = 0` for every `x`. -/
theorem lcm_zero_right (x : u64) : lcm_u64.lcm x 0 = RustM.ok 0 := by sorry

/-! ## Totality and divisibility (under no-overflow)

The property tests `prop_result_is_multiple_of_x`, `prop_result_is_multiple_of_y`,
and `prop_result_is_least_common_multiple` iterate over `1..40` (resp. `1..25`),
which stays well below `u64::MAX.sqrt()`. The natural Lean generalisation
quantifies over all `(x, y)` with `x.toNat * y.toNat < 2 ^ 64`, mirroring the
no-overflow precondition used in `gcd_lcm_u64`'s reference obligations: this is
the strongest practical no-overflow bound (it is sufficient but not strictly
necessary — `lcm(2^63, 2)` fits even though `2^63 * 2` overflows; that case
is handled by the explicit `lcm_overflow_*` theorems above). -/

/-- Totality: under no-overflow, `lcm x y` returns an `ok` value. -/
theorem lcm_total (x y : u64) (h_no_ovf : x.toNat * y.toNat < 2 ^ 64) :
    ∃ l : u64, lcm_u64.lcm x y = RustM.ok l := by sorry

/-- `prop_result_is_multiple_of_x`: the result is a multiple of `x`. Stated
under no-overflow; the property test exercises `x, y ∈ [1, 40)` (well within
the bound). The zero-input cases are excluded by the property test (`x ≥ 1`)
but the statement here is honest about them too: when `x.toNat = 0`,
`x.toNat ∣ l.toNat` reduces to `l.toNat = 0`, which `lcm(0, y) = 0` gives. -/
theorem lcm_multiple_of_x (x y : u64) (h_no_ovf : x.toNat * y.toNat < 2 ^ 64) :
    ∃ l : u64, lcm_u64.lcm x y = RustM.ok l ∧ x.toNat ∣ l.toNat := by sorry

/-- `prop_result_is_multiple_of_y`: the result is a multiple of `y`. Stated
under no-overflow; mirrors `lcm_multiple_of_x` with the second argument. -/
theorem lcm_multiple_of_y (x y : u64) (h_no_ovf : x.toNat * y.toNat < 2 ^ 64) :
    ∃ l : u64, lcm_u64.lcm x y = RustM.ok l ∧ y.toNat ∣ l.toNat := by sorry

/-- `prop_result_is_least_common_multiple`: when both inputs are positive,
the result is the *least* positive common multiple — no smaller positive
integer is divisible by both `x` and `y`. -/
theorem lcm_least (x y : u64) (hx : 0 < x.toNat) (hy : 0 < y.toNat)
    (h_no_ovf : x.toNat * y.toNat < 2 ^ 64) :
    ∃ l : u64, lcm_u64.lcm x y = RustM.ok l ∧
      ∀ z : Nat, 0 < z → z < l.toNat → ¬ (x.toNat ∣ z ∧ y.toNat ∣ z) := by sorry

end Lcm_u64Obligations
