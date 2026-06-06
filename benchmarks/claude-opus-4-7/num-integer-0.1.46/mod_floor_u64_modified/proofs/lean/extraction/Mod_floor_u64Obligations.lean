-- Companion obligations file for the `mod_floor_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import mod_floor_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Mod_floor_u64Obligations

open mod_floor_u64

/-- Failure condition: when the divisor is `0`, `my_mod_floor` panics with a
    `divisionByZero` error. Captures the `panics_on_zero_divisor`
    `#[should_panic]` test. -/
theorem mod_floor_fails_on_zero_divisor (x : u64) :
    my_mod_floor x 0 = RustM.fail Error.divisionByZero := by
  simp only [my_mod_floor, rust_primitives.ops.arith.Rem.rem]
  rfl

/-- Postcondition (range): when `y ≠ 0`, the result is strictly less than the
    divisor `y`. Captures `prop_result_less_than_divisor`. -/
theorem mod_floor_result_lt_divisor (x y : u64) :
    ⦃ ⌜ y ≠ 0 ⌝ ⦄ my_mod_floor x y ⦃ ⇓ r => ⌜ r < y ⌝ ⦄ := by
  mvcgen [my_mod_floor, rust_primitives.ops.arith.Rem.rem]
  · -- failure branch (vc1.isTrue): y = 0 contradicts the precondition y ≠ 0
    intro hy
    rename_i h
    exact absurd h hy
  · -- success branch (vc2.isFalse): given y ≠ 0, prove x % y < y on u64.
    -- bv_decide times out on 64-bit modulus; lift to Nat and use Nat.mod_lt.
    rename_i h _
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_mod]
    have hy_pos : 0 < y.toNat := by
      rw [Nat.pos_iff_ne_zero]
      intro hzero
      apply h
      exact UInt64.toNat_inj.mp (by simpa using hzero)
    exact Nat.mod_lt _ hy_pos

/-- Postcondition (division identity): when `y ≠ 0`, the result satisfies the
    floor-division identity `x = (x / y) * y + r` (stated on `Nat` via
    `toNat`). Captures `prop_division_identity`. -/
theorem mod_floor_division_identity (x y : u64) :
    ⦃ ⌜ y ≠ 0 ⌝ ⦄ my_mod_floor x y
    ⦃ ⇓ r => ⌜ x.toNat = (x.toNat / y.toNat) * y.toNat + r.toNat ⌝ ⦄ := by
  mvcgen [my_mod_floor, rust_primitives.ops.arith.Rem.rem]
  · -- failure branch (vc1.isTrue): y = 0 contradicts the precondition y ≠ 0
    intro hy
    rename_i h
    exact absurd h hy
  · -- success branch (vc2.isFalse): division identity from Nat.div_add_mod'.
    -- Convert (x % y).toNat to x.toNat % y.toNat, then close with the Nat lemma.
    rw [UInt64.toNat_mod]
    exact (Nat.div_add_mod' x.toNat y.toNat).symm

/-- Functional spec / agreement with source: when `y ≠ 0`, the extracted
    function returns exactly `x % y`, matching `num_integer::mod_floor` on
    `u64` (where floored modulus coincides with truncated remainder).
    Captures the differential `prop_agrees_with_source` property test as well
    as the unit tests `test_mod_floor`, `agrees_with_source`, and
    `agrees_with_source_large`. -/
theorem mod_floor_agrees_with_source (x y : u64) (hy : y ≠ 0) :
    my_mod_floor x y = RustM.ok (x % y) := by
  simp only [my_mod_floor, rust_primitives.ops.arith.Rem.rem, if_neg hy]
  rfl

end Mod_floor_u64Obligations
