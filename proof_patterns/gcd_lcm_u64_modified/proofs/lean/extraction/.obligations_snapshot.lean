-- Companion obligations file for the `gcd_lcm_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import gcd_lcm_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Gcd_lcm_u64Obligations

open rust_primitives.hax (Tuple2)

/-! ## Contract clauses for `gcd_lcm_u64.gcd_lcm`

The contract is captured by the property tests in the Rust source:

  * `gcd_is_a_common_divisor` — the gcd component (`g`) divides both inputs;
    `g = 0` only when both inputs are zero (i.e. `g ≥ 1` otherwise).
  * `gcd_is_the_greatest_common_divisor` — every common divisor of `x` and `y`
    divides `g`.
  * `gcd_times_lcm_equals_x_times_y` — `g * l = x * y` (uniquely pinning `l`
    given the gcd properties).
  * `zero_input_edge_cases` — `gcd_lcm(0,0) = (0,0)`, `gcd_lcm(x,0) = (x,0)`,
    `gcd_lcm(0,y) = (y,0)`.
  * `test_gcd_lcm_doc` — pinned values at `(10, 4)` and `(8, 9)`.

Failure mode: the function panics on overflow when computing
`l = x * (y / g)`. Since `l ≤ x * y` (because `g ≥ 1` when not both zero, so
`y/g ≤ y`), the precondition `x.toNat * y.toNat < 2 ^ 64` rules out the
panic. The proptests stay inside `0..128`, so this bound is satisfied
trivially. For the (0, *) and (*, 0) cases the multiplication is `0`, so no
precondition is needed; these get standalone theorems below.

`test_gcd_lcm` (the consistency check between `gcd_lcm(i,j).0` and the
standalone Stein `gcd(i,j)`) is a derived fact: once the gcd component is
characterised by `divides_x + divides_y + greatest`, it equals the unique
gcd, which both functions compute. We omit it as a standalone clause.
-/

/-- Doc test 1: `gcd_lcm(10, 4) = (2, 20)`. Pins the specific value
    `gcd(10,4) = 2`, `lcm(10,4) = 20` from the documentation. -/
theorem gcd_lcm_doc_10_4 :
    gcd_lcm_u64.gcd_lcm 10 4 = RustM.ok ⟨2, 20⟩ := by
  sorry

/-- Doc test 2: `gcd_lcm(8, 9) = (1, 72)`. Pins the coprime case
    `gcd(8,9) = 1`, `lcm(8,9) = 72` from the documentation. -/
theorem gcd_lcm_doc_8_9 :
    gcd_lcm_u64.gcd_lcm 8 9 = RustM.ok ⟨1, 72⟩ := by
  sorry

/-- Zero–zero boundary: `gcd_lcm(0, 0) = (0, 0)`. Captures the explicit
    special case in the Rust source (`if x == 0 && y == 0 { return (0, 0) }`)
    and the first assertion of the `zero_input_edge_cases` test. -/
theorem gcd_lcm_zero_zero :
    gcd_lcm_u64.gcd_lcm 0 0 = RustM.ok ⟨0, 0⟩ := by
  sorry

/-- `x`–zero boundary: `gcd_lcm(x, 0) = (x, 0)` for every `x`. Captures the
    `gcd_lcm(x, 0) = (x, 0)` arm of the `zero_input_edge_cases` test. Holds
    universally on `u64`: when `x = 0` it collapses into the explicit zero
    branch; when `x ≠ 0` the source computes `g = gcd(x, 0) = x` and
    `l = x * (0 / x) = 0`, with no overflow possible because `l = 0`. -/
theorem gcd_lcm_x_zero (x : u64) :
    gcd_lcm_u64.gcd_lcm x 0 = RustM.ok ⟨x, 0⟩ := by
  sorry

/-- Zero–`y` boundary: `gcd_lcm(0, y) = (y, 0)` for every `y`. Captures the
    `gcd_lcm(0, y) = (y, 0)` arm of the `zero_input_edge_cases` test.
    `g = gcd(0, y) = y` and `l = 0 * (y / y) = 0` (no overflow). -/
theorem gcd_lcm_zero_y (y : u64) :
    gcd_lcm_u64.gcd_lcm 0 y = RustM.ok ⟨y, 0⟩ := by
  sorry

/-- Totality / no panic when `x * y` fits in `u64`. Captures the failure-mode
    clause of the contract: the function's only panic site is the
    `x * (y / g)` multiplication, which cannot overflow when `x * y < 2 ^ 64`
    (since `g ≥ 1` in the non-zero branch, so `y / g ≤ y`, hence
    `x * (y / g) ≤ x * y`). Outside this range the function may panic, so the
    universal version is not provable. -/
theorem gcd_lcm_total (x y : u64) (h_no_ovf : x.toNat * y.toNat < 2 ^ 64) :
    ∃ r : Tuple2 u64 u64, gcd_lcm_u64.gcd_lcm x y = RustM.ok r := by
  sorry

/-- Common-divisor half (left): the gcd component divides `x`. Captures the
    `assert_eq!(x % g, 0, …)` arm of `gcd_is_a_common_divisor`. Holds for all
    inputs (including the all-zero case, where `g = 0` and `0 ∣ 0`). The
    precondition rules out the panic on the lcm multiplication. -/
theorem gcd_lcm_gcd_divides_x (x y : u64)
    (h_no_ovf : x.toNat * y.toNat < 2 ^ 64) :
    ∃ g l : u64,
      gcd_lcm_u64.gcd_lcm x y = RustM.ok ⟨g, l⟩ ∧ g.toNat ∣ x.toNat := by
  sorry

/-- Common-divisor half (right): the gcd component divides `y`. Captures the
    `assert_eq!(y % g, 0, …)` arm of `gcd_is_a_common_divisor`. -/
theorem gcd_lcm_gcd_divides_y (x y : u64)
    (h_no_ovf : x.toNat * y.toNat < 2 ^ 64) :
    ∃ g l : u64,
      gcd_lcm_u64.gcd_lcm x y = RustM.ok ⟨g, l⟩ ∧ g.toNat ∣ y.toNat := by
  sorry

/-- The gcd component is zero **iff** both inputs are zero. Captures the
    `if x == 0 && y == 0 { assert_eq!(g, 0) } else { assert!(g >= 1) }` arm
    of `gcd_is_a_common_divisor`. -/
theorem gcd_lcm_gcd_zero_iff (x y : u64)
    (h_no_ovf : x.toNat * y.toNat < 2 ^ 64) :
    ∃ g l : u64,
      gcd_lcm_u64.gcd_lcm x y = RustM.ok ⟨g, l⟩ ∧
        (g = 0 → x = 0 ∧ y = 0) := by
  sorry

/-- Greatest-common-divisor half: every common divisor of `x` and `y` divides
    the gcd component. Captures the `gcd_is_the_greatest_common_divisor`
    property test. Combined with `gcd_lcm_gcd_divides_x` and
    `gcd_lcm_gcd_divides_y`, this characterises the gcd component as the
    unique maximum common divisor (in the divisibility lattice). -/
theorem gcd_lcm_gcd_greatest (x y : u64)
    (h_no_ovf : x.toNat * y.toNat < 2 ^ 64) :
    ∃ g l : u64,
      gcd_lcm_u64.gcd_lcm x y = RustM.ok ⟨g, l⟩ ∧
        ∀ d : Nat, d ∣ x.toNat → d ∣ y.toNat → d ∣ g.toNat := by
  sorry

/-- Product identity: `g * l = x * y`. Captures the
    `gcd_times_lcm_equals_x_times_y` property test. Together with the gcd
    properties, this uniquely fixes the lcm component. Stated on `Nat` so the
    equation never overflows; the precondition `x * y < 2 ^ 64` keeps both
    sides bounded by `u64`. -/
theorem gcd_lcm_product_identity (x y : u64)
    (h_no_ovf : x.toNat * y.toNat < 2 ^ 64) :
    ∃ g l : u64,
      gcd_lcm_u64.gcd_lcm x y = RustM.ok ⟨g, l⟩ ∧
        g.toNat * l.toNat = x.toNat * y.toNat := by
  sorry

end Gcd_lcm_u64Obligations
