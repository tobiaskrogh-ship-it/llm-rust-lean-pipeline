-- Companion obligations file for the `gcd_stein_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import gcd_stein_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Gcd_stein_u64Obligations

/-! ## Helper lemmas for casting `Nat.gcd` back to `u64`.

Pure-Nat facts about `Nat.gcd a.toNat b.toNat` — copied verbatim from
`Gcd_whileObligations.lean`, where they are also used to bridge between
`Nat.gcd` and `UInt64.ofNat (Nat.gcd …)`. -/

private theorem gcd_lt_2_64 (a b : u64) : Nat.gcd a.toNat b.toNat < 2 ^ 64 := by
  by_cases hb : b.toNat = 0
  · rw [hb, Nat.gcd_zero_right]
    exact a.toNat_lt
  · have h_le : Nat.gcd a.toNat b.toNat ≤ b.toNat :=
      Nat.gcd_le_right a.toNat (Nat.pos_of_ne_zero hb)
    exact Nat.lt_of_le_of_lt h_le b.toNat_lt

private theorem gcd_toNat_ofNat (a b : u64) :
    (UInt64.ofNat (Nat.gcd a.toNat b.toNat)).toNat = Nat.gcd a.toNat b.toNat :=
  UInt64.toNat_ofNat_of_lt' (gcd_lt_2_64 a b)

/-! ## Contract obligations for `gcd_stein_u64.gcd_stein`

The contract is read off the property tests in `src/lib.rs`:

* `known_values` + `zero_zero_is_zero` — closed-form equation
  `gcd_stein a b = Nat.gcd a b`.  Stating this once as the
  `_postcondition` theorem subsumes every concrete hand-checked value
  (`(10, 2) = 2`, `(0, 3) = 3`, `(3, 3) = 3`, `(56, 42) = 14`, etc.).
* `result_divides_both_inputs` — two independent divisibility clauses
  `gcd | a` and `gcd | b`.
* `result_is_greatest` — every common divisor `d` divides the result.

Stein's binary algorithm has *no documented failure modes*: every
intermediate `u64` operation is provably in range (subtraction is guarded
by `m > n`, the final `m << shift` produces `gcd(a, b) ≤ max(a, b) < 2^64`).
Hence the postcondition is stated equationally as `RustM.ok …` rather
than as a Hoare triple — the no-panic clause is folded into the use of
`RustM.ok` on the right-hand side, and surfaced explicitly as
`gcd_stein_total`.

Shapes mirror `proof_patterns/gcd_while_modified/.../Gcd_whileObligations.lean`. -/

/-- **Functional correctness (closed form).** For every pair of `u64`
inputs, `gcd_stein` succeeds and returns the integer gcd of the two
inputs (computed over `Nat`).  This single equation pins down every
concrete `known_values` case as well as the `zero_zero_is_zero`
boundary (`Nat.gcd 0 0 = 0`). -/
theorem gcd_stein_postcondition (a b : u64) :
    gcd_stein_u64.gcd_stein a b
      = RustM.ok (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) := by
  sorry

/-- **No-panic / totality.** Stein's algorithm has no documented failure
mode (every `-?` is guarded by a `>`, the final `<<? shift` cannot
overflow because `gcd(a, b) ≤ max(a, b)`).  The function therefore
returns `RustM.ok _` on the entire input domain.  Stated separately
from `gcd_stein_postcondition` because it is the explicit "no failure"
clause of the contract, independent of the returned value. -/
theorem gcd_stein_total (a b : u64) :
    ∃ v : u64, gcd_stein_u64.gcd_stein a b = RustM.ok v :=
  ⟨_, gcd_stein_postcondition a b⟩

/-- **`gcd_stein(0, 0) = 0`.** The explicit boundary from
`zero_zero_is_zero` — the `m | n` short-circuit in the source returns
0 when both inputs are 0. -/
theorem gcd_stein_zero_zero :
    gcd_stein_u64.gcd_stein 0 0 = RustM.ok 0 := by
  simp only [gcd_stein_u64.gcd_stein, rust_primitives.cmp.eq,
             rust_primitives.hax.logical_op.or, pure_bind,
             beq_self_eq_true, Bool.or_self, ↓reduceIte]
  rfl

/-- **`gcd_stein(0, b) = b`.** Pins down the `a = 0` branch of the
`m == 0 || n == 0` short-circuit.  Covers the `(0, 3) = 3` row of
`known_values` (and, together with `gcd_stein_divides_b`, forces
`gcd_stein(0, b) = b` since the gcd must divide `b` and is itself
divisible by `b` via `Nat.gcd_zero_left`). -/
theorem gcd_stein_a_zero (b : u64) :
    gcd_stein_u64.gcd_stein 0 b = RustM.ok b := by
  simp only [gcd_stein_u64.gcd_stein, rust_primitives.cmp.eq,
             rust_primitives.hax.logical_op.or, pure_bind,
             beq_self_eq_true, Bool.true_or, ↓reduceIte]
  -- Goal: pure (0 ||| b) = RustM.ok b
  apply congrArg RustM.ok
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_or]
  show 0 ||| b.toNat = b.toNat
  exact Nat.zero_or b.toNat

/-- **`gcd_stein(a, 0) = a`.** Symmetric to `gcd_stein_a_zero`; pins
down the `b = 0` branch of the short-circuit. -/
theorem gcd_stein_b_zero (a : u64) :
    gcd_stein_u64.gcd_stein a 0 = RustM.ok a := by
  simp only [gcd_stein_u64.gcd_stein, rust_primitives.cmp.eq,
             rust_primitives.hax.logical_op.or, pure_bind,
             beq_self_eq_true, Bool.or_true, ↓reduceIte]
  -- Goal: pure (a ||| 0) = RustM.ok a
  apply congrArg RustM.ok
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_or]
  show a.toNat ||| 0 = a.toNat
  exact Nat.or_zero a.toNat

/-- **Common-divisor clause (left).** The returned value divides the
first input.  One of the two independent claims certified by the
`result_divides_both_inputs` property test.

Derived from `gcd_stein_postcondition` via `Nat.gcd_dvd_left`; carries
no independent `sorry` (so the only proof obligation remaining is the
closed-form postcondition itself). -/
theorem gcd_stein_divides_a (a b : u64) :
    ∃ v : u64, gcd_stein_u64.gcd_stein a b = RustM.ok v ∧ v.toNat ∣ a.toNat := by
  refine ⟨_, gcd_stein_postcondition a b, ?_⟩
  rw [gcd_toNat_ofNat]
  exact Nat.gcd_dvd_left a.toNat b.toNat

/-- **Common-divisor clause (right).** The returned value divides the
second input.  The other independent claim from
`result_divides_both_inputs`.

Derived from `gcd_stein_postcondition` via `Nat.gcd_dvd_right`. -/
theorem gcd_stein_divides_b (a b : u64) :
    ∃ v : u64, gcd_stein_u64.gcd_stein a b = RustM.ok v ∧ v.toNat ∣ b.toNat := by
  refine ⟨_, gcd_stein_postcondition a b, ?_⟩
  rw [gcd_toNat_ofNat]
  exact Nat.gcd_dvd_right a.toNat b.toNat

/-- **Greatest-divisor clause.** Every common divisor of `a` and `b`
divides the returned value.  This is the contract certified by the
`result_is_greatest` property test (which checks no integer strictly
greater than the result divides both inputs; equivalently, every
common divisor `d` satisfies `d ∣ gcd`, hence `d ≤ gcd` when both are
nonzero).  Stated in the `d ∣ result` form for parity with
`gcd_while_greatest` and to match `Nat.dvd_gcd`.

Derived from `gcd_stein_postcondition` via `Nat.dvd_gcd`. -/
theorem gcd_stein_greatest (a b : u64) :
    ∃ v : u64, gcd_stein_u64.gcd_stein a b = RustM.ok v ∧
      ∀ d : Nat, d ∣ a.toNat → d ∣ b.toNat → d ∣ v.toNat := by
  refine ⟨_, gcd_stein_postcondition a b, ?_⟩
  intro d hda hdb
  rw [gcd_toNat_ofNat]
  exact Nat.dvd_gcd hda hdb

end Gcd_stein_u64Obligations
