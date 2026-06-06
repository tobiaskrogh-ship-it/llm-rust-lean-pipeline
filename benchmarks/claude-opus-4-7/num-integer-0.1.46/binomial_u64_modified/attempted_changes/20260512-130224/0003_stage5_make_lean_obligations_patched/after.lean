-- Companion obligations file for the `binomial_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import binomial_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Binomial_u64Obligations

/-! ## Contract clauses for `binomial_u64.binomial`

Each theorem captures one independent clause of the function's contract,
matching a property-style test in the Rust source.  Proofs are `sorry`
placeholders; they are filled in by the proof stage.

The overflow-free range for `u64` binomial coefficients is `n ≤ 67`
(matching the table in the doc-comment of the original
`num_integer::binomial` and the bound used by the `pascal_oracle_up_to_n67`
test).  The Pascal-recurrence test stays at `n ≤ 50`. -/

/-- `k > n` case: when the second argument exceeds the first, the function
    returns 0 without panicking.  Captures the explicit early-return clause
    `if k > n { return 0; }` in the source and the property test
    `k_greater_than_n_is_zero`. -/
theorem binomial_k_gt_n (n k : u64) (hkn : n.toNat < k.toNat) :
    binomial_u64.binomial n k = RustM.ok 0 := by
  sorry

/-- Boundary case `k = 0`: `C(n, 0) = 1` for every `n`.  Half of the property
    test `boundary_k_zero_and_k_eq_n`. -/
theorem binomial_k_zero (n : u64) :
    binomial_u64.binomial n 0 = RustM.ok 1 := by
  sorry

/-- Boundary case `k = n`: `C(n, n) = 1` for every `n`.  Other half of the
    property test `boundary_k_zero_and_k_eq_n`. -/
theorem binomial_k_eq_n (n : u64) :
    binomial_u64.binomial n n = RustM.ok 1 := by
  sorry

/-- Symmetry: `C(n, k) = C(n, n - k)` for `k ≤ n`.  The implementation
    exploits this via the recursive call `binomial(n, n - k)` when
    `k > n - k`; the property test `symmetry` documents it as an
    independent contract clause.  Both sides denote `RustM u64`; the
    subtraction `n - k` is `u64` subtraction and is well-defined under
    `k ≤ n`. -/
theorem binomial_symmetry (n k : u64) (hkn : k.toNat ≤ n.toNat) :
    binomial_u64.binomial n k = binomial_u64.binomial n (n - k) := by
  sorry

/-- Pascal's recurrence: for `1 ≤ k ≤ n` (and within the overflow-free range
    `n ≤ 50` used by the property test `pascal_recurrence`),
    `C(n, k) = C(n - 1, k - 1) + C(n - 1, k)` at the `u64` level.
    The existential bundles the three successful results so the equality
    can be stated on plain `u64` values; for `n ≤ 50` every term fits in
    `u64` (`C(50, 25) ≈ 1.26 × 10^14 ≪ 2^64`) so the `u64` addition does
    not overflow. -/
theorem binomial_pascal_recurrence (n k : u64)
    (hk_pos : 0 < k.toNat) (hkn : k.toNat ≤ n.toNat) (hn : n.toNat ≤ 50) :
    ∃ v vsub1 vsub2 : u64,
      binomial_u64.binomial n k = RustM.ok v ∧
      binomial_u64.binomial (n - 1) (k - 1) = RustM.ok vsub1 ∧
      binomial_u64.binomial (n - 1) k = RustM.ok vsub2 ∧
      v = vsub1 + vsub2 := by
  sorry

/-- Main postcondition: in the overflow-free range `n ≤ 67`, the function
    computes the standard binomial coefficient `Nat.choose`.  Captures the
    sweep tests `pascal_oracle_up_to_n67` and `agrees_with_source`, and
    subsumes the specific instances in `test_binomial_u64`. -/
theorem binomial_postcondition (n k : u64) (hn : n.toNat ≤ 67) :
    binomial_u64.binomial n k
      = RustM.ok (UInt64.ofNat (Nat.choose n.toNat k.toNat)) := by
  sorry

/-- Totality / no-panic: in the overflow-free range `n ≤ 67`, the function
    returns successfully for every `k`.  Together with the property tests
    (which all stay in the overflow-free range), this is the explicit
    "no failure mode" clause of the contract. -/
theorem binomial_total (n k : u64) (hn : n.toNat ≤ 67) :
    ∃ v : u64, binomial_u64.binomial n k = RustM.ok v :=
  ⟨_, binomial_postcondition n k hn⟩

end Binomial_u64Obligations
