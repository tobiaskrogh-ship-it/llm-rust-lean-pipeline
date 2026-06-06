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

/-- Mathematical binomial coefficient on `Nat`, defined via Pascal's
    recurrence (no Mathlib in this build, no `Nat.choose` available).
    Acts as the oracle for the functional-correctness theorem
    `binomial_value`. The recursion is structural on the first
    argument:
      * `C(n, 0) = 1`  for every `n` (covers both `n = 0` and `n > 0`);
      * `C(0, k+1) = 0`;
      * `C(n+1, k+1) = C(n, k) + C(n, k+1)`. -/
private def binomCoeff : Nat → Nat → Nat
  | _,     0     => 1
  | 0,     _ + 1 => 0
  | n + 1, k + 1 => binomCoeff n k + binomCoeff n (k + 1)

/-- Postcondition (out-of-range): when `k > n`, the function returns
    `0`. This is the early-return branch in the source
    (`if k > n { return 0; }`) and holds for every pair `(n, k) : u64`
    with `k > n`, with no further precondition: no arithmetic occurs
    before the early return, so no overflow is possible. Captures the
    `k_greater_than_n_is_zero` Rust property test. -/
theorem binomial_zero_when_k_gt_n (n k : u64) (h : k > n) :
    binomial_u64.binomial n k = RustM.ok (0 : u64) := by
  sorry

/-- Postcondition (boundary at `k = 0`): `C(n, 0) = 1` for every
    `n : u64`. The Rust source threads `k = 0` through the early
    branches without any arithmetic that could overflow (the inner
    `binomial_iter` returns `r = 1` immediately because `d = 1 > 0 = k`),
    so the equation holds on the entire `u64` domain — no precondition
    needed. Captures the `k = 0` half of `boundary_k_zero_and_k_eq_n`. -/
theorem binomial_k_zero (n : u64) :
    binomial_u64.binomial n 0 = RustM.ok (1 : u64) := by
  sorry

/-- Postcondition (boundary at `k = n`): `C(n, n) = 1` for every
    `n : u64`. With `k = n` the source recurses once via
    `binomial(n, n - k) = binomial(n, 0)` (no underflow since `n - n = 0`),
    then the `binomial_iter` call returns `1` immediately, so the
    equation holds on the entire `u64` domain. Captures the `k = n` half
    of `boundary_k_zero_and_k_eq_n`. -/
theorem binomial_n_n (n : u64) :
    binomial_u64.binomial n n = RustM.ok (1 : u64) := by
  sorry

/-- Postcondition (symmetry in `k`): for every `n ≤ 67` and `k ≤ n`,
    `binomial n k = binomial n (n - k)`. The Rust source explicitly
    invokes this branch (`if k > n - k { return binomial(n, n - k); }`),
    so the equality is built into the function's structure. The bound
    `n ≤ 67` ensures both sides return successfully (every `C(n, k)` for
    `n ≤ 67` fits in `u64`). Captures the `symmetric_in_k` Rust property
    test. -/
theorem binomial_symmetry (n k : u64)
    (hkn : k ≤ n) (hn : n.toNat ≤ 67) :
    binomial_u64.binomial n k = binomial_u64.binomial n (n - k) := by
  sorry

/-- Postcondition (Pascal's recurrence): for every `1 ≤ k ≤ n ≤ 50`,
    `binomial(n, k)` equals the sum of `binomial(n - 1, k - 1)` and
    `binomial(n - 1, k)`. The right-hand side is expressed in `RustM`
    by sequencing the two recursive calls and combining them with the
    fallible `+?`; under the precondition both calls succeed and the
    addition does not overflow. The bound `n ≤ 50` matches the Rust
    test's range and stays well inside the overflow-free domain.
    Captures the `pascal_recurrence` Rust property test. -/
theorem binomial_pascal_recurrence (n k : u64)
    (hk : 1 ≤ k.toNat) (hkn : k.toNat ≤ n.toNat) (hn : n.toNat ≤ 50) :
    binomial_u64.binomial n k =
      (do
        let a ← binomial_u64.binomial (n - 1) (k - 1)
        let b ← binomial_u64.binomial (n - 1) k
        a +? b) := by
  sorry

/-- Postcondition (functional correctness): for every `n ≤ 67` and any
    `k : u64`, the function returns the mathematical binomial
    coefficient `C(n, k)` (defined locally via `binomCoeff` using
    Pascal's recurrence). The bound `67` is the largest `n` for which
    `C(n, k)` fits in `u64` for every `k`, so the function is total on
    this domain. This is the deepest contract clause and pins down the
    function's value on every input in its precondition; combined with
    `binomial_zero_when_k_gt_n` (which `binomCoeff` already evaluates to
    `0` for `k > n`) it covers the entire test range
    `pascal_oracle_up_to_n67`. -/
theorem binomial_value (n k : u64) (h : n.toNat ≤ 67) :
    binomial_u64.binomial n k =
      RustM.ok (UInt64.ofNat (binomCoeff n.toNat k.toNat)) := by
  sorry

end Binomial_u64Obligations
