-- Companion obligations file for the `multinomial_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import multinomial_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Multinomial_u64Obligations

/-! ## Mathematical binomial coefficient.

Lean core does not provide `Nat.choose` (only Mathlib does); define one
locally so the closed-form spec can use it. -/

/-- Mathematical binomial coefficient. Standard Pascal-triangle definition. -/
private def nchoose : Nat → Nat → Nat
  | _,     0     => 1
  | 0,     _ + 1 => 0
  | n + 1, k + 1 => nchoose n k + nchoose n (k + 1)

/-! ## Prefix-based specifications of running sum and multinomial product.

These mirror the algorithm's left-to-right iteration in `multinomial_loop`,
viewed at the `Nat` level so the spec itself cannot overflow. Every
theorem below quantifies the index so that it stays in range (the `dite`
guard keeps the definitions total).

- `sum_prefix k i = Σ_{j<i} (k.val[j]).toNat` — the running sum `p` after
  the loop has processed indices `0, 1, …, i-1`.
- `mult_prefix k i = ∏_{j<i} C(sum_prefix k (j+1), (k.val[j]).toNat)` —
  the running product `r`, equal to the multinomial coefficient of the
  prefix `k.val[0..i]`. -/

private def sum_prefix (k : RustSlice u64) : Nat → Nat
  | 0     => 0
  | i + 1 =>
      sum_prefix k i +
        (if h : i < k.val.size then (k.val[i]'h).toNat else 0)

private def mult_prefix (k : RustSlice u64) : Nat → Nat
  | 0     => 1
  | i + 1 =>
      mult_prefix k i *
        (if h : i < k.val.size then
           nchoose (sum_prefix k (i + 1)) (k.val[i]'h).toNat
         else 1)

/-! ## Theorems

Each theorem captures one independent contract clause documented by the
property tests in the Rust `tests` module. -/

/-- Boundary contract: `multinomial(&[])` is the empty product, 1.

    Captures the property test `empty_slice_returns_one` (and the
    `multinomial(&[]) == 1` case inside `test_multinomial`). Pinned to
    the equational form because the precondition is trivially satisfied
    on the empty slice. -/
theorem multinomial_empty_returns_one
    (k : RustSlice u64) (hempty : k.val.size = 0) :
    multinomial_u64.multinomial k = RustM.ok (1 : u64) := by
  sorry

/-- Boundary contract: a singleton `&[n]` returns 1 for any `n : u64`,
    including `u64::MAX`. The iteration computes
    `binomial(n, n) = 1` and starts with `r = 1`, so no arithmetic on
    the value itself happens beyond the (always-1) binomial step.

    Captures the property test `singleton_returns_one`, including the
    `u64::MAX` boundary case (which would catch a buggy implementation
    that performed any non-trivial arithmetic on the singleton value). -/
theorem multinomial_singleton_returns_one
    (k : RustSlice u64) (hsing : k.val.size = 1) :
    multinomial_u64.multinomial k = RustM.ok (1 : u64) := by
  sorry

/-- Closed-form postcondition: under the overflow-free preconditions on
    the running sum (`< 2^64`) and the final result (`< 2^64`), the
    function returns the mathematical multinomial coefficient encoded
    by the Pascal-chain product `mult_prefix`.

    Captures the postcondition clauses behind `test_multinomial`
    (specific small cases) and
    `matches_factorial_reference_on_small_inputs` (agreement with the
    factorial-based reference on inputs whose sum fits in `u64`):
    on the Nat level, `mult_prefix k k.val.size` equals
    `(Σ kᵢ)! / ∏ kᵢ!`, so this single closed form subsumes both
    tests. -/
theorem multinomial_closed_form (k : RustSlice u64)
    (hfit_sum    : sum_prefix  k k.val.size < 2 ^ 64)
    (hfit_result : mult_prefix k k.val.size < 2 ^ 64) :
    multinomial_u64.multinomial k =
      RustM.ok (UInt64.ofNat (mult_prefix k k.val.size)) := by
  sorry

/-- Permutation invariance: the multinomial coefficient is symmetric in
    its argument; reordering `k` does not change the result. Captures
    the property test `permutation_invariance` (which covers cyclic
    rotation, full reversal, and the first-two-entries swap).

    The implementation iterates left-to-right with a running sum, so
    symmetry is not visibly true from the code — a reorder-sensitive
    bug (e.g. computing `binomial(k[i], p_new)` instead of
    `binomial(p_new, k[i])`) would still pass the boundary and closed-
    form tests but would fail here. Stated using `List.Perm` on the
    underlying `Array u64` content.

    Both slices carry the same no-overflow preconditions; on the Nat
    level these are equivalent under permutation (the Nat sum and the
    factorial-form multinomial value are both symmetric), but stating
    both keeps the obligation self-contained. -/
theorem multinomial_permutation_invariant (k k' : RustSlice u64)
    (hperm        : k.val.toList.Perm k'.val.toList)
    (hfit_sum_k   : sum_prefix  k  k.val.size  < 2 ^ 64)
    (hfit_res_k   : mult_prefix k  k.val.size  < 2 ^ 64)
    (hfit_sum_k'  : sum_prefix  k' k'.val.size < 2 ^ 64)
    (hfit_res_k'  : mult_prefix k' k'.val.size < 2 ^ 64) :
    ∃ v : u64,
      multinomial_u64.multinomial k  = RustM.ok v ∧
      multinomial_u64.multinomial k' = RustM.ok v := by
  sorry

/-- Failure clause: when the integer running sum exceeds the `u64`
    range (i.e. `2 ^ 64 ≤ sum_prefix k k.val.size`), the unchecked
    `p + k[i]` addition in the loop body overflows and the function
    fails with an integer-overflow error.

    Captures the property test `sum_overflow_panics`
    (`multinomial(&[u64::MAX, 1])` panics): the Nat-level prefix sum is
    `u64::MAX + 1 = 2 ^ 64`, which falls under this clause. -/
theorem multinomial_overflow_fails (k : RustSlice u64)
    (hov : 2 ^ 64 ≤ sum_prefix k k.val.size) :
    ∃ e, multinomial_u64.multinomial k = RustM.fail e := by
  sorry

end Multinomial_u64Obligations
