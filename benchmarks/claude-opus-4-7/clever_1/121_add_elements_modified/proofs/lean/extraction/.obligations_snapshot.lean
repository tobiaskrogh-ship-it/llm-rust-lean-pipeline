-- Companion obligations file for the `clever_121_add_elements` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_121_add_elements

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_121_add_elementsObligations

/-! ## Integer-valued specification oracle

The Rust source computes
  `arr.iter().take(k).filter(|v| v.abs() <= 99).sum()`,
mirroring `add_elements`'s intended behaviour for `k > 0`.  We mirror that
at the `Int` level so the spec side cannot overflow on any input the Lean
model permits.

Because `cond_sum_int arr k j` contributes `0` for every index `j ≥ k`
*and* every index `j ≥ arr.val.size`, evaluating it at `arr.val.size`
yields exactly the prefix sum the function should produce regardless of
whether `k.toInt.toNat` is below or above `arr.val.size`. -/

/-- Conditional prefix sum: sum of `arr.val[j].toInt` over indices
    `j < arr.val.size` that satisfy `j < k` and
    `|arr.val[j].toInt| ≤ 99`.  The outer `dite` on `j < arr.val.size`
    keeps the function total — every theorem below either is universally
    quantified over `j` or instantiates it with `arr.val.size`, so the
    index never escapes range when the value matters. -/
private def cond_sum_int (arr : RustSlice i64) (k : Nat) : Nat → Int
  | 0     => 0
  | j + 1 =>
      cond_sum_int arr k j +
        (if h : j < arr.val.size then
           (if j < k ∧ (arr.val[j]'h).toInt.natAbs ≤ 99
            then (arr.val[j]'h).toInt
            else 0)
         else 0)

/-! ## Top-level theorems. -/

/-- Boundary clause: when `k ≤ 0`, `add_elements arr k` returns `0`
    regardless of the slice.  This pins down the explicit `k <= 0`
    short-circuit in `add_elements` (corresponding to the
    `nonpositive_k_returns_zero` proptest) independently of the recursive
    `sum_at` logic. -/
theorem add_elements_nonpositive_k_returns_zero
    (arr : RustSlice i64) (k : i64) (hk : k.toInt ≤ 0) :
    clever_121_add_elements.add_elements arr k = RustM.ok (0 : i64) := by
  sorry

/-- Main correctness postcondition: when `k > 0` and the model-level
    overflow guards hold, `add_elements arr k` succeeds and the result
    equals the integer-valued spec `cond_sum_int` (corresponding to the
    `matches_spec_for_positive_k` proptest).

    Two preconditions reconcile the universal Lean statement with the
    proptest's bounded sampling (`-1000..=1000` elements × length `0..256`):

    * `hno_min` — every element the recursion may inspect satisfies
      `(2^63 : Int) > |v.toInt|`, which both excludes `v = Int64.minValue`
      (so the unary `-v` in the `abs_v` computation cannot overflow) and
      rules out a positive `+v` ever overshooting `2^63 - 1`.  Without
      this, `arr[j] = Int64.minValue` would cause the recursive call to
      `fail` even when `|v| > 99` would otherwise skip it, because the
      Hax encoding evaluates `-v` before the `≤ 99` test.

    * `hfit` — every running conditional sum `cond_sum_int arr k j`
      (for `0 ≤ j ≤ arr.val.size`) fits in `i64`, so the accumulator
      addition `acc +? v` in each take-step cannot overflow. -/
theorem add_elements_matches_spec
    (arr : RustSlice i64) (k : i64)
    (hk_pos : 0 < k.toInt)
    (hno_min : ∀ (j : Nat) (h : j < arr.val.size),
                 j < k.toInt.toNat →
                   (arr.val[j]'h).toInt.natAbs < 2 ^ 63)
    (hfit : ∀ (j : Nat), j ≤ arr.val.size →
              -(2^63 : Int) ≤ cond_sum_int arr k.toInt.toNat j ∧
              cond_sum_int arr k.toInt.toNat j < 2^63) :
    ∃ r : i64,
      clever_121_add_elements.add_elements arr k = RustM.ok r ∧
      r.toInt = cond_sum_int arr k.toInt.toNat arr.val.size := by
  sorry

end Clever_121_add_elementsObligations
