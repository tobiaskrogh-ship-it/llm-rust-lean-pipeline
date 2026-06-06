-- Companion obligations file for the `clever_127_prod_signs` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_127_prod_signs

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_127_prod_signsObligations

/-! ## Integer-valued specification oracles.

The Rust `prod_signs(arr)` returns `Σ |v_i| · Π sgn(v_i)` (with empty
product `1`) on non-empty input, and `None` on the empty slice. We mirror
both factors as `Int`-valued prefix oracles so the spec itself never
overflows: the obligations parameterise overflow as preconditions
(`hfit`, `hno_min`) rather than burying it inside the spec. -/

/-- Integer signum on `Int`:
    `sgn_int 0 = 0`, `sgn_int n = 1` for `n > 0`, `sgn_int n = -1` for `n < 0`. -/
private def sgn_int (n : Int) : Int :=
  if n = 0 then 0 else if 0 < n then 1 else -1

/-- Integer-valued prefix sum of absolute values:
    `sum_abs_int arr k = Σ_{j<k} |(arr.val[j]).toInt|`.
    Empty sum is `0`, matching the `sum_abs = 0` seed of `run_at`. -/
private def sum_abs_int (arr : RustSlice i64) : Nat → Int
  | 0     => 0
  | k + 1 =>
      sum_abs_int arr k +
        (if h : k < arr.val.size then ((arr.val[k]'h).toInt.natAbs : Int) else 0)

/-- Integer-valued prefix product of signums:
    `sign_product_int arr k = Π_{j<k} sgn((arr.val[j]).toInt)`.
    Empty product is `1`, matching the `sign = 1` seed of `run_at`. -/
private def sign_product_int (arr : RustSlice i64) : Nat → Int
  | 0     => 1
  | k + 1 =>
      sign_product_int arr k *
        (if h : k < arr.val.size then sgn_int (arr.val[k]'h).toInt else 1)

/-! ## Contract theorems. -/

/-- Failure / None clause (proptest `empty_input_returns_none`):
    when the input slice is empty, `prod_signs` returns `None`. -/
theorem empty_returns_none
    (arr : RustSlice i64) (hempty : arr.val.size = 0) :
    clever_127_prod_signs.prod_signs arr
      = RustM.ok core_models.option.Option.None := by
  sorry

/-- Postcondition clause (proptest `matches_spec_formula`):
    on a non-empty input, when every element is not `i64::MIN`
    (so the unary negation in the absolute-value branch is safe) and
    every running absolute-value sum fits in `i64` (so the running
    `sum_abs +? av` does not overflow), the result is `Some r` where
    `r.toInt = (Σ |v_i|) * (Π sgn(v_i))`.

    Bound rationale:
      * `hno_min`: needed so `-? v` in the `v < 0` branch is safe.
      * `hfit`: each running sum of absolute values stays in `[0, 2^63)`,
        so `sum_abs +? av` never overflows.  (The final `sum_abs *? sign`
        with `sign ∈ {-1, 0, 1}` and `sum_abs ∈ [0, 2^63)` is automatically
        safe — no extra precondition needed.)
      * The proptest restricts to `[-50, 50]` with length ≤ 15, picking
        `(sum_abs ≤ 750, |sign_product| ≤ 1)`; this is a strict subset
        of the precondition stated here, which is the natural model-level
        contract that preserves provability. -/
theorem matches_spec_formula
    (arr : RustSlice i64)
    (hne : 0 < arr.val.size)
    (hno_min : ∀ (k : Nat) (h : k < arr.val.size),
                  (arr.val[k]'h) ≠ Int64.minValue)
    (hfit : ∀ k : Nat, k ≤ arr.val.size →
                  sum_abs_int arr k < 2^63) :
    ∃ r : i64,
      clever_127_prod_signs.prod_signs arr
        = RustM.ok (core_models.option.Option.Some r) ∧
      r.toInt = sum_abs_int arr arr.val.size *
                sign_product_int arr arr.val.size := by
  sorry

end Clever_127_prod_signsObligations
