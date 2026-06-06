-- Companion obligations file for the `clever_059_sum_to_n` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_059_sum_to_n

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_059_sum_to_nObligations

/-- Zero boundary (captures the unit test `zero_yields_zero`):
    `sum_to_n 0` returns `0`. Mirrors the explicit `n == 0` branch in the
    Rust source. -/
theorem sum_to_n_zero :
    clever_059_sum_to_n.sum_to_n 0 = RustM.ok 0 := by
  sorry

/-- Postcondition / closed-form correctness (captures the proptest
    `matches_closed_form`).

    For every `n : u64` whose Gauss closed-form sum `n*(n+1)/2` still
    fits in `u64`, `sum_to_n n` succeeds and returns that closed form.
    The hypothesis acts as the *implicit* precondition: in the tail-
    recursive accumulator, the running sum at step `k` equals
    `(k-1)*k/2`, so the only overflow site `acc + k` overflows
    precisely when the eventual total `n*(n+1)/2` exceeds `2^64`.

    Feasibility note: the proptest bounds `1 ≤ n ≤ 5_000`, but the
    universal Lean statement holds for the much wider true domain
    `n*(n+1)/2 < 2^64` (roughly `n ≤ 6.07·10^9`). Restricting to the
    proptest range would understate the contract; we state the strongest
    honest precondition. Subsumes the `n = 0` case since `0*1/2 = 0`. -/
theorem sum_to_n_closed_form (n : u64)
    (h : n.toNat * (n.toNat + 1) / 2 < 2 ^ 64) :
    clever_059_sum_to_n.sum_to_n n
      = RustM.ok (UInt64.ofNat (n.toNat * (n.toNat + 1) / 2)) := by
  sorry

/-- Failure condition (integer overflow).

    When the Gauss closed-form sum `n*(n+1)/2` exceeds `u64`'s range,
    the accumulator's `acc + k` step computing that sum overflows and
    the function panics with `Error.integerOverflow`. This is the only
    way `sum_to_n` can fail: the `n == 0` boundary is dispatched
    explicitly, and `k + 1` never overflows because the recursion only
    continues when `k ≤ n ≤ u64::MAX`, so `k + 1 ≤ n + 1 ≤ 2^64`. The
    Rust proptest cannot exercise this clause (its bound `n ≤ 5_000`
    is far below the overflow threshold), but the contract is implicit
    in the function's panicking behaviour on the larger domain. -/
theorem sum_to_n_overflow (n : u64)
    (h : 2 ^ 64 ≤ n.toNat * (n.toNat + 1) / 2) :
    clever_059_sum_to_n.sum_to_n n = RustM.fail .integerOverflow := by
  sorry

end Clever_059_sum_to_nObligations
