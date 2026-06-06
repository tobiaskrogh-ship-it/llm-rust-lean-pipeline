-- Companion obligations file for the `clever_076_iscube` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_076_iscube

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_076_iscubeObligations

/-! ## Contract clauses derived from the Rust property tests.

  * `small_cases` — 13 unit pins (9 cubes / 4 non-cubes) on specific
    values: `iscube` returns `true` on `0, 1, 8, 27, 64, 125, -1, -8, -27`
    and `false` on `2, 9, 26, 28`.
  * `matches_brute_force` — main equivalence with a naive oracle on
    `n.toInt ∈ [-2^30, 2^30]`.  Bracketed by `iscube_sound` (true →
    witness exists) together with `iscube_non_cubes_rejected` (no
    witness, safe range → false) and `iscube_actual_cubes_recognized`
    (witness present, safe range → true).
  * `soundness` — every `ok true` is justified by an integer witness.
  * `completeness` — every cube `k³` with `|k| ≤ 1024` is recognised.

### Feasibility notes

`cube_walks_to` computes `k * k * k` at each step and recurses with
`k + 1`.  The genuine failure modes in the i64 model are:

  1. Signed multiplication overflow at `k *? k` and `(k*k) *? k`
     (fires once `|k|` approaches `2^21`, since `(2^21)^3 = 2^63`).
  2. Signed addition overflow at `k +? 1` (fires at `k = i64::MAX`).
  3. The wrapper's `-? n` unary negation overflow at `n = i64::MIN`.

  * **Soundness** is universally feasible: an `ok true` from the wrapper
    constrains the inner trace of cube values to expose the witness.
    No precondition is needed.
  * **Completeness** at a cube `k³` requires the walk to reach
    `k.natAbs` without overflow.  `|k| ≤ 1024` makes every intermediate
    cube fit easily in i64 (max `1024^3 = 2^30`), matching the
    proptest's bound.
  * **Non-recognition** (`n` not a cube → `ok false`) requires the
    walk to overshoot before any overflow fires.  `|n.toInt| ≤ 2^30`
    keeps the walk to `k ≤ 1025` (since `1024^3 = 2^30 ≤ |n|`
    forces the walker to test up to `1025^3`), well within the i64
    cubing range, and rules out the `-? n` panic at `i64::MIN`. -/

/-! ## Unit pins from the `small_cases` test.

These are sanity pins on specific values.  `iscube` evaluates
end-to-end through the `partial_fixpoint` kernel, so each pin is
dischargeable by `native_decide`. -/

/-- `iscube(0) = true` (since `0³ = 0`). -/
theorem iscube_0_true :
    clever_076_iscube.iscube (0 : i64) = RustM.ok true := by native_decide

/-- `iscube(1) = true` (since `1³ = 1`). -/
theorem iscube_1_true :
    clever_076_iscube.iscube (1 : i64) = RustM.ok true := by native_decide

/-- `iscube(8) = true` (since `2³ = 8`). -/
theorem iscube_8_true :
    clever_076_iscube.iscube (8 : i64) = RustM.ok true := by native_decide

/-- `iscube(27) = true` (since `3³ = 27`). -/
theorem iscube_27_true :
    clever_076_iscube.iscube (27 : i64) = RustM.ok true := by native_decide

/-- `iscube(64) = true` (since `4³ = 64`). -/
theorem iscube_64_true :
    clever_076_iscube.iscube (64 : i64) = RustM.ok true := by native_decide

/-- `iscube(125) = true` (since `5³ = 125`). -/
theorem iscube_125_true :
    clever_076_iscube.iscube (125 : i64) = RustM.ok true := by native_decide

/-- `iscube(-1) = true` (since `(-1)³ = -1`). -/
theorem iscube_neg_1_true :
    clever_076_iscube.iscube (-1 : i64) = RustM.ok true := by native_decide

/-- `iscube(-8) = true` (since `(-2)³ = -8`). -/
theorem iscube_neg_8_true :
    clever_076_iscube.iscube (-8 : i64) = RustM.ok true := by native_decide

/-- `iscube(-27) = true` (since `(-3)³ = -27`). -/
theorem iscube_neg_27_true :
    clever_076_iscube.iscube (-27 : i64) = RustM.ok true := by native_decide

/-- `iscube(2) = false`. -/
theorem iscube_2_false :
    clever_076_iscube.iscube (2 : i64) = RustM.ok false := by native_decide

/-- `iscube(9) = false`. -/
theorem iscube_9_false :
    clever_076_iscube.iscube (9 : i64) = RustM.ok false := by native_decide

/-- `iscube(26) = false`. -/
theorem iscube_26_false :
    clever_076_iscube.iscube (26 : i64) = RustM.ok false := by native_decide

/-- `iscube(28) = false`. -/
theorem iscube_28_false :
    clever_076_iscube.iscube (28 : i64) = RustM.ok false := by native_decide

/-! ## Soundness: every `ok true` is witnessed by an integer cube root.

If `iscube n` returns `true`, there exists an integer `k` with
`k * k * k = n.toInt`.  Universal: a successful `ok true` already
constrains the inner trace of `cube` values to expose the witness;
for `n < 0` the witness is the negation of the inner walk's terminal
counter.  Captures the proptest `soundness`. -/
theorem iscube_sound (n : i64)
    (h : clever_076_iscube.iscube n = RustM.ok true) :
    ∃ k : Int, k * k * k = n.toInt := by
  sorry

/-! ## Completeness: every actual cube is recognised.

For every integer `k` with `|k| ≤ 1024`, `iscube` on the i64 lift of
`k³` returns `true`.  The bound keeps both the input and every
intermediate cube within i64 (since `1024^3 = 2^30 ≪ 2^63`).
Captures the proptest `completeness`. -/
theorem iscube_actual_cubes_recognized (k : Int)
    (h_lo : -1024 ≤ k) (h_hi : k ≤ 1024) :
    clever_076_iscube.iscube (Int64.ofInt (k * k * k)) = RustM.ok true := by
  sorry

/-! ## Non-recognition on the safe range.

If `n.toInt ∈ [-2^30, 2^30]` and `n` is not a perfect integer cube,
`iscube n` returns `false`.  The bound matches the proptest's
`matches_brute_force` range and keeps every cube computed during the
walk inside i64; it also rules out `n = i64::MIN` so the wrapper's
`-? n` cannot panic.  Together with `iscube_actual_cubes_recognized`
and `iscube_sound`, captures the bidirectional content of the
`matches_brute_force` proptest. -/
theorem iscube_non_cubes_rejected (n : i64)
    (h_lo : -(2 ^ 30 : Int) ≤ n.toInt)
    (h_hi : n.toInt ≤ 2 ^ 30)
    (h_not_cube : ¬ ∃ k : Int, k * k * k = n.toInt) :
    clever_076_iscube.iscube n = RustM.ok false := by
  sorry

end Clever_076_iscubeObligations
