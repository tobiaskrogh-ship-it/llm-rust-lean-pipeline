-- Companion obligations file for the `clever_051_below_threshold` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_051_below_threshold

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_051_below_thresholdObligations

/-! ## Contract obligations for `below_threshold`

The Rust source has two test suites:

* `empty_is_below_any_threshold` — boundary clause: an empty slice is
  vacuously below any threshold.
* `matches_brute_force` (proptest) — full iff: the function's `Bool`
  result agrees with `∀ x ∈ l. x < t`.  The doc comment in the Rust
  source explicitly notes this "subsumes both soundness (`true ⇒ all <`)
  and completeness (`some ≥ ⇒ false`)", so we split it into the three
  independent directional clauses below.

The function performs only a `usize +? 1` (during recursion, always
inside the size bound `< 2^64`) and signed `>=?` comparisons on `i64`.
Neither can fail in the model, so the contract is stated universally
without any precondition.  Comparisons use `i64`'s native `<` / `≤`,
matching the Hax extraction and the style of
`clever_050_monotonic_modified`. -/

/-- Boundary clause (`empty_is_below_any_threshold`):
    on an empty slice, `below_threshold l t = ok true` for every `t`. -/
theorem empty_returns_true (l : RustSlice i64) (t : i64) (hempty : l.val.size = 0) :
    clever_051_below_threshold.below_threshold l t = RustM.ok true := by
  sorry

/-- Soundness direction of `matches_brute_force`:
    if `below_threshold l t` returns `true`, then every element of `l`
    is strictly less than `t`.

    Rules out an always-`true` short-circuit or an off-by-one that
    accepts a slice containing an element ≥ `t`. -/
theorem below_threshold_sound (l : RustSlice i64) (t : i64)
    (h : clever_051_below_threshold.below_threshold l t = RustM.ok true) :
    ∀ i : Nat, ∀ (hi : i < l.val.size), l.val[i]'hi < t := by
  sorry

/-- Completeness direction of `matches_brute_force`:
    if every element of `l` is strictly less than `t`, then
    `below_threshold l t` returns `true`.

    Rules out an always-`false` short-circuit, or a scan that stops one
    step early and misses the tail. -/
theorem below_threshold_complete (l : RustSlice i64) (t : i64)
    (h : ∀ i : Nat, ∀ (hi : i < l.val.size), l.val[i]'hi < t) :
    clever_051_below_threshold.below_threshold l t = RustM.ok true := by
  sorry

/-- False-direction of `matches_brute_force` (`some ≥ ⇒ false`):
    if some element of `l` is at least `t`, then `below_threshold l t`
    returns `false`.

    Together with `below_threshold_complete`, this captures both halves
    of `prop_assert_eq!(below_threshold(&l, t), naive_below(&l, t))`
    and additionally pins down that the function returns successfully
    (not `fail`) on this branch. -/
theorem below_threshold_returns_false (l : RustSlice i64) (t : i64)
    (h : ∃ i : Nat, ∃ (hi : i < l.val.size), t ≤ l.val[i]'hi) :
    clever_051_below_threshold.below_threshold l t = RustM.ok false := by
  sorry

end Clever_051_below_thresholdObligations
