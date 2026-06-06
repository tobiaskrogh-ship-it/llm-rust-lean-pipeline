-- Companion obligations file for the `clever_033_unique` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_033_unique

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_033_uniqueObligations

/-! ## Contract clauses

The Rust source contains one anchor unit test and three property tests in
`mod tests`:

  * `empty_input_yields_empty_output`        — anchor: `unique(&[]) = []`.
  * `output_is_strictly_increasing`          — postcondition 1: consecutive
                                                output entries are strictly
                                                increasing (sortedness +
                                                no duplicates).
  * `output_contains_every_input_element`    — postcondition 2: every input
                                                element appears in the output.
  * `output_only_contains_input_elements`    — postcondition 3: every output
                                                element appears in the input.

Statement style: the three positive postconditions take the function's
`RustM.ok v` result as a hypothesis (`hres`) and assert the property on `v`.
This matches the result-conditional shape used in
`clever_025_remove_duplicates` and `clever_009_rolling_max`. It keeps the
contract surface portable in the face of model-level overflow concerns
(very large slices could in principle overflow the `extend_from_slice` size
check or the `usize +? 1` index step); the proof stage discharges any
overflow obligations from the `hres` hypothesis without forcing a precise
precondition into the contract surface.

The anchor test is stated equationally as a failure / boundary clause
(`unique l = RustM.ok ⟨#[], _⟩` when `l.val.size = 0`), with no `hres`
hypothesis — the proof stage must establish totality at the empty input. -/

/-! ## Anchor: empty input yields empty output. -/

/-- Anchor unit test: `unique(&[]) = []`. The function succeeds on the
    empty slice and returns a `Vec` of size `0`. Captures the Rust unit
    test `empty_input_yields_empty_output`. -/
theorem empty_input_yields_empty_output
    (l : RustSlice i64) (hempty : l.val.size = 0) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_033_unique.unique l = RustM.ok v ∧ v.val.size = 0 := by
  sorry

/-! ## Postcondition 1: output is strictly increasing.

Stated on consecutive entries (`k`, `k+1`) — matching the proptest's
`windows(2)` form. Strict ordering captures BOTH "sorted ascending" and
"no duplicates" in one clause, exactly as the proptest comment notes. -/

/-- Postcondition 1: consecutive output entries are strictly increasing.
    Captures the proptest `output_is_strictly_increasing`. -/
theorem output_is_strictly_increasing
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_033_unique.unique l = RustM.ok v)
    (k : Nat) (hk : k + 1 < v.val.size) :
    (v.val[k]'(Nat.lt_of_succ_lt hk)).toInt < (v.val[k + 1]'hk).toInt := by
  sorry

/-! ## Postcondition 2: every input element appears in the output.

Existential index witness: for each input position `i`, there is some
output position `k` with `v[k] = l[i]`. Matches the proptest's
`out.contains(x)` check translated to an index witness. -/

/-- Postcondition 2: every input element appears somewhere in the output.
    Captures the proptest `output_contains_every_input_element`. -/
theorem output_contains_every_input_element
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_033_unique.unique l = RustM.ok v)
    (i : Nat) (hi : i < l.val.size) :
    ∃ (k : Nat) (hk : k < v.val.size), v.val[k]'hk = l.val[i]'hi := by
  sorry

/-! ## Postcondition 3: every output element came from the input.

Existential index witness: for each output position `k`, there is some
input position `i` with `l[i] = v[k]`. Matches the proptest's
`l.contains(y)` check translated to an index witness. -/

/-- Postcondition 3: every output element occurs in the input.
    Captures the proptest `output_only_contains_input_elements`. -/
theorem output_only_contains_input_elements
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_033_unique.unique l = RustM.ok v)
    (k : Nat) (hk : k < v.val.size) :
    ∃ (i : Nat) (hi : i < l.val.size), l.val[i]'hi = v.val[k]'hk := by
  sorry

end Clever_033_uniqueObligations
