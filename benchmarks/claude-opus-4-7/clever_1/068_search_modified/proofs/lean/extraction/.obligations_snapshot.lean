-- Companion obligations file for the `clever_068_search` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_068_search

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_068_searchObligations

/-! ## Specification oracle: count of occurrences of `v` in a slice tail.

`count_occ_from l v i` is the number of indices `j ∈ [i, l.val.size)` with
`l.val[j] = v`, expressed at the `Nat` level. The top-level theorems apply
it with `i = 0`. This matches the operational behaviour of the extracted
`count_occurrences l v i`, modulo the Nat/u64 conversion. -/

private def count_occ_from (l : RustSlice u64) (v : u64) (i : Nat) : Nat :=
  if h : i < l.val.size then
    (if l.val[i]'h = v then 1 else 0) + count_occ_from l v (i + 1)
  else 0
termination_by l.val.size - i

/-- Boundary clause: on the empty input the function returns the sentinel `0`.

    Concrete case from the `small_cases` test (`search(&[]) == 0`). On an
    empty slice the outer `search_at` immediately hits the `i >= len`
    branch and returns the initial `best = 0`. -/
theorem empty_returns_zero
    (numbers : RustSlice u64) (hempty : numbers.val.size = 0) :
    clever_068_search.search numbers = RustM.ok (0 : u64) := by
  sorry

/-- Frequency invariant: if `search numbers` returns a positive value `r`,
    then `r` occurs at least `r` times in `numbers`.

    Captures the property test `frequency_invariant`:
    ```
    if r > 0 {
      let freq = l.iter().filter(|&&x| x == r).count() as u64;
      prop_assert!(freq >= r);
    }
    ```
    A buggy implementation that returns a positive `r` whose actual
    frequency is below `r` (e.g. an off-by-one in the count, or returning
    the maximum instead of the most-frequent-above-threshold) would
    falsify this. -/
theorem frequency_invariant
    (numbers : RustSlice u64) (r : u64)
    (h : clever_068_search.search numbers = RustM.ok r)
    (hr : (0 : u64) < r) :
    r.toNat ≤ count_occ_from numbers r 0 := by
  sorry

/-- Maximality: no value strictly greater than the result, occurring in
    `numbers`, satisfies the "frequency ≥ self" condition.

    Captures the property test `maximality`:
    ```
    for &v in &l {
      if v > r {
        let freq = l.iter().filter(|&&x| x == v).count() as u64;
        prop_assert!(freq < v);
      }
    }
    ```
    Together with `frequency_invariant` this pins down the result as
    *the greatest* positive value whose frequency reaches itself (and
    handles the `r = 0` case: no positive `v` in `numbers` has
    `count(v) ≥ v`). A buggy implementation that returns a smaller
    value than some legitimate winner (e.g. exits the scan early, or
    fails to update `best`) would falsify this. -/
theorem maximality
    (numbers : RustSlice u64) (r : u64)
    (h : clever_068_search.search numbers = RustM.ok r) :
    ∀ i : Nat, ∀ (hi : i < numbers.val.size),
      r < (numbers.val[i]'hi) →
      count_occ_from numbers (numbers.val[i]'hi) 0
        < (numbers.val[i]'hi).toNat := by
  sorry

end Clever_068_searchObligations
