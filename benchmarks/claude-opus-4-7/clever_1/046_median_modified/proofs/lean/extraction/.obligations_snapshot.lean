-- Companion obligations file for the `clever_046_median` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_046_median

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_046_medianObligations

/-! ## Specification oracles: counts of strictly less / strictly greater
    elements in a slice prefix.

`lt_count l m k` is the number of indices `j < k` for which `l.val[j] < m`,
expressed at the `Nat` level. Each top-level theorem applies it with
`k = l.val.size`, so the bounded indices always exist. The `gt_count`
oracle is the symmetric construction for `l.val[j] > m`. -/

private def lt_count (l : RustSlice i64) (m : i64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      if h : k < l.val.size then
        (if (l.val[k]'h) < m then 1 else 0) + lt_count l m k
      else lt_count l m k

private def gt_count (l : RustSlice i64) (m : i64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      if h : k < l.val.size then
        (if (l.val[k]'h) > m then 1 else 0) + gt_count l m k
      else gt_count l m k

/-! ## Top-level obligations on `median`.

Each theorem captures one universal property test in the Rust source.
The specific-input tests `singleton_returns_element` and
`even_length_returns_lower_median` are concrete instances of the count-based
characterisation below; the `matches_brute_force` test is captured by the
two count-bound theorems together (since `lt ≤ half ∧ gt + 1 + half ≤ size`
uniquely characterises the lower median). -/

/-- Boundary clause: on the empty input the function returns the sentinel `0`.
    Captures the property test `empty_returns_zero`. -/
theorem empty_returns_zero
    (l : RustSlice i64) (hempty : l.val.size = 0) :
    clever_046_median.median l = RustM.ok (0 : i64) := by
  sorry

/-- The returned value is one of the elements of the input slice.
    Captures the property test `returned_value_is_in_list`. -/
theorem returned_value_is_in_list
    (l : RustSlice i64) (m : i64)
    (hnonempty : 0 < l.val.size)
    (h : clever_046_median.median l = RustM.ok m) :
    ∃ i : Nat, ∃ (hi : i < l.val.size), l.val[i]'hi = m := by
  sorry

/-- Lower-median characterisation, part 1: the count of strictly-smaller
    elements is bounded by `(size - 1) / 2`. Together with
    `median_gt_count_bound`, this captures the property test
    `matches_brute_force`. -/
theorem median_lt_count_bound
    (l : RustSlice i64) (m : i64)
    (hnonempty : 0 < l.val.size)
    (h : clever_046_median.median l = RustM.ok m) :
    lt_count l m l.val.size ≤ (l.val.size - 1) / 2 := by
  sorry

/-- Lower-median characterisation, part 2: the count of strictly-greater
    elements plus `1 + (size - 1) / 2` is at most `size`. Together with
    `median_lt_count_bound`, captures `matches_brute_force`. -/
theorem median_gt_count_bound
    (l : RustSlice i64) (m : i64)
    (hnonempty : 0 < l.val.size)
    (h : clever_046_median.median l = RustM.ok m) :
    gt_count l m l.val.size + 1 + (l.val.size - 1) / 2 ≤ l.val.size := by
  sorry

end Clever_046_medianObligations
