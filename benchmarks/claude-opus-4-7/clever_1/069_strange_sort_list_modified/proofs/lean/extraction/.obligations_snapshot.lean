-- Companion obligations file for the `clever_069_strange_sort_list` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_069_strange_sort_list

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_069_strange_sort_listObligations

/-! ## Specification oracle for the multiset clause.

`vec_count s target k` counts the number of indices `j < k` for which
`s[j] = target`. The `dite` on `j < s.size` keeps the definition total —
every theorem below applies it with `k = s.size`, so the bounded indices
always exist. Pattern transferred from `clever_036_sort_even`'s
`total_count` / `clever_033_unique`'s `vec_count`. -/

private def vec_count (s : Array i64) (target : i64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      if h : k < s.size then
        (if (s[k]'h) = target then 1 else 0) + vec_count s target k
      else
        vec_count s target k

/-! ## Theorem statements.

The Rust source has three contract-bearing tests:
* The `small_cases` unit test (boundary check `strange_sort_list(&[]) = []`).
* The `matches_brute_force` proptest (output equals a sort-then-alternating-end-pick oracle).
* The `permutation_of_input` proptest (multiset preservation).

The `matches_brute_force` oracle is captured structurally by four
independent clauses on `v` — length preservation, even-position
ascending values, odd-position descending values, and adjacent
even ≤ odd. Together with multiset preservation, these properties
characterise the strange-sort arrangement uniquely (the proof
stage can compose them or prove each from the implementation directly).

Stated universally in the slice size: the function only rearranges
`i64` values, every intermediate `extend_from_slice` keeps each
accumulator bounded by `l.val.size + 1 ≤ 2^64`, so no precondition
on `l.val.size` is required. -/

/-- Anchor: empty input yields a successful empty output. Captures the
    boundary case from the Rust unit test `small_cases`
    (`strange_sort_list(&[]) = []`). -/
theorem strange_sort_list_empty_input_yields_empty_output
    (l : RustSlice i64) (hempty : l.val.size = 0) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_069_strange_sort_list.strange_sort_list l = RustM.ok v ∧
      v.val.size = 0 := by
  sorry

/-- Length-preservation postcondition: `out.len() = l.len()`. Implied by
    the multiset clause, but stated independently because (a) it is the
    simplest functional fact about the output and (b) the
    `matches_brute_force` proptest relies on it via `assert_eq` on
    vectors of the same length. -/
theorem strange_sort_list_length_preserved
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_069_strange_sort_list.strange_sort_list l = RustM.ok v) :
    v.val.size = l.val.size := by
  sorry

/-- Multiset preservation: for every target value, the number of
    occurrences in the output equals the number in the input. Captures
    the Rust proptest `permutation_of_input` (which sorts both sides
    and asserts equality — equivalent to multiset equality). -/
theorem strange_sort_list_multiset_preserved
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_069_strange_sort_list.strange_sort_list l = RustM.ok v)
    (target : i64) :
    vec_count v.val target v.val.size = vec_count l.val target l.val.size := by
  sorry

/-- Even-position ascending: at consecutive even output positions `k`
    and `k + 2`, the values are non-decreasing. Captures the "even
    slots carry the ascending lower half of the sorted input" facet of
    the Rust proptest `matches_brute_force`. -/
theorem strange_sort_list_even_indices_ascending
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_069_strange_sort_list.strange_sort_list l = RustM.ok v)
    (k : Nat) (hk : k + 2 < v.val.size) (heven : k % 2 = 0) :
    (v.val[k]'(Nat.lt_of_succ_lt (Nat.lt_of_succ_lt hk))).toInt ≤
      (v.val[k + 2]'hk).toInt := by
  sorry

/-- Odd-position descending: at consecutive odd output positions `k`
    and `k + 2`, the values are non-increasing. Captures the "odd
    slots carry the descending upper half of the sorted input" facet
    of the Rust proptest `matches_brute_force`. -/
theorem strange_sort_list_odd_indices_descending
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_069_strange_sort_list.strange_sort_list l = RustM.ok v)
    (k : Nat) (hk : k + 2 < v.val.size) (hodd : k % 2 = 1) :
    (v.val[k + 2]'hk).toInt ≤
      (v.val[k]'(Nat.lt_of_succ_lt (Nat.lt_of_succ_lt hk))).toInt := by
  sorry

/-- Adjacent cross relation: at each even position `2 * k` paired with
    its immediate odd successor `2 * k + 1`, the even value does not
    exceed the odd value. Captures the "min from the bottom, max from
    the top" cross-clause of the Rust proptest `matches_brute_force`;
    together with the even/odd monotonicity clauses and multiset
    preservation, this pins the arrangement down to the strange-sort
    oracle. -/
theorem strange_sort_list_even_le_adjacent_odd
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_069_strange_sort_list.strange_sort_list l = RustM.ok v)
    (k : Nat) (hk : 2 * k + 1 < v.val.size) :
    (v.val[2 * k]'(Nat.lt_of_succ_lt hk)).toInt ≤
      (v.val[2 * k + 1]'hk).toInt := by
  sorry

end Clever_069_strange_sort_listObligations
