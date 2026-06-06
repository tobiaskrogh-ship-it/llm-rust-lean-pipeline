-- Companion obligations file for the `clever_036_sort_even` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_036_sort_even

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_036_sort_evenObligations

/-! ## Specification oracle for the multiset clause.

`count_evens s target k` is the number of indices `j < k` for which
`j` is even and `s[j] = target`. The `dite` on `j < s.size` keeps the
definition total — every theorem below applies it with `k = s.size`,
so the bounded indices always exist. Pattern reused from
`clever_025_remove_duplicates`'s `total_count`. -/

private def count_evens (s : Array i64) (target : i64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      if h : k < s.size then
        (if k % 2 = 0 ∧ (s[k]'h) = target then 1 else 0)
          + count_evens s target k
      else
        count_evens s target k

/-! ## Theorem statements.

Each of the five obligations below corresponds to one property test in
the Rust source. Proofs are `sorry` and are filled in by the proof
stage. Stated universally in the slice size: the function only shuffles
`i64` values (no value-level arithmetic), and every intermediate
`extend_from_slice` keeps the accumulator bounded by `2^64` (the
half-size `sorted` vec built by `collect_evens` reaches at most
`(l.val.size + 1) / 2 ≤ 2^63`, and the final `rebuild_at` accumulator
reaches at most `l.val.size < 2^64`), so no precondition on
`l.val.size` is required. -/

/-- Anchor: empty input yields a successful empty output. Captures the
    Rust unit test `empty_input`. -/
theorem sort_even_empty_input_yields_empty_output
    (l : RustSlice i64) (hempty : l.val.size = 0) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_036_sort_even.sort_even l = RustM.ok v ∧ v.val.size = 0 := sorry

/-- Length-preservation postcondition: `out.len() = l.len()`. Captures
    the Rust proptest `length_preserved`. -/
theorem sort_even_length_preserved
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_036_sort_even.sort_even l = RustM.ok v) :
    v.val.size = l.val.size := sorry

/-- Odd-index identity postcondition: at every odd index `i`, the output
    equals the input pointwise. Captures the Rust proptest
    `odd_indices_unchanged`. -/
theorem sort_even_odd_indices_unchanged
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_036_sort_even.sort_even l = RustM.ok v)
    (i : Nat) (hi_v : i < v.val.size) (hi_l : i < l.val.size)
    (hodd : i % 2 = 1) :
    v.val[i]'hi_v = l.val[i]'hi_l := sorry

/-- Even-index sorted postcondition: at consecutive even output
    positions `k` and `k + 2`, the values are non-decreasing. Stated on
    pairs of stride-2 entries — exactly the proptest's `windows(2)` form
    over the `step_by(2)` projection. Captures the Rust proptest
    `even_indices_sorted`. -/
theorem sort_even_even_indices_sorted
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_036_sort_even.sort_even l = RustM.ok v)
    (k : Nat) (hk : k + 2 < v.val.size) (heven : k % 2 = 0) :
    (v.val[k]'(Nat.lt_of_succ_lt (Nat.lt_of_succ_lt hk))).toInt ≤
      (v.val[k + 2]'hk).toInt := sorry

/-- Even-index multiset preservation: for every target value, the
    number of occurrences at even output positions equals the number at
    even input positions. Captures the Rust proptest
    `even_indices_multiset_preserved`. Independent from
    `sort_even_even_indices_sorted`: catches implementations that
    produce a sorted-but-wrong sequence (e.g. all zeros) at even
    positions. -/
theorem sort_even_even_indices_multiset_preserved
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_036_sort_even.sort_even l = RustM.ok v)
    (target : i64) :
    count_evens v.val target v.val.size = count_evens l.val target l.val.size := sorry

end Clever_036_sort_evenObligations
