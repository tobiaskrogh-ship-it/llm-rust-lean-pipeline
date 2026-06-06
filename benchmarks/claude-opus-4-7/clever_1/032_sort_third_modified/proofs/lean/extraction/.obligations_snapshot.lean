-- Companion obligations file for the `clever_032_sort_third` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_032_sort_third

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_032_sort_thirdObligations

/-! ## Specification oracle: count occurrences of a value at third-divisible
     indices of a slice/array.

`third_count a x k` is the number of indices `j < k` for which `j % 3 = 0`
AND `a[j] = x`. The `dite` on `j < a.size` keeps the definition total —
every theorem below applies it with `k = a.size`, so the indices always
exist. Pattern transferred from `clever_025_remove_duplicates`'
`total_count` oracle. -/

private def third_count (a : Array i64) (x : i64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      if h : k < a.size then
        (if k % 3 = 0 ∧ (a[k]'h) = x then 1 else 0) + third_count a x k
      else
        third_count a x k

/-! ## Top-level obligations on `sort_third`.

Each theorem corresponds to one property test in the Rust source. The
signatures take the function's `RustM.ok` result as a hypothesis (the
`rolling_max` / `remove_duplicates` style), so they speak about the value
returned whenever the call succeeds. A separate `sort_third_total`
theorem captures the implicit totality assumption of the proptests. -/

/-- Totality: `sort_third` returns an `ok` value for every input slice.

`RustSlice` invariants give `l.val.size < 2^64`, so all recursive
counter increments stay within `usize`, and `extend_from_slice` never
overflows the accumulator (max final size = `l.val.size`).

Captures the proptests' implicit assumption that the call does not
panic. -/
theorem sort_third_total (l : RustSlice i64) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_032_sort_third.sort_third l = RustM.ok v := by
  sorry

/-- Length-preservation postcondition: the output has the same length
    as the input. Captures the proptest `length_preserved`. -/
theorem length_preserved
    (l : RustSlice i64) (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_032_sort_third.sort_third l = RustM.ok v) :
    v.val.size = l.val.size := by
  sorry

/-- Non-third indices are preserved elementwise: at every position
    `i < l.val.size` with `i % 3 ≠ 0`, the output equals the input.
    Captures the proptest `non_third_indices_unchanged`. -/
theorem non_third_indices_unchanged
    (l : RustSlice i64) (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_032_sort_third.sort_third l = RustM.ok v)
    (i : Nat) (hi_l : i < l.val.size) (hi_v : i < v.val.size)
    (hmod : i % 3 ≠ 0) :
    v.val[i]'hi_v = l.val[i]'hi_l := by
  sorry

/-- Values at indices divisible by 3 are in ascending order in the
    output: for any pair of such indices `i < j` (both `< v.val.size`),
    the output value at `i` is `≤` the output value at `j`. The
    proptest uses `windows(2)`, which is equivalent to this pairwise
    statement when applied to the strictly-increasing third-index
    sequence `0, 3, 6, …`. Captures `third_indices_sorted`. -/
theorem third_indices_sorted
    (l : RustSlice i64) (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_032_sort_third.sort_third l = RustM.ok v)
    (i j : Nat) (hi_v : i < v.val.size) (hj_v : j < v.val.size)
    (hi_mod : i % 3 = 0) (hj_mod : j % 3 = 0) (hlt : i < j) :
    (v.val[i]'hi_v).toInt ≤ (v.val[j]'hj_v).toInt := by
  sorry

/-- Multiset of values at third-divisible indices is preserved between
    input and output. For every target value `x`, the count of `i`
    with `i % 3 = 0` and `a[i] = x` is the same in `l` and `v`. This
    is exactly multiset equality expressed via the `third_count`
    spec oracle, matching the Rust test that sorts both sides and
    compares them as `Vec<i64>`. Captures
    `third_indices_are_permutation`. -/
theorem third_indices_are_permutation
    (l : RustSlice i64) (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_032_sort_third.sort_third l = RustM.ok v)
    (x : i64) :
    third_count v.val x v.val.size = third_count l.val x l.val.size := by
  sorry

end Clever_032_sort_thirdObligations
