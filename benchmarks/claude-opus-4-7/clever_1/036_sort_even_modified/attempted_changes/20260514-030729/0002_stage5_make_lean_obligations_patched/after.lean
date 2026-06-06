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

/-! ## Specification oracle: occurrence count at even-indexed positions.

For an `Array i64` `arr` and a value `target`, `count_at_even arr target k`
counts the number of indices `j < k` with `j` even and `arr[j] = target`.
The `dite` keeps the definition total — in actual use, every theorem below
applies it with `k ≤ arr.size`, keeping every checked index in range.

This is the analogue of `total_count` from `clever_025_remove_duplicates`
restricted to even positions. The multiset-equality contract clause is
expressed by saying this count agrees on the input slice and the output
`Vec` for every target — i.e. the function induces a bijection on even
indices (per the "rearrangement" claim of the postcondition). -/

private def count_at_even (arr : Array i64) (target : i64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      if h : k < arr.size then
        (if k % 2 = 0 ∧ (arr[k]'h) = target then 1 else 0)
          + count_at_even arr target k
      else
        count_at_even arr target k

/-! ## Top-level contract clauses.

The Rust source contains four proptest contract clauses and one boundary
unit test. Each becomes one independent theorem below.

* `length_preserved` (proptest)              — `out.len() == l.len()`.
* `odd_indices_unchanged` (proptest)         — `out[i] == l[i]` for odd `i`.
* `even_indices_sorted` (proptest)           — output even-indexed values
                                                are non-decreasing.
* `even_indices_multiset_preserved` (proptest) — multiset of even-indexed
                                                  values is preserved.
* `empty_input_returns_empty` (unit test)    — `sort_even(&[])` returns
                                                an empty `Vec`. -/

/-- Length-preservation postcondition (also packages totality).
    Captures the proptest `length_preserved`. -/
theorem length_preserved
    (l : RustSlice i64) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_036_sort_even.sort_even l = RustM.ok v ∧
      v.val.size = l.val.size := by
  sorry

/-- Odd-index-preservation postcondition: at every odd in-range position
    the output equals the input pointwise.  Captures the proptest
    `odd_indices_unchanged`. -/
theorem odd_indices_unchanged
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_036_sort_even.sort_even l = RustM.ok v)
    (i : Nat) (h_v : i < v.val.size) (h_l : i < l.val.size)
    (hodd : i % 2 = 1) :
    v.val[i]'h_v = l.val[i]'h_l := by
  sorry

/-- Even-index sortedness postcondition: consecutive even-indexed output
    values are non-decreasing (i.e. `out[0] ≤ out[2] ≤ out[4] ≤ …`).
    Captures the proptest `even_indices_sorted`. -/
theorem even_indices_sorted
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_036_sort_even.sort_even l = RustM.ok v)
    (i : Nat) (h_v_i : i < v.val.size) (h_v_i2 : i + 2 < v.val.size)
    (heven : i % 2 = 0) :
    (v.val[i]'h_v_i).toInt ≤ (v.val[i + 2]'h_v_i2).toInt := by
  sorry

/-- Multiset-preservation postcondition for even-indexed values: for every
    value `target`, the number of even-indexed occurrences in the output
    equals that in the input.  Captures the proptest
    `even_indices_multiset_preserved`. -/
theorem even_indices_multiset_preserved
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_036_sort_even.sort_even l = RustM.ok v)
    (target : i64) :
    count_at_even v.val target v.val.size =
      count_at_even l.val target l.val.size := by
  sorry

/-- Empty-input boundary clause: when the input slice is empty, `sort_even`
    returns successfully an empty `Vec`.  Captures the unit test
    `empty_input` (function is total — no panic on `&[]`). -/
theorem empty_input_returns_empty
    (l : RustSlice i64) (hempty : l.val.size = 0) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_036_sort_even.sort_even l = RustM.ok v ∧ v.val.size = 0 := by
  sorry

end Clever_036_sort_evenObligations
