-- Companion obligations file for the `clever_067_pluck` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_067_pluck

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_067_pluckObligations

/-! ## Predicates used in the contract. -/

/-- An `i64` value is even (the spec interprets `l[i] % 2 == 0` in `Int`;
    since the test compares to `0`, this is sign-agnostic). -/
private abbrev isEven (x : i64) : Prop := x.toInt % 2 = 0

/-- There exists an even element in `s`. -/
private abbrev hasEven (s : RustSlice i64) : Prop :=
  ∃ (i : Nat) (hi : i < s.val.size), isEven (s.val[i]'hi)

/-! ## Obligations.

The `pluck` function always succeeds (no failing operations on the path:
all `usize +? 1` increments respect the slice bound, the casts
`usize → u64` and `u64 → i64` are total wrapping conversions, and the
`extend_from_slice` of a fixed 2-element chunk onto a freshly-allocated
empty `Vec` doesn't overflow). The contract clauses below describe the
*postconditions* on the returned vector. -/

/-- Boundary: when `s` contains no even element (e.g. empty input or all-odd
    input), `pluck` returns an empty vector.
    Covers Rust tests `empty_returns_empty` and `all_odd_returns_empty`. -/
theorem pluck_no_even_returns_empty
    (s : RustSlice i64)
    (hno : ¬ hasEven s) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_067_pluck.pluck s = RustM.ok v ∧ v.val.size = 0 := by
  sorry

/-- Existence characterization: the result is non-empty exactly when `s`
    contains an even element. Covers Rust proptest `nonempty_iff_has_even`. -/
theorem pluck_nonempty_iff_has_even
    (s : RustSlice i64) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_067_pluck.pluck s = RustM.ok v ∧
      (v.val.size ≠ 0 ↔ hasEven s) := by
  sorry

/-- Output-shape clause (size): a non-empty result has size exactly `2`
    (the `[value, index]` pair). Covers the first sub-clause of Rust
    proptest `output_shape`. -/
theorem pluck_nonempty_size_two
    (s : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_067_pluck.pluck s = RustM.ok v)
    (hne : v.val.size ≠ 0) :
    v.val.size = 2 := by
  sorry

/-- Output-shape clause (index non-negative): when the result is non-empty,
    the index slot is non-negative. This requires the size of `s` to fit in
    the positive `i64` range so the `u64 → i64` cast doesn't wrap.
    Covers the `r[1] >= 0` sub-clause of `output_shape`. -/
theorem pluck_nonempty_index_nonneg
    (s : RustSlice i64)
    (hbnd : s.val.size ≤ 2 ^ 63)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_067_pluck.pluck s = RustM.ok v)
    (hne : v.val.size ≠ 0)
    (h1 : 1 < v.val.size) :
    0 ≤ (v.val[1]'h1).toInt := by
  sorry

/-- Output-shape clause (index in bounds): when the result is non-empty,
    the index slot, viewed as an `Int`, is a valid position into `s`.
    Covers the `(r[1] as usize) < l.len()` sub-clause of `output_shape`. -/
theorem pluck_nonempty_index_in_bounds
    (s : RustSlice i64)
    (hbnd : s.val.size ≤ 2 ^ 63)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_067_pluck.pluck s = RustM.ok v)
    (hne : v.val.size ≠ 0)
    (h1 : 1 < v.val.size) :
    (v.val[1]'h1).toInt < (s.val.size : Int) := by
  sorry

/-- Value-clause (parity): when the result is non-empty, the value slot
    `v[0]` is even. Covers the `v % 2 == 0` sub-clause of Rust proptest
    `value_is_minimum_even`. -/
theorem pluck_nonempty_value_is_even
    (s : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_067_pluck.pluck s = RustM.ok v)
    (hne : v.val.size ≠ 0)
    (h0 : 0 < v.val.size) :
    isEven (v.val[0]'h0) := by
  sorry

/-- Value-clause (minimality): when the result is non-empty, the value slot
    `v[0]` is at most every even element of `s`. Covers the `v ≤ x` sub-clause
    of Rust proptest `value_is_minimum_even`. -/
theorem pluck_nonempty_value_is_minimum_even
    (s : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_067_pluck.pluck s = RustM.ok v)
    (hne : v.val.size ≠ 0)
    (h0 : 0 < v.val.size) :
    ∀ (i : Nat) (hi : i < s.val.size),
      isEven (s.val[i]'hi) → (v.val[0]'h0).toInt ≤ (s.val[i]'hi).toInt := by
  sorry

/-- Index-clause (points to value): when the result is non-empty, the index
    slot identifies a position in `s` whose element equals the value slot.
    Covers the `l[i] == v` sub-clause of Rust proptest `index_is_first_occurrence`. -/
theorem pluck_nonempty_index_points_to_value
    (s : RustSlice i64)
    (hbnd : s.val.size ≤ 2 ^ 63)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_067_pluck.pluck s = RustM.ok v)
    (hne : v.val.size ≠ 0)
    (h0 : 0 < v.val.size) (h1 : 1 < v.val.size)
    (hbd : (v.val[1]'h1).toInt.toNat < s.val.size) :
    (s.val[(v.val[1]'h1).toInt.toNat]'hbd) = (v.val[0]'h0) := by
  sorry

/-- Index-clause (first occurrence): when the result is non-empty, no
    position strictly earlier than the index slot holds the value slot.
    Covers the `l[j] != v` sub-clause (tie-break on smallest index) of
    Rust proptest `index_is_first_occurrence`. -/
theorem pluck_nonempty_index_is_first_occurrence
    (s : RustSlice i64)
    (hbnd : s.val.size ≤ 2 ^ 63)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_067_pluck.pluck s = RustM.ok v)
    (hne : v.val.size ≠ 0)
    (h0 : 0 < v.val.size) (h1 : 1 < v.val.size) :
    ∀ (j : Nat) (hj : j < s.val.size),
      (j : Int) < (v.val[1]'h1).toInt → (s.val[j]'hj) ≠ (v.val[0]'h0) := by
  sorry

end Clever_067_pluckObligations
