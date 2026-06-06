-- Companion obligations file for the `clever_086_get_coords_sorted` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_086_get_coords_sorted

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_086_get_coords_sortedObligations

/-! ## Specification of `get_coords_sorted`.

The Rust function walks a jagged matrix `lst : &[&[i64]]` and returns the
list of `(row, col)` coordinates of every cell whose value equals `x`,
sorted by row ascending and (within a row) by column descending.

Because the emitted indices are `i64` values obtained from `usize` casts,
the natural Lean theorems are only true when both the row count and every
row length fit in the positive `i64` range — otherwise the cast wraps and
breaks both the equality with the original index and the comparison order.
Each theorem therefore takes:

* `hres   : ... = RustM.ok v`                 — successful execution,
* `hrows  : lst.val.size ≤ 2^63`              — row index cast preserves value,
* `hcols  : ∀ i hi, (lst.val[i]'hi).val.size ≤ 2^63` — column cast preserves value.

These are the minimal conditions under which the universal statement holds.
-/

/-- **Soundness** (proptest `returned_coords_point_to_x`).

Every output coordinate `(r, c)` in `v` corresponds to a valid cell of `lst`
whose value is `x`. Bundling the bounds and the value-equality is forced by
the dependency between them: you need the row index in range to look up the
row, and the column index in range to look up the value. -/
theorem returned_coords_point_to_x
    (lst : RustSlice (RustSlice i64)) (x : i64)
    (v : alloc.vec.Vec (rust_primitives.hax.Tuple2 i64 i64) alloc.alloc.Global)
    (hres : clever_086_get_coords_sorted.get_coords_sorted lst x = RustM.ok v)
    (hrows : lst.val.size ≤ 2^63)
    (hcols : ∀ (i : Nat) (hi : i < lst.val.size), (lst.val[i]'hi).val.size ≤ 2^63)
    (k : Nat) (hk : k < v.val.size) :
    ∃ (i : Nat) (j : Nat) (hi : i < lst.val.size)
      (hj : j < (lst.val[i]'hi).val.size),
      (v.val[k]'hk)._0.toInt = (i : Int) ∧
      (v.val[k]'hk)._1.toInt = (j : Int) ∧
      ((lst.val[i]'hi).val[j]'hj) = x := by
  sorry

/-- **Completeness** (proptest `every_occurrence_is_reported`).

Every cell of `lst` containing `x` is reported in `v` as a coordinate
whose `i64` projections match the (cast of the) cell's natural-number
indices. Combined with soundness this pins down the output multiset. -/
theorem every_occurrence_is_reported
    (lst : RustSlice (RustSlice i64)) (x : i64)
    (v : alloc.vec.Vec (rust_primitives.hax.Tuple2 i64 i64) alloc.alloc.Global)
    (hres : clever_086_get_coords_sorted.get_coords_sorted lst x = RustM.ok v)
    (hrows : lst.val.size ≤ 2^63)
    (hcols : ∀ (i : Nat) (hi : i < lst.val.size), (lst.val[i]'hi).val.size ≤ 2^63)
    (i j : Nat) (hi : i < lst.val.size) (hj : j < (lst.val[i]'hi).val.size)
    (hval : ((lst.val[i]'hi).val[j]'hj) = x) :
    ∃ (k : Nat) (hk : k < v.val.size),
      (v.val[k]'hk)._0.toInt = (i : Int) ∧
      (v.val[k]'hk)._1.toInt = (j : Int) := by
  sorry

/-- **Row order** (proptest `rows_are_non_decreasing`).

Consecutive entries in the output have non-decreasing row indices.
Stated directly on the emitted `i64` values; under `hrows` the i64 order
agrees with the underlying `Nat` order. -/
theorem rows_are_non_decreasing
    (lst : RustSlice (RustSlice i64)) (x : i64)
    (v : alloc.vec.Vec (rust_primitives.hax.Tuple2 i64 i64) alloc.alloc.Global)
    (hres : clever_086_get_coords_sorted.get_coords_sorted lst x = RustM.ok v)
    (hrows : lst.val.size ≤ 2^63)
    (k : Nat) (hk : k + 1 < v.val.size) :
    (v.val[k]'(Nat.lt_of_succ_lt hk))._0.toInt ≤ (v.val[k + 1]'hk)._0.toInt := by
  sorry

/-- **Within-row column order** (proptest `cols_non_increasing_within_row`).

For consecutive entries sharing a row, the column index does not
increase. Non-strict (`≥`) rather than strict (`>`) because the
implementation may emit the same coordinate twice for a single-element
row whose only element matches `x` (the `j = 0` branch falls through to
the explicit `if !is_empty then if row[0] == x then push (r,0)` after the
recursive call with `col = 0` has already pushed `(r,0)`). -/
theorem cols_non_increasing_within_row
    (lst : RustSlice (RustSlice i64)) (x : i64)
    (v : alloc.vec.Vec (rust_primitives.hax.Tuple2 i64 i64) alloc.alloc.Global)
    (hres : clever_086_get_coords_sorted.get_coords_sorted lst x = RustM.ok v)
    (hrows : lst.val.size ≤ 2^63)
    (hcols : ∀ (i : Nat) (hi : i < lst.val.size), (lst.val[i]'hi).val.size ≤ 2^63)
    (k : Nat) (hk : k + 1 < v.val.size)
    (hrow_eq :
      (v.val[k]'(Nat.lt_of_succ_lt hk))._0 = (v.val[k + 1]'hk)._0) :
    (v.val[k + 1]'hk)._1.toInt ≤
      (v.val[k]'(Nat.lt_of_succ_lt hk))._1.toInt := by
  sorry

end Clever_086_get_coords_sortedObligations
