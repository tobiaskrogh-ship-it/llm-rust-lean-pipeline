-- Companion obligations file for the `clever_114_max_fill_count` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_114_max_fill_count

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_114_max_fill_countObligations

/-! ## Specification oracle (Nat-valued).

`countNonzeroFrom row j` counts the indices `k ∈ [j, row.val.size)` whose
entry is non-zero.  Total on `Nat` and well-founded on `row.val.size - j`.
This is the Lean mirror of the inner Rust helper `count_row_at`. -/

private def countNonzeroFrom (row : RustSlice u64) (j : Nat) : Nat :=
  if h : j < row.val.size then
    (if (row.val[j]'h) = (0 : u64) then 0 else 1) + countNonzeroFrom row (j + 1)
  else 0
termination_by row.val.size - j

/-- `maxFillSpecFrom grid capacity i` is the running spec total starting
from row `i`: the sum, over rows `r ∈ [i, grid.val.size)`, of the ceiling
`(countNonzeroFrom r 0 + capacity - 1) / capacity` (Nat division).  This
mirrors the Rust reference `spec` used by the `matches_spec` proptest. -/
private def maxFillSpecFrom
    (grid : RustSlice (RustSlice u64)) (capacity : Nat) (i : Nat) : Nat :=
  if h : i < grid.val.size then
    ((countNonzeroFrom (grid.val[i]'h) 0 + capacity - 1) / capacity)
      + maxFillSpecFrom grid capacity (i + 1)
  else 0
termination_by grid.val.size - i

/-! ## Concrete grid for the `known` unit pins. -/

private def known_row_0 : RustSlice u64 := ⟨#[0, 0, 1, 0], by decide⟩
private def known_row_1 : RustSlice u64 := ⟨#[0, 1, 0, 0], by decide⟩
private def known_row_2 : RustSlice u64 := ⟨#[1, 1, 1, 1], by decide⟩
private def known_grid : RustSlice (RustSlice u64) :=
  ⟨#[known_row_0, known_row_1, known_row_2], by decide⟩

/-! ## Contract theorems. -/

/-- Failure-avoidance clause (proptest `capacity_zero_returns_zero`):
    for any grid, `max_fill_count grid 0 = 0`.  The wrapper short-circuits
    on `capacity = 0`, side-stepping the inner `_ /? capacity` divisor. -/
theorem capacity_zero_returns_zero (grid : RustSlice (RustSlice u64)) :
    clever_114_max_fill_count.max_fill_count grid 0 = RustM.ok 0 := by
  sorry

/-- Base case (proptest `empty_grid_returns_zero`): an empty grid has
    no wells, hence no trips, for every `capacity` (including 0). -/
theorem empty_grid_returns_zero
    (grid : RustSlice (RustSlice u64)) (capacity : u64)
    (hempty : grid.val.size = 0) :
    clever_114_max_fill_count.max_fill_count grid capacity = RustM.ok 0 := by
  sorry

/-- Main postcondition (proptest `matches_spec`).

When `capacity > 0` and no overflow occurs at the per-row or accumulator
level, `max_fill_count grid capacity` equals
`Σ_{row in grid} ⌈count_nonzero(row) / capacity⌉` (Nat ceiling).

The feasibility preconditions are needed because the natural Lean
generalisation quantifies over `RustSlice` inputs of any `size < 2^64`,
where the proptest bounds `0..8 × 0..8 × 1..1_000_000` are far below the
overflow edges:

* `h_cap_pos` — `capacity ≠ 0`; without this, the wrapper short-circuits
  and the universal closed form does not hold.
* `h_rows_no_overflow` — for every row, `count_nonzero(row) + capacity`
  fits in `u64`.  Rules out overflow at `w +? capacity` inside `rows_at`.
* `h_sum_no_overflow` — the Nat-level spec sum fits in `u64`.  Rules out
  overflow at `acc +? trips` across rows.

Outside these bounds the function fails with `integerOverflow`, so the
universal equation truly does not hold; these preconditions are the
strongest honest formulation in the Lean model. -/
theorem matches_spec
    (grid : RustSlice (RustSlice u64)) (capacity : u64)
    (h_cap_pos : 0 < capacity.toNat)
    (h_rows_no_overflow :
       ∀ (i : Nat) (hi : i < grid.val.size),
         countNonzeroFrom (grid.val[i]'hi) 0 + capacity.toNat < 2 ^ 64)
    (h_sum_no_overflow : maxFillSpecFrom grid capacity.toNat 0 < 2 ^ 64) :
    clever_114_max_fill_count.max_fill_count grid capacity
      = RustM.ok (UInt64.ofNat (maxFillSpecFrom grid capacity.toNat 0)) := by
  sorry

/-- Unit pin (test `known`, capacity 1): on the grid
    `[[0,0,1,0], [0,1,0,0], [1,1,1,1]]`, capacity-1 buckets need
    `1 + 1 + 4 = 6` trips. -/
theorem known_capacity_one :
    clever_114_max_fill_count.max_fill_count known_grid 1 = RustM.ok 6 := by
  sorry

/-- Unit pin (test `known`, capacity 2): on the same grid, capacity-2
    buckets need `⌈1/2⌉ + ⌈1/2⌉ + ⌈4/2⌉ = 1 + 1 + 2 = 4` trips. -/
theorem known_capacity_two :
    clever_114_max_fill_count.max_fill_count known_grid 2 = RustM.ok 4 := by
  sorry

end Clever_114_max_fill_countObligations
