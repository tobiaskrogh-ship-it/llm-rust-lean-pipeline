-- Companion obligations file for the `max_size_for_align_usize` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import max_size_for_align_usize

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Max_size_for_align_usizeObligations

/-- Definitional unfolding of the partial `usize` addition (the `add_one`
    `hax_add_def_u8` trick, transposed to `USize64`): `x +? y` is, by `rfl`,
    the overflow-guarded `if`. -/
private theorem hax_add_def_usize (x y : usize) :
    x +? y = if USize64.addOverflow x y
             then RustM.fail Error.integerOverflow
             else pure (x + y) := rfl

/-- Definitional unfolding of the partial `usize` subtraction. -/
private theorem hax_sub_def_usize (x y : usize) :
    x -? y = if USize64.subOverflow x y
             then RustM.fail Error.integerOverflow
             else pure (x - y) := rfl

/-- The static inner sum `isize::MAX + 1` evaluates to `2^63`. Both operands
    are literals, so this is a closed `USize64` (`BitVec 64`) computation. -/
private theorem const_add :
    (9223372036854775807 : usize) + (1 : usize) = (9223372036854775808 : usize) := by
  decide

/-- `MAX_ALIGN = 2^63 < 2^64`, so its `toNat` is the literal itself. -/
private theorem const_toNat : (9223372036854775808 : usize).toNat = 9223372036854775808 := by
  decide

/-- The static inner add `isize::MAX + 1` never overflows `usize`
    (`2^63 - 1 + 1 = 2^63 < 2^64`). Closed literal computation. -/
private theorem no_add_overflow :
    ¬ USize64.addOverflow (9223372036854775807 : usize) (1 : usize) := by
  decide

/-- Postcondition over the entire valid input domain.

    Captures the Rust property test `postcondition_formula_over_valid_alignments`:
    for every legal alignment `align ≤ MAX_ALIGN`
    (`MAX_ALIGN = isize::MAX + 1 = 2^63 = 9223372036854775808`), the function
    returns exactly `(isize::MAX + 1) - align`. The static inner sum
    `9223372036854775807 + 1` cannot overflow `usize` (`2^63 < 2^64`), so the
    only nontrivial precondition is that the trailing subtraction does not
    underflow, i.e. `align ≤ 2^63`. Stated in the equational form preferred by
    the references (`add_one_postcondition`): the guard `align ≤ 2^63` is
    exactly the no-underflow condition `¬ USize64.subOverflow 2^63 align`. -/
theorem max_size_for_align_postcondition (align : usize)
    (h : align ≤ (9223372036854775808 : usize)) :
    max_size_for_align_usize.max_size_for_align align
      = RustM.ok ((9223372036854775808 : usize) - align) := by
  -- No-underflow side condition: `align ≤ 2^63` ⇒ `¬ subOverflow (2^63) align`.
  have hsub : ¬ USize64.subOverflow ((9223372036854775807 : usize) + 1) align := by
    rw [USize64.subOverflow_iff, const_add, const_toNat]
    have hle : align.toNat ≤ 9223372036854775808 := by
      have h' := USize64.le_iff_toNat_le.mp h
      rwa [const_toNat] at h'
    omega
  -- Unfold the do-block and discharge the two partial operators.
  unfold max_size_for_align_usize.max_size_for_align
  rw [hax_add_def_usize, if_neg no_add_overflow]
  simp only [pure_bind]
  rw [hax_sub_def_usize, if_neg hsub, const_add]
  rfl

/-- Boundary case explicitly pinned by the same property test
    (`postcondition_formula_over_valid_alignments`, final iteration
    `shift = 63`, `align = MAX_ALIGN`): the maximum legal alignment leaves no
    room, so the result is exactly `0`. Independent contractual edge of the
    valid domain. -/
theorem max_size_for_align_boundary_zero :
    max_size_for_align_usize.max_size_for_align (9223372036854775808 : usize)
      = RustM.ok (0 : usize) := by
  rw [max_size_for_align_postcondition (9223372036854775808 : usize) (by decide)]
  decide

/-- Failure condition / precondition boundary.

    Captures the Rust property test `panics_when_align_exceeds_max`: the first
    value past the valid domain (`MAX_ALIGN + 1`) and every larger `align`
    makes the internal subtraction `(isize::MAX + 1) - align` underflow, so the
    function panics. The Rust panic is modelled by
    `RustM.fail Error.integerOverflow`. This pins that the contract only holds
    for `align ≤ MAX_ALIGN`. -/
theorem max_size_for_align_overflow (align : usize)
    (h : (9223372036854775808 : usize) < align) :
    max_size_for_align_usize.max_size_for_align align
      = RustM.fail Error.integerOverflow := by
  -- Underflow side condition: `2^63 < align` ⇒ `subOverflow (2^63) align`.
  have hsub : USize64.subOverflow ((9223372036854775807 : usize) + 1) align := by
    rw [USize64.subOverflow_iff, const_add, const_toNat]
    have h' := USize64.lt_iff_toNat_lt.mp h
    rwa [const_toNat] at h'
  unfold max_size_for_align_usize.max_size_for_align
  rw [hax_add_def_usize, if_neg no_add_overflow]
  simp only [pure_bind]
  rw [hax_sub_def_usize, if_pos hsub]

end Max_size_for_align_usizeObligations
