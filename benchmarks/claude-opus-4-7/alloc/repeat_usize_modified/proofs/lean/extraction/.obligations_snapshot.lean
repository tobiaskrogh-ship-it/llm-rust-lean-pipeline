-- Companion obligations file for the `repeat_usize` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import repeat_usize

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Repeat_usizeObligations

open repeat_usize

/-! ## Doc-example anchors

    These pin the concrete outputs the Rust doc-test for `Layout::repeat`
    asserts (transferred verbatim into the `doc_example` test). Decidable on
    closed `usize` arithmetic. -/

/-- `repeat({size:=12, align:=4}, 3) = Ok (Tuple2.mk {size:=36, align:=4} 12)`. -/
theorem repeat_layout_doc_example_1 :
    repeat_layout ⟨(12 : usize), (4 : usize)⟩ (3 : usize) =
      RustM.ok (core_models.result.Result.Ok
        (rust_primitives.hax.Tuple2.mk
          ⟨(36 : usize), (4 : usize)⟩ (12 : usize))) := by
  sorry

/-- `repeat({size:=6, align:=4}, 3) = Ok (Tuple2.mk {size:=24, align:=4} 8)`.
    Shows the round-up: stride = 8 (= round-up of 6 to align 4), array size
    = 8 * 3 = 24. -/
theorem repeat_layout_doc_example_2 :
    repeat_layout ⟨(6 : usize), (4 : usize)⟩ (3 : usize) =
      RustM.ok (core_models.result.Result.Ok
        (rust_primitives.hax.Tuple2.mk
          ⟨(24 : usize), (4 : usize)⟩ (8 : usize))) := by
  sorry

/-! ## `layout_errors` boundary anchors

    Transferred from the `tests/alloc.rs::layout_errors` `repeat` assertions
    with `layout = {size:=2, align:=1}`. `align_max = isize::MAX / 2`
    = `(2^63 - 1) / 2` = `2^62 - 1` = `4611686018427387903`. The Ok
    boundary uses `n = align_max`, the Err side `n = align_max + 1`.
    With `align = 1`, stride = `round_up(2, 1) = 2`. -/

/-- Ok side of `layout_errors`: `n = (2^63 - 1) / 2` succeeds (the array
    size is exactly `2 * ((2^63 - 1) / 2) ≤ 2^63 - 1`). -/
theorem repeat_layout_layout_errors_ok :
    ∃ result : rust_primitives.hax.Tuple2 Layout usize,
      repeat_layout ⟨(2 : usize), (1 : usize)⟩
          ((9223372036854775807 : usize) / (2 : usize)) =
        RustM.ok (core_models.result.Result.Ok result) := by
  sorry

/-- Err side of `layout_errors`: `n = (2^63 - 1) / 2 + 1` fails (the array
    size of `2 * n` exceeds `2^63 - 1`). -/
theorem repeat_layout_layout_errors_err :
    repeat_layout ⟨(2 : usize), (1 : usize)⟩
        ((9223372036854775807 : usize) / (2 : usize) + 1) =
      RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  sorry

/-! ## `prop_stride_is_correct_padding` — three stride properties.

    Universal "if Ok" obligations: when `repeat_layout layout n` succeeds with
    payload `Tuple2.mk arr offs`, the stride `offs` satisfies the contract.
    The stride properties (mod, gap) only hold for power-of-two `align`,
    which is a `Layout` invariant; the ALIGNS array in the proptest is
    `[1, 2, 4, 8, 16, 4096, 1 << 30]`, all powers of two. -/

/-- Stride is a multiple of `layout.align`. -/
theorem repeat_layout_ok_stride_mod
    (layout : Layout) (n : usize) (arr : Layout) (offs : usize)
    (hnz : layout.align ≠ 0)
    (hand : layout.align &&& (layout.align - 1) = 0)
    (h : repeat_layout layout n =
      RustM.ok (core_models.result.Result.Ok
        (rust_primitives.hax.Tuple2.mk arr offs))) :
    offs.toNat % layout.align.toNat = 0 := by
  sorry

/-- Stride is at least the input size. -/
theorem repeat_layout_ok_stride_ge_size
    (layout : Layout) (n : usize) (arr : Layout) (offs : usize)
    (h : repeat_layout layout n =
      RustM.ok (core_models.result.Result.Ok
        (rust_primitives.hax.Tuple2.mk arr offs))) :
    layout.size.toNat ≤ offs.toNat := by
  sorry

/-- Stride does not over-pad: the gap `offs - size` is strictly less than
    `layout.align`. -/
theorem repeat_layout_ok_stride_gap_lt_align
    (layout : Layout) (n : usize) (arr : Layout) (offs : usize)
    (hnz : layout.align ≠ 0)
    (hand : layout.align &&& (layout.align - 1) = 0)
    (h : repeat_layout layout n =
      RustM.ok (core_models.result.Result.Ok
        (rust_primitives.hax.Tuple2.mk arr offs))) :
    offs.toNat - layout.size.toNat < layout.align.toNat := by
  sorry

/-! ## `prop_array_size_is_stride_times_n` — alignment preserved, size = stride * n. -/

/-- The array layout preserves the alignment of the input layout. -/
theorem repeat_layout_ok_align_preserved
    (layout : Layout) (n : usize) (arr : Layout) (offs : usize)
    (h : repeat_layout layout n =
      RustM.ok (core_models.result.Result.Ok
        (rust_primitives.hax.Tuple2.mk arr offs))) :
    arr.align = layout.align := by
  sorry

/-- The array size equals the stride times `n` (no overflow at the `Nat`
    level — the proptest expresses this with `offs.checked_mul(n).expect(_)`). -/
theorem repeat_layout_ok_size_eq_stride_times_n
    (layout : Layout) (n : usize) (arr : Layout) (offs : usize)
    (h : repeat_layout layout n =
      RustM.ok (core_models.result.Result.Ok
        (rust_primitives.hax.Tuple2.mk arr offs))) :
    arr.size.toNat = offs.toNat * n.toNat := by
  sorry

/-! ## `prop_success_iff_fits` — Ok/Err boundary.

    The proptest asserts `got.is_ok() == should_fit`, where `should_fit`
    means `stride.checked_mul(n)` succeeds AND `stride * n ≤ max_size_for_align`.
    Split into the two directions of the iff. The bit-trick `stride` is
    `(size + (align - 1)) &&& ~(align - 1)`. -/

/-- Ok direction of the boundary: when `align` is a power of two with
    `align ≤ 2^63`, `size + align ≤ 2^64` (so the `+ (align - 1)` doesn't
    overflow), and the rounded stride times `n` plus `align` fits within
    `2^63` (i.e. `stride * n ≤ max_size_for_align align`), the function
    returns Ok with the closed form. -/
theorem repeat_layout_ok_when_fits
    (layout : Layout) (n : usize)
    (hnz : layout.align ≠ 0)
    (hand : layout.align &&& (layout.align - 1) = 0)
    (hadd : layout.size.toNat + layout.align.toNat ≤ 2 ^ 64)
    (hmul_bnd :
      ((layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1)).toNat
        * n.toNat
      + layout.align.toNat ≤ 2 ^ 63) :
    ∃ arr offs,
      repeat_layout layout n =
        RustM.ok (core_models.result.Result.Ok
          (rust_primitives.hax.Tuple2.mk arr offs))
      ∧ offs = (layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1)
      ∧ arr.align = layout.align
      ∧ arr.size.toNat = offs.toNat * n.toNat := by
  sorry

/-- Err direction of the boundary: when `align` is a power of two with
    `align ≤ 2^63`, `size + align ≤ 2^64`, but the rounded stride times `n`
    plus `align` exceeds `2^63` while the product still fits in `usize`,
    the function fails. -/
theorem repeat_layout_err_when_too_large
    (layout : Layout) (n : usize)
    (hnz : layout.align ≠ 0)
    (hand : layout.align &&& (layout.align - 1) = 0)
    (hadd : layout.size.toNat + layout.align.toNat ≤ 2 ^ 64)
    (hmul_no_ovf :
      ((layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1)).toNat
        * n.toNat < 2 ^ 64)
    (htoo_large :
      2 ^ 63 <
        ((layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1)).toNat
          * n.toNat
        + layout.align.toNat) :
    repeat_layout layout n =
      RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  sorry

/-- Err direction (mul-overflow case): when the rounded stride times `n`
    overflows `usize`, the function fails via the `MAX / n` guard. -/
theorem repeat_layout_err_when_mul_overflows
    (layout : Layout) (n : usize)
    (hnz : layout.align ≠ 0)
    (hand : layout.align &&& (layout.align - 1) = 0)
    (hadd : layout.size.toNat + layout.align.toNat ≤ 2 ^ 64)
    (hov : 2 ^ 64 ≤
      ((layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1)).toNat
        * n.toNat) :
    repeat_layout layout n =
      RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  sorry

end Repeat_usizeObligations
