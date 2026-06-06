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

/-- The `Layout` invariant precondition fragment: `align` is a power of two
    (hence `≥ 1`, so the inlined `align - 1` does not underflow). Powers of
    two are exactly the legal alignments enumerated by the Rust property
    tests (`ALIGNS = [1, 2, 4, 8, 16, 4096, 1 << 30]`). Mirrors the `IsPow2`
    helper of the `pad_to_align_usize` reference. -/
def IsPow2 (a : usize) : Prop := ∃ k : Nat, a.toNat = 2 ^ k

/-- Independent oracle for the padded element stride: the least multiple of
    `a` that is `≥ s` (for `a ≥ 1`). This is exactly the Rust test's
    `round_up` reimplementation `if s % a == 0 then s else s + (a - s % a)`,
    and equals the implementation's bitmask `(s + (a-1)) & ~(a-1)` when `a`
    is a power of two. -/
def RoundUp (s a : Nat) : Nat := a * ((s + (a - 1)) / a)

/-- No-panic / totality over the valid input domain (`n ≠ 0`).
    The property tests only ever feed valid layouts (power-of-two `align`,
    `size + (align - 1)` not overflowing) and never expect a panic — every
    call site pattern-matches the `Result` rather than catching an abort.
    So in the valid domain `repeat` always returns a `Result` value, never
    `RustM.fail`. (`n = 0` is excluded: the inlined overflow guard divides
    by `n`; see `repeat_layout_zero_n_succeeds`.) -/
theorem repeat_layout_total
    (layout : repeat_usize.Layout) (n : usize)
    (hpow : IsPow2 layout.align)
    (hnof : layout.size.toNat + (layout.align.toNat - 1) < 2 ^ 64)
    (hn : n.toNat ≠ 0) :
    ∃ r : core_models.result.Result
            (rust_primitives.hax.Tuple2 repeat_usize.Layout usize)
            repeat_usize.LayoutError,
      repeat_usize.repeat_layout layout n = RustM.ok r := by
  sorry

/-- `prop_stride_is_correct_padding`, clause 1: the returned stride is a
    multiple of `align` (`offs % align == 0`). Conditioned on the call
    returning `Ok`, exactly as the test's `if let Ok((_, offs))`. -/
theorem repeat_layout_stride_multiple_of_align
    (layout : repeat_usize.Layout) (n : usize)
    (arr : repeat_usize.Layout) (offs : usize)
    (hpow : IsPow2 layout.align)
    (hnof : layout.size.toNat + (layout.align.toNat - 1) < 2 ^ 64)
    (h : repeat_usize.repeat_layout layout n
          = RustM.ok (core_models.result.Result.Ok
              (rust_primitives.hax.Tuple2.mk arr offs))) :
    offs.toNat % layout.align.toNat = 0 := by
  sorry

/-- `prop_stride_is_correct_padding`, clause 2: rounding up never shrinks the
    element size (`offs >= size`). -/
theorem repeat_layout_stride_not_smaller_than_size
    (layout : repeat_usize.Layout) (n : usize)
    (arr : repeat_usize.Layout) (offs : usize)
    (hpow : IsPow2 layout.align)
    (hnof : layout.size.toNat + (layout.align.toNat - 1) < 2 ^ 64)
    (h : repeat_usize.repeat_layout layout n
          = RustM.ok (core_models.result.Result.Ok
              (rust_primitives.hax.Tuple2.mk arr offs))) :
    layout.size.toNat ≤ offs.toNat := by
  sorry

/-- `prop_stride_is_correct_padding`, clause 3: the padding added is strictly
    less than `align` (`offs - size < align`), so the stride is the *least*
    multiple of `align` that is `≥ size`. Together with clauses 1 and 2 this
    uniquely pins the stride. -/
theorem repeat_layout_stride_gap_less_than_align
    (layout : repeat_usize.Layout) (n : usize)
    (arr : repeat_usize.Layout) (offs : usize)
    (hpow : IsPow2 layout.align)
    (hnof : layout.size.toNat + (layout.align.toNat - 1) < 2 ^ 64)
    (h : repeat_usize.repeat_layout layout n
          = RustM.ok (core_models.result.Result.Ok
              (rust_primitives.hax.Tuple2.mk arr offs))) :
    offs.toNat - layout.size.toNat < layout.align.toNat := by
  sorry

/-- `prop_array_size_is_stride_times_n`, clause 1: the input alignment is
    preserved in the array layout (`arr.align() == align`). -/
theorem repeat_layout_alignment_preserved
    (layout : repeat_usize.Layout) (n : usize)
    (arr : repeat_usize.Layout) (offs : usize)
    (h : repeat_usize.repeat_layout layout n
          = RustM.ok (core_models.result.Result.Ok
              (rust_primitives.hax.Tuple2.mk arr offs))) :
    arr.align = layout.align := by
  sorry

/-- `prop_array_size_is_stride_times_n`, clause 2: the array size is exactly
    `n` strides (`arr.size() == offs * n`, the multiplication not
    overflowing on the success path). Independent of the stride-value
    clauses above. -/
theorem repeat_layout_array_size_is_stride_times_n
    (layout : repeat_usize.Layout) (n : usize)
    (arr : repeat_usize.Layout) (offs : usize)
    (h : repeat_usize.repeat_layout layout n
          = RustM.ok (core_models.result.Result.Ok
              (rust_primitives.hax.Tuple2.mk arr offs))) :
    arr.size.toNat = offs.toNat * n.toNat := by
  sorry

/-- `prop_success_iff_fits`, success direction (`should_fit ⇒ is_ok`): when
    the padded stride times `n` fits within
    `max_size_for_align(align) = (isize::MAX + 1) - align = 2^63 - align`,
    `repeat` returns `Ok`. -/
theorem repeat_layout_ok_when_fits
    (layout : repeat_usize.Layout) (n : usize)
    (hpow : IsPow2 layout.align)
    (hnof : layout.size.toNat + (layout.align.toNat - 1) < 2 ^ 64)
    (hn : n.toNat ≠ 0)
    (hfit : RoundUp layout.size.toNat layout.align.toNat * n.toNat
              ≤ 2 ^ 63 - layout.align.toNat) :
    ∃ (arr : repeat_usize.Layout) (offs : usize),
      repeat_usize.repeat_layout layout n
        = RustM.ok (core_models.result.Result.Ok
            (rust_primitives.hax.Tuple2.mk arr offs)) := by
  sorry

/-- `prop_success_iff_fits`, failure direction (`¬should_fit ⇒ is_err`): when
    the padded stride times `n` overflows `usize` or exceeds `2^63 - align`,
    `repeat` returns `Err` (a contract failure, not a panic). -/
theorem repeat_layout_err_when_not_fits
    (layout : repeat_usize.Layout) (n : usize)
    (hpow : IsPow2 layout.align)
    (hnof : layout.size.toNat + (layout.align.toNat - 1) < 2 ^ 64)
    (hn : n.toNat ≠ 0)
    (hbig : RoundUp layout.size.toNat layout.align.toNat * n.toNat
              > 2 ^ 63 - layout.align.toNat) :
    repeat_usize.repeat_layout layout n
      = RustM.ok (core_models.result.Result.Err repeat_usize.LayoutError.mk) := by
  sorry

/-- `prop_success_iff_fits`, `n = 0` sub-case: with zero repetitions the
    product `round_up(size, align) * 0 = 0 ≤ max`, so the Rust contract
    returns `Ok`. NOTE: the inlined overflow guard
    `n != 0 && size > usize::MAX / n` was extracted *without* `&&`
    short-circuiting, so the model evaluates `usize::MAX / 0` and this case
    actually yields `RustM.fail divisionByZero`. Kept for contract coverage
    (`ns()` exercises `n = 0`); the proof stage will admit it. -/
theorem repeat_layout_zero_n_succeeds
    (layout : repeat_usize.Layout)
    (hpow : IsPow2 layout.align)
    (hnof : layout.size.toNat + (layout.align.toNat - 1) < 2 ^ 64) :
    ∃ (arr : repeat_usize.Layout) (offs : usize),
      repeat_usize.repeat_layout layout (0 : usize)
        = RustM.ok (core_models.result.Result.Ok
            (rust_primitives.hax.Tuple2.mk arr offs)) := by
  sorry

/-- `doc_example`, case 1: a normal `[size 12, align 4]` layout repeated 3
    times gives array layout `[36, 4]` with element stride `12`. -/
theorem repeat_layout_example_normal :
    repeat_usize.repeat_layout (repeat_usize.Layout.mk 12 4) 3
      = RustM.ok (core_models.result.Result.Ok
          (rust_primitives.hax.Tuple2.mk (repeat_usize.Layout.mk 36 4) 12)) := by
  sorry

/-- `doc_example`, case 2: an under-aligned `[size 6, align 4]` layout
    repeated 3 times pads the stride to `8`, giving array layout `[24, 4]`. -/
theorem repeat_layout_example_padding_needed :
    repeat_usize.repeat_layout (repeat_usize.Layout.mk 6 4) 3
      = RustM.ok (core_models.result.Result.Ok
          (rust_primitives.hax.Tuple2.mk (repeat_usize.Layout.mk 24 4) 8)) := by
  sorry

/-- `layout_errors`, success edge: `[size 2, align 1]` repeated
    `isize::MAX / 2 = 4611686018427387903` times still fits (`is_ok`). -/
theorem repeat_layout_example_align_max_ok :
    ∃ (arr : repeat_usize.Layout) (offs : usize),
      repeat_usize.repeat_layout (repeat_usize.Layout.mk 2 1)
          4611686018427387903
        = RustM.ok (core_models.result.Result.Ok
            (rust_primitives.hax.Tuple2.mk arr offs)) := by
  sorry

/-- `layout_errors`, failure edge: one past the limit
    (`isize::MAX / 2 + 1 = 4611686018427387904`) overflows the layout size,
    so `repeat` returns `Err` (`is_err`). -/
theorem repeat_layout_example_align_max_plus_one_err :
    repeat_usize.repeat_layout (repeat_usize.Layout.mk 2 1)
        4611686018427387904
      = RustM.ok (core_models.result.Result.Err repeat_usize.LayoutError.mk) := by
  sorry

end Repeat_usizeObligations
