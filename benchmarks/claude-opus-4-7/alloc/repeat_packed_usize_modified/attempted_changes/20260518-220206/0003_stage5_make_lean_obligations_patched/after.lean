-- Companion obligations file for the `repeat_packed_usize` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import repeat_packed_usize

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Repeat_packed_usizeObligations

-- `MAX_ALIGN = isize::MAX + 1 = 2^63`; `usize::MAX = 2^64 - 1`. These are the
-- inlined literals appearing in the extracted `max_size_for_align` /
-- `repeat_packed`.

/-- Postcondition (success, "packed"): captures the first claim of the Rust
    property test `ok_is_packed_and_preserves_align` — when the inputs do not
    overflow `usize` and stay within the `isize` size limit, `repeat_packed`
    succeeds and the result size is *exactly* `size * n` (no inter-instance
    padding). Stated over `.toNat` so it pins the exact product with no wrap.

    Precondition: `align ≤ 2^63` (so the inlined `max_size_for_align` does not
    underflow / panic) and `size * n ≤ max_size_for_align(align) = 2^63 - align`
    (within the `isize` size limit; this bound also forces `size * n` not to
    overflow `usize`, so the division-based overflow guard is `false`). -/
theorem repeat_packed_ok_is_packed
    (layout : repeat_packed_usize.Layout) (n : usize)
    (halign : layout.align.toNat ≤ 9223372036854775808)
    (hlimit : layout.size.toNat * n.toNat
                ≤ 9223372036854775808 - layout.align.toNat) :
    ∃ r : repeat_packed_usize.Layout,
      repeat_packed_usize.repeat_packed layout n
          = RustM.ok (core_models.result.Result.Ok r)
      ∧ r.size.toNat = layout.size.toNat * n.toNat := by
  sorry

/-- Postcondition (success, alignment preserved): captures the second,
    independent claim of `ok_is_packed_and_preserves_align` — the original
    alignment is carried through unchanged (`out.align() == align`). Split
    from the packed-size claim so each contract clause is its own theorem. -/
theorem repeat_packed_preserves_align
    (layout : repeat_packed_usize.Layout) (n : usize)
    (halign : layout.align.toNat ≤ 9223372036854775808)
    (hlimit : layout.size.toNat * n.toNat
                ≤ 9223372036854775808 - layout.align.toNat) :
    ∃ r : repeat_packed_usize.Layout,
      repeat_packed_usize.repeat_packed layout n
          = RustM.ok (core_models.result.Result.Ok r)
      ∧ r.align = layout.align := by
  sorry

/-- Failure boundary (isize size limit): captures the `n_bad` direction of the
    Rust property test `isize_size_limit_boundary` — when `size * n` does not
    overflow `usize` (so the checked multiplication succeeds and control
    reaches `from_size_alignment`) but the product exceeds the `isize` size
    limit `max_size_for_align(align) = 2^63 - align`, `repeat_packed` returns
    `Err(LayoutError)` (a handled error, modelled by `RustM.ok (.Err …)`, not
    a panic). The `is_ok` (`n_ok`) direction of the same test is captured by
    `repeat_packed_ok_is_packed` / `repeat_packed_preserves_align`. -/
theorem repeat_packed_exceeds_isize_limit_is_err
    (layout : repeat_packed_usize.Layout) (n : usize)
    (hmul : layout.size.toNat * n.toNat < 2 ^ 64)
    (halign : layout.align.toNat ≤ 9223372036854775808)
    (hexceed : 9223372036854775808 - layout.align.toNat
                 < layout.size.toNat * n.toNat) :
    repeat_packed_usize.repeat_packed layout n
      = RustM.ok
          (core_models.result.Result.Err repeat_packed_usize.LayoutError.mk) := by
  sorry

/-- Failure condition (multiplication overflow): captures the Rust property
    test `mul_overflow_is_err` — when `size * n` overflows `usize`, the
    division-based overflow guard (`n != 0 && size > usize::MAX / n`) fires and
    `repeat_packed` returns `Err(LayoutError)`; it must not wrap around and
    report a bogus small layout. This is a handled error, modelled by
    `RustM.ok (.Err …)`, not a panic. The alignment is irrelevant here because
    the overflow branch returns before `from_size_alignment` is reached. -/
theorem repeat_packed_mul_overflow_is_err
    (layout : repeat_packed_usize.Layout) (n : usize)
    (hov : 2 ^ 64 ≤ layout.size.toNat * n.toNat) :
    repeat_packed_usize.repeat_packed layout n
      = RustM.ok
          (core_models.result.Result.Err repeat_packed_usize.LayoutError.mk) := by
  sorry

end Repeat_packed_usizeObligations
