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

open repeat_packed_usize

/-- Success postcondition (packed size + preserved alignment): when
    `layout.size * n + layout.align ≤ 2^63`, `repeat_packed layout n`
    returns `Ok ⟨layout.size * n, layout.align⟩`.

    Captures the Rust property test `ok_is_packed_and_preserves_align`,
    whose two asserts (`out.size() == size * n` and `out.align() == align`)
    are simultaneous consequences of this single `Layout` equation. Also
    captures the success side of `isize_size_limit_boundary` (for
    `n_ok = max/size` with `n_ok * size ≤ max = 2^63 - align`, the
    function must return `Ok`).

    The precondition `size*n + align ≤ 2^63` is the *strongest true*
    success threshold in the Lean model: it subsumes
      (a) no `usize` multiplication overflow (since `2^63 < 2^64`),
      (b) `align ≤ 2^63`, so `max_size_for_align align` does not
          underflow in the model, and
      (c) the `from_size_alignment` size guard
          `size * n > max_size_for_align align` is false, re-expressed
          as `size * n + align ≤ 2^63`.
    The Rust proptest uses a bounded grid (`size ≤ 65536`, `align ≤ 4096`,
    `n ≤ 50_000`) that lies strictly inside this region; the Lean
    statement generalises to the full success region the model admits. -/
theorem repeat_packed_ok (layout : Layout) (n : usize)
    (hbnd : layout.size.toNat * n.toNat + layout.align.toNat ≤ 2 ^ 63) :
    repeat_packed layout n =
      RustM.ok (core_models.result.Result.Ok
        (Layout.mk (size := layout.size * n) (align := layout.align))) := by
  sorry

/-- Failure clause (size exceeds `isize::MAX` after multiplication, no
    `usize` overflow): when `n ≠ 0`, `layout.size * n` does not overflow
    `usize`, `layout.align ≤ 2^63` (so `max_size_for_align` is well
    defined in the model), and `layout.size * n + layout.align > 2^63`,
    `repeat_packed layout n` returns `Err LayoutError`.

    Captures the failure-side asserts of the Rust property test
    `isize_size_limit_boundary`: for `n_bad = (2^63 - align)/size + 1`,
    `size * n_bad` exceeds `max_size_for_align(align)` but stays well
    under `2^64`, so the function must reject through the
    `from_size_alignment` size guard, not the explicit mul-overflow
    guard.

    The `align ≤ 2^63` precondition rules out the model-edge case
    where `max_size_for_align` itself underflows: there the function
    would panic with `integerOverflow` rather than returning a clean
    `Err`. The Rust proptest never exercises `align > 2^63`, so this
    is the strongest honest threshold for the failure mode. -/
theorem repeat_packed_err_size_too_large (layout : Layout) (n : usize)
    (hn : n ≠ 0)
    (hnomul : layout.size.toNat * n.toNat < 2 ^ 64)
    (halign : layout.align.toNat ≤ 2 ^ 63)
    (hsz : 2 ^ 63 < layout.size.toNat * n.toNat + layout.align.toNat) :
    repeat_packed layout n =
      RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  sorry

/-- Failure clause (multiplication overflow): when
    `layout.size.toNat * n.toNat ≥ 2^64` (i.e., the product overflows
    `usize`), `repeat_packed layout n` returns `Err LayoutError`,
    *without* attempting the `from_size_alignment` step.

    Captures the Rust property test `mul_overflow_is_err`. The check
    `layout.size > 18_446_744_073_709_551_615 / n` (in `usize`) is
    equivalent to `layout.size.toNat * n.toNat ≥ 2^64` for `n > 0`,
    which is exactly the unsigned-mul-overflow condition. For `n = 0`
    we have `size.toNat * 0 = 0 < 2^64`, so the precondition implicitly
    forces `n ≠ 0`; the alignment is unconstrained because the function
    returns the `Err` branch before consulting `align`. -/
theorem repeat_packed_err_mul_overflow (layout : Layout) (n : usize)
    (hov : 2 ^ 64 ≤ layout.size.toNat * n.toNat) :
    repeat_packed layout n =
      RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  sorry

end Repeat_packed_usizeObligations
