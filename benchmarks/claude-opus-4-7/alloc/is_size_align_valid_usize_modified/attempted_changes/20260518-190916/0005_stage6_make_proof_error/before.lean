-- Companion obligations file for the `is_size_align_valid_usize` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import is_size_align_valid_usize

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Is_size_align_valid_usizeObligations

open is_size_align_valid_usize

/-- Contract clause 1 (failure / precondition: invalid alignment is rejected).

    `Layout::from_size_align` requires `align` to be a power of two
    (`Alignment::new(align)` is `None` otherwise — including `align = 0`).
    Whenever `align` is **not** a power of two, `is_size_align_valid` must
    reject the input by returning `false`, *independently of* `size`.

    Captures the property test `non_power_of_two_align_always_rejected`
    (a sweep over many non-power-of-two alignments — among them `0`,
    `isize::MAX as usize`, `usize::MAX`, `2^63 + 1` — crossed with a range
    of sizes) and the unit test `rejects_non_power_of_two`
    (`!is_size_align_valid(8, 3)`, `!is_size_align_valid(0, 0)`,
    `!is_size_align_valid(0, 6)`). A "power of two" is the mathematical
    predicate `∃ k, align = 2^k`; `0` satisfies its negation. -/
theorem is_size_align_valid_non_power_of_two_rejected
    (size align : usize) (h : ¬ ∃ k : Nat, align.toNat = 2 ^ k) :
    is_size_align_valid size align = RustM.ok false := by
  sorry

/-- Contract clause 2 (postcondition for valid alignment).

    For every power-of-two `align`, the result is exactly the documented
    property: `size` rounded up to the next multiple of `align` must not
    exceed `isize::MAX` (`= 2^63 - 1` on a 64-bit target). The round-up is
    expressed at the `Nat` level as `⌈size / align⌉ * align`, written
    `((size + (align - 1)) / align) * align` (well-defined because a power
    of two is `≥ 1`) — exactly the overflow-safe `u128` oracle
    `fits_when_rounded_up` used by the Rust tests.

    Captures the property test `power_of_two_align_matches_round_up_contract`
    and the unit test `layout_round_up_to_align_edge_cases`, which assert
    `is_size_align_valid(size, align) == size.next_multiple_of(align) <= MAX`
    for every per-`align` boundary neighbourhood (pinning the exact off-by-one
    threshold) plus the size extremes `0`, `1`, `usize::MAX`. The special
    case `size = 0` (always accepted, `layout_accepts_all_valid_alignments`)
    is the instance at `size = 0` and is not given a separate obligation. -/
theorem is_size_align_valid_power_of_two_round_up
    (size align : usize) (k : Nat) (h : align.toNat = 2 ^ k) :
    is_size_align_valid size align
      = RustM.ok (decide
          (((size.toNat + (align.toNat - 1)) / align.toNat) * align.toNat
            ≤ 2 ^ 63 - 1)) := by
  sorry

/-- Documented no-panic / totality clause.

    The Rust source explicitly relies on the short-circuit `&&` so that
    `n - 1` "never underflows when `n == 0`", and `max_size_for_align`'s
    subtraction `2^63 - align` never underflows for a power-of-two `align`
    (`align ≤ 2^63`). Hence `is_size_align_valid` is a total `bool`-valued
    checker: for every `(size, align)` it returns a value and never panics
    (no integer overflow, no error). Every `assert!`/`assert_eq!` in the
    test suite implicitly certifies this no-panic behaviour. -/
theorem is_size_align_valid_no_panic (size align : usize) :
    ∃ v : Bool, is_size_align_valid size align = RustM.ok v := by
  sorry

end Is_size_align_valid_usizeObligations
