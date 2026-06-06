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

/-- Postcondition (failure / rejects non-power-of-two): when `align` is not
    a power of two (as decided by the helper `is_power_of_two_usize`), the
    function rejects regardless of `size`. Captures property tests
    `rejects_non_power_of_two` (e.g. `align ∈ {0, 3, 6}` are rejected) and
    `non_power_of_two_align_always_rejected` (sweep across non-pow-2 aligns
    and many sizes). A buggy implementation that accepted any non-power-of-two
    alignment for some size would falsify this. -/
theorem is_size_align_valid_rejects_non_power_of_two (size align : usize)
    (h : is_power_of_two_usize align = RustM.ok false) :
    is_size_align_valid size align = RustM.ok false := sorry

/-- Postcondition (accepts valid input): when `align` is a power of two and
    `size.toNat + align.toNat ≤ 2^63`, the function accepts.

    The implementation rejects when `size > max_size_for_align align`, i.e.
    when `size > 2^63 - align`; equivalently (in `Nat` arithmetic), when
    `size.toNat + align.toNat > 2^63`. For a power-of-two `align ≤ 2^63`,
    this is exactly the negation of "the next multiple of `align` ≥ `size`
    fits in `isize::MAX = 2^63 - 1`", which is the round-up contract stated
    in the doc comment.

    Captures the positive branch of property test
    `power_of_two_align_matches_round_up_contract`, the low-side asserts of
    `layout_round_up_to_align_edge_cases` (`is_size_align_valid(low, align)`
    is `true`), and `layout_accepts_all_valid_alignments` (instantiated at
    `size = 0`, where `0 + align ≤ 2^63` holds for every power-of-two
    `align ≤ 2^63`). -/
theorem is_size_align_valid_accepts (size align : usize)
    (hpow : is_power_of_two_usize align = RustM.ok true)
    (hsize : size.toNat + align.toNat ≤ 2 ^ 63) :
    is_size_align_valid size align = RustM.ok true := sorry

/-- Postcondition (rejects too-large size): when `align` is a power of two
    but the rounded-up size exceeds `isize::MAX`, the function rejects.

    Stated as `2^63 < size.toNat + align.toNat`, the `Nat`-arithmetic
    counterpart of the implementation check `size > 2^63 - align` (which is
    safe because a power-of-two `align ≤ 2^63`). Captures the negative
    branch of `power_of_two_align_matches_round_up_contract` and the
    high-side `assert!(!is_size_align_valid(high, align))` of
    `layout_round_up_to_align_edge_cases`. -/
theorem is_size_align_valid_rejects_large_size (size align : usize)
    (hpow : is_power_of_two_usize align = RustM.ok true)
    (hsize : 2 ^ 63 < size.toNat + align.toNat) :
    is_size_align_valid size align = RustM.ok false := sorry

/-- Totality / no-panic: for every pair of `usize` inputs, the function
    returns a `Bool` successfully (it never panics, never overflows).

    The only operation that could panic in the model is the literal
    subtraction `2^63 - align` inside `max_size_for_align`; but that branch
    is reached only after the helper has confirmed `align` is a power of
    two, which forces `align.toNat ∈ {1, 2, 4, …, 2^63}` and in particular
    `align ≤ 2^63`, so the subtraction is safe. Captures the implicit
    "returns a `bool`" totality contract of the function and the fact that
    every property test exercises the function via direct assertions on
    its `bool` return value (no `is_ok` / `unwrap` is needed). -/
theorem is_size_align_valid_total (size align : usize) :
    ∃ b : Bool, is_size_align_valid size align = RustM.ok b := sorry

end Is_size_align_valid_usizeObligations
