-- Companion obligations file for the `padding_needed_for_usize` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import padding_needed_for_usize

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Padding_needed_for_usizeObligations

open padding_needed_for_usize

/-- Doc-example anchor: `padding_needed_for 9 4 = 3`. Concrete instance from
    the doc comment of `core::alloc::Layout::padding_needed_for`, captured by
    the property test `doc_example`. Pinning the concrete value (rather than
    just the algebraic identity) catches accidental sign/overflow flips that
    would still satisfy a universal modular identity at this small input. -/
theorem padding_needed_for_doc_example :
    padding_needed_for (9 : usize) (4 : usize) = RustM.ok (3 : usize) := by
  sorry

/-- Failure clause: when `align` is not a power of two (as decided by the
    helper `is_power_of_two_usize`, which also rejects `align = 0`), the
    function returns the sentinel `usize::MAX` regardless of `size`.

    Captures the property test `prop_non_power_of_two_returns_max`
    (all `align ∈ 0..256` that aren't powers of two, every `size ∈ 0..256`,
    expected return is `usize::MAX = 2^64 - 1`). A buggy implementation that
    returned a non-MAX value, panicked, or branched on `align == 0`
    differently would falsify this. The sentinel is written out as the
    literal `2^64 - 1 = 18446744073709551615` because Hax inlines it in the
    extracted body. -/
theorem padding_needed_for_non_power_of_two (size align : usize)
    (h : is_power_of_two_usize align = RustM.ok false) :
    padding_needed_for size align = RustM.ok (18446744073709551615 : usize) := by
  sorry

/-- Postcondition (aligns size up): for a power-of-two `align` with the
    no-overflow precondition `size.toNat + align.toNat ≤ 2^64`, the
    function returns some padding `r` such that `size + r` is a multiple
    of `align` — i.e. the address after the padded block is `align`-aligned.

    The precondition `size.toNat + align.toNat ≤ 2^64` is the strongest
    statement that's truly universal in the Lean model: the bit-trick
    computes `(size + (align - 1)) & !(align - 1)`, and the inner `+?`
    would fail when `size + (align - 1) ≥ 2^64`. The proptest's
    `size < 1000`, `align ≤ 2^15` bound is a (very loose) instance of
    this precondition.

    Captures property test `prop_result_aligns_size_up`. A buggy
    implementation that returned `0` for nonzero residue, or rounded down
    instead of up, would falsify this. -/
theorem padding_needed_for_aligns_up (size align : usize)
    (hpow : is_power_of_two_usize align = RustM.ok true)
    (hbound : size.toNat + align.toNat ≤ 2 ^ 64) :
    ∃ r : usize, padding_needed_for size align = RustM.ok r
      ∧ (size.toNat + r.toNat) % align.toNat = 0 := by
  sorry

/-- Postcondition (minimality): for a power-of-two `align` with the
    no-overflow precondition, the returned padding is strictly less than
    `align`. Together with `padding_needed_for_aligns_up` this uniquely
    pins down the result (a value that overshoots by a whole `align`
    block satisfies the alignment clause but fails this minimality clause).

    Captures property test `prop_padding_is_minimal`. A buggy
    implementation that always returned `align` (also aligns `size + r`)
    or that returned `size + align - 1` in unaligned cases would falsify
    this. -/
theorem padding_needed_for_minimal (size align : usize)
    (hpow : is_power_of_two_usize align = RustM.ok true)
    (hbound : size.toNat + align.toNat ≤ 2 ^ 64) :
    ∃ r : usize, padding_needed_for size align = RustM.ok r ∧ r < align := by
  sorry

/-- Totality / no-panic: the function returns a value successfully whenever
    the implicit arithmetic precondition holds. When `align` is not a power
    of two the function short-circuits to the `usize::MAX` sentinel without
    any arithmetic, so totality is unconditional on that branch. When
    `align` IS a power of two, the inner `(size + (align - 1)) & !(align - 1)`
    requires `size + (align - 1) < 2^64`, i.e. `size.toNat + align.toNat ≤ 2^64`,
    to avoid the `+?` failure mode. The conditional precondition below
    states this without over-restricting the non-power-of-two case.

    Every property test exercises the function via a direct `assert_eq!`
    on its return value, which implicitly assumes totality in the test
    domain (powers of two with `size < 1000`, `align ≤ 2^15`). -/
theorem padding_needed_for_total (size align : usize)
    (hbound : is_power_of_two_usize align = RustM.ok true →
              size.toNat + align.toNat ≤ 2 ^ 64) :
    ∃ r : usize, padding_needed_for size align = RustM.ok r := by
  sorry

end Padding_needed_for_usizeObligations
