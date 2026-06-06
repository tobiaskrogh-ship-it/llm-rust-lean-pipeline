-- Companion obligations file for the `utf8_acc_cont_byte_u32` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import utf8_acc_cont_byte_u32

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Utf8_acc_cont_byte_u32Obligations

open utf8_acc_cont_byte_u32

/-- Foundational closed-form equation: the function is total and returns
    `(ch <<< 6) ||| (byte &&& CONT_MASK).toUInt32`. The shift `<<<? (6 : i32)`
    has its bounds check `0 ≤ 6 ∧ 6 < 32` discharged statically, the bitwise
    AND/OR have no failure mode at unsigned widths, and the `u8 → u32` cast
    is pure. Stated in equational form (rather than as a Hoare triple) since
    the precondition is trivially `True`; the per-test clauses derive from
    this. Not itself a Rust property test, but the foundational equation
    from which the contract clauses follow, in the style of
    `truncate_number_postcondition`. -/
theorem utf8_acc_cont_byte_postcondition (ch : u32) (byte : u8) :
    utf8_acc_cont_byte ch byte =
      RustM.ok ((ch <<< (6 : UInt32)) ||| (byte &&& CONT_MASK).toUInt32) := by
  sorry

/-- Totality / no-panic: the function is total on the entire `(u32, u8)`
    domain — the constant shift by `6` is always in `[0, 32)`, the bitwise
    AND/OR never overflow, and the `u8 → u32` cast is pure. Captures the
    explicit "no failure conditions" clause documented in the Rust source
    (test `total_function_never_panics_on_extremes`). -/
theorem utf8_acc_cont_byte_total (ch : u32) (byte : u8) :
    ∃ r : u32, utf8_acc_cont_byte ch byte = RustM.ok r :=
  ⟨_, utf8_acc_cont_byte_postcondition ch byte⟩

/-- Postcondition (low six bits): the low six bits of the result are
    exactly the low six bits of `byte` (zero-extended to `u32`), independent
    of `ch`. A buggy mask (e.g. `0x1F`, `0x7F`) or a wrong shift amount
    would falsify this. Captures the property test
    `low_six_bits_of_result_match_low_six_bits_of_byte`. -/
theorem utf8_acc_cont_byte_low_six_bits (ch : u32) (byte : u8) :
    ∃ r : u32, utf8_acc_cont_byte ch byte = RustM.ok r
      ∧ r &&& (0x3F : u32) = (byte &&& (0x3F : u8)).toUInt32 := by
  sorry

/-- Postcondition (high bits): the bits at positions 6..32 of the result
    are `ch` shifted left by 6 — equivalently, `result >>> 6 = ch &&&
    0x03FFFFFF`. The low 26 bits of `ch` are preserved in positions 6..32
    of the result; the top 6 bits of `ch` are discarded. A wrong shift
    width or corrupted accumulator path would falsify this. Captures the
    property test `high_bits_of_result_match_ch_shifted`. -/
theorem utf8_acc_cont_byte_high_bits (ch : u32) (byte : u8) :
    ∃ r : u32, utf8_acc_cont_byte ch byte = RustM.ok r
      ∧ r >>> (6 : UInt32) = ch &&& (0x03FFFFFF : u32) := by
  sorry

/-- Concrete anchor (basic): `utf8_acc_cont_byte 0b00010 0b10101010 =
    0b00010_101010` (= 170). Distinguished input from the original Rust
    test; would catch a uniform contract shift (e.g. swapping arguments).
    Captures the first vector of the `concrete_vectors` property test. -/
theorem utf8_acc_cont_byte_concrete_basic :
    utf8_acc_cont_byte (2 : u32) (170 : u8) = RustM.ok (170 : u32) := by
  sorry

/-- Concrete anchor (UTF-8 copyright sign): `utf8_acc_cont_byte 0x02 0xA9 =
    0xA9`, the accumulator step for decoding `U+00A9 ©` from `0xC2 0xA9`.
    Captures the second vector of the `concrete_vectors` property test. -/
theorem utf8_acc_cont_byte_concrete_copyright :
    utf8_acc_cont_byte (0x02 : u32) (0xA9 : u8) = RustM.ok (0xA9 : u32) := by
  sorry

end Utf8_acc_cont_byte_u32Obligations
