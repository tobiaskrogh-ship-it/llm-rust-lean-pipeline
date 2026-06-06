-- Companion obligations file for the `utf8_is_cont_byte_u8` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import utf8_is_cont_byte_u8

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Utf8_is_cont_byte_u8Obligations

open utf8_is_cont_byte_u8

/-- Postcondition (positive direction): every byte `b` with `0x80 ≤ b ≤ 0xBF` is
    classified as a continuation byte. Captures the property test
    `returns_true_on_every_byte_in_continuation_range`, which exhaustively
    iterates over `0x80u8..=0xBF`. -/
theorem utf8_is_cont_byte_in_range (byte : u8) (h1 : 128 ≤ byte) (h2 : byte ≤ 191) :
    utf8_is_cont_byte byte = RustM.ok true := by
  sorry

/-- Postcondition (negative direction, ASCII range): every byte `b ≤ 0x7F` is not
    a continuation byte. Captures the first half of the property test
    `returns_false_on_every_byte_outside_continuation_range`, which iterates over
    `0u8..=0x7F`. -/
theorem utf8_is_cont_byte_ascii (byte : u8) (h : byte ≤ 127) :
    utf8_is_cont_byte byte = RustM.ok false := by
  sorry

/-- Postcondition (negative direction, leading/invalid range): every byte `b` with
    `0xC0 ≤ b` is not a continuation byte. Captures the second half of the
    property test `returns_false_on_every_byte_outside_continuation_range`, which
    iterates over `0xC0u8..=0xFF`. -/
theorem utf8_is_cont_byte_leading (byte : u8) (h : 192 ≤ byte) :
    utf8_is_cont_byte byte = RustM.ok false := by
  sorry

/-- Totality / no-panic: for every `u8` input the function returns a value
    successfully (it never panics). The `u8 → i8` cast is pure and the signed
    comparison `<? (-64 : i8)` is total — implicitly checked by the two property
    tests together exhausting the full `0x00..=0xFF` range. -/
theorem utf8_is_cont_byte_total (byte : u8) :
    ∃ r : Bool, utf8_is_cont_byte byte = RustM.ok r := by
  sorry

end Utf8_is_cont_byte_u8Obligations
