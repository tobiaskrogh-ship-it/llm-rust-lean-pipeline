-- Companion obligations file for the `utf8_char_width_u8` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import utf8_char_width_u8

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Utf8_char_width_u8Obligations

open utf8_char_width_u8

/-- Postcondition (ASCII range): every byte `b < 0x80` has width `1`.
    Captures the property test `ascii_range_has_width_1`. -/
theorem utf8_char_width_ascii (b : u8) (h : b < 128) :
    utf8_char_width b = pure (1 : usize) := by sorry

/-- Postcondition (continuation + overlong 2-byte leaders):
    every byte `b` with `0x80 ≤ b < 0xC2` has width `0`.
    Captures the property test `continuation_and_overlong_have_width_0`. -/
theorem utf8_char_width_continuation_and_overlong
    (b : u8) (h1 : 128 ≤ b) (h2 : b < 194) :
    utf8_char_width b = pure (0 : usize) := by sorry

/-- Postcondition (2-byte leaders):
    every byte `b` with `0xC2 ≤ b < 0xE0` has width `2`.
    Captures the property test `two_byte_leaders_have_width_2`. -/
theorem utf8_char_width_two_byte_leader
    (b : u8) (h1 : 194 ≤ b) (h2 : b < 224) :
    utf8_char_width b = pure (2 : usize) := by sorry

/-- Postcondition (3-byte leaders):
    every byte `b` with `0xE0 ≤ b < 0xF0` has width `3`.
    Captures the property test `three_byte_leaders_have_width_3`. -/
theorem utf8_char_width_three_byte_leader
    (b : u8) (h1 : 224 ≤ b) (h2 : b < 240) :
    utf8_char_width b = pure (3 : usize) := by sorry

/-- Postcondition (4-byte leaders):
    every byte `b` with `0xF0 ≤ b < 0xF5` has width `4`.
    Captures the property test `four_byte_leaders_have_width_4`. -/
theorem utf8_char_width_four_byte_leader
    (b : u8) (h1 : 240 ≤ b) (h2 : b < 245) :
    utf8_char_width b = pure (4 : usize) := by sorry

/-- Postcondition (high invalid):
    every byte `b ≥ 0xF5` has width `0` (beyond U+10FFFF, not a valid leader).
    Captures the property test `high_invalid_have_width_0`. -/
theorem utf8_char_width_high_invalid (b : u8) (h : 245 ≤ b) :
    utf8_char_width b = pure (0 : usize) := by sorry

/-- Totality / no-panic: for every `u8` input, `utf8_char_width` returns
    a value successfully. The function uses only total unsigned comparisons
    against constants and `pure` in each branch, so it never panics —
    implicitly checked by the six tests above that exhaustively iterate over
    the full `0x00..=0xFF` range. -/
theorem utf8_char_width_total (b : u8) :
    ∃ v : usize, utf8_char_width b = pure v := by sorry

end Utf8_char_width_u8Obligations
