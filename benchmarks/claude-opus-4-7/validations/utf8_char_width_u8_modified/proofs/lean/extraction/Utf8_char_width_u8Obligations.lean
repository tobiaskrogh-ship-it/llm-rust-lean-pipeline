-- Companion obligations file for the `utf8_char_width_u8` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

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

/-- Helper: `decide (b < n) = false` whenever some larger constant `m` bounds
    `b` from below (`m ≤ b`) and `n ≤ m`. Routes through `toNat` so `omega`
    sees plain `Nat`s and doesn't have to evaluate `UInt8.toNat` on literals.
    Used to discharge the false branches of `utf8_char_width`'s nested
    `if`-chain. -/
private theorem decide_lt_false_of_le_of_le
    {b n m : u8} (hb : m ≤ b) (hnm : n ≤ m) :
    decide (b < n) = false := by
  apply decide_eq_false
  intro hlt
  have hltN : b.toNat < n.toNat := UInt8.lt_iff_toNat_lt.mp hlt
  have hbN : m.toNat ≤ b.toNat := UInt8.le_iff_toNat_le.mp hb
  have hnmN : n.toNat ≤ m.toNat := UInt8.le_iff_toNat_le.mp hnm
  omega

/-- Helper: `¬ b < n → n ≤ b` for `u8`. Saves repeating the `toNat` round-trip
    six times in the totality theorem's dispatch ladder. -/
private theorem le_of_not_lt {b n : u8} (h : ¬ b < n) : n ≤ b := by
  apply UInt8.le_iff_toNat_le.mpr
  have hn : ¬ (b.toNat < n.toNat) := fun hlt => h (UInt8.lt_iff_toNat_lt.mpr hlt)
  omega

/-- Postcondition (ASCII range): every byte `b < 0x80` has width `1`.
    Captures the property test `ascii_range_has_width_1`. -/
theorem utf8_char_width_ascii (b : u8) (h : b < 128) :
    utf8_char_width b = pure (1 : usize) := by
  simp only [utf8_char_width, rust_primitives.cmp.lt, pure_bind]
  have hcond : decide (b < (128 : u8)) = true := decide_eq_true h
  simp [hcond]

/-- Postcondition (continuation + overlong 2-byte leaders):
    every byte `b` with `0x80 ≤ b < 0xC2` has width `0`.
    Captures the property test `continuation_and_overlong_have_width_0`. -/
theorem utf8_char_width_continuation_and_overlong
    (b : u8) (h1 : 128 ≤ b) (h2 : b < 194) :
    utf8_char_width b = pure (0 : usize) := by
  simp only [utf8_char_width, rust_primitives.cmp.lt, pure_bind]
  have hcond1 : decide (b < (128 : u8)) = false :=
    decide_lt_false_of_le_of_le h1 (by decide : (128 : u8) ≤ 128)
  have hcond2 : decide (b < (194 : u8)) = true := decide_eq_true h2
  simp [hcond1, hcond2]

/-- Postcondition (2-byte leaders):
    every byte `b` with `0xC2 ≤ b < 0xE0` has width `2`.
    Captures the property test `two_byte_leaders_have_width_2`. -/
theorem utf8_char_width_two_byte_leader
    (b : u8) (h1 : 194 ≤ b) (h2 : b < 224) :
    utf8_char_width b = pure (2 : usize) := by
  simp only [utf8_char_width, rust_primitives.cmp.lt, pure_bind]
  have hcond1 : decide (b < (128 : u8)) = false :=
    decide_lt_false_of_le_of_le h1 (by decide : (128 : u8) ≤ 194)
  have hcond2 : decide (b < (194 : u8)) = false :=
    decide_lt_false_of_le_of_le h1 (by decide : (194 : u8) ≤ 194)
  have hcond3 : decide (b < (224 : u8)) = true := decide_eq_true h2
  simp [hcond1, hcond2, hcond3]

/-- Postcondition (3-byte leaders):
    every byte `b` with `0xE0 ≤ b < 0xF0` has width `3`.
    Captures the property test `three_byte_leaders_have_width_3`. -/
theorem utf8_char_width_three_byte_leader
    (b : u8) (h1 : 224 ≤ b) (h2 : b < 240) :
    utf8_char_width b = pure (3 : usize) := by
  simp only [utf8_char_width, rust_primitives.cmp.lt, pure_bind]
  have hcond1 : decide (b < (128 : u8)) = false :=
    decide_lt_false_of_le_of_le h1 (by decide : (128 : u8) ≤ 224)
  have hcond2 : decide (b < (194 : u8)) = false :=
    decide_lt_false_of_le_of_le h1 (by decide : (194 : u8) ≤ 224)
  have hcond3 : decide (b < (224 : u8)) = false :=
    decide_lt_false_of_le_of_le h1 (by decide : (224 : u8) ≤ 224)
  have hcond4 : decide (b < (240 : u8)) = true := decide_eq_true h2
  simp [hcond1, hcond2, hcond3, hcond4]

/-- Postcondition (4-byte leaders):
    every byte `b` with `0xF0 ≤ b < 0xF5` has width `4`.
    Captures the property test `four_byte_leaders_have_width_4`. -/
theorem utf8_char_width_four_byte_leader
    (b : u8) (h1 : 240 ≤ b) (h2 : b < 245) :
    utf8_char_width b = pure (4 : usize) := by
  simp only [utf8_char_width, rust_primitives.cmp.lt, pure_bind]
  have hcond1 : decide (b < (128 : u8)) = false :=
    decide_lt_false_of_le_of_le h1 (by decide : (128 : u8) ≤ 240)
  have hcond2 : decide (b < (194 : u8)) = false :=
    decide_lt_false_of_le_of_le h1 (by decide : (194 : u8) ≤ 240)
  have hcond3 : decide (b < (224 : u8)) = false :=
    decide_lt_false_of_le_of_le h1 (by decide : (224 : u8) ≤ 240)
  have hcond4 : decide (b < (240 : u8)) = false :=
    decide_lt_false_of_le_of_le h1 (by decide : (240 : u8) ≤ 240)
  have hcond5 : decide (b < (245 : u8)) = true := decide_eq_true h2
  simp [hcond1, hcond2, hcond3, hcond4, hcond5]

/-- Postcondition (high invalid):
    every byte `b ≥ 0xF5` has width `0` (beyond U+10FFFF, not a valid leader).
    Captures the property test `high_invalid_have_width_0`. -/
theorem utf8_char_width_high_invalid (b : u8) (h : 245 ≤ b) :
    utf8_char_width b = pure (0 : usize) := by
  simp only [utf8_char_width, rust_primitives.cmp.lt, pure_bind]
  have hcond1 : decide (b < (128 : u8)) = false :=
    decide_lt_false_of_le_of_le h (by decide : (128 : u8) ≤ 245)
  have hcond2 : decide (b < (194 : u8)) = false :=
    decide_lt_false_of_le_of_le h (by decide : (194 : u8) ≤ 245)
  have hcond3 : decide (b < (224 : u8)) = false :=
    decide_lt_false_of_le_of_le h (by decide : (224 : u8) ≤ 245)
  have hcond4 : decide (b < (240 : u8)) = false :=
    decide_lt_false_of_le_of_le h (by decide : (240 : u8) ≤ 245)
  have hcond5 : decide (b < (245 : u8)) = false :=
    decide_lt_false_of_le_of_le h (by decide : (245 : u8) ≤ 245)
  simp [hcond1, hcond2, hcond3, hcond4, hcond5]

/-- Totality / no-panic: for every `u8` input, `utf8_char_width` returns
    a value successfully. The function uses only total unsigned comparisons
    against constants and `pure` in each branch, so it never panics —
    implicitly checked by the six tests above that exhaustively iterate over
    the full `0x00..=0xFF` range. -/
theorem utf8_char_width_total (b : u8) :
    ∃ v : usize, utf8_char_width b = pure v := by
  by_cases h1 : b < (128 : u8)
  · exact ⟨1, utf8_char_width_ascii b h1⟩
  · have h128 : (128 : u8) ≤ b := le_of_not_lt h1
    by_cases h2 : b < (194 : u8)
    · exact ⟨0, utf8_char_width_continuation_and_overlong b h128 h2⟩
    · have h194 : (194 : u8) ≤ b := le_of_not_lt h2
      by_cases h3 : b < (224 : u8)
      · exact ⟨2, utf8_char_width_two_byte_leader b h194 h3⟩
      · have h224 : (224 : u8) ≤ b := le_of_not_lt h3
        by_cases h4 : b < (240 : u8)
        · exact ⟨3, utf8_char_width_three_byte_leader b h224 h4⟩
        · have h240 : (240 : u8) ≤ b := le_of_not_lt h4
          by_cases h5 : b < (245 : u8)
          · exact ⟨4, utf8_char_width_four_byte_leader b h240 h5⟩
          · have h245 : (245 : u8) ≤ b := le_of_not_lt h5
            exact ⟨0, utf8_char_width_high_invalid b h245⟩

end Utf8_char_width_u8Obligations
