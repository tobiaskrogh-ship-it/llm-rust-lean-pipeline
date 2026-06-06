-- Companion obligations file for the `utf8_first_byte_u8` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import utf8_first_byte_u8

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Utf8_first_byte_u8Obligations

open utf8_first_byte_u8

/-! ## Postconditions and totality. -/

/-- Foundational postcondition (equational form): when `width < 8`, the function
    returns `(byte AND (0x7F >> width))` zero-extended to `u32`. This is what
    `utf8_first_byte` literally reduces to once the partial shift's
    `0 ≤ width ∧ width < 8` guard is discharged (`0 ≤ width` is vacuous on
    `u32`), the bitwise AND is total at unsigned width, and the `u8 → u32` cast
    is pure. The proptest `matches_payload_mask` (`width ∈ 0..=7`) pins this
    contract; the per-vector unit tests are concrete instances. -/
theorem utf8_first_byte_postcondition (byte : u8) (width : u32) (h : width < (8 : u32)) :
    utf8_first_byte byte width =
      RustM.ok (byte &&& ((127 : u8) >>> width.toNat.toUInt8)).toUInt32 := by
  unfold utf8_first_byte
  show (do
    let __do_lift1 ← (((127 : u8) >>>? width) : RustM u8)
    let __do_lift2 ← ((byte &&&? __do_lift1) : RustM u8)
    (rust_primitives.hax.cast_op __do_lift2 : RustM u32))
    = RustM.ok (byte &&& ((127 : u8) >>> width.toNat.toUInt8)).toUInt32
  have h_0_le_w : (0 : UInt32) ≤ width := by
    rw [UInt32.le_iff_toNat_le]
    show (0 : UInt32).toNat ≤ width.toNat
    rw [show ((0 : UInt32).toNat) = 0 from rfl]
    exact Nat.zero_le _
  have h_cond_eq : ((0 : UInt32) ≤ width && width < (8 : UInt32)) = true := by
    simp [h_0_le_w, h]
  show (do
    let __do_lift1 ←
      (if ((0 : UInt32) ≤ width && width < (8 : UInt32)) then
         (pure ((127 : u8) >>> width.toNat.toUInt8) : RustM u8)
       else RustM.fail .integerOverflow)
    let __do_lift2 ← (pure (byte &&& __do_lift1) : RustM u8)
    (pure ((byte &&& __do_lift1).toUInt32) : RustM u32))
    = RustM.ok (byte &&& ((127 : u8) >>> width.toNat.toUInt8)).toUInt32
  rw [h_cond_eq]
  simp only [if_true, pure_bind]
  rfl

/-- Postcondition stated in the proptest's exact form:
    `utf8_first_byte byte width = (byte as u32) & ((0x7F : u32) >> width)`
    for every valid `width ∈ [0, 8)`. Directly captures the contract surface
    of the proptest `matches_payload_mask` from the Rust source. Equivalent
    to `utf8_first_byte_postcondition` modulo the standard bit-vector
    identities `(x &&& y).toUInt32 = x.toUInt32 &&& y.toUInt32` and
    `((127:u8) >>> w).toUInt32 = (127:u32) >>> w` (for `w.toNat < 8`). -/
theorem utf8_first_byte_matches_payload_mask
    (byte : u8) (width : u32) (h : width < (8 : u32)) :
    utf8_first_byte byte width =
      RustM.ok (byte.toUInt32 &&& ((127 : u32) >>> width)) := by
  rw [utf8_first_byte_postcondition byte width h]
  congr 1
  have hlt : width.toNat < 8 := by
    have h1 := UInt32.lt_iff_toNat_lt.mp h
    have h8 : (8 : UInt32).toNat = 8 := rfl
    omega
  -- Case-split on the 8 possible values of width
  have h_inj : ∀ (k : Nat), k < 2 ^ 32 → width.toNat = k → width = (UInt32.ofNat k) := by
    intro k _ hk
    apply UInt32.toNat_inj.mp
    rw [hk]
    symm
    exact UInt32.toNat_ofNat_of_lt' (by omega : k < 2 ^ 32)
  have h_nat : width.toNat = 0 ∨ width.toNat = 1 ∨ width.toNat = 2 ∨ width.toNat = 3 ∨
               width.toNat = 4 ∨ width.toNat = 5 ∨ width.toNat = 6 ∨ width.toNat = 7 := by
    omega
  have h_cases : width = 0 ∨ width = 1 ∨ width = 2 ∨ width = 3 ∨
                  width = 4 ∨ width = 5 ∨ width = 6 ∨ width = 7 := by
    rcases h_nat with h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0
    · left; exact h_inj 0 (by decide) h0
    · right; left; exact h_inj 1 (by decide) h0
    · right; right; left; exact h_inj 2 (by decide) h0
    · right; right; right; left; exact h_inj 3 (by decide) h0
    · right; right; right; right; left; exact h_inj 4 (by decide) h0
    · right; right; right; right; right; left; exact h_inj 5 (by decide) h0
    · right; right; right; right; right; right; left; exact h_inj 6 (by decide) h0
    · right; right; right; right; right; right; right; exact h_inj 7 (by decide) h0
  rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [show (UInt32.toNat (0 : UInt32)) = 0 from rfl,
                 show (UInt32.toNat (1 : UInt32)) = 1 from rfl,
                 show (UInt32.toNat (2 : UInt32)) = 2 from rfl,
                 show (UInt32.toNat (3 : UInt32)) = 3 from rfl,
                 show (UInt32.toNat (4 : UInt32)) = 4 from rfl,
                 show (UInt32.toNat (5 : UInt32)) = 5 from rfl,
                 show (UInt32.toNat (6 : UInt32)) = 6 from rfl,
                 show (UInt32.toNat (7 : UInt32)) = 7 from rfl,
                 show (Nat.toUInt8 0) = (0 : UInt8) from rfl,
                 show (Nat.toUInt8 1) = (1 : UInt8) from rfl,
                 show (Nat.toUInt8 2) = (2 : UInt8) from rfl,
                 show (Nat.toUInt8 3) = (3 : UInt8) from rfl,
                 show (Nat.toUInt8 4) = (4 : UInt8) from rfl,
                 show (Nat.toUInt8 5) = (5 : UInt8) from rfl,
                 show (Nat.toUInt8 6) = (6 : UInt8) from rfl,
                 show (Nat.toUInt8 7) = (7 : UInt8) from rfl]
      bv_decide

/-- Totality on the valid input range: for every `width < 8`, the function
    returns successfully (no panic, no overflow). Implicit in
    `matches_payload_mask` but stated explicitly so downstream proofs that
    only need "the call succeeds" don't have to project through the closed
    form. -/
theorem utf8_first_byte_total_when_width_lt_8
    (byte : u8) (width : u32) (h : width < (8 : u32)) :
    ∃ r : u32, utf8_first_byte byte width = RustM.ok r :=
  ⟨_, utf8_first_byte_postcondition byte width h⟩

/-! ## Failure mode (panic). -/

/-- Failure condition: when `width ≥ 8`, the inner shift `(0x7F : u8) >> width`
    overflows the byte width and the function panics with
    `Error.integerOverflow`. This is the universal form of the Rust
    `#[should_panic]` test `panics_when_width_reaches_byte_width`
    (which exercises the single value `width = 8`); stating it for all
    `width ≥ 8` is the strongest honest contract — the shift's guard is
    `width < 8`, so every value outside the safe range fails the same way. -/
theorem utf8_first_byte_panics_when_width_ge_8
    (byte : u8) (width : u32) (h : (8 : u32) ≤ width) :
    utf8_first_byte byte width = RustM.fail Error.integerOverflow := by
  unfold utf8_first_byte
  show (do
    let __do_lift1 ← (((127 : u8) >>>? width) : RustM u8)
    let __do_lift2 ← ((byte &&&? __do_lift1) : RustM u8)
    (rust_primitives.hax.cast_op __do_lift2 : RustM u32))
    = RustM.fail Error.integerOverflow
  have h_not : ¬ (width < (8 : UInt32)) := by
    intro hlt
    have h_lt_n : width.toNat < (8 : UInt32).toNat := UInt32.lt_iff_toNat_lt.mp hlt
    have h_ge_n : (8 : UInt32).toNat ≤ width.toNat := UInt32.le_iff_toNat_le.mp h
    omega
  have h_cond_false : ((0 : UInt32) ≤ width && width < (8 : UInt32)) = false := by
    simp [h_not]
  show (do
    let __do_lift1 ←
      (if ((0 : UInt32) ≤ width && width < (8 : UInt32)) then
         (pure ((127 : u8) >>> width.toNat.toUInt8) : RustM u8)
       else RustM.fail .integerOverflow)
    let __do_lift2 ← (pure (byte &&& __do_lift1) : RustM u8)
    (pure ((byte &&& __do_lift1).toUInt32) : RustM u32))
    = RustM.fail Error.integerOverflow
  rw [h_cond_false]
  rfl

/-! ## Concrete anchors (regression-style vectors from the unit tests).

    Each one captures a single `assert_eq!` from `ascii_width_passes_byte_low_bits`
    or `width_zero_keeps_low_7_bits`. They are instances of
    `utf8_first_byte_postcondition` but are stated independently so that a
    contract shift (wrong mask, swapped operands, missing AND) would be
    caught even if the postcondition were also subtly miswritten. -/

/-- `utf8_first_byte 0xC2 2 = 0x02`. Width 2 ⇒ mask 0x1F; 0xC2 & 0x1F = 0x02.
    First vector of `ascii_width_passes_byte_low_bits`. -/
theorem utf8_first_byte_concrete_C2_w2 :
    utf8_first_byte (0xC2 : u8) (2 : u32) = RustM.ok (0x02 : u32) := by
  rw [utf8_first_byte_postcondition (0xC2 : u8) (2 : u32) (by decide)]
  native_decide

/-- `utf8_first_byte 0xE0 3 = 0x00`. Width 3 ⇒ mask 0x0F; 0xE0 & 0x0F = 0x00.
    Second vector of `ascii_width_passes_byte_low_bits`. -/
theorem utf8_first_byte_concrete_E0_w3 :
    utf8_first_byte (0xE0 : u8) (3 : u32) = RustM.ok (0x00 : u32) := by
  rw [utf8_first_byte_postcondition (0xE0 : u8) (3 : u32) (by decide)]
  native_decide

/-- `utf8_first_byte 0xEF 3 = 0x0F`. Width 3 ⇒ mask 0x0F; 0xEF & 0x0F = 0x0F.
    Third vector of `ascii_width_passes_byte_low_bits`. -/
theorem utf8_first_byte_concrete_EF_w3 :
    utf8_first_byte (0xEF : u8) (3 : u32) = RustM.ok (0x0F : u32) := by
  rw [utf8_first_byte_postcondition (0xEF : u8) (3 : u32) (by decide)]
  native_decide

/-- `utf8_first_byte 0xF0 4 = 0x00`. Width 4 ⇒ mask 0x07; 0xF0 & 0x07 = 0x00.
    Fourth vector of `ascii_width_passes_byte_low_bits`. -/
theorem utf8_first_byte_concrete_F0_w4 :
    utf8_first_byte (0xF0 : u8) (4 : u32) = RustM.ok (0x00 : u32) := by
  rw [utf8_first_byte_postcondition (0xF0 : u8) (4 : u32) (by decide)]
  native_decide

/-- `utf8_first_byte 0xF4 4 = 0x04`. Width 4 ⇒ mask 0x07; 0xF4 & 0x07 = 0x04.
    Fifth vector of `ascii_width_passes_byte_low_bits`. -/
theorem utf8_first_byte_concrete_F4_w4 :
    utf8_first_byte (0xF4 : u8) (4 : u32) = RustM.ok (0x04 : u32) := by
  rw [utf8_first_byte_postcondition (0xF4 : u8) (4 : u32) (by decide)]
  native_decide

/-- `utf8_first_byte 0x7F 0 = 0x7F`. Width 0 ⇒ mask 0x7F; 0x7F & 0x7F = 0x7F.
    First vector of `width_zero_keeps_low_7_bits`. -/
theorem utf8_first_byte_concrete_7F_w0 :
    utf8_first_byte (0x7F : u8) (0 : u32) = RustM.ok (0x7F : u32) := by
  rw [utf8_first_byte_postcondition (0x7F : u8) (0 : u32) (by decide)]
  native_decide

/-- `utf8_first_byte 0xFF 0 = 0x7F`. Width 0 ⇒ mask 0x7F; 0xFF & 0x7F = 0x7F.
    Second vector of `width_zero_keeps_low_7_bits` — the high bit of `byte`
    is dropped, a regression anchor against accidentally returning the raw
    byte. -/
theorem utf8_first_byte_concrete_FF_w0 :
    utf8_first_byte (0xFF : u8) (0 : u32) = RustM.ok (0x7F : u32) := by
  rw [utf8_first_byte_postcondition (0xFF : u8) (0 : u32) (by decide)]
  native_decide

end Utf8_first_byte_u8Obligations
