-- Companion obligations file for the `pad_to_align_usize` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import pad_to_align_usize

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Pad_to_align_usizeObligations

/-- The `Layout` invariant precondition fragment: `align` is a power of two.
    Powers of two are exactly the legal alignments enumerated by the Rust
    property tests (`aligns()` ranges over `2^0 ..= 2^12`). A power of two is
    `≥ 1`, so this also discharges the `align -? 1` no-underflow side
    condition. -/
def IsPow2 (a : usize) : Prop := ∃ k : Nat, a.toNat = 2 ^ k

/-- Definitional unfolding of the partial `usize` addition (the `add_one`
    `hax_add_def_u8` trick, transposed to `USize64` — exactly the reference
    `max_size_for_align`'s `hax_add_def_usize`): `x +? y` is, by `rfl`, the
    overflow-guarded `if`. -/
private theorem hax_add_def_usize (x y : usize) :
    x +? y = if USize64.addOverflow x y
             then RustM.fail Error.integerOverflow
             else pure (x + y) := rfl

/-- Definitional unfolding of the partial `usize` subtraction. -/
private theorem hax_sub_def_usize (x y : usize) :
    x -? y = if USize64.subOverflow x y
             then RustM.fail Error.integerOverflow
             else pure (x - y) := rfl

/-- Bridge: `USize64` bitwise-and projects through to `Nat.land` of the
    `toNat`s. `USize64.land a b := ⟨a.toBitVec &&& b.toBitVec⟩` and
    `toNat := ·.toBitVec.toNat`, so this is `BitVec.toNat_and` under the
    structure projection. -/
private theorem usize_toNat_and (a b : usize) :
    (a &&& b).toNat = a.toNat &&& b.toNat := by
  have h : (a &&& b).toBitVec = a.toBitVec &&& b.toBitVec := rfl
  unfold USize64.toNat
  rw [h, BitVec.toNat_and]

/-- Bridge: `USize64` complement projects through to the 64-bit `BitVec`
    complement value `2^64 - 1 - n`. -/
private theorem usize_toNat_compl (a : usize) :
    (~~~ a).toNat = 2 ^ 64 - 1 - a.toNat := by
  have h : (~~~ a).toBitVec = ~~~ a.toBitVec := rfl
  unfold USize64.toNat
  rw [h, BitVec.toNat_not]

/-- Power-of-two bitmask round-down identity at the `Nat` level: masking off
    the low `k` bits (anding with the 64-bit high mask `2^64 - 2^k`) of any
    value `< 2^64` equals clearing the low `k` bits, i.e.
    `2^k * (sn / 2^k)`. Proved by bit extensionality
    (`Nat.eq_of_testBit_eq`): bit `i` of the result is `sn`'s bit `i` when
    `k ≤ i` and `0` otherwise; the only subtlety is that a set bit of `sn`
    forces `i < 64`, discharged from `sn < 2^64` via
    `Nat.testBit_lt_two_pow`.

    This is the missing library lemma flagged by the selector
    ("power-of-two bitmask round-up identity"): no reference example proved
    `(s + (a-1)) & ~(a-1)` as the least multiple of a power-of-two `a`. -/
private theorem mask_clear (sn k : Nat) (hsn : sn < 2 ^ 64) (hk : k ≤ 64) :
    sn &&& (2 ^ 64 - 2 ^ k) = 2 ^ k * (sn / 2 ^ k) := by
  have hfac : (2 : Nat) ^ 64 - 2 ^ k = (2 ^ (64 - k) - 1) * 2 ^ k := by
    have hpow : (2 : Nat) ^ (64 - k) * 2 ^ k = 2 ^ 64 := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [Nat.sub_mul, Nat.one_mul, hpow]
  rw [hfac]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one,
             Nat.testBit_two_pow_mul, Nat.testBit_div_two_pow, ge_iff_le]
  by_cases hkj : k ≤ j
  · have d1 : decide (k ≤ j) = true := decide_eq_true hkj
    have d3 : j - k + k = j := by omega
    rw [d1, d3]
    simp only [Bool.true_and]
    by_cases hb : sn.testBit j = true
    · have hj : j < 64 := by
        have hge2 : sn ≥ 2 ^ j := Nat.ge_two_pow_of_testBit hb
        have hlt2 : (2 : Nat) ^ j < 2 ^ 64 := Nat.lt_of_le_of_lt hge2 hsn
        exact (Nat.pow_lt_pow_iff_right (by decide)).mp hlt2
      rw [hb]
      simp only [Bool.true_and, decide_eq_true_eq]
      omega
    · simp only [Bool.not_eq_true] at hb
      simp [hb]
  · have d1 : decide (k ≤ j) = false := decide_eq_false hkj
    rw [d1]
    simp only [Bool.false_and, Bool.and_false]

/-- The exact `Nat` value of the rounded size, under the invariant. Combines
    the partial-operator `toNat` bridges (`toNat_sub_of_le`,
    `toNat_add_of_lt`), the complement bridge `usize_toNat_compl`
    (`~~~(a-1)` ↦ `2^64 - 2^k`), and the `mask_clear` round-down identity. -/
private theorem result_toNat (s a : usize) (k : Nat)
    (hk : a.toNat = 2 ^ k)
    (hnof : s.toNat + (a.toNat - 1) < 2 ^ 64) :
    ((s + (a - 1)) &&& ~~~(a - 1)).toNat
      = 2 ^ k * ((s.toNat + (2 ^ k - 1)) / 2 ^ k) := by
  have hk64 : k ≤ 64 := by
    have hlt : a.toNat < 2 ^ 64 := a.toNat_lt
    rw [hk] at hlt
    have hk' : k < 64 := (Nat.pow_lt_pow_iff_right (by decide)).mp hlt
    omega
  have hone : (1 : usize).toNat = 1 := by decide
  have hle1 : (1 : usize) ≤ a := by
    rw [USize64.le_iff_toNat_le, hone, hk]
    exact Nat.one_le_two_pow
  have ham1 : (a - (1 : usize)).toNat = 2 ^ k - 1 := by
    rw [USize64.toNat_sub_of_le _ _ hle1, hone, hk]
  have hbnd : s.toNat + (a - (1 : usize)).toNat < 2 ^ 64 := by
    rw [ham1]
    have hz : a.toNat - 1 = 2 ^ k - 1 := by rw [hk]
    omega
  have hSeq : (s + (a - 1)).toNat = s.toNat + (2 ^ k - 1) := by
    rw [USize64.toNat_add_of_lt hbnd, ham1]
  have hCeq : (~~~ (a - (1 : usize))).toNat = 2 ^ 64 - 2 ^ k := by
    rw [usize_toNat_compl, ham1]
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h2 : 2 ^ k ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hk64
    omega
  have hsn' : s.toNat + (2 ^ k - 1) < 2 ^ 64 := by
    have hz : a.toNat - 1 = 2 ^ k - 1 := by rw [hk]
    omega
  rw [usize_toNat_and, hSeq, hCeq]
  exact mask_clear (s.toNat + (2 ^ k - 1)) k hsn' hk64

/-- Foundational mechanical reduction (not itself a Rust property test, but
    stated in the equational style preferred by the references — cf.
    `max_size_for_align_postcondition`, `average_floor_postcondition`).

    Under the `Layout` invariant — `align` a power of two (hence `≥ 1`, so
    `align -? 1` does not underflow) and `size + (align - 1)` not overflowing
    `usize` — `pad_to_align` succeeds and returns the struct
    `Layout.mk ((size + (align-1)) &&& ~~~(align-1)) align`. The per-clause
    contract theorems below project out of this one equation. -/
private theorem pad_to_align_spec (layout : pad_to_align_usize.Layout)
    (hpow : IsPow2 layout.align)
    (hnof : layout.size.toNat + (layout.align.toNat - 1) < 2 ^ 64) :
    pad_to_align_usize.pad_to_align layout
      = RustM.ok (pad_to_align_usize.Layout.mk
          ((layout.size + (layout.align - 1)) &&& (~~~(layout.align - 1)))
          layout.align) := by
  obtain ⟨k, hk⟩ := hpow
  have hone : (1 : usize).toNat = 1 := by decide
  have hsub_no : ¬ USize64.subOverflow layout.align (1 : usize) := by
    rw [USize64.subOverflow_iff, hone, hk]
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  have hle1 : (1 : usize) ≤ layout.align := by
    rw [USize64.le_iff_toNat_le, hone, hk]
    exact Nat.one_le_two_pow
  have ham1 : (layout.align - (1 : usize)).toNat = 2 ^ k - 1 := by
    rw [USize64.toNat_sub_of_le _ _ hle1, hone, hk]
  have hadd_no : ¬ USize64.addOverflow layout.size (layout.align - (1 : usize)) := by
    rw [USize64.addOverflow_iff, ham1]
    have hz : layout.align.toNat - 1 = 2 ^ k - 1 := by rw [hk]
    omega
  unfold pad_to_align_usize.pad_to_align pad_to_align_usize.size_rounded_up_to_custom_align
  rw [hax_sub_def_usize, if_neg hsub_no]
  simp only [pure_bind]
  rw [hax_add_def_usize, if_neg hadd_no]
  simp only [pure_bind]
  rfl

/-- Totality / no-panic under the invariant. The Rust source comment states
    the padded size "is guaranteed to not exceed `isize::MAX`" — i.e. under
    the `Layout` invariant the function never panics. The property tests
    `aligns()`/`sizes()` only ever feed valid layouts, implicitly asserting
    this. -/
theorem pad_to_align_total (layout : pad_to_align_usize.Layout)
    (hpow : IsPow2 layout.align)
    (hnof : layout.size.toNat + (layout.align.toNat - 1) < 2 ^ 64) :
    ∃ r : pad_to_align_usize.Layout,
      pad_to_align_usize.pad_to_align layout = RustM.ok r :=
  ⟨_, pad_to_align_spec layout hpow hnof⟩

/-- Postcondition A — captures the Rust property test
    `prop_alignment_preserved`: the alignment is carried through unchanged
    (`out.align() == align`). -/
theorem pad_to_align_alignment_preserved (layout : pad_to_align_usize.Layout)
    (hpow : IsPow2 layout.align)
    (hnof : layout.size.toNat + (layout.align.toNat - 1) < 2 ^ 64) :
    ∃ r : pad_to_align_usize.Layout,
      pad_to_align_usize.pad_to_align layout = RustM.ok r
      ∧ r.align = layout.align :=
  ⟨_, pad_to_align_spec layout hpow hnof, rfl⟩

/-- Postcondition B — captures the Rust property test
    `prop_result_is_multiple_of_align`: the result size is a multiple of
    `align` (`out.size() % align == 0`). -/
theorem pad_to_align_result_is_multiple_of_align (layout : pad_to_align_usize.Layout)
    (hpow : IsPow2 layout.align)
    (hnof : layout.size.toNat + (layout.align.toNat - 1) < 2 ^ 64) :
    ∃ r : pad_to_align_usize.Layout,
      pad_to_align_usize.pad_to_align layout = RustM.ok r
      ∧ r.size.toNat % layout.align.toNat = 0 := by
  obtain ⟨k, hk⟩ := hpow
  refine ⟨_, pad_to_align_spec layout ⟨k, hk⟩ hnof, ?_⟩
  show ((layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1)).toNat
        % layout.align.toNat = 0
  rw [result_toNat layout.size layout.align k hk hnof, hk]
  exact Nat.mul_mod_right _ _

/-- Postcondition C — captures the Rust property test
    `prop_result_not_smaller_than_size`: rounding up never decreases the size
    (`out.size() >= size`). -/
theorem pad_to_align_result_not_smaller_than_size (layout : pad_to_align_usize.Layout)
    (hpow : IsPow2 layout.align)
    (hnof : layout.size.toNat + (layout.align.toNat - 1) < 2 ^ 64) :
    ∃ r : pad_to_align_usize.Layout,
      pad_to_align_usize.pad_to_align layout = RustM.ok r
      ∧ layout.size.toNat ≤ r.size.toNat := by
  obtain ⟨k, hk⟩ := hpow
  refine ⟨_, pad_to_align_spec layout ⟨k, hk⟩ hnof, ?_⟩
  show layout.size.toNat
        ≤ ((layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1)).toNat
  rw [result_toNat layout.size layout.align k hk hnof]
  have hdm := Nat.div_add_mod (layout.size.toNat + (2 ^ k - 1)) (2 ^ k)
  have hmod : (layout.size.toNat + (2 ^ k - 1)) % 2 ^ k < 2 ^ k :=
    Nat.mod_lt _ (Nat.two_pow_pos k)
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  omega

/-- Postcondition D (minimality) — captures the Rust property test
    `prop_result_is_least_such_multiple`: the padding added is strictly less
    than `align`, so the result is the *least* multiple of `align` that is
    `>= size` (`out.size() < size + align`). Together with B and C this
    uniquely pins the output size. -/
theorem pad_to_align_result_is_least_such_multiple (layout : pad_to_align_usize.Layout)
    (hpow : IsPow2 layout.align)
    (hnof : layout.size.toNat + (layout.align.toNat - 1) < 2 ^ 64) :
    ∃ r : pad_to_align_usize.Layout,
      pad_to_align_usize.pad_to_align layout = RustM.ok r
      ∧ r.size.toNat < layout.size.toNat + layout.align.toNat := by
  obtain ⟨k, hk⟩ := hpow
  refine ⟨_, pad_to_align_spec layout ⟨k, hk⟩ hnof, ?_⟩
  show ((layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1)).toNat
        < layout.size.toNat + layout.align.toNat
  rw [result_toNat layout.size layout.align k hk hnof, hk]
  have hdm := Nat.div_add_mod (layout.size.toNat + (2 ^ k - 1)) (2 ^ k)
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  omega

/-- Concrete instance from the unit test `pads_up` (first assertion):
    a size-6, align-4 layout pads up to size 8. -/
theorem pad_to_align_example_pads_6_to_8 :
    pad_to_align_usize.pad_to_align (pad_to_align_usize.Layout.mk 6 4)
      = RustM.ok (pad_to_align_usize.Layout.mk 8 4) := by
  refine (pad_to_align_spec (pad_to_align_usize.Layout.mk 6 4)
            ⟨2, by decide⟩ (by decide)).trans ?_
  rfl

/-- Concrete instance from the unit test `pads_up` (second assertion):
    a size-9, align-4 layout pads up to size 12. -/
theorem pad_to_align_example_pads_9_to_12 :
    pad_to_align_usize.pad_to_align (pad_to_align_usize.Layout.mk 9 4)
      = RustM.ok (pad_to_align_usize.Layout.mk 12 4) := by
  refine (pad_to_align_spec (pad_to_align_usize.Layout.mk 9 4)
            ⟨2, by decide⟩ (by decide)).trans ?_
  rfl

/-- Concrete instance from the unit test `already_aligned_is_unchanged`
    (first assertion): an already-aligned size-12, align-4 layout is
    unchanged. -/
theorem pad_to_align_example_already_aligned_12 :
    pad_to_align_usize.pad_to_align (pad_to_align_usize.Layout.mk 12 4)
      = RustM.ok (pad_to_align_usize.Layout.mk 12 4) := by
  refine (pad_to_align_spec (pad_to_align_usize.Layout.mk 12 4)
            ⟨2, by decide⟩ (by decide)).trans ?_
  rfl

/-- Concrete instance from the unit test `already_aligned_is_unchanged`
    (second assertion): a size-0, align-8 layout is unchanged. -/
theorem pad_to_align_example_already_aligned_0 :
    pad_to_align_usize.pad_to_align (pad_to_align_usize.Layout.mk 0 8)
      = RustM.ok (pad_to_align_usize.Layout.mk 0 8) := by
  refine (pad_to_align_spec (pad_to_align_usize.Layout.mk 0 8)
            ⟨3, by decide⟩ (by decide)).trans ?_
  rfl

end Pad_to_align_usizeObligations
