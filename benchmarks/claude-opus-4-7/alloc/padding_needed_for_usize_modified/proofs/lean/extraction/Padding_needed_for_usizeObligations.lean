-- Companion obligations file for the `padding_needed_for_usize` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

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

/-- Helper: when `x ≠ 0` is known, the unsigned subtraction `x - 1` does not
    overflow, so `x -? 1 = RustM.ok (x - 1)`. Ported from
    `is_size_align_valid_usize_modified`. -/
private theorem usize_sub_one_ok {x : usize} (hx : x ≠ 0) :
    (x -? (1 : usize)) = RustM.ok (x - 1) := by
  have hno : ¬ (BitVec.usubOverflow x.toBitVec (1#64) = true) := by
    have h0 : (USize64.subOverflow x 1 = true) ↔ x.toNat < (1 : usize).toNat :=
      USize64.subOverflow_iff
    have h1 : (1 : usize).toNat = 1 := rfl
    have hxnz : x.toNat ≠ 0 := by
      intro h
      apply hx
      apply USize64.toNat_inj.mp
      exact h
    show ¬ (USize64.subOverflow x 1 = true)
    rw [h0, h1]
    omega
  show (if BitVec.usubOverflow x.toBitVec (1#64) = true then
          (RustM.fail .integerOverflow : RustM usize)
        else pure (x - 1)) = RustM.ok (x - 1)
  rw [if_neg hno]
  rfl

/-- Characterization of `is_power_of_two_usize`: it always returns `ok`, with
    the Boolean value `x ≠ 0 ∧ (x &&& (x - 1) = 0)`. -/
private theorem is_power_of_two_usize_eq (x : usize) :
    is_power_of_two_usize x =
      RustM.ok (decide (x ≠ 0) && decide (x &&& (x - 1) = 0)) := by
  unfold is_power_of_two_usize
  by_cases hx : x = 0
  · subst hx
    decide
  · have hsub : (x -? (1 : usize)) = RustM.ok (x - 1) := usize_sub_one_ok hx
    show (do
      let __do_lift ← (pure (decide (x = 0)) : RustM Bool)
      if __do_lift = true then pure false
      else do
        let __do_lift ← (x -? (1 : usize))
        (x &&& __do_lift) ==? (0 : usize))
       = RustM.ok (decide (x ≠ 0) && decide (x &&& (x - 1) = 0))
    rw [decide_eq_false hx]
    simp only [pure_bind, Bool.false_eq_true, if_false]
    rw [hsub]
    show (do
        let __do_lift ← (pure (x - 1) : RustM usize)
        (x &&& __do_lift) ==? (0 : usize))
      = RustM.ok (decide (x ≠ 0) && decide (x &&& (x - 1) = 0))
    simp only [pure_bind]
    show (pure (decide (x &&& (x - 1) = 0)) : RustM Bool)
       = RustM.ok (decide (x ≠ 0) && decide (x &&& (x - 1) = 0))
    have h1 : decide (x ≠ 0) = true := decide_eq_true hx
    rw [h1, Bool.true_and]
    rfl

/-- From `is_power_of_two_usize align = ok true`, extract the bit-trick facts:
    `align ≠ 0` and `align &&& (align - 1) = 0`. -/
private theorem is_power_of_two_usize_facts {align : usize}
    (h : is_power_of_two_usize align = RustM.ok true) :
    align ≠ 0 ∧ align &&& (align - 1) = 0 := by
  rw [is_power_of_two_usize_eq] at h
  have hb : (decide (align ≠ 0) && decide (align &&& (align - 1) = 0)) = true := by
    have heq := h
    injection heq with heq1
    injection heq1
  rw [Bool.and_eq_true] at hb
  obtain ⟨h1, h2⟩ := hb
  exact ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩

/-- Doc-example anchor: `padding_needed_for 9 4 = 3`. Computed via `native_decide`
    since both inputs are concrete. -/
theorem padding_needed_for_doc_example :
    padding_needed_for (9 : usize) (4 : usize) = RustM.ok (3 : usize) := by
  native_decide

/-- Failure clause: when `align` is not a power of two, the function returns
    `usize::MAX = 2^64 - 1`. -/
theorem padding_needed_for_non_power_of_two (size align : usize)
    (h : is_power_of_two_usize align = RustM.ok false) :
    padding_needed_for size align = RustM.ok (18446744073709551615 : usize) := by
  unfold padding_needed_for
  rw [h]
  rfl

/-- Key BitVec fact: for any `s, a : BitVec 64` with `a ≠ 0`,
    `a &&& (a - 1) = 0` (i.e., `a` is a power of two), and `s + (a - 1)` not
    overflowing, the bit-trick rounded value
    (a) is ≥ `s` (so the outer subtraction is well-defined),
    (b) has `a - 1` low bits cleared (divisible by `a`), and
    (c) differs from `s` by strictly less than `a` (minimality). -/
private theorem bv_padding_key (s a : BitVec 64)
    (hnz : a ≠ 0#64)
    (hand : a &&& (a - 1#64) = 0#64)
    (hovf : BitVec.uaddOverflow s (a - 1#64) = false) :
    s ≤ ((s + (a - 1#64)) &&& ~~~(a - 1#64))
    ∧ ((s + (a - 1#64)) &&& ~~~(a - 1#64)) &&& (a - 1#64) = 0#64
    ∧ ((s + (a - 1#64)) &&& ~~~(a - 1#64)) - s < a := by
  bv_decide

/-- For power-of-two `a` at BitVec width 64, `x &&& (a - 1) = x % a`.
    This is the bit-trick form of modular reduction. -/
private theorem bv_and_mask_eq_mod (x a : BitVec 64)
    (hnz : a ≠ 0#64)
    (hand : a &&& (a - 1#64) = 0#64) :
    x &&& (a - 1#64) = x % a := by
  bv_decide (config := {timeout := 120})

/-- Helper simp lemma: `RustM.ok a >>= f = f a` (specialised `pure_bind`). -/
@[simp] private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

/-- Closed-form computation of `size_rounded_up_to_custom_align` under the
    power-of-two and no-overflow preconditions. -/
private theorem size_rounded_up_compute (size align : usize)
    (hnz : align ≠ 0)
    (hbound : size.toNat + align.toNat ≤ 2 ^ 64) :
    size_rounded_up_to_custom_align size align
      = RustM.ok ((size + (align - 1)) &&& ~~~ (align - 1)) := by
  have hnz_n : align.toNat ≠ 0 := fun h => hnz (USize64.toNat_inj.mp h)
  have halign_pos : 1 ≤ align.toNat := by omega
  have h_align_sub_one : align -? (1 : usize) = RustM.ok (align - 1) := usize_sub_one_ok hnz
  have h_one_toNat : (1 : usize).toNat = 1 := rfl
  have h_align_m1_nat : (align - 1).toNat = align.toNat - 1 := by
    have h := USize64.toNat_sub_of_le' (show (1 : usize).toNat ≤ align.toNat by
      rw [h_one_toNat]; exact halign_pos)
    rw [h_one_toNat] at h
    exact h
  have h_add_ok_nat : size.toNat + (align - 1).toNat < 2 ^ 64 := by
    rw [h_align_m1_nat]; omega
  have h_no_ovf_add : BitVec.uaddOverflow size.toBitVec (align - 1).toBitVec = false := by
    cases h_eq : BitVec.uaddOverflow size.toBitVec (align - 1).toBitVec with
    | false => rfl
    | true =>
      exfalso
      have : USize64.addOverflow size (align - 1) = true := h_eq
      rw [USize64.addOverflow_iff] at this; omega
  have h_size_add : (size +? (align - 1) : RustM usize) = RustM.ok (size + (align - 1)) := by
    show (if BitVec.uaddOverflow size.toBitVec (align - 1).toBitVec = true then
            (RustM.fail .integerOverflow : RustM usize)
          else pure (size + (align - 1))) = RustM.ok (size + (align - 1))
    rw [if_neg (by rw [h_no_ovf_add]; decide)]
    rfl
  unfold size_rounded_up_to_custom_align
  rw [h_align_sub_one, RustM_ok_bind, h_size_add, RustM_ok_bind]
  rfl

/-- Conversion helpers: assemble the BV-level facts into usize / Nat facts. -/
private theorem padding_compute_facts (size align : usize)
    (hpow : is_power_of_two_usize align = RustM.ok true)
    (hbound : size.toNat + align.toNat ≤ 2 ^ 64) :
    padding_needed_for size align
      = RustM.ok (((size + (align - 1)) &&& ~~~ (align - 1)) - size)
    ∧ size ≤ ((size + (align - 1)) &&& ~~~ (align - 1))
    ∧ ((size + (align - 1)) &&& ~~~ (align - 1)).toNat % align.toNat = 0
    ∧ (((size + (align - 1)) &&& ~~~ (align - 1)) - size) < align := by
  obtain ⟨hnz, hand⟩ := is_power_of_two_usize_facts hpow
  -- BV-level versions of the hypotheses.
  have hb_nz : align.toBitVec ≠ 0#64 := fun h => hnz (USize64.toBitVec_inj.mp h)
  have hb_and : align.toBitVec &&& (align.toBitVec - 1#64) = 0#64 := by
    have h1 : (align &&& (align - 1)).toBitVec = align.toBitVec &&& (align - 1).toBitVec := rfl
    have h2 : (align - 1).toBitVec = align.toBitVec - 1#64 := rfl
    have h0 : (0 : usize).toBitVec = 0#64 := rfl
    have h := congrArg USize64.toBitVec hand
    rw [h1, h2, h0] at h
    exact h
  -- Nat-level pos.
  have hnz_n : align.toNat ≠ 0 := fun h => hnz (USize64.toNat_inj.mp h)
  have halign_pos : 1 ≤ align.toNat := by omega
  have h_one_toNat : (1 : usize).toNat = 1 := rfl
  have h_align_m1_nat : (align - 1).toNat = align.toNat - 1 := by
    have h := USize64.toNat_sub_of_le' (show (1 : usize).toNat ≤ align.toNat by
      rw [h_one_toNat]; exact halign_pos)
    rw [h_one_toNat] at h
    exact h
  -- No overflow in +.
  have h_add_ok_nat : size.toNat + (align - 1).toNat < 2 ^ 64 := by
    rw [h_align_m1_nat]; omega
  have h_no_ovf_add : BitVec.uaddOverflow size.toBitVec (align - 1).toBitVec = false := by
    cases h_eq : BitVec.uaddOverflow size.toBitVec (align - 1).toBitVec with
    | false => rfl
    | true =>
      exfalso
      have : USize64.addOverflow size (align - 1) = true := h_eq
      rw [USize64.addOverflow_iff] at this; omega
  have h_no_ovf_add' : BitVec.uaddOverflow size.toBitVec (align.toBitVec - 1#64) = false := h_no_ovf_add
  -- Apply BV key lemma.
  obtain ⟨h_le_bv, h_div_bv, h_lt_bv⟩ :=
    bv_padding_key size.toBitVec align.toBitVec hb_nz hb_and h_no_ovf_add'
  -- Convert h_le_bv to usize-level.
  have h_le_usize : size ≤ ((size + (align - 1)) &&& ~~~ (align - 1)) := by
    show size.toBitVec ≤ ((size + (align - 1)) &&& ~~~ (align - 1)).toBitVec
    show size.toBitVec
          ≤ (size.toBitVec + (align.toBitVec - 1#64)) &&& ~~~(align.toBitVec - 1#64)
    exact h_le_bv
  -- No underflow in -.
  have h_le_nat : size.toNat ≤ ((size + (align - 1)) &&& ~~~ (align - 1)).toNat := by
    have h := BitVec.le_def.mp h_le_bv
    -- h : size.toBitVec.toNat ≤ ((... + ...) &&& ~~~ ...).toNat
    -- These are definitionally USize64.toNat at usize-level.
    exact h
  have h_no_ovf_sub :
      BitVec.usubOverflow ((size + (align - 1)) &&& ~~~ (align - 1)).toBitVec size.toBitVec
        = false := by
    cases h_eq : BitVec.usubOverflow ((size + (align - 1)) &&& ~~~ (align - 1)).toBitVec size.toBitVec with
    | false => rfl
    | true =>
      exfalso
      have h1 : USize64.subOverflow ((size + (align - 1)) &&& ~~~ (align - 1)) size = true :=
        h_eq
      rw [USize64.subOverflow_iff] at h1
      omega
  -- Compute h_size_add for rewriting.
  have h_size_add : (size +? (align - 1) : RustM usize) = RustM.ok (size + (align - 1)) := by
    show (if BitVec.uaddOverflow size.toBitVec (align - 1).toBitVec = true then
            (RustM.fail .integerOverflow : RustM usize)
          else pure (size + (align - 1))) = RustM.ok (size + (align - 1))
    rw [if_neg (by rw [h_no_ovf_add]; decide)]
    rfl
  -- Compute rounded -? size = ok (rounded - size).
  have h_rounded_sub :
      (((size + (align - 1)) &&& ~~~ (align - 1)) -? size : RustM usize)
        = RustM.ok (((size + (align - 1)) &&& ~~~ (align - 1)) - size) := by
    show (if BitVec.usubOverflow
              ((size + (align - 1)) &&& ~~~ (align - 1)).toBitVec size.toBitVec = true then
            (RustM.fail .integerOverflow : RustM usize)
          else pure (((size + (align - 1)) &&& ~~~ (align - 1)) - size))
        = _
    rw [if_neg (by rw [h_no_ovf_sub]; decide)]
    rfl
  -- Closed-form equation.
  have h_eq : padding_needed_for size align
                = RustM.ok (((size + (align - 1)) &&& ~~~ (align - 1)) - size) := by
    unfold padding_needed_for
    rw [hpow, RustM_ok_bind]
    show (do
        let __do_lift ← (!? true : RustM Bool)
        if __do_lift = true then pure (18446744073709551615 : usize)
        else do
          let len_rounded_up ← size_rounded_up_to_custom_align size align
          (len_rounded_up -? size)) = _
    show (do
        let __do_lift ← (pure (!true) : RustM Bool)
        if __do_lift = true then pure (18446744073709551615 : usize)
        else do
          let len_rounded_up ← size_rounded_up_to_custom_align size align
          (len_rounded_up -? size)) = _
    simp only [Bool.not_true, pure_bind, Bool.false_eq_true, if_false]
    rw [size_rounded_up_compute size align hnz hbound, RustM_ok_bind, h_rounded_sub]
  -- Divisibility: rounded.toNat % align.toNat = 0.
  have h_mod_zero :
      ((size + (align - 1)) &&& ~~~ (align - 1)).toNat % align.toNat = 0 := by
    -- bv_and_mask_eq_mod gives x &&& (a - 1) = x % a (BV mod).
    -- h_div_bv : rounded &&& (a - 1) = 0 in BV.
    -- Combined: rounded.toBitVec % align.toBitVec = 0.
    -- Then toNat_umod gives rounded.toNat % align.toNat = 0.
    have h1 : ((size + (align - 1)) &&& ~~~ (align - 1)).toBitVec &&&
                (align.toBitVec - 1#64) = 0#64 := h_div_bv
    have h2 : ((size + (align - 1)) &&& ~~~ (align - 1)).toBitVec &&&
                (align.toBitVec - 1#64)
              = ((size + (align - 1)) &&& ~~~ (align - 1)).toBitVec % align.toBitVec :=
      bv_and_mask_eq_mod ((size + (align - 1)) &&& ~~~ (align - 1)).toBitVec
        align.toBitVec hb_nz hb_and
    have h3 : ((size + (align - 1)) &&& ~~~ (align - 1)).toBitVec % align.toBitVec
              = 0#64 := by rw [← h2]; exact h1
    have h4 := congrArg BitVec.toNat h3
    rw [BitVec.toNat_umod] at h4
    -- h4 : ((size + (align - 1)) &&& ~~~ (align - 1)).toBitVec.toNat % align.toBitVec.toNat = 0
    exact h4
  -- Minimality: rounded - size < align.
  have h_lt_usize : (((size + (align - 1)) &&& ~~~ (align - 1)) - size) < align := by
    show (((size + (align - 1)) &&& ~~~ (align - 1)) - size).toBitVec
          < align.toBitVec
    show ((size.toBitVec + (align.toBitVec - 1#64)) &&&
            ~~~(align.toBitVec - 1#64)) - size.toBitVec < align.toBitVec
    exact h_lt_bv
  exact ⟨h_eq, h_le_usize, h_mod_zero, h_lt_usize⟩

theorem padding_needed_for_aligns_up (size align : usize)
    (hpow : is_power_of_two_usize align = RustM.ok true)
    (hbound : size.toNat + align.toNat ≤ 2 ^ 64) :
    ∃ r : usize, padding_needed_for size align = RustM.ok r
      ∧ (size.toNat + r.toNat) % align.toNat = 0 := by
  obtain ⟨h_eq, h_le, h_mod, _⟩ := padding_compute_facts size align hpow hbound
  refine ⟨((size + (align - 1)) &&& ~~~ (align - 1)) - size, h_eq, ?_⟩
  -- (size.toNat + r.toNat) % align.toNat = rounded.toNat % align.toNat = 0
  have h_size_le_rounded : size.toNat ≤ ((size + (align - 1)) &&& ~~~ (align - 1)).toNat :=
    USize64.le_iff_toNat_le.mp h_le
  have h_sub_nat :
      (((size + (align - 1)) &&& ~~~ (align - 1)) - size).toNat
        = ((size + (align - 1)) &&& ~~~ (align - 1)).toNat - size.toNat :=
    USize64.toNat_sub_of_le' h_size_le_rounded
  rw [h_sub_nat]
  have h_add_sub :
      size.toNat + (((size + (align - 1)) &&& ~~~ (align - 1)).toNat - size.toNat)
        = ((size + (align - 1)) &&& ~~~ (align - 1)).toNat := by omega
  rw [h_add_sub]
  exact h_mod

theorem padding_needed_for_minimal (size align : usize)
    (hpow : is_power_of_two_usize align = RustM.ok true)
    (hbound : size.toNat + align.toNat ≤ 2 ^ 64) :
    ∃ r : usize, padding_needed_for size align = RustM.ok r ∧ r < align := by
  obtain ⟨h_eq, _, _, h_lt⟩ := padding_compute_facts size align hpow hbound
  exact ⟨_, h_eq, h_lt⟩

theorem padding_needed_for_total (size align : usize)
    (hbound : is_power_of_two_usize align = RustM.ok true →
              size.toNat + align.toNat ≤ 2 ^ 64) :
    ∃ r : usize, padding_needed_for size align = RustM.ok r := by
  -- Case-split on whether align is a power of two.
  have hPow := is_power_of_two_usize_eq align
  by_cases hb : (decide (align ≠ 0) && decide (align &&& (align - 1) = 0)) = true
  · -- power-of-two: use aligns_up.
    rw [hb] at hPow
    have hbound' := hbound hPow
    obtain ⟨r, h_eq, _⟩ := padding_needed_for_aligns_up size align hPow hbound'
    exact ⟨r, h_eq⟩
  · -- non-power-of-two: returns sentinel.
    have hbf : (decide (align ≠ 0) && decide (align &&& (align - 1) = 0)) = false :=
      Bool.eq_false_iff.mpr hb
    rw [hbf] at hPow
    exact ⟨18446744073709551615,
           padding_needed_for_non_power_of_two size align hPow⟩

end Padding_needed_for_usizeObligations
